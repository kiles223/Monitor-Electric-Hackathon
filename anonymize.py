#!/usr/bin/env python3
"""
Обезличивание CIM-модели (RDF/XML) с сохранением структуры и ссылочной целостности.

Потоковая обработка: файл читается построчно, память не зависит от размера файла.
Детерминированность: все замены считаются как HMAC(соль, значение) -> результат
повторяется между запусками при одной и той же соли и одном и том же входе.

Использование:
    python anonymize.py input.xml output.xml --salt "секрет" [--config config.json]

Два прохода:
  1) сбор словаря «чувствительных слов» (топонимы, названия объектов, имена абонентов);
  2) замена по всему файлу, включая бинарные вложения (схемы, XML, изображения).

Язык подставляемых названий и имён задаётся в config.json (параметр "language"),
словари языков лежат в папке lexicons/ (один JSON-файл на язык).
"""
import argparse, base64, collections, hashlib, io, json, os, re, struct, sys, time, zipfile, zlib

try:
    import resource
except ImportError:          # Windows
    resource = None

HERE = os.path.dirname(os.path.abspath(__file__))

# ----------------------------------------------------------------------------
# Настройки по умолчанию (переопределяются файлом config.json)
# ----------------------------------------------------------------------------
DEFAULT_CONFIG = {
    "language": "auto",            # auto | ru | en | de | ... (имя файла из lexicons/ без .json)
    "lexicon_files": [],           # дополнительные файлы словарей (JSON)
    "extra_vocab": [],             # дополнительные слова, которые тоже нужно заменять
    "stop_words": [],              # дополнительные «технические» слова, которые НЕ заменять
    "min_digits_prefixed": 3,      # номера после «Sub», «ПС», «ТП»... от скольки цифр менять
    "min_digits_global": 6,        # длинные числа в любом тексте: от скольки цифр менять
    "process_blobs": True,         # разбирать бинарные вложения (base64) внутри XML
    "images": "blank",             # blank - заменять изображения в схемах заглушкой; keep - оставлять
    "icon_max_pixels": 65536,      # одиночные PNG-значки до этого размера считаются служебными и остаются
}


def load_config(path):
    cfg = dict(DEFAULT_CONFIG)
    if path is None:
        p = os.path.join(HERE, 'config.json')
        path = p if os.path.exists(p) else None
    if path:
        with open(path, encoding='utf-8') as f:
            user = json.load(f)
        unknown = set(user) - set(cfg) - {'_comment'}
        if unknown:
            print('Предупреждение: неизвестные параметры конфигурации:', sorted(unknown), file=sys.stderr)
        cfg.update({k: v for k, v in user.items() if k != '_comment'})
    return cfg


# ----------------------------------------------------------------------------
# Справочники синтетических значений
# ----------------------------------------------------------------------------
# «название овоща/фрукта -> прилагательное» (для юрлиц, объектов, топонимов)
PRODUCE_ADJ = """яблочный грушевый сливовый вишнёвый персиковый абрикосовый малиновый клубничный
черничный лимонный апельсиновый мандариновый грейпфрутовый гранатовый банановый ананасовый
манговый арбузный дынный виноградный смородиновый крыжовниковый облепиховый рябиновый
клюквенный брусничный морковный свекольный капустный картофельный томатный огуречный луковый
чесночный перечный баклажанный кабачковый тыквенный редисочный репный брюквенный редьковый
сельдереевый шпинатный салатный укропный петрушечный горошковый фасолевый кукурузный имбирный
хреновый щавелевый спаржевый артишоковый оливковый миндальный фисташковый ореховый инжирный
финиковый айвовый нектариновый помеловый гуавовый кокосовый каштановый ревенный пастернаковый
бататный""".split()

# «имя из справочника -> фамилия, имя, отчество, email, улица»
BASE_NAMES = """Иван Пётр Алексей Дмитрий Сергей Андрей Михаил Николай Владимир Александр Григорий Борис
Виктор Георгий Денис Егор Захар Игорь Кирилл Леонид Максим Олег Павел Роман Станислав Тимур
Фёдор Артём Евгений Константин Матвей Степан Юрий Ярослав Антон Валентин Василий Глеб Давид
Тихон Герман Аркадий""".split()

_TR = {'а':'a','б':'b','в':'v','г':'g','д':'d','е':'e','ё':'e','ж':'zh','з':'z','и':'i','й':'y',
       'к':'k','л':'l','м':'m','н':'n','о':'o','п':'p','р':'r','с':'s','т':'t','у':'u','ф':'f',
       'х':'kh','ц':'ts','ч':'ch','ш':'sh','щ':'shch','ъ':'','ы':'y','ь':'','э':'e','ю':'yu','я':'ya'}


def translit(s):
    out = []
    for ch in s:
        low = ch.lower()
        t = _TR.get(low, ch)
        out.append(t.capitalize() if ch.isupper() and t else t)
    return ''.join(out)


def surname(b):     # Иван -> Иванов, Дмитрий -> Дмитриев
    return b[:-1] + 'ев' if b[-1] in 'йь' else b + 'ов'


def patronymic(b):  # Иван -> Иванович
    return b[:-1] + 'евич' if b[-1] in 'йь' else b + 'ович'


def builtin_lexicons():
    ru = {'adjectives': [w.capitalize() for w in PRODUCE_ADJ],
          'first_names': list(BASE_NAMES),
          'surnames': [surname(b) for b in BASE_NAMES],
          'patronymics': [patronymic(b) for b in BASE_NAMES],
          'name_format': '{surname} {first} {patronymic}'}
    en = {k: ([translit(x) for x in v] if isinstance(v, list) else v) for k, v in ru.items()}
    en['adjectives'] = [w.capitalize() for w in en['adjectives']]
    return {'ru': ru, 'en': en}


def load_lexicons(cfg):
    lex = builtin_lexicons()
    files = []
    d = os.path.join(HERE, 'lexicons')
    if os.path.isdir(d):
        files += [os.path.join(d, n) for n in sorted(os.listdir(d)) if n.endswith('.json')]
    files += list(cfg.get('lexicon_files') or [])
    for p in files:
        with open(p, encoding='utf-8') as f:
            data = json.load(f)
        code = data.get('language') or os.path.splitext(os.path.basename(p))[0]
        lex[code] = {'adjectives': data['adjectives'], 'first_names': data['first_names'],
                     'surnames': data.get('surnames') or data['first_names'],
                     'patronymics': data.get('patronymics') or [],
                     'name_format': data.get('name_format', '{surname} {first} {patronymic}')}
    return lex


# ----------------------------------------------------------------------------
# Технические слова, которые НЕ являются собственными именами
# ----------------------------------------------------------------------------
STOP = set(w.lower() for w in """
sub substation feeder segment line cableline main pole from to electrical network factory plant emergency
warning switch device transformer test tank circuit breaker load current voltage reserve section street
district center centre rue new bay bus busbar protection tap ring with area power input output light
balancing aux auxgen enterprise processing matching facilities sports active mobile compound branch
agro plus wells combine state connector installation arrester surge limit imax fault operating
working status control monitoring transfer inverted setpoint converter reactor shunt cabinet
nov mar kvl segment http https
новые новый предприятие станция подстанция линия фидер нов
cable central church closed communication company complex east west north south education educational
elevator equivalent fall feed forestry global higher inlet institution interconnection invest joint local
market meat neighbouring nuclear objects park pool professional project railway rotor salad settlement
site station stock sugar support switchgear treatment university urban weighing cellular biological dairy
confectionery base areas budgetary hydro novye predpriyatie kompaniya gorodskaya tsentr avtomatika
ввод плюс район улица переулок поселок посёлок
""".split())

# Дополнительные собственные имена, которые автоматический сбор мог не найти
EXTRA_STEMS = ['Болгары', 'Аксуб', 'Aksub', 'Lancast', 'Lancst', 'Kabé', 'Mali', 'Bamako', 'bamako']

SUFFIXES = ('segment', 'main', 'brline', 'tap', 'line', 'plant', 'sub')

L = 'A-Za-zÀ-ÖØ-öø-ÿĀ-ſА-Яа-яЁё'
TOKEN_RE = re.compile(rf'[{L}]+')

# классы / теги, из которых собираем словарь собственных имён
HARVEST_CLASSES = {'cim:Substation', 'cim:Line', 'cim:ACLineSegment', 'rf:ACLineSeriesSection',
                   'cim:ServiceLocation', 'cim:Organisation', 'cim:GeographicalRegion',
                   'cim:SubGeographicalRegion', 'rf:Plant'}
HARVEST_TAGS = {'cim:StreetDetail.name', 'cim:TownDetail.name', 'cim:TownDetail.stateOrProvince',
                'cim:TownDetail.country', 'cim:TownDetail.section'}

# Правило из ответов организаторов: обезличиваются ВСЕ поля, в названии которых есть "name"
# (name, aliasName, folderName, buildingName, nameplate, ...), плюс текстовые поля ниже.
TEXT_SUFFIXES = ('.description', '.text', '.comment', '.markerText', '.djRecordText', '.textTemplate',
                 '.mRIDStr', '.mRID', '.number', '.suiteNumber', '.addressGeneral',
                 '.stateOrProvince', '.country', '.section', '.serialNumber', '.meteringPointCode',
                 '.ccsCode', '.mainAddress')
NO_TEXT_TAGS = {'md:Model.created', 'md:Model.version'}

UUID_RE = re.compile(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}')
SYSTEM_UUID_TAIL = '-0000-0000-c000-0000006d746c'   # справочные идентификаторы - не трогаем
LEAF_RE = re.compile(r'^(\s*)<([\w:.\-]+)((?:\s[^>]*)?)>([^<]*)</([\w:.\-]+)>(\s*)$')
CLASS_RE = re.compile(r'^  <([\w:.\-]+)\s+rdf:about=')
EMAIL_RE = re.compile(r'[\w.+\-]+@[\w\-]+(?:\.[\w\-]+)+')
PHONE_RE = re.compile(r'(?<![\d.\-])(?:(?:\+\d{1,3}|8)[\s\-]?\(?\d{3}\)?|\(\d{3}\))[\s\-]?\d{3}[\s\-]?\d{2}[\s\-]?\d{2}(?![\d\-])')
B64_RE = re.compile(r'[A-Za-z0-9+/]{64,}={0,2}')

# атрибуты и текстовые узлы внутри вложенных XML (схемы, описания участков линий)
ATTR_RE = re.compile(r'(\s)([\w:.\-]+)="([^"]*)"')
TEXTNODE_RE = re.compile(r'>([^<>]*[^\s<>][^<>]*)<')
NAME_ATTR_RE = re.compile(r'name|text|descr|caption|title|label|tooltip|comment|header|content|note', re.I)
SKIP_ATTRS = ('xmlns', 'encoding', 'version', 'Type', 'Target', 'ContentType', 'Extension')
DOTTED_ID_RE = re.compile(r'[A-Za-z_][\w]*(?:\.[\w]+)+(?:,[\w. =\-]+)?')
XML_MEMBERS = ('.xml', '.rels', '.scrap', '.xaml', '.xsd')


PREFIX_BEFORE_RE = re.compile(
    r'(?<![A-Za-zА-Яа-я])(?:Sub|Substation|ПС|ТП|КТП|KTP|РП|RP|f|feeder|Ф)\.?\s*[-–]?\s*$', re.I)
UNIT_AFTER_RE = re.compile(r'\s*(?:kV|kv|KV|кВ|kB|кв|А\b|A\b)')   # 110 kV, 400 A - это параметры, не номера
DIGITS_ANY_RE = re.compile(r'\d+')


def blank_png(raw):
    """Заглушка: белое изображение тех же размеров (текст на исходной картинке не сохраняется)."""
    w, h = struct.unpack('>II', raw[16:24])
    if w * h > 1_000_000:
        w, h = 64, 64

    def chunk(t, d):
        return struct.pack('>I', len(d)) + t + d + struct.pack('>I', zlib.crc32(t + d) & 0xFFFFFFFF)
    data = zlib.compress((b'\x00' + b'\xff' * w) * h, 9)
    return (b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', w, h, 8, 0, 0, 0, 0))
            + chunk(b'IDAT', data) + chunk(b'IEND', b''))


class Anonymizer:
    def __init__(self, salt: str, cfg=None):
        self.cfg = cfg or dict(DEFAULT_CONFIG)
        self.lex = load_lexicons(self.cfg)
        lang = self.cfg['language']
        if lang != 'auto' and lang not in self.lex:
            raise SystemExit(f'Язык "{lang}" не найден. Доступны: {sorted(self.lex)} (папка lexicons/ или lexicon_files)')
        self.key = hashlib.sha256(salt.encode()).digest()
        self.prefix_min = int(self.cfg['min_digits_prefixed'])
        self.global_min = int(self.cfg['min_digits_global'])
        self.stop = STOP | {w.lower() for w in self.cfg.get('stop_words') or []}
        self.num_map, self.used_num = {}, set()
        self.stem_map, self.used_stem = {}, set()
        self.fio_map, self.used_fio = {}, set()
        self.street_map, self.used_street = {}, set()
        self.stem_re = None
        self.cust_re = None
        self.cust_names = {}
        self.vocab = []
        self.stats = collections.Counter()        # сколько значений каждого вида заменено
        self.blob_stats = collections.Counter()   # что найдено во вложениях и что с ним сделано

    # ---- язык подставляемых значений ---------------------------------------
    def lang_of(self, text: str) -> str:
        lang = self.cfg['language']
        if lang != 'auto':
            return lang
        return 'ru' if re.search('[А-Яа-я]', text) else 'en'

    # ---- детерминированный хэш --------------------------------------------
    def h(self, s: str) -> int:
        return int.from_bytes(hashlib.blake2b(s.encode(), key=self.key, digest_size=16).digest(), 'big')

    def uuid(self, u: str) -> str:
        lu = u.lower()
        if lu.endswith(SYSTEM_UUID_TAIL):
            return u
        self.stats['идентификаторы объектов (GUID)'] += 1
        d = bytearray(hashlib.blake2b(lu.encode(), key=self.key, digest_size=16).digest())
        d[6] = (d[6] & 0x0F) | 0x40
        d[8] = (d[8] & 0x3F) | 0x80
        x = d.hex()
        r = f'{x[:8]}-{x[8:12]}-{x[12:16]}-{x[16:20]}-{x[20:]}'
        return r.upper() if u.isupper() else r

    # ---- числа (сохраняем длину, биекция) ---------------------------------
    def num(self, run: str) -> str:
        r = self.num_map.get(run)
        if r is not None:
            return r
        n, i = len(run), 0
        while True:
            x = self.h(f'num|{run}|{i}')
            s = str(x % (10 ** n)).zfill(n)
            if run[0] != '0' and s[0] == '0':
                s = str(1 + (x // 13) % 9) + s[1:]
            if s != run and s not in self.used_num:
                break
            i += 1
        self.num_map[run] = s
        self.used_num.add(s)
        return s

    def digits(self, text: str, minlen: int) -> str:
        """Заменяет числа от minlen цифр; фрагменты, похожие на GUID, не трогает."""
        rx = re.compile(r'\d{%d,}' % minlen)
        if '-' in text and UUID_RE.search(text):
            out, pos = [], 0
            for m in UUID_RE.finditer(text):
                out.append(rx.sub(lambda d: self.num(d.group()), text[pos:m.start()]))
                out.append(m.group())
                pos = m.end()
            out.append(rx.sub(lambda d: self.num(d.group()), text[pos:]))
            return ''.join(out)
        return rx.sub(lambda m: self.num(m.group()), text)

    # ---- прилагательное (овощ/фрукт) для собственных имён ------------------
    def adj(self, key: str) -> str:
        r = self.stem_map.get(key)
        if r:
            return r
        pool = self.lex[self.lang_of(key)]['adjectives']
        n, i = len(pool), 0
        while True:
            x = self.h(f'adj|{key}|{i}')
            w = pool[x % n]
            if i >= 4:
                w += '-' + pool[(x // n) % n]
            if i >= 40:
                w += str(i)
            if w not in self.used_stem:
                break
            i += 1
        self.stem_map[key] = w
        self.used_stem.add(w)
        return w

    # ---- ФИО / email / улица ----------------------------------------------
    def fio(self, orig: str):
        r = self.fio_map.get(orig)
        if r:
            return r
        lex = self.lex[self.lang_of(orig)]
        ns, nf, npat = len(lex['surnames']), len(lex['first_names']), len(lex['patronymics'])
        i = 0
        while True:
            x = self.h(f'fio|{orig}|{i}')
            t = (lex['surnames'][x % ns], lex['first_names'][(x // ns) % nf],
                 lex['patronymics'][(x // ns // nf) % npat] if npat else '')
            if t not in self.used_fio:
                break
            i += 1
        self.fio_map[orig] = t
        self.used_fio.add(t)
        return t

    def fio_str(self, orig: str) -> str:
        s, f, p = self.fio(orig)
        fmt = self.lex[self.lang_of(orig)]['name_format']
        return re.sub(r'\s+', ' ', fmt.format(surname=s, first=f, patronymic=p)).strip()

    def email(self, orig: str) -> str:
        s, f, _ = self.fio('email|' + orig)
        slug = lambda w: re.sub(r'[^a-z0-9]', '', translit(w).lower())
        local = f'{slug(f)}.{slug(s)}'.strip('.')
        if not local:
            local = 'user' + str(self.h('mail|' + orig) % 10 ** 8)
        return local + '@example.invalid'

    def street(self, orig: str) -> str:
        r = self.street_map.get(orig)
        if r:
            return r
        pool = self.lex[self.lang_of(orig)]['surnames']
        n, i = len(pool), 0
        while True:
            x = self.h(f'street|{orig}|{i}')
            nm = pool[x % n] + ('' if i < 4 else str(i))
            if nm not in self.used_street:
                break
            i += 1
        self.used_street.add(nm)
        self.street_map[orig] = nm
        return nm

    # ---- словарь собственных имён ----------------------------------------
    def stems_from(self, text: str):
        out = set()
        for tok in TOKEN_RE.findall(text):
            t = tok
            low = t.lower()
            for suf in SUFFIXES:
                if low.endswith(suf):
                    t = t[:-len(suf)] if len(t) - len(suf) >= 4 else ''   # короткий остаток: техническая склейка, не имя
                    low = t.lower()
                    break
            if len(t) >= 4 and t[0].isupper() and not t.isupper() and low not in self.stop:
                out.add(t)
        return out

    def finalize_vocab(self, stems, customers):
        stems = sorted(set(stems), key=lambda s: (-len(s), s))
        keys = []
        for s in stems:                       # ключ учитывает регистр: GoshenJT != GoshenJt
            if s not in self.stem_map:
                self.adj(s)
            keys.append(s)
        for s in stems:                       # вариант ЗАГЛАВНЫМИ - тем же прилагательным (строчные не берём: совпадают с кусками обычных слов)
            for v, f in ((s.upper(), str.upper),):
                if v not in self.stem_map:
                    self.stem_map[v] = f(self.stem_map[s])
                    keys.append(v)
        keys = sorted(set(keys), key=lambda s: (-len(s), s))
        short = [re.escape(s) for s in keys if len(s) < 6]
        long_ = [re.escape(s) for s in keys if len(s) >= 6]
        parts = []
        if short:
            parts.append(rf'(?<![{L}])(?:{"|".join(short)})')
        if long_:
            parts.append(rf'(?:{"|".join(long_)})')
        self.stem_re = re.compile('|'.join(parts)) if parts else None
        self.vocab = keys
        self.cust_names = {c: self.fio_str(c) for c in customers}
        if customers:
            alts = sorted(customers, key=len, reverse=True)
            self.cust_re = re.compile('|'.join(re.escape(c) for c in alts))

    # ---- обезличивание произвольного текста -------------------------------
    def numbers(self, v: str, minlen: int) -> str:
        """Заменяет числа за один проход: любые от minlen цифр и номера от prefix_min цифр после Sub/ПС/ТП/feeder..."""
        def rep(m):
            run = m.group()
            n = len(run)
            if n >= minlen:
                return self.num(run)
            if n >= self.prefix_min and PREFIX_BEFORE_RE.search(v[max(0, m.start() - 20):m.start()]) \
                    and not UNIT_AFTER_RE.match(v, m.end()):
                return self.num(run)
            return run
        return DIGITS_ANY_RE.sub(rep, v)

    def _text(self, v: str, full=True, minlen=None) -> str:
        if not v:
            return v
        if self.cust_re is not None and ' ' in v:
            v = self.cust_re.sub(lambda m: self.cust_names[m.group()], v)
        if self.stem_re is not None:
            v = self.stem_re.sub(lambda m: self.stem_map[m.group()], v)
        if any(c.isdigit() for c in v):
            v = self.numbers(v, (minlen or self.global_min) if full else 10 ** 9)
            if full:
                v = PHONE_RE.sub(lambda m: re.sub(r'\d', lambda d: str(self.h('ph|' + m.group() + str(d.start())) % 10), m.group()), v)
        if full and '@' in v:
            v = EMAIL_RE.sub(lambda m: self.email(m.group()), v)
        return v

    def text(self, v: str, full=True, minlen=None) -> str:
        """Текст с защитой GUID: идентификаторы внутри строки остаются как есть (их заменяют отдельно)."""
        if '-' in v and UUID_RE.search(v):
            out, pos = [], 0
            for m in UUID_RE.finditer(v):
                out.append(self._text(v[pos:m.start()], full, minlen))
                out.append(m.group())
                pos = m.end()
            out.append(self._text(v[pos:], full, minlen))
            return ''.join(out)
        return self._text(v, full, minlen)

    # ---- вложения (base64) -------------------------------------------------
    def xml(self, s: str) -> str:
        """Вложенный XML (схема подстанции, описание участков линии, фильтры...)."""
        def attr(m):
            sp, k, v = m.groups()
            if not v or k.startswith(SKIP_ATTRS) or UUID_RE.fullmatch(v.strip('{} ')) or DOTTED_ID_RE.fullmatch(v):
                return m.group(0)
            nv = self.text(v, full=bool(NAME_ATTR_RE.search(k)))
            return m.group(0) if nv == v else f'{sp}{k}="{nv}"'
        s = ATTR_RE.sub(attr, s)
        s = TEXTNODE_RE.sub(lambda m: '>' + self.text(m.group(1)) + '<', s)
        return UUID_RE.sub(lambda m: self.uuid(m.group()), s)   # ссылки на объекты - тем же способом, что и в основной модели

    def _png(self, raw: bytes, in_diagram: bool):
        if raw[:8] != b'\x89PNG\r\n\x1a\n' or len(raw) < 24:
            return raw, 'оставлен (не PNG)'
        w, h = struct.unpack('>II', raw[16:24])
        if self.cfg['images'] == 'blank' and (in_diagram or w * h > int(self.cfg['icon_max_pixels'])):
            return blank_png(raw), 'заменён заглушкой'
        return raw, 'оставлен (служебный значок)'

    def _zip(self, raw: bytes):
        zin = zipfile.ZipFile(io.BytesIO(raw))
        out, changed = io.BytesIO(), False
        with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as zout:
            for zi in zin.infolist():
                data = zin.read(zi)
                nd, low = data, zi.filename.lower()
                if data[:4] == b'PK\x03\x04':                      # вложенный архив (например, .scrap)
                    try:
                        nd = self._zip(data)
                        self.blob_stats[('вложенный архив в схеме', 'обезличен')] += 1
                    except zipfile.BadZipFile:
                        self.blob_stats[('вложенный архив в схеме', 'оставлен (повреждён)')] += 1
                elif low.endswith(XML_MEMBERS):
                    try:
                        s = data.decode('utf-8')
                    except UnicodeDecodeError:
                        self.blob_stats[('xml в схеме', 'оставлен (не UTF-8)')] += 1
                    else:
                        ns = self.xml(s)
                        if ns != s:
                            nd = ns.encode('utf-8')
                        self.blob_stats[('xml в схеме', 'обезличен')] += 1
                elif low.endswith('.png'):
                    nd, act = self._png(data, True)
                    self.blob_stats[('png в схеме', act)] += 1
                else:
                    self.blob_stats[('прочее в схеме (' + os.path.splitext(low)[1] + ')', 'оставлен')] += 1
                if nd is not data:
                    changed = True
                ni = zipfile.ZipInfo(zi.filename, zi.date_time)
                ni.compress_type = zipfile.ZIP_DEFLATED
                ni.external_attr = zi.external_attr
                zout.writestr(ni, nd)
        return out.getvalue() if changed else raw

    def blob(self, text: str) -> str:
        """Определяет тип вложения по сигнатуре и обезличивает его содержимое."""
        try:
            raw = base64.b64decode(text, validate=True)
        except Exception:
            return text
        if raw[:4] == b'PK\x03\x04':
            kind, new = 'zip-схема', None
            try:
                new = self._zip(raw)
            except zipfile.BadZipFile:
                self.blob_stats[(kind, 'оставлен (повреждён)')] += 1
                return text
            self.blob_stats[(kind, 'обезличен')] += 1
        elif raw[:8] == b'\x89PNG\r\n\x1a\n':
            new, act = self._png(raw, False)
            self.blob_stats[('png-изображение', act)] += 1
        elif raw.lstrip(b'\xef\xbb\xbf')[:1] == b'<':
            try:
                s = raw.decode('utf-8')
            except UnicodeDecodeError:
                self.blob_stats[('xml-вложение', 'оставлен (не UTF-8)')] += 1
                return text
            ns = self.xml(s)
            new = ns.encode('utf-8') if ns != s else raw
            self.blob_stats[('xml-вложение', 'обезличен')] += 1
        elif raw[:4] == b'RIFF':
            self.blob_stats[('звук (wav)', 'оставлен (текста нет)')] += 1
            return text
        else:
            self.blob_stats[('двоичные таблицы/кривые', 'оставлен (текста нет)')] += 1
            return text
        if new is raw:
            return text
        self.stats['бинарные вложения обработаны'] += 1
        return base64.b64encode(new).decode('ascii')

    # ---- обработка одной листовой строки ----------------------------------
    def leaf(self, cls, tag, text):
        if tag in NO_TEXT_TAGS or not text.strip():
            return text
        if len(text) >= 64 and self.cfg['process_blobs'] and B64_RE.fullmatch(text):
            return self.blob(text)
        if cls == 'cim:Person' and tag in ('cim:Person.lastName', 'cim:Person.firstName', 'cim:IdentifiedObject.name'):
            self.stats['ФИО сотрудников'] += 1
            s, f, p = self.fio(text)
            return {'cim:Person.lastName': s, 'cim:Person.firstName': f}.get(tag, self.fio_str(text))
        if tag == 'me:Location.inChargeFullName' or (cls == 'cim:Customer' and tag == 'cim:IdentifiedObject.name'):
            self.stats['ФИО абонентов и ответственных'] += 1
            return self.fio_str(text)
        if tag == 'cim:StreetDetail.name':
            self.stats['адреса (улицы, дома)'] += 1
            if re.match(r'^\s*(h\.|д\.?|дом)\s*№?\s*\d', text, re.I):      # номер дома в поле улицы
                return re.sub(r'\d+', lambda d: self.num(d.group()) if len(d.group()) >= 3 else str(self.h('hn|' + text + d.group()) % 90 + 1), text)
            m = re.match(r'^((?:Av\.?|Rue|ул\.?|пр\.?)\s+)?(.*?)(\s+(?:Street|Avenue))?$', text)
            pre, core, suf = m.group(1) or '', m.group(2), m.group(3) or ''
            if not core.strip() or core.strip().isdigit():
                return pre + self.digits(core, 3) + suf
            core2 = self.text(core)
            if core2 == core:          # собственного имени в словаре нет - подменяем целиком
                core2 = self.street(core)
            return pre + core2 + suf
        if tag in ('cim:StreetDetail.buildingName', 'cim:StreetDetail.number', 'cim:StreetDetail.suiteNumber'):
            self.stats['адреса (улицы, дома)'] += 1
            return re.sub(r'\d+', lambda d: self.num(d.group()) if len(d.group()) >= 3 else str(self.h('hn|' + text + d.group()) % 90 + 1), text)
        if tag.endswith(('.serialNumber', '.ccsCode', '.meteringPointCode')):
            self.stats['серийные и инвентарные номера'] += 1
            return self.text(text, minlen=4)
        if tag.endswith('.mRIDStr') or tag.endswith('.mRID'):
            self.stats['внутренние идентификаторы (mRID)'] += 1
            return UUID_RE.sub(lambda m: self.uuid(m.group()), self.text(text, minlen=5))
        if 'name' in tag.rsplit('.', 1)[-1].lower() or tag.endswith(TEXT_SUFFIXES):
            new = self.text(text)
            if new != text:
                self.stats['названия и описания (изменено значений)'] += 1
            return new
        return text


def run_pass1(src, anon: Anonymizer):
    stems, customers = set(), set()
    cls = None
    t0 = time.time()
    with open(src, encoding='utf-8', newline='') as f:
        for n, line in enumerate(f, 1):
            m = CLASS_RE.match(line)
            if m:
                cls = m.group(1)
                continue
            m = LEAF_RE.match(line)
            if not m:
                continue
            tag, text = m.group(2), m.group(4)
            if not text or tag in NO_TEXT_TAGS:
                continue
            if cls == 'cim:Customer' and tag == 'cim:IdentifiedObject.name':
                customers.add(text)
            elif tag in HARVEST_TAGS or (cls in HARVEST_CLASSES and tag == 'cim:IdentifiedObject.name'):
                stems |= anon.stems_from(text)
            if n % 2_000_000 == 0:
                print(f'  проход 1: {n:,} строк, {time.time()-t0:.0f}с', file=sys.stderr)
    return stems, customers


def run_pass2(src, dst, anon: Anonymizer):
    cls = None
    t0 = time.time()
    with open(src, encoding='utf-8', newline='') as fi, open(dst, 'w', encoding='utf-8', newline='') as fo:
        for n, line in enumerate(fi, 1):
            m = CLASS_RE.match(line)
            if m:
                cls = m.group(1)
            else:
                lm = LEAF_RE.match(line) if ('<' in line and '</' in line) else None
                if lm and lm.group(2) == lm.group(5):
                    ind, tag, attrs, text, _, tail = lm.groups()
                    new = anon.leaf(cls, tag, text)
                    line = f'{ind}<{tag}{attrs}>{new}</{tag}>{tail}'
            if '-' in line and '#_' in line or 'fias' in line:
                line = UUID_RE.sub(lambda m: anon.uuid(m.group()), line)
            fo.write(line)
            if n % 2_000_000 == 0:
                print(f'  проход 2: {n:,} строк, {time.time()-t0:.0f}с', file=sys.stderr)
    return n


def peak_memory_mb():
    if resource is None:
        return None
    kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return round(kb / 1024 / (1024 if sys.platform == 'darwin' else 1), 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('src'); ap.add_argument('dst')
    ap.add_argument('--salt', default=os.environ.get('ANON_SALT'),
                    help='секретная соль (или переменная окружения ANON_SALT); одинаковая соль -> одинаковый результат')
    ap.add_argument('--config', help='файл настроек (по умолчанию config.json рядом со скриптом)')
    ap.add_argument('--language', help='язык подставляемых значений (переопределяет config.json)')
    ap.add_argument('--extra-vocab', help='файл со словами (по одному в строке), которые тоже нужно заменять')
    ap.add_argument('--stats-out', help='сохранить статистику работы (без исходных данных) в JSON')
    ap.add_argument('--map-out', help='сохранить таблицу соответствий (СОДЕРЖИТ ИСХОДНЫЕ ДАННЫЕ, не передавать)')
    a = ap.parse_args()
    if not a.salt:
        ap.error('нужна соль: --salt или переменная окружения ANON_SALT')

    cfg = load_config(a.config)
    if a.language:
        cfg['language'] = a.language
    t_start = time.time()
    an = Anonymizer(a.salt, cfg)
    print(f'Язык подставляемых значений: {cfg["language"]}', file=sys.stderr)
    print('Проход 1: сбор словаря...', file=sys.stderr)
    stems, customers = run_pass1(a.src, an)
    stems |= set(EXTRA_STEMS) | set(cfg.get('extra_vocab') or [])
    if a.extra_vocab:
        stems |= {w.strip() for w in open(a.extra_vocab, encoding='utf-8') if w.strip()}
    an.finalize_vocab(stems, customers)
    t1 = time.time()
    print(f'  найдено собственных имён: {len(an.vocab)}, абонентов: {len(customers)}', file=sys.stderr)
    print('Проход 2: замена...', file=sys.stderr)
    lines = run_pass2(a.src, a.dst, an)
    t_total = time.time() - t_start
    mem = peak_memory_mb()
    size_mb = os.path.getsize(a.src) / 1e6

    print('\nСтатистика:', file=sys.stderr)
    for k, v in an.stats.most_common():
        print(f'  {k}: {v:,}', file=sys.stderr)
    if an.blob_stats:
        print('Вложения:', file=sys.stderr)
        for (kind, act), v in sorted(an.blob_stats.items()):
            print(f'  {kind}: {act} - {v:,}', file=sys.stderr)
    print(f'Время: {t_total:.0f} с (проход 1: {t1 - t_start:.0f} с), строк: {lines:,}, '
          f'скорость {size_mb / t_total:.1f} МБ/с, пиковая память: {mem} МБ', file=sys.stderr)

    if a.stats_out:
        json.dump({'seconds': round(t_total, 1), 'pass1_seconds': round(t1 - t_start, 1), 'lines': lines,
                   'input_mb': round(size_mb, 1), 'peak_memory_mb': mem, 'language': cfg['language'],
                   'replaced': dict(an.stats), 'vocab_size': len(an.vocab), 'customers': len(customers),
                   'blobs': {f'{k[0]} | {k[1]}': v for k, v in an.blob_stats.items()}},
                  open(a.stats_out, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
    if a.map_out:
        json.dump({'words': an.stem_map, 'customers': an.cust_names, 'numbers': an.num_map},
                  open(a.map_out, 'w', encoding='utf-8'), ensure_ascii=False)
    print('Готово.', file=sys.stderr)


if __name__ == '__main__':
    main()

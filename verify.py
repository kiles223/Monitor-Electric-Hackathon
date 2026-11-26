#!/usr/bin/env python3
"""
Проверка результата обезличивания.

    python verify.py input.xml output.xml --salt СОЛЬ              # все этапы подряд
    python verify.py input.xml output.xml --stage orig             # (для огромных файлов) только скан оригинала
    python verify.py input.xml output.xml --stage result           # структура, ссылки, уникальность
    python verify.py input.xml output.xml --stage leak             # утечки в полях + нумерация
    python verify.py input.xml output.xml --stage blobs            # утечки внутри бинарных вложений
    python verify.py input.xml output.xml --stage names --salt С   # согласованность имён между объектами

Этапы blobs и names запускают первый проход обезличивателя (сбор словаря) по оригиналу.
"""
import argparse, base64, collections, io, os, pickle, re, struct, sys, zipfile, zlib

CLASS_RE = re.compile(r'^  <([\w:.\-]+)\s+rdf:about="#([^"]+)"')
LEAF_RE = re.compile(r'^\s*<([\w:.\-]+)[^>]*>([^<]*)</\1>\s*$')
NAME_TAG = 'cim:IdentifiedObject.name'
RES_RE = re.compile(r'rdf:resource="#([^"]+)"')
TAGS_RE = re.compile(r'<(/?[\w:.\-]+)')
B64_RE = re.compile(r'[A-Za-z0-9+/]{64,}={0,2}')
DIGITS_RE = re.compile(r'\d{3,}')


def is_text_field(tag, an):
    return 'name' in tag.rsplit('.', 1)[-1].lower() or tag.endswith(an.TEXT_SUFFIXES)


def scan(path):
    classes = collections.Counter()
    names = collections.defaultdict(set)
    abouts, resources = set(), collections.Counter()
    skel, lines, cls = 0, 0, None
    with open(path, encoding='utf-8', newline='') as f:
        for line in f:
            lines += 1
            m = CLASS_RE.match(line)
            if m:
                cls = m.group(1); classes[cls] += 1; abouts.add(m.group(2))
            if 'rdf:resource' in line:
                for r in RES_RE.findall(line):
                    resources[r] += 1
            if NAME_TAG in line:
                lm = LEAF_RE.match(line)
                if lm and cls:
                    names[cls].add(lm.group(2))
            skel = (skel * 1000003 + zlib.crc32(' '.join(TAGS_RE.findall(line)).encode())) & 0xFFFFFFFFFFFF
    return dict(lines=lines, classes=classes, names=names, abouts=abouts, resources=resources, skel=skel)


class Report:
    ok = True
    def check(self, title, cond, extra=''):
        print(('  [OK]   ' if cond else '  [FAIL] ') + title + (' ' + extra if extra else ''))
        Report.ok &= bool(cond)


def vocab(src, salt):
    """Словарь собственных имён оригинала (тот же, что строит обезличиватель на проходе 1)."""
    import anonymize as an
    a = an.Anonymizer(salt, an.load_config(None))
    stems, customers = an.run_pass1(src, a)
    stems |= set(an.EXTRA_STEMS) | set(a.cfg.get('extra_vocab') or [])
    a.finalize_vocab(stems, customers)
    return a, customers


def structural(A, B, r):
    print('\n1. Структура')
    r.check('число строк совпадает', A['lines'] == B['lines'], f"({A['lines']:,})")
    r.check('последовательность тегов идентична построчно', A['skel'] == B['skel'])
    r.check('число объектов по классам идентично', A['classes'] == B['classes'],
            f"({sum(A['classes'].values()):,} объектов, {len(A['classes'])} классов)")
    print('\n2. Ссылочная целостность')
    miss_a = sum(1 for x in A['resources'] if x not in A['abouts'])
    miss_b = sum(1 for x in B['resources'] if x not in B['abouts'])
    r.check('число «висячих» ссылок как в оригинале', miss_a == miss_b, f'(было {miss_a}, стало {miss_b})')
    r.check('число ссылок идентично', sum(A['resources'].values()) == sum(B['resources'].values()),
            f"({sum(A['resources'].values()):,})")
    r.check('распределение входящих степеней графа идентично',
            collections.Counter(A['resources'].values()) == collections.Counter(B['resources'].values()))
    print('\n3. Уникальность имён (число различных имён в классе)')
    bad = [(c, len(A['names'][c]), len(B['names'].get(c, ()))) for c in A['names'] if len(A['names'][c]) != len(B['names'].get(c, ()))]
    r.check('число уникальных имён по каждому классу сохранено', not bad,
            f'(расхождения: {bad[:5]})' if bad else f"({len(A['names'])} классов)")


def leaks(a, b, r):
    import anonymize as an
    print('\n4. Утечки и нумерация (построчное сравнение исходного и результата)')
    must = {'cim:Customer', 'cim:Person', 'cim:ServiceLocation'}
    watch = {'cim:Substation', 'cim:Line', 'cim:ACLineSegment', 'rf:ACLineSeriesSection'}
    same_pii, susp = collections.Counter(), collections.Counter()
    len_a, len_b = collections.Counter(), collections.Counter()
    run_map, run_conflict = {}, 0
    cls = None
    with open(a, encoding='utf-8', newline='') as fa, open(b, encoding='utf-8', newline='') as fb:
        for la, lb in zip(fa, fb):
            m = CLASS_RE.match(la)
            if m:
                cls = m.group(1)
            x = LEAF_RE.match(la)
            if not x:
                continue
            tag, text = x.group(1), x.group(2)
            if la == lb and tag == NAME_TAG and (cls in must or cls in watch):
                if cls in must:
                    same_pii[cls] += 1
                elif [t for t in an.TOKEN_RE.findall(text) if len(t) >= 4 and t[0].isupper() and not t.isupper() and t.lower() not in an.STOP]:
                    susp[text] += 1
            if len(text) < 64 and cls not in must and is_text_field(tag, an) and not an.UUID_RE.search(text):
                y = LEAF_RE.match(lb)
                if not y:
                    continue
                ra, rb = DIGITS_RE.findall(text), DIGITS_RE.findall(y.group(2))
                len_a.update(len(v) for v in ra); len_b.update(len(v) for v in rb)
                if len(ra) == len(rb):                 # соответствие «старое число -> новое» должно быть функцией
                    for p, q in zip(ra, rb):
                        if len(p) >= 6:
                            if run_map.setdefault(p, q) != q:
                                run_conflict += 1
    r.check('имена абонентов, сотрудников, адресов: ни одно не осталось прежним', not same_pii,
            f'({dict(same_pii)})' if same_pii else '')
    r.check('имена ПС/ЛЭП с собственными именами: ни одно не осталось прежним', not susp,
            f'({len(susp)} шт., напр. {list(susp)[:4]})' if susp else '')
    r.check('нумерация: длины чисел (от 3 цифр) в названиях сохранены', len_a == len_b,
            f'(было {dict(sorted(len_a.items()))}, стало {dict(sorted(len_b.items()))})' if len_a != len_b else f'({sum(len_a.values()):,} чисел)')
    r.check('нумерация: одно и то же число всегда заменяется одним и тем же', run_conflict == 0,
            f'(конфликтов: {run_conflict})' if run_conflict else f'({len(run_map):,} различных чисел от 6 цифр)')


def blob_texts(raw, depth=0):
    """Тексты и статус изображений из вложения: (список строк, список «не заглушка»)."""
    texts, images = [], []
    if raw[:4] == b'PK\x03\x04' and depth < 4:
        z = zipfile.ZipFile(io.BytesIO(raw))
        for i in z.infolist():
            d = z.read(i)
            if d[:4] == b'PK\x03\x04':
                t, im = blob_texts(d, depth + 1); texts += t; images += im
            elif i.filename.lower().endswith(('.xml', '.rels', '.scrap', '.xaml', '.xsd')):
                texts.append(d.decode('utf-8', 'replace'))
            elif i.filename.lower().endswith('.png'):
                images.append(not png_is_blank(d))
    elif raw.lstrip(b'\xef\xbb\xbf')[:1] == b'<':
        texts.append(raw.decode('utf-8', 'replace'))
    return texts, images


def png_is_blank(d):
    try:
        pos, idat = 8, b''
        while pos < len(d):
            n = struct.unpack('>I', d[pos:pos + 4])[0]
            if d[pos + 4:pos + 8] == b'IDAT':
                idat += d[pos + 8:pos + 8 + n]
            pos += 12 + n
        data = zlib.decompress(idat)
        return set(data) <= {0, 255}
    except Exception:
        return False


def blobs(a, b, salt, r):
    print('\n5. Бинарные вложения (схемы, XML, изображения)')
    an, customers = vocab(a, salt)
    n_blob = n_leak_stem = n_leak_cust = n_img_bad = n_img = 0
    examples = []
    with open(b, encoding='utf-8', newline='') as f:
        for line in f:
            if len(line) < 120 or '<' not in line:
                continue
            lm = LEAF_RE.match(line)
            if not lm or not B64_RE.fullmatch(lm.group(2)):
                continue
            try:
                raw = base64.b64decode(lm.group(2), validate=True)
            except Exception:
                continue
            texts, images = blob_texts(raw)
            if not texts and not images:
                continue
            n_blob += 1
            for t in texts:
                hit = an.stem_re.search(t) if an.stem_re else None
                if hit:
                    n_leak_stem += 1
                    if len(examples) < 3: examples.append(hit.group())
                if an.cust_re and an.cust_re.search(t):
                    n_leak_cust += 1
            n_img += len(images); n_img_bad += sum(images)
    r.check('в обработанных вложениях не осталось исходных топонимов и названий', n_leak_stem == 0,
            f'({n_blob:,} вложений проверено)' if not n_leak_stem else f'({n_leak_stem} вложений, напр. {examples})')
    r.check('в обработанных вложениях не осталось имён абонентов', n_leak_cust == 0)
    r.check('изображения внутри схем заменены заглушкой', n_img_bad == 0, f'({n_img:,} изображений)' if not n_img_bad else f'({n_img_bad} из {n_img} не заменены)')


def names(a, b, salt, r):
    import anonymize as an_mod
    print('\n6. Согласованность имён между объектами')
    an, customers = vocab(a, salt)
    # (а) каждое слово из словаря заменяется одним и тем же значением везде
    bad_stem, checked_stem = 0, 0
    ids = {}                       # старый id -> (старое имя, новое имя)
    cls = None
    skip_cls = {'cim:Customer', 'cim:Person'}
    with open(a, encoding='utf-8', newline='') as fa, open(b, encoding='utf-8', newline='') as fb:
        cur = None
        for la, lb in zip(fa, fb):
            m = CLASS_RE.match(la)
            if m:
                cur, cls = m.group(2), m.group(1)
            x = LEAF_RE.match(la)
            if not x or la == lb or cls in skip_cls:
                continue
            tag, text = x.group(1), x.group(2)
            if len(text) >= 64 or not is_text_field(tag, an_mod):
                continue
            y = LEAF_RE.match(lb)
            if an.stem_re is not None and y:
                for mm in an.stem_re.finditer(text):
                    checked_stem += 1
                    if an.stem_map[mm.group()] not in y.group(2):
                        bad_stem += 1
            if tag == NAME_TAG and y and cur:
                ids[cur] = (text, y.group(2))
    r.check('одно и то же слово заменяется одним и тем же значением во всех местах', bad_stem == 0,
            f'({checked_stem:,} вхождений проверено)' if not bad_stem else f'(расхождений: {bad_stem})')
    # (б) если имя объекта входит в имя ссылающегося на него объекта, то и после замены входит
    edges = bad_edge = 0
    obj_id = old_name = new_name = None
    refs = []
    with open(a, encoding='utf-8', newline='') as fa, open(b, encoding='utf-8', newline='') as fb:
        for la, lb in zip(fa, fb):
            m = CLASS_RE.match(la)
            if m:
                obj_id, refs = m.group(2), []
                old_name, new_name = ids.get(obj_id, (None, None))
            elif 'rdf:resource' in la:
                refs += RES_RE.findall(la)
            elif la.startswith('  </') and old_name:
                for rid in refs:
                    tgt = ids.get(rid)
                    if tgt and len(tgt[0]) >= 6 and re.search('[A-Za-zА-Яа-я]', tgt[0]) and tgt[0] in old_name and tgt[0] != old_name:
                        edges += 1
                        if tgt[1] not in new_name:
                            bad_edge += 1
                obj_id = old_name = None
    r.check('имя объекта, входящее в имя ссылающегося объекта, остаётся его частью', bad_edge == 0,
            f'({edges:,} связей проверено)' if not bad_edge else f'(расхождений: {bad_edge} из {edges:,})')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src'); ap.add_argument('dst')
    ap.add_argument('--salt', default=os.environ.get('ANON_SALT', 'verify'), help='соль обезличивания (нужна для этапа names)')
    ap.add_argument('--stage', choices=['all', 'orig', 'result', 'leak', 'blobs', 'names'], default='all')
    a = ap.parse_args()
    cache = os.path.join(os.path.dirname(os.path.abspath(a.src)), '.verify_orig.pkl')
    r = Report()
    if a.stage == 'orig':
        pickle.dump(scan(a.src), open(cache, 'wb')); print('оригинал отсканирован'); return 0
    if a.stage in ('all', 'result'):
        A = pickle.load(open(cache, 'rb')) if os.path.exists(cache) else scan(a.src)
        structural(A, scan(a.dst), r)
    if a.stage in ('all', 'leak'):
        leaks(a.src, a.dst, r)
    if a.stage in ('all', 'blobs'):
        blobs(a.src, a.dst, a.salt, r)
    if a.stage in ('all', 'names'):
        names(a.src, a.dst, a.salt, r)
    return 0 if Report.ok else 1


if __name__ == '__main__':
    sys.exit(main())

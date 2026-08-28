#!/usr/bin/env python3
"""R1c phase 2: the tie premises `icfg_X = icfg_X ->` that de-threading left
behind, and the `intros` names and call-site arguments that go with them."""
import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import strip_comments, parse_binders, declarations, skip_ws, OPEN, CLOSE
from premise import body_start, skip_lets, premises, TIE
from rewrite import args_of, IDCHAR

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.environ.get('R1C_IRIS') or os.path.join(SCR, '..', 'iris')
IDRE = '[' + IDCHAR + ']+'


def scan(path):
    raw = open(path, encoding='utf-8').read()
    t = strip_comments(raw)
    out = []
    for kind, name, nspan, regions, dstart in declarations(t):
        bs = []
        for (lo, hi) in regions:
            bs += parse_binders(t, lo, hi)
        nargs = sum(len(b['names']) for b in bs if b['kind'] == 'explicit')
        i = body_start(t, kind, regions)
        i, nlets = skip_lets(t, i)
        ps = premises(t, i)
        ties = [(idx, s, e, ae, TIE.match(t[s:e]).group(1))
                for idx, (s, e, ae) in enumerate(ps) if TIE.match(t[s:e])]
        head = None
        m = re.match(IDRE, t[skip_ws(t, i):])
        if m:
            head = m.group(0)
        out.append({'kind': kind, 'name': name, 'nargs': nargs, 'nlets': nlets,
                    'ties': ties, 'npr': len(ps), 'head': head,
                    'dstart': dstart, 'bodyi': i, 'regions': regions})
    return raw, t, out


def proof_span(t, d):
    """(start, end) of the declaration's Proof ... Qed, or None."""
    i = d['bodyi']
    depth, n = 0, len(t)
    while i < n:
        c = t[i]
        if c == '"':
            j = t.find('"', i + 1)
            i = (j + 1) if j >= 0 else n
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == '.' and depth <= 0 and (i + 1 >= n or t[i+1] in ' \n\t\r'):
            break
        i += 1
    j = skip_ws(t, i + 1)
    if not t.startswith('Proof', j):
        return None
    m = re.search(r'\b(Qed|Defined|Admitted|Abort)\.', t[j:])
    if not m:
        return None
    return (j + 5, j + m.start())


def main():
    mode = sys.argv[1]
    cut = [l.strip() for l in open(os.path.join(SCR, 'cut.txt')) if l.strip()]
    allf = sorted(set(re.findall(
        r'([A-Za-z0-9_]+)\.v',
        '\n'.join(l for l in open(os.path.join(IRIS, '_CoqProject'), encoding='utf-8')
                  if not l.lstrip().startswith('#')))))

    info = {}
    bodymap = {}
    bodylets = {}
    for b in cut:
        raw, t, decls = scan(os.path.join(IRIS, b + '.v'))
        info[b] = decls
        for d in decls:
            if d['ties']:
                bodymap[d['name']] = [x[0] for x in d['ties']]
                bodylets[d['name']] = d['nlets']

    # link: a declaration whose statement IS an application of a tied body
    # inherits its tie indices (position = own nargs + index).
    local = collections.defaultdict(dict)
    table = {}

    def record(b, nm, nargs, idxs):
        local[b][nm] = (nargs, idxs)
        if nm not in table or b.startswith('Spec') or b.startswith('Fs'):
            table[nm] = (nargs, idxs)

    for b in cut:
        for d in info[b]:
            if d['ties']:
                record(b, d['name'], d['nargs'], [x[0] for x in d['ties']])
            elif d['head'] in bodymap and d['npr'] == 0:
                record(b, d['name'], d['nargs'], bodymap[d['head']])

    if mode == 'table':
        for k in sorted(table):
            print(k, table[k])
        print('tied declarations:', len(table), file=sys.stderr)
        return

    names = sorted(table, key=len, reverse=True)
    headre = re.compile('(?<![' + IDCHAR + r'.])((?:[' + IDCHAR + r']+\.)*)(' +
                        '|'.join(re.escape(n) for n in names) + ')(?![' + IDCHAR + '])')
    OKARG = re.compile(r"^(eq_refl|_|H[" + IDCHAR + r"]*|ltac:\(.*\)|\(.*\))$", re.S)

    stats = collections.Counter()
    problems = []
    for b in allf:
        p = os.path.join(IRIS, b + '.v')
        if not os.path.exists(p):
            continue
        raw = open(p, encoding='utf-8').read()
        t = strip_comments(raw)
        declnames, declared_here = set(), set()
        for kind, nmx, nspan, regions, dstart in declarations(t):
            declnames.add(nspan)
            declared_here.add(nmx)
        edits = []
        for m in headre.finditer(t):
            nm = m.group(2)
            if m.span(2) in declnames:
                continue
            if m.group(1) == '':
                if nm in local[b]:
                    nargs, idxs = local[b][nm]
                elif nm in declared_here:
                    continue
                else:
                    nargs, idxs = table[nm]
            else:
                nargs, idxs = table[nm]
            args = args_of(t, m.end(), len(t))
            want = nargs + max(idxs)
            if len(args) <= want:
                stats['skipped'] += 1
                problems.append('SKIP %s:%d %s: %d args, want %d' %
                                (b, t[:m.start()].count('\n') + 1, nm, len(args), want))
                continue
            for k in idxs:
                a = t[args[nargs + k][0]:args[nargs + k][1]]
                if not OKARG.match(a):
                    problems.append('%s:%d %s: tie arg %r' %
                                    (b, t[:m.start()].count('\n') + 1, nm, a))
            for k in idxs:
                s, e = args[nargs + k]
                s2 = s
                while s2 > 0 and t[s2-1] in ' ':
                    s2 -= 1
                edits.append((s2 if s2 < s else s, e, ''))
            stats['apps'] += 1
        if b in cut:
            for d in info[b]:
                for (idx, s, e, ae, fld) in d['ties']:
                    s2 = s
                    while s2 > 0 and t[s2-1] in ' \n':
                        s2 -= 1
                    edits.append((s2, ae, ''))
                    stats['premises'] += 1
                # ---- the proof's `intros`: drop the name the premise got
                idxs = None
                off = 0
                if d['ties']:
                    idxs = [x[0] for x in d['ties']]
                    off = d['nlets']
                elif d['head'] in bodymap and d['npr'] == 0:
                    idxs = bodymap[d['head']]
                if idxs is None:
                    continue
                pe = proof_span(t, d)
                if pe is None:
                    continue
                ps_, pend = pe
                cbv = re.search(r'cbv[^.]*\bdelta\b[^.]*\.', t[ps_:pend])
                if cbv:
                    if 'zeta' in t[ps_ + cbv.start():ps_ + cbv.end()]:
                        off = 0
                    else:
                        off = bodylets.get(d['head'], d['nlets'])
                    q = ps_ + cbv.end()
                else:
                    q = ps_
                mi = re.search(r'\bintros\b', t[q:pend])
                if not mi:
                    problems.append('%s %s: no intros found' % (b, d['name']))
                    continue
                istart = q + mi.end()
                iend = istart
                while iend < pend and t[iend] != '.':
                    iend += 1
                toks = [(m.group(0), (istart + m.start(), istart + m.end()))
                        for m in re.finditer('[' + IDCHAR + ']+|_', t[istart:iend])]
                for k in idxs:
                    j = off + k
                    if j >= len(toks):
                        problems.append('%s %s: intros has %d names, want %d'
                                        % (b, d['name'], len(toks), j + 1))
                        continue
                    nm2, (a, bnd) = toks[j]
                    a2 = a
                    while a2 > 0 and t[a2-1] in ' ':
                        a2 -= 1
                    edits.append((a2 if a2 < a else a, bnd, ''))
                    stats['intros'] += 1
                    live = []
                    for mu in re.finditer('(?<![' + IDCHAR + '])' + re.escape(nm2)
                                          + '(?![' + IDCHAR + '])', t[bnd:pend]):
                        us, ue = bnd + mu.start(), bnd + mu.end()
                        if any(x <= us and ue <= y for (x, y, _) in edits):
                            continue
                        live.append(t[:us].count('\n') + 1)
                    if live:
                        problems.append('%s %s: dropped intro %r still used at %s'
                                        % (b, d['name'], nm2, live[:6]))
        if not edits:
            continue
        edits.sort(key=lambda x: (-x[0], -x[1]))
        out = raw
        last = len(raw) + 1
        for (s, e, r) in edits:
            if e > last:
                problems.append('%s: overlapping edit %d-%d' % (b, s, e))
                continue
            out = out[:s] + r + out[e:]
            last = s
        if mode == 'apply':
            open(p, 'w', encoding='utf-8').write(out)
        stats['files'] += 1

    print('stats:', dict(stats), file=sys.stderr)
    for x in problems:
        print('  ', x, file=sys.stderr)


main()

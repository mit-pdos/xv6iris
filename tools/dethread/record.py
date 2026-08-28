#!/usr/bin/env python3
"""Take FIELDS off a names record whose value is now an ambient config field.

    python3 tools/dethread/record.py apply <RecordFile.v> <Record> <Mk> \
        field=fsc_x field=fsc_y ...

Three edits, tree-wide over `_CoqProject`:
  * the `Record`'s own field lines go;
  * every POSITIONAL application of the constructor loses those arguments
    (the `Inhabited` witness is one of these), and every `{| f := v |}`
    record-syntax construction loses those fields;
  * every projection application `f e` becomes the ambient field name.
Anything it cannot parse is REPORTED, never guessed -- in particular a
projection named inside a `cbn [...]` / `simpl [...]` delta list, which has
no argument and must be removed by hand.
"""
import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import strip_comments, declarations, skip_ws, OPEN, CLOSE, match_group
from rewrite import args_of, IDCHAR

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.environ.get('R1C_IRIS') or os.path.join(SCR, '..', 'iris')


def tokre(tok):
    return re.compile('(?<![' + IDCHAR + '.])' + re.escape(tok) + '(?![' + IDCHAR + '])')


def main():
    mode, recfile, recname, mkname = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    drop = dict(a.split('=') for a in sys.argv[5:])

    # ---- 1. the record's own field list, and the field ORDER -------------
    p = os.path.join(IRIS, recfile)
    raw = open(p, encoding='utf-8').read()
    t = strip_comments(raw)
    m = re.search(r'(?:^|\n)\s*Record\s+' + re.escape(recname) + r'\b', t)
    assert m, 'no Record ' + recname
    b = t.index('{', m.end())
    e = match_group(t, b)
    body = t[b + 1:e]
    fields = [(mm.group(1), b + 1 + mm.start(), b + 1 + mm.end())
              for mm in re.finditer(r'(?:^|\n)\s*(' + '[' + IDCHAR + ']+' + r')\s*:[^;]*;',
                                    body)]
    order = [f for f, _, _ in fields]
    for f in drop:
        assert f in order, (f, order)
    idx = sorted(order.index(f) for f in drop)
    print('record %s: %d fields, dropping %s at %s' % (recname, len(order),
                                                       sorted(drop), idx))

    # delete the field lines (on the RAW text: same offsets, comments blanked)
    cuts = [(s, en) for (f, s, en) in fields if f in drop]
    out = raw
    for (s, en) in sorted(cuts, reverse=True):
        s2 = s
        while s2 > 0 and out[s2 - 1] in ' \t':
            s2 -= 1
        if s2 > 0 and out[s2 - 1] == '\n':
            s2 -= 1
        out = out[:s2] + out[en:]
    if mode == 'apply':
        open(p, 'w', encoding='utf-8').write(out)

    # ---- 2 & 3. the tree ------------------------------------------------
    allf = sorted(set(re.findall(
        r'([A-Za-z0-9_]+)\.v',
        '\n'.join(l for l in open(os.path.join(IRIS, '_CoqProject'), encoding='utf-8')
                  if not l.lstrip().startswith('#')))))
    stats = collections.Counter()
    problems = []
    # the record's OWN declaration span: its constructor name and its field
    # declarations are not applications and must not be looked at.  RECOMPUTED
    # on the post-edit text -- deleting the fields moved every later offset,
    # and a stale span silently swallows the Inhabited witness below it.
    t2 = strip_comments(out)
    m2 = re.search(r'(?:^|\n)\s*Record\s+' + re.escape(recname) + r'\b', t2)
    b2 = t2.index('{', m2.end())
    own = (m2.start(), match_group(t2, b2) + 1)
    mkre = tokre(mkname)
    projres = {f: tokre(f) for f in drop}
    recsyn = re.compile(r'(?<![' + IDCHAR + r'.])(' + '|'.join(re.escape(f) for f in drop) +
                        r')\s*:=')
    for bnm in allf:
        q = os.path.join(IRIS, bnm + '.v')
        if not os.path.exists(q):
            continue
        raw = open(q, encoding='utf-8').read()
        t = strip_comments(raw)
        edits = []
        # -- constructor applications
        for mm in mkre.finditer(t):
            if bnm + '.v' == recfile and own[0] <= mm.start() < own[1]:
                continue
            args = args_of(t, mm.end(), len(t))
            if len(args) <= max(idx):
                problems.append('%s:%d %s: only %d args' %
                                (bnm, t[:mm.start()].count('\n') + 1, mkname, len(args)))
                continue
            for k in idx:
                s, en = args[k]
                s2 = s
                while s2 > 0 and t[s2 - 1] == ' ':
                    s2 -= 1
                edits.append((s2 if s2 < s else s, en, ''))
            stats['mk'] += 1
        # -- record syntax  {| f := v; ... |}
        for mm in recsyn.finditer(t):
            j = mm.end()
            depth, k = 0, j
            while k < len(t):
                c = t[k]
                if c in OPEN:
                    depth += 1
                elif c in CLOSE:
                    if depth == 0:
                        break
                    depth -= 1
                elif depth == 0 and c == ';':
                    break
                elif depth == 0 and t.startswith('|}', k):
                    break
                k += 1
            en = k + 1 if (k < len(t) and t[k] == ';') else k
            s = mm.start()
            while s > 0 and t[s - 1] in ' \t':
                s -= 1
            if s > 0 and t[s - 1] == '\n':
                s -= 1
            edits.append((s, en, ''))
            stats['recsyn'] += 1
        # -- projection applications
        for f, r in projres.items():
            for mm in r.finditer(t):
                if bnm + '.v' == recfile and own[0] <= mm.start() < own[1]:
                    continue
                args = args_of(t, mm.end(), len(t))
                if not args:
                    problems.append('%s:%d %s: projection with no argument' %
                                    (bnm, t[:mm.start()].count('\n') + 1, f))
                    continue
                s, en = mm.start(), args[0][1]
                edits.append((s, en, drop[f]))
                stats['proj'] += 1
        if not edits:
            continue
        edits.sort(key=lambda x: (-x[0], -x[1]))
        o = raw
        last = len(raw) + 1
        for (s, en, rep) in edits:
            if en > last:
                problems.append('%s: overlapping edit at %d-%d' % (bnm, s, en))
                continue
            o = o[:s] + rep + o[en:]
            last = s
        if mode == 'apply':
            open(q, 'w', encoding='utf-8').write(o)
        stats['files'] += 1
    print('stats:', dict(stats))
    if problems:
        print('PROBLEMS (%d):' % len(problems))
        for x in problems:
            print('  ', x)


main()

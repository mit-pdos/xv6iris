#!/usr/bin/env python3
"""Remove the `rewrite`s that the tie premises fed.  A tie hypothesis now has
type `icfg_X = icfg_X`, so every rewrite by it is a no-op Rocq REFUSES; the
tactic goes with the premise."""
import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import strip_comments, OPEN, CLOSE

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.environ.get('R1C_IRIS') or os.path.join(SCR, '..', 'iris')
IDCHAR = "A-Za-z0-9_'Ͱ-Ͽἀ-῿"

# (file, declaration, hypothesis) triples, read off phase2's report.  The
# search is restricted to the DECLARATION's own span: the same hypothesis name
# elsewhere in the file is a different hypothesis.
from dethread import declarations
targets = collections.defaultdict(lambda: collections.defaultdict(set))
for line in open(os.environ.get('R1C_USED') or os.path.join(SCR, 'used.txt'), encoding='utf-8'):
    m = re.match(r"(\S+) (\S+): dropped intro '(\S+)'", line.strip())
    if m:
        targets[m.group(1)][m.group(2)].add(m.group(3))


def spans(t, wanted):
    """{decl name: (start, end)} for the wanted declarations"""
    out = {}
    for kind, name, nspan, regions, dstart in declarations(t):
        if name not in wanted:
            continue
        i = regions[-1][1]
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
        mm = re.search(r'\b(Qed|Defined|Admitted|Abort)\.', t[i:])
        out[name] = (i, i + mm.start() if mm else n)
    return out

STOP = set(';.)]|')

def strings_mask(raw):
    """spans of "..." string literals"""
    out = []
    i = 0
    while True:
        a = raw.find('"', i)
        if a < 0:
            break
        b = raw.find('"', a + 1)
        if b < 0:
            break
        out.append((a, b + 1))
        i = b + 1
    return out

mode = sys.argv[1] if len(sys.argv) > 1 else 'dry'
total, left = 0, []
for f, decls in sorted(targets.items()):
    p = os.path.join(IRIS, f + '.v')
    raw = open(p, encoding='utf-8').read()
    t = strip_comments(raw)
    masks = strings_mask(t)
    sp = spans(t, set(decls))
    edits = []
    for dname, hyps in decls.items():
        if dname not in sp:
            left.append('%s %s: declaration not found' % (f, dname))
            continue
        lo, hi = sp[dname]
        for h in hyps:
          for m in re.finditer('(?<![' + IDCHAR + '])' + re.escape(h) + '(?![' + IDCHAR + '])', t, ):
            s, e = m.span()
            if not (lo <= s < hi):
                continue
            if any(a <= s < b for (a, b) in masks):
                continue
            # walk back to the head of the rewrite, over other rewrite terms
            j = s
            while j > 0:
                k = j - 1
                while k > 0 and t[k] in ' \n\t':
                    k -= 1
                if k <= 0 or t[k] in STOP:
                    j = -1
                    break
                # a term: an identifier(-ish) or a ')' group or a '-'/'<-'
                if t[k] == ')':
                    d, kk = 0, k
                    while kk >= 0:
                        if t[kk] in CLOSE:
                            d += 1
                        elif t[kk] in OPEN:
                            d -= 1
                            if d == 0:
                                break
                        kk -= 1
                    j = kk
                    continue
                a = k
                while a > 0 and re.match('[' + IDCHAR + '<>-]', t[a-1]):
                    a -= 1
                w = t[a:k+1]
                if w == 'rewrite':
                    j = a
                    break
                if not re.fullmatch('[' + IDCHAR + '<>-]+', w):
                    j = -1
                    break
                j = a
            if j < 0:
                left.append('%s:%d %s' % (f, t[:s].count('\n') + 1, h))
                continue
            rw = j                     # index of 'rewrite'
            # the rewrite's term list ends at the first STOP char at depth 0
            # or at a bare `in`
            q = rw + 7
            depth = 0
            while q < len(t):
                c = t[q]
                if c in OPEN:
                    depth += 1
                elif c in CLOSE:
                    if depth == 0:
                        break
                    depth -= 1
                elif depth == 0 and c in ';.':
                    break
                elif depth == 0 and re.match(r'\bin\b', t[q:q+2]) and t[q-1] in ' \n' \
                        and t[q+2:q+3] in (' ', '\n'):
                    break
                q += 1
            terms = t[rw+7:q]
            others = [x for x in re.findall('[' + IDCHAR + ']+', terms) if x != h]
            if others:
                # drop just this term (with a leading `-`/`<-`)
                a = s
                while a > 0 and t[a-1] in '-<':
                    a -= 1
                while a > 0 and t[a-1] == ' ':
                    a -= 1
                edits.append((a, e))
                total += 1
                continue
            # the whole rewrite goes -- with its `iEval (...)` wrapper if any
            a, b = rw, q
            pre = t[:rw].rstrip()
            if pre.endswith('iEval ('):
                a = len(pre) - 7
                b = q + 1 if q < len(t) and t[q] in CLOSE else q
                # `in "X"` after the closing paren
                mi = re.match(r'\s*in\s*"[^"]*"', t[b:])
                if mi:
                    b += mi.end()
            elif pre.endswith('iEval('):
                a = len(pre) - 6
                b = q + 1 if q < len(t) and t[q] in CLOSE else q
                mi = re.match(r'\s*in\s*"[^"]*"', t[b:])
                if mi:
                    b += mi.end()
            # swallow the terminating `;` or `.` and the space after it
            if b < len(t) and t[b] in ';.':
                b += 1
                while b < len(t) and t[b] == ' ':
                    b += 1
            while a > 0 and t[a-1] == ' ':
                a -= 1
            if a > 0 and t[a-1] == '\n' and t[b-1:b] != ' ':
                pass
            edits.append((a, b))
            total += 1
    if not edits:
        continue
    edits = sorted(set(edits), reverse=True)
    out = raw
    last = len(raw) + 1
    for (a, b) in edits:
        if b > last:
            left.append('%s: overlap %d-%d' % (f, a, b))
            continue
        out = out[:a] + out[b:]
        last = a
    if mode == 'apply':
        open(p, 'w', encoding='utf-8').write(out)
print('rewrites removed:', total)
for x in left:
    print('  LEFT', x)

#!/usr/bin/env python3
"""Remove the blank lines the binder deletions left INSIDE a declaration's
binder list.  Nothing outside a binder region is touched."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import strip_comments, declarations

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.environ.get('R1C_IRIS') or os.path.join(SCR, '..', 'iris')

n = 0
for b in [l.strip() for l in open(os.path.join(SCR, 'cut.txt')) if l.strip()]:
    p = os.path.join(IRIS, b + '.v')
    raw = open(p, encoding='utf-8').read()
    t = strip_comments(raw)
    kill = []
    for kind, name, nspan, regions, dstart in declarations(t):
        for (lo, hi) in regions:
            for m in re.finditer(r'\n[ \t]*(?=\n)', raw[lo:hi]):
                kill.append((lo + m.start(), lo + m.end()))
    if not kill:
        continue
    kill.sort(reverse=True)
    for (s, e) in kill:
        raw = raw[:s] + raw[e:]
    open(p, 'w', encoding='utf-8').write(raw)
    n += len(kill)
print('blank binder lines removed:', n)

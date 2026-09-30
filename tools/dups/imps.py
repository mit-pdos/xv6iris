#!/usr/bin/env python3
"""usage: imps.py MOD [TARGET...]  -- print whether MOD transitively imports each TARGET
   imps.py --rdeps MOD            -- modules that transitively import MOD"""
import os, re, sys, functools
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def path(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
@functools.lru_cache(None)
def direct(m):
    p = path(m)
    if not os.path.exists(p): return ()
    out = []
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'\s*import\s+(.*)', line)
        if mm: out += mm.group(1).split()
    return tuple(out)
@functools.lru_cache(None)
def closure(m):
    s = set()
    for d in direct(m):
        s.add(d); s |= closure(d)
    return frozenset(s)
def allmods():
    for top in ('Xv6', 'MachCSL'):
        for dp, _, fs in os.walk(os.path.join(ROOT, top)):
            for f in fs:
                if f.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(dp, f), ROOT)[:-5]
                    yield rel.replace(os.sep, '.')
if sys.argv[1] == '--rdeps':
    t = sys.argv[2]
    for m in sorted(allmods()):
        if t in closure(m): print(m)
else:
    m = sys.argv[1]
    for t in sys.argv[2:]:
        print(t, t in closure(m))

"""Declarations in the cut with UNTYPED binders whose name is one of the
sweep's target names -- the parser cannot classify them, so they need a
MANUAL entry."""
import sys, os, re, collections
SCR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCR)
from dethread import strip_comments, parse_binders, declarations, TARGET
IRIS = os.environ.get('R1C_IRIS')
NAMES = set(n for (n, _) in TARGET)
cut = [l.strip() for l in open(os.path.join(SCR, 'cut.txt')) if l.strip()]
extra = os.environ.get('R1D_EXTRA', '')
cut += [x for x in extra.split() if x]
for b in cut:
    p = os.path.join(IRIS, b + '.v')
    t = strip_comments(open(p, encoding='utf-8').read())
    for kind, name, nspan, regions, dstart in declarations(t):
        bs = []
        for (lo_, hi_) in regions:
            bs += parse_binders(t, lo_, hi_)
        hit = set()
        for bd in bs:
            if bd['kind'] != 'explicit':
                continue
            ty = bd['type']
            if ty is not None and ty.strip():
                continue
            for nm, sp in bd['names']:
                if nm in NAMES:
                    hit.add(nm)
        if hit:
            print("    ('%s.v', '%s'): %s," % (b, name, sorted(hit)))

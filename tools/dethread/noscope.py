"""Which declarations in the cut would name an fsc_* field with no [fscfg]
in scope (rank 1b's memory bomb)?  Those keep their parameters."""
import sys, os, re
SCR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCR)
sys.path.insert(0, os.path.join(SCR, '..'))
from dethread import strip_comments, parse_binders, declarations, TARGET
import dethread_check as C

IRIS = os.environ.get('R1C_IRIS')
cut = [l.strip() for l in open(os.path.join(SCR, 'cut.txt')) if l.strip()]
extra = os.environ.get('R1D_EXTRA', '')
cut += [x for x in extra.split() if x]
for b in cut:
    p = os.path.join(IRIS, b + '.v')
    t = strip_comments(open(p, encoding='utf-8').read())
    ev = C.scopes(t)
    for kind, name, nspan, regions, dstart in declarations(t):
        bs = []
        for (lo_, hi_) in regions:
            bs += parse_binders(t, lo_, hi_)
        hit = set()
        for bd in bs:
            if bd['kind'] != 'explicit':
                continue
            ty = (bd['type'] or '').strip()
            for nm, sp in bd['names']:
                if (nm, ty) in TARGET:
                    hit.add(TARGET[(nm, ty)])
        if not hit:
            continue
        hi, hf = C.in_scope(ev, dstart)
        # the declaration's own binder group may carry the class
        own = ''.join(t[a:b2] for a, b2 in regions)
        hi = hi or bool(C.HAS_ICFG.search(own))
        hf = hf or bool(C.HAS_FSCFG.search(own))
        need_i = any(f.startswith('icfg_') for f in hit)
        need_f = any(f.startswith('fsc_') for f in hit)
        if (need_i and not hi) or (need_f and not hf):
            print("    ('%s.v', '%s')," % (b, name), '#', sorted(hit),
                  'icfg=%s fscfg=%s' % (hi, hf))

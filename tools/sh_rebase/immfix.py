"""For every instruction whose encoding changed, rewrite its OLD immediate to the new one on
lines that mention its (new) pc, and list what else mentions the old immediate."""
import re, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import OLD, OLDPC, NEWPC, amap, R
from rvdec import decode

IMM = re.compile(r'(-?\d+#\d+)')
changes = []
for a, w, e, s in OLD:
    n = amap(a)
    if n is None:
        continue
    nw, ne, ns = NEWPC[n]
    if ne != e:
        do, dn = decode(e, w), decode(ne, nw)
        io = IMM.findall(do); inn = IMM.findall(dn)
        assert len(io) >= 1 and len(io) == len(inn), (do, dn)
        diffs = [(x, y) for x, y in zip(io, inn) if x != y]
        changes.append((a, n, diffs))
files = [l.strip() for l in open(sys.argv[1])]
apply = '--apply' in sys.argv
for f in files:
    lines = open(os.path.join(R, f)).read().split('\n')
    changed = False
    for i, l in enumerate(lines):
        for a, n, diffs in changes:
            if re.search(r'(?<![\w])0x%x(?![\w])' % n, l):
                for x, y in diffs:
                    if re.search(r'(?<![\w#])%s(?![\w])' % re.escape(x), l):
                        l2 = re.sub(r'(?<![\w#])%s(?![\w])' % re.escape(x), y, l)
                        print('%s:%d  %#x %s -> %s' % (f, i + 1, n, x, y))
                        l = l2; changed = True
        lines[i] = l
    if changed and apply:
        open(os.path.join(R, f), 'w').write('\n'.join(lines))

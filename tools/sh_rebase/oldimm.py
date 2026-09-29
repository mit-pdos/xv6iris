"""Report every remaining occurrence of an OLD changed immediate in sh files."""
import re, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import OLD, NEWPC, amap, R
from rvdec import decode
IMM = re.compile(r'(-?\d+#\d+)')
ch = {}
for a, w, e, s in OLD:
    n = amap(a)
    if n is None: continue
    nw, ne, ns = NEWPC[n]
    if ne != e:
        for x, y in zip(IMM.findall(decode(e, w)), IMM.findall(decode(ne, nw))):
            if x != y: ch.setdefault(x, set()).add((y, hex(a), hex(n)))
files = [l.strip() for l in open(sys.argv[1])]
for f in files:
    for i, l in enumerate(open(os.path.join(R, f)), 1):
        for x in ch:
            if re.search(r'(?<![\w#])%s(?![\w])' % re.escape(x), l):
                print('%s:%d  %s -> %s  | %s' % (f, i, x, sorted(ch[x]), l.strip()[:120]))

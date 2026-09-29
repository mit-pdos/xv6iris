import os, sys, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import OLD, OLDPC, NEWPC, amap
from rvdec import bits, sext

def auipcs(tab):
    out = {}
    for a, w, e, s in tab:
        if w == 4 and (e & 0x7f) == 0x17:
            out[a] = a + (sext(bits(e, 31, 12), 20) << 12)
    return out

OT = auipcs(OLD)
TEMPS = {}
for a, v in OT.items():
    n = amap(a)
    if n is None:
        continue
    nv = n + (v - a)
    TEMPS[v] = nv
if __name__ == '__main__':
    for v, nv in sorted(TEMPS.items()):
        coll = []
        if v in OLDPC: coll.append('INSTR')
        if 0x1288 <= v < 0x13f0: coll.append('RO->%#x' % amap(v))
        print('%#x -> %#x %s' % (v, nv, ' '.join(coll)))

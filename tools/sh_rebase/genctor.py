import os, sys, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import NEW, R
from rvdec import decode
p = os.path.join(R, 'Xv6', 'UshCode.lean')
s = open(p).read()
a = s.index('/-! ## execcmd/redircmd/pipecmd -/')
b = s.index('/-! ## gettoken..parseline -/')
L = ['/-! ## cmdalloc/execcmd/redircmd/pipecmd -/\n']
for pc, w, e, asm in NEW:
    if 0x1d2 <= pc < 0x29e:
        d = decode(e, w)
        assert d, hex(pc)
        L.append("/-- `%#x  %s` -/\ntheorem ushI_%03x (γt : GName) :\n    ushCode (GF := GF) γt ⊢ uinstrIs γt (BitVec.ofNat 64 %#x) %s (%s) :=\n  ushm_uis γt %#x _ _ ⟨_, _, _, rfl⟩ (by decide) (by decide)\n"
                 % (pc, asm.replace('\t', ' '), pc, pc, 'true' if w == 2 else 'false', d, pc))
s = s[:a] + '\n'.join(L) + '\n' + s[b:]
open(p, 'w').write(s)

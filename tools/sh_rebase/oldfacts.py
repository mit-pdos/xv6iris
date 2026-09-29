"""Collect every (pc, rvc, AST) the tree states about sh, and check rvdec on the OLD image."""
import re, glob, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amap import OLDPC, NEWPC, R
from rvdec import decode

def paren_arg(s, i):
    """s[i] == '(' ; return (content, end index after ')')."""
    assert s[i] == '(', s[i:i+20]
    d = 0
    for j in range(i, len(s)):
        if s[j] == '(':
            d += 1
        elif s[j] == ')':
            d -= 1
            if d == 0:
                return s[i + 1:j], j + 1
    raise ValueError

PATS = [re.compile(r'uinstrIs (?:γt|N\.t|[A-Za-z.]+) \(BitVec\.ofNat 64 (0x[0-9a-f]+)\) (true|false) (?=\()'),
        re.compile(r'ushm?_uis (?:γt|N\.t|[A-Za-z.]+) (0x[0-9a-f]+) (true|false) (?=\()')]

def collect(files):
    out = []
    for f in files:
        s = open(f).read()
        for P in PATS:
            for m in P.finditer(s):
                ast, _ = paren_arg(s, m.end())
                out.append((f, int(m.group(1), 16), m.group(2) == 'true', ' '.join(ast.split()), m.start()))
    return out

if __name__ == '__main__':
    files = [f for f in glob.glob(R + '/Xv6/*.lean')]
    facts = collect(files)
    bad = 0; n = 0; sh = 0
    for f, pc, rvc, ast, _ in facts:
        s = open(f).read()
        if not re.search(r'ushCode|ushm_uis|ush_uis|User\.Sh\.', s):
            continue
        if pc not in OLDPC:
            continue
        sh += 1
        w, e, asm = OLDPC[pc]
        d = decode(e, w)
        n += 1
        if d != ast or (w == 2) != rvc:
            bad += 1
            print(os.path.basename(f), hex(pc), asm, '\n   lean:', ast, '\n   py  :', d)
    print('checked', n, 'bad', bad)

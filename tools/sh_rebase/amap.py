"""sh image-bump rebase kit (lane D1-img, xv6 7b2c1b1b -> d66e41c).

Pipeline used for the d66e41c bump (re-runnable for the next sh relayout, after
adjusting `amap.amap`'s regions to the new symbol table):
  1. keep the OLD dumps: cp -r Xv6/User scratch/d1img/User.old ; regenerate the
     new ones with tools/dump_user_elf.py (and fs.img with tools/dump_fs_image.py);
  2. oldfacts.py   -- sanity: rvdec's expanded ASTs == every stated sh fact (old image);
  3. listfiles.py > shfiles.txt ; rewrite.py @shfiles.txt -- re-point pcs, fact names,
     .rodata / auipc temporaries, re-decode every stated AST, fix docstrings;
  4. immfix.py shfiles.txt --apply ; oldimm.py shfiles.txt -- the changed immediates;
  5. genctor.py -- regenerate the facts of a rewritten function range;
  6. fsblocks.py -- the fs.img block layout diff (FsImgFiles pins).
The scripts expect the old dump under scratch/d1img/User.old and the two
binaries under scratch/d1img/{pin,main}/... (amap.D).
"""
"""Old (7b2c1b1b) -> new (d66e41c) sh address map, and instruction tables."""
import re, os
R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
D = os.path.join(R, 'scratch', 'd1img')
ENTRY_RE = re.compile(r'^\s*⟨(0x[0-9a-f]+), (\d+), (0x[0-9a-f]+)⟩,?\s*$')

def instrs(path):
    out = []; asm = None
    for line in open(path):
        m = re.match(r'\s*-- (.*)', line)
        if m: asm = m.group(1); continue
        m = ENTRY_RE.match(line)
        if m: out.append((int(m.group(1), 16), int(m.group(2)), int(m.group(3), 16), asm))
    return out

OLD = instrs(os.path.join(D, 'User.old', 'ShImage.lean'))
NEW = instrs(os.path.join(R, 'Xv6', 'User', 'ShImage.lean'))
OLDPC = {a: (w, e, s) for a, w, e, s in OLD}
NEWPC = {a: (w, e, s) for a, w, e, s in NEW}
OLD_TEXT_END = 0x1286

def amap(a):
    """None = no mapping (the rewritten constructors)."""
    if a < 0x1d2: return a
    if a < 0x310: return None
    if a <= OLD_TEXT_END: return a - 0x24
    if 0x1288 <= a < 0x12e0: return a - 0x20
    if 0x12e0 <= a < 0x1c64: return a - 0x10 if a < 0x13f0 else a + 0x10 - 0x20 + 0x10  # eh_frame: 0x13f0 -> 0x13e0
    if a == 0x1c64: return 0x1c74
    if a >= 0x2000: return a
    return None

if __name__ == '__main__':
    same = diff = 0
    for a, w, e, s in OLD:
        n = amap(a)
        if n is None: continue
        nw, ne, ns = NEWPC[n]
        assert nw == w, hex(a)
        if ne == e: same += 1
        else:
            diff += 1
            print('%5x -> %5x  %-40s | %s' % (a, n, s, ns))
    print('same', same, 'diff', diff)

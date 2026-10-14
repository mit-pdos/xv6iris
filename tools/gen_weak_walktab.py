#!/usr/bin/env python3
"""gen_weak_walktab.py -- W9a (B) B5: the WALK-STATE TABLE generator (Lean).

UNTRUSTED.  For every walk-certifying row of B3's claimed pin set `pinsW9a`
(Weak/WeakRvwmoPinBridge4.lean: the table `pins` of Weak/KernelPins.lean with the one
`ret` row `kexec+0x1b4` demoted), it runs the static checker's all-paths search
(`KernelPinsDef.pdfs`, ported in tools/gen_weak_pins.py as `pdfs`) and records the
VISITED states -- the walk states the alignment `reachesA`/`reachesT` can be at.  The
table is re-checked by Weak/PinWalkTab.lean with `decide +kernel` through the SAME
Lean definitions (`pstep`, `pinStart`, `krole`, `kflowOf`, the Sail decoder): every
row's start state is in its list, the list is CLOSED under `pstep`'s successors, and
every state passes the per-state checks.  A disagreement between this port and the
Lean checker is a failed reflection lemma, never a silently wrong claim.

Usage: tools/gen_weak_walktab.py [--emit] [--check] [--quiet]
   --emit   print the Lean table block (between the GENERATED markers of PinWalkTab.lean)
   --check  regenerate the block and fail if PinWalkTab.lean's differs
"""

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_weak_sites as S   # noqa: E402
import gen_weak_pins as P    # noqa: E402

REPO = S.REPO
OUT = 'Weak/PinWalkTab.lean'
BEGIN = '-- BEGIN GENERATED (tools/gen_weak_walktab.py --emit)'
END = '-- END GENERATED'
CHUNK = 40


def walk_states(FL, own, st0):
    """The visited list of `pdfs` (same DFS order; the states, not the verdict)."""
    seen, work = [], [st0]
    for _ in range(P.DFS_FUEL):
        if not work:
            return seen
        st = work.pop(0)
        if st in seen:
            continue
        ns = P.pstep(FL, own, st)
        if ns is None:
            raise SystemExit('walk fails at 0x%08x' % st[0])
        seen.append(st)
        work = ns + work
    raise SystemExit('DFS fuel exhausted')


def rows_of(img):
    funs, by_addr = P.build_funs(img)
    FL = P.Flat(img)
    demoted = img.syms['kexec'] + 0x1b4
    out = []
    for r in P.classify(img, funs, by_addr):
        if r['witness'] not in ('Ctrl', 'Fence', 'Dep') or r['pc'] == demoted:
            continue
        out.append((r['pc'], r['own'], walk_states(FL, r['own'], P.pin_start(FL, r['pc']))))
    return out


def emit(rows):
    def h(x):
        return '0x%x' % x

    def st(s):
        pc, t, rs = s
        return 'PState.PSt %s [%s] [%s]' % (h(pc), ', '.join(str(x) for x in t),
                                           ', '.join(h(x) for x in rs))
    out = [BEGIN]
    names = []
    for c in range(0, len(rows), CHUNK):
        nm = 'walkRows%d' % (c // CHUNK)
        names.append(nm)
        out.append('def %s : List WRow := [' % nm)
        out.append(',\n'.join('  ⟨%s, %s, [%s]⟩' % (h(pc), 'true' if own else 'false',
                                                    ', '.join(st(s) for s in sts))
                              for pc, own, sts in rows[c:c + CHUNK]))
        out.append(']')
        out.append('')
    out.append('/-- THE WALK-STATE TABLE: per walk-certifying row of `pinsW9a`, in table order, the')
    out.append('load pc, the `own` bit and the states the all-paths search visits. -/')
    out.append('def walkRows : List WRow :=')
    out.append('  ' + ' ++ '.join(names))
    out.append('')
    for i, nm in enumerate(names):
        out.append('theorem walkRowsOk%d : %s.all rowOk = true := by decide +kernel' % (i, nm))
    out.append('')
    out.append('/-- Every row of the table passes the closure and per-state checks. -/')
    out.append('theorem walkRowsOk : walkRows.all rowOk = true := by')
    out.append('  simp only [walkRows, List.all_append, %s, Bool.and_self]'
               % ', '.join('walkRowsOk%d' % i for i in range(len(names))))
    out.append(END)
    return '\n'.join(out) + '\n'


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', default='Xv6/KernelImage.lean')
    ap.add_argument('--elf', default='MachCSL/KernelElf.lean')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args(argv)
    os.chdir(REPO)
    img = S.Image(a.image, a.elf)
    rows = rows_of(img)
    block = emit(rows)
    if a.emit:
        sys.stdout.write(block)
        return 0
    if a.check:
        src = open(OUT, encoding='utf-8').read()
        m = re.search(re.escape(BEGIN) + r'.*?' + re.escape(END) + r'\n', src, re.S)
        ok = m is not None and m.group(0) == block
        print('gen_weak_walktab --check: %s' % ('ok' if ok else 'FAIL'))
        return 0 if ok else 1
    if not a.quiet:
        n = sum(len(s) for _, _, s in rows)
        pcs = set(x[0] for _, _, s in rows for x in s)
        print('walk-state table over xv6-riscv %s: %d walk-certifying rows, %d states '
              '(%d distinct pcs), largest walk %d states'
              % (img.rev, len(rows), n, len(pcs), max(len(s) for _, _, s in rows)))
    return 0


if __name__ == '__main__':
    sys.exit(main())

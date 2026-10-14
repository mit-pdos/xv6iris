#!/usr/bin/env python3
"""gen_weak_trapsites.py -- W9a (B) B2-census: the TRAP-PATH census generator (Lean).

UNTRUSTED.  It computes, over the tracked kernel image, the per-function fence-free summaries
and the tables that Weak/PinTrapSites.lean re-checks with `decide +kernel` through the SAME
decoders (`KernelPinsDef.kflowOf`, `krole`, `KernelSitesDef.kw`); a disagreement is a failed
reflection lemma, never a silently wrong claim.  It also prints the census report (the trap paths,
the pre-fence exit table by class, the fence-free region).

THE WALK (Weak/PinTrapSites.lean `tstep`, ported here as `tstep`).  A trap path starts at
`kernelvec` (the direct-mode `stvec`) and is followed until its FIRST COVERING FENCE -- a `fence`
whose predecessor set has R and whose successor set has W (riscv.cat ppo rule 4 then orders every
po-earlier read before every po-later write) -- or until `kernelvec`'s `sret`, or until a call
to `swtch` (the hart leaves the thread's context).  Calls are summarised per function: a callee
contributes its return point as a successor only if it MAY RETURN fence-free (`ret`), and a call
edge carries `swt` if the callee may reach `swtch` fence-free.  The one indirect call on a trap
path, `uartintr+0x5a` (`c.jalr a5`, the port's rx hook), is resolved to `consoleintr`
(`Xv6.uartRxHook`: port 0's hook is `consoleintr`, port 1's is 0 and the `beqz` before the
`jalr` skips it).  Every other indirect transfer FAILS the walk.

Usage: tools/gen_weak_trapsites.py [--emit] [--check] [--quiet]
   --emit   print the Lean table block (between the GENERATED markers of PinTrapSites.lean)
   --check  regenerate the block and fail if PinTrapSites.lean's differs
"""

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_weak_sites as S   # noqa: E402
import gen_weak_pins as P    # noqa: E402

REPO = S.REPO
OUT = 'Weak/PinTrapSites.lean'
BEGIN = '-- BEGIN GENERATED (tools/gen_weak_trapsites.py --emit)'
END = '-- END GENERATED'


def covering(w):
    return S.is_fence(w) and bool(S.fence_pred(w) & 2) and bool(S.fence_succ(w) & 1)


class Census:
    def __init__(self, img):
        self.img = img
        sy = img.syms
        self.kv = sy['kernelvec']
        self.sret = self.kv + 0x4c
        self.swtch = sy['swtch']
        self.hook = sy['uartintr'] + 0x5a
        self.hook_tgt = sy['consoleintr']
        self.resume = sy['scheduler'] + 0x7a
        self.summ = {}          # entry -> [ret, swt]
        self.reach = {}
        self.free = {}

    def word(self, pc):
        return self.img.word(pc) if self.img.lo <= pc < self.img.hi else None

    def call(self, tgt, ra):
        if tgt not in self.summ:
            self.summ[tgt] = [False, False]
            self.changed = True
        ret, swt = self.summ[tgt]
        return ('next', [ra] if ret else [], swt)

    def tstep(self, pc):
        w = self.word(pc)
        if w is None:
            return ('fail',)
        if covering(w):
            return ('fenced',)
        wd = S.size_of(w)
        k, tgt = P.kflow_of(pc, w)
        if k == P.FL_NONE:
            return ('next', [pc + wd], False)
        if k == P.FL_BRANCH:
            return ('next', [pc + wd, tgt], False)
        if k == P.FL_JUMP:
            return ('next', [tgt], False)
        if k == P.FL_CALL:
            if tgt == self.swtch:
                return ('swtch',)
            return self.call(tgt, pc + wd)
        if k == P.FL_RET:
            return ('ret',)
        if pc == self.sret:
            return ('sret',)
        if pc == self.hook:
            return self.call(self.hook_tgt, pc + wd)
        return ('fail',)

    def walk(self, ent):
        seen, work = [], [ent]
        sset = set()
        while work:
            pc = work.pop()
            if pc in sset:
                continue
            sset.add(pc)
            seen.append(pc)
            r = self.tstep(pc)
            if r[0] == 'next':
                work.extend(reversed(r[1]))
        return sorted(sset)

    def run(self):
        self.summ[self.kv] = [False, False]
        # the hart-side continuation of a fence-free `swtch` call: `swtch`'s body, then the
        # scheduler's resume point (the return address in `cpus[h].context`)
        self.summ[self.swtch] = [False, False]
        self.summ[self.resume] = [False, False]
        while True:
            self.changed = False
            for f in list(self.summ):
                rc = self.walk(f)
                self.reach[f] = rc
                outs = [self.tstep(pc) for pc in rc]
                ret = any(o[0] == 'ret' for o in outs)
                swt = any(o[0] == 'swtch' or (o[0] == 'next' and o[2]) for o in outs)
                if [ret, swt] != self.summ[f]:
                    self.summ[f] = [ret, swt]
                    self.changed = True
            if not self.changed:
                break
        self.fails = [(f, pc) for f in self.summ for pc in self.reach[f]
                      if self.tstep(pc)[0] == 'fail']
        for f in self.summ:
            fr = set()
            rc = self.reach[f]
            while True:
                n = len(fr)
                for pc in rc:
                    o = self.tstep(pc)
                    if o[0] in ('ret', 'sret') or (o[0] == 'next' and any(x in fr for x in o[1])):
                        fr.add(pc)
                if len(fr) == n:
                    break
            self.free[f] = sorted(fr)
        # the functions entered on a fence-free kernelvec -> sret path
        ff, work = set(), [self.kv]
        while work:
            f = work.pop()
            if f in ff:
                continue
            ff.add(f)
            for pc in self.free[f]:
                for t in self.callees(pc):
                    if self.summ[t][0]:
                        work.append(t)
        self.freefuns = sorted(ff)

    def witness(self, way):
        """A shortest concrete fence-free `kernelvec` -> `sret` run through the pc `way` (the
        `TRun` non-vacuity witness): BFS over (fn, pc, frames, way-passed) with the `tmove`
        transitions."""
        from collections import deque
        st0 = (self.kv, self.kv, (), False)
        end = (self.kv, self.sret, (), True)
        prev = {st0: None}
        q = deque([st0])
        while q:
            st = q.popleft()
            if st == end:
                break
            f, pc, fr, wy = st
            wy = wy or pc == way
            w = self.word(pc)
            if w is None or covering(w):
                continue
            wd = S.size_of(w)
            k, tgt = P.kflow_of(pc, w)
            nxt = []
            if k == P.FL_NONE:
                nxt = [(f, pc + wd, fr)]
            elif k == P.FL_BRANCH:
                nxt = [(f, pc + wd, fr), (f, tgt, fr)]
            elif k == P.FL_JUMP:
                nxt = [(f, tgt, fr)]
            elif k == P.FL_CALL and tgt != self.swtch:
                nxt = [(tgt, tgt, ((f, pc + wd),) + fr)]
            elif k == P.FL_IND and pc == self.hook:
                nxt = [(self.hook_tgt, self.hook_tgt, ((f, pc + wd),) + fr)]
            elif k == P.FL_RET and fr:
                nxt = [(fr[0][0], fr[0][1], fr[1:])]
            for n in nxt:
                n = n + (wy,)
                if n not in prev and len(n[2]) <= 8:
                    prev[n] = st
                    q.append(n)
        path, st = [], end
        while st is not None:
            path.append(st[:3])
            st = prev[st]
        return list(reversed(path))

    # ---- B2-free: the per-register carry analysis over the fence-free walk states -------------

    def good(self, st):
        f, pc, fr = st
        return pc in self.free.get(f, []) and all(a in self.free.get(g, []) for g, a in fr)

    def succs(self, st):
        """`PinTrapSites.tsuccs` filtered by `tgoodb`: the fence-free walk states' graph."""
        f, pc, fr = st
        w = self.word(pc)
        if w is None or covering(w):
            return []
        wd = S.size_of(w)
        k, tgt = P.kflow_of(pc, w)
        if k == P.FL_NONE:
            n = [(f, pc + wd, fr)]
        elif k == P.FL_BRANCH:
            n = [(f, pc + wd, fr), (f, tgt, fr)]
        elif k == P.FL_JUMP:
            n = [(f, tgt, fr)]
        elif k == P.FL_CALL and tgt != self.swtch:
            n = [(tgt, tgt, ((f, pc + wd),) + fr)]
        elif k == P.FL_IND and pc == self.hook:
            n = [(self.hook_tgt, self.hook_tgt, ((f, pc + wd),) + fr)]
        elif k == P.FL_RET and fr:
            n = [(fr[0][0], fr[0][1], fr[1:])]
        else:
            n = []
        return [x for x in n if self.good(x)]

    def xfer(self, st, a):
        """`PinTrapSites.xferR`/`xferS`/`xferSp` (the port)."""
        f, pc, fr = st
        sp, rc, sc = a
        w = self.word(pc)
        r = P.deps_of_bits(w)
        rc = dict(rc)
        sc = dict(sc)
        o = sp_mem_off(w)
        if r[0] == 'store' and r[1] == 2 and o is not None:
            c = set()
            for x in P.deps_vsrc(r):
                c |= rc.get(x, set())
            sc[sp + o] = c
        slot = set()
        if r[0] == 'load' and r[2] == 2 and o is not None:
            slot = sc.get(sp + o, set())
        d1 = P.deps_rd(r)
        if d1:
            rd, srcs = d1
            c = set(slot)
            for x in srcs:
                c |= rc.get(x, set())
            rc[rd] = c
        d2 = P.deps_rd2(r)
        if d2:
            rd, srcs = d2
            c = set()
            for x in srcs:
                c |= rc.get(x, set())
            rc[rd] = c
        nsp = sp
        if d1 and d1[0] == 2:
            adj = sp_adj(w)
            assert r[0] == 'alu' and adj is not None, 'unsupported sp write at 0x%x' % pc
            nsp = sp + adj
        assert not (d2 and d2[0] == 2), 'unsupported sp write at 0x%x' % pc
        return (nsp, rc, sc)

    def flow(self):
        st0 = (self.kv, self.kv, ())
        A = {st0: (0, {x: {x} for x in FLOW_REGS}, {})}
        E = {}
        changed = True
        while changed:
            changed = False
            for s in list(A):
                if s not in E:
                    E[s] = self.succs(s)
                a = self.xfer(s, A[s])
                for n in E[s]:
                    if n not in A:
                        A[n] = (a[0], {k: set(v) for k, v in a[1].items()},
                                {k: set(v) for k, v in a[2].items()})
                        changed = True
                    else:
                        b = A[n]
                        assert b[0] == a[0], 'sp offset disagrees at %r' % (n,)
                        nr = {k: b[1][k] & a[1].get(k, set()) for k in b[1]}
                        ns = {k: b[2][k] & a[2].get(k, set()) for k in b[2] if k in a[2]}
                        if nr != b[1] or ns != b[2]:
                            A[n] = (b[0], nr, ns)
                            changed = True
        return A

    def callees(self, pc):
        w = self.word(pc)
        k, tgt = P.kflow_of(pc, w)
        if k == P.FL_CALL and tgt != self.swtch:
            return [tgt]
        if k == P.FL_IND and pc == self.hook:
            return [self.hook_tgt]
        return []


FLOW_REGS = list(range(1, 53))


def sext(v, b):
    return v - (1 << b) if v & (1 << (b - 1)) else v


def sp_mem_off(w):
    """`PinTrapSites.spMemOff`: the offset of an sp-based load/store form."""
    ib = P.ibits
    if S.is_rvc(w):
        q, f3 = w & 3, ib(w, 15, 13)
        if q == 2 and f3 == 7:
            return (ib(w, 12, 10) << 3) | (ib(w, 9, 7) << 6)
        if q == 2 and f3 == 6:
            return (ib(w, 12, 9) << 2) | (ib(w, 8, 7) << 6)
        if q == 2 and f3 == 3:
            return (ib(w, 12, 12) << 5) | (ib(w, 6, 5) << 3) | (ib(w, 4, 2) << 6)
        if q == 2 and f3 == 2:
            return (ib(w, 12, 12) << 5) | (ib(w, 6, 4) << 2) | (ib(w, 3, 2) << 6)
        return None
    op = w & 0x7f
    if op == 0x23:
        return sext((ib(w, 31, 25) << 5) | ib(w, 11, 7), 12)
    if op == 0x03:
        return sext(ib(w, 31, 20), 12)
    return None


def sp_adj(w):
    """`PinTrapSites.spAdj`: the immediate of an `sp := sp + imm` form."""
    ib = P.ibits
    if S.is_rvc(w):
        q, f3 = w & 3, ib(w, 15, 13)
        if q == 1 and f3 == 3:
            return sext((ib(w, 12, 12) << 9) | (ib(w, 6, 6) << 4) | (ib(w, 5, 5) << 6)
                        | (ib(w, 4, 3) << 7) | (ib(w, 2, 2) << 5), 10)
        if q == 1 and f3 == 0:
            return sext((ib(w, 12, 12) << 5) | ib(w, 6, 2), 6)
        return None
    if (w & 0x7f) == 0x13 and ib(w, 14, 12) == 0 and ib(w, 19, 15) == 2:
        return sext(ib(w, 31, 20), 12)
    return None


def is_store(img, pc):
    return P.role_is_store(P.deps_of_bits(img.word(pc)))


def exit_class(img, pc):
    """The census CLASS of a pre-fence exit (an annotation; Lean checks `frame` and `amo`)."""
    r = P.deps_of_bits(img.word(pc))
    fn, off = img.sym_of(pc)
    if r[0] == 'amo':
        return 'amo'
    if r[0] == 'store' and r[1] == 2:
        return 'frame'
    if r[0] == 'store' and r[1] == 8:
        return 'frameS0'        # s0-relative: the function's own frame (printk's va_list)
    tbl = {
        ('printint', 0x34): 'frameBuf', ('printint', 0x54): 'frameBuf',
        ('consoleintr', 0xc8): 'consBuf', ('consoleintr', 0x120): 'consBuf',
        ('wakeup', 0x44): 'procField', ('wakeup', 0x4e): 'procField',
        ('virtio_disk_intr', 0x2a): 'mmio',
        ('push_off', 0x20): 'cpuCell', ('push_off', 0x36): 'cpuCell', ('pop_off', 0x1c): 'cpuCell',
        ('sched', 0x7a): 'cpuCell', ('scheduler', 0x82): 'cpuCell', ('scheduler', 0x86): 'cpuCell',
        ('acquire', 0x28): 'lockCpu', ('release', 0x12): 'lockCpu',
        ('plic_complete', 0x1a): 'mmio', ('uartputc_sync', 0x4e): 'mmio', ('unreachable', 0xc): 'mmio',
        ('clockintr', 0x40): 'ticks', ('yield', 0x16): 'procField',
    }
    if (fn, off) in tbl:
        return tbl[(fn, off)]
    if fn == 'swtch':
        return 'swtchCtx'
    return 'other'


def emit(img, C):
    def h(x):
        return '0x%x' % x
    out = [BEGIN]
    out.append('/-- The per-function fence-free summaries (entry, ret, swt, reach, free). -/')
    out.append('def trapTab : List TSum := [')
    rows = []
    for f in sorted(C.summ):
        ret, swt = C.summ[f]
        rows.append('  ⟨%s, %s, %s,\n    [%s],\n    [%s]⟩' % (
            h(f), 'true' if ret else 'false', 'true' if swt else 'false',
            ', '.join(h(x) for x in C.reach[f]), ', '.join(h(x) for x in C.free[f])))
    out.append(',\n'.join(rows))
    out.append(']')
    out.append('')
    out.append('/-- The functions entered on a fence-free `kernelvec` → `sret` path. -/')
    out.append('def trapFreeFuns : List Int := [%s]' % ', '.join(h(x) for x in C.freefuns))
    out.append('')
    ex = sorted(set(pc for f in C.summ for pc in C.reach[f] if is_store(img, pc)))
    out.append('/-- THE PRE-FENCE EXIT TABLE: every store/AMO on a trap path before its first covering')
    out.append('fence, by class. -/')
    out.append('def trapExits : List (Int × TExit) := [')
    out.append(',\n'.join('  (%s, .%s)' % (h(pc), exit_class(img, pc)) for pc in ex))
    out.append(']')
    ff = sorted(set(pc for f in C.freefuns for pc in C.free[f] if is_store(img, pc)))
    out.append('')
    out.append('/-- The exits on the FENCE-FREE paths (the stores of the free region of `trapFreeFuns`). -/')
    out.append('def trapFreeExits : List Int := [%s]' % ', '.join(h(x) for x in ff))
    out.append('')
    out.append('/-- A concrete fence-free `kernelvec` → `sret` run after `tStart`: path (a), the spurious')
    out.append('PLIC claim (`devintr` → `plic_claim` → irq = 0 → return 1). -/')
    out.append('def trapWitnessTail : List TSt := [')
    def fr(x):
        return '[' + ', '.join('(%s, %s)' % (h(g), h(a)) for g, a in x) + ']'
    out.append(',\n'.join('  ⟨%s, %s, %s⟩' % (h(f), h(pc), fr(x)) for f, pc, x in C.witness(img.syms['devintr'] + 0x2c)[1:]))
    out.append(']')
    A = C.flow()
    maps, idx = [], {}

    def mkey(a):
        return (tuple(sorted((k, tuple(sorted(v))) for k, v in a[1].items() if v)),
                tuple(sorted((k, tuple(sorted(v))) for k, v in a[2].items() if v)))
    rows = []
    for st in sorted(A, key=lambda x: (x[1], x[0], x[2])):
        k = mkey(A[st])
        if k not in idx:
            idx[k] = len(maps)
            maps.append(k)
        rows.append((st, A[st][0], idx[k]))
    out.append('')
    out.append('/-- THE CARRY MAPS (B2-free): which interrupted registers each register / `sp`-slot')
    out.append('(offset from the trap\'s entry `sp`) carries, on EVERY fence-free path. -/')
    out.append('def trapMaps : List CMap := [')

    def lst(v):
        return '[' + ', '.join(str(x) for x in v) + ']'
    mr = []
    for rk, sk in maps:
        mr.append('  ⟨[%s],\n    [%s]⟩' % (', '.join('(%d, %s)' % (k, lst(v)) for k, v in rk),
                                         ', '.join('(%d, %s)' % (k, lst(v)) for k, v in sk)))
    out.append(',\n'.join(mr))
    out.append(']')
    out.append('')
    def ii(v):
        return '(%d : Int)' % v if v >= 0 else '(-%d : Int)' % -v
    CH = 48
    names = []
    for c in range(0, len(rows), CH):
        nm = 'trapFlow%d' % (c // CH)
        names.append(nm)
        out.append('def %s : List (TSt × Int × Nat) := [' % nm)
        out.append(',\n'.join('  ((⟨%s, %s, %s⟩ : TSt), %s, %d)' % (h(f), h(pc), fr(x), ii(sp), m)
                              for (f, pc, x), sp, m in rows[c:c + CH]))
        out.append(']')
        out.append('')
    out.append('/-- The fence-free walk states with their `sp` offset and carry map (index into `trapMaps`). -/')
    out.append('def trapFlow : List (TSt × Int × Nat) :=')
    out.append('  ' + ' ++ '.join(names))
    out.append(END)
    return '\n'.join(out) + '\n', ex, ff


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
    C = Census(img)
    C.run()
    block, ex, ff = emit(img, C)
    if a.emit:
        sys.stdout.write(block)
        return 0
    if a.check:
        src = open(OUT, encoding='utf-8').read()
        m = re.search(re.escape(BEGIN) + r'.*?' + re.escape(END) + r'\n', src, re.S)
        ok = m is not None and m.group(0) == block and not C.fails
        print('gen_weak_trapsites --check: %s' % ('ok' if ok else 'FAIL'))
        return 0 if ok else 1
    say = (lambda *x: None) if a.quiet else print

    def nm(pc):
        f, o = img.sym_of(pc)
        return '%s+0x%x' % (f, o)
    say('trap-path census over xv6-riscv %s (kernelvec 0x%08x, sret 0x%08x)' % (img.rev, C.kv, C.sret))
    say('functions on trap paths before their first covering fence: %d' % len(C.summ))
    for f in sorted(C.summ, key=lambda x: img.sym_of(x)[0]):
        ret, swt = C.summ[f]
        fen = [nm(pc) for pc in C.reach[f] if C.tstep(pc)[0] == 'fenced']
        say('  %-18s ret=%-5s swt=%-5s reach=%3d free=%3d fences=%s' % (
            img.sym_of(f)[0], ret, swt, len(C.reach[f]), len(C.free[f]), ','.join(fen) or '-'))
    say('walk failures: %s' % (C.fails or 'none'))
    say('fence-free functions (kernelvec -> sret): %s' % ', '.join(img.sym_of(f)[0] for f in C.freefuns))
    sw = [nm(pc) for f in C.summ for pc in C.reach[f] if C.tstep(pc)[0] == 'swtch']
    say('fence-free swtch calls: %s' % (', '.join(sorted(set(sw))) or 'none'))
    from collections import Counter
    cls = Counter(exit_class(img, pc) for pc in ex)
    say('pre-fence exits: %d  %s' % (len(ex), dict(sorted(cls.items()))))
    for pc in ex:
        c = exit_class(img, pc)
        if c not in ('frame',):
            say('    0x%08x %-22s %-10s %s%s' % (pc, nm(pc), c, img.disasm.get(pc, ''),
                                               '   [FREE]' if pc in ff else ''))
    say('fence-free exits: %d  %s' % (len(ff), dict(sorted(Counter(exit_class(img, pc) for pc in ff).items()))))
    A = C.flow()
    end = (C.kv, C.sret, ())
    sp, rc, _ = A[end]
    pres = [r for r in FLOW_REGS if r in rc.get(r, set())]
    say('carry analysis: %d fence-free walk states; at the sret sp offset %d; preserved %d of %d '
        'registers, lost %s' % (len(A), sp, len(pres), len(FLOW_REGS),
                                [r for r in FLOW_REGS if r not in pres]))
    return 1 if C.fails else 0


if __name__ == '__main__':
    sys.exit(main())

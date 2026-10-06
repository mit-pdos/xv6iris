#!/usr/bin/env python3
"""gen_weak_pins.py -- THE STATIC PIN CHECKER's witness generator (Lean).

The Lean retarget of the Rocq weak line's tools/gen_pins.py, in the shape of
tools/gen_weak_sites.py (which retargeted gen_sites.py).  A sibling of
gen_weak_sites.py, one level up in ambition: that one classifies single WORDS,
this one classifies LOAD SITES by what the kernel does with the loaded value
before its hart's next store.  Route-b 4g(B): a load whose result is branched
on, fenced after, or fed into the next store is PINNED on its row; a load off
[sp] or off a [tp]-derived per-cpu base reads a byte no other hart writes.
What is left is the OWNERSHIP RESIDUE, which the [WProt] port convention has
to cover.

Inputs (the tracked dumps of this tree only -- never the ELF, never a proof),
read through gen_weak_sites.Image:

  Xv6/KernelImage.lean     the text (address, width, encoding, objdump line)
                           and the symbol table (namespace MachCSL.KernelSyms)
  MachCSL/KernelElf.lean   the loaded segment's bytes (what Weak/KernelSitesDef
                           reads through `KernelElf.elfByte`)

OUTPUTS.

  Weak/KernelPins.lean (always) the witness table `pins` and the two
      reflection facts `imagePinnedb` (every witness survives
      `Weak.KernelPinsDef`'s re-check, `decide +kernel`) and `pinsCover`
      (every load position of the flat text walk is in the table).  Rocq's
      iris/KernelPins.v is the same file.
  stdout    the census, the direct-target decoder cross-check, the callee
            summaries and the residue list (Rocq's tools/pins.md, as a report;
            `--json PATH` also writes Rocq's tools/pins.json census).

THE TRUST BOUNDARY (Rocq's, unchanged).  THIS FILE IS UNTRUSTED.  Everything it
computes is re-checked by Weak/KernelPinsDef.lean's `pinnedb` with
`decide +kernel` over the same image bytes, through `Weak.depsOfBits` -- the
model's own role decoder, not this file's Python port of it.  A disagreement
between the port below and WeakDeps is a FAILED `imagePinnedb`, never a
silently wrong claim.  To make that failure cheap to find, this generator ALSO
re-runs its own port of `pinnedb` over the FLAT image (exactly the Lean
checker's walk: `kw`, the text bounds, no real-instruction map) on every
witness it emits; `--check` fails if any of them does not hold.

CHECK MODE (`--check`, the `make check-gen` counterpart): regenerate into
memory and fail if it differs from the checked-in Weak/KernelPins.lean; fail if
Weak/KernelPinsDef.lean's `pinFuel`/`pdfsFuel`/`pinDepth` are not the ones used
here; fail on a load-decoding position outside the real instruction stream, on
a direct-target disagreement with objdump, or on a witness that the flat
re-check rejects.  Nothing is written.

Usage:
    tools/gen_weak_pins.py [--image Xv6/KernelImage.lean] [--elf MachCSL/KernelElf.lean]
                           [--out Weak/KernelPins.lean] [--def Weak/KernelPinsDef.lean]
                           [--json PATH] [--residue] [--check] [--quiet]
"""

import argparse
import difflib
import json
import os
import re
import sys
import textwrap

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_weak_sites as S   # noqa: E402

REPO = S.REPO


# ===========================================================================
# 1.  A PYTHON PORT OF Weak/WeakDeps.depsOfBits
#
# Faithful, constructor for constructor (Rocq gen_pins.py's port, unchanged:
# the Lean decoder is the Rocq one).  It is a PORT and it is untrusted:
# Weak/KernelPinsDef.lean calls the real thing.  Roles are tuples whose head
# is the WeakDeps constructor name in lower case.
# ===========================================================================

def ibits(w, hi, lo):
    return (w >> lo) & ((1 << (hi - lo + 1)) - 1)


# WeakDeps' pseudo-register numbers for the CSR file (DEC-5/DEC-6).
SATP, SEPC, MEPC, SSCRATCH, MSCRATCH = 32, 33, 34, 35, 36
STVEC, MTVEC, MSTATUS, MIE, MIP = 37, 38, 39, 40, 41
MEDELEG, MIDELEG, PMPADDR0, PMPCFG0 = 42, 43, 44, 45
MCOUNTEREN, MENVCFG, MHARTID, TIME = 46, 47, 48, 49
SCAUSE, STVAL, STIMECMP = 50, 51, 52

CSR_REG = {
    0x180: SATP, 0x141: SEPC, 0x341: MEPC, 0x140: SSCRATCH, 0x340: MSCRATCH,
    0x105: STVEC, 0x305: MTVEC, 0x100: MSTATUS, 0x300: MSTATUS,
    0x104: MIE, 0x304: MIE, 0x144: MIP, 0x344: MIP,
    0x302: MEDELEG, 0x303: MIDELEG, 0x3b0: PMPADDR0, 0x3a0: PMPCFG0,
    0x306: MCOUNTEREN, 0x30a: MENVCFG, 0xf14: MHARTID, 0xc01: TIME,
    0x142: SCAUSE, 0x143: STVAL, 0x14d: STIMECMP,
}

F12_SRET, F12_MRET = 0x102, 0x302

NONE = ('none',)


def deps_of_csr(p, w):
    rd, rs1 = ibits(w, 11, 7), ibits(w, 19, 15)
    f3 = ibits(w, 14, 12)
    if f3 == 1:
        return ('csr', p, [rs1], rd)
    if f3 == 5:
        return ('csr', p, [], rd)
    if f3 in (2, 3):
        return ('alu', rd, [p]) if rs1 == 0 else ('csr', p, [rs1, p], rd)
    if f3 in (6, 7):
        return ('alu', rd, [p]) if rs1 == 0 else ('csr', p, [p], rd)
    return NONE


def deps_of_system(w):
    c = ibits(w, 31, 20)
    if ibits(w, 14, 12) == 0:
        if c == F12_SRET:
            return ('jalr', 0, SEPC)
        if c == F12_MRET:
            return ('jalr', 0, MEPC)
        return NONE
    p = CSR_REG.get(c)
    return NONE if p is None else deps_of_csr(p, w)


def deps_of_base(w):
    rd, rs1, rs2 = ibits(w, 11, 7), ibits(w, 19, 15), ibits(w, 24, 20)
    op = ibits(w, 6, 0)
    if op == 3:
        return ('load', rd, rs1)
    if op == 35:
        return ('store', rs1, rs2)
    if op == 99:
        return ('branch', rs1, rs2)
    if op == 103:
        return ('jalr', rd, rs1)
    if op == 111:
        return ('jal', rd)
    if op in (55, 23):
        return ('alu', rd, [])
    if op in (19, 27):
        return ('alu', rd, [rs1])
    if op in (51, 59):
        return ('alu', rd, [rs1, rs2])
    if op == 47:
        return ('load', rd, rs1) if ibits(w, 31, 27) == 2 else ('amo', rd, rs1, rs2)
    if op == 115:
        return deps_of_system(w)
    return NONE


def creg(n):
    return 8 + n


def deps_of_c0(w):
    rd_, rs1_ = creg(ibits(w, 4, 2)), creg(ibits(w, 9, 7))
    f3 = ibits(w, 15, 13)
    if f3 == 0:
        return NONE if ibits(w, 12, 5) == 0 else ('alu', rd_, [2])
    if f3 in (2, 3):
        return ('load', rd_, rs1_)
    if f3 in (6, 7):
        return ('store', rs1_, rd_)
    return NONE


def deps_of_c1(w):
    rd = ibits(w, 11, 7)
    rd_, rs2_ = creg(ibits(w, 9, 7)), creg(ibits(w, 4, 2))
    f3 = ibits(w, 15, 13)
    if f3 in (0, 1):
        return ('alu', rd, [rd])
    if f3 == 2:
        return ('alu', rd, [])
    if f3 == 3:
        return ('alu', 2, [2]) if rd == 2 else ('alu', rd, [])
    if f3 == 4:
        k = ibits(w, 11, 10)
        if k in (0, 1, 2):
            return ('alu', rd_, [rd_])
        if ibits(w, 12, 12) == 0:
            return ('alu', rd_, [rd_, rs2_])
        if ibits(w, 6, 5) <= 1:
            return ('alu', rd_, [rd_, rs2_])
        return NONE
    if f3 == 5:
        return NONE
    if f3 in (6, 7):
        return ('branch', rd_, 0)
    return NONE


def deps_of_c2(w):
    rd, rs2 = ibits(w, 11, 7), ibits(w, 6, 2)
    f3 = ibits(w, 15, 13)
    if f3 == 0:
        return ('alu', rd, [rd])
    if f3 in (2, 3):
        return ('load', rd, 2)
    if f3 == 4:
        if ibits(w, 12, 12) == 0:
            return ('jalr', 0, rd) if rs2 == 0 else ('alu', rd, [rs2])
        if rs2 == 0:
            return NONE if rd == 0 else ('jalr', 1, rd)
        return ('alu', rd, [rd, rs2])
    if f3 in (6, 7):
        return ('store', 2, rs2)
    return NONE


def deps_of_bits(w):
    q = ibits(w, 1, 0)
    if q == 0:
        return deps_of_c0(w)
    if q == 1:
        return deps_of_c1(w)
    if q == 2:
        return deps_of_c2(w)
    return deps_of_base(w)


# ---- the projections (WeakDeps 3).  A source is a register number; the
# load-reservation source DLdRes is never tainted, so it is dropped here.

def deps_ctrl(r):
    if r[0] == 'branch':
        return [x for x in (r[1], r[2]) if x != 0]
    if r[0] == 'jalr':
        return [r[2]] if r[2] != 0 else []
    return []


def deps_addr(r):
    if r[0] == 'load':
        return [r[2]] if r[2] != 0 else []
    if r[0] == 'store':
        return [r[1]] if r[1] != 0 else []
    if r[0] == 'amo':
        return [r[2]] if r[2] != 0 else []
    return []


def deps_vsrc(r):
    if r[0] == 'store':
        return [r[2]] if r[2] != 0 else []
    if r[0] == 'amo':
        return [r[3]] if r[3] != 0 else []
    return []


def deps_rd(r):
    """(rd, srcs) or None.  Mirrors WeakDeps.depsRd, DLdRes dropped."""
    if r[0] == 'load':
        return None if r[1] == 0 else (r[1], deps_addr(r))
    if r[0] == 'amo':
        return None if r[1] == 0 else (r[1], [])
    if r[0] in ('jal', 'jalr'):
        return None if r[1] == 0 else (r[1], [])
    if r[0] == 'alu':
        return None if r[1] == 0 else (r[1], [x for x in r[2] if x != 0])
    if r[0] == 'csr':
        return (r[1], [x for x in r[2] if x != 0])
    return None


def deps_rd2(r):
    if r[0] == 'csr':
        return None if r[3] == 0 else (r[3], [r[1]])
    return None


def role_is_load(r):
    return r[0] == 'load'


def role_is_store(r):
    return r[0] in ('store', 'amo')


def role_is_branch(r):
    return r[0] == 'branch'


# ===========================================================================
# 2.  CONTROL FLOW -- a PORT of Weak/KernelPinsDef.kflowOf
# ===========================================================================

FL_NONE, FL_BRANCH, FL_JUMP, FL_CALL, FL_RET, FL_IND = range(6)


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def imm_b(w):
    return sext((ibits(w, 31, 31) << 12) | (ibits(w, 7, 7) << 11)
                | (ibits(w, 30, 25) << 5) | (ibits(w, 11, 8) << 1), 13)


def imm_j(w):
    return sext((ibits(w, 31, 31) << 20) | (ibits(w, 19, 12) << 12)
                | (ibits(w, 20, 20) << 11) | (ibits(w, 30, 21) << 1), 21)


def imm_cb(w):
    return sext((ibits(w, 12, 12) << 8) | (ibits(w, 6, 5) << 6)
                | (ibits(w, 2, 2) << 5) | (ibits(w, 11, 10) << 3)
                | (ibits(w, 4, 3) << 1), 9)


def imm_cj(w):
    return sext((ibits(w, 12, 12) << 11) | (ibits(w, 8, 8) << 10)
                | (ibits(w, 10, 9) << 8) | (ibits(w, 6, 6) << 7)
                | (ibits(w, 7, 7) << 6) | (ibits(w, 2, 2) << 5)
                | (ibits(w, 11, 11) << 4) | (ibits(w, 5, 3) << 1), 12)


def kflow_of(pc, w):
    """(kind, target).  Target is meaningful for BRANCH / JUMP / CALL."""
    if S.is_rvc(w):
        q, f3 = S.c_quad(w), S.c_f3(w)
        if q == 1 and f3 == 5:
            return (FL_JUMP, pc + imm_cj(w))                 # c.j
        if q == 1 and f3 in (6, 7):
            return (FL_BRANCH, pc + imm_cb(w))               # c.beqz / c.bnez
        if q == 2 and f3 == 4 and ibits(w, 6, 2) == 0:
            rd = ibits(w, 11, 7)
            if ibits(w, 12, 12) == 0:                        # c.jr rd
                return (FL_RET, 0) if rd == 1 else \
                       ((FL_NONE, 0) if rd == 0 else (FL_IND, 0))
            if rd == 0:
                return (FL_NONE, 0)                          # c.ebreak
            return (FL_IND, 0)                               # c.jalr rd
        return (FL_NONE, 0)
    op = ibits(w, 6, 0)
    if op == 99:
        return (FL_BRANCH, pc + imm_b(w))
    if op == 111:
        return ((FL_JUMP if ibits(w, 11, 7) == 0 else FL_CALL), pc + imm_j(w))
    if op == 103:
        if ibits(w, 11, 7) == 0 and ibits(w, 19, 15) == 1 and ibits(w, 31, 20) == 0:
            return (FL_RET, 0)                               # ret = jalr x0,0(ra)
        return (FL_IND, 0)
    if op == 115 and ibits(w, 14, 12) == 0:
        c = ibits(w, 31, 20)
        if c == 0x105 or ibits(w, 31, 25) == 0x09:
            return (FL_NONE, 0)                              # wfi, sfence.vma
        return (FL_IND, 0)                                   # ecall/ebreak/sret/mret
    return (FL_NONE, 0)


# ===========================================================================
# 3.  THE TWO WALKS -- ports of Weak/KernelPinsDef.fwalk and pdfs
# ===========================================================================

PIN_FUEL = 64          # instructions the FALL-THROUGH walk may cross
DFS_FUEL = 400         # states the all-paths DFS may pop
PIN_DEPTH = 2          # return-stack depth: how many call levels are inlined
BACK_WINDOW = 32       # instructions the tp-idiom search looks back over


class Fun:
    def __init__(self, name, lo, hi, insns):
        self.name, self.lo, self.hi = name, lo, hi
        self.insns = insns                       # [(addr, word, width_bits)]
        self.idx = {a: i for i, (a, _, _) in enumerate(insns)}


def build_funs(img):
    """Per-symbol real instruction lists (Rocq: gen_code.instructions over the
    symbol's range; here the `Kernel.text` entries in that range)."""
    out, by_addr = [], {}
    starts = img.symaddrs
    text = img.text
    j = 0
    for i, s in enumerate(starts):
        hi = starts[i + 1] if i + 1 < len(starts) else img.hi
        while j < len(text) and text[j][0] < s:
            j += 1
        ins = []
        k = j
        while k < len(text) and text[k][0] < hi:
            a, wd, e = text[k]
            ins.append((a, e, wd * 8))
            k += 1
        if not ins:
            continue
        f = Fun(img.symname[s], s, hi, ins)
        out.append(f)
        for a, _, _ in ins:
            by_addr[a] = f
    return out, by_addr


# ---- the taint, as an ORDERED LIST with no duplicates.  This mirrors
# KernelPinsDef.taintUpd1 exactly (duplicate-free, so that the DFS's visited
# set can compare taints syntactically); a Python set here would make the two
# checkers explore different state spaces.

def taint_del(r, t):
    return [x for x in t if x != r]


def taint_upd1(t, d):
    if d is None:
        return t
    rd, srcs = d
    if any(s in t for s in srcs):
        return t if rd in t else [rd] + t
    return taint_del(rd, t)


def taint_step(t, w):
    r = deps_of_bits(w)
    return taint_upd1(taint_upd1(t, deps_rd(r)), deps_rd2(r))


class Img:
    """The REAL instruction map the generator's walks step over (Rocq's)."""
    def __init__(self, funs):
        self.at = {}
        for f in funs:
            for a, w, wd in f.insns:
                self.at[a] = (w, S.size_of(w))

    def word(self, a):
        return self.at[a][0] if a in self.at else None


class Flat:
    """The FLAT image the Lean checker steps over: `kw`, the text bounds, and
    nothing else (for the generator's own re-check of every witness)."""
    def __init__(self, img):
        self.img = img
        self.lo, self.hi = img.lo, img.hi
        self.cache = {}

    def word(self, a):
        if not (self.lo <= a < self.hi):
            return None
        w = self.cache.get(a)
        if w is None:
            w = self.cache[a] = self.img.word(a)
        return w


def pstep(IM, own, st):
    """ONE state of the walk; the port of KernelPinsDef.pstep.  `IM.word`
    returns None off the map (the generator: off the real instruction stream;
    the flat re-check: outside the text bounds, which is the Lean guard)."""
    pc, t, rs = st
    w = IM.word(pc)
    if w is None:
        return None
    wd = S.size_of(w)
    r = deps_of_bits(w)
    if S.is_fence(w):
        return []                                          # PIN: a fence
    if role_is_store(r):
        if any(s in t for s in deps_addr(r)) or any(s in t for s in deps_vsrc(r)):
            return []                                      # PIN: a dep store
        if own and r[0] == 'store' and r[1] == 2:
            return [(pc + wd, taint_step(t, w), rs)]       # the hart's own frame
        return None
    k, tgt = kflow_of(pc, w)
    if k == FL_BRANCH:
        if any(s in t for s in deps_ctrl(r)):
            return []                                      # PIN: a control dep
        nt = taint_step(t, w)
        return [(pc + wd, nt, rs), (tgt, nt, rs)]
    if k == FL_JUMP:
        return [(tgt, t, rs)]
    if k == FL_CALL:
        if len(rs) >= PIN_DEPTH:
            return None
        return [(tgt, taint_step(t, w), (pc + wd,) + rs)]
    if k == FL_RET:
        return None if not rs else [(rs[0], t, rs[1:])]
    if k == FL_IND:
        return None
    return [(pc + wd, taint_step(t, w), rs)]


def fwalk(IM, own, stop, st, fuel=PIN_FUEL):
    """The FALL-THROUGH walk to a named witness pc (KernelPinsDef.fwalk)."""
    for _ in range(fuel):
        if st[0] == stop:
            return st[1]
        ns = pstep(IM, own, st)
        if not ns:
            return None
        st = ns[0]
    return None


def fclassify(IM, own, st, fuel=PIN_FUEL):
    """The same walk, run to its own verdict: which pin the fall-through path
    reaches first.  This is what names the witness pc in the table."""
    for _ in range(fuel):
        pc, t, rs = st
        w = IM.word(pc)
        if w is None:
            return ('Residue', None, 'offmap')
        r = deps_of_bits(w)
        if S.is_fence(w):
            return ('Fence', pc, None)
        if role_is_store(r):
            if any(s in t for s in deps_addr(r)) or any(s in t for s in deps_vsrc(r)):
                return ('Dep', pc, None)
            if not (own and r[0] == 'store' and r[1] == 2):
                return ('Residue', pc, 'store-unpinned')
        elif role_is_branch(r) and any(s in t for s in deps_ctrl(r)):
            return ('Ctrl', pc, None)
        else:
            k, tgt = kflow_of(pc, w)
            if k == FL_CALL and len(rs) >= PIN_DEPTH:
                return ('Call', pc, 'depth')
            if k == FL_IND:
                return ('Call', pc, 'indirect') if r[0] == 'jalr' and r[1] != 0 \
                    else ('Residue', pc, 'indirect')
            if k == FL_RET and not rs:
                return ('Residue', pc, 'ret')
        ns = pstep(IM, own, st)
        if not ns:
            return ('Residue', pc, 'stuck')
        st = ns[0]
    return ('Residue', None, 'window')


def pdfs(IM, own, st0, fuel=DFS_FUEL):
    """ALL PATHS (KernelPinsDef.pdfs): a fuel-bounded DFS with a visited set."""
    seen, work = [], [st0]
    for _ in range(fuel):
        if not work:
            return True
        st = work.pop(0)
        if st in seen:
            continue
        ns = pstep(IM, own, st)
        if ns is None:
            return False
        seen.append(st)
        work = ns + work
    return False


def percpu_origin(fn, pc, base):
    """The pc of the instruction that put [tp]'s value into a register that
    reaches the load's base, or None (a straight-line stretch in one function)."""
    i = fn.idx[pc]
    for j in range(i - 1, max(-1, i - 1 - BACK_WINDOW), -1):
        a0, w0, _ = fn.insns[j]
        d = deps_rd(deps_of_bits(w0))
        if d is None or 4 not in d[1]:
            continue
        t = [d[0]]
        for k in range(j + 1, i):
            t = taint_step(t, fn.insns[k][1])
        if base in t:
            return a0
    return None


# ---- the generator's port of KernelPinsDef.pinnedb, over the FLAT image.

def walk_to(FL, fuel, nost, a, stop, t):
    for _ in range(fuel):
        if a == stop:
            return t
        if stop < a:
            return None
        w = FL.img.word(a)
        if nost and role_is_store(deps_of_bits(w)):
            return None
        t = taint_step(t, w)
        a += S.size_of(w)
    return None


def load_rd(FL, pc):
    d = deps_rd(deps_of_bits(FL.img.word(pc)))
    return None if d is None else d[0]


def pin_start(FL, pc):
    rd = load_rd(FL, pc)
    return (pc + S.size_of(FL.img.word(pc)), [rd] if rd is not None else [], ())


def pinnedb(FL, pc, wit, fuel=PIN_FUEL):
    """`KernelPinsDef.pinnedb fuel pc w`, as the Lean checker computes it."""
    r = deps_of_bits(FL.img.word(pc))
    if not role_is_load(r):
        return False
    c = wit[0]
    if c == 'Stack':
        return deps_addr(r) == [2]
    if c == 'PerCpu':
        pc0 = wit[1]
        if not pc0 < pc:
            return False
        d = deps_rd(deps_of_bits(FL.img.word(pc0)))
        if d is None or 4 not in d[1]:
            return False
        t = walk_to(FL, fuel, False, pc0 + S.size_of(FL.img.word(pc0)), pc, [d[0]])
        return t is not None and any(s in t for s in deps_addr(r))
    if c in ('Call', 'Residue'):
        return True
    at, own = wit[1], wit[2]
    t = fwalk(FL, own, at, pin_start(FL, pc), fuel)
    if t is None:
        return False
    r2 = deps_of_bits(FL.img.word(at)) if FL.word(at) is not None else NONE
    if c == 'Ctrl':
        ok = role_is_branch(r2) and any(s in t for s in deps_ctrl(r2))
    elif c == 'Fence':
        ok = FL.word(at) is not None and S.is_fence(FL.img.word(at))
    else:
        ok = role_is_store(r2) and (any(s in t for s in deps_addr(r2))
                                    or any(s in t for s in deps_vsrc(r2)))
    return ok and pdfs(FL, own, pin_start(FL, pc))


# ===========================================================================
# 3b.  CALLEE SUMMARIES -- an AUDIT artifact (nothing downstream trusts it)
# ===========================================================================

ARGREGS = [10, 11, 12, 13, 14, 15, 16, 17]


def callee_summary(IM, entry):
    st = (entry, [ARGREGS[0]], ())
    c, at, why = fclassify(IM, True, st)
    return {'entry': entry, 'first_store_pinned': pdfs(IM, True, st),
            'strict': pdfs(IM, False, st), 'fallthrough_class': c,
            'first_store': at, 'why': why}


# ===========================================================================
# 4.  The census
# ===========================================================================

CLASSES = ['Stack', 'PerCpu', 'Ctrl', 'Fence', 'Dep', 'Call', 'Residue']


def classify(img, funs, by_addr):
    IM = Img(funs)
    addrs, _end = img.flat_walk()
    rows = []
    for a in addrs:
        w = img.word(a)
        r = deps_of_bits(w)
        if not role_is_load(r):
            continue
        rd, base = r[1], r[2]
        fn = by_addr.get(a)
        sym, off = img.sym_of(a)
        rec = {'pc': a, 'word': w & ((1 << (S.size_of(w) * 8)) - 1),
               'width': S.size_of(w) * 8, 'rd': rd, 'base': base,
               'fun': fn.name if fn else sym, 'off': off,
               'text': img.disasm.get(a, ''), 'real': fn is not None,
               'witness': 'Residue', 'at': None, 'why': None, 'own': False,
               'callee': None, 'allpaths': False}
        if fn is None:
            rec['why'] = 'not-a-real-instruction'
            rows.append(rec)
            continue
        if base == 2:
            rec['witness'] = 'Stack'
            rec['allpaths'] = True
            rows.append(rec)
            continue
        pc0 = percpu_origin(fn, a, base) if base != 0 else None
        if pc0 is not None:
            rec['witness'] = 'PerCpu'
            rec['at'] = pc0
            rec['allpaths'] = True
            rows.append(rec)
            continue
        t0 = [rd] if rd != 0 else []
        st0 = (a + S.size_of(w), t0, ())
        # PREFER THE ASSUMPTION-FREE REGIME (own = False), as Rocq does.
        got = None
        for own in (False, True):
            c, at, why = fclassify(IM, own, st0)
            if c in ('Ctrl', 'Fence', 'Dep') and pdfs(IM, own, st0):
                got = (c, at, own)
                break
        if got is not None:
            rec['witness'], rec['at'], rec['own'] = got
            rec['allpaths'] = True
        else:
            c, at, why = fclassify(IM, True, st0)
            rec['witness'] = 'Call' if c == 'Call' else 'Residue'
            rec['at'], rec['why'] = at, why
        if rec['witness'] == 'Call' and rec['at'] is not None:
            k, tgt = kflow_of(rec['at'], IM.at[rec['at']][0])
            rec['callee'] = img.symname.get(tgt) if k == FL_CALL else None
            if rec['callee'] is None and k == FL_CALL:
                rec['callee'] = img.sym_of(tgt)[0]
        rows.append(rec)
    return rows


def audit_targets(img, funs):
    """CROSS-CHECK the immediate decoders against objdump's printed target."""
    ok = bad = skipped = 0
    bads = []
    for f in funs:
        for a, w, _ in f.insns:
            k, tgt = kflow_of(a, w)
            if k not in (FL_BRANCH, FL_JUMP, FL_CALL):
                continue
            txt = img.disasm.get(a, '')
            hexes = re.findall(r'\b([0-9a-f]{8,16})\b\s*<', txt)
            if not hexes:
                skipped += 1
                continue
            if int(hexes[-1], 16) == tgt:
                ok += 1
            else:
                bad += 1
                bads.append((a, txt, tgt))
    return ok, bad, skipped, bads


def witness_tuple(r):
    c = r['witness']
    if c in ('Ctrl', 'Fence', 'Dep'):
        return (c, r['at'], r['own'])
    if c in ('PerCpu', 'Call'):
        return (c, r['at'])
    return (c,)


# ===========================================================================
# 5.  Weak/KernelPins.lean
# ===========================================================================

HEADER = """-- AUTO-GENERATED by tools/gen_weak_pins.py from Xv6/KernelImage.lean (xv6-riscv %(rev)s); do not edit.
/-
Weak: **the witness table of the static pin checker** (generated): one `KernelPinsDef.Pin` per
LOAD site of `KernelSitesDef.textPcs`, re-checked against the image by `KernelPinsDef.pinnedb`.

Rocq: `iris/KernelPins.v` @ xxvzwolszwmp (1cc222280), itself generated by Rocq's
`tools/gen_pins.py`.  Regenerate with `python3 tools/gen_weak_pins.py`; check with
`python3 tools/gen_weak_pins.py --check`.

Each certifying witness carries TWO facts, both re-checked: the FALL-THROUGH pin it names
(`fwalk`, which follows direct jumps and descends into direct calls to depth `pinDepth`), and that
EVERY path out of the load reaches some pin before the hart's next store (`pdfs`, the fuel-bounded
all-paths DFS).  The boolean in each witness is the `own` bit: `true` means the check skipped
stores through `sp` as the hart's own frame (the dual of `PStack`); `false` means it skipped
nothing.

The two reflection facts at the bottom are the whole point of the file:

* `imagePinnedb` -- every witness in the table survives the re-check;
* `pinsCover` -- every load position of the flat text walk is IN the table, so the census below is
  exhaustive, not a hand-picked sample.

Census at this revision: %(census)s.
Of the certifying witnesses, %(owned)d need the sp-frame assumption.

**Deviations from Rocq.**

1. THE IMAGE.  The table is this tree's image's (xv6-riscv %(rev)s; `KernelSitesDef` deviation 1), not the Rocq weak line's (9dd28f5e): %(nsites)d load sites (Rocq 1611).
2. `vm_cast_no_check (eq_refl true)` ↦ `decide +kernel`.  %(split)s
3. `pinsCover` (Rocq: one `vm_compute` sweep searching the table at every flat-walk position) is
   proved through the added `loadPcs` (the walk's load positions, in order) and `loadPcsEq`
   (`loadPcs = pinPcs`, one linear `decide +kernel` comparison) plus list plumbing; the
   statement is Rocq's.  The generator emits the table in walk order, which is what makes the
   equation hold.
4. Rocq's `Print Assumptions` audit lines are not reproduced (the tree's lint bans new axioms).
   `#print axioms`: `imagePinnedb` `[propext]`; `pinsCover` `[propext, Classical.choice,
   Quot.sound]`, the standard three, from the list lemmas of its plumbing.

**Name map** (Rocq → Lean): `pins`→`pins`, `image_pinnedb`→`imagePinnedb`, `pin_pcs`→`pinPcs`,
`pins_coverb`→`pinsCoverb`, `pins_cover`→`pinsCover`.  Added: `loadPcs`, `loadPcsEq`,
`imagePinnedb<k>` and the chunks `pins<k>` (deviation 2).
-/
import Weak.KernelPinsDef

namespace Weak

open MachCSL KernelPinsDef KernelPinsDef.Pin
"""


def lean_witness(r):
    c, at, own = r['witness'], r['at'], 'true' if r['own'] else 'false'
    if c == 'Stack':
        return 'PStack'
    if c == 'PerCpu':
        return 'PPerCpu 0x%08x' % at
    if c == 'Ctrl':
        return 'PCtrl 0x%08x %s' % (at, own)
    if c == 'Fence':
        return 'PFence 0x%08x %s' % (at, own)
    if c == 'Dep':
        return 'PDep 0x%08x %s' % (at, own)
    if c == 'Call':
        return 'PCall 0x%08x' % at
    return 'PResidue'


def emit_lean(rows, rev, chunk):
    counts = {c: 0 for c in CLASSES}
    owned = 0
    for r in rows:
        counts[r['witness']] += 1
        if r['own']:
            owned += 1
    census = ', '.join('%d %s' % (counts[c], c) for c in CLASSES)
    chunks = [rows[i:i + chunk] for i in range(0, len(rows), chunk)] or [[]]
    split = ('The table is spelled in %d chunks `pins0`…`pins%d` of at most %d entries (`pins` is '
             'their append), each re-checked by its own `decide +kernel` theorem `imagePinnedb<k>`; '
             '`imagePinnedb` is their assembly by `List.all_append` -- a kernel-evaluation budget '
             'split, the statement is Rocq\'s.' % (len(chunks), len(chunks) - 1, chunk))
    head = HEADER % dict(rev=rev, census=census, owned=owned, nsites=len(rows), split=split)
    out = []
    for para in head.split('\n'):
        m = re.match(r'^(\d+\. |   )(.*)$', para)
        if m and len(para) > 100:
            out += textwrap.wrap(m.group(2), 100, initial_indent=m.group(1),
                                 subsequent_indent='   ', break_on_hyphens=False)
        else:
            out.append(para)
    L = ['\n'.join(out)]
    for k, ch in enumerate(chunks):
        L.append('/-- The witness table, entries %d..%d. -/' % (k * chunk, k * chunk + len(ch) - 1))
        L.append('def pins%d : List (Int × Pin) :=' % k)
        if not ch:
            L.append('  []')
        for i, r in enumerate(ch):
            head = '  [ ' if i == 0 else '  , '
            w = lean_witness(r)
            L.append('%s(0x%08x, %s)%s-- %s+0x%x'
                     % (head, r['pc'], w, ' ' * max(1, 32 - len(w)), r['fun'], r['off']))
        if ch:
            L.append('  ]')
        L.append('')
    L.append('/-- THE WITNESS TABLE: one entry per load site of the flat text walk. -/')
    L.append('def pins : List (Int × Pin) :=')
    L += textwrap.wrap(' ++ '.join('pins%d' % k for k in range(len(chunks))), 98,
                       initial_indent='  ', subsequent_indent='    ')
    L.append('')
    L.append('/-! ### THE RE-CHECK, one `decide +kernel` per chunk -/')
    L.append('')
    for k in range(len(chunks)):
        L.append('theorem imagePinnedb%d : pins%d.all (fun p => pinnedb pinFuel p.1 p.2) = true := by'
                 % (k, k))
        L.append('  decide +kernel')
        L.append('')
    L.append('/-- THE RE-CHECK: every witness in the table survives `pinnedb`. -/')
    L.append('theorem imagePinnedb : pins.all (fun p => pinnedb pinFuel p.1 p.2) = true := by')
    L.append('  simp only [pins, List.all_append, Bool.true_and,')
    L += textwrap.wrap(', '.join('imagePinnedb%d' % k for k in range(len(chunks))) + ']', 96,
                       initial_indent='    ', subsequent_indent='    ')
    L.append('')
    L.append('/-! ### EXHAUSTIVENESS: every load position of the flat text walk is in the table above, so')
    L.append('no load site escaped the census. -/')
    L.append('')
    L.append('def pinPcs : List Int := pins.map Prod.fst')
    L.append('')
    L.append('def pinsCoverb : Bool :=')
    L.append('  textPcs.all (fun pc => if roleIsLoad (krole pc) then pinPcs.any (fun q => pc == q) else true)')
    L.append('')
    L.append('/-- The load positions of the flat text walk, in walk order (added: the proof route of')
    L.append('`pinsCover`, deviation 3). -/')
    L.append('def loadPcs : List Int := textPcs.filter (fun pc => roleIsLoad (krole pc))')
    L.append('')
    L.append('/-- The table lists exactly the load positions, in walk order: one linear `decide +kernel`')
    L.append('comparison, where the Rocq sweep searches the table at every position. -/')
    L.append('theorem loadPcsEq : loadPcs = pinPcs := by decide +kernel')
    L.append('')
    L.append('theorem pinsCover : pinsCoverb = true := by')
    L.append('  unfold pinsCoverb')
    L.append('  rw [List.all_eq_true]')
    L.append('  intro pc hpc')
    L.append('  split')
    L.append('  · next h =>')
    L.append('    rw [List.any_eq_true]')
    L.append('    exact ⟨pc, loadPcsEq ▸ List.mem_filter.2 ⟨hpc, h⟩, beq_self_eq_true pc⟩')
    L.append('  · rfl')
    L.append('')
    L.append('end Weak')
    return '\n'.join(L) + '\n', counts, owned


def parse_def_consts(path):
    src = open(path, encoding='utf-8').read()
    got = {}
    for n in ('pinFuel', 'pdfsFuel', 'pinDepth'):
        m = re.search(r'^def %s : Nat := (\d+)' % n, src, re.M)
        got[n] = int(m.group(1)) if m else None
    return got


# ===========================================================================
# 6.  main
# ===========================================================================

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', default='Xv6/KernelImage.lean')
    ap.add_argument('--elf', default='MachCSL/KernelElf.lean')
    ap.add_argument('--out', default='Weak/KernelPins.lean')
    ap.add_argument('--def', dest='defn', default='Weak/KernelPinsDef.lean')
    ap.add_argument('--chunk', type=int, default=100, help='witnesses per decide +kernel theorem')
    ap.add_argument('--json', help='also write the census (Rocq tools/pins.json) here')
    ap.add_argument('--residue', action='store_true', help='print the full residue list')
    ap.add_argument('--check', action='store_true', help='regenerate and diff; write nothing')
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args(argv)
    os.chdir(REPO)
    say = (lambda *x: None) if a.quiet else print

    img = S.Image(a.image, a.elf)
    funs, by_addr = build_funs(img)
    IM = Img(funs)
    FL = Flat(img)
    addrs, _ = img.flat_walk()
    rows = classify(img, funs, by_addr)
    text, counts, owned = emit_lean(rows, img.rev, a.chunk)

    summaries = {}
    for r in rows:
        if r['witness'] == 'Call' and r['callee']:
            k, e = kflow_of(r['at'], IM.at[r['at']][0])
            if r['callee'] not in summaries and k == FL_CALL:
                summaries[r['callee']] = callee_summary(IM, e)
    tgt = audit_targets(img, funs)

    say('load sites %d over %d flat-walk positions (text 0x%08x..0x%08x, xv6-riscv %s)'
        % (len(rows), len(addrs), img.lo, img.hi, img.rev))
    for c in CLASSES:
        say('  %-8s %d' % (c, counts[c]))
    cert = sum(counts[c] for c in ('Stack', 'PerCpu', 'Ctrl', 'Fence', 'Dep'))
    say('  certifying %d (%d assumption-free, %d sp-frame)' % (cert, cert - owned, owned))
    say('  branch/jump target cross-check: %d ok, %d BAD, %d unprinted' % tgt[:3])
    for b in tgt[3][:20]:
        say('    MISMATCH 0x%08x `%s` -> computed 0x%08x' % b)
    say('  callee summaries: %d' % len(summaries))
    for name in sorted(summaries):
        s = summaries[name]
        say('    %-24s 0x%08x first_store_pinned=%s strict=%s fall-through=%s'
            % (name, s['entry'], s['first_store_pinned'], s['strict'], s['fallthrough_class']))
    if a.residue:
        for r in rows:
            if r['witness'] in ('Call', 'Residue'):
                say('  residue 0x%08x %s+0x%x `%s` %s %s %s' % (
                    r['pc'], r['fun'], r['off'], r['text'], r['witness'],
                    ('0x%08x' % r['at']) if r['at'] is not None else '-',
                    r['callee'] or r['why'] or ''))

    probs = []
    junk = [r for r in rows if not r['real']]
    for r in junk:
        probs.append('load-decoding position outside the real instruction stream: 0x%08x %s+0x%x'
                     % (r['pc'], r['fun'], r['off']))
    if tgt[1]:
        probs.append('%d direct targets disagree with objdump' % tgt[1])
    for r in rows:
        if not pinnedb(FL, r['pc'], witness_tuple(r)):
            probs.append('witness %s at 0x%08x %s+0x%x fails the flat re-check'
                         % (lean_witness(r), r['pc'], r['fun'], r['off']))
    if a.json:
        json.dump({'xv6_rev': img.rev, 'fuel': PIN_FUEL, 'dfs_fuel': DFS_FUEL, 'depth': PIN_DEPTH,
                   'sites': rows, 'callee_summaries': summaries},
                  open(a.json, 'w'), indent=1, sort_keys=True)
        say('wrote %s' % a.json)

    if a.check:
        old = open(a.out, encoding='utf-8').read() if os.path.exists(a.out) else ''
        if old != text:
            probs.append('%s is stale (regenerate with tools/gen_weak_pins.py)' % a.out)
            sys.stdout.writelines(difflib.unified_diff(
                old.splitlines(True), text.splitlines(True), a.out, '(regenerated)', n=1))
        got = parse_def_consts(a.defn)
        want = {'pinFuel': PIN_FUEL, 'pdfsFuel': DFS_FUEL, 'pinDepth': PIN_DEPTH}
        for k in want:
            if got.get(k) != want[k]:
                probs.append('%s: %s is %r, the generator uses %r' % (a.defn, k, got.get(k), want[k]))
        for p in probs:
            print('FAIL: ' + p)
        print('gen_weak_pins --check: %s' % ('FAIL' if probs else 'ok'))
        return 1 if probs else 0

    with open(a.out, 'w', encoding='utf-8') as f:
        f.write(text)
    say('wrote %s: %d witnesses' % (a.out, len(rows)))
    for p in probs:
        print('WARNING: ' + p)
    return 1 if probs else 0


if __name__ == '__main__':
    sys.exit(main())

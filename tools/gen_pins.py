#!/usr/bin/env python3
"""gen_pins.py -- THE STATIC PIN CHECKER's witness generator (R-1(B) slice 1).

A sibling of tools/gen_sites.py, one level up in ambition: gen_sites.py
classifies single WORDS, this one classifies LOAD SITES by what the kernel
does with the loaded value before its hart's next store.  Route-b 4g(B): a
load whose result is branched on, fenced after, or fed into the next store is
PINNED on its row, and the graph-level [seg_pin] follows; a load off [sp] or
off a [tp]-derived per-cpu base reads a byte no other hart writes.  What is
left is the OWNERSHIP RESIDUE, which is what the [WProt] port convention has
to cover.

Inputs (the tracked dump only -- never the ELF, never a proof):
  kernel-rocq/KernelSyms.v    symbol table
  kernel-rocq/KernelInstrs.v  image bytes + objdump text

Outputs, all deterministic:
  tools/pins.json     the machine-readable census (per site: pc, word, rd,
                      base, witness, function, plus the audit fields)
  tools/pins.md       the audit tables: counts per class per function, the
                      full residue list, and the path-coverage column
  iris/KernelPins.v   the Rocq witness table [pins] plus the two reflection
                      lemmas [image_pinnedb] and [pins_cover]

THE TWO LAYERS, and where the trust boundary is (route-b 4g.1).

  * THIS FILE IS UNTRUSTED.  Everything it computes is re-checked by
    iris/KernelPinsDef.[pinnedb] with [vm_compute] over the same image bytes,
    through WeakDeps.[deps_of_bits] -- the model's own role decoder, not this
    file's Python port of it.  A disagreement between the port below and
    WeakDeps is a FAILED [image_pinnedb], never a silently wrong claim.

  * SLICE 2 MOVED THE PATH ANALYSIS INTO ROCQ.  [pinnedb] now runs TWO
    checks per certifying witness, both by [vm_compute]:
      - [fwalk], the FALL-THROUGH walk to the named witness pc, which now
        FOLLOWS direct jumps and DESCENDS into direct calls (a return stack
        of depth [pin_depth]) instead of stopping at them; and
      - [pdfs], a fuel-bounded DEPTH-FIRST SEARCH over BOTH arms of every
        conditional branch, the same call descent, and a visited set --
        i.e. exactly the [all_paths] column slice 1 trusted to Python.
    So "every path out of this load reaches a pin before the hart's next
    store" is now a Rocq fact.  The [Summary] table below is an AUDIT
    artifact only: Rocq re-derives it by walking into the callee.

  * THE ONE NEW TRUST ITEM, and it is recorded in the witness itself.  A
    callee's first act is to spill to its OWN stack frame, so descending
    into a call is worthless unless a store through [sp] is not treated as
    the hart's next publication.  A witness therefore carries an [own] bit:
    [own = false] means the check passed with NO store skipped (fully
    value-independent, no ownership claim); [own = true] means it needed
    "a store whose base register is [sp] is the hart's own frame" -- the
    exact dual of the [PStack] LOAD class slice 1 already rests on.  The
    census reports the two counts separately.

  * STILL TRUSTED TO PYTHON: that the flat walk [text_pcs] covers every real
    instruction, and that the bitmask classification agrees with the Sail
    decoder (KernelSitesDef 6.6 items 1 and 4, unchanged).  The branch/jump
    IMMEDIATE decoders below are cross-checked against objdump's printed
    targets by [audit_targets] (reported in pins.md); their Rocq twins are
    checked by the census agreeing.

REPRODUCIBILITY.  Same discipline as gen_sites.py: derived from the tracked
dump, the header records the image revision and the exact invocation, and
re-running after a re-dump rewrites the whole output.  `make check-pins`
regenerates and fails if anything moved.
"""

import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_code as G
import gen_sites as S


# ===========================================================================
# 1.  A PYTHON PORT OF iris/WeakDeps.deps_of_bits
#
# Faithful, constructor for constructor.  It is a PORT and it is untrusted:
# iris/KernelPinsDef.v calls the real thing.  Roles are tuples whose head is
# the WeakDeps constructor name in lower case.
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
    """(rd, srcs) or None.  Mirrors WeakDeps.deps_rd, DLdRes dropped."""
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
# 2.  CONTROL FLOW -- a PORT of iris/KernelPinsDef.kflow_of
#
# Every control transfer of the image, decoded from the word.  The Rocq twin
# is [kflow_of]; these two must agree instruction for instruction, and the
# census agreeing is what says they do.  [audit_targets] additionally checks
# every direct target against objdump's printed one.
#
# SLICE-1 HOLE CLOSED HERE: [flow_kind] classified control flow through
# WeakDeps' ROLES, and [c.j] has no role (deps_of_c1 f3=5 is ORnone), so a
# straight-line walk stepped straight past an unconditional compressed jump.
# No slice-1 witness actually crossed one (checked), but the checker would
# have accepted it.  Control flow is now decoded on its own.
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
# 3.  THE TWO WALKS -- ports of iris/KernelPinsDef.[fwalk] and [pdfs]
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
        self.at = {a: (w, wd) for a, w, wd in insns}


def build_funs(img):
    out, by_addr = [], {}
    starts = img.symaddrs
    for i, s in enumerate(starts):
        hi = starts[i + 1] if i + 1 < len(starts) else img.hi
        ins = G.instructions(img.bytes, s, hi)
        if not ins:
            continue
        f = Fun(img.symname[s], s, hi, ins)
        out.append(f)
        for a, _, _ in ins:
            by_addr[a] = f
    return out, by_addr


# ---- the taint, as an ORDERED LIST with no duplicates.  This mirrors
# KernelPinsDef.[taint_upd1] exactly (which slice 2 made duplicate-free so
# that the DFS's visited set can compare taints syntactically); using a
# Python set here instead would make the two checkers explore different
# state spaces and the reflection lemma would start failing for no reason.

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
    """The flat instruction map the two walks step over."""
    def __init__(self, funs):
        self.at = {}
        for f in funs:
            for a, w, wd in f.insns:
                self.at[a] = (w, S.size_of(w))

    def __contains__(self, a):
        return a in self.at


def pstep(IM, own, st):
    """ONE state of the walk; the port of KernelPinsDef.[pstep].

    Returns [] when the state IS a pin (a fence, a branch on the tainted
    value, a store fed by it), None when the path FAILS (an unpinned store
    that is not a skipped stack spill, an indirect transfer, a return with
    an empty stack, a call past the inlining depth, an unknown pc), and
    otherwise the list of successor states (two at a conditional branch)."""
    pc, t, rs = st
    if pc not in IM.at:
        return None
    w, wd = IM.at[pc]
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
    """The FALL-THROUGH walk to a named witness pc (KernelPinsDef.[fwalk]):
    the not-taken arm of every conditional branch, but direct jumps FOLLOWED
    and direct calls DESCENDED into.  Returns the taint at [stop], or None."""
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
        if pc not in IM.at:
            return ('Residue', None, 'offmap')
        w, wd = IM.at[pc]
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
                return ('Call', pc, 'indirect') if deps_of_bits(w)[0] == 'jalr' \
                    and deps_of_bits(w)[1] != 0 else ('Residue', pc, 'indirect')
            if k == FL_RET and not rs:
                return ('Residue', pc, 'ret')
        ns = pstep(IM, own, st)
        if not ns:
            return ('Residue', pc, 'stuck')
        st = ns[0]
    return ('Residue', None, 'window')


def pdfs(IM, own, st0, fuel=DFS_FUEL):
    """ALL PATHS (KernelPinsDef.[pdfs]): a fuel-bounded DFS with a visited
    set.  True iff EVERY path out of the load reaches a pin before any store
    the load's value does not feed."""
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
    reaches the load's base, or None.  Unchanged from slice 1: the [PPerCpu]
    re-check is a straight-line stretch inside one function."""
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


# ===========================================================================
# 3b.  CALLEE SUMMARIES -- an AUDIT artifact (Rocq re-derives them by
#      walking into the callee, so nothing downstream trusts this table)
# ===========================================================================

ARGREGS = [10, 11, 12, 13, 14, 15, 16, 17]


def callee_summary(IM, by_addr, entry):
    """Summary of one callee, over ITS OWN CFG, with a0 standing for the
    caller's tainted argument:

      first_store_pinned  every path from the entry reaches a store only
                          after a pin of a0 (this is [pdfs] run at the entry
                          with the taint {a0}, in the sp-owned regime);
      strict              the same with NO store skipped at all;
      first_store         the pc of the first store on the fall-through path;
      returns_branched    the caller's use of the return value -- filled in
                          per CALL SITE, not here (see [classify]).
    """
    st = (entry, [ARGREGS[0]], ())
    c, at, why = fclassify(IM, True, st)
    return {
        'entry': entry,
        'first_store_pinned': pdfs(IM, True, st),
        'strict': pdfs(IM, False, st),
        'fallthrough_class': c,
        'first_store': at,
        'why': why,
    }


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
        # PREFER THE ASSUMPTION-FREE REGIME.  [own = False] skips no store at
        # all; only if that fails is the sp-frame regime tried, and then the
        # witness records it.
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
    """CROSS-CHECK the immediate decoders against objdump's printed target.

    objdump renders a direct branch/jump as `<mnemonic> ...,<hex> <sym+off>`;
    the hex is the target.  Any disagreement is a decoder bug in THIS file
    (and, since the Rocq twin is a line-by-line port, probably in that too)."""
    ok = bad = skipped = 0
    bads = []
    for f in funs:
        for a, w, _ in f.insns:
            k, tgt = kflow_of(a, w)
            if k not in (FL_BRANCH, FL_JUMP, FL_CALL):
                continue
            txt = img.disasm.get(a, '')
            m = re.search(r'0x([0-9a-f]+)|\b([0-9a-f]{8,16})\s+<', txt)
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


# ===========================================================================
# 5.  Reports
# ===========================================================================

def write_md(path, rows, meta, summaries, tgt_audit):
    L = ['# Kernel load-site PINS', '',
         'AUTO-GENERATED by `tools/gen_pins.py` -- do not edit by hand.', '',
         '| | |', '|---|---|',
         '| image revision (`XV6_REV`) | `%s` |' % meta['rev'],
         '| text range | `0x%08x .. 0x%08x` |' % (meta['lo'], meta['hi']),
         '| flat-walk positions | %d |' % meta['positions'],
         '| load sites | %d |' % len(rows),
         '| fall-through walk fuel | %d instructions |' % PIN_FUEL,
         '| all-paths DFS fuel | %d states |' % DFS_FUEL,
         '| call inlining depth | %d |' % PIN_DEPTH,
         '| regenerate | `%s` |' % meta['invocation'], '']

    counts = {c: 0 for c in CLASSES}
    owned = {c: 0 for c in CLASSES}
    for r in rows:
        counts[r['witness']] += 1
        if r['own']:
            owned[r['witness']] += 1
    L += ['## Census', '',
          'The `sp-frame` column counts the witnesses that needed the ONE',
          'ownership assumption (a store through `sp` is the hart\'s own',
          'frame, so it is not the publication the pin is about -- the dual',
          'of the `Stack` LOAD class).  The rest are assumption-free.', '',
          '| witness class | count | of which sp-frame | what it certifies |',
          '|---|---|---|---|']
    WHAT = {
        'Stack': 'base register is `sp` -- the hart\'s own stack, no other hart writes it',
        'PerCpu': 'base tainted from `tp` (the `mv/slli/auipc/add` idiom) -- per-cpu data',
        'Ctrl': 'ON EVERY PATH a branch on the loaded value before the hart\'s next store',
        'Fence': 'ON EVERY PATH a fence before the hart\'s next store',
        'Dep': 'ON EVERY PATH the next store\'s address or data register is fed by the load',
        'Call': 'RESIDUE: a call past the inlining depth, or an indirect call',
        'Residue': 'RESIDUE: unpinned -- the `WProt` / ownership bucket',
    }
    for c in CLASSES:
        L.append('| %s | %d | %d | %s |' % (c, counts[c], owned[c], WHAT[c]))
    L += ['| **total** | **%d** | **%d** | |'
          % (len(rows), sum(owned.values())), '']

    cert = sum(counts[c] for c in ('Stack', 'PerCpu', 'Ctrl', 'Fence', 'Dep'))
    L += ['%d of %d load sites carry a CERTIFYING witness; %d of those need'
          % (cert, len(rows), sum(owned.values())),
          'the sp-frame assumption, %d need nothing beyond the image.'
          % (cert - sum(owned.values())), '',
          'Every certifying witness is now checked ON ALL PATHS in Rocq',
          '(`KernelPinsDef.pdfs`): slice 1\'s `all_paths` column was a Python',
          'fact, this is a `vm_compute` one.', '']

    L += ['## Direct-target decoder cross-check', '',
          'Every conditional branch / direct jump / direct call in the image,',
          'with `kflow_of`\'s computed target checked against the target',
          'objdump printed.', '',
          '| agreeing | disagreeing | no printed target |', '|---|---|---|',
          '| %d | %d | %d |' % (tgt_audit[0], tgt_audit[1], tgt_audit[2]), '']
    for a, txt, tgt in tgt_audit[3][:20]:
        L.append('- MISMATCH `0x%08x` `%s` -> computed `0x%08x`' % (a, txt, tgt))
    L.append('')

    per = {}
    for r in rows:
        per.setdefault(r['fun'], {c: 0 for c in CLASSES})[r['witness']] += 1
    L += ['## Counts per class per function', '',
          '| function | ' + ' | '.join(CLASSES) + ' | total |',
          '|---' * (len(CLASSES) + 2) + '|']
    for f in sorted(per, key=lambda f: (-sum(per[f].values()), f)):
        c = per[f]
        L.append('| `%s` | %s | %d |'
                 % (f, ' | '.join(str(c[k]) for k in CLASSES), sum(c.values())))
    L.append('')

    L += ['## Callee summaries (AUDIT ONLY -- nothing trusts this table)', '',
          'One row per callee reached from a `Call`-classified load site.',
          '`first_store_pinned` is the all-paths DFS run at the callee\'s',
          'entry with the caller\'s argument register `a0` tainted;',
          '`strict` is the same with no store skipped at all.  Rocq does NOT',
          'read this table: `pinnedb` walks INTO the callee itself (a return',
          'stack of depth %d), so the summary is re-derived, not assumed.'
          % PIN_DEPTH, '',
          '| callee | entry | first_store_pinned | strict | fall-through | first store |',
          '|---|---|---|---|---|---|']
    for name in sorted(summaries):
        s = summaries[name]
        L.append('| `%s` | `0x%08x` | %s | %s | %s | %s |'
                 % (name, s['entry'], s['first_store_pinned'], s['strict'],
                    s['fallthrough_class'],
                    ('`0x%08x`' % s['first_store']) if s['first_store'] else ''))
    L.append('')

    res = [r for r in rows if r['witness'] in ('Call', 'Residue')]
    L += ['## The residue, in full (%d sites)' % len(res), '',
          'Every site the checker does NOT pin.  `Call` is a call past the',
          'inlining depth or an indirect call; `Residue` is the ownership',
          'bucket that the `WProt` port convention (route-b 4g(A)) covers.', '',
          '| pc | site | insn | class | at | why / callee |',
          '|---|---|---|---|---|---|']
    for r in res:
        L.append('| `0x%08x` | `%s+0x%x` | `%s` | %s | %s | %s |'
                 % (r['pc'], r['fun'], r['off'], r['text'], r['witness'],
                    ('`0x%08x`' % r['at']) if r['at'] is not None else '',
                    r['callee'] or r['why'] or ''))
    L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


COQ_HEADER = """(* KernelPins.v -- AUTO-GENERATED by tools/gen_pins.py.  DO NOT EDIT BY HAND.

   THE WITNESS TABLE for the static pin checker (route-b 4g(B), slice 2):
   one [pin] per LOAD site of [KernelSitesDef.text_pcs], re-checked against
   the image by [KernelPinsDef.pinnedb] under [vm_compute].

   Each certifying witness now carries TWO facts, both re-checked:
     - the FALL-THROUGH pin it names ([fwalk], which follows direct jumps
       and descends into direct calls to depth [pin_depth]); and
     - that EVERY path out of the load reaches some pin before the hart's
       next store ([pdfs], the fuel-bounded all-paths DFS).
   The boolean in each witness is the [own] bit: [true] means the check
   skipped stores through [sp] as the hart's own frame (the dual of
   [PStack]); [false] means it skipped nothing.

   The two reflection lemmas at the bottom are the whole point of the file:

     [image_pinnedb]  every witness in the table survives the re-check;
     [pins_cover]     every load position of the flat text walk is IN the
                      table -- so the census below is exhaustive, not a
                      hand-picked sample.

   Both are [vm_cast_no_check (eq_refl true)], the trust shape of
   [KernelSitesDef.kernel_discipline] (durable-notes: a [vm_compute]-closed
   equation leaves a bare [eq_refl] that the kernel re-reduces LAZILY at
   [Qed], which on a whole-image walk overflows the stack).

   Census at this revision: %(census)s.
   Of the certifying witnesses, %(owned)d need the sp-frame assumption.

   Image revision (XV6_REV): %(rev)s
   Regenerate with:  %(invocation)s                                        *)
From Stdlib Require Import ZArith List Bool.
Require Import KernelSitesDef KernelPinsDef.
Import ListNotations.
Local Open Scope Z_scope.
"""


def emit_coq(path, rows, meta):
    counts = {c: 0 for c in CLASSES}
    owned = 0
    for r in rows:
        counts[r['witness']] += 1
        if r['own']:
            owned += 1
    census = ', '.join('%d %s' % (counts[c], c) for c in CLASSES)
    L = [COQ_HEADER % dict(rev=meta['rev'], invocation=meta['invocation'],
                           census=census, owned=owned)]
    L.append('')
    L.append('Definition pins : list (Z * pin) :=')
    for i, r in enumerate(rows):
        head = '  [ ' if i == 0 else '  ; '
        c, at, own = r['witness'], r['at'], 'true' if r['own'] else 'false'
        if c == 'Stack':
            w = 'PStack'
        elif c == 'PerCpu':
            w = 'PPerCpu 0x%08x' % at
        elif c == 'Ctrl':
            w = 'PCtrl 0x%08x %s' % (at, own)
        elif c == 'Fence':
            w = 'PFence 0x%08x %s' % (at, own)
        elif c == 'Dep':
            w = 'PDep 0x%08x %s' % (at, own)
        elif c == 'Call':
            w = 'PCall 0x%08x' % at
        else:
            w = 'PResidue'
        L.append('%s(0x%08x, %s)%s(* %s+0x%x *)'
                 % (head, r['pc'], w, ' ' * max(1, 32 - len(w)),
                    r['fun'], r['off']))
    L.append('  ].')
    L.append('')
    L.append('(* THE RE-CHECK.  One [vm_compute] over the whole table. *)')
    L.append('Lemma image_pinnedb :')
    L.append('  forallb (fun p => pinnedb pin_fuel (fst p) (snd p)) pins = true.')
    L.append('Proof. vm_cast_no_check (eq_refl true). Qed.')
    L.append('')
    L.append('(* EXHAUSTIVENESS.  Every load position of the flat text walk is')
    L.append('   in the table above, so no load site escaped the census. *)')
    L.append('Definition pin_pcs : list Z := map fst pins.')
    L.append('')
    L.append('Definition pins_coverb : bool :=')
    L.append('  forallb (fun pc => if role_is_load (krole pc)')
    L.append('                     then existsb (Z.eqb pc) pin_pcs else true)')
    L.append('          text_pcs.')
    L.append('')
    L.append('Lemma pins_cover : pins_coverb = true.')
    L.append('Proof. vm_cast_no_check (eq_refl true). Qed.')
    L.append('')
    L.append('(* AUDIT *)')
    L.append('Print Assumptions image_pinnedb.')
    L.append('Print Assumptions pins_cover.')
    L.append('')
    open(path, 'w').write('\n'.join(L))
    return counts, owned


# ===========================================================================
# 6.  main
# ===========================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kernel-rocq', default='kernel-rocq')
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--tools', default='tools')
    ap.add_argument('--check', action='store_true',
                    help='exit non-zero if a witness fails its own re-check')
    args = ap.parse_args()

    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    rev = S.xv6_rev(root)
    invocation = 'python3 tools/gen_pins.py'

    img = S.Image(args.kernel_rocq)
    funs, by_addr = build_funs(img)
    IM = Img(funs)
    addrs, _ = img.flat_walk()
    rows = classify(img, funs, by_addr)
    meta = {'rev': rev, 'lo': img.lo, 'hi': img.hi,
            'positions': len(addrs), 'invocation': invocation}

    summaries = {}
    for r in rows:
        if r['witness'] == 'Call' and r['callee']:
            k, e = kflow_of(r['at'], IM.at[r['at']][0])
            if r['callee'] not in summaries:
                summaries[r['callee']] = callee_summary(IM, by_addr, e)
    tgt_audit = audit_targets(img, funs)

    jpath = os.path.join(args.tools, 'pins.json')
    json.dump({'xv6_rev': rev, 'fuel': PIN_FUEL, 'dfs_fuel': DFS_FUEL,
               'depth': PIN_DEPTH, 'sites': rows,
               'callee_summaries': summaries},
              open(jpath, 'w'), indent=1, sort_keys=True)
    mpath = os.path.join(args.tools, 'pins.md')
    write_md(mpath, rows, meta, summaries, tgt_audit)
    cpath = os.path.join(args.iris, 'KernelPins.v')
    counts, owned = emit_coq(cpath, rows, meta)

    print('load sites %d over %d flat-walk positions' % (len(rows), len(addrs)))
    for c in CLASSES:
        print('  %-8s %d' % (c, counts[c]))
    cert = sum(counts[c] for c in ('Stack', 'PerCpu', 'Ctrl', 'Fence', 'Dep'))
    print('  certifying %d (%d assumption-free, %d sp-frame)'
          % (cert, cert - owned, owned))
    print('  branch/jump target cross-check: %d ok, %d BAD, %d unprinted'
          % (tgt_audit[0], tgt_audit[1], tgt_audit[2]))
    print('  callee summaries: %d' % len(summaries))
    print('wrote %s, %s, %s' % (jpath, mpath, cpath))

    junk = [r for r in rows if not r['real']]
    if junk:
        print('LOAD-DECODING POSITIONS OUTSIDE THE REAL INSTRUCTION STREAM: %d'
              % len(junk))
        for r in junk[:20]:
            print('  0x%08x %s+0x%x' % (r['pc'], r['fun'], r['off']))
    if args.check and (junk or tgt_audit[1]):
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

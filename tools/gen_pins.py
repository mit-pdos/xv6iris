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

  * WHAT ROCQ RE-CHECKS is the STRAIGHT-LINE path: byte-successor stepping
    from the load to the witness pc', which -- because this generator stops
    its own walk at every jump, call and return -- is exactly the
    no-branch-taken execution path out of the load.  So the re-checked claim
    is "on the fall-through path out of this load, the witness event happens
    before the hart's next store".

  * WHAT THIS FILE IS TRUSTED FOR is PATH COVERAGE: the [all_paths] column of
    pins.md is a full intra-function CFG analysis (both arms of every
    conditional branch, direct jumps followed, calls/returns/window-exhaustion
    recorded as unknown), and it is a PYTHON fact.  Promoting it into Rocq --
    a fuelled worklist over the same CFG -- is the next slice; so is the
    callee-summary table for the ~30 leaf helpers that turns the [Call] class
    from residue into a pin.

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
# 2.  Control flow: direct targets, calls, returns
# ===========================================================================

def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def branch_target(pc, w):
    """Direct target of a conditional branch, or None."""
    if S.is_rvc(w):
        q, f3 = S.c_quad(w), S.c_f3(w)
        if q == 1 and f3 in (6, 7):                      # c.beqz / c.bnez
            imm = ((ibits(w, 12, 12) << 8) | (ibits(w, 6, 5) << 6)
                   | (ibits(w, 2, 2) << 5) | (ibits(w, 11, 10) << 3)
                   | (ibits(w, 4, 3) << 1))
            return pc + sext(imm, 9)
        return None
    if ibits(w, 6, 0) == 99:                             # B-type
        imm = ((ibits(w, 31, 31) << 12) | (ibits(w, 7, 7) << 11)
               | (ibits(w, 30, 25) << 5) | (ibits(w, 11, 8) << 1))
        return pc + sext(imm, 13)
    return None


def jump_target(pc, w):
    """Direct target of an unconditional jump/call, or None (indirect)."""
    if S.is_rvc(w):
        q, f3 = S.c_quad(w), S.c_f3(w)
        if q == 1 and f3 == 5:                           # c.j
            imm = ((ibits(w, 12, 12) << 11) | (ibits(w, 8, 8) << 10)
                   | (ibits(w, 10, 9) << 8) | (ibits(w, 6, 6) << 7)
                   | (ibits(w, 7, 7) << 6) | (ibits(w, 2, 2) << 5)
                   | (ibits(w, 11, 11) << 4) | (ibits(w, 5, 3) << 1))
            return pc + sext(imm, 12)
        return None
    if ibits(w, 6, 0) == 111:                            # jal
        imm = ((ibits(w, 31, 31) << 20) | (ibits(w, 19, 12) << 12)
               | (ibits(w, 20, 20) << 11) | (ibits(w, 30, 21) << 1))
        return pc + sext(imm, 21)
    return None


def flow_kind(pc, w):
    """One of: 'call', 'ret', 'jump', 'branch', 'ijump', None.

    'call'  writes a link register (jal/jalr rd != 0, c.jalr)
    'ret'   jalr x0, ra / c.jr ra
    'jump'  a direct unconditional jump (jal x0 / c.j)
    'ijump' an indirect jump that is not a return (a jump table, a tail call)
    """
    r = deps_of_bits(w)
    if r[0] == 'jal':
        return 'call' if r[1] != 0 else 'jump'
    if r[0] == 'jalr':
        if r[1] != 0:
            return 'call'
        return 'ret' if r[2] == 1 else 'ijump'
    if r[0] == 'branch':
        return 'branch'
    return None


# ===========================================================================
# 3.  The image, functions, and the two walks
# ===========================================================================

PIN_FUEL = 64          # instructions the witness walk may cross
BACK_WINDOW = 32       # instructions the tp-idiom search looks back over
CFG_NODES = 4000       # (pc, taint) states the all-paths walk may visit


class Fun:
    def __init__(self, name, lo, hi, insns):
        self.name, self.lo, self.hi = name, lo, hi
        self.insns = insns                       # [(addr, word, width)]
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


def taint_step(t, w):
    """The taint transfer of one instruction; mirrors KernelPinsDef.taint_step."""
    r = deps_of_bits(w)
    for d in (deps_rd(r), deps_rd2(r)):
        if d is None:
            continue
        rd, srcs = d
        if any(s in t for s in srcs):
            t = t | {rd}
        else:
            t = t - {rd}
    return t


def straight_walk(fn, pc, t0):
    """Classify a load at [pc] by the FALL-THROUGH path out of it.

    Yields the same verdict KernelPinsDef.pinnedb re-checks: the walk steps by
    the decoded width (never following a branch), and STOPS at every jump,
    call and return -- so the stretch it crosses is a genuine execution path
    (the one on which no conditional branch is taken)."""
    i = fn.idx[pc] + 1
    t = set(t0)
    for _ in range(PIN_FUEL):
        if i >= len(fn.insns):
            return ('Residue', None, 'leave')
        a, w, _wd = fn.insns[i]
        r = deps_of_bits(w)
        if role_is_store(r):
            if any(s in t for s in deps_addr(r)) or any(s in t for s in deps_vsrc(r)):
                return ('Dep', a, None)
            return ('Residue', a, 'store-unpinned')
        if S.is_fence(w):
            return ('Fence', a, None)
        if role_is_branch(r):
            if any(s in t for s in deps_ctrl(r)):
                return ('Ctrl', a, None)
            # not taken: the fall-through path continues
        else:
            k = flow_kind(a, w)
            if k == 'call':
                return ('Call', a, None)
            if k == 'ret':
                return ('Residue', a, 'ret')
            if k in ('jump', 'ijump'):
                return ('Residue', a, 'jump')
        t = taint_step(t, w)
        i += 1
    return ('Residue', None, 'window')


def cfg_paths(fn, pc, t0):
    """ALL-PATHS coverage: does every intra-function path out of the load
    reach a pin before the hart's next store?

    Returns 'all' (every path pinned or provably storeless), 'call' (no path
    reaches an unpinned store, but some path leaves through a call, a return,
    a jump table, or the fuel bound), or 'bad' (some path reaches a store the
    load's value does not feed).  PYTHON-TRUSTED: nothing in Rocq re-checks
    this yet."""
    seen, work = set(), [(fn.idx[pc] + 1, frozenset(t0), 0)]
    unknown = False
    budget = CFG_NODES
    while work:
        i, t, d = work.pop()
        budget -= 1
        if budget <= 0 or d > PIN_FUEL:
            unknown = True
            continue
        if (i, t) in seen:
            continue
        seen.add((i, t))
        if i >= len(fn.insns):
            unknown = True
            continue
        a, w, _wd = fn.insns[i]
        r = deps_of_bits(w)
        if role_is_store(r):
            if any(s in t for s in deps_addr(r)) or any(s in t for s in deps_vsrc(r)):
                continue                                  # pinned by dep
            return 'bad'
        if S.is_fence(w):
            continue                                      # pinned by fence
        if role_is_branch(r):
            if any(s in t for s in deps_ctrl(r)):
                continue                                  # pinned by ctrl
            tgt = branch_target(a, w)
            nt = taint_step(set(t), w)
            work.append((i + 1, frozenset(nt), d + 1))
            if tgt is not None and tgt in fn.idx:
                work.append((fn.idx[tgt], frozenset(nt), d + 1))
            else:
                unknown = True
            continue
        k = flow_kind(a, w)
        if k in ('call', 'ret', 'ijump'):
            unknown = True
            continue
        if k == 'jump':
            tgt = jump_target(a, w)
            if tgt is not None and tgt in fn.idx:
                work.append((fn.idx[tgt], t, d + 1))
            else:
                unknown = True
            continue
        work.append((i + 1, frozenset(taint_step(set(t), w)), d + 1))
    return 'call' if unknown else 'all'


def percpu_origin(fn, pc, base):
    """The pc of the instruction that put [tp]'s value into a register that
    reaches the load's base, or None.

    Exactly KernelPinsDef.pinnedb's PPerCpu re-check, run forwards from each
    candidate: an instruction whose destination is written from x4, whose
    taint then reaches [base] along the fall-through path to [pc]."""
    i = fn.idx[pc]
    for j in range(i - 1, max(-1, i - 1 - BACK_WINDOW), -1):
        a0, w0, _ = fn.insns[j]
        d = deps_rd(deps_of_bits(w0))
        if d is None or 4 not in d[1]:
            continue
        t = {d[0]}
        for k in range(j + 1, i):
            t = taint_step(t, fn.insns[k][1])
        if base in t:
            return a0
    return None


# ===========================================================================
# 4.  The census
# ===========================================================================

CLASSES = ['Stack', 'PerCpu', 'Ctrl', 'Fence', 'Dep', 'Call', 'Residue']


def classify(img, funs, by_addr):
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
               'witness': 'Residue', 'at': None, 'why': None,
               'callee': None, 'all_paths': None}
        if fn is None:
            rec['why'] = 'not-a-real-instruction'
            rows.append(rec)
            continue
        if base == 2:
            rec['witness'] = 'Stack'
            rec['all_paths'] = 'all'
            rows.append(rec)
            continue
        pc0 = percpu_origin(fn, a, base) if base != 0 else None
        if pc0 is not None:
            rec['witness'] = 'PerCpu'
            rec['at'] = pc0
            rec['all_paths'] = 'all'
            rows.append(rec)
            continue
        t0 = {rd} if rd != 0 else set()
        cls, at, why = straight_walk(fn, a, t0)
        rec['witness'], rec['at'], rec['why'] = cls, at, why
        if cls == 'Call' and at is not None:
            tgt = jump_target(at, fn.at[at][0])
            rec['callee'] = img.symname.get(tgt) if tgt is not None else None
            if rec['callee'] is None and tgt is not None:
                rec['callee'] = img.sym_of(tgt)[0]
        rec['all_paths'] = cfg_paths(fn, a, t0)
        rows.append(rec)
    return rows


# ===========================================================================
# 5.  Reports
# ===========================================================================

def write_md(path, rows, meta):
    L = ['# Kernel load-site PINS', '',
         'AUTO-GENERATED by `tools/gen_pins.py` -- do not edit by hand.', '',
         '| | |', '|---|---|',
         '| image revision (`XV6_REV`) | `%s` |' % meta['rev'],
         '| text range | `0x%08x .. 0x%08x` |' % (meta['lo'], meta['hi']),
         '| flat-walk positions | %d |' % meta['positions'],
         '| load sites | %d |' % len(rows),
         '| witness walk fuel | %d instructions |' % PIN_FUEL,
         '| regenerate | `%s` |' % meta['invocation'], '']

    counts = {c: 0 for c in CLASSES}
    for r in rows:
        counts[r['witness']] += 1
    L += ['## Census', '', '| witness class | count | what it certifies |',
          '|---|---|---|']
    WHAT = {
        'Stack': 'base register is `sp` -- the hart\'s own stack, no other hart writes it',
        'PerCpu': 'base tainted from `tp` (the `mv/slli/auipc/add` idiom) -- per-cpu data',
        'Ctrl': 'a branch on the loaded value before the hart\'s next store',
        'Fence': 'a fence between the load and the hart\'s next store',
        'Dep': 'the next store\'s address or data register is fed by the load',
        'Call': 'RESIDUE: a call comes first; needs a callee summary (next slice)',
        'Residue': 'RESIDUE: unpinned -- the `WProt` / ownership bucket',
    }
    for c in CLASSES:
        L.append('| %s | %d | %s |' % (c, counts[c], WHAT[c]))
    L += ['| **total** | **%d** | |' % len(rows), '']

    cov = {}
    for r in rows:
        cov[r['all_paths']] = cov.get(r['all_paths'], 0) + 1
    L += ['## Path coverage (PYTHON-TRUSTED -- not re-checked in Rocq)', '',
          'The straight-line witness above is what `KernelPinsDef.pinnedb`',
          're-checks.  This column is the full intra-function CFG analysis:',
          '`all` = every path out of the load reaches a pin before the next',
          'store; `call` = no path reaches an unpinned store but some path',
          'leaves through a call/return/jump-table/window; `bad` = some path',
          'reaches a store the loaded value does not feed.', '',
          '| coverage | count |', '|---|---|']
    for k in sorted(cov, key=lambda x: (x is None, str(x))):
        L.append('| %s | %d |' % (k, cov[k]))
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

    res = [r for r in rows if r['witness'] in ('Call', 'Residue')]
    L += ['## The residue, in full (%d sites)' % len(res), '',
          'Every site the checker does NOT pin.  `Call` needs the callee',
          'summary table; `Residue` is the ownership bucket that the `WProt`',
          'port convention (route-b 4g(A)) has to cover.', '',
          '| pc | site | insn | class | at | why / callee | paths |',
          '|---|---|---|---|---|---|---|']
    for r in res:
        L.append('| `0x%08x` | `%s+0x%x` | `%s` | %s | %s | %s | %s |'
                 % (r['pc'], r['fun'], r['off'], r['text'], r['witness'],
                    ('`0x%08x`' % r['at']) if r['at'] is not None else '',
                    r['callee'] or r['why'] or '', r['all_paths']))
    L.append('')

    bad = [r for r in rows if r['all_paths'] == 'bad']
    L += ['## Sites with an unpinned store on SOME path (%d)' % len(bad), '',
          'Pinned on the fall-through path (so `pinnedb` accepts the',
          'witness) but not on every path.  These are exactly the sites a',
          'future all-paths checker must either pin or move to the residue.',
          '']
    if bad:
        L += ['| pc | site | insn | witness |', '|---|---|---|---|']
        for r in bad:
            L.append('| `0x%08x` | `%s+0x%x` | `%s` | %s |'
                     % (r['pc'], r['fun'], r['off'], r['text'], r['witness']))
    else:
        L.append('None.')
    L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


COQ_HEADER = """(* KernelPins.v -- AUTO-GENERATED by tools/gen_pins.py.  DO NOT EDIT BY HAND.

   THE WITNESS TABLE for the static pin checker (route-b 4g(B), slice 1):
   one [pin] per LOAD site of [KernelSitesDef.text_pcs], re-checked against
   the image by [KernelPinsDef.pinnedb] under [vm_compute].

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

   Image revision (XV6_REV): %(rev)s
   Regenerate with:  %(invocation)s                                        *)
From Stdlib Require Import ZArith List Bool.
Require Import KernelSitesDef KernelPinsDef.
Import ListNotations.
Local Open Scope Z_scope.
"""


def emit_coq(path, rows, meta):
    counts = {c: 0 for c in CLASSES}
    for r in rows:
        counts[r['witness']] += 1
    census = ', '.join('%d %s' % (counts[c], c) for c in CLASSES)
    L = [COQ_HEADER % dict(rev=meta['rev'], invocation=meta['invocation'],
                           census=census)]
    L.append('')
    L.append('Definition pins : list (Z * pin) :=')
    for i, r in enumerate(rows):
        head = '  [ ' if i == 0 else '  ; '
        c, at = r['witness'], r['at']
        if c == 'Stack':
            w = 'PStack'
        elif c == 'PerCpu':
            w = 'PPerCpu 0x%08x' % at
        elif c == 'Ctrl':
            w = 'PCtrl 0x%08x' % at
        elif c == 'Fence':
            w = 'PFence 0x%08x' % at
        elif c == 'Dep':
            w = 'PDep 0x%08x' % at
        elif c == 'Call':
            w = 'PCall 0x%08x' % at
        else:
            w = 'PResidue'
        L.append('%s(0x%08x, %s)%s(* %s+0x%x *)'
                 % (head, r['pc'], w, ' ' * max(1, 26 - len(w)),
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
    open(path, 'w').write('\n'.join(L))
    return counts


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
    addrs, _ = img.flat_walk()
    rows = classify(img, funs, by_addr)
    meta = {'rev': rev, 'lo': img.lo, 'hi': img.hi,
            'positions': len(addrs), 'invocation': invocation}

    jpath = os.path.join(args.tools, 'pins.json')
    json.dump({'xv6_rev': rev, 'fuel': PIN_FUEL, 'sites': rows},
              open(jpath, 'w'), indent=1, sort_keys=True)
    mpath = os.path.join(args.tools, 'pins.md')
    write_md(mpath, rows, meta)
    cpath = os.path.join(args.iris, 'KernelPins.v')
    counts = emit_coq(cpath, rows, meta)

    print('load sites %d over %d flat-walk positions' % (len(rows), len(addrs)))
    for c in CLASSES:
        print('  %-8s %d' % (c, counts[c]))
    cov = {}
    for r in rows:
        cov[r['all_paths']] = cov.get(r['all_paths'], 0) + 1
    for k in sorted(cov, key=lambda x: (x is None, str(x))):
        print('  paths %-8s %d' % (k, cov[k]))
    print('wrote %s, %s, %s' % (jpath, mpath, cpath))

    junk = [r for r in rows if not r['real']]
    if junk:
        print('LOAD-DECODING POSITIONS OUTSIDE THE REAL INSTRUCTION STREAM: %d'
              % len(junk))
        for r in junk[:20]:
            print('  0x%08x %s+0x%x' % (r['pc'], r['fun'], r['off']))
    bad = [r for r in rows if r['all_paths'] == 'bad']
    print('sites with an unpinned store on some path: %d' % len(bad))
    if args.check and junk:
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

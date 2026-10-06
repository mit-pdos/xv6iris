#!/usr/bin/env python3
"""gen_weak_sites.py -- ENUMERATE the kernel image's memory-ordering sites (Lean).

The Lean retarget of the Rocq weak line's tools/gen_sites.py.  It reads the
tracked kernel dumps of this tree -- never the ELF, never a proof:

  Xv6/KernelImage.lean     the text (address, width, encoding, objdump line)
                           and the symbol table (namespace MachCSL.KernelSyms)
  MachCSL/KernelElf.lean   the loaded segment's bytes (what Weak/KernelSitesDef
                           reads through `KernelElf.elfByte`)

and reports every place in the image where the weak-memory discipline has a
static shape:

  fence     every FENCE / FENCE.I, with its pred/succ kind bits and its
            stream neighbours
  amo       every AMO / LR / SC, with its aq / rl bits
  racy-load a plain load whose STREAM SUCCESSOR is an acquire fence (r,rw)
  release   a plain store whose STREAM PREDECESSOR is a release fence (rw,w)

OUTPUTS.

  Weak/KernelSites.lean (always) the per-site DECODE LINKAGE: for each
      enumerated site, the Sail decoder's verdict on its encoding word,
      `decodesAll32`/`decodesAll16` (MachCSL.MConf) proved through
      `decodesAll32_bridge`/`decodesAll16_bridge` -- the kernel evaluates the
      decoder on the reference register maps (`rfl`), Lean's replacement for
      Rocq's `exact kd_<word>` catalogue lookup -- plus the fact that the word
      IS the image's bytes at that pc (`kw pc`, by `decide +kernel`).  Rocq's
      KernelSites.v is the same file over the kd_<word> catalogue.
  --lists   print the Lean site lists and text bounds that the hand-written
            Weak/KernelSitesDef.lean must spell exactly.
  stdout    the site counts, the interrupts-off audit and the racy-byte
            reference audit (Rocq's tools/sites.md, as a report).

CHECK MODE (`--check`, the `make check-gen` counterpart): regenerate into a
scratch file and fail if it differs from the checked-in Weak/KernelSites.lean;
fail if Weak/KernelSitesDef.lean's `textLo`/`textHi` or its five site lists
are not the ones derived here; fail on a discipline violation, a site with no
recorded interrupts-off argument, the flat walk not ending exactly at the text
end, or the walk not covering every real instruction.  Nothing is written.

Usage:
    tools/gen_weak_sites.py [--image Xv6/KernelImage.lean] [--elf MachCSL/KernelElf.lean]
                            [--out Weak/KernelSites.lean] [--def Weak/KernelSitesDef.lean]
                            [--lists] [--check] [--quiet]
"""

import argparse
import difflib
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------------------
# word-level classification -- the SAME predicates Weak/KernelSitesDef.lean
# defines (and Rocq's gen_sites.py / KernelSitesDef.v).
# ---------------------------------------------------------------------------

def is_rvc(w):        return (w & 3) != 3
def size_of(w):       return 2 if is_rvc(w) else 4
def op(w):            return w & 0x7f
def f3(w):            return (w >> 12) & 7
def fld(w, hi, lo):   return (w >> lo) & ((1 << (hi - lo + 1)) - 1)

def is_fence(w):      return not is_rvc(w) and op(w) == 0x0f and f3(w) == 0
def is_fencei(w):     return not is_rvc(w) and op(w) == 0x0f and f3(w) == 1
def fence_pred(w):    return fld(w, 27, 24)
def fence_succ(w):    return fld(w, 23, 20)
def is_acq_fence(w):  return is_fence(w) and fence_pred(w) == 2 and fence_succ(w) == 3
def is_rel_fence(w):  return is_fence(w) and fence_pred(w) == 3 and fence_succ(w) == 1
def is_full_fence(w): return is_fence(w) and fence_pred(w) == 15 and fence_succ(w) == 15

def is_amoop(w):      return not is_rvc(w) and op(w) == 0x2f
def amo_funct5(w):    return fld(w, 31, 27)
def amo_aq(w):        return bool((w >> 26) & 1)
def amo_rl(w):        return bool((w >> 25) & 1)
def is_lr(w):         return is_amoop(w) and amo_funct5(w) == 2
def is_sc(w):         return is_amoop(w) and amo_funct5(w) == 3

def c_quad(w):        return w & 3
def c_f3(w):          return fld(w, 15, 13)

def is_plain_load(w):
    if is_rvc(w):
        return c_quad(w) in (0, 2) and c_f3(w) in (2, 3)
    return op(w) == 0x03

def is_plain_store(w):
    if is_rvc(w):
        return c_quad(w) in (0, 2) and c_f3(w) in (6, 7)
    return op(w) == 0x23

PRED_BITS = ['pi', 'po', 'pr', 'pw']
SUCC_BITS = ['si', 'so', 'sr', 'sw']

def kinds(nib, names):
    return ''.join(n[1] for i, n in enumerate(names) if nib & (8 >> i)) or '-'

AMOOPS = {0x00: 'AMOADD', 0x01: 'AMOSWAP', 0x04: 'AMOXOR', 0x08: 'AMOOR', 0x0c: 'AMOAND',
          0x10: 'AMOMIN', 0x14: 'AMOMAX', 0x18: 'AMOMINU', 0x1c: 'AMOMAXU'}


# ---------------------------------------------------------------------------
# the Sail AST of a site word, in Lean constructor syntax (model/Lean_RV64D
# `instruction`).  Only the forms a discipline site can take; anything else is
# reported as NOT DECODED (Rocq: "NOT in the kd_<word> catalogue").  A wrong
# spelling here cannot pass silently: the generated `rfl` would fail to build.
# ---------------------------------------------------------------------------

def _r(n):  return 'regidx.Regidx %d#5' % n
def _c(n):  return 'cregidx.Cregidx %d#3' % n
def _b(x):  return 'true' if x else 'false'

def ast_of(w, width):
    if width == 32:
        o, fn3 = op(w), f3(w)
        rd, rs1, rs2 = fld(w, 11, 7), fld(w, 19, 15), fld(w, 24, 20)
        if o == 0x23 and fn3 <= 3:
            imm = (fld(w, 31, 25) << 5) | fld(w, 11, 7)
            return 'instruction.STORE (%d#12, %s, %s, %d)' % (imm, _r(rs2), _r(rs1), 1 << fn3)
        if o == 0x03 and fn3 != 7:
            return 'instruction.LOAD (%d#12, %s, %s, %s, %d)' % (
                fld(w, 31, 20), _r(rs1), _r(rd), _b(fn3 & 4), 1 << (fn3 & 3))
        if is_fence(w):
            return 'instruction.FENCE (%d#4, %d#4, %d#4, %s, %s)' % (
                fld(w, 31, 28), fence_pred(w), fence_succ(w), _r(rs1), _r(rd))
        if is_amoop(w) and amo_funct5(w) in AMOOPS and fn3 in (2, 3):
            return 'instruction.AMO (amoop.%s, %s, %s, %s, %s, %d, %s)' % (
                AMOOPS[amo_funct5(w)], _b(amo_aq(w)), _b(amo_rl(w)), _r(rs2), _r(rs1),
                1 << fn3, _r(rd))
        return None
    if c_quad(w) == 0:
        rs1, r2 = fld(w, 9, 7), fld(w, 4, 2)
        if c_f3(w) in (2, 6):      # C.LW / C.SW: ui6 @ ui53 @ ui2
            ui = (fld(w, 5, 5) << 4) | (fld(w, 12, 10) << 1) | fld(w, 6, 6)
            return 'instruction.%s (%d#5, %s, %s)' % (
                'C_LW' if c_f3(w) == 2 else 'C_SW', ui, _c(rs1), _c(r2))
        if c_f3(w) in (3, 7):      # C.LD / C.SD: ui76 @ ui53
            ui = (fld(w, 6, 5) << 3) | fld(w, 12, 10)
            return 'instruction.%s (%d#5, %s, %s)' % (
                'C_LD' if c_f3(w) == 3 else 'C_SD', ui, _c(rs1), _c(r2))
    return None


# ---------------------------------------------------------------------------
# the image
# ---------------------------------------------------------------------------

ENTRY_RE = re.compile(r'^\s*⟨(0x[0-9a-f]+), (\d+), (0x[0-9a-f]+)⟩,?\s*$')
COMMENT_RE = re.compile(r'^\s*-- (.*)$')
SYM_RE = re.compile(r'^def «([^»]+)» : Nat := (0x[0-9a-f]+)\s*$')
HEADER_RE = re.compile(r'^-- AUTO-GENERATED by \S+ from \S+ \(xv6-riscv (.*?)(?:, md5 [0-9a-f]{32})?\); do not edit\.')


class Image:
    def __init__(self, image_path, elf_path):
        src = open(image_path, encoding='utf-8').read().split('\n')
        m = HEADER_RE.match(src[0])
        self.rev = m.group(1) if m else 'unknown'
        self.text, self.disasm, self.syms = [], {}, {}
        pending, in_syms = None, False
        for line in src:
            if line.startswith('namespace MachCSL.KernelSyms'):
                in_syms = True
                continue
            if line.startswith('end MachCSL.KernelSyms'):
                in_syms = False
                continue
            if in_syms:
                sm = SYM_RE.match(line)
                if sm:
                    self.syms[sm.group(1)] = int(sm.group(2), 16)
                continue
            em = ENTRY_RE.match(line)
            if em:
                a, wd, e = int(em.group(1), 16), int(em.group(2)), int(em.group(3), 16)
                self.text.append((a, wd, e))
                if pending is not None:
                    self.disasm[a] = pending
                pending = None
                continue
            cm = COMMENT_RE.match(line)
            pending = cm.group(1).replace('\t', ' ') if cm else None
        assert self.text, 'no instructions in %s' % image_path
        assert self.syms, 'no MachCSL.KernelSyms block in %s' % image_path

        esrc = open(elf_path, encoding='utf-8').read()
        self.elf_base = int(re.search(r'^def elfBase : Nat := (0x[0-9a-f]+)', esrc, re.M).group(1), 16)
        pages = []
        for pm in re.finditer(r'def page(\d+) : List Nat := \[\n(.*?)\n\]', esrc, re.S):
            rows = [int(r.group(1), 16) for r in re.finditer(r'^\s*0x([0-9a-f]+),?', pm.group(2), re.M)]
            pages.append((int(pm.group(1)), rows))
        pages.sort()
        self.rows = [r for _, p in pages for r in p]

        self.lo = self.text[0][0]
        self.hi = self.text[-1][0] + self.text[-1][1]
        # the text list and the byte dump must agree (the build proves it
        # too, Xv6.BootCarve; checked here so a stale dump fails loudly)
        for a, wd, e in self.text:
            for j in range(wd):
                if self.elf_byte(a - self.elf_base + j) != (e >> (8 * j)) & 0xff:
                    raise SystemExit('gen_weak_sites: Kernel.text and KernelElf disagree at 0x%x' % a)
        self.symaddrs = sorted(set(a for a in self.syms.values() if self.lo <= a < self.hi))
        self.symname = {}
        for n, a in sorted(self.syms.items()):
            self.symname.setdefault(a, n)

    def elf_byte(self, off):          # KernelElf.elfByte
        r = off // 32
        row = self.rows[r] if r < len(self.rows) else 0
        return (row >> (8 * (31 - off % 32))) & 0xff

    def kbyte(self, a):               # KernelSitesDef.kbyte
        return self.elf_byte(a - self.elf_base) if self.lo <= a < self.hi else 0

    def word(self, a):                # KernelSitesDef.kw
        return sum(self.kbyte(a + i) << (8 * i) for i in range(4))

    def sym_of(self, a):
        lo = None
        for s in self.symaddrs:
            if s <= a:
                lo = s
            else:
                break
        return (self.symname[lo], a - lo) if lo is not None else ('?', 0)

    def flat_walk(self):
        """KernelSitesDef.textAddrs: from `lo`, stepping by the decoded width."""
        out, a = [], self.lo
        while a < self.hi:
            out.append(a)
            a += size_of(self.word(a))
        return out, a


# ---------------------------------------------------------------------------
# enumeration (Rocq gen_sites.py's, over this image)
# ---------------------------------------------------------------------------

def enumerate_sites(img):
    addrs, end = img.flat_walk()
    real = set(a for a, _, _ in img.text)
    words = [img.word(a) for a in addrs]

    def rec(a, extra=None):
        w = img.word(a)
        sym, off = img.sym_of(a)
        r = {'pc': a, 'sym': sym, 'off': off, 'word': w, 'width': size_of(w) * 8,
             'real': a in real, 'text': img.disasm.get(a, '')}
        if extra:
            r.update(extra)
        return r

    fences, fenceis, amos, racy, rels, viol = [], [], [], [], [], []
    for i, a in enumerate(addrs):
        w = words[i]
        prev = words[i - 1] if i > 0 else None
        nxt = words[i + 1] if i + 1 < len(words) else None
        pa = addrs[i - 1] if i > 0 else None
        na = addrs[i + 1] if i + 1 < len(addrs) else None
        if is_fence(w):
            fences.append(rec(a, {
                'pred_bits': kinds(fence_pred(w), PRED_BITS),
                'succ_bits': kinds(fence_succ(w), SUCC_BITS),
                'class': ('acq' if is_acq_fence(w) else 'rel' if is_rel_fence(w) else
                          'full' if is_full_fence(w) else 'other'),
                'prev': img.disasm.get(pa, ''), 'next': img.disasm.get(na, '')}))
        if is_fencei(w):
            fenceis.append(rec(a, {'next': img.disasm.get(na, '')}))
        if is_amoop(w):
            amos.append(rec(a, {'aq': amo_aq(w), 'rl': amo_rl(w)}))
        if is_plain_load(w) and nxt is not None and is_acq_fence(nxt):
            racy.append(rec(a, {'fence_pc': na}))
        if is_plain_store(w) and prev is not None and is_rel_fence(prev):
            rels.append(rec(a, {'fence_pc': pa}))
        if is_acq_fence(w) and not (prev is not None and is_plain_load(prev)):
            viol.append(rec(a, {'why': 'acquire fence not preceded by a plain load'}))
        if is_rel_fence(w) and not (nxt is not None and is_plain_store(nxt)):
            viol.append(rec(a, {'why': 'release fence not followed by a plain store'}))
        if is_amoop(w) and not amo_aq(w):
            viol.append(rec(a, {'why': 'atomic memory operation without .aq'}))
        if is_lr(w) or is_sc(w):
            viol.append(rec(a, {'why': 'LR/SC in the image (no discipline defined)'}))

    return {'text_lo': img.lo, 'text_hi': img.hi, 'walk_end': end,
            'walk_positions': len(addrs), 'real_instructions': len(real),
            'walk_covers_real': not (real - set(addrs)), 'addrs': addrs,
            'fence': fences, 'fencei': fenceis, 'amo': amos,
            'racy_load': racy, 'release_store': rels, 'violations': viol}


# Why each enumerated site's region has S-mode interrupts disabled: a
# SOURCE-LEVEL claim about the pinned xv6-riscv (Rocq gen_sites.py's table,
# minus forkret, which has no discipline site in this kernel).  A kernel bump
# that moves a site into another function shows up as UNKNOWN.
INTR_OFF = {
    'acquire': "push_off() is the first thing acquire() does, so the amoswap runs with sstatus.SIE clear (spinlock.c).",
    'release': "release() runs inside the critical section it is ending: pop_off() comes AFTER the flag store, so the fence+store pair is still under push_off (spinlock.c).",
    'main': "pre-scheduler boot path: start() enables sie.SEIE/STIE but never sets sstatus.SIE; the first intr_on() is inside scheduler(), which main() only reaches after the started publication (start.c, main.c, proc.c).",
    'virtio_disk_rw': "holds disk.vdisk_lock (acquire -> push_off) across the whole body (virtio_disk.c).",
    'virtio_disk_intr': "holds disk.vdisk_lock (acquire -> push_off) across the whole body (virtio_disk.c).",
    'userret': "trampoline; usertrapret()/prepare_return does intr_off() before jumping here (trap.c, trampoline.S).",
}


def audit_intr_off(sites):
    rows = []
    for cls in ('racy_load', 'release_store', 'amo', 'fence', 'fencei'):
        for s in sites[cls]:
            why = INTR_OFF.get(s['sym'])
            rows.append({'class': cls, 'sym': s['sym'], 'off': s['off'], 'ok': why is not None,
                         'why': why or 'UNKNOWN -- no recorded argument'})
    return rows


REF = re.compile(r'#\s*([0-9a-f]+)\s+<([^>]+)>')


def audit_flag_bytes(img, sites):
    """Rocq gen_sites.py's racy-byte reference audit: the global each racy-load /
    release-store site touches (from the address-materialising pair's objdump
    target), and every other reference to it in the image."""
    addrs = sites['addrs']
    pos = {a: i for i, a in enumerate(addrs)}
    site_pcs = set(s['pc'] for s in sites['racy_load'] + sites['release_store'])
    flags = {}
    for s in sites['racy_load'] + sites['release_store']:
        i = pos[s['pc']]
        for j in range(i, max(-1, i - 6), -1):
            m = REF.search(img.disasm.get(addrs[j], ''))
            if m:
                flags.setdefault(m.group(2), set()).add(s['pc'])
                break
    rows = []
    for name in sorted(flags):
        refs = []
        for a in addrs:
            m = REF.search(img.disasm.get(a, ''))
            if m and m.group(2) == name:
                i = pos[a]
                near = [addrs[k] for k in range(i, min(len(addrs), i + 4)) if addrs[k] in site_pcs]
                sym, off = img.sym_of(a)
                refs.append({'sym': sym, 'off': off, 'text': img.disasm.get(a, ''),
                             'feeds_site': near[0] if near else None})
        rows.append({'flag': name, 'refs': refs,
                     'unaccounted': [r for r in refs if r['feeds_site'] is None]})
    return rows


# ---------------------------------------------------------------------------
# the Lean site lists (Weak/KernelSitesDef.lean must spell exactly these)
# ---------------------------------------------------------------------------

def site_expr(s):
    base = '(KernelSyms.«%s» : Int)' % s['sym']
    return base if s['off'] == 0 else '%s + 0x%x' % (base, s['off'])


def lean_site_lists(sites):
    return {
        'racyLoadPcs': [site_expr(s) for s in sites['racy_load']],
        'releasePcs': [site_expr(s) for s in sites['release_store']],
        'amoPcs': [site_expr(s) for s in sites['amo']],
        'acqFencePcs': [site_expr(s) for s in sites['fence'] if s['class'] == 'acq'],
        'relFencePcs': [site_expr(s) for s in sites['fence'] if s['class'] == 'rel'],
    }


def render_lists(sites):
    L = ['def textLo : Int := 0x%x' % sites['text_lo'], 'def textHi : Int := 0x%x' % sites['text_hi']]
    for name, xs in lean_site_lists(sites).items():
        if not xs:
            L.append('def %s : List Int := []' % name)
            continue
        L.append('def %s : List Int :=' % name)
        for i, x in enumerate(xs):
            L.append('  %s %s' % ('[' if i == 0 else ',', x))
        L[-1] += ' ]'
    return L


def parse_def_lists(path):
    """textLo/textHi and the five lists as Weak/KernelSitesDef.lean spells them."""
    src = open(path, encoding='utf-8').read()
    got = {}
    for n in ('textLo', 'textHi'):
        m = re.search(r'^def %s : Int := (0x[0-9a-f]+)' % n, src, re.M)
        got[n] = int(m.group(1), 16) if m else None
    for n in ('racyLoadPcs', 'releasePcs', 'amoPcs', 'acqFencePcs', 'relFencePcs'):
        m = re.search(r'^def %s : List Int :=\s*\[(.*?)\]' % n, src, re.M | re.S)
        got[n] = None if not m else [' '.join(x.split()) for x in m.group(1).split(',') if x.strip()]
    return got


# ---------------------------------------------------------------------------
# Weak/KernelSites.lean
# ---------------------------------------------------------------------------

HEADER = """-- AUTO-GENERATED by tools/gen_weak_sites.py from Xv6/KernelImage.lean (xv6-riscv %(rev)s); do not edit.
/-
Weak: **the decode linkage of the enumerated memory-ordering sites** (generated).

Rocq: `iris/KernelSites.v` @ xxvzwolszwmp (1cc222280), itself generated by Rocq's
`tools/gen_sites.py --emit-coq`.  Regenerate with `python3 tools/gen_weak_sites.py`; check with
`python3 tools/gen_weak_sites.py --check`.

For each site `Weak.KernelSitesDef` enumerates, the Sail decoder's verdict on that site's
encoding word, and the fact that the word is the image's at that pc.  `KernelSitesDef` decides
the discipline with raw BITMASK tests on the image words and never mentions the Sail model; this
file discharges, AT THE ENUMERATED SITES, the obligation that the bitmask classification agrees
with what the machine decodes (`KernelSitesDef` section 6.6, item 1).

**Deviations from Rocq.**

1. No catalogue: Rocq proves each fact by `exact kd_<word>` (the generated KernelDecode*.v
   catalogue); Lean has none (DU3), so each `decodesAll32`/`decodesAll16` fact is proved by
   `MachCSL.decodesAll32_bridge`/`decodesAll16_bridge`, the kernel evaluating the decoder's
   read-only walk on the machine- and supervisor-mode reference maps (`rfl`).  The statement is
   Lean's decode fact (`MachCSL.MConf`: in M-mode at any configuration and in S-mode at the
   kernel's `menvcfg`) rather than Rocq's `exec (ext_decode w) s = Some (ast, s)` under its
   per-word `misa`/`cfg_ok` premises; the AMO needs no hand-written override (Rocq `amodec`).
2. Added, per site: `<name>Word`, the encoding word as `kw pc` (low half for a compressed one),
   by `decide +kernel` -- the pc-to-word link Rocq's file leaves to the generator.
3. The sites are this tree's image's (`KernelSitesDef` deviation 1): %(nsites)d facts.

**Name map:** Rocq `ks_<class>_<sym>_<off>` → Lean `ks<Class><Sym><Off>` (camelCase, offset in
lowercase hex).
-/
import Weak.KernelSitesDef
import MachCSL.DecodeBridge

namespace Weak

open Iris Iris.ProgramLogic MachCSL LeanRV64D

-- The decoder's walk reads the platform configuration (see `Xv6/CodeTactics.lean`).
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
"""


def camel(*parts):
    out = ''
    for p in parts:
        for seg in re.split(r'[^0-9A-Za-z]+', p):
            if seg:
                out += seg[0].upper() + seg[1:]
    return out[0].lower() + out[1:]


def emit_lean(sites, rev):
    rows, missing, seen = [], [], set()
    body = []
    for cls in ('racy_load', 'release_store', 'amo', 'fence'):
        for s in sites[cls]:
            wd = s['width']
            w = s['word'] & ((1 << wd) - 1)
            name = '%s+0x%x' % (s['sym'], s['off'])
            ast = ast_of(w, wd)
            if ast is None:
                missing.append((cls, name, w, wd))
                body.append('-- %-14s %-24s word %0*x: NOT DECODED by tools/gen_weak_sites.py' % (cls, name, wd // 4, w))
                body.append('')
                continue
            lem = 'ks' + camel(cls, s['sym'], '%x' % s['off'])[0].upper() + camel(cls, s['sym'], '%x' % s['off'])[1:]
            if lem in seen:
                continue
            seen.add(lem)
            pc = site_expr(s)
            body.append('/-- %s @ %s -- `%s` -/' % (cls, name, s['text']))
            if wd == 16:
                body.append('theorem %s : decodesAll16 (GF := GF) 0x%04x#16' % (lem, w))
                body.append('    (%s) :=' % ast)
                body.append('  decodesAll16_bridge _ _ rfl rfl')
                body.append('theorem %sWord : kw (%s) %% 65536 = 0x%04x := by decide +kernel' % (lem, pc, w))
            else:
                body.append('theorem %s : decodesAll32 (GF := GF) 0x%08x#32' % (lem, w))
                body.append('    (%s) :=' % ast)
                body.append('  decodesAll32_bridge _ _ rfl rfl')
                body.append('theorem %sWord : kw (%s) = 0x%08x := by decide +kernel' % (lem, pc, w))
            body.append('')
    text = HEADER % {'rev': rev, 'nsites': len(seen)} + '\n' + '\n'.join(body) + '\nend Weak\n'
    return text, len(seen), missing


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', default='Xv6/KernelImage.lean')
    ap.add_argument('--elf', default='MachCSL/KernelElf.lean')
    ap.add_argument('--out', default='Weak/KernelSites.lean')
    ap.add_argument('--def', dest='defn', default='Weak/KernelSitesDef.lean')
    ap.add_argument('--lists', action='store_true', help='print the KernelSitesDef site lists')
    ap.add_argument('--check', action='store_true', help='regenerate and diff; write nothing')
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args(argv)
    os.chdir(REPO)

    img = Image(a.image, a.elf)
    sites = enumerate_sites(img)
    audit = audit_intr_off(sites)
    flags = audit_flag_bytes(img, sites)
    text, n, missing = emit_lean(sites, img.rev)
    say = (lambda *x: None) if a.quiet else print

    say('text 0x%08x..0x%08x, flat walk %d positions ending 0x%08x (%s)'
        % (sites['text_lo'], sites['text_hi'], sites['walk_positions'], sites['walk_end'],
           'exact' if sites['walk_end'] == sites['text_hi'] else 'MISMATCH'))
    say('real instructions %d, flat walk covers them: %s'
        % (sites['real_instructions'], sites['walk_covers_real']))
    for k in ('fence', 'fencei', 'amo', 'racy_load', 'release_store'):
        say('  %-14s %d' % (k, len(sites[k])))
    for s in sites['fence']:
        say('    fence  %s+0x%x  %s,%s  (%s)' % (s['sym'], s['off'], s['pred_bits'], s['succ_bits'], s['class']))
    for s in sites['fencei']:
        say('    fencei %s+0x%x' % (s['sym'], s['off']))
    say('interrupts-off audit:')
    for r in audit:
        say('  %-13s %s+0x%x: %s' % (r['class'], r['sym'], r['off'], r['why']))
    say('racy-byte audit:')
    for f in flags:
        for r in f['refs']:
            say('  %s referenced at %s+0x%x (%s): %s' % (
                f['flag'], r['sym'], r['off'], r['text'],
                ('feeds site 0x%08x' % r['feeds_site']) if r['feeds_site'] else 'FEEDS NO SITE'))
    if a.lists:
        print('\n'.join(render_lists(sites)))

    probs = []
    if sites['walk_end'] != sites['text_hi']:
        probs.append('the flat walk ends at 0x%x, not at the text end 0x%x' % (sites['walk_end'], sites['text_hi']))
    if not sites['walk_covers_real']:
        probs.append('the flat walk misses a real instruction')
    for s in sites['violations']:
        probs.append('discipline violation at %s+0x%x: %s' % (s['sym'], s['off'], s['why']))
    for r in audit:
        if not r['ok']:
            probs.append('no interrupts-off argument for %s %s+0x%x' % (r['class'], r['sym'], r['off']))
    for cls, name, w, wd in missing:
        probs.append('site %s %s (word %0*x) has no decoded AST' % (cls, name, wd // 4, w))
    loose = [(f['flag'], r) for f in flags for r in f['unaccounted']]
    for name, r in loose:
        say('NOTE: %s referenced at %s+0x%x outside a site: %s' % (name, r['sym'], r['off'], r['text']))

    if a.check:
        old = open(a.out, encoding='utf-8').read() if os.path.exists(a.out) else ''
        if old != text:
            probs.append('%s is stale (regenerate with tools/gen_weak_sites.py)' % a.out)
            sys.stdout.writelines(difflib.unified_diff(
                old.splitlines(True), text.splitlines(True), a.out, '(regenerated)', n=1))
        got = parse_def_lists(a.defn)
        want = lean_site_lists(sites)
        want['textLo'], want['textHi'] = sites['text_lo'], sites['text_hi']
        for k in ('textLo', 'textHi', 'racyLoadPcs', 'releasePcs', 'amoPcs', 'acqFencePcs', 'relFencePcs'):
            if got.get(k) != want[k]:
                probs.append('%s: %s is %r, the image gives %r' % (a.defn, k, got.get(k), want[k]))
        for p in probs:
            print('FAIL: ' + p)
        print('gen_weak_sites --check: %s' % ('FAIL' if probs else 'ok'))
        return 1 if probs else 0

    with open(a.out, 'w', encoding='utf-8') as f:
        f.write(text)
    say('wrote %s: %d site decode facts' % (a.out, n))
    for p in probs:
        print('WARNING: ' + p)
    return 1 if probs else 0


if __name__ == '__main__':
    sys.exit(main())

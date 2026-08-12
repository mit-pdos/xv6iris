#!/usr/bin/env python3
"""gen_sites.py -- ENUMERATE the kernel image's memory-ordering sites.

A sibling of tools/gen_code.py: it reads the same two tracked files
(kernel-rocq/{KernelSyms,KernelInstrs}.v -- never the ELF, never a proof) and
reports every place in the image where the weak-memory discipline has a static
shape:

  fence     every FENCE / FENCE.I, with its pred/succ kind bits (pi po pr pw /
            si so sr sw) and its stream neighbours
  amo       every AMO / LR / SC, with its aq / rl bits
  racy-load a plain load whose STREAM SUCCESSOR is an acquire fence (r,rw)
  release   a plain store whose STREAM PREDECESSOR is a release fence (rw,w)

Outputs, all deterministic:

  tools/sites.json   the machine-readable table (the report)
  tools/sites.md     the same as a human-readable set of tables, plus the
                     interrupts-off audit and the Coq snippet that
                     iris/KernelSitesDef.v's site lists must agree with
  iris/KernelSites.v (--emit-coq) per-site decode facts stated over the
                     EXISTING kd_<word> catalogue -- see below

STATUS OF THE GENERATED .v.  The formal object of this effort is the
hand-written iris/KernelSitesDef.v: a word-level decidable checker plus one
vm_compute reflection fact.  iris/KernelSites.v is the CATALOGUE-LINKAGE
prototype -- it re-states each enumerated site's decode adjacency against the
Sail decoder by looking the site's encoding word up in the generated
KernelDecode*.v shards, so nothing here re-runs the decoder.  It is
documentation and a cross-check, not the load-bearing artifact.

REPRODUCIBILITY.  Same discipline as gen_code.py: everything is derived from
the tracked dump, the manifest header records the image revision and the exact
invocation, and re-running after a re-dump rewrites the whole output.  Unlike
gen_code.py there is no --only footgun here: this tool always walks the WHOLE
image, and its Coq output is one self-contained file.
"""

import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_code as G


# ---------------------------------------------------------------------------
# word-level classification -- the SAME predicates iris/KernelSitesDef.v
# defines in Coq.  Kept in lockstep by construction: the site lists this tool
# emits are exactly the ones that file's [forallb] lemmas must accept, and the
# tool re-derives them from the image rather than reading them back.
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


# The FENCE nibble bit names, high to low, as the ISA spells them.
PRED_BITS = ['pi', 'po', 'pr', 'pw']
SUCC_BITS = ['si', 'so', 'sr', 'sw']

def kinds(nib, names):
    return ''.join(n[1] for i, n in enumerate(names) if nib & (8 >> i)) or '-'


AMOOPS = {0x00: 'amoadd', 0x01: 'amoswap', 0x02: 'lr', 0x03: 'sc',
          0x04: 'amoxor', 0x08: 'amoor', 0x0c: 'amoand', 0x10: 'amomin',
          0x14: 'amomax', 0x18: 'amominu', 0x1c: 'amomaxu'}


# ---------------------------------------------------------------------------
# the image
# ---------------------------------------------------------------------------

class Image:
    def __init__(self, kdir):
        self.syms = G.load_syms(os.path.join(kdir, 'KernelSyms.v'))
        self.bytes = G.load_bytes(os.path.join(kdir, 'KernelInstrs.v'))
        self.lo = min(self.bytes)
        self.hi = max(self.bytes) + 1
        self.disasm = load_disasm(os.path.join(kdir, 'KernelInstrs.v'))
        # symbol lookup: highest symbol at or below an address
        self.symaddrs = sorted(set(a for a in self.syms.values() if a in self.bytes))
        self.symname = {}
        for n, a in sorted(self.syms.items()):
            self.symname.setdefault(a, n)

    def word(self, a):
        v = 0
        for i in range(4):
            v |= self.bytes.get(a + i, 0) << (8 * i)
        return v

    def sym_of(self, a):
        lo = None
        for s in self.symaddrs:
            if s <= a:
                lo = s
            else:
                break
        return (self.symname[lo], a - lo) if lo is not None else ('?', 0)

    def flat_walk(self):
        """Instruction addresses, stepping by the decoded width from [lo].

        This is exactly iris/KernelSitesDef.v's [text_addrs].  It visits a
        SUPERSET of the real instruction boundaries (the extra positions are
        inter-function alignment nops and the .rodata gap); [check_walk]
        proves that containment against gen_code.py's per-symbol walk, which
        is the walk the proofs' Code files are generated from."""
        out, a = [], self.lo
        while a < self.hi:
            out.append(a)
            a += size_of(self.word(a))
        return out, a

    def symbol_walk(self):
        """gen_code.py's walk: per symbol, truncated at the alignment padding."""
        out = []
        for i, s in enumerate(self.symaddrs):
            hi = self.symaddrs[i + 1] if i + 1 < len(self.symaddrs) else self.hi
            out += [a for a, _, _ in G.instructions(self.bytes, s, hi)]
        return out


def load_disasm(path):
    """The objdump text the dumper left in KernelInstrs.v, keyed by address."""
    d = {}
    pat = re.compile(r'\s*\(\* (0x[0-9a-f]+): (.*?)\s*\*\)')
    for line in open(path):
        m = pat.match(line)
        if m:
            d[int(m.group(1), 16)] = m.group(2)
    return d


# ---------------------------------------------------------------------------
# enumeration
# ---------------------------------------------------------------------------

def enumerate_sites(img):
    addrs, end = img.flat_walk()
    real = set(img.symbol_walk())
    words = [img.word(a) for a in addrs]

    def rec(a, extra=None):
        w = img.word(a)
        sym, off = img.sym_of(a)
        r = {'pc': a, 'sym': sym, 'off': off, 'word': w,
             'width': size_of(w) * 8, 'real': a in real,
             'text': img.disasm.get(a, '')}
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
                'pred': fence_pred(w), 'succ': fence_succ(w),
                'pred_bits': kinds(fence_pred(w), PRED_BITS),
                'succ_bits': kinds(fence_succ(w), SUCC_BITS),
                'class': ('acq' if is_acq_fence(w) else
                          'rel' if is_rel_fence(w) else
                          'full' if is_full_fence(w) else 'other'),
                'prev_pc': pa, 'prev': img.disasm.get(pa, ''),
                'next_pc': na, 'next': img.disasm.get(na, '')}))
        if is_fencei(w):
            fenceis.append(rec(a, {'prev_pc': pa, 'prev': img.disasm.get(pa, ''),
                                   'next_pc': na, 'next': img.disasm.get(na, '')}))
        if is_amoop(w):
            amos.append(rec(a, {
                'amoop': AMOOPS.get(amo_funct5(w), 'amo?%02x' % amo_funct5(w)),
                'aq': amo_aq(w), 'rl': amo_rl(w),
                'lr': is_lr(w), 'sc': is_sc(w),
                'prev_pc': pa, 'prev': img.disasm.get(pa, ''),
                'next_pc': na, 'next': img.disasm.get(na, '')}))
        if is_plain_load(w) and nxt is not None and is_acq_fence(nxt):
            racy.append(rec(a, {'fence_pc': na, 'fence': img.disasm.get(na, ''),
                                'delta': na - a}))
        if is_plain_store(w) and prev is not None and is_rel_fence(prev):
            rels.append(rec(a, {'fence_pc': pa, 'fence': img.disasm.get(pa, ''),
                                'delta': a - pa}))

        # the checker's own clauses, re-run here so the report and
        # iris/KernelSitesDef.v cannot disagree about what passed
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
            'walk_covers_real': not (real - set(addrs)),
            'fence': fences, 'fencei': fenceis, 'amo': amos,
            'racy_load': racy, 'release_store': rels, 'violations': viol}


# ---------------------------------------------------------------------------
# the interrupts-off audit (source level, best effort)
# ---------------------------------------------------------------------------

# Why each enumerated site's region has S-mode interrupts disabled.  This is a
# SOURCE-LEVEL claim about xv6-riscv at the pinned revision, not something the
# image can settle -- it is recorded here so a kernel bump that invalidates it
# shows up as an unmatched key rather than as a silently stale note.
INTR_OFF = {
    'acquire': ("push_off() is the first thing acquire() does, so the amoswap "
                "runs with sstatus.SIE clear (spinlock.c)."),
    'release': ("release() runs inside the critical section it is ending: "
                "pop_off() comes AFTER the flag store, so the fence+store pair "
                "is still under push_off (spinlock.c)."),
    'main':    ("pre-scheduler boot path.  start() enables sie.SEIE/STIE but "
                "never sets sstatus.SIE; the first intr_on() in the whole "
                "kernel is inside scheduler(), which main() only reaches after "
                "the started publication (start.c, main.c, proc.c)."),
    'forkret': ("reached only by swtch() from scheduler(), whose loop does "
                "intr_on(); intr_off(); BEFORE acquire(&p->lock) -- so the "
                "push_off recorded intena = 0 and forkret's release(&p->lock) "
                "pop_off() does NOT re-enable interrupts.  The `first` "
                "acquire-load and release-store therefore run with SIE clear. "
                "NOTE: this depends on scheduler()'s intr_on();intr_off() "
                "pair; an xv6 revision without it would leave these two sites "
                "interruptible (proc.c)."),
    'virtio_disk_rw':   ("holds disk.vdisk_lock (acquire -> push_off) across "
                         "the whole body (virtio_disk.c)."),
    'virtio_disk_intr': ("holds disk.vdisk_lock (acquire -> push_off) across "
                         "the whole body (virtio_disk.c)."),
    'userret':          ("trampoline; usertrapret() does intr_off() before "
                         "jumping here (trap.c, trampoline.S)."),
}


REF = re.compile(r'#\s*([0-9a-f]+)\s+<([^>]+)>')


def audit_flag_bytes(img, sites):
    """Which DATA bytes the discipline sites touch, and who else touches them.

    The completeness direction the word-level checker cannot see: a plain store
    to a byte another hart racy-reads, sitting OUTSIDE a release site, is a
    discipline violation.  Which byte an access touches is not a function of
    the encoding word -- but for a global it IS statically resolvable, because
    gcc materialises the address with an auipc/addi (or lui/addi) pair whose
    target objdump already resolved in the tracked dump's comments.

    So: for each enumerated racy-load / release-store site, walk BACK a few
    instructions to the address-materialising pair and read off the symbol;
    then list every OTHER reference to that symbol in the whole image.  Any
    reference that is not itself part of a site is reported."""
    addrs, _ = img.flat_walk()
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
                # the site this reference feeds, if any: the next few
                # instructions using the materialised address
                near = [addrs[k] for k in range(i, min(len(addrs), i + 4))
                        if addrs[k] in site_pcs]
                sym, off = img.sym_of(a)
                refs.append({'pc': a, 'sym': sym, 'off': off,
                             'text': img.disasm.get(a, ''),
                             'feeds_site': near[0] if near else None})
        rows.append({'flag': name, 'refs': refs,
                     'unaccounted': [r for r in refs if r['feeds_site'] is None]})
    return rows


def audit_intr_off(sites):
    rows = []
    for cls in ('racy_load', 'release_store', 'amo', 'fence', 'fencei'):
        for s in sites[cls]:
            why = INTR_OFF.get(s['sym'])
            rows.append({'class': cls, 'pc': s['pc'], 'sym': s['sym'],
                         'off': s['off'], 'ok': why is not None,
                         'why': why or 'UNKNOWN -- no recorded argument'})
    return rows


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------

def fmt_site(s):
    return '`%s+0x%x`' % (s['sym'], s['off'])


def write_md(path, sites, audit, flags, rev, invocation):
    L = []
    L.append('# Kernel memory-ordering sites')
    L.append('')
    L.append('AUTO-GENERATED by `tools/gen_sites.py` -- do not edit by hand.')
    L.append('')
    L.append('| | |')
    L.append('|---|---|')
    L.append('| image revision (`XV6_REV`) | `%s` |' % rev)
    L.append('| text range | `0x%08x .. 0x%08x` |' % (sites['text_lo'], sites['text_hi']))
    L.append('| flat walk ends at | `0x%08x` (%s) |'
             % (sites['walk_end'],
                'exact' if sites['walk_end'] == sites['text_hi'] else 'MISMATCH'))
    L.append('| flat-walk positions | %d |' % sites['walk_positions'])
    L.append('| real instructions (gen_code walk) | %d |' % sites['real_instructions'])
    L.append('| flat walk covers every real instruction | %s |'
             % ('yes' if sites['walk_covers_real'] else 'NO'))
    L.append('| regenerate | `%s` |' % invocation)
    L.append('')
    L.append('## Counts')
    L.append('')
    L.append('| class | count |')
    L.append('|---|---|')
    for k in ('fence', 'fencei', 'amo', 'racy_load', 'release_store', 'violations'):
        L.append('| %s | %d |' % (k, len(sites[k])))
    L.append('')

    L.append('## FENCE')
    L.append('')
    L.append('| pc | site | word | pred | succ | class | prev insn | next insn |')
    L.append('|---|---|---|---|---|---|---|---|')
    for s in sites['fence']:
        L.append('| `0x%08x` | %s | `%08x` | `%s` | `%s` | %s | `%s` | `%s` |'
                 % (s['pc'], fmt_site(s), s['word'], s['pred_bits'],
                    s['succ_bits'], s['class'], s['prev'], s['next']))
    L.append('')

    if sites['fencei']:
        L.append('## FENCE.I')
        L.append('')
        L.append('| pc | site | word | next insn |')
        L.append('|---|---|---|---|')
        for s in sites['fencei']:
            L.append('| `0x%08x` | %s | `%08x` | `%s` |'
                     % (s['pc'], fmt_site(s), s['word'], s['next']))
        L.append('')

    L.append('## AMO / LR / SC')
    L.append('')
    L.append('| pc | site | word | op | aq | rl | insn |')
    L.append('|---|---|---|---|---|---|---|')
    for s in sites['amo']:
        L.append('| `0x%08x` | %s | `%08x` | %s | %s | %s | `%s` |'
                 % (s['pc'], fmt_site(s), s['word'], s['amoop'],
                    s['aq'], s['rl'], s['text']))
    L.append('')

    L.append('## Racy-read sites (plain load, stream successor is `fence r,rw`)')
    L.append('')
    L.append('| pc | site | word | width | insn | fence pc | delta |')
    L.append('|---|---|---|---|---|---|---|')
    for s in sites['racy_load']:
        L.append('| `0x%08x` | %s | `%0*x` | %d | `%s` | `0x%08x` | +%d |'
                 % (s['pc'], fmt_site(s), s['width'] // 4,
                    s['word'] & ((1 << s['width']) - 1), s['width'],
                    s['text'], s['fence_pc'], s['delta']))
    L.append('')

    L.append('## Release-flag sites (plain store, stream predecessor is `fence rw,w`)')
    L.append('')
    L.append('| pc | site | word | width | insn | fence pc | delta |')
    L.append('|---|---|---|---|---|---|---|')
    for s in sites['release_store']:
        L.append('| `0x%08x` | %s | `%0*x` | %d | `%s` | `0x%08x` | -%d |'
                 % (s['pc'], fmt_site(s), s['width'] // 4,
                    s['word'] & ((1 << s['width']) - 1), s['width'],
                    s['text'], s['fence_pc'], s['delta']))
    L.append('')

    L.append('## Discipline violations')
    L.append('')
    if sites['violations']:
        L.append('| pc | site | why |')
        L.append('|---|---|---|')
        for s in sites['violations']:
            L.append('| `0x%08x` | %s | **%s** |' % (s['pc'], fmt_site(s), s['why']))
    else:
        L.append('None -- `iris/KernelSitesDef.image_disciplineb` is `true`.')
    L.append('')

    L.append('## Interrupts-off audit')
    L.append('')
    L.append('Source-level, best effort: every enumerated site should sit in a')
    L.append('region where `sstatus.SIE` is clear, so that no trap can be')
    L.append('delivered between a discipline fence and its adjacent access.')
    L.append('')
    L.append('| class | site | interrupts off? | why |')
    L.append('|---|---|---|---|')
    for r in audit:
        L.append('| %s | `%s+0x%x` | %s | %s |'
                 % (r['class'], r['sym'], r['off'],
                    'yes' if r['ok'] else '**UNKNOWN**', r['why']))
    L.append('')

    L.append('## Racy-byte reference audit')
    L.append('')
    L.append('Every reference in the image to a byte a discipline site touches.')
    L.append('A reference that feeds no site is a candidate discipline violation.')
    L.append('')
    L.append('| byte | referenced at | insn | feeds site |')
    L.append('|---|---|---|---|')
    for f in flags:
        for r in f['refs']:
            L.append('| `%s` | `%s+0x%x` | `%s` | %s |'
                     % (f['flag'], r['sym'], r['off'], r['text'],
                        ('`0x%08x`' % r['feeds_site']) if r['feeds_site']
                        else '**none**'))
    L.append('')

    L.append('## The Coq site lists')
    L.append('')
    L.append('`iris/KernelSitesDef.v`\'s enumerations must be exactly these.')
    L.append('')
    L.append('```coq')
    L += coq_site_lists(sites)
    L.append('```')
    L.append('')
    open(path, 'w').write('\n'.join(L) + '\n')


def coq_site_lists(sites):
    def lst(name, rows):
        out = ['Definition %s : list Z :=' % name]
        for i, s in enumerate(rows):
            head = '  [ ' if i == 0 else '  ; '
            off = '' if s['off'] == 0 else ' + 0x%x' % s['off']
            out.append('%sKernelSyms.%s%s' % (head, s['sym'], off))
        out.append('  ].' if rows else '  [].')
        return out
    L = []
    L += lst('racy_load_pcs', sites['racy_load']) + ['']
    L += lst('release_pcs', sites['release_store']) + ['']
    L += lst('amo_pcs', [s for s in sites['amo']]) + ['']
    L += lst('acq_fence_pcs', [s for s in sites['fence'] if s['class'] == 'acq']) + ['']
    L += lst('rel_fence_pcs', [s for s in sites['fence'] if s['class'] == 'rel'])
    return L


# ---------------------------------------------------------------------------
# the catalogue-linkage prototype: iris/KernelSites.v
# ---------------------------------------------------------------------------

COQ_HEADER = """(* KernelSites.v -- AUTO-GENERATED by tools/gen_sites.py.  DO NOT EDIT BY HAND.

   The CATALOGUE LINKAGE for the enumerated memory-ordering sites: for each
   site, the Sail decoder's verdict on that site's encoding word, taken
   verbatim from the generated [kd_<word>] catalogue in KernelDecode*.v.  No
   decoder is re-run here -- every proof below is [exact kd_<word>], so this
   file costs a load and nothing else.

   WHAT IT IS FOR.  iris/KernelSitesDef.v decides the discipline with raw
   BITMASK tests on the image words; it never mentions the Sail model.  That
   is what makes its whole-image fold a millisecond-scale [vm_compute] instead
   of a decoder run per instruction -- but it leaves one obligation open: that
   the bitmask classification agrees with what the machine actually decodes.
   This file discharges that obligation AT THE ENUMERATED SITES, which is
   where the Layer-1 transfer argument consumes it.  (The generic
   mask-implies-decode lemma is the recorded fallback; see KernelSitesDef.v's
   bridging writeup.)

   Image revision (XV6_REV): %(rev)s
   Regenerate with:  %(invocation)s                                        *)
From iris.program_logic Require Import lifting.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvFetchExec.
Require Import WpMmodeLeafBase.
%(shards)s
Require Import KernelSitesDef.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.
"""


def emit_coq(path, sites, catalogue, rev, invocation):
    """One [site_decodes] fact per enumerated site, by catalogue lookup."""
    rows = []
    extra_imports = []
    for cls in ('racy_load', 'release_store', 'amo', 'fence'):
        for s in sites[cls]:
            w = s['word'] & ((1 << s['width']) - 1)
            key = (w, s['width'])
            if key in G.OVERRIDES:
                # gen_code.py keeps this word's decode fact HAND-WRITTEN (its
                # hypotheses are not the generic (MISA_C, cfg_ok) pair); the
                # catalogue linkage goes through that lemma instead.
                ast, dec, req = G.OVERRIDES[key]
                if req not in extra_imports:
                    extra_imports.append(req)
                rows.append((cls, s, w, ast, None, dec))
                continue
            if key not in catalogue:
                rows.append((cls, s, w, None, None, None))
                continue
            exp, cast, _op = catalogue[key]
            rows.append((cls, s, w, exp, cast, 'kd_%0*x' % (s['width'] // 4, w)))

    shards = sorted(set(G.shard_of(w) for _, _, w, exp, _, d in rows
                        if exp is not None and d and d.startswith('kd_')))
    L = []
    seen = set()
    missing = []
    for cls, s, w, exp, cast, dec in rows:
        name = '%s+0x%x' % (s['sym'], s['off'])
        if exp is None:
            missing.append((cls, name, w, s['width']))
            L.append('(* %-14s %-24s word %0*x: NOT in the kd_<word> catalogue *)'
                     % (cls, name, s['width'] // 4, w))
            L.append('')
            continue
        lem = 'ks_%s_%s_%02x' % (cls, s['sym'], s['off'])
        if lem in seen:
            continue
        seen.add(lem)
        ast = cast if (s['width'] == 16 and cast is not None) else exp
        L.append('(* %s @ %s -- %s *)' % (cls, name, s['text']))
        if not dec.startswith('kd_'):
            # a hand-written override: restate ITS hypotheses verbatim
            L.append('Lemma %s s :' % lem)
            L.append('  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->')
            L.append('  eq_vec (_get_Misa_A (register_lookup misa s.(sregs))) (\'b"1") = true ->')
            L.append('  exec (ext_decode (mword_of_int 0x%08x : mword 32)) s' % w)
            L.append('  = Some (%s, s).' % ast)
            L.append('Proof. exact (%s s). Qed.' % dec)
        elif s['width'] == 16:
            L.append('Lemma %s s :' % lem)
            L.append('  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) (\'b"1") = true ->')
            L.append('  exec (ext_decode_compressed (mword_of_int 0x%04x : mword 16)) s' % w)
            L.append('  = Some (%s, s).' % ast)
            L.append('Proof. exact (%s s). Qed.' % dec)
        else:
            L.append('Lemma %s s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->' % lem)
            L.append('  exec (ext_decode (mword_of_int 0x%08x : mword 32) : M instruction) s' % w)
            L.append('  = Some (%s, s).' % ast)
            L.append('Proof. exact (%s s). Qed.' % dec)
        L.append('')

    body = '\n'.join(L)
    head = COQ_HEADER % dict(
        rev=rev, invocation=invocation,
        shards='\n'.join(['Require Import KernelDecode%02d.' % i for i in shards]
                         + extra_imports))
    open(path, 'w').write(head + '\n' + body)
    return len(seen), missing


def load_catalogue(kdir, manifest):
    """The (word, width) -> AST map gen_code.py builds for the covered set."""
    syms = G.load_syms(os.path.join(kdir, 'KernelSyms.v'))
    by = G.load_bytes(os.path.join(kdir, 'KernelInstrs.v'))
    man = json.load(open(manifest))
    starts = sorted(set(a for a in syms.values() if a in by))
    end = max(by) + 1
    out = {}
    for row in man:
        a = syms[row[1]]
        i = starts.index(a)
        hi = starts[i + 1] if i + 1 < len(starts) else end
        for _, w, wd in G.instructions(by, a, hi):
            if (w, wd) in out or (w, wd) in G.OVERRIDES:
                continue
            d = G.decode(w, wd)
            if d is not None:
                out[(w, wd)] = d
    return out


def xv6_rev(root):
    try:
        for line in open(os.path.join(root, 'Makefile')):
            m = re.match(r'XV6_REV \?= (\S+)', line)
            if m:
                return m.group(1)
    except OSError:
        pass
    return 'unknown'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kernel-rocq', default='kernel-rocq')
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--tools', default='tools')
    ap.add_argument('--manifest', default='tools/code_manifest.json')
    ap.add_argument('--emit-coq', action='store_true',
                    help='also write iris/KernelSites.v (catalogue linkage)')
    ap.add_argument('--check', action='store_true',
                    help='exit non-zero if any discipline violation is found')
    args = ap.parse_args()

    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    rev = xv6_rev(root)
    invocation = 'python3 tools/gen_sites.py' + (' --emit-coq' if args.emit_coq else '')

    img = Image(args.kernel_rocq)
    sites = enumerate_sites(img)
    audit = audit_intr_off(sites)
    flags = audit_flag_bytes(img, sites)

    jpath = os.path.join(args.tools, 'sites.json')
    json.dump({'xv6_rev': rev, 'sites': sites, 'intr_off_audit': audit,
               'racy_byte_audit': flags},
              open(jpath, 'w'), indent=1, sort_keys=True, default=sorted)
    mpath = os.path.join(args.tools, 'sites.md')
    write_md(mpath, sites, audit, flags, rev, invocation)

    print('text 0x%08x..0x%08x, flat walk %d positions ending 0x%08x (%s)'
          % (sites['text_lo'], sites['text_hi'], sites['walk_positions'],
             sites['walk_end'],
             'exact' if sites['walk_end'] == sites['text_hi'] else 'MISMATCH'))
    print('real instructions %d, flat walk covers them: %s'
          % (sites['real_instructions'], sites['walk_covers_real']))
    for k in ('fence', 'fencei', 'amo', 'racy_load', 'release_store'):
        print('  %-14s %d' % (k, len(sites[k])))
    print('wrote %s, %s' % (jpath, mpath))

    if args.emit_coq:
        cat = load_catalogue(args.kernel_rocq, args.manifest)
        cpath = os.path.join(args.iris, 'KernelSites.v')
        n, missing = emit_coq(cpath, sites, cat, rev, invocation)
        print('wrote %s: %d catalogue-linked site facts' % (cpath, n))
        for cls, name, w, wd in missing:
            print('  NOT IN CATALOGUE: %-12s %-22s %0*x' % (cls, name, wd // 4, w))

    loose = [(f['flag'], r) for f in flags for r in f['unaccounted']]
    if loose:
        print('RACY-BYTE REFERENCES NOT AT A SITE: %d' % len(loose))
        for name, r in loose:
            print('  %s referenced at %s+0x%x: %s' % (name, r['sym'], r['off'], r['text']))
    else:
        print('racy-byte audit: every reference to a site byte feeds a site')

    bad = sites['violations']
    unknown = [r for r in audit if not r['ok']]
    if bad:
        print('DISCIPLINE VIOLATIONS: %d' % len(bad))
        for s in bad:
            print('  0x%08x %s+0x%x: %s' % (s['pc'], s['sym'], s['off'], s['why']))
    if unknown:
        print('SITES WITH NO INTERRUPTS-OFF ARGUMENT: %d' % len(unknown))
        for r in unknown:
            print('  %s %s+0x%x' % (r['class'], r['sym'], r['off']))
    if args.check and (bad or unknown or loose):
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

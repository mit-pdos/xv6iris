#!/usr/bin/env python3
"""gen_ucode.py -- GENERATE a USER program's code catalog, iris/UCode<Prog>.v.

The user-tier sibling of tools/gen_code.py.  From a dumped user image
(user-rocq/<Module>{Instrs,Data,Syms}.v, produced by tools/dump_elf.py) plus a
set of program counters, it emits the file UCodeEcho.v is the hand-written
example of:

  §0  <prog>_text_sub / _data_sub / _img_sub, the key-range lemmas, the
      <prog>_text_layout record with its fetch/load projections, and
      <prog>_syms_pins;
  §1  one [udec_<word>] per DISTINCT instruction word -- [udecode_rvc] /
      [udecode_base], proved by the one-shot tactics;
  §2  one [ui_<prog>_<off>] per pc -- the [uinstr] fact a verified leaf takes.

EVERY AST IS READ OFF THE MODEL, NEVER COMPUTED HERE.  That is the standing
rule of this layer and the reason the tool is two-pass: gen_code.py may use
tools/riscv_ast.py because the kernel tier's proofs re-derive the encoding, but
a [udecode_*] statement is only as good as the AST it names, and a hand-written
Python decoder gets exactly the cases wrong that a catalog cannot afford --
base JAL/BTYPE immediates are the decoder's POSITIVE residue while compressed
C_J/C_BEQZ/C_BNEZ immediates count HALFwords, LOAD's width field is a plain [Z]
byte count, and the constructor tuple orders are not the assembler's.  So:

  pass 1 (probe)  emit a throwaway .v that [Eval vm_compute]s the model's own
                  decoder at the U-mode reference state [dstateU] for every
                  distinct word -- [exec (ext_decode w) dstateU] for base,
                  [exec (decode_c_pure h) dstateU] for compressed -- plus a
                  [Check] per constructor for the field WIDTHS; run it under
                  coqc and parse the printed [instruction] terms;
  pass 2 (emit)   render the catalog from those terms.

The byte map is re-read INDEPENDENTLY of the instruction index and every pc's
little-endian window (and every RVC-at-4-aligned trailing byte pair) is checked
against the word the catalog claims; a mismatch is fatal.

Output is deterministic and idempotent: regenerating produces a byte-identical
file, so `git diff` after a re-dump is the list of what actually moved -- the
property `make check-decode` relies on for the kernel layer.

Invocation:

  tools/gen_ucode.py --module Sh --out iris/UCodeSh.v --spec tools/ucode_sh.txt
  tools/gen_ucode.py --module Echo --out /tmp/UCodeEcho.v \
      --funcs main,start,strlen,exit,write --omit '0x338:exit never returns'

Run it from the REPO ROOT (--user-rocq and --iris default to the trees there);
it shells out to coqc in the iris/ tree, so an [eval $(opam env --switch=
/shared/xv6rocq)] must be in effect.

Selecting the pcs (a shell has unreachable functions and dead code after a
diverging call; the catalog must not claim facts about instructions no proof
will ever fetch):

  --all                every instruction in the dump
  --funcs a,b,c        every instruction of those symbols' ranges
  --pcs FILE           one address per line
  --spec FILE          the richer form, which also records WHY something was
                       left out so the generated header can say so:
                         func <name>
                         pc <addr>
                         omit <addr> <reason>
                         omitfrom <addr> <reason>      (addr .. end of function)
                         skipfunc <name> <reason>      (a whole function, with
                                                        the reason the header
                                                        must record)
                         skipdefault <reason>          (the reason for every
                                                        OTHER unselected code
                                                        symbol)
                         note <free text>
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

PAGE = 4096

# ---------------------------------------------------------------------------
# The dump.
#
# Parsed with the same regexes gen_code.py uses, widened to the user dumps'
# names: the two tools read the SAME generator's output and a divergence here
# would be a silent one.
# ---------------------------------------------------------------------------

BYTE_RE = re.compile(r'\(\((0x[0-9a-fA-F]+)\)%Z, Z_to_bv 8 \((0x[0-9a-fA-F]+)\)%Z\)')
INSN_RE = re.compile(r'MkKInstr \((0x[0-9a-fA-F]+)\)%Z (\d+)%nat \((0x[0-9a-fA-F]+)\)%Z')
SYM_RE = re.compile(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+)%Z\.')
ASM_RE = re.compile(r'^\s*\(\* (0x[0-9a-fA-F]+): (.*?) \*\)\s*$')
LABEL_RE = re.compile(r'^\s*\(\* <(\S+)> @ (0x[0-9a-fA-F]+) \*\)\s*$')
DEF_Z_RE = re.compile(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+)%Z\.')
SEG_RE = re.compile(r'\(\((0x[0-9a-fA-F]+)\)%Z, \((0x[0-9a-fA-F]+)\)%Z, '
                    r'\((0x[0-9a-fA-F]+)\)%Z, \((\d+)\)%Z\)')


def load_bytes(path):
    """address -> byte value, from a [list_to_map] byte dump."""
    d = {}
    for line in open(path):
        m = BYTE_RE.search(line)
        if m:
            d[int(m.group(1), 16)] = int(m.group(2), 16)
    return d


def load_instrs(path):
    """The decode INDEX: [(addr, width_bits, enc)] in program order."""
    out = []
    for line in open(path):
        m = INSN_RE.search(line)
        if m:
            out.append((int(m.group(1), 16), int(m.group(2)), int(m.group(3), 16)))
    return out


def load_syms(path):
    d = {}
    for line in open(path):
        m = SYM_RE.match(line.strip())
        if m:
            d[m.group(1)] = int(m.group(2), 16)
    return d


def load_asm(path):
    """addr -> objdump mnemonic, and addr -> function label, from the comments.

    The dumper prints a label comment INSTEAD of the asm for the first
    instruction of each function, so [asm] has a hole at every function entry;
    the caller falls back to the AST's own constructor name there."""
    asm, labels = {}, {}
    for line in open(path):
        m = ASM_RE.match(line)
        if m:
            asm.setdefault(int(m.group(1), 16), m.group(2))
            continue
        m = LABEL_RE.match(line)
        if m:
            labels[int(m.group(2), 16)] = m.group(1)
    return asm, labels


def load_data_defs(path):
    """The scalar Z definitions of a <Module>Data.v (MemBase/MemEnd/Entry)."""
    d = {}
    for line in open(path):
        m = DEF_Z_RE.match(line.strip())
        if m:
            d[m.group(1)] = int(m.group(2), 16)
    return d


def load_segments(path):
    """The PT_LOAD table: [(vaddr, filesz, memsz, flags)].  PF_X = 1."""
    out = []
    grab = False
    for line in open(path):
        if '_segments' in line:
            grab = True
        if grab:
            m = SEG_RE.search(line)
            if m:
                out.append(tuple(int(m.group(i), 16) for i in (1, 2, 3))
                           + (int(m.group(4)),))
            if line.strip().startswith('].'):
                grab = False
    return out


class Dump:
    def __init__(self, user_rocq, module, prefix):
        self.module, self.prefix = module, prefix
        ip = os.path.join(user_rocq, module + 'Instrs.v')
        dp = os.path.join(user_rocq, module + 'Data.v')
        sp = os.path.join(user_rocq, module + 'Syms.v')
        for p in (ip, dp, sp):
            if not os.path.exists(p):
                sys.exit('gen_ucode: no such dump file: %s' % p)
        self.bytes = load_bytes(ip)
        self.instrs = load_instrs(ip)
        self.asm, self.labels = load_asm(ip)
        self.data = load_bytes(dp)
        self.defs = load_data_defs(dp)
        self.segments = load_segments(dp)
        self.syms = load_syms(sp)
        if not self.instrs:
            sys.exit('gen_ucode: %s has no instructions' % ip)
        self.by_addr = {}
        for a, w, e in self.instrs:
            if a in self.by_addr:
                sys.exit('gen_ucode: duplicate instruction address 0x%x' % a)
            self.by_addr[a] = (w, e)

    # -- symbol ranges ------------------------------------------------------
    def func_range(self, sym):
        """[lo, hi) for a symbol: up to the next symbol that starts code."""
        if sym not in self.syms:
            sys.exit('gen_ucode: no symbol %r in %sSyms.v' % (sym, self.module))
        lo = self.syms[sym]
        starts = sorted(set(a for a in self.syms.values() if a in self.by_addr))
        end = max(self.by_addr) + 1
        if lo not in starts:
            sys.exit('gen_ucode: symbol %r (0x%x) is not a code address' % (sym, lo))
        i = starts.index(lo)
        return lo, (starts[i + 1] if i + 1 < len(starts) else end)


# ---------------------------------------------------------------------------
# The pc set.
# ---------------------------------------------------------------------------

class PcSpec:
    """Which instructions the catalog covers, and why the rest are out."""

    def __init__(self):
        self.funcs = []          # symbol names, in the order given
        self.extra_pcs = []      # bare addresses
        self.omit = {}           # addr -> reason
        self.omitfrom = {}       # addr -> reason (addr .. end of its function)
        self.skipfuncs = []      # (symbol, reason) -- whole functions left out
        self.skipdefault = None  # the reason for every OTHER unselected function
        self.notes = []

    @staticmethod
    def parse(path):
        sp = PcSpec()
        for lineno, raw in enumerate(open(path), 1):
            line = raw.split('#', 1)[0].strip()
            if not line:
                continue
            kw, _, rest = line.partition(' ')
            rest = rest.strip()
            if kw == 'func':
                sp.funcs.append(rest)
            elif kw == 'pc':
                sp.extra_pcs.append(int(rest, 0))
            elif kw in ('omit', 'omitfrom'):
                a, _, why = rest.partition(' ')
                (sp.omit if kw == 'omit' else sp.omitfrom)[int(a, 0)] = why.strip()
            elif kw == 'skipdefault':
                sp.skipdefault = rest
            elif kw == 'skipfunc':
                nm, _, why = rest.partition(' ')
                sp.skipfuncs.append((nm, why.strip()))
            elif kw == 'note':
                sp.notes.append(rest)
            else:
                sys.exit('gen_ucode: %s:%d: unknown directive %r' % (path, lineno, kw))
        return sp

    def resolve(self, dump):
        """-> (sorted pcs, [(sym, [pcs])] in spec order, [(addr, reason)])."""
        groups, chosen, dropped = [], set(), []
        for sym in self.funcs:
            lo, hi = dump.func_range(sym)
            pcs = []
            cut = None
            for a in sorted(dump.by_addr):
                if not (lo <= a < hi):
                    continue
                if a in self.omitfrom:
                    cut = a
                if cut is not None and a >= cut:
                    dropped.append((a, self.omitfrom[cut]))
                    continue
                if a in self.omit:
                    dropped.append((a, self.omit[a]))
                    continue
                pcs.append(a)
            groups.append((sym, pcs))
            chosen.update(pcs)
        loose = []
        for a in self.extra_pcs:
            if a in self.omit:
                dropped.append((a, self.omit[a]))
                continue
            if a not in chosen:
                loose.append(a)
                chosen.add(a)
        if loose:
            groups.append((None, sorted(loose)))
        return sorted(chosen), groups, sorted(dropped)


def spec_from_flags(dump, args):
    sp = PcSpec()
    if args.all:
        # Every function that starts code, in address order.  A symbol whose
        # range is empty (a data symbol) is skipped by func_range's own check,
        # so filter on the byte map rather than trusting the name.
        starts = sorted(set(a for a in dump.syms.values() if a in dump.by_addr))
        byaddr = {}
        for s, a in sorted(dump.syms.items()):
            byaddr.setdefault(a, s)
        sp.funcs = [byaddr[a] for a in starts]
    if args.funcs:
        sp.funcs += [f for f in args.funcs.split(',') if f]
    if args.pcs:
        for raw in open(args.pcs):
            line = raw.split('#', 1)[0].strip()
            if line:
                sp.extra_pcs.append(int(line, 0))
    for o in (args.omit or []):
        a, _, why = o.partition(':')
        sp.omit[int(a, 0)] = why.strip()
    return sp


# ---------------------------------------------------------------------------
# Verification -- re-derive everything from the byte map alone.
#
# The instruction index and the byte map are two independent renderings of the
# same ELF, so agreeing is evidence; the catalog quotes BOTH (the word in the
# [udec_] lemma, the bytes in [ui_code]) and a proof would only find a
# disagreement at Qed time, one lemma at a time.
# ---------------------------------------------------------------------------

def le_word(by, a, n):
    v = 0
    for i in range(n):
        b = by.get(a + i)
        if b is None:
            return None
        v |= b << (8 * i)
    return v


def verify(dump, pcs):
    bad = []

    def fail(a, msg):
        bad.append('  0x%-6x %s' % (a, msg))

    for a in pcs:
        if a not in dump.by_addr:
            fail(a, 'not an instruction address in %sInstrs.v' % dump.module)
            continue
        width, enc = dump.by_addr[a]
        if width not in (16, 32):
            fail(a, 'unsupported width %d' % width)
            continue
        if a % 2:
            fail(a, 'pc is not 2-aligned (ui_al2 would be false)')
        got = le_word(dump.bytes, a, width // 8)
        if got is None:
            fail(a, 'byte window [0x%x,0x%x) has a hole in %s_bytes'
                 % (a, a + width // 8, dump.prefix))
        elif got != enc:
            fail(a, 'bytes spell 0x%0*x but the index says 0x%0*x'
                 % (width // 4, got, width // 4, enc))
        rvc = (enc & 3) != 3
        if rvc != (width == 16):
            fail(a, 'width %d disagrees with the RVC bits of 0x%x' % (width, enc))
        if a % PAGE > PAGE - 4:
            fail(a, 'fetch window crosses a page (ui_inpage would be false)')
        if width == 16 and a % 4 == 0:
            for j in (2, 3):
                if dump.bytes.get(a + j) is None:
                    fail(a, 'RVC at a 4-aligned pc but byte 0x%x is not in %s_bytes'
                         % (a + j, dump.prefix))
    if bad:
        sys.exit('gen_ucode: IMAGE VERIFICATION FAILED (%d problems):\n%s'
                 % (len(bad), '\n'.join(bad)))


# ---------------------------------------------------------------------------
# The probe: read the ASTs off the model.
# ---------------------------------------------------------------------------

PROBE_PRELUDE = """(* THROWAWAY -- written and deleted by tools/gen_ucode.py. *)
From Stdlib Require Import ZArith Bool List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvExec RiscvFetchExec.
Require Import WpDecodeBridge DecodeTotalU WpRvcBridge.
Local Open Scope Z_scope.
Import Defs.

(* The two decoders, at the U-mode reference state the [udecode_*] predicates
   are stated over.  [decode_c_pure] is [ext_decode_compressed] with the
   [Ext_Zca] gate discharged (WpRvcBridge.v), which is what [rvc_oneshot]
   proves the catalog's lemmas against. *)
Definition db (w : Z) : option instruction :=
  match exec (ext_decode (mword_of_int w : mword 32)) dstateU with
  | Some (i, _) => Some i | _ => None end.
Definition dc (w : Z) : option instruction :=
  match exec (decode_c_pure (mword_of_int w : mword 16)) dstateU with
  | Some (i, _) => Some i | _ => None end.

Set Printing Depth 100000.
Set Printing Width 200.
Unset Printing Notations.
"""


def run_coqc(iris, path, keep_log=None):
    cmd = ['coqc', '-R', '.', 'xv6iris', '-R', '../model-xv6iris', 'Riscv',
           '-R', '../kernel-rocq', 'Kernel', '-R', '../user-rocq', 'User',
           '-w', '-notation-overridden', path]
    r = subprocess.run(cmd, cwd=iris, capture_output=True, text=True)
    out = r.stdout + r.stderr
    if keep_log:
        open(keep_log, 'w').write(out)
    if r.returncode != 0:
        sys.exit('gen_ucode: probe compile failed (%s):\n%s' % (path, out[-4000:]))
    return out


def probe_values(iris, work, words, keep):
    """words: sorted [(width, value)] -> {(width, value): printed term}."""
    L = [PROBE_PRELUDE]
    for width, w in words:
        L.append('Eval vm_compute in (%s 0x%0*x).' % ('dc' if width == 16 else 'db',
                                                      width // 4, w))
    path = os.path.join(work, 'ZZUProbeVal.v')
    open(path, 'w').write('\n'.join(L) + '\n')
    out = run_coqc(iris, path, keep and path + '.log')
    blocks = re.findall(r'^\s*=(.*?)^\s*: option instruction\s*$', out, re.S | re.M)
    if len(blocks) != len(words):
        sys.exit('gen_ucode: probe printed %d results for %d words'
                 % (len(blocks), len(words)))
    res, undec = {}, []
    for (width, w), b in zip(words, blocks):
        t = ' '.join(b.split())
        if t == 'None':
            undec.append((width, w))
        elif t.startswith('Some '):
            res[(width, w)] = t[len('Some '):].strip()
        else:
            sys.exit('gen_ucode: unparseable probe result for 0x%x: %r' % (w, t))
    if undec:
        sys.exit('gen_ucode: the model does not decode %d word(s):\n%s' %
                 (len(undec), '\n'.join('  0x%0*x (%d-bit)' % (wd // 4, w, wd)
                                        for wd, w in undec)))
    if not keep:
        _rm(path)
    return res


def probe_types(iris, work, ctors, keep):
    """ctors: sorted constructor names -> {name: [field type terms]}."""
    L = [PROBE_PRELUDE]
    for c in ctors:
        L.append('Check %s.' % c)
    path = os.path.join(work, 'ZZUProbeTy.v')
    open(path, 'w').write('\n'.join(L) + '\n')
    out = run_coqc(iris, path, keep and path + '.log')
    # `Check C.` prints the name then, indented, `: <type>`.  Rejoin the
    # wrapped lines before parsing.
    chunks, cur = [], None
    for line in out.splitlines():
        if line.startswith('[NOTE]'):
            continue
        if line and not line[0].isspace():
            if cur is not None:
                chunks.append(cur)
            cur = line.strip()
        elif cur is not None:
            cur += ' ' + line.strip()
    if cur is not None:
        chunks.append(cur)
    if len(chunks) != len(ctors):
        sys.exit('gen_ucode: Check probe printed %d results for %d constructors'
                 % (len(chunks), len(ctors)))
    out_ty = {}
    for c, ch in zip(ctors, chunks):
        body = ch.split(':', 1)[1].strip() if ':' in ch else ''
        m = re.match(r'forall\s+_\s*:\s*(.*)$', body)
        if not m:
            out_ty[c] = []          # a nullary constructor (BGE, true, tt, ...)
            continue
        ty = _cut_at_top_comma(m.group(1))
        out_ty[c] = flatten_prod(parse_term(ty))
    if not keep:
        _rm(path)
    return out_ty


def _rm(path):
    """Delete a probe file and every artefact coqc left beside it."""
    base = path[:-2] if path.endswith('.v') else path
    d, b = os.path.split(base)
    for p in [base + e for e in ('.v', '.vo', '.vos', '.vok', '.glob')] + \
             [os.path.join(d, '.' + b + '.aux')]:
        try:
            os.remove(p)
        except OSError:
            pass


def _cut_at_top_comma(s):
    depth = 0
    for i, ch in enumerate(s):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == ',' and depth == 0:
            return s[:i].strip()
    return s.strip()


# ---------------------------------------------------------------------------
# The printed term: parse, then render as Rocq source.
#
# With [Unset Printing Notations] the model prints an AST as a pure
# application spine -- `BTYPE (pair (pair (pair 96%bv (Regidx 10%bv))
# (Regidx 15%bv)) BGE)` -- so the parser needs nothing but parentheses.
# ---------------------------------------------------------------------------

TOK_RE = re.compile(r'\(|\)|[^\s()]+')


def parse_term(s):
    toks = TOK_RE.findall(s)
    pos = [0]

    def atom():
        t = toks[pos[0]]
        if t == '(':
            pos[0] += 1
            e = spine()
            if pos[0] >= len(toks) or toks[pos[0]] != ')':
                sys.exit('gen_ucode: unbalanced term %r' % s)
            pos[0] += 1
            return e
        pos[0] += 1
        m = re.fullmatch(r'(-?\d+)%bv', t)
        if m:
            return ('bv', int(m.group(1)))
        if re.fullmatch(r'-?\d+', t):
            return ('int', int(t))
        return ('app', t, [])

    def spine():
        head = atom()
        args = []
        while pos[0] < len(toks) and toks[pos[0]] != ')':
            args.append(atom())
        if not args:
            return head
        if head[0] != 'app':
            sys.exit('gen_ucode: non-constructor head in %r' % s)
        return ('app', head[1], head[2] + args)

    e = spine()
    if pos[0] != len(toks):
        sys.exit('gen_ucode: trailing tokens in %r' % s)
    return e


def flatten_prod(ty):
    """`prod (prod A B) C` -> [A, B, C]; anything else -> [it]."""
    if ty[0] == 'app' and ty[1] == 'prod' and len(ty[2]) == 2:
        return flatten_prod(ty[2][0]) + [ty[2][1]]
    return [ty]


def flatten_pairs(t):
    if t[0] == 'app' and t[1] == 'pair' and len(t[2]) == 2:
        return flatten_pairs(t[2][0]) + [t[2][1]]
    return [t]


def bits_width(ty):
    if ty[0] == 'app' and ty[1] in ('bits', 'mword') and len(ty[2]) == 1 \
            and ty[2][0][0] == 'int':
        return ty[2][0][1]
    return None


def collect_ctors(t, acc):
    if t[0] == 'app':
        if t[1] not in ('pair',):
            acc.add(t[1])
        for a in t[2]:
            collect_ctors(a, acc)


def _paren(s):
    return '(%s)' % s if ' ' in s else s


def render(t, ftypes, annotate):
    """Render a parsed AST node as the Rocq term the catalog states.

    [annotate] carries the `: mword N` ascription onto bare bitvector fields.
    It is set only at the INSTRUCTION constructor's own fields, matching
    UCodeEcho.v: a [Regidx]'s width is fixed by [Regidx] and saying it again
    adds nothing."""
    if t[0] == 'bv':
        w = bits_width(ftypes) if ftypes is not None else None
        if w is None:
            sys.exit('gen_ucode: bitvector %d at a non-[bits] field %r' % (t[1], ftypes))
        return 'mword_of_int %d : mword %d' % (t[1], w) if annotate \
            else 'mword_of_int %d' % t[1]
    if t[0] == 'int':
        return str(t[1])
    name, args = t[1], t[2]
    if not args:
        return name
    if len(args) != 1:
        sys.exit('gen_ucode: %s applied to %d arguments' % (name, len(args)))
    fields = flatten_pairs(args[0])
    tys = FIELD_TYPES.get(name)
    if tys is None or len(tys) != len(fields):
        sys.exit('gen_ucode: %s has %d printed fields but %s declared types'
                 % (name, len(fields), 'no' if tys is None else len(tys)))
    # the ascription is for THIS constructor's own bitvector fields only:
    # a [Regidx]'s width is fixed by [Regidx], and saying it again is noise
    parts = [render(f, ty, annotate and f[0] == 'bv') for f, ty in zip(fields, tys)]
    if len(parts) == 1:
        return '%s %s' % (name, _paren(parts[0]))
    return '%s (%s)' % (name, ', '.join(parts))


FIELD_TYPES = {}


def ast_head(t):
    return t[1] if t[0] == 'app' else '?'


def mnemonic(t):
    """The AST head as an assembler mnemonic: C_SDSP -> c.sdsp, BTYPE -> btype."""
    h = ast_head(t)
    return ('c.' + h[2:]).lower() if h.startswith('C_') else h.lower()


def disasm(dump, pc, width, t):
    """The comment text for one instruction.

    Two repairs to what the dump can give: the dumper prints a `<fn> @ addr`
    LABEL instead of the asm for each function's first instruction, so those
    pcs have no disassembly at all; and objdump prints a compressed
    instruction under its EXPANDED name (`sd ra,56(sp)` for a [c.sdsp]), which
    is the wrong mnemonic to read beside a lemma stating [C_SDSP].  So a
    compressed instruction takes its mnemonic from the AST and its operands
    from objdump."""
    asm = dump.asm.get(pc)
    if width != 16:
        return asm or mnemonic(t)
    ops = asm.split(None, 1)[1:] if asm else []
    return ' '.join([mnemonic(t)] + ops)


# ---------------------------------------------------------------------------
# Emission.
# ---------------------------------------------------------------------------

IMPORTS = """From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvExtras.
Require Import UserPtTree.
Require Import WpDecodeBridge DecodeTotalU WpRvcBridge.
Require Import UmodeMem UmodeAbi.
From User Require %(M)sInstrs %(M)sData %(M)sSyms.
Local Open Scope Z_scope.
Import Defs."""

# Above this many instructions the header quotes per-function RANGES rather
# than a full disassembly; every pc carries its own comment in §2 either way,
# and a 1500-line listing at the top of the file is not a table of contents.
LISTING_LIMIT = 200


def page_bound(maxkey):
    """The catalog's key bound: the first page boundary past the last key.

    A page multiple rather than `maxkey+1` because that is the shape the users
    of the fact want -- [uM_only_img] asks "is the written window disjoint from
    every key of the image", and the windows a program writes are its stack,
    which starts at a page boundary above the image."""
    return (maxkey // PAGE + 1) * PAGE


def geometry(pc, width):
    if width == 16:
        return 'rvc4' if pc % 4 == 0 else 'rvc2'
    return 'base'


def geometry_note(pc, width):
    if width == 16:
        return 'RVC, 4-aligned' if pc % 4 == 0 else 'RVC, 2 mod 4'
    return 'base, 4-aligned' if pc % 4 == 0 else 'base, 2 mod 4 -> split fetch'


def comment_block(text):
    """A free-standing `(* ... *)` comment, paragraphs split on a blank line."""
    out = []
    for para in text.split('\n\n'):
        if out:
            out.append('')
        out += wrap_comment(para, '   ')
    out[0] = '(*' + out[0][2:]
    out[-1] = out[-1] + ' *)'
    return out


def csan(text):
    """Make a free-text fragment safe inside a Rocq comment.

    Rocq lexes STRING LITERALS inside comments, so a stray double quote in an
    objdump operand or a spec's reason text swallows the rest of the file; and
    a literal [(*] or [*)] nests or closes the comment.  All three come from
    data this tool does not control."""
    return (text.replace('"', "'").replace('(*', '( *').replace('*)', '* )'))


def wrap_comment(text, indent, width=72):
    words, lines, cur = csan(text).split(), [], ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w).strip()
    if cur:
        lines.append(cur)
    return [indent + l for l in lines]


def emit(dump, prog, pcs, groups, dropped, skipfuncs, skipdefault, notes, asts,
         out_path, args):
    P, M = prog, dump.module
    tmax = max(dump.bytes)
    dmax = max(dump.data) if dump.data else None
    tbound, dbound = page_bound(tmax), (page_bound(dmax) if dmax is not None else None)
    # The TEXT pages are the pages of the EXECUTABLE PT_LOAD segment(s), not
    # just of the instruction bytes: a program's .rodata shares the last text
    # page and gets handed to [write] as a buffer, so the page must carry the
    # load permission too and the count must cover it.  (sh: R-X runs
    # 0x0..0x1c54, so 2 pages even though the last instruction is at 0x127c.)
    xsegs = [(v, mz) for v, fz, mz, fl in dump.segments if fl & 1]
    if not xsegs:
        sys.exit('gen_ucode: %s has no executable PT_LOAD segment' % P)
    text_pages = sorted(set(pg for v, mz in xsegs
                            for pg in range(v // PAGE, (v + mz - 1) // PAGE + 1)))
    if text_pages != list(range(len(text_pages))):
        sys.exit('gen_ucode: the text pages of %s are %s -- not 0..N-1, so the '
                 'range-indexed layout record does not describe this image; '
                 'the record needs an explicit page LIST.' % (P, text_pages))
    ntext = len(text_pages)
    stray = sorted(a for a in dump.bytes if a // PAGE >= ntext)
    if stray:
        sys.exit('gen_ucode: %d text byte(s) outside the executable segment(s), '
                 'first 0x%x' % (len(stray), stray[0]))

    L = []
    a = L.append

    # ---- header ----------------------------------------------------------
    a('(* %s -- the CODE CATALOG of the user program [%s].' % (os.path.basename(out_path), P))
    a('   AUTO-GENERATED by tools/gen_ucode.py.  DO NOT EDIT BY HAND.')
    a('')
    for l in wrap_comment(
            'The verified-user tier (claude-notes/projects/user-verified.md) drives '
            'one step from one [uinstr] fact (UmodeMem.v): the pure statement that at '
            'a given user pc the program\'s bytes sit in the process image [M], the '
            'pc\'s page is mapped fetch-executable, and the fetched word decodes to a '
            'named AST on any U-mode machine.  This file proves those facts for the '
            '%d instruction(s) of this catalog, from the dumped image '
            '[User.%sInstrs.%s_bytes].' % (len(pcs), M, P), '   '):
        a(l)
    a('')
    a('   Two premises carry every [uinstr] lemma:')
    a('')
    a('     [%s_text_sub M]   -- [M] contains the dumped text (so a proof may talk' % P)
    a('                          about a process image that ALSO has rodata, bss, a')
    a('                          stack page and an argument area in it);')
    a('     [%s_text_layout pt]' % P)
    a('                       -- the pure page-table fact: each of the %d page(s) of' % ntext)
    a('                          the executable segment (0x0 .. 0x%x) is mapped with a' % (ntext * PAGE - 1))
    a('                          leaf that permits instruction FETCH and a user data')
    a('                          LOAD.  The load half is not decoration: a program\'s')
    a('                          .rodata shares a text page and its string literals are')
    a('                          handed to [write]/[exec] as buffers.  The DATA page and')
    a('                          the heap are NOT this file\'s business -- they are')
    a('                          read-WRITE and belong to USpec%s.v, as do the stack and' % (P[0].upper() + P[1:]))
    a('                          argv facts.')
    a('')
    a('   Image geometry, as dumped:')
    a('     text  0x%x .. 0x%x   (%d bytes)' % (min(dump.bytes), tmax + 1,
                                                 len(dump.bytes)))
    for v, fz, mz, fl in dump.segments:
        a('     PT_LOAD 0x%-6x filesz 0x%-6x memsz 0x%-6x flags %d%s'
          % (v, fz, mz, fl, '   (executable: %d text page(s))' % ntext if fl & 1 else ''))
    if dmax is not None:
        a('     data  0x%x .. 0x%x   (%d bytes)' % (min(dump.data), dmax + 1, len(dump.data)))
    a('     entry 0x%x, MemBase 0x%x, MemEnd 0x%x'
      % (dump.defs.get(P + 'Entry', 0), dump.defs.get(P + 'MemBase', 0),
         dump.defs.get(P + 'MemEnd', 0)))
    a('')
    a('   Catalogued: %d instruction(s), %d distinct word(s), in %d function(s):'
      % (len(pcs), len(asts), sum(1 for s, p in groups if s and p)))
    full = len(pcs) <= LISTING_LIMIT
    for sym, gp in groups:
        if not gp:
            continue
        nm = sym if sym else '(loose addresses)'
        if full:
            a('')
            a('     <%s> @ 0x%x' % (nm, gp[0]))
            for pc in gp:
                width, enc = dump.by_addr[pc]
                a('       %5x:  %0*x%s  %s'
                  % (pc, width // 4, enc, '    ' if width == 16 else '',
                     csan(disasm(dump, pc, width, asts[(width, enc)]))))
        else:
            a('     %-16s 0x%-6x .. 0x%-6x  %4d instr'
              % ('<%s>' % nm, gp[0], gp[-1], len(gp)))
    # ---- what is deliberately NOT here -----------------------------------
    # A catalog is a claim about coverage as much as about content, so the
    # reasons live in the file, not only in the spec that generated it.
    covered = set(sym for sym, gp in groups if sym and gp)
    others = [(nm, dump.syms[nm]) for nm in sorted(dump.syms)
              if dump.syms[nm] in dump.by_addr and nm not in covered]
    if dropped or others:
        a('')
        a('   NOT catalogued, because no proof ever fetches it:')
    if dropped:
        byreason = {}
        for addr, why in dropped:
            byreason.setdefault(why or '(no reason recorded)', []).append(addr)
        for why in sorted(byreason):
            addrs = sorted(byreason[why])
            span = ('0x%x' % addrs[0]) if len(addrs) == 1 \
                else '0x%x .. 0x%x (%d instr)' % (addrs[0], addrs[-1], len(addrs))
            for l in wrap_comment('%s -- %s' % (span, why), '       '):
                a(l)
    if others:
        skipped = dict(skipfuncs)
        if skipdefault:
            for nm, _ in others:
                skipped.setdefault(nm, skipdefault)
        byreason = {}
        for nm, addr in others:
            byreason.setdefault(skipped.get(nm) or '(no reason recorded)', []).append(nm)
        for why in sorted(byreason):
            names = byreason[why]
            for l in wrap_comment('%s -- %s' % (', '.join(names), why), '       '):
                a(l)
    if notes:
        a('')
        for l in wrap_comment(' '.join(notes), '   '):
            a(l)
    a('')
    for l in wrap_comment(
            'Every AST below was READ OFF the model -- [vm_compute] of the decoder at '
            'the U-mode reference state [dstateU] (base) / [decode_c_pure] under the '
            'misa.C gate (compressed) -- never guessed.  In particular every jal/branch '
            'immediate is the decoder\'s POSITIVE residue, and a COMPRESSED branch or '
            'jump immediate counts HALFwords.  The compressed words decode to the raw '
            'C_* constructors -- the expansion into ITYPE/STORE/... happens in '
            '[execute], not here.', '   '):
        a(l)
    a(' *)')
    a(IMPORTS % dict(M=M))
    a('')

    # ---- §0 --------------------------------------------------------------
    a('(* ===================================================================== *)')
    a('(* §0 The image and the layout premise.                                   *)')
    a('(* ===================================================================== *)')
    a('')
    a('(* [M] contains the dumped text -- the generic image inclusion (UmodeAbi.v)')
    a('   at this program\'s text bytes.  An inclusion (not an equality), so a')
    a('   process image carrying rodata/bss/stack/argv on top still qualifies. *)')
    a('Definition %s_text_sub (M : gmap Z (bv 8)) : Prop :=' % P)
    a('  uimg_sub %sInstrs.%s_bytes M.' % (M, P))
    a('')
    a('(* ... and the dumped RODATA/data.  A string literal a program hands to')
    a('   [write] lives here, not in the text map, so the readable-window lemma')
    a('   below needs THIS inclusion. *)')
    a('Definition %s_data_sub (M : gmap Z (bv 8)) : Prop :=' % P)
    a('  uimg_sub %sData.%s_data M.' % (M, P))
    a('')
    a('(* ... and the two together, so a spec carries ONE image premise.  The')
    a('   per-pc [uinstr] facts below deliberately take only [%s_text_sub]: an' % P)
    a('   instruction fetch never reads the data half. *)')
    a('Definition %s_img_sub (M : gmap Z (bv 8)) : Prop :=' % P)
    a('  %s_text_sub M /\\ %s_data_sub M.' % (P, P))
    a('')
    a('Lemma %s_img_text (M : gmap Z (bv 8)) : %s_img_sub M -> %s_text_sub M.' % (P, P, P))
    a('Proof. intros [ H _ ]. exact H. Qed.')
    a('Lemma %s_img_data (M : gmap Z (bv 8)) : %s_img_sub M -> %s_data_sub M.' % (P, P, P))
    a('Proof. intros [ _ H ]. exact H. Qed.')
    a('')
    a('(* ---- the KEY RANGE of each dumped map ------------------------------- *)')
    a('(* The bounds are COMPUTED from the dump (text keys stop at 0x%x, data keys' % tmax)
    a('   at 0x%x) and rounded up to the next page, which is the shape the users of'
      % (dmax if dmax is not None else 0))
    a('   the fact want: [UmodeAbi.uM_only_img] asks exactly "the written window is')
    a('   disjoint from every key of [img]", and the windows a program writes are')
    a('   its stack, which starts at a page boundary above the image. *)')
    a('')
    a('Lemma list_key_lt {A : Type} (L : list (Z * A)) (B k : Z) (b : A) :')
    a('  forallb (fun kv => Z.ltb (fst kv) B) L = true -> In (k, b) L -> k < B.')
    a('Proof.')
    a('  induction L as [ | x xs IH ]; cbn [forallb In]; [ tauto | ].')
    a('  intros HF [ Hx | Hin ].')
    a('  - apply andb_prop in HF as [ H1 _ ]. subst x. cbn in H1.')
    a('    apply Z.ltb_lt in H1. exact H1.')
    a('  - apply andb_prop in HF as [ _ H2 ]. exact (IH H2 Hin).')
    a('Qed.')
    a('')
    for nm, mod, mapname, bound in (('%s_bytes_key_lt' % P, M, '%s_bytes' % P, tbound),
                                    ('%s_data_key_lt' % P, M, '%s_data' % P, dbound)):
        if bound is None:
            continue
        modfile = mod + ('Instrs' if mapname.endswith('_bytes') else 'Data')
        a('Lemma %s (k : Z) (b : bv 8) :' % nm)
        a('  %s.%s !! k = Some b -> k < %d.' % (modfile, mapname, bound))
        a('Proof.')
        a('  intro Hk.')
        a('  apply elem_of_list_to_map_2 in Hk.')
        a('  apply elem_of_list_In in Hk.')
        a('  refine (list_key_lt _ %d k b _ Hk).' % bound)
        a('  vm_compute. reflexivity.')
        a('Qed.')
        a('')
    a('(* The vpn of an address IS the vpn of its page base.  This is the')
    a('   arithmetic the two projections below need, and having it ONCE is what')
    a('   lets a per-pc proof state no svpn identity of its own -- UCodeEcho.v')
    a('   could do that identification with a [vm_compute] per instance only')
    a('   because its whole image was page 0. *)')
    a('Lemma %s_svpn_page (a : Z) :' % P)
    a('  0 <= a < 274877906944 ->')
    a('  svpn_of (mword_of_int a : mword 64)')
    a('    = svpn_of (mword_of_int (4096 * (a / 4096)) : mword 64).')
    a('Proof.')
    a('  intros [ Hlo Hhi ].')
    a('  assert (Hq : 0 <= 4096 * (a / 4096) <= a).')
    a('  { split.')
    a('    - apply Z.mul_nonneg_nonneg; [ lia | apply Z.div_pos; lia ].')
    a('    - apply Z.mul_div_le; lia. }')
    a('  apply bv_eq.')
    a('  rewrite (svpn_of_unsigned_lo (mword_of_int a : mword 64))')
    a('    by (rewrite uint_unsigned, moi64_small; lia).')
    a('  rewrite (svpn_of_unsigned_lo (mword_of_int (4096 * (a / 4096)) : mword 64))')
    a('    by (rewrite uint_unsigned, moi64_small; lia).')
    a('  rewrite !uint_unsigned, !moi64_small by lia.')
    a('  rewrite !Z.shiftr_div_pow2 by lia.')
    a('  change (2 ^ 12) with 4096.')
    a('  rewrite (Z.mul_comm 4096 (a / 4096)), Z.div_mul by lia. reflexivity.')
    a('Qed.')
    a('')
    a('(* The pure page-table premise: each of the %d page(s) of the executable' % ntext)
    a('   segment is mapped with a leaf that permits instruction FETCH and a user')
    a('   data LOAD.  Quantified over the page INDEX rather than one field per')
    a('   page, so the record does not change shape when a program grows; page [i]')
    a('   is user va [4096*i], because a user program is linked at 0')
    a('   (user/user.ld).  The load half is what makes a .rodata string sharing a')
    a('   text page a legal [write] buffer. *)')
    a('Record %s_text_layout (pt : uptd) : Prop := %sTextLayout {' % (P, P[0].upper() + P[1:]))
    a('  %stl_pg : forall i : Z, 0 <= i < %d ->' % (P[0], ntext))
    a('    exists w : mword 64,')
    a('      ud_um pt !! svpn_of (mword_of_int (4096 * i) : mword 64) = Some w /\\')
    a('      uleaf_ok (InstructionFetch tt) w /\\ uleaf_ok (Load Data) w')
    a('}.')
    a('')
    a('(* the fetch projection, in exactly the shape [UmodeMem.uva_fetch_leaf]')
    a('   wants -- it takes the page index from the address itself *)')
    a('Lemma %s_text_layout_fetch (pt : uptd) (off : Z) :' % P)
    a('  %s_text_layout pt -> 0 <= off < %d ->' % (P, ntext * PAGE))
    a('  uva_fetch_leaf pt (mword_of_int off).')
    a('Proof.')
    a('  intros [ Hpg ] Hoff.')
    a('  destruct (Hpg (off / 4096)')
    a('              ltac:(split; [ apply Z.div_pos; lia')
    a('                           | apply Z.div_lt_upper_bound; lia ]))')
    a('    as (w & Hl & Hok & _).')
    a('  exists w. rewrite (%s_svpn_page off ltac:(lia)). split; assumption.' % P)
    a('Qed.')
    a('')
    a('(* the same leaf, in the shape [UmodeAbi.uv_rd]\'s [urd_leaf] field wants *)')
    a('Lemma %s_text_layout_load (pt : uptd) (a : Z) :' % P)
    a('  %s_text_layout pt -> 0 <= a < %d ->' % (P, ntext * PAGE))
    a('  exists w : mword 64,')
    a('    ud_um pt !! svpn_of (mword_of_int a : mword 64) = Some w /\\')
    a('    uleaf_ok (Load Data) w.')
    a('Proof.')
    a('  intros [ Hpg ] Ha.')
    a('  destruct (Hpg (a / 4096)')
    a('              ltac:(split; [ apply Z.div_pos; lia')
    a('                           | apply Z.div_lt_upper_bound; lia ]))')
    a('    as (w & Hl & _ & Hok).')
    a('  exists w. rewrite (%s_svpn_page a ltac:(lia)). split; assumption.' % P)
    a('Qed.')
    a('')
    a('(* ONE readable byte of the loaded data image, on a text page -- the')
    a('   address is a parameter, so each string literal a program hands to')
    a('   [write] costs one line at the call site. *)')
    a('Lemma %s_rodata_rd1 (pt : uptd) (M : gmap Z (bv 8)) (a : Z) (b : bv 8) :' % P)
    a('  %s_text_layout pt -> %s_data_sub M ->' % (P, P))
    a('  0 <= a < %d ->' % (ntext * PAGE))
    a('  %sData.%s_data !! a = Some b ->' % (M, P))
    a('  uv_rd pt M a 1.')
    a('Proof.')
    a('  intros Hl Hsub Ha Hb. constructor.')
    a('  - lia.')
    a('  - lia.')
    a('  - change (2 ^ 38) with 274877906944. lia.')
    a('  - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.')
    a('    rewrite Z.add_0_r. exact (%s_text_layout_load pt a Hl Ha).' % P)
    a('  - intros j Hj. assert (Hj0 : j = 0) by lia. subst j.')
    a('    rewrite Z.add_0_r. exists b. exact (Hsub a b Hb).')
    a('Qed.')
    a('')
    a('(* the addresses this file is about, as the dumper named them *)')
    pinned = [s for s, gp in groups if s and gp]
    if pinned:
        a('Lemma %s_syms_pins :' % P)
        conj = ' /\\\n  '.join('%sSyms.%s = 0x%x' % (M, s, dump.syms[s]) for s in pinned)
        a('  %s.' % conj)
        a('Proof.')
        a('  unfold %s.' % (',\n         '.join('%sSyms.%s' % (M, s) for s in pinned)))
        a('  split_and!; reflexivity.')
        a('Qed.')
        a('')

    # ---- §1 --------------------------------------------------------------
    a('(* ===================================================================== *)')
    a('(* §1 Per-WORD decode facts.                                              *)')
    a('(* ===================================================================== *)')
    a('')
    for l in comment_block(
            'One lemma per DISTINCT word (%d of them for %d instructions), reused at '
            'every pc where that word occurs.\n\n'
            'Base words: the concrete-state bridge at [dstateU] (WpDecodeBridge), '
            'transported to any state agreeing with it on the U-mode decode read set '
            '[D_u] -- exactly the [udecode_base] shape [uinstr] wants.  The closing '
            'step descends the AST with [f_equal] and finishes each bitvector leaf '
            'with [bv_eq] (a bare [reflexivity] would have to match well-formedness '
            'proof terms).\n\n'
            'Compressed words: [rvc_oneshot] under the misa.C premise.'
            % (len(asts), len(pcs))):
        a(l)
    a('')
    a('Ltac udec_base_bridge :=')
    a('  let s := fresh "s" in let Hag := fresh "Hag" in')
    a('  intros s Hag;')
    a('  apply (decode_state_bridge D_u _ dstateU);')
    a('  [ exact Hag')
    a('  | vm_compute; reflexivity')
    a('  | vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ] ].')
    a('')
    a('Ltac udec_rvc_oneshot :=')
    a('  let s := fresh "s" in let Hm := fresh "Hm" in intros s Hm; rvc_oneshot s Hm.')
    a('')
    # Sorted by (width, AST head, word): deterministic, and it groups the
    # catalogue the way a reader reads it (all the c.sdsp together).
    order = sorted(asts, key=lambda k: (k[0], ast_head(asts[k]), k[1]))
    firstc = firstb = True
    rendered = {}
    for width, w in order:
        t = asts[(width, w)]
        term = render(t, None, True)
        rendered[(width, w)] = term
        if width == 16 and firstc:
            a('(* ---- compressed ---- *)')
            firstc = False
        if width == 32 and firstb:
            a('(* ---- base ---- *)')
            firstb = False
        ex = _example_pc(dump, pcs, width, w)
        note = disasm(dump, ex, width, t) if ex is not None else mnemonic(t)
        a('(* %0*x  %s *)' % (width // 4, w, csan(note)))
        a('Lemma udec_%0*x :' % (width // 4, w))
        if width == 16:
            a('  udecode_rvc (mword_of_int 0x%04x) (%s).' % (w, term))
            a('Proof. udec_rvc_oneshot. Qed.')
        else:
            a('  udecode_base (mword_of_int 0x%08x) (%s).' % (w, term))
            a('Proof. udec_base_bridge. Qed.')
        a('')

    # ---- §2 --------------------------------------------------------------
    a('(* ===================================================================== *)')
    a('(* §2 Per-PC [uinstr] facts.                                              *)')
    a('(* ===================================================================== *)')
    a('')
    for l in comment_block(
            'Shared shape: [ui_al2] / [ui_canon] / [ui_inpage] are [vm_compute]s on '
            'the concrete pc; [ui_leaf] is ONE application of '
            '[%s_text_layout_fetch], which finds the pc\'s page itself; and each '
            'byte of [ui_code]\'s window is a concrete [%s_bytes] lookup '
            'transported by [%s_text_sub].\n\n'
            'NOTE the RVC-at-4-ALIGNED extra obligation: the fetch of a compressed '
            'instruction at a 4-aligned pc is ONE 4-byte read, so [uinstr] also '
            'wants the two FOLLOWING bytes present (their values are irrelevant -- '
            'they belong to the next instruction, and are quoted from the image).'
            % (P, P, P)):
        a(l)
    a('')
    a('(* the four field goals that do not depend on the encoding *)')
    a('Ltac ui_frame off Hl :=')
    a('  constructor;')
    a('  [ vm_compute; reflexivity                                   (* ui_al2    *)')
    a('  | vm_compute; reflexivity                                   (* ui_canon  *)')
    a('  | apply (%s_text_layout_fetch _ off Hl); lia               (* ui_leaf   *)' % P)
    a('  | apply Z.leb_le; vm_compute; reflexivity                   (* ui_inpage *)')
    a('  | idtac ].')
    a('')
    a('(* one image byte, through [%s_text_sub] *)' % P)
    a('Ltac ui_byte Hsub := apply Hsub; vm_compute; f_equal; apply bv_eq; reflexivity.')
    a('')
    a('Ltac ui_bytes2 Hsub :=')
    a('  let j := fresh "j" in let Hj := fresh "Hj" in')
    a('  intros j Hj; do 2 (destruct j as [|j]; [ui_byte Hsub|]); lia.')
    a('Ltac ui_bytes4 Hsub :=')
    a('  let j := fresh "j" in let Hj := fresh "Hj" in')
    a('  intros j Hj; do 4 (destruct j as [|j]; [ui_byte Hsub|]); lia.')
    a('')
    a('(* compressed at a 2-mod-4 pc: 2-byte fetch, no trailing-byte obligation *)')
    a('Ltac ui_rvc2 off Hl Hsub h dec :=')
    a('  let Hc := fresh "Hc" in')
    a('  ui_frame off Hl;')
    a('  exists h; split; [vm_compute; reflexivity|];')
    a('  split; [ui_bytes2 Hsub|];')
    a('  split; [exact dec|];')
    a('  intro Hc; vm_compute in Hc; discriminate.')
    a('')
    a('(* compressed at a 4-aligned pc: 4-byte fetch, so [b2]/[b3] must be there *)')
    a('Ltac ui_rvc4 off Hl Hsub h dec b2 b3 :=')
    a('  ui_frame off Hl;')
    a('  exists h; split; [vm_compute; reflexivity|];')
    a('  split; [ui_bytes2 Hsub|];')
    a('  split; [exact dec|];')
    a('  intros _; exists b2, b3; split; ui_byte Hsub.')
    a('')
    a('(* base (either alignment): 4 bytes of window *)')
    a('Ltac ui_base off Hl Hsub w dec :=')
    a('  ui_frame off Hl;')
    a('  exists w; split; [vm_compute; reflexivity|];')
    a('  split; [ui_bytes4 Hsub|]; exact dec.')
    a('')
    sec = os.path.basename(out_path)[:-2]
    a('Section %s.' % sec)
    a('  Context (pt : uptd) (M : gmap Z (bv 8)).')
    a('  Context (Hl : %s_text_layout pt) (Hsub : %s_text_sub M).' % (P, P))
    a('')
    for sym, gp in groups:
        if not gp:
            continue
        nm = sym if sym else '(loose addresses)'
        a('  (* ---------------- <%s> @ 0x%x ---------------- *)' % (nm, gp[0]))
        a('')
        for pc in gp:
            width, enc = dump.by_addr[pc]
            t = asts[(width, enc)]
            term = rendered[(width, enc)]
            note = disasm(dump, pc, width, t)
            a('  (* 0x%x  %s  (%s) *)' % (pc, csan(note), geometry_note(pc, width)))
            a('  Lemma ui_%s_%02x :' % (P, pc))
            a('    uinstr pt M (mword_of_int 0x%x) %s' % (pc, 'true' if width == 16 else 'false'))
            a('      (%s).' % term)
            g = geometry(pc, width)
            if g == 'base':
                a('  Proof. ui_base 0x%x Hl Hsub (mword_of_int 0x%08x : mword 32) udec_%08x. Qed.'
                  % (pc, enc, enc))
            elif g == 'rvc2':
                a('  Proof. ui_rvc2 0x%x Hl Hsub (mword_of_int 0x%04x : mword 16) udec_%04x. Qed.'
                  % (pc, enc, enc))
            else:
                b2, b3 = dump.bytes[pc + 2], dump.bytes[pc + 3]
                a('  Proof. ui_rvc4 0x%x Hl Hsub (mword_of_int 0x%04x : mword 16) udec_%04x'
                  % (pc, enc, enc))
                a('           (Z_to_bv 8 0x%02x) (Z_to_bv 8 0x%02x). Qed.' % (b2, b3))
            a('')
    a('End %s.' % sec)

    text = '\n'.join(L) + '\n'
    # A comment that never closes is a LEXER error 10 000 lines later, and coqc
    # reports it at the end of the file with no hint of where it started -- so
    # balance the delimiters here, where the offending line is still to hand.
    depth, line = 0, 0
    for n, l in enumerate(L, 1):
        for tok in re.findall(r'\(\*|\*\)', l):
            if tok == '(*':
                if depth == 0:
                    line = n
                depth += 1
            else:
                depth -= 1
                if depth < 0:
                    sys.exit('gen_ucode: stray `*)` at generated line %d: %r' % (n, l))
    if depth:
        sys.exit('gen_ucode: unterminated comment opened at generated line %d: %r'
                 % (line, L[line - 1]))

    old = open(out_path).read() if os.path.exists(out_path) else None
    if old == text:
        print('%s: unchanged (%d instr, %d words)' % (out_path, len(pcs), len(asts)))
        return
    open(out_path, 'w').write(text)
    print('%s: %d lines, %d instr facts, %d decode lemmas (%d compressed, %d base)'
          % (out_path, len(L) + 1, len(pcs), len(asts),
             sum(1 for wd, _ in asts if wd == 16), sum(1 for wd, _ in asts if wd == 32)))


def _example_pc(dump, pcs, width, w):
    for pc in pcs:
        if dump.by_addr[pc] == (width, w) and pc in dump.asm:
            return pc
    return None


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--user-rocq', default='user-rocq')
    ap.add_argument('--iris', default='iris', help='cwd for coqc, and -R . xv6iris')
    ap.add_argument('--module', required=True, help='dump module prefix, e.g. Sh')
    ap.add_argument('--prefix', help='dump map prefix, e.g. sh (default: --module lowercased)')
    ap.add_argument('--prog', help='name used in the emitted lemmas (default: --prefix)')
    ap.add_argument('--out', required=True)
    ap.add_argument('--spec', help='pc-selection file (func/pc/omit/omitfrom/skipfunc/note)')
    ap.add_argument('--funcs', help='comma-separated symbol names')
    ap.add_argument('--pcs', help='file of addresses, one per line')
    ap.add_argument('--omit', action='append', metavar='ADDR[:REASON]')
    ap.add_argument('--all', action='store_true', help='every instruction in the dump')
    ap.add_argument('--work', help='where to write the probe files (default: a temp dir)')
    ap.add_argument('--keep-probe', action='store_true')
    args = ap.parse_args()

    prefix = args.prefix or args.module.lower()
    prog = args.prog or prefix
    dump = Dump(args.user_rocq, args.module, prefix)

    if args.spec:
        sp = PcSpec.parse(args.spec)
        flag = spec_from_flags(dump, args)
        sp.funcs += flag.funcs
        sp.extra_pcs += flag.extra_pcs
        sp.omit.update(flag.omit)
    else:
        sp = spec_from_flags(dump, args)
    if not sp.funcs and not sp.extra_pcs:
        sys.exit('gen_ucode: no pcs selected -- pass --all, --funcs, --pcs or --spec')

    pcs, groups, dropped = sp.resolve(dump)
    chosen = set(sym for sym, gp in groups if sym and gp)
    for nm, _ in sp.skipfuncs:
        if nm not in dump.syms or dump.syms[nm] not in dump.by_addr:
            sys.exit('gen_ucode: skipfunc %r is not a code symbol of %s'
                     % (nm, dump.module))
        if nm in chosen:
            sys.exit('gen_ucode: %r is both selected and skipfunc\'d' % nm)
    verify(dump, pcs)
    print('selected %d instruction(s) in %d function(s); %d omitted'
          % (len(pcs), sum(1 for s, g in groups if s and g), len(dropped)))

    words = sorted(set((dump.by_addr[pc][0], dump.by_addr[pc][1]) for pc in pcs))
    work = args.work or tempfile.mkdtemp(prefix='gen_ucode.')
    os.makedirs(work, exist_ok=True)
    raw = probe_values(args.iris, work, words, args.keep_probe)
    asts = {k: parse_term(v) for k, v in raw.items()}
    ctors = set()
    for t in asts.values():
        collect_ctors(t, ctors)
    FIELD_TYPES.update(probe_types(args.iris, work, sorted(ctors), args.keep_probe))
    print('probed %d distinct word(s), %d constructor(s)' % (len(words), len(ctors)))

    emit(dump, prog, pcs, groups, dropped, sp.skipfuncs, sp.skipdefault, sp.notes,
         asts, args.out, args)
    return 0


if __name__ == '__main__':
    sys.exit(main())

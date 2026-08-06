#!/usr/bin/env python3
"""gen_decode.py -- keep the iris/ instruction-DECODE layer in step with the ELF.

The decode layer (iris/Code*.v and friends) proves, for every instruction of
every verified function, a

    kernel_text -* instr <pc> <is_rvc> <AST>

fact whose proof feeds the raw encoding word to [mk_rvc] / [mk_base].  Two
things in each such site are properties of the IMAGE rather than of the proof:

  * the encoding word itself (e.g. [mword_of_int 0xf33fd0ef : mword 32]), and
  * the pc-relative immediate inside the AST (a JAL/branch offset, or the
    low-12 of an auipc+addi pair).

Both move whenever the kernel is relaid out -- which any xv6 update does, even
one that changes no instruction in the function concerned, because a call whose
target shifted re-encodes and because linker relaxation resizes call sequences.
The ADDRESSES are already symbol-relative ([KernelSyms.bpin + 0x14]) and so
survive relayout untouched; these two literals are what does not.

This tool derives them from the image instead of by hand:

  (no flag)  CHECK: every site's stated word is compared against the bytes at
             its address in kernel-rocq/KernelInstrs.v, and every decoded
             immediate against our own decode of that word; every decode lemma
             is checked against itself.  Zero mismatches means the decode layer
             and the image agree.  Run it on a tree that is known good and it
             validates the tool; run it after a re-dump and it is the worklist.
  --update   rewrite the stale words / immediates / word-keyed lemma names in
             place.  Refuses, and lists, any site where the INSTRUCTION changed
             rather than just its immediate: those are real code changes whose
             proofs need a human.

Address resolution follows the file's own [Notation BP := KernelSyms.bpin]
aliases, so nothing here needs a table of which file covers which function.
"""

import argparse
import glob
import os
import re
import sys

# --------------------------------------------------------------------------
# The image: symbols + the flat byte map, both read from the TRACKED dumps
# (never from a freshly built ELF -- xv6-riscv/ is gitignored and routinely
# drifts from the image the proofs are about).
# --------------------------------------------------------------------------

def load_syms(path):
    syms = {}
    for line in open(path):
        m = re.match(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+)%Z\.', line)
        if m:
            syms[m.group(1)] = int(m.group(2), 16)
    return syms


def load_bytes(path):
    by = {}
    pat = re.compile(r'\(\((0x[0-9a-fA-F]+)\)%Z, Z_to_bv 8 \((0x[0-9a-fA-F]+)\)%Z\)')
    for line in open(path):
        m = pat.search(line)
        if m:
            by[int(m.group(1), 16)] = int(m.group(2), 16)
    return by


def word_at(by, addr, nbytes):
    """Little-endian read of nbytes at addr; None if any byte is absent."""
    v = 0
    for i in range(nbytes):
        b = by.get(addr + i)
        if b is None:
            return None
        v |= b << (8 * i)
    return v


# --------------------------------------------------------------------------
# Parsing a decode site out of a .v file
# --------------------------------------------------------------------------

def split_args(text, pos, want):
    """Read `want` top-level Rocq arguments starting at text[pos].

    An argument is a parenthesised group or a bare token.  Returns
    (list-of-arg-strings, index-just-past-the-last-arg), or None if the text
    runs out first."""
    args = []
    i = pos
    n = len(text)
    while len(args) < want:
        while i < n and text[i] in ' \t\n\r':
            i += 1
        if i >= n:
            return None
        if text[i] == '(':
            depth = 0
            start = i
            while i < n:
                if text[i] == '(':
                    depth += 1
                elif text[i] == ')':
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            arg = text[start:i]
            # an optional scope suffix belongs to the argument
            while i < n and text[i] == '%':
                j = i + 1
                while j < n and (text[j].isalnum() or text[j] == '_'):
                    j += 1
                arg += text[i:j]
                i = j
        else:
            start = i
            while i < n and text[i] not in ' \t\n\r().':
                i += 1
            # a trailing '.' ends the tactic, but '.' also occurs inside
            # qualified names such as KernelSyms.bpin
            while i < n and text[i] == '.' and i + 1 < n and (text[i + 1].isalpha() or text[i + 1] == '_'):
                i += 1
                while i < n and (text[i].isalnum() or text[i] == '_'):
                    i += 1
            arg = text[start:i]
            if not arg:
                return None
        args.append((arg, start, i))
    return args, i


def strip_outer(s):
    s = s.strip()
    s = re.sub(r'%[A-Za-z_]+$', '', s).strip()
    while s.startswith('(') and s.endswith(')'):
        depth = 0
        ok = True
        for k, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
                if depth == 0 and k != len(s) - 1:
                    ok = False
                    break
        if not ok:
            break
        s = s[1:-1].strip()
        s = re.sub(r'%[A-Za-z_]+$', '', s).strip()
    return s


def resolve_addr(expr, notations, syms):
    """Evaluate an address expression like `(BP + 0x14)%Z` to a concrete Z."""
    e = strip_outer(expr)
    e = re.sub(r'\bmword_of_int\b', '', e)
    e = strip_outer(e)
    # Normalise numeric literals FIRST: the `x00` of `0x00` would otherwise be
    # matched as an identifier by the substitution below.
    e = re.sub(r'\b0[xX][0-9a-fA-F]+', lambda m: str(int(m.group(0), 16)), e)

    # KernelSyms.foo / a file-local Notation / a bare decimal literal
    def sub_ident(m):
        name = m.group(0)
        if name.startswith('KernelSyms.'):
            base = name.split('.', 1)[1]
            if base in syms:
                return str(syms[base])
            raise KeyError(name)
        if name in notations:
            return str(notations[name])
        raise KeyError(name)

    e2 = re.sub(r'(?:KernelSyms\.)?[A-Za-z_][A-Za-z_0-9]*', sub_ident, e)
    if not re.fullmatch(r'[-+*0-9() \t]+', e2):
        raise ValueError(e)
    return int(eval(e2, {"__builtins__": {}}, {}))


def parse_word(expr):
    """`(mword_of_int 0xf33fd0ef : mword 32)` -> (0xf33fd0ef, 32)."""
    m = re.search(r'mword_of_int\s+(0x[0-9a-fA-F]+|\d+)\s*:\s*mword\s+(\d+)', expr)
    if m:
        return int(m.group(1), 0), int(m.group(2))
    return None


NOTATION_RE = re.compile(r'Notation\s+([A-Za-z_][A-Za-z_0-9]*)\s*:=\s*(KernelSyms\.[A-Za-z_][A-Za-z_0-9]*)\s*\.')
# The RHS may be a qualified name (`KernelSyms.acquire.`), so the terminating
# '.' is the one NOT followed by an identifier character.
DEFN_ADDR_RE = re.compile(
    r'Definition\s+([A-Za-z_][A-Za-z_0-9]*)\s*:\s*Z\s*:=\s*(.+?)\.(?![A-Za-z_0-9])', re.S)
# Named encoding words (`Definition w_auipc : mword 32 := mword_of_int 0xa117.`)
# live wherever it was convenient -- WpDecode.v, not the Code file that uses
# them -- so these are collected across the whole directory.
DEFN_WORD_RE = re.compile(
    r'Definition\s+([A-Za-z_][A-Za-z_0-9]*)\s*:\s*mword\s+(\d+)\s*:=\s*'
    r'mword_of_int\s+(0[xX][0-9a-fA-F]+|\d+)\s*\.')


def strip_comments(text):
    """Blank out (* ... *) comments, preserving offsets and line structure."""
    out = list(text)
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith('(*', i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
        elif text.startswith('*)', i) and depth > 0:
            depth -= 1
            i += 2
            if depth == 0:
                for k in range(start, i):
                    if out[k] != '\n':
                        out[k] = ' '
        else:
            i += 1
    return ''.join(out)


def file_notations(text, syms):
    """Symbolic aliases a file introduces for a function entry address."""
    nots = {}
    for m in NOTATION_RE.finditer(text):
        base = m.group(2).split('.', 1)[1]
        if base in syms:
            nots[m.group(1)] = syms[base]
    for m in DEFN_ADDR_RE.finditer(text):
        try:
            nots[m.group(1)] = resolve_addr(m.group(2), nots, syms)
        except Exception:
            pass
    return nots


class Site:
    __slots__ = ('file', 'tactic', 'addr', 'width', 'word', 'word_span',
                 'ast', 'ast_span', 'lineno', 'raw_addr', 'named_word',
                 'dec', 'dec_span', 'raw')

    def __init__(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)


def collect_notations(iris_dir, syms):
    """Entry-address aliases from every file, so a proof file can use the
    alias its sibling Code file introduced (ProofPushOff.v uses CodePushOff's
    [PP]).  Collisions are impossible in practice: an alias names one symbol."""
    nots = {}
    for f in sorted(glob.glob(os.path.join(iris_dir, '*.v'))):
        nots.update(file_notations(strip_comments(open(f).read()), syms))
    return nots


def collect_word_defs(iris_dir):
    """Named encoding-word constants, gathered across the whole iris tree."""
    words = {}
    for f in sorted(glob.glob(os.path.join(iris_dir, '*.v'))):
        body = strip_comments(open(f).read())
        for m in DEFN_WORD_RE.finditer(body):
            words[m.group(1)] = (int(m.group(3), 0), int(m.group(2)))
    return words


def parse_sites(path, syms, word_defs=None, extra_notations=None):
    """Every mk_rvc / mk_base invocation in `path`, resolved against the image."""
    raw = open(path).read()
    text = strip_comments(raw)
    word_defs = word_defs or {}
    nots = dict(extra_notations or {})
    nots.update(file_notations(text, syms))
    sites, unparsed = [], []
    for m in re.finditer(r'\bmk_(rvc|base)\b', text):
        # the Ltac definitions in KernelText.v are not call sites
        line_start = text.rfind('\n', 0, m.start()) + 1
        if text[line_start:m.start()].lstrip().startswith('Ltac'):
            continue
        kind = m.group(1)
        want = 6 if kind == 'rvc' else 5
        got = split_args(text, m.end(), want)
        if got is None:
            unparsed.append((path, text[:m.start()].count('\n') + 1, 'args'))
            continue
        args, _ = got
        try:
            addr = resolve_addr(args[0][0], nots, syms)
        except Exception:
            unparsed.append((path, text[:m.start()].count('\n') + 1, 'addr:' + args[0][0][:40]))
            continue
        pw = parse_word(args[1][0])
        named_word = None
        if pw is None:
            # a named word constant (CodeEntry-style `w_jal`), defined elsewhere
            named_word = strip_outer(args[1][0])
            pw = word_defs.get(named_word)
        if pw is None:
            unparsed.append((path, text[:m.start()].count('\n') + 1, 'word:' + args[1][0][:30]))
            continue
        word, width = pw
        sites.append(Site(
            file=path, tactic=kind, addr=addr, width=width, word=word,
            word_span=(args[1][1], args[1][2]), named_word=named_word,
            ast=args[3][0], ast_span=(args[3][1], args[3][2]),
            dec=strip_outer(args[4][0]), dec_span=(args[4][1], args[4][2]),
            lineno=text[:m.start()].count('\n') + 1,
            raw_addr=strip_outer(args[0][0]), raw=raw))
    return sites, unparsed, text


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# Immediates
#
# Only a few AST shapes carry a value that MOVES when the kernel is relaid
# out: a JAL/branch offset, the low-12 of an auipc+addi pair, the hi-20 of the
# auipc itself, and a relocated load/store displacement.  Everything else in
# an AST (register indices, struct offsets, widths) is layout-invariant.
#
# Each extractor below is validated against every site in the tracked tree by
# --check, so a mistake here cannot pass silently.
# --------------------------------------------------------------------------

def imm_from_word(word, width):
    """The relocated immediate a word encodes, as (kind, value), or None."""
    if width == 32:
        op = word & 0x7f
        if op == 0x6f:                                   # JAL
            imm = ((((word >> 31) & 1) << 20) | (((word >> 12) & 0xff) << 12)
                   | (((word >> 20) & 1) << 11) | (((word >> 21) & 0x3ff) << 1))
            return ('JAL21', imm & 0x1fffff)
        if op == 0x63:                                   # BRANCH
            imm = ((((word >> 31) & 1) << 12) | (((word >> 7) & 1) << 11)
                   | (((word >> 25) & 0x3f) << 5) | (((word >> 8) & 0xf) << 1))
            return ('B13', imm & 0x1fff)
        if op == 0x13:                                   # OP-IMM
            # A shift's immediate is a SHAMT, not a relocated displacement:
            # it is layout-invariant and the AST spells it `mword 6`/`mword 5`.
            if ((word >> 12) & 7) in (1, 5):
                return None
            return ('I12', (word >> 20) & 0xfff)
        if op in (0x03, 0x67):                           # LOAD / JALR
            return ('I12', (word >> 20) & 0xfff)
        if op in (0x17, 0x37):                           # AUIPC / LUI
            return ('U20', (word >> 12) & 0xfffff)
        if op == 0x23:                                   # STORE
            return ('S12', (((word >> 25) & 0x7f) << 5) | ((word >> 7) & 0x1f))
        return None

    if width == 16 and (word & 3) == 1:
        f3 = (word >> 13) & 7
        if f3 == 5:                                      # C.J
            b = lambda i: (word >> i) & 1
            imm = ((b(12) << 11) | (b(8) << 10) | (((word >> 9) & 3) << 8)
                   | (b(6) << 7) | (b(7) << 6) | (b(2) << 5) | (b(11) << 4)
                   | (((word >> 3) & 7) << 1))
            # the AST stores imm[11:1], i.e. the offset with its always-zero
            # low bit dropped
            return ('CJ11', (imm >> 1) & 0x7ff)
        if f3 in (6, 7):                                 # C.BEQZ / C.BNEZ
            b = lambda i: (word >> i) & 1
            imm = ((b(12) << 8) | (((word >> 5) & 3) << 6) | (b(2) << 5)
                   | (((word >> 10) & 3) << 3) | (((word >> 3) & 3) << 1))
            return ('CB8', (imm >> 1) & 0xff)
    return None


# How each AST shape spells the immediate it carries.  The captured group is
# the literal that --update rewrites.
_LIT = r'(0x[0-9a-fA-F]+|\d+)'
AST_IMM_PATTERNS = [
    ('JAL21', re.compile(r'JAL\s*\(\s*mword_of_int\s+' + _LIT)),
    ('B13',   re.compile(r'BTYPE\s*\(\s*mword_of_int\s+' + _LIT)),
    ('U20',   re.compile(r'UTYPE\s*\(\s*mword_of_int\s+' + _LIT)),
    ('I12',   re.compile(r'ITYPE\s*\(\s*mword_of_int\s+' + _LIT)),
    ('I12',   re.compile(r'LOAD\s*\(\s*mword_of_int\s+' + _LIT)),
    ('S12',   re.compile(r'STORE\s*\(\s*mword_of_int\s+' + _LIT)),
    ('I12',   re.compile(r'JALR\s*\(\s*mword_of_int\s+' + _LIT)),
    # a compressed jump/branch, expanded into its base-AST form
    ('CJ11',  re.compile(r'JAL\s*\(\s*sign_extend\'\s+21\s+\(concat_vec\s+\(mword_of_int\s+' + _LIT)),
    ('CB8',   re.compile(r'BTYPE\s*\(\s*sign_extend\'\s+13\s+\(concat_vec\s+\(mword_of_int\s+' + _LIT)),
]


def imm_from_ast(ast):
    """The immediate literal an AST states, as (kind, value, span), or None."""
    for kind, pat in AST_IMM_PATTERNS:
        m = pat.search(ast)
        if m:
            return (kind, int(m.group(1), 0), m.span(1))
    return None


def decode_files(iris_dir):
    """Every .v carrying decode sites -- Code*.v plus the handful of others
    (the trampoline's UservecDefs/UserretDefs, SmodeCore, ...)."""
    out = []
    for f in sorted(glob.glob(os.path.join(iris_dir, '*.v'))):
        if os.path.basename(f) == 'KernelText.v':
            continue                      # defines the tactics, uses neither
        body = strip_comments(open(f).read())
        if re.search(r'\bmk_(rvc|base)\b', body):
            out.append(f)
    return out


def check(files, syms, by, word_defs, verbose=False, notations=None):
    """Compare every decode site against the image.  Returns the mismatch list."""
    n_sites = n_imm = n_sym = n_compressed = 0
    bad_word, bad_imm, unparsed = [], [], []
    for f in files:
        sites, unp, _ = parse_sites(f, syms, word_defs, notations)
        unparsed.extend(unp)
        for s in sites:
            n_sites += 1
            actual = word_at(by, s.addr, s.width // 8)
            if actual is None or actual != s.word:
                bad_word.append((s, actual))
                continue
            # Immediates: a relocated one appears in any 4-byte encoding and
            # in the compressed jumps/branches.  Every other compressed
            # displacement is a stack or struct offset, which no relayout
            # moves, and imm_from_word returns None for those.
            fw = imm_from_word(s.word, s.width)
            if fw is None:
                n_compressed += 1
                continue
            fa = imm_from_ast(strip_outer(s.ast))
            if fw is None:
                continue
            if fa is None:
                n_sym += 1          # AST states the immediate via a named constant
                continue
            n_imm += 1
            if fw[0] != fa[0] or fw[1] != fa[1]:
                bad_imm.append((s, fw, fa))

    print("decode sites          : %d" % n_sites)
    print("  immediates checked  : %d" % n_imm)
    print("  symbolic immediates : %d (AST names the constant; not a literal)" % n_sym)
    print("  compressed          : %d (displacement is layout-invariant)" % n_compressed)
    print("unparsed sites        : %d" % len(unparsed))
    ls_self, ls_name = check_decode_lemmas(decode_lemma_index(os.path.dirname(files[0]) or '.'))
    print("decode lemmas         : %d self-inconsistent (AST vs own word)" % len(ls_self))
    for name, f, word, fw, fa in ls_self[:20]:
        print("  L %s (%s): word 0x%x encodes %s=%d, AST states %s=%d"
              % (name, os.path.basename(f), word, fw[0], fw[1], fa[0], fa[1]))
    print("WORD MISMATCHES       : %d" % len(bad_word))
    print("IMMEDIATE MISMATCHES  : %d" % len(bad_imm))
    for s, actual in bad_word[:40]:
        print("  W %s:%d  %s  stated 0x%x, image %s"
              % (os.path.basename(s.file), s.lineno, s.raw_addr, s.word,
                 ('0x%x' % actual) if actual is not None else 'ABSENT'))
    for s, fw, fa in bad_imm[:40]:
        print("  I %s:%d  %s  word 0x%x gives %s=%d, AST states %s=%d"
              % (os.path.basename(s.file), s.lineno, s.raw_addr, s.word,
                 fw[0], fw[1], fa[0], fa[1]))
    if verbose:
        for p_, ln, why in unparsed[:20]:
            print("  ? %s:%d %s" % (os.path.basename(p_), ln, why))
    return bad_word, bad_imm + ls_self + ls_name, unparsed


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--iris', default='iris', help='directory holding the decode layer')
    ap.add_argument('--kernel-rocq', default='kernel-rocq', help='directory holding the tracked dumps')
    ap.add_argument('--files', nargs='*', help='restrict to these .v files')
    ap.add_argument('--update', action='store_true',
                    help='rewrite stale words/immediates/lemma names in place')
    ap.add_argument('--dry-run', action='store_true',
                    help='with --update, report what would change and write nothing')
    ap.add_argument('--verbose', '-v', action='store_true')
    args = ap.parse_args()

    syms = load_syms(os.path.join(args.kernel_rocq, 'KernelSyms.v'))
    by = load_bytes(os.path.join(args.kernel_rocq, 'KernelInstrs.v'))
    word_defs = collect_word_defs(args.iris)
    notations = collect_notations(args.iris, syms)
    print("image: %d symbols, %d text bytes, %d named word constants"
          % (len(syms), len(by), len(word_defs)))

    files = args.files or decode_files(args.iris)

    if not args.update:
        bad_word, bad_imm, _ = check(files, syms, by, word_defs, args.verbose, notations)
        return 1 if (bad_word or bad_imm) else 0

    edits, dec_moves, moved_refs, flagged, changed = plan_updates(
        files, syms, by, word_defs, notations)
    refs = count_referrers(files, syms, word_defs, notations)
    idx = decode_lemma_index(args.iris)
    wanted = {}
    for old, news in dec_moves.items():
        keep_old = refs.get(old, 0) > moved_refs[old] or len(news) > 1
        wanted[old] = {n: (w, keep_old) for n, w in news.items()}

    print("sites needing update  : %d" % changed)
    print("files touched         : %d" % len(edits))
    print("decode lemmas moving  : %d" % len(wanted))
    print("SITES NEEDING A HUMAN : %d" % len(flagged))
    for s, actual, why in flagged[:60]:
        print("  ! %s:%d  %s  0x%x -> %s : %s"
              % (os.path.basename(s.file), s.lineno, s.raw_addr, s.word,
                 ('0x%x' % actual) if actual is not None else 'ABSENT', why))
    if args.dry_run:
        print("(dry run -- nothing written)")
        return 0
    lem_edits, added, renamed = sync_decode_lemmas(args.iris, wanted, idx)
    ls_self, ls_name = check_decode_lemmas(idx)
    fix_edits, fixed = fix_decode_lemmas(idx, ls_self, ls_name)
    # ONE pass over each file: a rename resizes it, so applying the lemma
    # edits first would invalidate every site span planned above.
    for src in (lem_edits, fix_edits):
        for f, es in src.items():
            edits[f].extend(es)
    apply_edits(edits)
    print("decode lemma bodies restated : %d" % fixed)
    print("decode lemmas renamed : %d" % renamed)
    print("decode lemmas added   : %d" % added)
    return 0






# --------------------------------------------------------------------------
# --update: rewrite the stale literals
# --------------------------------------------------------------------------

def instr_shape(word, width):
    """Everything an encoding says EXCEPT its relocated immediate.

    Used as a guard: this tool may only refresh an immediate.  If the shape
    changed too, the function's code genuinely changed and its proof needs a
    human, so the site is reported instead of rewritten."""
    if width == 32:
        op = word & 0x7f
        if op == 0x6f:
            return ('JAL', (word >> 7) & 0x1f)
        if op == 0x63:
            return ('B', (word >> 12) & 7, (word >> 15) & 0x1f, (word >> 20) & 0x1f)
        if op in (0x17, 0x37):
            return ('U', op, (word >> 7) & 0x1f)
        if op in (0x13, 0x03, 0x67):
            return ('I', op, (word >> 12) & 7, (word >> 7) & 0x1f, (word >> 15) & 0x1f)
        if op == 0x23:
            return ('S', (word >> 12) & 7, (word >> 15) & 0x1f, (word >> 20) & 0x1f)
        return ('raw32', word)
    if width == 16 and (word & 3) == 1:
        f3 = (word >> 13) & 7
        if f3 == 5:
            return ('CJ',)
        if f3 in (6, 7):
            return ('CB', f3, (word >> 7) & 7)
    return ('raw16', word)


def _hexlit(old_literal, value):
    """Format `value` the way `old_literal` was written."""
    m = re.match(r'0[xX]([0-9a-fA-F]+)$', old_literal)
    if m:
        return '0x%0*x' % (len(m.group(1)), value)
    if re.fullmatch(r'[0-9a-fA-F]+', old_literal) and not old_literal.isdigit():
        return '%0*x' % (len(old_literal), value)      # a lemma name's suffix
    return str(value)


def _sub_word(arg_text, new_word):
    return re.sub(r'(mword_of_int\s+)(0x[0-9a-fA-F]+|\d+)',
                  lambda m: m.group(1) + _hexlit(m.group(2), new_word), arg_text, count=1)


def _sub_imm(ast_text, kind, new_value):
    """Replace the immediate literal inside an AST, keeping its shape."""
    for k, pat in AST_IMM_PATTERNS:
        if k != kind:
            continue
        m = pat.search(ast_text)
        if m:
            a, b = m.span(1)
            return ast_text[:a] + _hexlit(m.group(1), new_value) + ast_text[b:]
    return None


WORD_KEYED_RE = re.compile(r'^([A-Za-z_][A-Za-z_0-9]*?_)([0-9a-fA-F]{4,8})$')


def plan_updates(files, syms, by, word_defs, notations):
    """Per-file edit list, plus the sites this tool must not touch."""
    from collections import defaultdict
    edits = defaultdict(list)
    dec_moves = defaultdict(dict)     # old lemma -> {new lemma: new word}
    moved_refs = defaultdict(int)     # old lemma -> how many sites left it
    flagged = []
    changed = 0
    for f in files:
        sites, _, raw = parse_sites(f, syms, word_defs, notations)
        for s in sites:
            actual = word_at(by, s.addr, s.width // 8)
            if actual is None:
                flagged.append((s, actual, 'address absent from image'))
                continue
            if actual == s.word:
                continue
            if instr_shape(s.word, s.width) != instr_shape(actual, s.width):
                flagged.append((s, actual, 'instruction changed, not just its immediate'))
                continue
            if s.named_word is not None:
                flagged.append((s, actual, 'word is the named constant %s' % s.named_word))
                continue
            changed += 1
            # 1. the encoding word in the tactic call
            edits[f].append((s.word_span[0], s.word_span[1],
                             _sub_word(raw[s.word_span[0]:s.word_span[1]], actual)))
            # 2. the immediate, in the tactic's AST and in the Lemma statement
            fw = imm_from_word(actual, s.width)
            fa = imm_from_ast(strip_outer(s.ast))
            if fw is not None and fa is not None and fw[1] != fa[1]:
                new_ast = _sub_imm(s.ast, fw[0], fw[1])
                if new_ast is None:
                    flagged.append((s, actual, 'cannot place immediate in AST'))
                    continue
                edits[f].append((s.ast_span[0], s.ast_span[1], new_ast))
                # the same AST text appears in the Lemma statement above
                stmt = raw.rfind(s.ast, max(0, s.ast_span[0] - 4000), s.ast_span[0])
                if stmt != -1:
                    edits[f].append((stmt, stmt + len(s.ast), new_ast))
            elif fw is not None and fa is None:
                flagged.append((s, actual, 'immediate moved but AST names it symbolically'))
                continue
            # 3. a word-keyed decode lemma has to follow its word
            m = WORD_KEYED_RE.match(s.dec)
            if m and int(m.group(2), 16) == s.word:
                new_name = m.group(1) + ('%0*x' % (len(m.group(2)), actual))
                dec_moves[s.dec][new_name] = actual
                moved_refs[s.dec] += 1
                edits[f].append((s.dec_span[0], s.dec_span[1], new_name))
    return edits, dec_moves, moved_refs, flagged, changed


def apply_edits(edits):
    """Apply each file's edits right-to-left so earlier spans stay valid."""
    for f, es in edits.items():
        raw = open(f).read()
        seen = set()
        for a, b, new in sorted(es, key=lambda e: -e[0]):
            if (a, b) in seen:
                continue
            seen.add((a, b))
            raw = raw[:a] + new + raw[b:]
        open(f, 'w').write(raw)


DECODE_LEMMA_RE = re.compile(
    r'(Lemma\s+)([A-Za-z_][A-Za-z_0-9]*)(\s+s\s*:.*?exec\s*\(\s*ext_decode(?:_compressed)?\s*\(\s*'
    r'mword_of_int\s+)(0x[0-9a-fA-F]+|\d+)(\s*:\s*mword\s+(\d+)\s*\)\s*\)\s*s\s*=\s*Some\s*\()(.*?)(,\s*s\s*\)\s*\.)',
    re.S)


def decode_lemma_index(iris_dir):
    """name -> (file, match-span, word, width, ast) for every decode lemma."""
    idx = {}
    for f in sorted(glob.glob(os.path.join(iris_dir, '*.v'))):
        body = strip_comments(open(f).read())
        for m in DECODE_LEMMA_RE.finditer(body):
            idx[m.group(2)] = (f, m.span(), int(m.group(4), 0), int(m.group(6)), m.group(7))
    return idx


def count_referrers(files, syms, word_defs, notations):
    from collections import Counter
    c = Counter()
    for f in files:
        sites, _, _ = parse_sites(f, syms, word_defs, notations)
        for s in sites:
            c[s.dec] += 1
    return c


def sync_decode_lemmas(iris_dir, wanted, idx):
    """`wanted` maps old lemma name -> {new_name: new_word}.

    A lemma every referrer moved off is renamed in place; one still needed by
    an unchanged referrer is kept and the new variant added beside it."""
    from collections import defaultdict
    per_file = defaultdict(list)
    added = renamed = 0
    for old, news in wanted.items():
        if old not in idx:
            continue
        f, (a, b), word, width, ast = idx[old]
        body = open(f).read()
        text = body[a:b]
        for new_name, (new_word, keep_old) in news.items():
            if new_name in idx:
                continue                      # the target lemma already exists
            fw = imm_from_word(new_word, width)
            new_text = text.replace(old, new_name, 1)
            new_text = re.sub(r'(ext_decode(?:_compressed)?\s*\(\s*mword_of_int\s+)(0x[0-9a-fA-F]+|\d+)',
                              lambda m: m.group(1) + _hexlit(m.group(2), new_word), new_text, count=1)
            if fw is not None:
                sub = _sub_imm(new_text, fw[0], fw[1])
                if sub is not None:
                    new_text = sub
            if keep_old:
                per_file[f].append((b, b, '\n\n' + new_text.strip()))
                added += 1
            else:
                per_file[f].append((a, b, new_text))
                renamed += 1
    return per_file, added, renamed




def check_decode_lemmas(idx):
    """Each decode lemma must agree with ITSELF and with its name.

    A site can be right while the lemma it cites is stale, so the site check
    alone is not enough: verify that every lemma's AST states the immediate its
    own word encodes, and that a word-keyed name says the word it decodes."""
    bad_self, bad_name = [], []
    for name, (f, span, word, width, ast) in sorted(idx.items()):
        fw = imm_from_word(word, width)
        fa = imm_from_ast(ast)
        if fw is not None and fa is not None and (fw[0] != fa[0] or fw[1] != fa[1]):
            bad_self.append((name, f, word, fw, fa))
        # A name is word-keyed only when its hex suffix already IS the word:
        # there is no way to tell a stale word-keyed name from an ordinary
        # address- or mnemonic-keyed one (`kv_dec4`, `kvdec_mv_a2a5` both parse
        # as hex).  Renaming is therefore driven from the call sites, which do
        # know the old word, and never guessed at from a name alone.
    return bad_self, bad_name


def fix_decode_lemmas(idx, bad_self, bad_name):
    """Restate a lemma's word (from its name) and its immediate (from the word)."""
    from collections import defaultdict
    per_file = defaultdict(list)
    targets = {}
    for name, f, word in bad_name:
        targets[name] = int(WORD_KEYED_RE.match(name).group(2), 16)
    for name, f, word, fw, fa in bad_self:
        targets.setdefault(name, word)
    for name, new_word in targets.items():
        f, (a, b), word, width, ast = idx[name]
        text = open(f).read()[a:b]
        new_text = re.sub(
            r'(ext_decode(?:_compressed)?\s*\(\s*mword_of_int\s+)(0x[0-9a-fA-F]+|\d+)',
            lambda m: m.group(1) + _hexlit(m.group(2), new_word), text, count=1)
        fw = imm_from_word(new_word, width)
        if fw is not None:
            sub = _sub_imm(new_text, fw[0], fw[1])
            if sub is not None:
                new_text = sub
        per_file[f].append((a, b, new_text))
    return per_file, len(targets)


if __name__ == '__main__':
    sys.exit(main())

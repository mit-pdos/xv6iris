#!/usr/bin/env python3
"""fix_proof_imms.py -- the image literals that live in PROOF files.

tools/gen_code.py regenerates the decode layer, but that is not the only place
an instruction's immediate is written down: a proof applies a WP leaf with the
immediate spelled out, e.g.

    iApply (wp_jal_s_sconf Phi (mword_of_int (KL + 0x0e)) kl_ra
              (mword_of_int 2091704 : mword 21) ...

and usually repeats it in the register-map / address assertions that follow.
Those go stale on any relayout exactly as the decode layer does.

Each site is located by its PC, which the application states right before the
immediate: decode the image at that pc, and the immediate follows.  This is
deliberately NOT a pattern-match on numbers -- a wrong immediate compiles
fine and silently proves something about a different instruction, and unlike
the decode layer nothing downstream would catch it.

  (no flag)  report every leaf application whose immediate disagrees
  --update   rewrite them, and the repeats of the same stale literal inside
             the same proof
"""

import argparse
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import riscv_ast as R

# ---------------------------------------------------------------------------
# Image + source helpers, inlined: they used to live in gen_decode.py, which
# full generation retired.
# ---------------------------------------------------------------------------

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


DEFN_ADDR_RE = re.compile(
    r'Definition\s+([A-Za-z_][A-Za-z_0-9]*)\s*:\s*Z\s*:=\s*(.+?)\.(?![A-Za-z_0-9])', re.S)


# [(only parsing)] is how most of the tree declares its aliases, and without
# the modifier group here the whole file goes UNRESOLVABLE -- 31 files,
# including every create/namex/kfork/kexec proof, were invisible to this tool.
NOTATION_RE = re.compile(
    r'Notation\s+([A-Za-z_][A-Za-z_0-9]*)\s*:=\s*(KernelSyms\.[A-Za-z_][A-Za-z_0-9]*)'
    r'\s*(?:\([^)]*\)\s*)?\.')


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


# width of the AST immediate each leaf family carries
KIND_WIDTH = {'JAL21': 21, 'B13': 13, 'U20': 20, 'I12': 12, 'S12': 12,
              'CJ11': 11, 'CB8': 8}

PC_RE = re.compile(r'mword_of_int\s*\(\s*(?:KernelSyms\.)?([A-Za-z_][A-Za-z_0-9]*)\s*\+\s*(0x[0-9a-fA-F]+|\d+)\s*\)')
# The width ascription is OPTIONAL: plenty of proof sites write a bare
# [mword_of_int 2256].  When it is absent there is no width to cross-check, so
# such a site is only ever rewritten under --old-image, whose "this literal IS
# the pre-bump immediate at this pc" test is the stronger guard anyway.
IMM_RE = re.compile(r'mword_of_int\s+(0x[0-9a-fA-F]+|\d+)(?:\s*:\s*mword\s+(\d+))?')


def proof_files(iris):
    """Every hand-written .v -- the auto-generated Code<F>.v are gen_code.py's.

    Keyed by CONTENT (the generator's header marker), never by filename: a
    restated relocation can live in any hand-written file, and a name-keyed
    whitelist silently drops one the moment a definition is relocated to its
    proper altitude ([ProcGeom.mycpu_ret], whose auipc/addi pair moves on
    every upstream bump, is exactly that case).
    """
    out = []
    for p in sorted(glob.glob(os.path.join(iris, '*.v'))):
        with open(p, encoding='utf8', errors='replace') as f:
            if 'AUTO-GENERATED' in f.read(2000):
                continue
        out.append(p)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--kernel-rocq', default='kernel-rocq')
    ap.add_argument('--update', action='store_true')
    ap.add_argument('--window', type=int, default=1500,
                    help='chars after a pc in which its immediate must appear. '
                         'Wide on purpose: a relocation is often restated in an '
                         'assert several statements below its pc.  Safe only '
                         'because --old-image refuses any literal that is not '
                         'the pre-bump immediate at that pc.')
    ap.add_argument('--old-image', default=None,
                    help='pre-bump KernelInstrs.v/KernelSyms.v dir: a literal is '
                         'only rewritten when it IS the old immediate at that pc')
    args = ap.parse_args()

    syms = load_syms(os.path.join(args.kernel_rocq, 'KernelSyms.v'))
    by = load_bytes(os.path.join(args.kernel_rocq, 'KernelInstrs.v'))

    # Aliases MUST be resolved per file.  The same short name means different
    # functions in different files -- [CI] is clockintr in CodeClockintr.v,
    # consoleinit in CodeConsoleinit.v and copyin in CodeCopyin.v -- so a
    # global merge silently resolves a pc to the WRONG function and would
    # write a wrong immediate, which compiles and proves the wrong thing.
    file_nots = {}
    for q in sorted(glob.glob(os.path.join(args.iris, '*.v'))):
        file_nots[os.path.basename(q)[:-2]] = file_notations(
            strip_comments(open(q).read()), syms)

    def aliases_for(path):
        body = strip_comments(open(path).read())
        out = {}
        # what this file imports, then its own -- its own wins
        for mod in re.findall(r'Require\s+(?:Import|Export)?\s*([A-Za-z_][A-Za-z_0-9. ]*)\.', body):
            for name in mod.split():
                out.update(file_nots.get(name.strip(), {}))
        out.update(file_nots.get(os.path.basename(path)[:-2], {}))
        return out

    old_by = old_syms = None
    if args.old_image:
        old_by = load_bytes(os.path.join(args.old_image, 'OldKernelInstrs.v'))
        old_syms = load_syms(os.path.join(args.old_image, 'OldKernelSyms.v'))

    def old_imm_at(base, off, width, plus4=False):
        """The immediate the PRE-BUMP image had at this pc, if resolvable."""
        if old_by is None:
            return None
        sym = None
        for nm, v in nots.items():
            if nm == base:
                sym = next((k for k, a in syms.items() if a == v), None)
        if sym is None and base in syms:
            sym = base
        if sym is None or sym not in old_syms:
            return None
        a = old_syms[sym] + off + (4 if plus4 else 0)
        w = word_at(old_by, a, width // 8)
        if w is None:
            return None
        r = imm_from_word(w, width)
        return r[1] if r else None

    n_ok = n_bad = n_pc = 0
    per_file = {}
    all_pc = {}
    n_amb = 0
    for p in proof_files(args.iris):
        raw = open(p).read()
        text = strip_comments(raw)
        nots = aliases_for(p)
        edits = []
        pcs = []
        for m in PC_RE.finditer(text):
            base, off = m.group(1), int(m.group(2), 0)
            if base in nots:
                addr = nots[base] + off
            elif base in syms:
                addr = syms[base] + off
            else:
                n_amb += 1
                continue
            n_pc += 1
            pcs.append(m.start())
            w = word_at(by, addr, 2)
            if w is None:
                continue
            width = 32 if (w & 3) == 3 else 16
            if width == 32:
                w = word_at(by, addr, 4)
                if w is None:
                    continue
            fw = R.decode_base(w) if width == 32 else None
            got = imm_from_word(w, width)
            if got is None:
                continue
            kind, want = got
            pair = False
            seg = text[m.end():m.end() + args.window]

            # An auipc+addi PAIR is often restated as a closed form anchored on
            # the AUIPC's pc -- `add_vec (pc) (auipc_off hi) + sign_extend' 64
            # (mword_of_int lo : mword 12)` -- so the 12-bit literal in the
            # window belongs to the instruction at pc+4, not to this one.
            # Without this the site is skipped (widths disagree) and the stale
            # lo-12 survives: ProofAllocpid's pid_lock relocation, ProofSched's
            # and ProofScheduler's, ProcGeom's mycpu_ret.
            if kind == 'U20' and 'auipc_off' in seg:
                nxt = word_at(by, addr + 4, 4)
                if nxt is not None:
                    g2 = imm_from_word(nxt, 32)
                    # the low-12 may live in an ADDI *or* in a STORE's
                    # immediate -- `auipc a5,hi` + `sw a4,lo(a5)` relocates
                    # exactly the same way
                    if g2 and g2[0] in ('I12', 'S12'):
                        kind, want = g2
                        pair = True
            oldv = old_imm_at(base, off, 32 if width == 32 else 16, pair)
            # Without the width ascription a bare [mword_of_int 11] is usually a
            # REGISTER index, so taking the first match finds the wrong thing.
            # Pick the candidate that IS the pre-bump immediate at this pc; fall
            # back to the first correctly-ascribed one.
            im = None
            if oldv is not None:
                for c in IMM_RE.finditer(seg):
                    if int(c.group(1), 0) == oldv and (
                            c.group(2) is None or int(c.group(2)) == KIND_WIDTH.get(kind)):
                        im = c
                        break
            if im is None:
                for c in IMM_RE.finditer(seg):
                    if c.group(2) and int(c.group(2)) == KIND_WIDTH.get(kind):
                        im = c
                        break
            if not im:
                continue
            have = int(im.group(1), 0)
            hw = int(im.group(2)) if im.group(2) else None
            if hw is not None and hw != KIND_WIDTH.get(kind):
                continue
            if hw is None and old_by is None:
                continue
            if have == want:
                n_ok += 1
                continue
            # Only rewrite when the literal IS what the pre-bump image had at
            # this pc.  Without that the 260-char window sometimes grabs an
            # unrelated same-width literal (a struct offset), and "fixing" it
            # writes a wrong immediate -- which compiles.
            if old_by is not None and oldv != have:
                continue
            n_bad += 1
            a = m.end() + im.start(1)
            b = m.end() + im.end(1)
            edits.append((a, b, have, want, kind, base, off))
        all_pc[p] = pcs
        if edits:
            per_file[p] = edits

    print("pc-anchored sites seen : %d  (unresolvable alias: %d)" % (n_pc, n_amb))
    print("immediates AGREE       : %d" % n_ok)
    print("immediates STALE       : %d in %d file(s)" % (n_bad, len(per_file)))
    for p, es in sorted(per_file.items()):
        print("  %-28s %s" % (os.path.basename(p),
                              ', '.join('%s+0x%x %s %d->%d' % (b, o, k, h, w)
                                        for _, _, h, w, k, b, o in es[:3])))
    if not args.update:
        return 1 if n_bad else 0

    total = 0
    for p, es in per_file.items():
        raw = open(p).read()
        # An instruction's immediate is echoed by the register-map and address
        # assertions that FOLLOW its leaf application, so each replacement is
        # scoped to the span from its own pc anchor to the NEXT one.  A
        # file-wide replace is wrong and does not even converge: the same value
        # is a different instruction's immediate elsewhere in the file, and
        # successive passes flip it back and forth.
        anchors = sorted(all_pc[p])
        for a, b, have, want, kind, base, off in sorted(es, key=lambda e: -e[0]):
            nxt = next((x for x in anchors if x > a), len(raw))
            wd = KIND_WIDTH[kind]
            # The ANCHOR literal is [a,b) and is replaced outright; the echoes
            # are rewritten in the block that FOLLOWS it.  Substituting over a
            # block that still contains the anchor and then splicing by the
            # anchor's OLD length corrupts the source whenever the new literal
            # has a different width -- it ate the [: mword 12] ascription of a
            # 4094 -> 14 site and spliced 998 -> 1014 into "101444444", both of
            # which are well-formed enough to reach the build as a mystery.
            blk = raw[b:nxt]
            blk = re.sub(r'mword_of_int(\s+)(?:%d|0x%x)\b((?:\s*:\s*mword\s+%d)?)' % (have, have, wd),
                         lambda m: 'mword_of_int%s%d%s' % (m.group(1), want, m.group(2)), blk)
            head = ('0x%x' % want) if raw[a:b].startswith('0x') else str(want)
            total += 1
            raw = raw[:a] + head + blk + raw[nxt:]
        open(p, 'w').write(raw)
    print("rewrote %d site(s) across %d file(s)" % (total, len(per_file)))
    return 0


if __name__ == '__main__':
    sys.exit(main())

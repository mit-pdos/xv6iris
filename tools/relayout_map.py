#!/usr/bin/env python3
"""Re-point a hand-written proof at the new image after a kernel relayout.

An image relayout re-encodes every pc-relative immediate (jal/branch targets,
auipc/addi data pairs), so a proof that SPELLS one -- and every whole-function
proof spells each of them, typically twice per call site -- is now wrong.  The
generated `iris/Code<F>.v` files are the ground truth: they are regenerated
from the dump by tools/gen_code.py, so their git diff IS the map.

    map   : print the per-offset old -> new immediate changes for a Code file
    apply : rewrite a proof file with that map

`apply` works the way durable-notes.md's playbook prescribes -- keyed by
LEMMA OFFSET rather than by value.  It scans the proof linearly, tracking the
most recent `KernelSyms.<sym> + 0x<off>` anchor, and inside each anchored
region rewrites only the immediates that moved AT THAT OFFSET OR AT OFFSET+4.
That is what makes it safe where a global value substitution is not: the same
number means different things at different offsets, adjacent call sites
collide, and some proofs write the immediate in hex and others in decimal.

WHAT THE MAP CANNOT SEE, and the one way it could corrupt a proof: it compares
old against new AT THE SAME OFFSET.  That is exact only while the two images
agree on where instructions START.  As soon as a function gains or loses an
instruction, every offset above that point names a DIFFERENT instruction in
the two images, and comparing them is comparing two unrelated things.  Usually
that shows up as a shape change and is reported; but when the two unrelated
instructions happen to share a shape, the difference looks exactly like an
ordinary moved immediate, and substituting it splices a stranger's immediate
into the proof.  It still typechecks as an immediate, so nothing downstream
catches it.  (Real case: on CodeKexec.v phase C gained instructions at +0x23c,
and the map proposed rewriting phase B's tail at +0x318 -- `ld s6,480(sp)` /
`j +0x64` -- with phase D's `ld s11,440(sp)` / `j +0x72`.  Both `ldsp`+`cj`.)

So once a symbol has ANY reshaped offset, every change at or above the LOWEST
one is quarantined into the reshape report as UNTRUSTED, and `apply` cannot
reach it; below the first reshape the offsets still line up and the changes
stay usable.  This also closes a narrower hole: an offset reported as
REGISTERS REALLOCATED used to have its IMMEDIATES substituted anyway.

THE +4 IS NOT SLOP, it is the auipc/I-type pair.  A "reloc lemma" states the
address an `auipc`/`addi` pair computes, so it ANCHORS on the auipc
(`KernelSyms.f + 0x0c`) while spelling the immediate of the addi at `+0x10`.
Keying strictly on the anchor skipped every one of those, silently -- three
separate relayout batches caught them only via `residue` and fixed ~25 by
hand.  Substitution is single-pass for the same reason: with two offsets'
maps merged, sequential replacement could CHAIN (100->200 then 200->300
yielding 100->300).  A literal the two maps disagree about is left alone for
`residue` to report as AMBIGUOUS.

Usage:
    relayout_map.py map   CodeBalloc.v
    relayout_map.py apply CodeBalloc.v ProofBalloc.v [--write]
    relayout_map.py residue CodeBalloc.v ProofBalloc.v   (MANDATORY post-step)

Without --write, `apply` prints a unified diff and changes nothing.
"""
import re, subprocess, sys, difflib, os

# DERIVED FROM THIS SCRIPT'S OWN LOCATION, not hard-coded: the tool is checked
# in and every agent runs it from a different worktree, so an absolute path
# here fails with a FileNotFoundError naming somebody else's checkout.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IRIS = os.path.join(ROOT, 'iris')

# "Lemma bai_02c : kernel_text -* instr (mword_of_int (KernelSyms.balloc + 0x2c)
#  : mword 64) false (<AST>)."
LEMMA_RE = re.compile(
    r'Lemma\s+(\w+)\s*:\s*\n?\s*kernel_text\s*-∗\s*instr\s*'
    r'\(mword_of_int\s*\(?KernelSyms\.(\w+)(?:\s*\+\s*(0x[0-9a-fA-F]+))?\)?'
    r'\s*:\s*mword 64\)\s+(true|false)\s+(.*?)\.\s*\n\s*Proof\.',
    re.S)
NUM_RE = re.compile(r'\b(0x[0-9a-fA-F]+|\d+)\b')

# A number inside [Regidx (mword_of_int N)] is a REGISTER FIELD, not an
# immediate.  It moves only when gcc re-did register allocation -- i.e. only
# when the function's own code genuinely changed -- and substituting it in a
# proof is ACTIVELY WRONG, because the same literal appears in side conditions
# like [r <> mword_of_int 15] that have nothing to do with this instruction.
# (Caught on ProofFetchaddr.v, where copyin's new second argument shifted five
# registers and offset +0x1e had 14 -> 15 and 15 -> 11 colliding.)  So register
# fields are tracked separately and reported as a reallocation warning instead.
REGIDX_RE = re.compile(r'(?:Regidx|creg2reg_idx)\s*\(\s*mword_of_int\s+(0x[0-9a-fA-F]+|\d+)')

# A bitvector WIDTH is never an instruction immediate, and it shows up in
# several positions: `(mword_of_int 12 : mword 12)` carries the number twice,
# and `sign_extend' 64 (...)` / `zero_extend' 12 (...)` / `ones 0` carry it as
# a leading argument.  Rewriting any of them is silent corruption -- see the
# note at the substitution site.
WIDTH_RE = re.compile(
    r'\bmword\s+(\d+)'
    r"|\b(?:sign_extend|zero_extend|truncate|truncateLSB)'?\s+(\d+)"
    r"|\b(?:ones|zeros)'?\s+(\d+)")


def _num_kinds(ast):
    """[(value, is_register_field)] for every number in [ast], in order."""
    reg = [m.span(1) for m in REGIDX_RE.finditer(ast)]
    return [(int(m.group(1), 0),
             any(a <= m.span(1)[0] and m.span(1)[1] <= b for a, b in reg))
            for m in NUM_RE.finditer(ast)]


def parse_code(text):
    """{(symbol, offset) -> (ast_text, [numbers])}, offset 0 for the bare symbol.

    KEYED BY SYMBOL AS WELL AS OFFSET.  Five Code files cover more than one
    function (CodeSleeplock has four, CodeKalloc/CodeEitherCopy/CodeBpin/
    CodeHolding two each); keying by offset alone silently let the second
    function's lemmas overwrite the first's at every shared offset, so the map
    came out both short and WRONG -- and `apply` would then have written one
    function's immediates into the other's regions.
    """
    out = {}
    for m in LEMMA_RE.finditer(text):
        off = int(m.group(3), 16) if m.group(3) else 0
        ast = ' '.join(m.group(5).split())
        out[(m.group(2), off)] = (ast, _num_kinds(ast))
    return out


def read_old(path):
    rel = os.path.relpath(os.path.join(IRIS, path), ROOT)
    return subprocess.run(['git', '-C', ROOT, 'show', f'HEAD:{rel}'],
                          capture_output=True, text=True).stdout


def build_map(code_file):
    """{(sym, offset) -> [(old, new), ...]} plus a list of shape changes.

    Register-field changes never enter the substitution map: they are appended
    to `reshaped` as a REGISTERS REALLOCATED note, because a moved register
    means gcc recompiled the function and the proof needs a human, not a sed.
    """
    old = parse_code(read_old(code_file))
    new = parse_code(open(os.path.join(IRIS, code_file)).read())
    changes, reshaped = {}, []
    for key, (nast, nnums) in sorted(new.items()):
        if key not in old:
            reshaped.append((key, '(new)', nast))
            continue
        oast, onums = old[key]
        if len(onums) != len(nnums) or NUM_RE.sub('#', oast) != NUM_RE.sub('#', nast):
            reshaped.append((key, oast, nast))
            continue
        pairs, regs = [], []
        for (o, oreg), (n, nreg) in zip(onums, nnums):
            if o == n:
                continue
            (regs if (oreg or nreg) else pairs).append((o, n))
        if regs:
            reshaped.append((key, 'REGISTERS REALLOCATED: '
                             + ', '.join(f'x{o} -> x{n}' for o, n in regs), nast))
        if pairs:
            changes[key] = pairs

    # OFFSETS ABOVE A SHAPE CHANGE NAME A DIFFERENT INSTRUCTION, so the
    # old-vs-new comparison at that offset is comparing two unrelated things.
    # Where the two happen to share a SHAPE, the diff looks like an ordinary
    # moved immediate and would be substituted -- silently splicing a later
    # function's instruction into an earlier one's proof.  This is not
    # hypothetical: on CodeKexec.v, phase C gained instructions at +0x23c, and
    # the map then proposed rewriting phase B's tail at +0x318 (`ld s6,480(sp)`
    # / `j +0x64`) with phase D's `ld s11,440(sp)` / `j +0x72`.  Both are
    # `ldsp`+`cj`, so nothing else would have caught it.
    #
    # So: once a symbol has ANY reshaped offset, every change at or above the
    # LOWEST one is untrustworthy.  Quarantine them into `reshaped`, where
    # `map` prints them and `apply` cannot reach them.  Below the first
    # reshape the offsets still line up, so those changes stay usable.
    first_reshape = {}
    for (sym, off), _, _ in reshaped:
        if sym not in first_reshape or off < first_reshape[sym]:
            first_reshape[sym] = off
    for key in sorted(changes):
        sym, off = key
        if sym in first_reshape and off >= first_reshape[sym]:
            reshaped.append((key, 'UNTRUSTED: at/above this symbol\'s first shape '
                             f'change (+0x{first_reshape[sym]:x}), so this offset no '
                             'longer names the same instruction -- '
                             + ', '.join(f'{o} -> {n}' for o, n in changes[key]),
                             new[key][0]))
            del changes[key]
    return changes, reshaped


def symbols(code_file):
    """Every function symbol this Code file covers, in file order."""
    seen = []
    for m in LEMMA_RE.finditer(open(os.path.join(IRIS, code_file)).read()):
        if m.group(2) not in seen:
            seen.append(m.group(2))
    return seen


ANCHOR_RE = re.compile(r'KernelSyms\.(\w+)\s*\+\s*(0x[0-9a-fA-F]+|\d+)')
BARE_RE = re.compile(r'KernelSyms\.(\w+)')


def find_aliases(text, sym):
    """Local names standing for the symbol, e.g. `Let SE := KernelSyms.sys_exit`.

    A proof that abbreviates the symbol this way anchors on the ALIAS, not on
    `KernelSyms.<sym>`, so without this the scan never re-anchors and `apply`
    reports a truthful-looking "0 substitutions" while leaving the file broken.
    """
    return set(re.findall(r'(\w+)\s*:=\s*KernelSyms\.' + re.escape(sym) + r'\b', text)) - {sym}


def apply_map(proof_file, changes, syms, aliases=()):
    """Linear anchored rewrite.  Returns (new_text, [(line, old, new)]).

    `changes` is keyed by (symbol, offset); the scan tracks WHICH symbol the
    current anchor named, so a Code file covering several functions rewrites
    each one's region with its own map.
    """
    path = os.path.join(IRIS, proof_file)
    text = open(path).read()
    alias_of = {}
    for s in syms:
        for a in {s} | set(find_aliases(text, s)):
            alias_of[a] = s
    # `aliases` may be a plain sequence (every name stands for the file's first
    # symbol -- the command-line form) or a {alias: symbol} mapping, which is
    # what a caller resolving aliases across a proof family must pass: a Code
    # file covering several functions would otherwise attribute the second
    # function's alias to the first's map.
    for a in aliases:
        alias_of.setdefault(a, aliases[a] if isinstance(aliases, dict) else syms[0])
    names = sorted(alias_of, key=len, reverse=True)
    anchor_re = re.compile(r'(?:KernelSyms\.)?\b(' + '|'.join(map(re.escape, names))
                           + r')\b\s*\+\s*(0x[0-9a-fA-F]+|\d+)')
    bare_re = re.compile(r'(?:KernelSyms\.)?\b(' + '|'.join(map(re.escape, names)) + r')\b')
    lines = text.split('\n')
    cur, out, log = None, [], []
    for i, line in enumerate(lines):
        # An OFFSET is not an immediate.  `KernelSyms.argraw + 0x18` names a pc;
        # rewriting the 0x18 because 24 happens to be a moved immediate at the
        # anchor is the tool's one real footgun, so blank those spans out before
        # substituting and splice them back afterwards.
        # A BITVECTOR WIDTH IS NOT AN IMMEDIATE EITHER.  `(mword_of_int 12 :
        # mword 12)` carries the same number twice, and only the FIRST one is
        # the instruction's immediate; the second is the type.  Rewriting both
        # (procdump+0x2e moved 12 -> 4088) produced `mword_of_int 4088 :
        # mword 4088` -- a 4088-BIT WORD.  That one happened to fail loudly,
        # but a width that stays plausible would not: `mword 12` -> `mword 20`
        # is a well-typed lie.  Same rule as the register fields: freeze them.
        spans = [m.span(2) for m in anchor_re.finditer(line)] \
              + [m.span(g) for m in WIDTH_RE.finditer(line)
                 for g in (1, 2, 3) if m.group(g) is not None]
        spans.sort()
        # re-anchor on the LAST symbol reference in the line
        anchors = [((alias_of[m.group(1)], int(m.group(2), 0)), m.start())
                   for m in anchor_re.finditer(line)]
        bares = [((alias_of[m.group(1)], 0), m.start()) for m in bare_re.finditer(line)
                 if not line[m.end():m.end() + 3].strip().startswith('+')]
        if anchors or bares:
            cur = max(anchors + bares, key=lambda t: t[1])[0]
        # THE ANCHOR IS A WINDOW, NOT A POINT.  A "reloc lemma" anchors on the
        # AUIPC (`KernelSyms.f + 0x0c`) but spells the immediate of the I-type
        # that COMPLETES the pair, which lives 4 bytes later -- so keying
        # strictly on the anchor skipped every one of them, silently.  `residue`
        # caught them as stale, but only after a human went looking: three
        # separate batches hit this and fixed 25-odd literals by hand.
        keys = [cur] if cur is not None else []
        if cur is not None:
            keys.append((cur[0], cur[1] + 4))
        pairs = [c for k in keys for c in changes.get(k, ())]
        if pairs:
            frozen = [line[a:b] for a, b in spans]
            new_line, off = [], 0
            for k, (a, b) in enumerate(spans):
                new_line.append(line[off:a]); new_line.append(f'\x00{k}\x00'); off = b
            new_line.append(line[off:])
            new_line = ''.join(new_line)
            # ONE PASS, so a literal is never re-examined after being written.
            # Sequential per-pair substitution could CHAIN (100->200 followed by
            # 200->300 yields 100->300); with two maps merged that stopped being
            # hypothetical.  A literal that two entries disagree about is left
            # alone -- `residue` reports it as AMBIGUOUS for a human to settle.
            repl, bad = {}, set()
            for oldv, newv in pairs:
                for lit, rep in ((str(oldv), str(newv)), (hex(oldv), hex(newv))):
                    if repl.get(lit, rep) != rep:
                        bad.add(lit)
                    repl[lit] = rep
            for lit in bad:
                repl.pop(lit, None)
            if repl:
                # SUBSTITUTE ONLY THE OPERAND OF [mword_of_int], never a bare
                # number.  Every immediate a proof spells goes through it --
                # `mword_of_int 1378`, `caddi16sp_imm (mword_of_int 61 : ...)`,
                # `auipc_off (mword_of_int 6 : ...)` -- while an anchored line
                # is full of numbers that are NOT immediates and must not move:
                # frame arithmetic (`K - 4`, and a map entry 4 -> 4076 really
                # did turn it into `K - 4076`), bitvector widths (`mword 12`,
                # `sign_extend' 64`), loop counts, `%nat` indices.  Freezing
                # each such context as it was discovered was whack-a-mole; this
                # is the closed form of the same rule.
                MOI = re.compile(r'(mword_of_int\s+)(0x[0-9a-fA-F]+|\d+)')

                def _sub(m, _i=i):
                    lit = m.group(2)
                    if lit not in repl:
                        return m.group(0)
                    log.append((_i + 1, lit, repl[lit]))
                    return m.group(1) + repl[lit]

                new_line = MOI.sub(_sub, new_line)
            for k, s in enumerate(frozen):
                new_line = new_line.replace(f'\x00{k}\x00', s)
            line = new_line
        out.append(line)
    return '\n'.join(out), log


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 1
    cmd, code_file = sys.argv[1], sys.argv[2]
    changes, reshaped = build_map(code_file)
    if cmd == 'map':
        for (sym, off), pairs in sorted(changes.items()):
            print(f'  {sym}+0x{off:x}: ' + ', '.join(f'{o} -> {n}' for o, n in pairs))
        for (sym, off), oast, nast in reshaped:
            print(f'  !! {sym}+0x{off:x} SHAPE CHANGED\n     old: {oast}\n     new: {nast}')
        print(f'({len(changes)} offsets moved, {len(reshaped)} reshaped, '
              f'symbols: {" ".join(symbols(code_file))})')
        return 0
    if cmd in ('apply', 'residue'):
        proof_file = sys.argv[3]
        syms = symbols(code_file)
        aliases = [a for a in sys.argv[4:] if not a.startswith("--")]
        if cmd == 'residue':
            # THE MANDATORY POST-STEP.  `apply` only rewrites inside an anchored
            # region, and a proof states an immediate in places the anchor does
            # not reach -- a companion `assert (Haddr : ... = ...)` a few lines
            # down, or an addi whose region the proof keys at the paired AUIPC's
            # offset.  This reports every OLD value from the map that still
            # appears anywhere in the file, so a silent miss cannot pass for a
            # clean run.  Some hits are legitimate (a value that means something
            # else); each needs an eye, not a sed.
            text = open(os.path.join(IRIS, proof_file)).read()
            stale = {o for pairs in changes.values() for o, _ in pairs}
            new = {n for pairs in changes.values() for _, n in pairs}
            hits, amb = 0, 0
            for i, line in enumerate(text.split('\n'), 1):
                for v in sorted(stale):
                    for lit in (str(v), hex(v)):
                        if re.search(r'(?<![\w.])' + re.escape(lit) + r'(?![\w])', line):
                            # A value that is ALSO a new value at some other
                            # offset cannot be judged from the number alone --
                            # reporting it anyway is what stops a real miss from
                            # being masked (it happened: eight reloc lemmas in
                            # ProofEndOp.v).  Reported separately because the
                            # benign case is the common one.
                            tag = 'AMBIGUOUS' if v in new else 'stale'
                            print(f'  {proof_file}:{i}: {tag} {lit}  |  {line.strip()[:110]}')
                            if v in new:
                                amb += 1
                            else:
                                hits += 1
            print(f'({hits} residual pre-relayout immediates, {amb} ambiguous '
                  f'-- a value that is also a NEW value elsewhere, so only an '
                  f'eye can tell)')
            return 0
        if reshaped:
            print(f'WARNING: {len(reshaped)} offsets changed SHAPE in {code_file}; '
                  'those need a human.', file=sys.stderr)
        text, log = apply_map(proof_file, changes, syms, aliases)
        path = os.path.join(IRIS, proof_file)
        old = open(path).read()
        if '--write' in sys.argv:
            open(path, 'w').write(text)
            print(f'{proof_file}: {len(log)} substitutions')
        else:
            sys.stdout.writelines(difflib.unified_diff(
                old.split('\n'), text.split('\n'), proof_file, proof_file + '.new',
                lineterm='', n=1))
            print(f'\n({len(log)} substitutions)')
        return 0
    print(__doc__)
    return 1


if __name__ == '__main__':
    sys.exit(main())

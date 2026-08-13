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
region rewrites only the immediates that moved AT THAT OFFSET.  That is what
makes it safe where a global value substitution is not: the same number means
different things at different offsets, adjacent call sites collide, and some
proofs write the immediate in hex and others in decimal.

Usage:
    relayout_map.py map   CodeBalloc.v
    relayout_map.py apply CodeBalloc.v ProofBalloc.v [--write]
    relayout_map.py residue CodeBalloc.v ProofBalloc.v   (MANDATORY post-step)

Without --write, `apply` prints a unified diff and changes nothing.
"""
import re, subprocess, sys, difflib, os

# The repo root, and the git revision the "old" (pre-relayout) Code files are
# read from.  Both are overridable, because a relayout is not always measured
# against HEAD: during a MERGE the pre-bump generation lives in the index
# (RELAYOUT_OLD_REV=''), and a two-step reconciliation needs the merge base.
ROOT = os.environ.get('RELAYOUT_ROOT',
                      os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OLD_REV = os.environ.get('RELAYOUT_OLD_REV', 'HEAD')
IRIS = os.path.join(ROOT, 'iris')

# "Lemma bai_02c : kernel_text -* instr (mword_of_int (KernelSyms.balloc + 0x2c)
#  : mword 64) false (<AST>)."
LEMMA_RE = re.compile(
    r'Lemma\s+(\w+)\s*:\s*\n?\s*kernel_text\s*-∗\s*instr\s*'
    r'\(mword_of_int\s*\(?KernelSyms\.(\w+)(?:\s*\+\s*(0x[0-9a-fA-F]+))?\)?'
    r'\s*:\s*mword 64\)\s+(true|false)\s+(.*?)\.\s*\n\s*Proof\.',
    re.S)
NUM_RE = re.compile(r'\b(0x[0-9a-fA-F]+|\d+)\b')


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
        out[(m.group(2), off)] = (ast, [int(n, 0) for n in NUM_RE.findall(ast)])
    return out


def read_old(path):
    rel = os.path.relpath(os.path.join(IRIS, path), ROOT)
    return subprocess.run(['git', '-C', ROOT, 'show', f'{OLD_REV}:{rel}'],
                          capture_output=True, text=True).stdout


def build_map(code_file):
    """{(sym, offset) -> [(old, new), ...]} plus a list of shape changes."""
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
        pairs = [(o, n) for o, n in zip(onums, nnums) if o != n]
        if pairs:
            changes[key] = pairs
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
    for a in aliases:
        alias_of.setdefault(a, syms[0])
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
        spans = [m.span(2) for m in anchor_re.finditer(line)]
        # re-anchor on the LAST symbol reference in the line
        anchors = [((alias_of[m.group(1)], int(m.group(2), 0)), m.start())
                   for m in anchor_re.finditer(line)]
        bares = [((alias_of[m.group(1)], 0), m.start()) for m in bare_re.finditer(line)
                 if not line[m.end():m.end() + 3].strip().startswith('+')]
        if anchors or bares:
            cur = max(anchors + bares, key=lambda t: t[1])[0]
        if cur is not None and cur in changes:
            frozen = [line[a:b] for a, b in spans]
            new_line, off = [], 0
            for k, (a, b) in enumerate(spans):
                new_line.append(line[off:a]); new_line.append(f'\x00{k}\x00'); off = b
            new_line.append(line[off:])
            new_line = ''.join(new_line)
            for oldv, newv in changes[cur]:
                for lit in (str(oldv), hex(oldv)):
                    pat = re.compile(r'(?<![\w.])' + re.escape(lit) + r'(?![\w])')
                    rep = str(newv) if lit == str(oldv) else hex(newv)
                    new_line, n = pat.subn(rep, new_line)
                    if n:
                        log.append((i + 1, lit, rep))
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

#!/usr/bin/env python3
"""relayout_batch.py -- drive relayout_map.py over the whole tree after a bump.

A pure-relayout bump re-encodes a pc-relative immediate in nearly every
function, so the per-file `relayout_map.py apply` has to run ~100 times against
~200 hand-written proof files.  This pairs them up automatically:

  * a Code<F>.v whose git diff carries immediate changes is a SOURCE;
  * every hand-written .v that ANCHORS on one of that file's symbols is a
    TARGET -- see targets_for for why "names the Code module" is the obvious
    rule and the wrong one;
  * aliases are collected from the target AND FROM THE FILES IT REQUIRES.
    relayout_map.find_aliases only reads the file it rewrites, but a proof
    split across `Proof<F>.v` / `Proof<F>Parts.v` declares the alias in the
    Parts file (`Notation FC := KernelSyms.fileclose`) and uses it in the
    other -- so the scan never re-anchors there and `apply` reports a
    truthful-looking "0 substitutions" over a file it left stale.  The alias
    table CANNOT be global: `KX` is `kexec` in one proof family and `kexit`
    in another, so it is resolved per target through that target's imports.

It refuses to run when any source reports a SHAPE change (`reshaped`), because
then the map is quarantined and a human has to classify the function first --
see claude-notes/xv6-bump-playbook.md §2.  `--allow-shape=Code<F>.v` records
that classification: the file stops blocking the run, and the batch prints the
targets that anchor on its symbols so you can see what the quarantined map
would reach.  Zero targets is the common case (the reshaped function has no
proof) and is the only case where the flag is free.

    relayout_batch.py            # dry run: what would change, per file
    relayout_batch.py --write    # do it
    relayout_batch.py --residue  # the MANDATORY post-step, over every pair
"""
import os, re, sys, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import relayout_map as R

GENERATED = ('Code', 'KernelDecode', 'KernelConsts')

REQUIRE_RE = re.compile(r'Require\s+(?:Import|Export)\s+([\w\s.]+?)\.\s*$', re.M)


ANY_ALIAS_RE = re.compile(r'(\w+)\s*:=\s*KernelSyms\.(\w+)\b')
BARE_SYM_RE = re.compile(r'KernelSyms\.(\w+)\b')

_TEXT = {}


def body(f):
    if f not in _TEXT:
        with open(os.path.join(R.IRIS, f)) as h:
            _TEXT[f] = h.read()
    return _TEXT[f]


def handwritten():
    return sorted(f for f in os.listdir(R.IRIS)
                  if f.endswith('.v') and not f.startswith(GENERATED))


def build_index():
    """(sym -> [files anchoring on it], file -> {alias: sym}), in ONE pass.

    Written as an inversion rather than the obvious per-pair scan for a reason:
    the natural phrasing ("for each Code file, for each candidate target, work
    out that target's aliases") re-reads every target AND its whole import list
    once per Code file -- ~170 x ~200 x ~30 file reads, which takes minutes and
    looks like a hang.  Read each file once, build the index, then every
    lookup is a dict hit.
    """
    files = handwritten()
    # each file's alias table, scoped to its own imports: `KX` is kexec in one
    # proof family and kexit in another, so a tree-wide table would rewrite one
    # function's region with the other's map.
    own = {f: dict(ANY_ALIAS_RE.findall(body(f))) for f in files}
    aliases, anchors = {}, {}
    for f in files:
        scope = [f] + [mod + '.v'
                       for m in REQUIRE_RE.finditer(body(f))
                       for mod in m.group(1).split()
                       if mod + '.v' in own]
        tbl = {}
        for g in scope:
            tbl.update(own[g])
        tbl = {a: s for a, s in tbl.items() if a != s}
        aliases[f] = tbl
        seen = set(BARE_SYM_RE.findall(body(f)))
        for a, s in tbl.items():
            if re.search(r'\b%s\b' % re.escape(a), body(f)):
                seen.add(s)
        for s in seen:
            anchors.setdefault(s, []).append(f)
    return anchors, aliases


def targets_for(anchors, syms):
    """Hand-written .v files that could spell one of `syms`' immediates.

    PAIRING IS BY ANCHOR, NOT BY IMPORT.  Matching files that name the Code
    module is the obvious rule and it is not sufficient: a `Proof<F>Parts.v`
    can state pure arithmetic lemmas ABOUT the immediates
    (`add_vec (PRR + 0x18) (auipc_off ...) (sign_extend' 64 2972) = uservec`)
    without needing any instruction fact, so it never Requires `Code<F>` and an
    import-keyed batch skips it in silence.  That is how
    ProofPrepareReturnParts.v survived a full batch + residue pass and failed
    the build instead.  So a file is a target when it anchors on the symbol at
    all -- via `KernelSyms.<sym>` or via an alias its own imports declare.
    """
    out = []
    for s in syms:
        for f in anchors.get(s, ()):
            if f not in out:
                out.append(f)
    return out


def main():
    write = '--write' in sys.argv
    residue = '--residue' in sys.argv
    allowed = {a.split('=', 1)[1] for a in sys.argv if a.startswith('--allow-shape=')}
    codes = sorted(f for f in os.listdir(R.IRIS)
                   if f.startswith('Code') and f.endswith('.v'))
    anchors, aliases = build_index()
    pairs, blocked = [], []
    for c in codes:
        changes, reshaped = R.build_map(c)
        if reshaped and c not in allowed:
            blocked.append((c, reshaped))
        if not changes:
            continue
        syms = R.symbols(c)
        for t in targets_for(anchors, syms):
            pairs.append((c, t, changes, syms))

    if blocked:
        print('SHAPE CHANGES -- classify these before any batch (playbook §2):')
        for c, rs in blocked:
            print(f'  {c}: {len(rs)} reshaped offsets')
        return 1

    for c in sorted(allowed):
        reach = sorted({t for s, t, _, _ in pairs if s == c})
        print(f'SHAPE CHANGE ACKNOWLEDGED {c}: quarantined map reaches '
              + (', '.join(reach) if reach else 'no hand-written file'))

    if residue:
        seen = set()
        for c, t, _, _ in pairs:
            if (c, t) in seen:
                continue
            seen.add((c, t))
            out = subprocess.run([sys.executable,
                                  os.path.join(os.path.dirname(__file__),
                                               'relayout_map.py'),
                                  'residue', c, t],
                                 capture_output=True, text=True).stdout.strip()
            if out and 'no residue' not in out.lower():
                print(f'--- {c} -> {t}\n{out}')
        return 0

    total = 0
    for c, t, changes, syms in pairs:
        new_text, log = R.apply_map(t, changes, syms, aliases[t])
        if not log:
            continue
        total += len(log)
        print(f'{c} -> {t}: {len(log)} substitutions')
        if write:
            open(os.path.join(R.IRIS, t), 'w').write(new_text)
    print(f'TOTAL {total} substitutions over {len({t for _, t, _, _ in pairs})} files'
          + ('' if write else '  (dry run -- pass --write)'))
    return 0


if __name__ == '__main__':
    sys.exit(main())

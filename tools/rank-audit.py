#!/usr/bin/env python3
"""Check every order premise against the ranks its callees demand.

A contract's bound must sit at the MINIMUM rank over its whole cone --
[locks_below_mono] raises but never lowers -- so a premise stated above any
callee's is unprovable.  Checks Spec bodies AND each local Lemma in the Proof
files, which is where the Spec-level check does not reach (kfork was stated at
allocproc's rank while its fd scan quietly called filedup)."""
import re, glob, sys

RANKS = re.search(r'Definition lock_ranks[^[]*\[(.*?)\n  \]\.',
                  open('LockRank.v').read(), re.S).group(1)
RANK = {m.group(1): int(m.group(2))
        for m in re.finditer(r'\("([^"]+)",\s*(\d+)\)', RANKS)}
NAME = {v: k for k, v in RANK.items()}

# rank of every premise-carrying body: Spec definitions AND the local Lemmas
# in the Proof files, because a Proof lemma routinely calls another file's
# local Lemma (kfork's arms call ProofKforkB5.kfk_b5) and the Spec-only map
# cannot see those.
spec = {}
for f in glob.glob('Proof*.v'):
    s2 = open(f).read().split('\n')
    hd = [(i, l) for i, l in enumerate(s2)
          if re.match(r'\s*(Local\s+)?(Lemma|Definition)\s+\w+', l)]
    for k, (i, l) in enumerate(hd):
        end = hd[k+1][0] if k+1 < len(hd) else len(s2)
        seg = '\n'.join(s2[i:end])
        r = re.search(r'locks_below\s+lks\s+"([^"]+)"(?:%string)?\s*->', seg)
        if r:
            nm = re.match(r'\s*(?:Local\s+)?(?:Lemma|Definition)\s+(\w+)', l).group(1)
            spec[nm] = RANK[r.group(1)]
for f in glob.glob('Spec*.v'):
    for p in re.split(r'(?m)^(?=\s*Definition\s+wp_\w+_body\b)', open(f).read()):
        m = re.match(r'\s*Definition\s+(wp_\w+)_body\b', p)
        if not m: continue
        seg = re.split(r'(?m)^\s*Module\s', p)[0]
        r = re.search(r'locks_below\s+lks\s+"([^"]+)"', seg)
        if r: spec[m.group(1)] = RANK[r.group(1)]

bad = 0
for f in sorted(glob.glob('Proof*.v')):
    s = open(f).read().split('\n')
    heads = [(i, l) for i, l in enumerate(s)
             if re.match(r'\s*(Local\s+)?(Lemma|Definition)\s+\w+', l)]
    for k, (i, l) in enumerate(heads):
        end = heads[k+1][0] if k+1 < len(heads) else len(s)
        body = '\n'.join(s[i:end])
        r = re.search(r'locks_below\s+lks\s+"([^"]+)"(?:%string)?\s*->', body)
        if not r: continue
        mine = RANK[r.group(1)]
        low = {c: spec[c] for c in spec
               if re.search(r'\.' + c + r'\b', body) and spec[c] < mine}
        if low:
            nm = re.match(r'\s*(?:Local\s+)?(?:Lemma|Definition)\s+(\w+)', l).group(1)
            print(f'{f}:{i+1}  {nm} @"{r.group(1)}"({mine}) '
                  f'-> "{NAME[min(low.values())]}"  (via {", ".join(sorted(low))})')
            bad += 1
# THE VACUITY TRIPWIRE.  This tool is redundant with the build -- Rocq will
# refuse a premise stated above a callee's regardless -- so its ONLY value is
# naming the fix, and a green light it did not earn is worse than no tool.
# It has already failed this way once: the [lks] refactor moved the premise
# from [locks_below lks (lock_rank "log")] to [locks_below lks "log"], every
# pattern below stopped matching, and it printed "clean" while checking
# nothing.  Re-derive the floor from the tree, not from a memory of it.
SEEN = sum(len(re.findall(r'locks_below\s+lks\s+"[^"]+"', open(f).read()))
           for f in glob.glob('Spec*.v') + glob.glob('Proof*.v'))
if SEEN < 100:
    print(f'PATTERNS HAVE DRIFTED: only {SEEN} order premises matched tree-wide '
          f'(expected hundreds).  This run checked nothing; fix the regexes '
          f'above before trusting it.', file=sys.stderr)
    sys.exit(2)
print(f'{bad} premise(s) stated above a callee' if bad else f'clean ({SEEN} premises checked)')
sys.exit(1 if bad else 0)

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

spec = {}
for f in glob.glob('Spec*.v'):
    for p in re.split(r'(?m)^(?=\s*Definition\s+wp_\w+_body\b)', open(f).read()):
        m = re.match(r'\s*Definition\s+(wp_\w+)_body\b', p)
        if not m: continue
        seg = re.split(r'(?m)^\s*Module\s', p)[0]
        r = re.search(r'locks_below\s+lks\s+\(lock_rank\s+"([^"]+)"', seg)
        if r: spec[m.group(1)] = RANK[r.group(1)]

bad = 0
for f in sorted(glob.glob('Proof*.v')):
    s = open(f).read().split('\n')
    heads = [(i, l) for i, l in enumerate(s)
             if re.match(r'\s*(Local\s+)?(Lemma|Definition)\s+\w+', l)]
    for k, (i, l) in enumerate(heads):
        end = heads[k+1][0] if k+1 < len(heads) else len(s)
        body = '\n'.join(s[i:end])
        r = re.search(r'locks_below\s+lks\s+\(lock_rank\s+"([^"]+)"\)\s*->', body)
        if not r: continue
        mine = RANK[r.group(1)]
        low = {c: spec[c] for c in spec
               if re.search(r'\.' + c + r'\b', body) and spec[c] < mine}
        if low:
            nm = re.match(r'\s*(?:Local\s+)?(?:Lemma|Definition)\s+(\w+)', l).group(1)
            print(f'{f}:{i+1}  {nm} @"{r.group(1)}"({mine}) '
                  f'-> "{NAME[min(low.values())]}"  (via {", ".join(sorted(low))})')
            bad += 1
print(f'{bad} premise(s) stated above a callee' if bad else 'clean')
sys.exit(1 if bad else 0)

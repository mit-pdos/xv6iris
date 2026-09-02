#!/usr/bin/env python3
"""The HONEST build measure (tso-cutover-endgame.md §1.2 / §7.2).

`make -k` leaves a failed file's stale .vo in place, so its dependents are
skipped as up to date and `ls *.vo` over-reports.  This script reads a
`make -k` log and the coq_makefile dependency file and prints:
  roots   = files whose compile printed an Error,
  blocked = their transitive dependents (via .CoqMakefile.d),
  green   = everything else.

usage: tools/cone.py <make-k.log> <.CoqMakefile.d> [--cone out.txt]
The dependency file lives on the VM: fetch it with
  run-on-gcp sh -c 'grep "^[A-Za-z0-9_]*\.vo " <tree>/iris/.CoqMakefile.d'
"""
import re, sys, collections
log, depf = sys.argv[1], sys.argv[2]
out = sys.argv[4] if len(sys.argv) > 4 and sys.argv[3] == '--cone' else None
L = [l.rstrip() for l in open(log)]
roots = {}
for i, l in enumerate(L):
    m = re.match(r'File "\./([A-Za-z0-9_]+)\.v", line (\d+)', l)
    if not m: continue
    for j in range(i + 1, min(i + 8, len(L))):
        if L[j].startswith('Error'):
            roots.setdefault(m.group(1), (m.group(2), L[j][:120])); break
        if L[j].startswith('File'): break
deps = collections.defaultdict(set)
for l in open(depf):
    if ':' not in l: continue
    tgt, rest = l.split(':', 1)
    if not tgt.split(): continue
    f = tgt.split()[0]
    if not f.endswith('.vo'): continue
    for d in rest.split():
        if d.endswith('.vo'): deps[f[:-3]].add(d[:-3])
rev = collections.defaultdict(set)
for f, ds in deps.items():
    for d in ds: rev[d].add(f)
def closure(rs):
    c, st = set(), list(rs)
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in c and y not in rs: c.add(y); st.append(y)
    return c
allf = set(deps) | {d for ds in deps.values() for d in ds}
cone = closure(set(roots))
print(f"total {len(allf)}  roots {len(roots)}  blocked {len(cone)}  green {len(allf) - len(roots) - len(cone)}")
for r, (ln, msg) in sorted(roots.items(), key=lambda kv: -len(closure({kv[0]}))):
    print(f"  {r}.v:{ln} [{len(closure({r}))} dependents] {msg}")
if out: open(out, 'w').write('\n'.join(sorted(cone)) + '\n')

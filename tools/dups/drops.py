#!/usr/bin/env python3
"""From build errors (file:line) in the applied tree, find the moved/renamed
groups responsible and append their gids to scratch/home_drop.txt.
usage: drops.py ERRFILE"""
import json, os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
app = [json.loads(l) for l in open(os.path.join(ROOT, 'scratch/home_applied.jsonl'))]
by_new = {a['new']: a for a in app}
short2 = {}
for a in app: short2.setdefault(a['new'].split('.')[-1], []).append(a)
drop = set()
unk = []
for line in open(sys.argv[1]):
    mo = re.match(r'error: (\S+\.lean):(\d+):\d+: (.*)', line)
    if not mo: continue
    f, ln, msg = mo.group(1), int(mo.group(2)), mo.group(3)
    L = open(os.path.join(ROOT, f), encoding='utf-8').read().split('\n')
    hit = None
    # 1. the error is inside a moved block: nearest decl header above
    for i in range(ln - 1, -1, -1):
        m2 = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s(:{\[]+)', L[i])
        if m2:
            nm = m2.group(1)
            if nm in short2:
                mod = f[:-5].replace('/', '.')
                cands = [a for a in short2[nm] if a['home'] == mod]
                if cands: hit = cands
            break
    # 2. the error line mentions a renamed name
    if not hit:
        txt = L[ln - 1] if ln - 1 < len(L) else ''
        near = '\n'.join(L[max(0, ln - 3): ln + 2])
        hit = [a for a in app if a['new'] in near or re.search(r'\b' + re.escape(a['new'].split('.')[-1]) + r'\b', near)]
    if hit:
        for a in hit: drop.add(a['gid'])
    else:
        unk.append(line.strip())
with open(os.path.join(ROOT, 'scratch/home_drop.txt'), 'a') as fo:
    for g in sorted(drop): fo.write(g + '\n')
print('dropped', len(drop)); print('\n'.join(unk[:30]))

"""For each residual candidate, its restricted-graph parents that are ported in Lean
(any parent, not only the BFS one).  Flags residuals with NO ported parent."""
import json, collections
S = 'scratch/cone/'
src = open('tools/cone_reaudit/restrict.py').read().split('edges = collections.defaultdict(list)')[0]
g = {}
exec(src, g)
excl_key = g['excl_key']
rows = {r['key']: r for r in json.load(open(S + 'audit.json'))}
RS = json.load(open(S + 'restrict.json'))
cat = json.load(open(S + 'cat.json'))
rev = collections.defaultdict(set)
for r in 'PSU':
    for line in open(S + 'edges_%s.txt' % r, errors='replace'):
        t = line.rstrip('\n').split(' ')
        if t[0] == 'E':
            rev[t[2]].add(t[1])


def ported(k):
    r = rows.get(k)
    return r is not None and r['lean'] in ('decl', 'doc', 'mention')


bad = []
for r in cat['None']:
    k = r['key']
    # BFS upward through unported live parents until ported ones
    seen = {k}
    frontier = [k]
    found = set()
    while frontier:
        nxt = []
        for x in frontier:
            for p in rev[x]:
                if p in seen or p not in RS or excl_key(p):
                    continue
                seen.add(p)
                if ported(p) or not p.startswith('xv6iris.'):
                    found.add(p)
                else:
                    nxt.append(p)
        frontier = nxt
    if not found:
        bad.append(k)
    else:
        print('%-45s <- %s' % (k.replace('xv6iris.', ''), ', '.join(sorted(x.replace('xv6iris.', '') for x in found))[:150]))
print('NO PORTED CONSUMER:', bad)

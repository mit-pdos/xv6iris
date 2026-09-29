"""Shortest root path to each given key in the RESTRICTED graph (no DU-dropped nodes)."""
import sys, collections, importlib.util
S = 'scratch/cone/'
src = open('tools/cone_reaudit/restrict.py').read().split('edges = collections.defaultdict(list)')[0]
g = {}
exec(src, g)
excl_key = g['excl_key']
edges = collections.defaultdict(list)
roots = {}
for r in 'PSU':
    for line in open(S + 'edges_%s.txt' % r, errors='replace'):
        t = line.rstrip('\n').split(' ')
        if t[0] == 'R':
            roots[r] = t[1]
        elif t[0] == 'E':
            edges[t[1]].append(t[2])
root = roots[sys.argv[1]]
par = {root: None}
q = collections.deque([root])
while q:
    k = q.popleft()
    for d in edges.get(k, ()):
        if d in par or excl_key(d):
            continue
        par[d] = k
        q.append(d)
for k in sys.argv[2:]:
    if k not in par:
        print(k, 'NOT REACHED (restricted)')
        continue
    p = []
    while k:
        p.append(k.replace('xv6iris.', ''))
        k = par[k]
    print(' → '.join(reversed(p)))

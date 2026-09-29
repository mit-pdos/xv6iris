"""Statement cone: from each root, the transparent definitions/inductives its
statement unfolds to (never through an opaque proof).  Any unported xv6iris
definition here could make a Lean top statement differ from Rocq's."""
import json, collections, os, re
S = 'scratch/cone/'
kind = {}
edges = collections.defaultdict(list)
roots = {}
for r in 'PSU':
    for line in open(S + 'edges_%s.txt' % r, errors='replace'):
        t = line.rstrip('\n').split(' ')
        if t[0] == 'R':
            roots[r] = t[1]
        elif t[0] == 'N':
            kind[t[1]] = t[2]
        elif t[0] == 'E':
            edges[t[1]].append(t[2])
rows = {r['key']: r for r in json.load(open(S + 'audit.json'))}
res = {}
for r, root in roots.items():
    seen = set()
    todo = [d for d in edges[root] if kind.get(d) in ('def', 'ind')]
    seen.update(todo)
    while todo:
        k = todo.pop()
        for d in edges.get(k, ()):
            if d not in seen and kind.get(d) in ('def', 'ind'):
                seen.add(d)
                todo.append(d)
    xs = sorted(k for k in seen if k.startswith('xv6iris.'))
    res[r] = xs
    un = [k for k in xs if rows.get(k, {}).get('lean') not in ('decl', 'doc')]
    print(r, root, 'statement cone xv6iris defs:', len(xs), 'unmatched:', len(un))
    byf = collections.Counter(k.split('.')[1] for k in un)
    print('   ', dict(byf.most_common(60)))
json.dump(res, open(S + 'stmt.json', 'w'))

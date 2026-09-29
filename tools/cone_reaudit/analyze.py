"""Kernel-term cone vs Lean ports.

Inputs (scratch/): edges_{P,S,U}.txt (depdump plugin), globidx.tsv, globreach.txt,
leanidx.json.  Output: scratch/audit.json + a text summary on stdout.
"""
import json, re, collections, sys, os

S = 'scratch/cone'
ROOTS = {'U': 'union_adequacy_closed', 'S': 'xv6_fs_adequacy_xv6Σ', 'P': 'UserProof.wp_user_exec_closed'}

# ---- kernel graph
nodes = {}            # key -> kind
edges = collections.defaultdict(list)
parent = {}           # (root,key) -> parent key   (BFS order of the dump = BFS)
reach = collections.defaultdict(set)
for r in 'PSU':
    p = os.path.join(S, 'edges_%s.txt' % r)
    if not os.path.exists(p):
        continue
    seen = set()
    for line in open(p, errors='replace'):
        t = line.rstrip('\n').split(' ')
        if t[0] == 'R':
            seen.add(t[1]); reach[r].add(t[1]); parent[(r, t[1])] = None
        elif t[0] == 'N':
            nodes[t[1]] = t[2] if len(t) > 2 else '?'
        elif t[0] == 'E':
            a, b = t[1], t[2]
            edges[a].append(b)
            if b not in seen:
                seen.add(b); reach[r].add(b); parent[(r, b)] = a

# ---- glob index
gkind = {}
gpos = {}
for line in open(os.path.join(S, 'globidx.tsv'), errors='replace'):
    mod, sp, name, kind, pos = line.rstrip('\n').split('\t')
    if kind in ('binder', 'var', 'not', 'sec'):
        continue
    key = '.'.join([mod] + ([] if sp == '<>' else [sp]) + [name])
    gkind.setdefault(key, kind)
    gpos.setdefault(key, pos)
greach = collections.defaultdict(set)
for line in open(os.path.join(S, 'globreach.txt')):
    r, k = line.split()
    greach[r].add(k)

lean = json.load(open(os.path.join(S, 'leanidx.json')))
ldecls, ldoc, lmention = lean['decls'], lean['doc'], lean['mention']


def norm(s):
    return re.sub(r"[_'«»]", '', s).lower()


AUTO = re.compile(r'(_obligation_\d+|_subproof\d*|_subterm\d*|_ind|_rec|_rect|_sind|_instance_\d+|_elim\d*|_obligations)$|^Build_|^_')


def split_key(k):
    parts = k.split('.')
    return parts[0] + '.' + parts[1], parts[2:-1], parts[-1]


def lean_status(name):
    n = norm(name)
    if n in ldecls:
        return 'decl', ldecls[n][:3]
    if name in ldoc:
        return 'doc', ldoc[name][:3]
    if name in lmention:
        return 'mention', lmention[name][:6]
    return None, []


def path_of(r, k, maxlen=12):
    out = []
    while k is not None and len(out) < 60:
        out.append(k)
        k = parent.get((r, k))
    out.reverse()
    short = [x.replace('xv6iris.', '') for x in out]
    if len(short) > maxlen:
        short = short[:3] + ['…'] + short[-(maxlen - 4):]
    return ' → '.join(short)


rows = []
for k, kind in nodes.items():
    if not k.startswith('xv6iris.'):
        continue
    mod, secs, name = split_key(k)
    rs = ''.join(r for r in 'PSU' if k in reach[r])
    gr = ''.join(r for r in 'PSU' if k in greach[r])
    st, where = lean_status(name)
    rows.append(dict(key=k, file=mod[len('xv6iris.'):], secs='.'.join(secs), name=name, kind=kind,
                     gkind=gkind.get(k, '?'), roots=rs, glob=gr, auto=bool(AUTO.search(name)),
                     lean=st, where=where,
                     path=path_of(rs[-1], k) if rs else ''))
json.dump(rows, open(os.path.join(S, 'audit.json'), 'w'), ensure_ascii=False)
c = collections.Counter((r['lean'], r['auto']) for r in rows)
print(len(rows), c)

import json, sys, collections
W = 'scratch/cone/'
rows = json.load(open(W + 'audit.json'))
RS = json.load(open(W + 'restrict.json'))
by = collections.defaultdict(list)
for r in rows:
    by[r['name']].append(r)
for n in sys.argv[1:]:
    rs = by.get(n)
    if not rs:
        print('%-30s UNREACHED' % n)
    for r in rs or []:
        print('%-30s %-18s roots=%-3s glob=%-3s live=%s lean=%s %s' % (n, r['file'], r['roots'], r['glob'], r['key'] in RS, r['lean'], r['where'][:1]))

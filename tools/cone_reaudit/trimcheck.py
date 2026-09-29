"""For every Lean header paragraph that calls declarations unreached / trimmed,
check each backticked name against the kernel-term reach and the Lean ports."""
import json, re, glob, collections, os, sys
W = './'
rows = json.load(open(W + 'scratch/cone/audit.json'))
RS = json.load(open(W + 'scratch/cone/restrict.json'))
byname = collections.defaultdict(list)
for r in rows:
    byname[r['name']].append(r)
L = json.load(open(W + 'scratch/cone/leanidx.json'))
KW = re.compile(r'unreached|UNREACHED|CONE TRIM|[Nn]ot reached|no declaration reached', re.S)
out = collections.defaultdict(list)
for f in sorted(glob.glob(W + 'Xv6/*.lean') + glob.glob(W + 'MachCSL/**/*.lean', recursive=True)):
    txt = open(f, errors='replace').read()
    m = re.match(r'\s*/-(?!-)(.*?)-/', txt, re.S)
    if not m:
        continue
    head = m.group(1)
    # paragraphs: split on blank lines or numbered items
    paras = re.split(r'\n\s*\n|\n(?=\d+\. |\* |## )', head)
    for p in paras:
        if not KW.search(p):
            continue
        for n in re.findall(r'`([A-Za-z_][A-Za-z0-9_\']*)`', p):
            rs = byname.get(n, [])
            if not rs:
                continue
            reached = [r for r in rs if 'U' in r['roots']]
            if not reached:
                continue
            r = reached[0]
            ported = r['lean'] in ('decl', 'doc')
            where = r['where'][:2] if ported else []
            live = r['key'] in RS
            out[os.path.relpath(f, W)].append((n, r['file'], 'glob' if 'U' in r['glob'] else 'KERNEL-ONLY',
                                               'live' if live else 'via-dropped', ported, where))
for f, xs in out.items():
    print('==', f)
    for x in xs:
        print('   %-30s %-16s %-11s %-11s ported=%s %s' % (x[0], x[1], x[2], x[3], x[4], ','.join(w.split(':')[0].split('/')[-1] + ':' + w.split(':')[1] for w in x[5])))

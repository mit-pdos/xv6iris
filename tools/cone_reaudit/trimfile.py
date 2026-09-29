"""Per Lean file: every backticked name in its trim paragraph(s), with kernel status."""
import json, re, collections, sys
W = './'
rows = json.load(open(W + 'scratch/cone/audit.json'))
RS = json.load(open(W + 'scratch/cone/restrict.json'))
L = json.load(open(W + 'scratch/cone/leanidx.json'))
byname = collections.defaultdict(list)
for r in rows:
    byname[r['name']].append(r)


def norm(s):
    return re.sub(r"[_'«»]", '', s).lower()


KW = re.compile(r'unreached|UNREACHED|CONE TRIM|[Nn]ot reached|no declaration reached|[Nn]ot ported')
for f in sys.argv[1:]:
    txt = open(W + f, errors='replace').read()
    m = re.match(r'\s*/-(?!-)(.*?)-/', txt, re.S)
    head = m.group(1)
    paras = re.split(r'\n\s*\n|\n(?=\d+\. |\* |## )', head)
    print('==', f)
    for p in paras:
        if not KW.search(p):
            continue
        names = re.findall(r'`([A-Za-z_][A-Za-z0-9_\']*)`', p)
        st = []
        for n in names:
            rs = byname.get(n, [])
            if not rs:
                # lean name or unknown or unreached entirely
                st.append('%s:UNREACHED' % n)
                continue
            r = rs[0]
            if r['lean'] in ('decl', 'doc'):
                where = r['where'][0].split('/')[-1]
                st.append('%s:PORTED[%s]' % (n, where))
            else:
                st.append('%s:REACHED-UNPORTED(%s%s)' % (n, 'live' if r['key'] in RS else 'via-dropped', ',K' if 'U' not in r['glob'] else ''))
        print('  PARA:', p.strip().split('\n')[0][:90])
        for s in st:
            print('     ', s)

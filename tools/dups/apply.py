#!/usr/bin/env python3
"""Apply auto-mergeable duplicate groups: keep one member, delete the others,
re-point their uses.  usage: apply.py [--dry] [--kind thm] [--skip NAME ...]
Writes scratch/applied.jsonl (one record per applied group) and
scratch/skipped.txt (reasons)."""
import json, os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze import load, closure, category, ROOT

args = sys.argv[1:]
dry = '--dry' in args
kind = args[args.index('--kind') + 1] if '--kind' in args else 'thm'
skipnames = set()
if '--skipfile' in args:
    skipnames = set(l.strip() for l in open(args[args.index('--skipfile') + 1]) if l.strip())

def modpath(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
_src = {}
def src(m):
    if m not in _src: _src[m] = open(modpath(m), encoding='utf-8').read().split('\n')
    return _src[m]
def slice_(mem):
    L = src(mem['mod']); return '\n'.join(L[mem['l0'] - 1: mem['l1']])

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|instance)\b', re.M)
IDENT = re.compile(r"^[A-Za-z_][\w'!?]*$")

def is_decl(mem):
    return bool(DECL.search(slice_(mem)))

def attrs(mem):
    return re.findall(r'@\[([^\]]*)\]', slice_(mem))

import functools
@functools.lru_cache(None)
def depth(m):
    from analyze import direct
    ds = [d for d in direct(m) if d.split('.')[0] in ('Xv6', 'MachCSL')]
    return 1 + max((depth(d) for d in ds), default=0)

def is_pl(mod):
    b = mod.split('.')[-1]
    return b.startswith('Proof') or b.startswith('Link')

def pick_keeper(g, allow_imports=True):
    mems = g['mems']
    cands = []
    for k in mems:
        ok = True; imps = set()
        for o in mems:
            if o is k: continue
            if o['mod'] == k['mod']:
                if o['l0'] < k['l0']: ok = False
                continue
            if k['priv']: ok = False; continue
            if k['mod'] in closure(o['mod']): continue
            if allow_imports and not is_pl(k['mod']) and o['mod'] not in closure(k['mod']) \
                    and depth(k['mod']) < depth(o['mod']):
                imps.add((o['mod'], k['mod']))
            else:
                ok = False
        if ok: cands.append((k, imps))
    if not cands: return None, None, 'no keeper'
    insts = [m for m in mems if m.get('inst')]
    if insts:
        ci = [c for c in cands if c[0].get('inst')]
        if not ci: return None, None, 'instance member but keeper is not an instance'
        cands = ci
    cands.sort(key=lambda c: (len(c[1]), not c[0]['mod'].startswith('MachCSL'), len(closure(c[0]['mod'])), c[0]['name']))
    return cands[0][0], cands[0][1], None

allmods = []
for top in ('Xv6', 'MachCSL'):
    for dp, _, fs in os.walk(os.path.join(ROOT, top)):
        for f in fs:
            if f.endswith('.lean'):
                allmods.append(os.path.relpath(os.path.join(dp, f), ROOT)[:-5].replace(os.sep, '.'))

def users_of(mem):
    if mem['priv']: return [mem['mod']]
    return [m for m in allmods if m == mem['mod'] or mem['mod'] in closure(m)]

applied, skipped = [], []
newimports = set()
deletions = collections.defaultdict(list)   # mod -> [(l0,l1)]
renames = []                                # (Dfull, keeperFull, [mods])
for g in load():
    if g['kind'] != kind: continue
    if category(g): continue
    names = [m['name'] for m in g['mems']]
    if any(n in skipnames for n in names):
        skipped.append(('skiplist', names)); continue
    if not all(is_decl(m) for m in g['mems']):
        skipped.append(('non-decl member (field/structure)', names)); continue
    k, imps, why = pick_keeper(g, allow_imports='--noimports' not in args)
    if not k:
        skipped.append((why, names)); continue
    bad = None
    for m in g['mems']:
        if m is k: continue
        a = [x for x in attrs(m) if x.strip() not in ('instance',)]
        if a and sorted(a) != sorted(attrs(k)): bad = 'attribute on deleted member: ' + ','.join(a)
        if not IDENT.match(m['name'].split('.')[-1]): bad = 'non-identifier name'
    if bad:
        skipped.append((bad, names)); continue
    # a new import must not close a cycle with an import added for an earlier group
    cyc = False
    for (a, b) in imps:
        if a in closure(b) or any(x == b and y == a for (x, y) in newimports): cyc = True
    if cyc:
        skipped.append(('import cycle', names)); continue
    newimports.update(imps)
    for m in g['mems']:
        if m is k: continue
        deletions[m['mod']].append((m['l0'], m['l1']))
        renames.append((m['name'], k['name'], users_of(m), m['mod']))
    applied.append({'keep': k['name'], 'keepmod': k['mod'], 'imports': sorted(imps),
                    'del': [(m['name'], m['mod']) for m in g['mems'] if m is not k], 'type': g['type']})

with open(os.path.join(ROOT, 'scratch/skipped_%s.txt' % kind), 'w') as f:
    for why, names in skipped: f.write(f'{why}: {" ".join(names)}\n')
with open(os.path.join(ROOT, 'scratch/applied_%s.jsonl' % kind), 'w') as f:
    for a in applied: f.write(json.dumps(a) + '\n')
print(f'imports {len(newimports)}; applied {len(applied)} groups, {sum(len(a["del"]) for a in applied)} deletions; skipped {len(skipped)}')
if dry: sys.exit(0)

PREFIX = re.compile(r'^\s*(set_option|omit|include|variable|unseal|seal|open|attribute)\b.*\sin\s*$')
for mod, rngs in deletions.items():
    L = src(mod)
    kill = set()
    for l0, l1 in rngs:
        for i in range(l0 - 1, l1): kill.add(i)
        j = l0 - 2
        while j >= 0 and PREFIX.match(L[j]):
            kill.add(j); j -= 1
    out = [l for i, l in enumerate(L) if i not in kill]
    # collapse runs of >2 blank lines created by deletions
    res = []
    for l in out:
        if l.strip() == '' and len(res) >= 2 and res[-1].strip() == '' and res[-2].strip() == '':
            continue
        res.append(l)
    _src[mod] = res

def visible_bare(text, ns, dmod, fmod):
    if fmod == dmod or ns in ('Xv6', 'MachCSL', ''): return True
    last = ns.split('.')[-1]
    return bool(re.search(r'^\s*(namespace|open)\b.*\b' + re.escape(last) + r'\b', text, re.M))

by_file = collections.defaultdict(list)
for dfull, kfull, mods, dmod in renames:
    for m in mods: by_file[m].append((dfull, kfull, dmod))
for mod, rs in by_file.items():
    L = src(mod); text = '\n'.join(L); orig = text
    for dfull, kfull, dmod in rs:
        parts = dfull.split('.'); s = parts[-1]; ns = '.'.join(parts[:-1])
        pat = re.compile(r"(?<![\w.'!?])((?:[A-Za-z_][\w']*\.)*)" + re.escape(s) + r"(?![\w'!?])")
        okbare = visible_bare(text, ns, dmod, mod)
        def rep(mo, ns=ns, kfull=kfull, okbare=okbare):
            q = mo.group(1)[:-1] if mo.group(1) else ''
            if q:
                if ('.' + ns).endswith('.' + q): return kfull
                return mo.group(0)
            return kfull if okbare else mo.group(0)
        text = pat.sub(rep, text)
    if text != orig: _src[mod] = text.split('\n')

def header_last_import(L):
    inc = False; last = None
    for i, l in enumerate(L):
        st = l.strip()
        if inc:
            if '-/' in st: inc = False
            continue
        if st.startswith('/-'):
            if '-/' not in st[2:]: inc = True
            continue
        if st == '' or st.startswith('--'): continue
        if st.startswith('import '): last = i; continue
        break
    assert last is not None
    return last

for (a, b) in sorted(newimports):
    L = src(a)
    last = header_last_import(L)
    if ('import ' + b) not in L:
        L.insert(last + 1, 'import ' + b)
    _src[a] = L

for mod in set(list(deletions) + list(by_file) + [a for (a, b) in newimports]):
    new = '\n'.join(_src[mod]) if isinstance(_src[mod], list) else _src[mod]
    old = open(modpath(mod), encoding='utf-8').read()
    if new != old: open(modpath(mod), 'w', encoding='utf-8').write(new)
print('files written')

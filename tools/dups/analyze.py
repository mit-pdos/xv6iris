#!/usr/bin/env python3
"""Classify duplicate groups from scratch/dups.jsonl.
auto  : some public member's module is imported (transitively) by every other member's module
        (or all members share a module) -> keep it, delete the rest
home  : no such member (e.g. all in Proof* files) -> needs a new common home
"""
import json, os, sys, re, collections
sys.path.insert(0, os.path.dirname(__file__))
import importlib.util
spec = importlib.util.spec_from_file_location('imps', os.path.join(os.path.dirname(__file__), 'imps.py'))
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import functools
def path(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
@functools.lru_cache(None)
def direct(m):
    p = path(m)
    if not os.path.exists(p): return ()
    out = []
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'\s*import\s+(.*)', line)
        if mm: out += mm.group(1).split()
    return tuple(out)
@functools.lru_cache(None)
def closure(m):
    s = set()
    for d in direct(m):
        s.add(d); s |= closure(d)
    return frozenset(s)

def load():
    return [json.loads(l) for l in open(os.path.join(ROOT, 'scratch/dups.jsonl')) if l.strip()]

def category(g):
    mods = [m['mod'] for m in g['mems']]
    if any(x.split('.')[-1].startswith('Link') for x in mods): return 'link'
    t = g['type']
    if ('MachCSL.KA.' in t or 'MachCSL.KStr.' in t) and not t.startswith('∀'): return 'kaddr'
    return None

def keeper(g):
    mems = g['mems']
    cands = []
    for k in mems:
        ok = True
        for o in mems:
            if o is k: continue
            if o['mod'] == k['mod']:
                if o['l0'] < k['l0']: ok = False   # keep the earliest in a file
                continue
            if k['priv'] or k['mod'] not in closure(o['mod']): ok = False
        if ok: cands.append(k)
    if not cands: return None
    # prefer: MachCSL, then smallest closure (lowest module)
    cands.sort(key=lambda k: (not k['mod'].startswith('MachCSL'), len(closure(k['mod'])), k['name']))
    return cands[0]

if __name__ == '__main__':
    gs = load()
    stats = collections.Counter()
    for g in gs:
        k = keeper(g)
        cls = category(g) or ('auto' if k else 'home')
        stats[(g['kind'], cls)] += 1
        if len(sys.argv) > 1 and sys.argv[1] == cls and g['kind'] == (sys.argv[2] if len(sys.argv) > 2 else g['kind']):
            print(g['kind'], len(g['mems']), 'KEEP', k['name'] if k else '-', '|', ' '.join(m['name'] + '@' + m['mod'] for m in g['mems']))
            print('    ', g['type'][:160].replace('\n', ' '))
    print(stats, file=sys.stderr)

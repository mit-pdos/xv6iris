#!/usr/bin/env python3
"""Merge duplicate-theorem groups that have no member every other member can
see, by MOVING one member to a common home H and deleting the rest.
H = the deepest non-Proof/Link module defining a constant of the statement,
or MachCSL.BvLemmas (new) for statements over core constants only.
usage: home.py [--dry] [--drop FILE]   (FILE: group ids to leave alone)
Writes scratch/home_applied.jsonl."""
import json, os, re, sys, collections, functools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from analyze import closure, direct, category, ROOT

args = sys.argv[1:]
dry = '--dry' in args
drop = set()
if '--drop' in args:
    drop = set(l.strip() for l in open(args[args.index('--drop') + 1]) if l.strip())
BVHOME = 'MachCSL.BvLemmas'

def modpath(m): return os.path.join(ROOT, *m.split('.')) + '.lean'
_src = {}
def src(m):
    if m not in _src:
        p = modpath(m)
        _src[m] = open(p, encoding='utf-8').read().split('\n') if os.path.exists(p) else None
    return _src[m]

@functools.lru_cache(None)
def depth(m):
    if m == BVHOME: return 1
    ds = [d for d in direct(m) if d.split('.')[0] in ('Xv6', 'MachCSL')]
    return 1 + max((depth(d) for d in ds), default=0)

def is_pl(mod):
    b = mod.split('.')[-1]
    return b.startswith('Proof') or b.startswith('Link')

DECL = re.compile(r"^(\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*)(theorem|lemma)\s+([^\s(:{\[]+)", re.M)
PREFIX = re.compile(r'^\s*(set_option|omit|include|variable|unseal|seal|open|attribute)\b.*\sin\s*$')
GOODPFX = ('bcond', 'imm', 'lui', 'add', 'sext', 'ext', 'beq', 'bne', 'blt', 'bge', 'li', 'ofNat', 'toNat',
           'bv', 'nat', 'signExtend', 'extractLsb', 'setWidth', 'trunc', 'mask', 'shift', 'KCtx', 'withSpie',
           'withLocks', 'withRegs', 'procAddr', 'pcIs', 'calleeSaved', 'zext', 'sub', 'mul', 'and', 'or', 'xor')

def mem_text(m):
    L = src(m['mod']); return '\n'.join(L[m['l0'] - 1: m['l1']])

def name_score(n):
    s = n.split('.')[-1]
    bad = re.match(r'^[a-z][a-z0-9]{0,5}_', s) and not s.startswith(GOODPFX)
    return (1 if bad else 0, s.count('_'), len(s), s)

def bad_prefix(s):
    return bool(re.match(r'^[a-z][a-z0-9]{0,6}_', s)) and not s.startswith(GOODPFX)

def decent(s):
    return len(s) >= 7 and ('_' in s or any(ch.isupper() for ch in s)) and not re.match(r'^h\d', s)

def decent(s):
    segs = s.split('_')
    if len(s) < 5 or s[0].isdigit(): return False
    if '_' not in s and sum(ch.isupper() for ch in s) < 1: return False
    if all(re.match(r'^[0-9a-f]+$', x) and len(x) <= 4 for x in segs[-1:]) and len(segs) <= 2 and not re.search(r'[g-z]', segs[-1]):
        return False
    return True

def clean_name(g):
    cnt = collections.Counter()
    for m in g['mems']:
        s = m['name'].split('.')[-1]
        segs = s.split('_')
        cnt.update(set(['_'.join(segs[i:]) for i in range(len(segs))]))
    fulls = set(m['name'].split('.')[-1] for m in g['mems'])
    cands = [(c, len(x), x) for x, c in cnt.items() if c >= 2 and decent(x) and ('_' in x or x in fulls)
             and re.match(r"^[A-Za-z_][\w'!?]*$", x)]
    if not cands: return None
    return max(cands)[2]

def pick_home(g):
    mods = [m['mod'] for m in g['mems']]
    cm = [c for c in g['cmods'] if c.split('.')[0] in ('Xv6', 'MachCSL')]
    if any(is_pl(c) for c in cm): return None, 'statement constant defined in a Proof/Link file'
    if any(c in mods for c in cm): return None, 'statement constant defined in a member module'
    if not cm and ('BitVec' not in g['type'] or 'List' in g['type'] or 'String' in g['type']):
        return None, 'core statement outside BitVec'
    H = max(cm, key=lambda c: (depth(c), c)) if cm else BVHOME
    imps = set()
    for o in mods:
        if H == o: return None, 'home is a member module'
        if H == BVHOME or H not in closure(o):
            if depth(H) < depth(o) and not is_pl(H): imps.add((o, H))
            else: return None, 'home not visible'
    return H, imps

existing = collections.Counter()
for top in ('Xv6', 'MachCSL'):
    for dp, _, fs in os.walk(os.path.join(ROOT, top)):
        for f in fs:
            if f.endswith('.lean'):
                for mo in re.finditer(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)', open(os.path.join(dp, f), encoding='utf-8').read(), re.M):
                    existing[mo.group(1).split('.')[-1]] += 1

allmods = []
for top in ('Xv6', 'MachCSL'):
    for dp, _, fs in os.walk(os.path.join(ROOT, top)):
        for f in fs:
            if f.endswith('.lean'):
                allmods.append(os.path.relpath(os.path.join(dp, f), ROOT)[:-5].replace(os.sep, '.'))

def users_of(mem):
    if mem['priv']: return [mem['mod']]
    return [m for m in allmods if m == mem['mod'] or mem['mod'] in closure(m)]

def code_mask(L):
    """True for lines that start outside any block comment."""
    depth_ = 0; out = []
    for l in L:
        out.append(depth_ == 0)
        i = 0
        while i < len(l):
            if l.startswith('/-', i): depth_ += 1; i += 2; continue
            if l.startswith('-/', i) and depth_ > 0: depth_ -= 1; i += 2; continue
            if depth_ == 0 and l.startswith('--', i): break
            if depth_ == 0 and l[i] == '"':
                j = l.find('"', i + 1); i = (j + 1) if j > 0 else len(l); continue
            i += 1
    return out

def last_end(L):
    M = code_mask(L)
    return max(i for i, l in enumerate(L) if M[i] and re.match(r'^end\b', l))

def ns_at_end(H):
    L = src(H)
    if L is None: return 'MachCSL'
    k = last_end(L)
    M = code_mask(L)
    stack = []
    for i, l in enumerate(L[:k]):
        if not M[i]: continue
        mo = re.match(r'^namespace\s+(\S+)', l)
        if mo: stack.append(('ns', mo.group(1))); continue
        mo = re.match(r'^section\b\s*(\S*)', l)
        if mo: stack.append(('sec', mo.group(1))); continue
        mo = re.match(r'^end\b\s*(\S*)', l)
        if mo and stack: stack.pop()
    return '.'.join(n for kind, n in stack if kind == 'ns')

def home_ns(H):
    return ns_at_end(H)

gs = [json.loads(l) for l in open(os.path.join(ROOT, 'scratch/dups.jsonl')) if l.strip()]
applied, skipped = [], []
deletions = collections.defaultdict(list)
insertions = collections.defaultdict(list)   # H -> [text]
renames = []
newimports = set()
taken = set()
for gi, g in enumerate(gs):
    if g['kind'] != 'thm' or category(g): continue
    names = [m['name'] for m in g['mems']]
    gid = names[0]
    if gid in drop: skipped.append(('dropped', names)); continue
    if any(m.get('inst') for m in g['mems']): skipped.append(('instance', names)); continue
    texts = [mem_text(m) for m in g['mems']]
    if not all(DECL.search(t) for t in texts): skipped.append(('non-decl', names)); continue
    if any('@[' in t for t in texts): skipped.append(('attribute', names)); continue
    # members that some earlier group already claimed a line range of (nested) -> skip
    H, imps = pick_home(g)
    if H is None: skipped.append((imps, names)); continue
    src_m = min(g['mems'], key=lambda m: (m['l1'] - m['l0'], m['name']))
    newshort = clean_name(g)
    if newshort is None: skipped.append(('no clean name', names)); continue
    newfull = home_ns(H) + '.' + newshort
    # the short name must not denote anything else in the tree
    others = existing[newshort] - sum(1 for m in g['mems'] if m['name'].split('.')[-1] == newshort)
    if others > 0 or newfull in taken:
        alt = newshort + '_' + ('bv' if H == BVHOME else 'x')
        skipped.append(('name clash ' + newshort, names)); continue
    taken.add(newfull)
    # text to move
    L = src(src_m['mod'])
    j = src_m['l0'] - 2; pre = []
    while j >= 0 and PREFIX.match(L[j]):
        pre.insert(0, L[j]); j -= 1
    body = mem_text(src_m)
    old_short = src_m['name'].split('.')[-1]
    body = DECL.sub(lambda mo: mo.group(1).replace('private ', '') + mo.group(2) + ' ' + newshort, body, count=1)
    insertions[H].append('\n'.join(pre + [body]))
    for m in g['mems']:
        deletions[m['mod']].append((m['l0'], m['l1']))
        renames.append((m['name'], newfull, users_of(m), m['mod']))
    newimports |= imps
    applied.append({'gid': gid, 'home': H, 'new': newfull, 'src': src_m['name'],
                    'del': [(m['name'], m['mod']) for m in g['mems']], 'imports': sorted(imps)})

with open(os.path.join(ROOT, 'scratch/home_skipped.txt'), 'w') as f:
    for why, names in skipped: f.write(f'{why}: {" ".join(names)}\n')
with open(os.path.join(ROOT, 'scratch/home_applied.jsonl'), 'w') as f:
    for a in applied: f.write(json.dumps(a) + '\n')
print(f'home: applied {len(applied)} groups, {sum(len(a["del"]) for a in applied)} deletions, '
      f'{len(newimports)} imports, homes {len(insertions)}; skipped {len(skipped)}')
print(collections.Counter(w if isinstance(w, str) else 'x' for w, _ in skipped))
if dry: sys.exit(0)

# 1. deletions (whole members, with their `… in` prefix lines)
for mod, rngs in deletions.items():
    L = src(mod); kill = set()
    for l0, l1 in rngs:
        kill.update(range(l0 - 1, l1))
        j = l0 - 2
        while j >= 0 and PREFIX.match(L[j]): kill.add(j); j -= 1
    _src[mod] = [l for i, l in enumerate(L) if i not in kill]

# 2. insertions
if BVHOME in insertions and src(BVHOME) is None:
    _src[BVHOME] = ['/-', 'MachCSL: plain `BitVec` / `Nat` facts over core constants only -- the one',
                    'home of the arithmetic identities the kernel proofs share (frame immediates,',
                    'sign/zero extensions, `lui` constants, small `toNat`/`ofNat` steps).', '-/',
                    'import Std.Tactic.BVDecide', '', 'namespace MachCSL', '', 'end MachCSL', '']
for H, blocks in insertions.items():
    L = src(H)
    k = last_end(L)
    ins = []
    for b in blocks: ins += [b, '']
    _src[H] = L[:k] + ins + L[k:]

# 3. uses
def visible_bare(text, ns, dmod, fmod):
    if fmod == dmod or ns in ('Xv6', 'MachCSL', ''): return True
    last = ns.split('.')[-1]
    return bool(re.search(r'^\s*(namespace|open)\b.*\b' + re.escape(last) + r'\b', text, re.M))
by_file = collections.defaultdict(list)
for dfull, kfull, mods, dmod in renames:
    for m in mods: by_file[m].append((dfull, kfull, dmod))
for mod, rs in by_file.items():
    text = '\n'.join(src(mod)); orig = text
    for dfull, kfull, dmod in rs:
        parts = dfull.split('.'); s = parts[-1]; ns = '.'.join(parts[:-1])
        pat = re.compile(r"(?<![\w.'!?])((?:[A-Za-z_][\w']*\.)*)" + re.escape(s) + r"(?![\w'!?])")
        okbare = visible_bare(text, ns, dmod, mod)
        def rep(mo, ns=ns, kfull=kfull, okbare=okbare):
            q = mo.group(1)[:-1] if mo.group(1) else ''
            if q:
                return kfull if ('.' + ns).endswith('.' + q) else mo.group(0)
            return kfull if okbare else mo.group(0)
        text = pat.sub(rep, text)
    if text != orig: _src[mod] = text.split('\n')

# 4. imports
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
    return last
for (a, b) in sorted(newimports):
    L = src(a); last = header_last_import(L)
    if ('import ' + b) not in L: L.insert(last + 1, 'import ' + b)
if BVHOME in insertions:
    R = src('MachCSL') if False else open(os.path.join(ROOT, 'MachCSL.lean')).read().split('\n')
    if 'import ' + BVHOME not in R:
        last = header_last_import(R); R.insert(last + 1, 'import ' + BVHOME)
        open(os.path.join(ROOT, 'MachCSL.lean'), 'w').write('\n'.join(R))

for mod, L in _src.items():
    if L is None: continue
    new = '\n'.join(L)
    p = modpath(mod)
    old = open(p, encoding='utf-8').read() if os.path.exists(p) else None
    if new != old: open(p, 'w', encoding='utf-8').write(new)
print('written')

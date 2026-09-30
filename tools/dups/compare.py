import re
def load(p):
    s = open(p).read().split('\n')
    nums = [l for l in s if l.strip().isdigit()]
    t0, t1 = int(nums[0]), int(nums[-1])
    mods = {}
    for m in re.finditer(r'Built (\S+) \(([\d.]+)(m?s)\)', '\n'.join(s)):
        v = float(m.group(2)); v = v / 1000 if m.group(3) == 'ms' else v
        if m.group(1).startswith(('Xv6', 'MachCSL')): mods[m.group(1)] = v
    return t1 - t0, mods
wb, b = load('scratch/fullbase.log'); wn, n = load('scratch/fullnew.log')
print('wall base', wb, 'new', wn)
print('modules', len(b), len(n), 'cpu base %.0f new %.0f' % (sum(b.values()), sum(n.values())))
d = sorted(((n.get(k, 0) - b.get(k, 0)), k) for k in set(b) | set(n))
print('biggest increases', [(k, round(x, 1)) for x, k in d[-8:]])
print('biggest decreases', [(k, round(x, 1)) for x, k in d[:8]])
def ax(p):
    t = open(p).read()
    nat = re.findall(r'[\w.\'«»]+\._native\.[\w.]+', t)
    other = sorted(set(re.findall(r'\b(propext|Classical\.choice|Quot\.sound|[\w.]*sorryAx|[\w.]+ofReduceBool)\b', t)))
    heads = re.findall(r"'([\w.]+)' depends on axioms", t)
    return heads, other, nat
for p in ('scratch/axioms_base.txt', 'scratch/axioms_new.txt'):
    h, o, nat = ax(p)
    print(p, h, o, 'natives', len(nat), 'distinct', len(set(nat)))

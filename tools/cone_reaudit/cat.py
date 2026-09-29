"""Categorise the not-excluded, not-matched candidates by rule; print the residue."""
import json, re, sys, collections
S = 'scratch/cone/'
cand = json.load(open(S + 'cand.json'))
RS = json.load(open(S + 'restrict.json'))

RULES = [
    ('via-dropped', lambda r: r['key'] not in RS),
    ('camera', lambda r: 'Σ' in r['name'] or r['name'].startswith('subG_') or r['name'].endswith('_inG')
        or re.match(r'^(fa|eg|fog|pog|ppg|png|eo|ep)_', r['name']) and r['gkind'] == 'proj'
        or re.search(r'(UR|R)$', r['name']) and r['gkind'] == 'def' and r['file'] in ('FdSlots', 'FileInvDefs', 'ProcAvail', 'TsoGhost', 'Xv6Cameras', 'RiscvPtsto', 'UkCatFIface', 'UkPipesIface', 'UkFileIface')),
    ('DU9-dec', lambda r: r['gkind'] == 'inst' and re.search(r'(dec|_eq_dec|inhabited|countable|_inj)$|_dec_hook$', r['name'])
        or r['name'].endswith('_dec') or 'eq_dec' in r['name']),
    ('inst-tl/pers', lambda r: r['gkind'] == 'inst' and re.search(r'(timeless|persistent|pers\d*|tl\d*|_pers0|_tl0|forkable.*)$', r['name'])
        or re.search(r'_(T|links|kit|exf)_(pers|tl)0$', r['name'])),
    ('DU3-codepin', lambda r: re.match(r'^(shp|shpp|shr|shd_pin|ushp_code|ushm_code|ushf_code|ushf_rodata|ushp_code_shk)_', r['name'])
        or r['name'].endswith('_union_comm_bool') or r['name'].endswith('_code_persistent')),
    ('DU4-printf', lambda r: r['file'] == 'UkShDiag' and re.match(r'^(wp_kshd_(vprintf|putc|fprintf)|vp_|shd_str|shd_sb|moi_sub)', r['name'])
        or re.match(r'^(cat|init|secc)_lit_', r['name'])),
    ('elf-image', lambda r: r['file'] == 'ElfUser'),
    ('proj', lambda r: r['gkind'] == 'proj'),
    ('documented', lambda r: r['lean'] == 'mention'),
]


def cat(r):
    for n, f in RULES:
        if f(r):
            return n
    return None


out = collections.defaultdict(list)
for r in cand:
    if r['excl']:
        continue
    out[cat(r)].append(r)
for k, v in out.items():
    print(k, len(v))
json.dump({str(k): v for k, v in out.items()}, open(S + 'cat.json', 'w'), ensure_ascii=False)
if len(sys.argv) > 1:
    for r in sorted(out[None if sys.argv[1] == 'None' else sys.argv[1]], key=lambda r: (r['file'], r['name'])):
        kg = 'K' if 'U' not in r['glob'] else ' '
        print('%-18s %-34s %-5s %s  %s' % (r['file'], r['name'], r['gkind'], kg, r['path'][-230:]))

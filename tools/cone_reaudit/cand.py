"""Candidate list: union-side reached, not name-matched in Lean, after file-level exclusions."""
import json, collections, re, sys
S = 'scratch/cone/'
rows = json.load(open(S + 'audit.json'))
fr = collections.defaultdict(set)
for r in rows:
    fr[r['file']] |= set(r['roots'])
uonly = {f for f, s in fr.items() if s == {'U'}}

DU3 = lambda f: f.startswith('UCode')
DU9 = {'UnionDecU', 'PipesDecE', 'FileDiscDec', 'PipesDiscDec', 'UnionDiscDec'}
DU8F = {'UkShPipeCm', 'UkShRedirPr', 'UkShParseExec', 'UkShPipePex', 'UkShPipeEx2', 'UkShPipeParse',
        'UkShParseRedir', 'UkShPipePr', 'UkShPipeRight', 'UkShPipeEx', 'UkShPipeTok', 'UkShRedirLex'}
DU8D = {('UkShParseCmd', n) for n in ['wp_kshp_parser', 'wp_kshp_parsecmd', 'wp_kshp_parseline', 'wp_kshp_parsepipe', 'wp_kshp_nulterminate']}
DU8D |= {('UkShParseTok', n) for n in ['wp_kshp_gettoken', 'wp_kshp_gtk_disp', 'ushp_gettok_end', 'ushp_gettok_fin', 'ushp_gettok_res']}
DU4 = re.compile(r'^Uk(Cat|Grep|Secc|Init|Sh)(Putc|Vprintf|VprintfS|Fprintf|FprintfS)$')
DU2 = re.compile(r'^(WpUmode|Umode|WpMmode|UkStep$|UkLeaf$|UkLoad$|UkStore$|UkLoadText$|UkBranch$|UserTotalU$|HartSMem$|UserPtTree$|RiscvPtsto$|DevModel$|Xv6Cameras$|PStringBytes$)')


def excl(r):
    f, n = r['file'], r['name']
    if DU3(f): return 'DU3'
    if f in DU9: return 'DU9'
    if f in DU8F or (f, n) in DU8D: return 'DU8'
    if f == 'UkShParseLex' and n.endswith('_sym'): return 'DU8'
    if f == 'UkShPipesLex' and n.endswith('_barw'): return 'DU8'
    if DU4.match(f): return 'DU4'
    if DU2.match(f): return 'DU2'
    if r['auto']: return 'auto'
    return None


out = []
for r in rows:
    if not (r['file'] in uonly or r['roots'] == 'U'):
        continue
    if r['lean'] in ('decl', 'doc'):
        continue
    r['excl'] = excl(r)
    out.append(r)
c = collections.Counter(r['excl'] for r in out)
print(c)
json.dump(out, open(S + 'cand.json', 'w'), ensure_ascii=False)
if len(sys.argv) > 1:
    for r in sorted(out, key=lambda r: (r['file'], r['name'])):
        if r['excl'] is None:
            kg = 'K' if 'U' not in r['glob'] else ' '
            print('%-20s %-40s %-6s %s %-8s %s' % (r['file'], (r['secs'] + '.' if r['secs'] else '') + r['name'], r['gkind'], kg,
                                                 r['lean'] or '-', ','.join(x.split('/')[-1] for x in r['where'][:3])))

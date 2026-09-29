"""Re-walk each root's kernel graph WITHOUT entering documented-dropped
declarations (DU2/DU3/DU4/DU8/DU9 files and decls).  A candidate reached only
through such a declaration is dead weight by that ruling.  Writes
scratch/restrict.json: key -> (reached-without-excluded?, parent)."""
import json, collections, re, sys
S = 'scratch/cone/'
# reuse excl() without running cand.py's main: copy the rules
DU3 = lambda f: f.startswith('UCode')
DU9 = {'UnionDecU', 'PipesDecE', 'FileDiscDec', 'PipesDiscDec', 'UnionDiscDec'}
DU8F = {'UkShPipeCm', 'UkShRedirPr', 'UkShParseExec', 'UkShPipePex', 'UkShPipeEx2', 'UkShPipeParse',
        'UkShParseRedir', 'UkShPipePr', 'UkShPipeRight', 'UkShPipeEx', 'UkShPipeTok', 'UkShRedirLex'}
DU8D = {('UkShParseCmd', n) for n in ['wp_kshp_parser', 'wp_kshp_parsecmd', 'wp_kshp_parseline', 'wp_kshp_parsepipe', 'wp_kshp_nulterminate']}
DU8D |= {('UkShParseTok', n) for n in ['wp_kshp_gettoken', 'wp_kshp_gtk_disp', 'ushp_gettok_end', 'ushp_gettok_fin', 'ushp_gettok_res']}
DU8D |= {('UkShEcho', n) for n in ['wp_kshm_child_x_holds', 'wp_kshm_child_x_v_holds']}
DU8D |= {('UkShPipesCmd', n) for n in ['wp_kshp_parsecmd_pipes', 'wp_kshp_parseline_pipes', 'wp_kshp_nulterminate_pipes', 'ushp_pipe_node', 'ushq_tree_pipe_node']}
DU8D |= {('UkShPipesParse', n) for n in ['wp_kshp_parsepipe_bars', 'ushq_pex_left_at_holds', 'ushq_tree_pipe', 'ushp_pipe_node']}
DU4 = re.compile(r'^Uk(Cat|Grep|Secc|Init|Sh)(Putc|Vprintf|VprintfS|Fprintf|FprintfS)$')


def excl_key(k):
    p = k.split('.')
    if p[0] != 'xv6iris':
        return None
    f, n = p[1], p[-1]
    if DU3(f): return 'DU3'
    if f in DU9: return 'DU9'
    if f in DU8F or (f, n) in DU8D: return 'DU8'
    if f == 'UkShParseLex' and n.endswith('_sym'): return 'DU8'
    if f == 'UkShPipesLex' and n.endswith('_barw'): return 'DU8'
    if DU4.match(f): return 'DU4'
    if f == 'UkShDiag' and re.match(r'^(wp_kshd_(vprintf|putc|fprintf)|vp_)', n): return 'DU4'
    return None


edges = collections.defaultdict(list)
roots = {}
for r in 'PSU':
    for line in open(S + 'edges_%s.txt' % r, errors='replace'):
        t = line.rstrip('\n').split(' ')
        if t[0] == 'R':
            roots[r] = t[1]
        elif t[0] == 'E':
            edges[t[1]].append(t[2])
res = {}
for r, root in roots.items():
    seen = {root}
    todo = [root]
    while todo:
        k = todo.pop()
        for d in edges.get(k, ()):
            if d in seen or excl_key(d):
                continue
            seen.add(d)
            todo.append(d)
    for k in seen:
        res.setdefault(k, set()).add(r)
json.dump({k: ''.join(sorted(v)) for k, v in res.items()}, open(S + 'restrict.json', 'w'))
print(len(res))

#!/usr/bin/env python3
"""Greedy what-if optimiser for the build critical path.

Starts from the *exact-needs* graph (every module depends on exactly the modules whose
constants / macros / simp sets / attributes it uses, i.e. all dead imports gone) and then
repeatedly looks at each edge P -> C on the critical path.  If C uses only a small part of
P, it simulates splitting P into
    P~k   : the constants C uses from P plus their intra-P dependency closure
    P     : the rest (imports P~k if it still refers to it)
and re-points every node that only uses P~k's constants at P~k.  The split with the best
critical-path gain is applied and the loop repeats.

Two closure modes:
  move  the moved constants carry their proofs (a plain "move these lemmas down" refactor)
  spec  a theorem used by C contributes only its *statement* (C would take the lemma as a
        hypothesis / use a Spec-def + separately proven instance, as in a stage-lemma
        pipeline); definitions still carry their bodies.

Time model: P~k costs 0.7s + (t(P) - 0.7s) * |moved| / |P| (constant-count share); the
remaining P keeps its full measured time (conservative).

Usage:
  tools/split_whatif.py --needs needs.tsv --consts constdeps.tsv --log build.log \
      --rev REV [--mode move|spec] [--steps 25] [--max-frac 0.5]
"""
import argparse, collections, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_graph as ig  # noqa
from import_shake import load, LOCAL, UMBRELLA, CORE, root  # noqa

OVERHEAD = 0.7


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--needs", required=True)
    ap.add_argument("--consts", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--rev")
    ap.add_argument("--root", default=ig.HERE)
    ap.add_argument("--mode", default="move", choices=["move", "spec"])
    ap.add_argument("--steps", type=int, default=25)
    ap.add_argument("--max-frac", type=float, default=0.5)
    ap.add_argument("--min-gain", type=float, default=0.5)
    ap.add_argument("--set-time", nargs="*", default=[],
                    help="MOD=SECONDS overrides of measured build times (what-if)")
    ap.add_argument("--no-model", action="store_true",
                    help="never split the generated model / lean-sail (LeanRV64D, Sail)")
    a = ap.parse_args()

    t = ig.read_times(a.log)
    for kv in a.set_time:
        k, v = kv.split("=")
        t[k] = float(v)
    gfull, _ = ig.build_graph(a.root, a.rev)
    g = ig.restrict(gfull, ["MachCSL", "Xv6"])
    imports, needs, decls, _ = load(a.needs)

    # ---- constants ----
    cmod, ckind, ctref, cvref, cext = {}, {}, {}, {}, {}
    owners = collections.defaultdict(list)
    for line in open(a.consts, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if f[0] != "C" or len(f) < 7:
            continue
        m, c, k = f[1], f[2], f[3]
        key = (m, c)
        owners[c].append(m)
        ckind[key] = k
        ctref[key] = f[4].split() if f[4] else []
        cvref[key] = f[5].split() if f[5] else []
        cext[key] = [x for x in f[6].split() if x in g]

    # original transitive closure for resolving duplicated names
    order0, _ = ig.topo(g)
    clos0 = {}
    for m in order0:
        s = set()
        for i in g[m]:
            s.add(i)
            s |= clos0[i]
        clos0[m] = s

    def resolve(m, c):
        ms = owners.get(c)
        if not ms:
            return None
        if len(ms) == 1:
            return (ms[0], c)
        if m in ms:
            return (m, c)
        for o in ms:
            if o in clos0.get(m, ()):
                return (o, c)
        return (ms[0], c)

    tref = {k: [r for r in (resolve(k[0], c) for c in v) if r] for k, v in ctref.items()}
    vref = {k: [r for r in (resolve(k[0], c) for c in v) if r] for k, v in cvref.items()}
    # extra (macro/simp-set/attribute) needs per module, kept by both halves of a split
    extra = {}
    for m in g:
        ex = set()
        for j, (kind, *_r) in needs.get(m, {}).items():
            if kind in ("extra", "indirect", "quote") and j in clos0.get(m, ()) and j in g:
                ex.add(j)
        extra[m] = ex

    # ---- nodes ----
    node_of = {}                   # const key -> node
    consts = collections.defaultdict(set)
    for k in ckind:
        if k[0] in g:
            node_of[k] = k[0]
            consts[k[0]].add(k)
    base_mod = {n: n for n in g}   # node -> original module (for times/extra)
    times = {n: t.get(n, 0.0) for n in g}

    spec_host = {}   # spec mode: moved theorem -> node that keeps (hosts) its proof
    hosted = collections.defaultdict(set)

    def node_deps(n):
        ks = consts.get(n)
        m = base_mod[n]
        if not ks or root(m) not in LOCAL or m in UMBRELLA:
            return set(g[n]) if n in g else set()
        d = set(extra[m])
        for k in ks:
            for r in tref[k]:
                d.add(node_of.get(r, r[0]))
            if k not in spec_host:
                for r in vref[k]:
                    d.add(node_of.get(r, r[0]))
            d.update(cext[k])
        for k in hosted.get(n, ()):
            d.add(node_of[k])
            for r in vref[k]:
                d.add(node_of.get(r, r[0]))
        d.discard(n)
        return {x for x in d if x in times}

    deps = {n: node_deps(n) for n in times}

    def crit(deps, times):
        gg = {n: list(v) for n, v in deps.items()}
        total, path, ef, slack, order, rev = ig.critical(gg, times)
        return total, path

    total0, path0 = crit({n: set(g[n]) for n in g}, times)
    total, path = crit(deps, times)
    print(f"import graph critical path: {total0:.1f}s")
    print(f"exact-needs graph critical path: {total:.1f}s (mode {a.mode})")

    def closure_in(n, seeds):
        """intra-node closure of seed constants."""
        todo, S = list(seeds), set(seeds)
        while todo:
            k = todo.pop()
            refs = tref[k] if (a.mode == "spec" and ckind[k] == "thm") else tref[k] + vref[k]
            for r in refs:
                if node_of.get(r) == n and r not in S:
                    S.add(r)
                    todo.append(r)
        return S

    step = 0
    applied = []
    while step < a.steps:
        best = None
        for P, C in zip(path, path[1:]):
            if P not in consts or C not in consts or base_mod[C] in UMBRELLA:
                continue
            if root(base_mod[P]) not in LOCAL:
                continue
            if a.no_model and root(base_mod[P]) in ("LeanRV64D", "Sail"):
                continue
            U = set()
            for k in consts[C]:
                for r in tref[k] + vref[k]:
                    if node_of.get(r) == P:
                        U.add(r)
            if not U:
                continue  # extra-only use (macro/simp set): can't split by constants
            S = closure_in(P, U)
            frac = len(S) / max(1, len(consts[P]))
            if frac > a.max_frac:
                continue
            new = f"{P}~{step}"
            rest = consts[P] - S
            # tentative graph edits
            nd = dict(deps)
            nt = dict(times)
            nt[new] = OVERHEAD + max(0.0, times[P] - OVERHEAD) * frac
            saved = (dict((k, node_of[k]) for k in S))
            spec_ks = {k for k in S if a.mode == "spec" and ckind[k] == "thm"}
            for k in S:
                node_of[k] = new
            for k in spec_ks:
                spec_host[k] = P
                hosted[P].add(k)
            consts[new] = S
            consts[P] = rest
            base_mod[new] = base_mod[P]
            nt_extra_ok = True
            affected = {P, new} | {n for n in deps if P in deps[n]}
            times[new] = nt[new]
            for n in affected:
                nd[n] = node_deps(n)
            del times[new]
            tot, pth = crit(nd, nt)
            # undo
            for k, v in saved.items():
                node_of[k] = v
            for k in spec_ks:
                del spec_host[k]
                hosted[P].discard(k)
            consts[P] = consts[P] | S
            del consts[new]
            del base_mod[new]
            gain = total - tot
            if best is None or gain > best[0]:
                best = (gain, P, C, S, U, new, nt[new], tot)
        if not best or best[0] < a.min_gain:
            break
        gain, P, C, S, U, new, tnew, tot = best
        for k in S:
            node_of[k] = new
            if a.mode == "spec" and ckind[k] == "thm":
                spec_host[k] = P
                hosted[P].add(k)
        consts[new] = S
        consts[P] = consts[P] - S
        base_mod[new] = base_mod[P]
        times[new] = tnew
        affected = {P, new} | {n for n in deps if P in deps[n]}
        times[new] = tnew
        deps[new] = set()
        for n in affected:
            deps[n] = node_deps(n)
        prev = total
        total, path = crit(deps, times)
        movers = sorted(c for _, c in U)
        ext_deps = sorted(d for d in deps[new] if root(base_mod.get(d, d)) in ("MachCSL", "Xv6"))
        applied.append((step, P, C, len(U), len(S), len(consts[P]) + len(S), gain, total))
        print(f"\n[{step}] split {base_mod[P]} for {base_mod[C]}: move {len(S)} of "
              f"{len(consts[P]) + len(S)} constants ({len(U)} used directly) -> new node "
              f"({tnew:.1f}s); critical path {prev:.1f}s -> {total:.1f}s (gain {prev - total:.1f}s)")
        print(f"    used: {' '.join(movers[:12])}{' ...' if len(movers) > 12 else ''}")
        print(f"    new node depends on (MachCSL/Xv6 only): {' '.join(ext_deps[:12])}{' ...' if len(ext_deps) > 12 else ''}")
        step += 1
    print(f"\nfinal critical path ({a.mode}): {total:.1f}s")
    for n in path:
        print(f"  {n:55s} {times[n]:6.2f}s")


if __name__ == "__main__":
    main()

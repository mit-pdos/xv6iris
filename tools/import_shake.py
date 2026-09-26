#!/usr/bin/env python3
"""Unused-import analysis over the output of tools/ImportNeeds.lean (a non-`module`
port of `lake shake`'s needs computation).

Usage:
  lake env lean --run tools/ImportNeeds.lean Xv6 MachCSL > needs.tsv
  tools/import_shake.py needs.tsv --src ROOT --out DIR

Writes into DIR:
  dead.txt        dead imports: file -> import, nothing in {import} ∪ closure(import) is needed
                  (grouped: redundant / high / manual-check)
  edits_dead.txt  `Mod -Imp` / `Mod +Imp` lines: remove every dead import (computed in topo
                  order against the already-edited upstream closures) and re-add whatever a
                  module loses because an upstream module stopped importing it.
  edits_exact.txt the exact graph: each module imports precisely the maximal elements of its
                  needs (lower bound for import-only fixes).
  usage.tsv       per direct import: #needed modules it (exclusively) provides, #constants used
Both edit files feed `tools/import_graph.py --move`.
"""
import argparse, collections, os, re, sys

LOCAL = ("MachCSL", "Xv6", "LeanRV64D", "Sail")
UMBRELLA = {"MachCSL", "Xv6", "LeanRV64D", "Sail"}
CORE = ("Init", "Lean", "Std", "Lake")


def root(m):
    return m.split(".")[0]


NSPROV = collections.defaultdict(set)   # namespace -> modules with public constants in it


def load(path):
    imports, needs, decls, rev_keep = {}, collections.defaultdict(dict), {}, set()
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "M":
            imps = [x for x in f[2].split(",") if x] if len(f) > 2 else []
            imports[f[1]] = list(dict.fromkeys(imps))
        elif f[0] == "N":
            m, j, kind, user, used = f[1:6]
            cnt = int(f[6]) if len(f) > 6 else 1
            ex = f[7].split() if len(f) > 7 else [used]
            needs[m][j] = (kind, user, used, cnt, ex)
        elif f[0] == "D":
            decls[f[1]] = f[2].split() if len(f) > 2 else []
        elif f[0] == "R":
            rev_keep.add(f[1])
        elif f[0] == "P" and len(f) > 2:
            for ns in f[2].split():
                NSPROV[ns].add(f[1])
    return imports, needs, decls, rev_keep


def opened_namespaces(text):
    """(candidates, ...) for every `open`/`export` in text: each entry is the list of fully
    qualified namespaces the opened identifier may denote, most specific first."""
    text = strip_comments(text)
    stack, out = [], []   # stack of ("ns", [components]) / ("sec", None)
    for line in text.split("\n"):
        st = line.strip()
        m = re.match(r"^(?:noncomputable\s+)?(?:@\[[^\]]*\]\s*)?namespace\s+(\S+)", st)
        if m:
            stack.append(("ns", m.group(1).split(".")))
            continue
        if re.match(r"^(?:noncomputable\s+)?(?:public\s+)?section\b", st):
            stack.append(("sec", None))
            continue
        m = re.match(r"^end(?:\s+(\S+))?\s*$", st)
        if m and stack:
            stack.pop()
            continue
        for m in re.finditer(r"(?:^|\s|\()(?:open|export)\s+(?:scoped\s+)?(.*?)(?:\s+in\b|$)", line):
            body = re.split(r"\s(?:hiding|renaming)\s|\(|=>|:=", m.group(1))[0]
            cur = [c for kind, cs in stack if kind == "ns" for c in cs]
            for ident in body.split():
                ident = ident.strip("«»")
                if not re.match(r"^[A-Za-z_][\w.'!?]*$", ident):
                    break
                cands = [".".join(cur[:k] + [ident]) for k in range(len(cur), 0, -1)] + [ident]
                out.append(cands)
    return out


def topo(imports):
    order, seen = [], set()
    for m in imports:
        stack = [(m, iter(imports[m]))]
        if m in seen:
            continue
        seen.add(m)
        while stack:
            n, it = stack[-1]
            for c in it:
                if c not in seen and c in imports:
                    seen.add(c)
                    stack.append((c, iter(imports[c])))
                    break
            else:
                stack.pop()
                order.append(n)
    return order


class Bits:
    def __init__(self, names):
        self.idx = {n: i for i, n in enumerate(names)}
        self.names = names

    def of(self, it):
        v = 0
        for n in it:
            if n in self.idx:
                v |= 1 << self.idx[n]
        return v

    def members(self, v):
        out, i = [], 0
        while v:
            if v & 1:
                out.append(self.names[i])
            v >>= 1
            i += 1
        return out


def closures(imports, order, B):
    clos = {}
    for m in order:
        c = 0
        for i in imports[m]:
            if i in clos:
                c |= clos[i] | (1 << B.idx[i])
        clos[m] = c
    return clos


AUX = {"below", "brecOn", "rec", "recOn", "casesOn", "injEq", "inj", "elim", "noConfusion",
       "noConfusionType", "ctorIdx", "mk", "sizeOf_spec", "binductionOn", "ibelow", "ctorElim",
       "ctorElimType", "toCtorIdx", "ofNat", "eq_def", "go", "loop", "pure", "bind", "map",
       "get", "set", "step", "level", "read", "write", "init", "none", "some", "val", "cons"}


def interesting(d):
    parts = d.split(".")
    if any(p in AUX or p.startswith(("match_", "proof_", "eq_", "_")) for p in parts[1:]):
        return None
    last = parts[-1].strip("«»")
    return last if len(last) >= 5 else None


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def ident_tokens(text):
    text = strip_comments(text)
    toks = set()
    for t in re.findall(r"[A-Za-z_À-ɏͰ-Ͽ«][\w'!?.«»À-ɏͰ-Ͽ]*", text):
        for p in t.split("."):
            p = p.strip("«»")
            if p:
                toks.add(p)
    return toks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("needs")
    ap.add_argument("--src", required=True, help="repo root holding the analysed sources")
    ap.add_argument("--out", required=True)
    ap.add_argument("--pkg-root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    help="repo root whose .lake/packages holds the git dependencies")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)

    imports, needs, decls, rev_keep = load(a.needs)
    order = topo(imports)
    B = Bits(order)
    clos = closures(imports, order, B)
    bit = lambda m: 1 << B.idx[m]

    def is_edit(m):
        return root(m) in LOCAL and m not in UMBRELLA

    # filter needs: indirect uses only count inside the original closure (as lake shake does)
    need_bits = {}
    for m in order:
        if root(m) not in LOCAL:
            continue
        nb = 0
        for j, (kind, *_rest) in needs[m].items():
            if j not in B.idx:
                continue
            if kind in ("indirect", "dup", "quote") and not (clos[m] >> B.idx[j]) & 1:
                continue
            nb |= bit(j)
        for k in rev_keep:
            if (clos[m] >> B.idx[k]) & 1:
                nb |= bit(k)
        bad = nb & ~clos[m]
        if bad:
            print(f"warning: {m} needs modules outside its closure: {B.members(bad)[:5]}", file=sys.stderr)
        need_bits[m] = nb & clos[m]

    # only Init.* comes for free (the implicit prelude import); Lean.*/Std.* modules a file
    # needs must stay reachable through its imports like any other module
    core_bits = B.of(n for n in order if root(n) == "Init")

    # file paths for text checks
    def path_of(m):
        r = root(m)
        rel = m.replace(".", "/") + ".lean"
        if r == "LeanRV64D":
            return os.path.join(a.src, "model/Lean_RV64D", rel)
        if r == "Sail":
            return os.path.join(a.src, "vendor/lean-sail", rel)
        return os.path.join(a.src, rel)

    # namespaces opened by a bare `namespace N ... end N` (no public constants) are invisible
    # in the olean constant tables: scan the sources (local + packages) for them too
    def scan_namespaces(mod, text):
        stack = []
        for line in strip_comments(text).split("\n"):
            st = line.strip()
            mm = re.match(r"^(?:noncomputable\s+)?namespace\s+(\S+)", st)
            if mm:
                stack.append(mm.group(1).split("."))
                full = [c for cs in stack if cs for c in cs]
                for k in range(1, len(full) + 1):
                    NSPROV[".".join(full[:k])].add(mod)
                continue
            if re.match(r"^(?:noncomputable\s+)?(?:public\s+)?section\b", st):
                stack.append([])
                continue
            if re.match(r"^end(\s+\S+)?\s*$", st) and stack:
                stack.pop()
    for m in order:
        if root(m) in LOCAL:
            try:
                scan_namespaces(m, open(path_of(m), encoding="utf-8").read())
            except OSError:
                pass
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import import_graph as ig
    for full, mod, text in ig.package_files(a.pkg_root):
        if mod in B.idx:
            scan_namespaces(mod, text)

    # `open N` needs some module with constants in N to stay in the closure
    open_req = {}
    for m in order:
        if not is_edit(m):
            continue
        try:
            text = open(path_of(m), encoding="utf-8").read()
        except OSError:
            continue
        reqs = []
        for cands in opened_namespaces(text):
            for ns in cands:
                prov = B.of(NSPROV.get(ns, ())) & clos[m]
                own = m in NSPROV.get(ns, ())
                if prov:
                    reqs.append((ns, prov))
                    break
                if own:
                    break
        open_req[m] = reqs

    def opens_ok(m, cov):
        return all(prov & cov for _, prov in open_req.get(m, ()))

    # ---------- (2) dead imports w.r.t. the original graph ----------
    # An import I of m is *dead* when every module m needs is still reachable through m's
    # other imports: removing I (alone, upstream unchanged) cannot lose anything.  Imports
    # are tested greedily, biggest closure first, and a removed one stays removed, so the
    # dead set of a module can be dropped all together.
    #   redundant : I is itself reachable through another import (a no-op edge for the DAG)
    #   high      : I brings modules nobody uses and m's text names none of their decls
    #   manual    : as `high`, but m's text mentions a decl name from those modules
    #               (open/namespace, unused simp args, notation, example, ...)
    dead = []  # (m, imp, cls, detail)
    usage = []
    for m in order:
        if not is_edit(m):
            continue
        nb = need_bits[m] & ~core_bits
        imps = [i for i in imports[m] if i in B.idx]
        cover = {i: bit(i) | clos[i] for i in imps}
        cur = [i for i in imps if root(i) not in CORE]
        text = None
        for i in sorted(cur, key=lambda i: -bin(cover[i]).count("1")):
            others = 0
            for j in imps:
                if j != i:
                    others |= cover[j]
            excl = cover[i] & ~others
            used_excl = excl & nb
            nconst = sum(needs[m].get(j, ("", "", "", 0, []))[3] for j in B.members(used_excl))
            usage.append((m, i, bin(excl).count("1"), bin(cover[i] & nb).count("1"),
                          bin(used_excl).count("1"), nconst,
                          " ".join(B.members(used_excl)[:6])))
        core_cover = 0
        for j in imps:
            if root(j) in CORE:
                core_cover |= cover[j]
        for i in sorted(cur, key=lambda i: -bin(cover[i]).count("1")):
            rest = [j for j in cur if j != i]
            others = core_cover
            for j in rest:
                others |= cover[j]
            if nb & ~others or not opens_ok(m, others):
                continue
            cur = rest
            if not (cover[i] & ~others):
                dead.append((m, i, "redundant", "reachable through another import"))
                continue
            excl = cover[i] & ~others
            if text is None:
                try:
                    text = open(path_of(m), encoding="utf-8").read()
                except OSError:
                    text = ""
                toks = ident_tokens(text)
            hits, ext = set(), []
            for j in B.members(excl):
                if j in decls:
                    for d in decls[j]:
                        last = interesting(d)
                        if last and last in toks:
                            hits.add(d)
                elif root(j) not in CORE:
                    ext.append(j)
            flags = [f"drops {bin(excl).count('1')} modules from m's closure"]
            if hits:
                flags.append("names mentioned: " + ", ".join(sorted(hits)[:6]))
            if re.search(r"^\s*example\b", text, re.M):
                flags.append("has `example`")
            if ext:
                flags.append(f"{len(ext)} external modules (e.g. {ext[0]})")
            dead.append((m, i, "manual" if hits else "high", "; ".join(flags)))

    with open(os.path.join(a.out, "dead.txt"), "w") as f:
        for cls in ("high", "manual", "redundant"):
            rows = [d for d in dead if d[2] == cls]
            f.write(f"## {cls}: {len(rows)}\n")
            for m, i, _, det in rows:
                f.write(f"{m}\t{i}\t{det}\n")
    with open(os.path.join(a.out, "usage.tsv"), "w") as f:
        f.write("module\timport\t#exclusive_mods\t#needed_via\t#needed_exclusive\t#consts_exclusive\texamples\n")
        for r in usage:
            f.write("\t".join(map(str, r)) + "\n")

    # ---------- edited graphs ----------
    def rewrite(mode):
        newimp = {}
        newclos = {}
        edits = []
        for m in order:
            if not is_edit(m):
                newimp[m] = imports[m]
            else:
                nb = need_bits[m]
                old = [i for i in imports[m] if i in B.idx]
                if mode == "dead":
                    keep = list(old)
                    nbx = nb & ~core_bits
                    for i in sorted([i for i in old if root(i) not in CORE],
                                    key=lambda i: -bin(newclos[i]).count("1")):
                        others = 0
                        for j in keep:
                            if j != i:
                                others |= bit(j) | newclos[j]
                        if not (nbx & ~others) and opens_ok(m, others):
                            keep.remove(i)
                else:  # exact: maximal elements of the needs (plus core imports kept as-is)
                    keep = [i for i in old if root(i) in CORE]
                got = 0
                for i in keep:
                    got |= bit(i) | newclos[i]
                missing = nb & ~got & ~core_bits
                if mode == "exact":
                    missing = nb & ~core_bits
                # add the maximal missing modules
                ms = B.members(missing)
                implied = 0
                for n in ms:
                    implied |= newclos[n]
                adds = [n for n in ms if not (implied >> B.idx[n]) & 1 and not (got >> B.idx[n]) & 1]
                cov = got
                for n in adds:
                    cov |= bit(n) | newclos[n]
                for ns, prov in open_req.get(m, ()):
                    if not (prov & cov):
                        # cheapest provider of the namespace
                        best = min(B.members(prov), key=lambda x: bin(newclos[x]).count("1"))
                        adds.append(best)
                        cov |= bit(best) | newclos[best]
                newimp[m] = keep + adds
                for i in old:
                    if i not in newimp[m]:
                        edits.append(f"{m} -{i}")
                for n in adds:
                    if n not in old:
                        edits.append(f"{m} +{n}")
            c = 0
            for i in newimp[m]:
                if i in newclos:
                    c |= newclos[i] | bit(i)
            newclos[m] = c
            if is_edit(m):
                lost = need_bits[m] & ~c & ~core_bits
                if lost:
                    print(f"BUG {mode}: {m} loses {B.members(lost)[:3]}", file=sys.stderr)
        return edits

    for mode in ("dead", "exact"):
        ed = rewrite(mode)
        with open(os.path.join(a.out, f"edits_{mode}.txt"), "w") as f:
            f.write("\n".join(ed) + "\n")
        nrm = sum(1 for e in ed if " -" in e)
        nad = sum(1 for e in ed if " +" in e)
        print(f"{mode}: -{nrm} +{nad} imports over {len({e.split()[0] for e in ed})} modules")
    cnt = collections.Counter(d[2] for d in dead)
    print("dead imports (original graph):", dict(cnt))


if __name__ == "__main__":
    main()

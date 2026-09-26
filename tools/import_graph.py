#!/usr/bin/env python3
"""Module import graph + critical-path analysis for the lean-xv6 build.

Usage:
  tools/import_graph.py --log BUILD.log [--root DIR] [--git-rev REV]
                        [--prune SHAKE.txt] [--move EDITS.txt] [--cores N ...]
                        [--json OUT.json]

  --log      a `lake build` log with lines `✔ [n/N] Built Mod.Name (12s)`
             (per-module times; modules missing from the log count as 0s).
  --root     repo root to read sources from (default: the script's repo).
  --git-rev  read sources via `git show REV:path` instead of the work tree
             (for analysing the committed tree while others edit files).
  --prune    output of `lake shake` (text form: "Mod:\n  remove #[A, B]\n
             add #[C]" or the `--gh-style` form); the graph is rewritten
             with those removals/additions and the critical path recomputed.
  --move     hypothetical edit file, lines `Mod -Imp` / `Mod +Imp` /
             `Mod =T` (set Mod's build time to T seconds);  for what-if runs.
  --cores    list-schedule the graph on N cores (default 32 96) and report
             the simulated makespan.

Sources: every .lean under MachCSL/, Xv6/, model/Lean_RV64D/LeanRV64D,
vendor/lean-sail/Sail and the packages in .lake/packages (Iris, Batteries,
Qq). Init/Lean/Std/Lake modules are toolchain modules with time 0.
"""
import argparse, collections, heapq, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SRC_ROOTS = [  # (dir relative to repo root, module prefix dir)
    ("", ["MachCSL", "Xv6", "MachCSL.lean", "Xv6.lean"]),
    ("model/Lean_RV64D", ["LeanRV64D", "LeanRV64D.lean"]),
    ("vendor/lean-sail", ["Sail", "Sail.lean"]),
]
IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([^\s-]+)")


def time_of(s):
    m = re.fullmatch(r"([0-9.]+)(ms|s|m)", s)
    if not m:
        # e.g. "1m 5s"
        tot = 0.0
        for v, u in re.findall(r"([0-9.]+)(ms|s|m)\b", s):
            tot += float(v) * {"ms": 0.001, "s": 1, "m": 60}[u]
        return tot
    v, u = float(m.group(1)), m.group(2)
    return v * {"ms": 0.001, "s": 1, "m": 60}[u]


def read_times(log):
    t = {}
    for line in open(log, encoding="utf-8", errors="replace"):
        m = re.search(r"Built (\S+) \(([^)]*)\)", line)
        if m:
            t[m.group(1)] = time_of(m.group(2))
    return t


def parse_imports(text):
    imps = []
    in_comment = 0
    for line in text.splitlines():
        s = line
        # crude block-comment skip (header region only matters)
        if in_comment:
            if "-/" in s:
                in_comment = 0
                s = s.split("-/", 1)[1]
            else:
                continue
        if s.strip().startswith("/-") and "-/" not in s:
            in_comment = 1
            continue
        m = IMPORT_RE.match(s)
        if m:
            imps.append(m.group(1))
            continue
        st = s.strip()
        if st == "" or st.startswith("--") or st.startswith("/-") or st.startswith("prelude") or st.startswith("module"):
            continue
        break  # header over
    return imps


def list_files(root, rev):
    """Yield (relpath_from_repo_root, module_name, text)."""
    out = []
    if rev:
        files = subprocess.run(["git", "-C", root, "ls-tree", "-r", "--name-only", rev],
                               capture_output=True, text=True, check=True).stdout.split()
        fileset = files
        def read(p):
            return subprocess.run(["git", "-C", root, "show", f"{rev}:{p}"],
                                  capture_output=True, text=True, check=True).stdout
    else:
        fileset = []
        for base, tops in SRC_ROOTS:
            for top in tops:
                p = os.path.join(root, base, top)
                if os.path.isfile(p):
                    fileset.append(os.path.relpath(p, root))
                elif os.path.isdir(p):
                    for dp, _, fs in os.walk(p):
                        for f in fs:
                            if f.endswith(".lean"):
                                fileset.append(os.path.relpath(os.path.join(dp, f), root))
        def read(p):
            return open(os.path.join(root, p), encoding="utf-8").read()
    # batch read via cat-file for speed when rev given
    wanted = []
    for p in fileset:
        if not p.endswith(".lean"):
            continue
        for base, tops in SRC_ROOTS:
            rel = p[len(base) + 1:] if base else p
            if base and not p.startswith(base + "/"):
                continue
            if any(rel == t or rel.startswith(t + "/") for t in tops):
                wanted.append((p, rel[:-5].replace("/", ".")))
                break
    if rev:
        inp = "".join(f"{rev}:{p}\n" for p, _ in wanted)
        proc = subprocess.run(["git", "-C", root, "cat-file", "--batch"], input=inp.encode(),
                              capture_output=True, check=True).stdout
        i = 0
        for p, mod in wanted:
            nl = proc.index(b"\n", i)
            hdr = proc[i:nl].split()
            size = int(hdr[2])
            text = proc[nl + 1: nl + 1 + size].decode("utf-8", "replace")
            i = nl + 1 + size + 1
            out.append((p, mod, text))
    else:
        for p, mod in wanted:
            out.append((p, mod, read(p)))
    return out


PKG_ROOTS = [".lake/packages/iris/Iris", ".lake/packages/batteries", ".lake/packages/Qq"]


def package_files(root):
    """External git packages (source roots listed in PKG_ROOTS)."""
    out = []
    for pr in PKG_ROOTS:
        base = os.path.join(root, pr)
        if not os.path.isdir(base):
            continue
        for dp, dns, fs in os.walk(base):
            dns[:] = [d for d in dns if d not in (".lake", ".git")]
            for f in fs:
                if not f.endswith(".lean") or f.startswith("lakefile"):
                    continue
                full = os.path.join(dp, f)
                mod = os.path.relpath(full, base)[:-5].replace(os.sep, ".")
                out.append((full, mod, open(full, encoding="utf-8", errors="replace").read()))
    return out


def build_graph(root, rev):
    g = {}
    local = set()
    for p, mod, text in list_files(root, rev):
        g[mod] = parse_imports(text)
        local.add(mod)
    for p, mod, text in package_files(root):
        if mod not in g:
            g[mod] = parse_imports(text)
    return g, local


def is_core(m):
    return m.split(".")[0] in ("Init", "Lean", "Std", "Lake")


def restrict(g, targets):
    """Keep only modules reachable from targets (and non-core)."""
    seen, stack = set(), list(targets)
    while stack:
        m = stack.pop()
        if m in seen or is_core(m) or m not in g:
            continue
        seen.add(m)
        stack.extend(g[m])
    return {m: [i for i in g[m] if i in seen] for m in seen}


def topo(g):
    indeg = {m: 0 for m in g}
    rev = collections.defaultdict(list)
    for m, imps in g.items():
        for i in imps:
            rev[i].append(m)
            indeg[m] += 1
    q = [m for m in g if indeg[m] == 0]
    order = []
    while q:
        m = q.pop()
        order.append(m)
        for u in rev[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                q.append(u)
    if len(order) != len(g):
        raise SystemExit("cycle in import graph")
    return order, rev


def critical(g, t):
    order, rev = topo(g)
    ef, pred = {}, {}
    for m in order:
        best, bp = 0.0, None
        for i in g[m]:
            if ef[i] > best:
                best, bp = ef[i], i
        ef[m] = best + t.get(m, 0.0)
        pred[m] = bp
    end = max(ef, key=ef.get)
    total = ef[end]
    # latest finish / slack
    lf = {}
    for m in reversed(order):
        lf[m] = min([lf[u] - t.get(u, 0.0) for u in rev[m]], default=total)
    slack = {m: lf[m] - ef[m] for m in g}
    path = []
    m = end
    while m:
        path.append(m)
        m = pred[m]
    path.reverse()
    return total, path, ef, slack, order, rev


def depth_profile(g, order):
    d = {}
    for m in order:
        d[m] = 1 + max([d[i] for i in g[m]], default=-1)
    prof = collections.Counter(d.values())
    return d, [prof[k] for k in range(max(prof) + 1)]


def schedule(g, t, order, rev, cores):
    """List scheduling (priority = longest remaining path), returns makespan."""
    # bottom level
    bl = {}
    for m in reversed(order):
        bl[m] = t.get(m, 0.0) + max([bl[u] for u in rev[m]], default=0.0)
    indeg = {m: len(g[m]) for m in g}
    ready = [(-bl[m], m) for m in g if indeg[m] == 0]
    heapq.heapify(ready)
    running = []  # (finish, m)
    now, busy_time = 0.0, 0.0
    while ready or running:
        while ready and len(running) < cores:
            _, m = heapq.heappop(ready)
            heapq.heappush(running, (now + t.get(m, 0.0), m))
        fin, m = heapq.heappop(running)
        now = fin
        for u in rev[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                heapq.heappush(ready, (-bl[u], u))
    return now


def concurrency_profile(g, t, ef, buckets=20):
    """With unbounded cores and ASAP start: how many modules run in each time slice."""
    total = max(ef.values())
    w = total / buckets
    prof = [0.0] * buckets
    for m in g:
        s, f = ef[m] - t.get(m, 0.0), ef[m]
        for b in range(buckets):
            lo, hi = b * w, (b + 1) * w
            ov = max(0.0, min(hi, f) - max(lo, s))
            prof[b] += ov / w
    return w, prof


def parse_shake(path):
    """Return {mod: (removes, adds)} from `lake shake` output."""
    edits = collections.defaultdict(lambda: (set(), set()))
    cur = None
    for line in open(path, encoding="utf-8", errors="replace"):
        m = re.match(r"^(\S+):\s*$", line.rstrip())
        if m and "/" not in m.group(1):
            cur = m.group(1)
            continue
        m = re.match(r"^\s*(remove|add)\s+#\[(.*)\]", line)
        if m and cur:
            mods = [x.strip() for x in m.group(2).split(",") if x.strip()]
            mods = [re.sub(r"^(public |meta |private )*(import )?(all )?", "", x) for x in mods]
            (edits[cur][0] if m.group(1) == "remove" else edits[cur][1]).update(mods)
    return edits


def parse_moves(path):
    edits = collections.defaultdict(lambda: (set(), set()))
    times = {}
    for line in open(path):
        line = line.split("#")[0].strip()
        if not line:
            continue
        mod, op = line.split()
        if op[0] == "-":
            edits[mod][0].add(op[1:])
        elif op[0] == "+":
            edits[mod][1].add(op[1:])
        elif op[0] == "=":
            times[mod] = float(op[1:])
    return edits, times


def apply_edits(g, edits):
    g2 = {m: list(v) for m, v in g.items()}
    for m, (rm, add) in edits.items():
        if m not in g2:
            continue
        g2[m] = [i for i in g2[m] if i not in rm] + [a for a in add if a in g2 and a not in g2[m]]
    return g2


def report(g, t, local, cores, label):
    total, path, ef, slack, order, rev = critical(g, t)
    print(f"\n==== {label} ====")
    print(f"modules: {len(g)}  total CPU: {sum(t.get(m,0) for m in g):.0f}s  "
          f"critical path: {total:.1f}s  (ideal parallelism {sum(t.get(m,0) for m in g)/total:.1f})")
    for c in cores:
        print(f"  list-schedule on {c} cores: {schedule(g, t, order, rev, c):.1f}s")
    print("critical path:")
    cum = 0.0
    for m in path:
        cum += t.get(m, 0.0)
        print(f"  {m:55s} {t.get(m,0):7.2f}s  cum {cum:7.1f}s  imports={len(g[m])}")
    return total, path, ef, slack, order, rev


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", required=True)
    ap.add_argument("--root", default=HERE)
    ap.add_argument("--git-rev")
    ap.add_argument("--targets", nargs="*", default=["MachCSL", "Xv6"])
    ap.add_argument("--prune")
    ap.add_argument("--move")
    ap.add_argument("--cores", nargs="*", type=int, default=[32, 96])
    ap.add_argument("--json")
    ap.add_argument("--top", type=int, default=20)
    a = ap.parse_args()

    t = read_times(a.log)
    gfull, local = build_graph(a.root, a.git_rev)
    g = restrict(gfull, a.targets)
    missing = [m for m in g if m not in t]
    total, path, ef, slack, order, rev = report(g, t, local, a.cores, "CURRENT GRAPH")
    print(f"(modules with no time in log, counted 0s: {len(missing)}; e.g. {missing[:5]})")

    # zero-slack modules by time
    zs = sorted([m for m in g if slack[m] < 0.5], key=lambda m: -t.get(m, 0))
    print(f"\ntop-{a.top} zero-slack (critical) modules by own time:")
    for m in zs[:a.top]:
        print(f"  {m:55s} {t.get(m,0):6.1f}s  finish@{ef[m]:6.1f}s")
    # near-critical: slack < 10s, ranked by time
    nc = sorted([m for m in g if 0.5 <= slack[m] < 10], key=lambda m: -t.get(m, 0))
    print(f"\nnear-critical modules (slack < 10s) by own time:")
    for m in nc[:a.top]:
        print(f"  {m:55s} {t.get(m,0):6.1f}s  slack {slack[m]:5.1f}s")

    d, prof = depth_profile(g, order)
    print("\nwidth profile (modules per import-depth level):")
    for k, n in enumerate(prof):
        tsum = sum(t.get(m, 0) for m in g if d[m] == k)
        print(f"  depth {k:3d}: {n:4d} modules  {tsum:7.1f}s CPU")
    w, cp = concurrency_profile(g, t, ef, 30)
    print(f"\nconcurrency profile (infinite cores, ASAP; {w:.1f}s slices): avg #modules running")
    for b, v in enumerate(cp):
        print(f"  t={b*w:6.1f}s  {v:6.1f}  " + "#" * int(round(v / 2)))

    # descendant counts (how many modules transitively depend on m)
    desc = {}
    for m in reversed(order):
        s = set()
        for u in rev[m]:
            s.add(u)
            s |= desc[u]
        desc[m] = s
    print("\nhubs on the critical path (fan-out):")
    for m in path:
        print(f"  {m:55s} direct importers {len(rev[m]):4d}  transitive dependents {len(desc[m]):5d}")
    del desc

    res = {"critical": total, "path": path}
    if a.prune or a.move:
        edits = collections.defaultdict(lambda: (set(), set()))
        times = dict(t)
        if a.prune:
            for m, (r, ad) in parse_shake(a.prune).items():
                edits[m][0].update(r); edits[m][1].update(ad)
        if a.move:
            e2, tt = parse_moves(a.move)
            for m, (r, ad) in e2.items():
                edits[m][0].update(r); edits[m][1].update(ad)
            times.update(tt)
        g2 = apply_edits(g, edits)
        nrm = sum(len(r) for r, _ in edits.values())
        nad = sum(len(ad) for _, ad in edits.values())
        print(f"\n(edits applied: {len(edits)} modules, -{nrm} imports, +{nad} imports)")
        g2 = restrict(g2, a.targets)
        total2, path2, *_ = report(g2, times, local, a.cores, "EDITED GRAPH")
        res.update({"critical_edited": total2, "path_edited": path2})
    if a.json:
        json.dump(res, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()

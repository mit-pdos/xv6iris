#!/usr/bin/env python3
"""Proof-build profiler for the Lean tree (Rocq counterpart: tools/proof_profile.py
on main, fed by `make TIMED=1`).

Consumes a `lake build` log and the import graph and reports where the
wall-clock goes:

  * wall span, ΣCPU, Σ of per-module wall, average / peak parallelism and the
    effectively-serial seconds;
  * the most expensive modules -- from lake's own `✔ [i/N] Built M (12s)`;
  * the longest dependency chain -- the critical path through the import DAG
    (every module weighted by its time).  The build is critical-path bound,
    not core bound: extra cores cannot beat the longest weighted import chain;
  * parallelism over time -- how many modules are being compiled at each
    instant (start = finish - wall), as an inline Unicode chart.

THE LOG.  A plain `lake build` log has the per-module times and is enough
for the module table and the critical path.  The wall span, ΣCPU and the
parallelism chart need the TIMED log that tools/ci/timed_build.sh writes
(each line prefixed `@<epoch>`, framed by `@start`/`@cpu`/`@end`); without
it those rows say so instead of guessing.  The log must be of a CLEAN build
(`timed_build.sh LOG --clean`): an incremental log only lists what was stale.

THE GRAPH is read from the sources' `import` lines (tools/import_graph.py):
Xv6/, MachCSL/, the model, lean-sail, and the fetched packages under
.lake/packages.  Toolchain modules (Init/Lean/Std) take no build time.

Differences from the Rocq tool, all forced by what lake reports: there is no
per-statement table (lake times modules, not commands) and no per-module CPU
(the `(12s)` is wall; ΣCPU is the whole build's, from `times`).

Usage:
    tools/proof_profile.py --build-log LOG [--repo DIR] [--out-dir DIR] [--top N] [--jobs N]

Stdlib only.  INFORMATIONAL: always exits 0 -- a missing input degrades to a
partial report, never to a failed step.
"""
import argparse
import importlib.util
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

NUM = r"\d+(?:\.\d+)?"
STAMP_RE = re.compile(rf"^@({NUM}) ?(.*)$")
# `✔ [324/2657] Built MachCSL.Dev.DevIds (260ms)`; the mark may be ✔ ⚠ ✖ or absent
BUILT_RE = re.compile(rf"\[\d+/\d+\] Built (\S+) \(((?:{NUM}(?:ms|s|m|h) ?)+)\)\s*$")
UNIT = {"ms": 0.001, "s": 1.0, "m": 60.0, "h": 3600.0}


def time_of(s):
    """`260ms` / `6.9s` / `1m 5s` -> seconds."""
    parts = re.findall(rf"({NUM})(ms|s|m|h)", s)
    if not parts:
        raise ValueError(s)
    return sum(float(v) * UNIT[u] for v, u in parts)


def parse_build_log(path):
    """-> dict(times, finish, start, end, cpu, nproc, dropped, rc).

    times[module] = wall seconds (lake's own figure); finish[module] = the
    epoch its line arrived (timed logs only).  A line that mentions a built
    module but does not parse is COUNTED, never guessed at: dropped rows
    would silently understate every total."""
    out = dict(times={}, finish={}, start=None, end=None, cpu=None, nproc=None,
               dropped=0, rc=None)
    if not path or not os.path.exists(path):
        return out
    with open(path, encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.rstrip("\n")
            stamp = None
            m = STAMP_RE.match(line)
            if m:
                stamp, line = float(m.group(1)), m.group(2)
            elif line.startswith("@start "):
                p = line.split()
                out["start"] = float(p[1])
                for kv in p[2:]:
                    if kv.startswith("nproc="):
                        out["nproc"] = int(kv[6:])
                continue
            elif line.startswith("@end "):
                p = line.split()
                out["end"] = float(p[1])
                for kv in p[2:]:
                    if kv.startswith("rc="):
                        out["rc"] = int(kv[3:])
                continue
            elif line.startswith("@cpu "):
                kv = dict(x.split("=") for x in line.split()[1:])
                out["cpu"] = float(kv.get("user", 0)) + float(kv.get("sys", 0))
                continue
            if "] Built " not in line:
                continue
            m = BUILT_RE.search(line)
            if not m or ":" in m.group(1):
                out["dropped"] += 1
                continue
            out["times"][m.group(1)] = time_of(m.group(2))
            if stamp is not None:
                out["finish"][m.group(1)] = stamp
    return out


def load_import_graph(repo, targets):
    """The import DAG of everything the targets reach, via tools/import_graph.py.
    -> (graph or None, note).  Failure is informational."""
    script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "import_graph.py")
    if not os.path.isfile(script):
        return None, "`tools/import_graph.py` was not found"
    try:
        spec = importlib.util.spec_from_file_location("_profile_import_graph", script)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        gfull, _local = mod.build_graph(repo, None)
        g = mod.restrict(gfull, targets)
        note = None
        if not any(os.path.isdir(os.path.join(repo, p)) for p in mod.PKG_ROOTS):
            note = ("the fetched packages (.lake/packages) are not in this checkout, so the "
                    "chain starts at the first local module")
        return g, note
    except (Exception, SystemExit) as e:     # informational: degrade, do not fail
        return None, f"import graph unavailable: {type(e).__name__}: {e}"


def critical_path(g, t):
    """finish[m] = t[m] + max over imports.  -> (finish, pred).  Iterative: the
    chain is hundreds of modules deep."""
    finish, pred = {}, {}
    nodes = set(g) | set(t)
    for root in nodes:
        if root in finish:
            continue
        stack = [(root, iter(g.get(root, ())))]
        onstack = {root}
        while stack:
            n, it = stack[-1]
            adv = False
            for d in it:
                if d in finish or d in onstack or d not in nodes:
                    continue
                stack.append((d, iter(g.get(d, ()))))
                onstack.add(d)
                adv = True
                break
            if adv:
                continue
            best, bp = 0.0, None
            for d in g.get(n, ()):
                fd = finish.get(d)
                if fd is not None and fd > best:
                    best, bp = fd, d
            finish[n] = t.get(n, 0.0) + best
            pred[n] = bp
            stack.pop()
            onstack.discard(n)
    return finish, pred


def path_to(end, pred):
    chain, cur = [], end
    while cur is not None:
        chain.append(cur)
        cur = pred.get(cur)
    chain.reverse()
    return chain


def build_timeline(times, finish, start=None):
    """[(module, start, end)] with t=0 at the build start -> (intervals, span)."""
    iv = [[m, finish[m] - times[m], finish[m]] for m in times if m in finish]
    if not iv:
        return [], 0.0
    t0 = start if start is not None else min(x[1] for x in iv)
    for x in iv:
        x[1] = max(0.0, x[1] - t0)
        x[2] = max(x[1], x[2] - t0)
    return iv, max(x[2] for x in iv)


def concurrency_steps(intervals):
    events = []
    for _, s, e in intervals:
        events.append((s, +1))
        events.append((e, -1))
    events.sort()
    steps, cur = [], 0
    for t, d in events:
        cur += d
        if steps and steps[-1][0] == t:
            steps[-1] = (t, cur)
        else:
            steps.append((t, cur))
    return steps


def serial_seconds(steps, span):
    tot = 0.0
    if steps and steps[0][0] > 0:
        tot += steps[0][0]
    for i, (t, c) in enumerate(steps):
        nt = steps[i + 1][0] if i + 1 < len(steps) else span
        if c <= 1:
            tot += max(0.0, nt - t)
    return tot


def render_ascii(steps, span, width=70, height=12):
    """Block chart of modules-in-flight vs time (renders inline in a CI step
    summary, where an image cannot)."""
    if not steps or span <= 0:
        return "(no timeline data)"
    ymax = max(max(c for _, c in steps), 1)
    segs = []
    for i, (t, c) in enumerate(steps):
        segs.append((t, steps[i + 1][0] if i + 1 < len(steps) else span, c))

    def avg(a, b):
        if b <= a:
            return 0.0
        return sum(c * (min(b, e) - max(a, s)) for s, e, c in segs if min(b, e) > max(a, s)) / (b - a)

    cols = [avg(span * i / width, span * (i + 1) / width) for i in range(width)]
    blocks = " ▁▂▃▄▅▆▇█"
    out = []
    for r in range(height - 1, -1, -1):
        line = []
        for v in cols:
            cell = int(round(v / ymax * height * 8 - r * 8))
            line.append(blocks[0 if cell < 0 else 8 if cell > 8 else cell])
        out.append((f"{ymax:>3} ┤" if r == height - 1 else "    │") + "".join(line))
    out.append("  0 ┼" + "─" * width)
    end = f"{int(round(span))}s"
    out.append("     0s" + " " * (width - 2 - len(end)) + end)
    return "\n".join(out)


def md_table(headers, rows):
    def cell(c):
        return str(c).replace("|", "\\|")
    out = ["| " + " | ".join(cell(h) for h in headers) + " |",
           "|" + "|".join("---" for _ in headers) + "|"]
    out += ["| " + " | ".join(cell(c) for c in r) + " |" for r in rows]
    return "\n".join(out)


def package_of(m):
    return m.split(".")[0]


def report(log, g, graph_note, top=30, jobs=None):
    t = log["times"]
    finish, pred = critical_path(g or {}, t) if g is not None else ({}, {})
    chain = path_to(max(finish, key=lambda n: finish[n]), pred) if finish else []
    crit = finish[chain[-1]] if chain else 0.0
    intervals, tl_span = build_timeline(t, log["finish"], log["start"])
    steps = concurrency_steps(intervals)
    span = (log["end"] - log["start"]) if (log["start"] and log["end"]) else tl_span
    total = sum(t.values())
    peak = max([c for _, c in steps], default=0)
    jobs = jobs or log["nproc"]

    md = ["## Proof build profile (Lean: `lake build Xv6 MachCSL`)\n"]
    wall = f"**wall span** {span:.0f}s" if span else "**wall span** n/a (plain log; use `tools/ci/timed_build.sh`)"
    cpu = f"**ΣCPU** {log['cpu']:.0f}s" if log["cpu"] is not None else "**ΣCPU** n/a"
    md.append(f"- {wall}  ·  {cpu}  ·  **Σwall** {total:.0f}s (per-module)  ·  "
              f"**critical path** {crit:.0f}s ({len(chain)} modules)")
    if span and steps:
        md.append(f"- **avg parallelism** {total / span:.1f}×  ·  **peak** {peak}×"
                  + (f" (of {jobs} cores)" if jobs else "")
                  + f"  ·  **~{serial_seconds(steps, span):.0f}s effectively serial** (≤1 module in flight)")
    line = f"- {len(t)} modules timed"
    if g is not None:
        line += f" · {len(g)} in the import graph · {sum(1 for m in g if m not in t)} of them not in the log"
    if log["dropped"]:
        line += (f" · **{log['dropped']} `Built` line(s) dropped** (unparseable, so the totals "
                 "are short by that much)")
    if log["rc"] not in (None, 0):
        line += f" · **the build FAILED (rc={log['rc']})**, so this profile is partial"
    md.append(line + "\n")

    by_pkg = {}
    for m, s in t.items():
        e = by_pkg.setdefault(package_of(m), [0, 0.0])
        e[0] += 1
        e[1] += s
    md.append("\n### Where the time is\n")
    md.append(md_table(["library", "modules", "Σwall", "share"],
                       [[f"`{p}`", n, f"{s:.0f}s", f"{100 * s / total:.0f}%" if total else "-"]
                        for p, (n, s) in sorted(by_pkg.items(), key=lambda kv: -kv[1][1])]))

    onpath = set(chain)
    md.append("\n### Most expensive modules\n")
    md.append("`wall` is lake's own per-module figure for this run (it includes contention with "
              "the other jobs, so compare runs with care).\n")
    rows = [[f"{s:.1f}", f"`{m}`", "●" if m in onpath else ""]
            for m, s in sorted(t.items(), key=lambda x: -x[1])[:top]]
    md.append(md_table(["wall", "module", "crit"], rows) if rows else "_no per-module times in the log_")

    md.append("\n### Longest dependency chain (critical path)\n")
    if chain:
        md.append("Each row imports the row above it; `cum` is the earliest instant the module "
                  "can finish, however many cores there are.\n")
        if graph_note:
            md.append(f"_Note: {graph_note}._\n")
        rows, cum, skipped = [], 0.0, 0
        for n in chain:
            s = t.get(n, 0.0)
            cum += s
            # the long run of sub-second modules in the middle of a chain is noise
            if s < 0.5 and n != chain[-1]:
                skipped += 1
                continue
            rows.append([f"{s:.1f}", f"{cum:.1f}", f"`{n}`"])
        md.append(md_table(["wall", "cum", "module"], rows))
        if skipped:
            md.append(f"\n({skipped} modules under 0.5s on the chain are not listed; "
                      "`cum` includes them.)")
        others = sorted(((finish[n], n) for n in finish if n not in onpath), reverse=True)
        if others:
            md.append("\n**Other deep chains** (longest path ending at each module, off the critical path):\n")
            md.append(md_table(["chain len", "ends at"], [[f"{f:.1f}", f"`{n}`"] for f, n in others[:10]]))
    else:
        md.append(f"_no dependency data{': ' + graph_note if graph_note else ''}_")

    md.append("\n### Parallelism over time\n")
    if steps:
        md.append(f"modules in flight (peak {peak}× · avg {total / span:.1f}×"
                  + (f" · {jobs} cores" if jobs else "") + "):\n")
        md.append("```\n" + render_ascii(steps, span) + "\n```")
    else:
        md.append("_no timestamps in the log (build with `tools/ci/timed_build.sh`)_")
    summary = (f"profile: wall {span:.0f}s, ΣCPU "
               + (f"{log['cpu']:.0f}s" if log["cpu"] is not None else "n/a")
               + f", Σwall {total:.0f}s, critical path {crit:.0f}s over {len(chain)} modules, "
               + f"{len(t)} modules timed")
    return "\n".join(md) + "\n", summary


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build-log", required=True)
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--out-dir", default=None, help="write report.md here (default: stdout only)")
    ap.add_argument("--targets", nargs="*", default=["MachCSL", "Xv6"])
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument("--jobs", type=int, default=None)
    a = ap.parse_args(argv)
    try:
        log = parse_build_log(a.build_log)
        if not os.path.exists(a.build_log):
            print(f"profile: {a.build_log} does not exist; nothing to report", file=sys.stderr)
        g, note = load_import_graph(os.path.abspath(a.repo), a.targets)
        md, summary = report(log, g, note, top=a.top, jobs=a.jobs)
        if a.out_dir:
            os.makedirs(a.out_dir, exist_ok=True)
            with open(os.path.join(a.out_dir, "report.md"), "w") as f:
                f.write(md)
        print(md)
        print(summary, file=sys.stderr)
    except Exception as e:                       # informational: never fail the step
        print(f"profile: could not produce a report: {type(e).__name__}: {e}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Proof-build profiler for iris/.

Consumes the artifacts a *profiled* build leaves behind and emits a report of
where the wall-clock goes:

  * most expensive statements  -- per-sentence, from the `-time-file` output
    (`<file>.v.timing`) that `make TIMING=1` writes;
  * most expensive files       -- per-file wall, from the `Foo.vo (real: T, ...)`
    lines that `make TIMED=1` prints (this is the number that gates the build:
    it INCLUDES the async `Qed` rocqworker, which `coqc -time` does not);
  * longest dependency chains  -- the critical path(s) through the require DAG
    (from coqdep's `.CoqMakefile.d`), each node weighted by its per-file wall;
  * parallelism over time      -- a step plot (SVG, no external deps) of how many
    iris compiles are in flight at each instant, reconstructed from `.vo` mtimes
    (finish) and the per-file wall (start = finish - wall).

The build is critical-path bound, not core bound: extra cores cannot beat the
longest weighted require chain.  So the levers this report surfaces are (a) the
single most expensive statements/files, and (b) whether the critical path is
padded by a needless require edge or a serial tail (low parallelism late in the
build).

Usage:
  tools/proof_profile.py --build-log LOG [--iris-dir iris] [--out-dir DIR]
                         [--deps iris/.CoqMakefile.d] [--top N]

Stdlib only, so it runs on a bare CI runner.  Designed to be informational:
missing inputs degrade to a partial report rather than a crash.
"""

import argparse
import glob
import os
import re
import sys
from collections import defaultdict

# ---------------------------------------------------------------------------
# parsing
# ---------------------------------------------------------------------------

def parse_build_log(path):
    """`Foo.vo (real: 12.34, user: .., sys: .., mem: N ko)` -> {'Foo': 12.34}."""
    real = {}
    if not path or not os.path.exists(path):
        return real
    pat = re.compile(r'(\S+)\.vo \(real: ([\d.]+),')
    with open(path, errors="replace") as f:
        for line in f:
            m = pat.search(line)
            if m and '/' not in m.group(1):
                real[m.group(1)] = float(m.group(2))
    return real


def parse_deps(path):
    """coqdep `.CoqMakefile.d` -> {target: set(local-dep)} over `.vo` rules."""
    deps = defaultdict(set)
    targets = set()
    if not path or not os.path.exists(path):
        return deps, targets
    tgt_re = re.compile(r'([^/\s]+)\.vo$')
    dep_re = re.compile(r'([^/\s]+)\.vo$')
    with open(path, errors="replace") as f:
        for line in f:
            if ':' not in line:
                continue
            lhs, rhs = line.split(':', 1)
            lhs_first = lhs.split()[0] if lhs.split() else ""
            tm = tgt_re.match(lhs_first)
            # only the `.vo` rule (skip the sibling `.vos`/`.vok` rule)
            if not tm or not lhs_first.endswith('.vo'):
                continue
            tgt = tm.group(1)
            targets.add(tgt)
            for tok in rhs.split():
                dm = dep_re.match(tok)
                if dm and dm.group(1) != tgt:
                    deps[tgt].add(dm.group(1))
    return deps, targets


def parse_timings(iris_dir):
    """All `<file>.v.timing` sentences -> list of (secs, file, startchar, cmd)."""
    stmts = []
    files = glob.glob(os.path.join(iris_dir, "*.v.timing"))
    pat = re.compile(r'Chars (\d+) - (\d+) \[(.*?)\] ([\d.]+) secs')
    for tf in files:
        fbase = os.path.basename(tf)[:-len(".v.timing")]
        with open(tf, errors="replace") as f:
            for line in f:
                m = pat.match(line)
                if m:
                    stmts.append((float(m.group(4)), fbase,
                                  int(m.group(1)), m.group(3)))
    return stmts, len(files)


# ---------------------------------------------------------------------------
# analysis
# ---------------------------------------------------------------------------

def critical_path(deps, targets, real):
    """finish[n] = real[n] + max over deps; returns (finish, pred)."""
    finish, pred = {}, {}

    def compute(n, stack):
        if n in finish:
            return finish[n]
        if n in stack:                 # cycle guard (should not happen)
            return real.get(n, 0.0)
        stack.add(n)
        best, bp = 0.0, None
        for d in deps.get(n, ()):
            if d not in targets and d not in real:
                continue               # non-local / unknown dep
            fd = compute(d, stack)
            if fd > best:
                best, bp = fd, d
        stack.discard(n)
        finish[n] = real.get(n, 0.0) + best
        pred[n] = bp
        return finish[n]

    for n in set(targets) | set(real):
        compute(n, set())
    return finish, pred


def path_to(end, pred):
    chain, cur = [], end
    while cur is not None:
        chain.append(cur)
        cur = pred.get(cur)
    chain.reverse()
    return chain


def offset_to_line(iris_dir, cache, fbase, off):
    if fbase not in cache:
        try:
            cache[fbase] = open(os.path.join(iris_dir, fbase + ".v"), "rb").read()
        except OSError:
            cache[fbase] = b""
    return cache[fbase].count(b"\n", 0, off) + 1


def build_timeline(iris_dir, real):
    """[(name, start, end)] with t=0 at the first compile start.

    finish = .vo mtime; start = finish - per-file wall.  Files whose .vo is
    missing (never built) are dropped.
    """
    intervals = []
    for name, dur in real.items():
        vo = os.path.join(iris_dir, name + ".vo")
        try:
            end = os.stat(vo).st_mtime
        except OSError:
            continue
        intervals.append([name, end - dur, end])
    if not intervals:
        return [], 0.0
    t0 = min(iv[1] for iv in intervals)
    for iv in intervals:
        iv[1] -= t0
        iv[2] -= t0
    span = max(iv[2] for iv in intervals)
    return intervals, span


def concurrency_steps(intervals):
    """Sweep line -> [(t, count)] step points (count valid until next t)."""
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


def render_ascii(steps, span, jobs=None, width=70, height=14):
    """Monospace block-chart of concurrency vs time (renders inline in the CI
    step summary, where a real image/SVG can't).  Each column is a time bin;
    bar height is the time-averaged number of compiles in flight over that bin,
    smoothed with the 1/8-block glyphs."""
    if not steps or span <= 0:
        return "(no timeline data)"
    peak = max(c for _, c in steps)
    ymax = max(peak, 1)
    # step function as [start, end, count) segments
    segs = []
    for i, (t, c) in enumerate(steps):
        end = steps[i + 1][0] if i + 1 < len(steps) else span
        segs.append((t, end, c))

    def avg(a, b):                       # time-weighted mean concurrency on [a,b)
        if b <= a:
            return 0.0
        tot = 0.0
        for s, e, c in segs:
            lo, hi = max(a, s), min(b, e)
            if hi > lo:
                tot += c * (hi - lo)
        return tot / (b - a)

    cols = [avg(span * i / width, span * (i + 1) / width) for i in range(width)]
    blocks = " ▁▂▃▄▅▆▇█"                 # 0/8 .. 8/8, filling from the cell bottom
    out = []
    for r in range(height - 1, -1, -1):  # top row down
        line = []
        for v in cols:
            eighths = v / ymax * height * 8
            cell = int(round(eighths - r * 8))
            line.append(blocks[0 if cell < 0 else 8 if cell > 8 else cell])
        lab = f"{ymax:>3} ┤" if r == height - 1 else "    │"
        out.append(lab + "".join(line))
    out.append("  0 ┼" + "─" * width)
    end = f"{int(round(span))}s"
    out.append("     0s" + " " * (width - 2 - len(end)) + end)
    return "\n".join(out)


# ---------------------------------------------------------------------------
# rendering
# ---------------------------------------------------------------------------

def render_svg(steps, span, jobs=None, W=960, H=380):
    """Step-area plot of concurrency vs wall time.  Returns an SVG string."""
    ml, mr, mt, mb = 60, 20, 40, 46
    pw, ph = W - ml - mr, H - mt - mb
    ymax = max([c for _, c in steps] + [1])
    if jobs:
        ymax = max(ymax, jobs)
    xspan = span if span > 0 else 1.0

    def X(t): return ml + pw * (t / xspan)
    def Y(c): return mt + ph * (1 - c / ymax)

    # build the step polyline points
    pts = []
    prev_c = 0
    for i, (t, c) in enumerate(steps):
        pts.append((X(t), Y(prev_c)))   # horizontal to this event's time
        pts.append((X(t), Y(c)))        # vertical step to the new count
        prev_c = c
    pts.append((X(xspan), Y(prev_c)))

    line = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
    area = f"{ml:.1f},{Y(0):.1f} " + line + f" {X(xspan):.1f},{Y(0):.1f}"

    def xticks():
        # ~8 ticks on a "nice" step
        raw = xspan / 8
        mag = 10 ** (len(str(int(raw))) - 1) if raw >= 1 else 1
        step = max(mag, round(raw / mag) * mag)
        out, t = [], 0
        while t <= xspan + 1e-6:
            out.append(t)
            t += step
        return out

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
        f'viewBox="0 0 {W} {H}" font-family="monospace" font-size="12">',
        f'<rect width="{W}" height="{H}" fill="white"/>',
        f'<text x="{ml}" y="22" font-size="15" font-weight="bold">'
        f'iris/ proof build: concurrent compiles over time</text>',
    ]
    # y grid + labels
    yticks = list(range(0, ymax + 1, max(1, ymax // 8)))
    if yticks[-1] != ymax:
        yticks.append(ymax)
    for c in yticks:
        y = Y(c)
        parts.append(f'<line x1="{ml}" y1="{y:.1f}" x2="{W-mr}" y2="{y:.1f}" '
                     f'stroke="#eee"/>')
        parts.append(f'<text x="{ml-8}" y="{y+4:.1f}" text-anchor="end" '
                     f'fill="#555">{c}</text>')
    # x ticks
    for t in xticks():
        x = X(t)
        parts.append(f'<line x1="{x:.1f}" y1="{mt}" x2="{x:.1f}" y2="{mt+ph}" '
                     f'stroke="#f4f4f4"/>')
        parts.append(f'<text x="{x:.1f}" y="{mt+ph+16:.1f}" '
                     f'text-anchor="middle" fill="#555">{int(t)}s</text>')
    # optional jobs cap line
    if jobs and jobs <= ymax:
        y = Y(jobs)
        parts.append(f'<line x1="{ml}" y1="{y:.1f}" x2="{W-mr}" y2="{y:.1f}" '
                     f'stroke="#d33" stroke-dasharray="5,4"/>')
        parts.append(f'<text x="{W-mr}" y="{y-4:.1f}" text-anchor="end" '
                     f'fill="#d33">-j {jobs}</text>')
    # area + line
    parts.append(f'<polygon points="{area}" fill="#4c78a8" fill-opacity="0.18"/>')
    parts.append(f'<polyline points="{line}" fill="none" stroke="#4c78a8" '
                 f'stroke-width="1.5"/>')
    # axis labels
    parts.append(f'<text x="{ml+pw/2:.0f}" y="{H-6}" text-anchor="middle" '
                 f'fill="#333">wall-clock seconds</text>')
    parts.append(f'<text x="16" y="{mt+ph/2:.0f}" text-anchor="middle" '
                 f'fill="#333" transform="rotate(-90 16 {mt+ph/2:.0f})">'
                 f'compiles in flight</text>')
    parts.append('</svg>')
    return "\n".join(parts)


def md_table(headers, rows):
    # A literal `|` in a cell (common in tactic snippets like `first [a | b]`)
    # ends the column early in GitHub's table parser -- escape it, even inside
    # the backtick code spans (GitHub renders `\|` back to `|` there).
    def cell(c):
        return str(c).replace("|", "\\|")
    out = ["| " + " | ".join(cell(h) for h in headers) + " |",
           "|" + "|".join("---" for _ in headers) + "|"]
    for r in rows:
        out.append("| " + " | ".join(cell(c) for c in r) + " |")
    return "\n".join(out)


def snippet(cmd, n=64):
    s = cmd.replace("~", " ").strip()
    return (s[:n - 3] + "...") if len(s) > n else s


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build-log", required=True,
                    help="stdout/stderr of `make TIMED=1` (per-file real lines)")
    ap.add_argument("--iris-dir", default="iris",
                    help="dir with .v / .v.timing / .vo (default: iris)")
    ap.add_argument("--out-dir", default=".",
                    help="where to write report.md, parallelism.svg, report-full.txt")
    ap.add_argument("--deps", default=None,
                    help="coqdep file (default: <iris-dir>/.CoqMakefile.d)")
    ap.add_argument("--top", type=int, default=30, help="rows per table")
    ap.add_argument("--jobs", type=int, default=None,
                    help="the -j level, drawn as a cap line on the plot")
    args = ap.parse_args()

    iris = args.iris_dir
    deps_path = args.deps or os.path.join(iris, ".CoqMakefile.d")
    os.makedirs(args.out_dir, exist_ok=True)

    real = parse_build_log(args.build_log)
    deps, targets = parse_deps(deps_path)
    stmts, n_timing = parse_timings(iris)

    # ---- analyses ----
    finish, pred = critical_path(deps, targets, real)
    chain = path_to(max(finish, key=lambda n: finish[n]), pred) if finish else []
    crit_len = finish[chain[-1]] if chain else 0.0

    intervals, span = build_timeline(iris, real)
    steps = concurrency_steps(intervals)
    sigma_cpu = sum(real.values())
    maxpar = max([c for _, c in steps], default=0)
    avgpar = (sigma_cpu / span) if span > 0 else 0.0
    # wall spent effectively serial (<=1 compile in flight)
    serial = 0.0
    for i in range(len(steps)):
        t = steps[i][0]
        nt = steps[i + 1][0] if i + 1 < len(steps) else span
        if steps[i][1] <= 1:
            serial += max(0.0, nt - t)

    linecache = {}
    stmts.sort(reverse=True)
    byfile_stmt = defaultdict(float)
    for secs, fbase, _, _ in stmts:
        byfile_stmt[fbase] += secs

    # ---- report.md (the step-summary view) ----
    md = []
    md.append("## Proof build profile (iris/)\n")
    md.append(
        f"- **wall span** {span:.0f}s  ·  **ΣCPU** {sigma_cpu:.0f}s  ·  "
        f"**critical path** {crit_len:.0f}s ({len(chain)} files)\n"
        f"- **avg parallelism** {avgpar:.1f}×  ·  **peak** {maxpar}×"
        + (f" (of -j{args.jobs})" if args.jobs else "")
        + f"  ·  **~{serial:.0f}s effectively serial** (≤1 compile in flight)\n"
        f"- {len(real)} files timed · {n_timing} timing files · "
        f"{len(stmts)} sentences\n")

    md.append("\n### Most expensive statements\n")
    rows = []
    for secs, fbase, off, cmd in stmts[:args.top]:
        ln = offset_to_line(iris, linecache, fbase, off)
        rows.append([f"{secs:.1f}", f"`{fbase}.v:{ln}`", f"`{snippet(cmd)}`"])
    md.append(md_table(["secs", "location", "statement"], rows)
              if rows else "_no `.v.timing` files found (build with `TIMING=1`)_")

    md.append("\n### Most expensive files (wall, incl. async Qed)\n")
    onpath = set(chain)
    rows = []
    for name, dur in sorted(real.items(), key=lambda x: -x[1])[:args.top]:
        rows.append([f"{dur:.1f}", f"`{name}`",
                     f"{byfile_stmt.get(name, 0.0):.1f}",
                     "●" if name in onpath else ""])
    md.append(md_table(["wall", "file", "tactic-Σ", "crit"], rows)
              if rows else "_no per-file times (build with `TIMED=1`)_")

    md.append("\n### Longest dependency chain (critical path)\n")
    if chain:
        rows, cum = [], 0.0
        for n in chain:
            cum += real.get(n, 0.0)
            rows.append([f"{real.get(n, 0.0):.1f}", f"{cum:.1f}", f"`{n}`"])
        md.append(md_table(["wall", "cum", "file"], rows))
        # other long chains: top files by their own critical depth, off this path
        others = [(finish[n], n) for n in finish if n not in onpath]
        others.sort(reverse=True)
        if others:
            md.append("\n**Other deep chains** (longest path *ending at* each file, "
                      "excluding files already on the critical path):\n")
            rows = [[f"{f:.1f}", f"`{n}`"] for f, n in others[:12]]
            md.append(md_table(["chain len", "ends at"], rows))
    else:
        md.append("_no dependency data (need `.CoqMakefile.d` + per-file times)_")

    md.append("\n### Parallelism over time\n")
    md.append(f"compiles in flight (peak {maxpar}× · avg {avgpar:.1f}×"
              + (f" · -j{args.jobs}" if args.jobs else "") + "):\n")
    md.append("```\n" + render_ascii(steps, span, jobs=args.jobs) + "\n```")
    md.append(f"~{serial:.0f}s of the {span:.0f}s wall runs ≤1 compile in flight "
              "(the serial tail no amount of `-j` can shrink). "
              "A standalone `parallelism.svg` is also written to the output dir.\n")

    report_md = "\n".join(md) + "\n"
    with open(os.path.join(args.out_dir, "report.md"), "w") as f:
        f.write(report_md)

    # ---- parallelism.svg ----
    with open(os.path.join(args.out_dir, "parallelism.svg"), "w") as f:
        f.write(render_svg(steps, span, jobs=args.jobs))

    # ---- report-full.txt (everything, for the artifact) ----
    with open(os.path.join(args.out_dir, "report-full.txt"), "w") as f:
        f.write(f"wall span {span:.1f}s  ΣCPU {sigma_cpu:.1f}s  "
                f"critical path {crit_len:.1f}s  "
                f"peak {maxpar}x  avg {avgpar:.2f}x  serial ~{serial:.1f}s\n\n")
        f.write(f"== top {min(1000, len(stmts))} statements by cost "
                f"(of {len(stmts)}) ==\n")
        for secs, fbase, off, cmd in stmts[:1000]:
            ln = offset_to_line(iris, linecache, fbase, off)
            f.write(f"{secs:8.3f}  {fbase}.v:{ln:<6} {snippet(cmd, 80)}\n")
        f.write("\n== ALL files by wall ==\n")
        for name, dur in sorted(real.items(), key=lambda x: -x[1]):
            f.write(f"{dur:8.2f}  {name}"
                    f"{'  [crit]' if name in onpath else ''}\n")
        f.write("\n== critical path ==\n")
        cum = 0.0
        for n in chain:
            cum += real.get(n, 0.0)
            f.write(f"{real.get(n,0.0):8.2f}  cum {cum:8.2f}  {n}\n")

    print(report_md)
    return 0


if __name__ == "__main__":
    sys.exit(main())

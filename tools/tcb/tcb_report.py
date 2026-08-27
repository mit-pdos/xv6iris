#!/usr/bin/env python3
"""The DEFINITION-LEVEL trusted base of a theorem's STATEMENT, as a report.

Reads the output of tools/tcb/tcb-report.sh's [Print All Dependencies] and
answers two questions about it:

  which FILES must a reader read, and
  how much of each -- how many source lines do those definitions occupy.

NAME RESOLUTION.  [Print All Dependencies] prints SHORTEST QUALIDS, not
canonical names, so two passes are needed: suffix-match the printed qualid
against the load paths in iris/_CoqProject plus the switch's library
directories, then fall back to the in-tree .glob files for anything printed
BARE, with no module component at all ([fsimg_cov] is one).  Measured on
xv6_fs_adequacy_xv6Σ: 2401 of 2402 in-tree names resolve by the first pass
and the last one by the second.

LINE COUNTS come from splitting each .v into vernac sentences (comment- and
string-aware) and mapping the .glob byte offsets onto them.  What is counted
is the sentences that DECLARE something in the trusted set -- not the
comments around them, which in this tree are load-bearing, so the honest
"lines a human reads" is somewhat above the number printed here.

TWO KNOWN GAPS, both in [Print All Dependencies] rather than here:

  INDUCTIVES ARE NEVER REPORTED.  printer.mli's [context_object] is
  Variable | Axiom | Opaque | Transparent, with no inductive case, so
  datatype declarations are traversed but never printed -- and they ARE part
  of the trusted base ([FsDurSnap.snap_bytes], a 21-field Record, is what
  the FS durability guarantee actually SAYS).  --with-inductives adds every
  inductive DECLARED in an already-trusted file, which is an upper bound on
  that component; the truth is between the two totals.

  THE OPAQUE/TRANSPARENT SPLIT IS A PROXY.  What makes a constant need no
  trust is that it INHABITS A PROP -- the kernel checked it, nothing
  eliminates a Prop into Type, and no Prop-valued statement distinguishes
  two inhabitants of one Prop.  [Qed] merely correlates with that.  So the
  Opaque section is reported here with its types, to be read rather than
  assumed: an opaque constant whose type is NOT a Prop is meaning-bearing
  and belongs in the trusted list whatever heading it printed under.
  (Checked 2026-08-27: all 43 in-tree opaque constants are Prop-valued.)

Usage:
  tcb_report.py deps.out [--only iris] [--md] [--with-inductives]
                         [--target Module.theorem]
"""
import bisect, collections, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WS = (b" ", b"\n", b"\t", b"\r")


def coq_lib():
    switch = os.environ.get("SWITCH", "/shared/xv6rocq")
    try:
        return subprocess.run(["opam", "exec", "--switch=" + switch, "--", "coqc", "-where"],
                              capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return None


def index_root(index, dirpath, prefix):
    if not os.path.isdir(dirpath):
        return
    for dp, _dn, fns in os.walk(dirpath):
        for fn in fns:
            if fn.endswith(".v"):
                mod = os.path.relpath(os.path.join(dp, fn), dirpath)[:-2].replace(os.sep, ".")
                index.setdefault(prefix + "." + mod if prefix else mod, os.path.join(dp, fn))


def build_index():
    index, repo_dirs = {}, []
    with open(os.path.join(ROOT, "iris", "_CoqProject")) as f:
        for line in f:
            p = line.split()
            if len(p) >= 3 and p[0] in ("-R", "-Q"):
                d = os.path.normpath(os.path.join(ROOT, "iris", p[1]))
                index_root(index, d, p[2])
                repo_dirs.append(d)
    lib = coq_lib()
    if lib:
        index_root(index, os.path.join(lib, "theories"), "Corelib")
        uc = os.path.join(lib, "user-contrib")
        if os.path.isdir(uc):
            for e in sorted(os.listdir(uc)):
                index_root(index, os.path.join(uc, e), e)
    return index, repo_dirs


def glob_entries(vpath):
    """[(kind, byte-offset, name)] from the .glob beside vpath, or []."""
    g = vpath[:-2] + ".glob"
    if not os.path.exists(g):
        return []
    out = []
    for line in open(g, errors="replace"):
        m = re.match(r"^(\w+) (\d+):(\d+) \S+ (\S+)$", line.strip())
        if m:
            out.append((m.group(1), int(m.group(2)), m.group(4)))
    return out


def parse(path):
    """-> {Rocq section heading: [printed name, ...]}"""
    out, section = collections.defaultdict(list), None
    for line in open(path, errors="replace"):
        s = line.rstrip("\n")
        if re.match(r"^[A-Z][a-z]+( [a-z]+)*:$", s):
            section = s[:-1]
            continue
        if not section:
            continue
        m = re.match(r"^(\S+) :$", s)
        if m:
            out[section].append(m.group(1))
            continue
        # Rocq fits short entries on one line; the Axioms section usually is.
        m = re.match(r"^(\S+) : \S.*$", s)
        if m and section == "Axioms":
            out[section].append(m.group(1))
    return out


def sentences(data):
    """[(start, end)] byte spans of top-level vernac sentences."""
    out, i, n, start, depth, instr = [], 0, len(data), 0, 0, False
    while i < n:
        c = data[i:i + 1]
        if instr:
            instr = c != b'"'
            i += 1
            continue
        if depth:
            if data[i:i + 2] == b"(*":
                depth += 1; i += 2; continue
            if data[i:i + 2] == b"*)":
                depth -= 1; i += 2; continue
            i += 1; continue
        if data[i:i + 2] == b"(*":
            depth = 1; i += 2; continue
        if c == b'"':
            instr = True; i += 1; continue
        if c == b"." and (i + 1 >= n or data[i + 1:i + 2] in WS):
            out.append((start, i + 1))
            i += 1
            while i < n and data[i:i + 1] in WS:
                i += 1
            start = i
            continue
        i += 1
    if start < n:
        out.append((start, n))
    return out


def covered_lines(vpath, names, with_ind):
    """(lines declaring something in `names`, total lines in the file)"""
    data = open(vpath, "rb").read()
    total = data.count(b"\n") + 1
    ents = glob_entries(vpath)
    if not ents:
        return None, total
    nl = [0] + [m.start() + 1 for m in re.finditer(b"\n", data)]
    sents = sentences(data)
    starts = [s for s, _ in sents]
    kinds = {"def", "inst", "proj", "rec", "scheme", "abbrev"}
    marked = set()
    for kind, off, name in ents:
        if kind in ("ind", "constr"):
            if not with_ind:
                continue
        elif kind not in kinds or name not in names:
            continue
        k = bisect.bisect_right(starts, off) - 1
        if 0 <= k < len(sents):
            marked.add(k)
    lines = set()
    for k in marked:
        a, b = sents[k]
        lines.update(range(bisect.bisect_right(nl, a), bisect.bisect_right(nl, b - 1) + 1))
    return len(lines), total


def main():
    pos = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not pos:
        sys.exit(__doc__)
    md = "--md" in sys.argv
    with_ind = "--with-inductives" in sys.argv
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else "iris"
    target = (sys.argv[sys.argv.index("--target") + 1] if "--target" in sys.argv
              else "SystemAdequacy.xv6_fs_adequacy_xv6Σ")

    index, repo_dirs = build_index()
    suffix = collections.defaultdict(list)
    for k, v in index.items():
        p = k.split(".")
        for i in range(len(p)):
            suffix[".".join(p[i:])].append(v)
    bare = {}
    for d in repo_dirs:
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".v"):
                for kind, _off, name in glob_entries(os.path.join(d, fn)):
                    bare.setdefault(name, os.path.join(d, fn))

    def resolve(n):
        p = n.split(".")
        for i in range(len(p) - 1, 0, -1):
            c = ".".join(p[:i])
            if c in suffix:
                return suffix[c][0]
        return bare.get(p[-1])

    sections = parse(pos[0])
    trans = sections.get("Transparent constants", [])
    per = collections.defaultdict(set)
    unresolved = 0
    for n in trans:
        p = resolve(n)
        if p is None:
            unresolved += 1
        else:
            per[p].add(n.split(".")[-1])

    sel = {p: v for p, v in per.items() if os.path.relpath(p, ROOT).split(os.sep)[0] == only}
    rows, tot_d = [], 0
    tot_c = tot_f = 0
    for p in sel:
        c, f = covered_lines(p, sel[p], with_ind)
        rows.append((os.path.relpath(p, ROOT), len(sel[p]), c, f))
        tot_d += len(sel[p])
        tot_c += c or 0
        tot_f += f
    rows.sort(key=lambda r: (-(r[2] or 0), r[0]))

    tree_lines = 0
    for fn in os.listdir(os.path.join(ROOT, only)):
        if fn.endswith(".v"):
            tree_lines += open(os.path.join(ROOT, only, fn), "rb").read().count(b"\n") + 1
    tree_files = sum(1 for fn in os.listdir(os.path.join(ROOT, only)) if fn.endswith(".v"))

    elsewhere = collections.Counter()
    for p in per:
        d = os.path.relpath(p, ROOT).split(os.sep)[0]
        if d != only and any(p.startswith(x + os.sep) for x in repo_dirs):
            elsewhere[d] += 1

    if not md:
        for r in rows:
            print("  %-34s %4d defs  %5s / %5d lines" % (r[0], r[1], r[2], r[3]))
        print("  %-34s %4d defs  %5d / %5d lines" % ("TOTAL", tot_d, tot_c, tot_f))
        return

    short = target.split(".")[-1]
    print("## Trusted base of `%s` (`%s/`)" % (short, only))
    print()
    print("`Print All Dependencies` on the **statement** of `%s` — the" % target)
    print("definitions a reader must read for the theorem to say what they think it says.")
    print("The proof cone is *not* here: Rocq's kernel checks it, so nothing a proof")
    print("mentions needs trusting.")
    print()
    print("**%d of %d `%s/` files · %d definitions · %d lines** "
          "(%.1f%% of those files' %s lines; %.2f%% of `%s/`'s %s)"
          % (len(rows), tree_files, only, tot_d, tot_c,
             100.0 * tot_c / tot_f if tot_f else 0, f"{tot_f:,}",
             100.0 * tot_c / tree_lines if tree_lines else 0, only, f"{tree_lines:,}"))
    print()
    print("| file | defs | lines | file lines | % of file |")
    print("|---|---:|---:|---:|---:|")
    for name, nd, c, f in rows:
        print("| `%s` | %d | %d | %d | %.1f%% |" % (name, nd, c or 0, f, 100.0 * (c or 0) / f))
    print("| **total** | **%d** | **%d** | **%d** | **%.1f%%** |"
          % (tot_d, tot_c, tot_f, 100.0 * tot_c / tot_f if tot_f else 0))
    print()
    # Both commands print an "Axioms:" heading, so the same names arrive twice.
    axioms = sorted(set(sections.get("Axioms", [])))
    print("Also in the trusted base, outside `%s/`: %s."
          % (only, ", ".join("`%s/` %d files" % (d, n) for d, n in sorted(elsewhere.items()))
             or "nothing"))
    print()
    print("Axioms and parameters the statement reaches (%d): %s"
          % (len(axioms), ", ".join("`%s`" % a for a in axioms)))
    print()
    print("<details><summary>Caveats — read once</summary>")
    print()
    print("* **Inductives are not counted.** `printer.mli`'s `context_object` has no")
    print("  inductive case, so `Print All Dependencies` traverses datatype declarations")
    print("  but never prints them — yet they are trusted. `FsDurSnap.snap_bytes`, the")
    print("  21-field `Record` that says what \"the committed view is a file system\"")
    print("  *means*, is invisible here. Re-run with `--with-inductives` for an upper")
    print("  bound on that component.")
    print("* **Opaque/Transparent is a proxy.** What excuses a constant from trust is that")
    print("  it *inhabits a `Prop`*, not that it is `Qed`'d. Read the Opaque section's")
    print("  printed types: any whose type is not a `Prop` is meaning-bearing and belongs")
    print("  in this table. All 43 in-tree opaque constants were `Prop`-valued when last")
    print("  checked.")
    print("* **Lines are vernac sentences**, not the comments around them, which in this")
    print("  tree carry a lot of the meaning. The real reading burden is somewhat higher.")
    print("* This is a **report, not a check** — no baseline is diffed. A jump in the file")
    print("  count is the signal to look: it means a statement-level definition picked up")
    print("  a dependency on a new part of the tree.")
    print("* Three theorems are reported, most general first. "
          "`RiscvAdequacy.riscv_power_adequacy`")
    print("  is the **any provable pure trace property** theorem: the crash invariant `Pc`")
    print("  is a *parameter*, so it names no file system and is the cheapest of the three")
    print("  to state. `xv6_power_adequacy_xv6Σ` is xv6's instance of it, with `Pc` fixed")
    print("  at `FsCrash.P_fs_named` — the invariant xv6's boot cone establishes — and")
    print("  `phi` still free. `xv6_fs_adequacy_xv6Σ` then chooses `phi`.")
    print("* **Neither of the lower two contains the other.** Leaving `phi` free puts the")
    print("  `Hphi` *hypothesis* — an iProp entailment — in the statement, so the Iris")
    print("  ghost-state layer is in that base; but only the bottom one reaches the pure")
    print("  FS-consistency vocabulary `phi` names (`xv6_trace_pure`, `fs_boot_pure`,")
    print("  `snap_ok` and its cone, the link-count definitions).")
    print("* **Do not read containment off the file column.** Those FS-only definitions")
    print("  live in files the general theorem reaches for other reasons, so the FILE sets")
    print("  nest while the DEFINITION sets do not.")
    print()
    print("</details>")
    if unresolved:
        print()
        print("_%d printed names could not be mapped to a file (all outside this tree)._"
              % unresolved)


if __name__ == "__main__":
    main()

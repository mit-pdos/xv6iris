#!/usr/bin/env python3
"""find_dead.py -- find definitions/lemmas that are never referenced.

Uses Coq's .glob files (emitted during compilation), which record every
top-level definition and every cross-reference by fully-qualified name.
A definition is reported as "dead" when its qualified name (module, secpath,
name) appears in no reference (R) line anywhere in the considered fileset.

Only files listed in _CoqProject are considered (scratch/Zz*/Scratch* globs
are ignored), so a lemma referenced only by a throwaway Print-Assumptions
file is still counted as dead.

Caveats (why a "dead" hit may be a false positive):
  * Instances / Notations / Canonical structures are used by inference, not by
    name -- reported separately under [implicit] and almost never truly dead.
  * Lemmas used ONLY via a hint database (auto/eauto with, autorewrite) or a
    generic tactic may not emit a name reference -> could appear dead.
  * A recursive Fixpoint references itself, so it won't show as dead even if
    externally unused.
  * A genuinely-unused top-level THEOREM (a result nothing consumes yet) is
    indistinguishable from dead code by this analysis -- that's the judgment
    call this tool is meant to surface, not make.

The run also ends with a whole-FILE report: modules (.v files) that no OTHER
module in the project Require's. Build LEAVES / top-level targets (adequacy,
the current top theorem, Print-Assumptions/smoke files) legitimately appear
there; a non-target module that appears is a dead-FILE candidate. This is read
from the Require graph of the .v sources (not the .glob refs), so a file
imported only for side effects -- an Export shim, an instance/notation/hint-only
module -- still counts as imported.

Usage:
  python3 find_dead.py                 # analyse ./ (dir holding the .glob files)
  python3 find_dead.py --dir .         # same
  python3 find_dead.py --all           # include implicit (inst/not/ind/...) too
  python3 find_dead.py --kinds prf,def # restrict to given glob kinds
  python3 find_dead.py --files-only    # ONLY list .v files imported by nothing
  python3 find_dead.py --no-files      # skip the unreferenced-.v-file report
"""
import argparse, bisect, os, re, sys

# glob def-kinds we treat as "lemmas & definitions" (the primary report)
PRIMARY = {"prf", "def", "rec", "abbrev", "scheme"}
# structural / implicitly-used kinds (reported separately, rarely truly dead)
IMPLICIT = {"inst", "not", "ind", "constr", "proj", "ax", "coe", "class"}
KIND_LABEL = {"prf": "Lemma/Thm", "def": "Definition", "rec": "Fixpoint",
              "abbrev": "Notation(abbrev)", "scheme": "Scheme",
              "inst": "Instance", "not": "Notation", "ind": "Inductive",
              "constr": "Constructor", "proj": "Projection", "ax": "Axiom",
              "coe": "Coercion", "class": "Class"}

def coqproject_modules(dirpath):
    """Return the set of module basenames listed in _CoqProject (no extension)."""
    cp = os.path.join(dirpath, "_CoqProject")
    mods = set()
    if not os.path.exists(cp):
        return None
    for line in open(cp):
        line = line.strip()
        if line.endswith(".v") and not line.startswith("-"):
            mods.add(os.path.basename(line)[:-2])
    return mods

# ---------------------------------------------------------------------------
# Whole-FILE dead check: modules (.v files) that nothing else Require's.
# Detected from the Require graph of the .v sources (NOT the .glob refs), so a
# file imported only for side effects -- an Export shim, an instance/notation/
# hint-only module -- still counts as imported. Only intra-project (xv6iris)
# requires count: an external `From Kernel Require Import X` never marks an iris
# module named X as imported.
# ---------------------------------------------------------------------------
_MODTOKEN = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"
_REQUIRE_RE = re.compile(
    r"(?:From\s+(" + _MODTOKEN + r")\s+)?"
    r"Require\s+(?:(?:Import|Export)\s+)?"
    r"(" + _MODTOKEN + r"(?:\s+" + _MODTOKEN + r")*)\s*\.")

def strip_coq_comments(text):
    """Drop (possibly nested) (* ... *) comments so a 'Require' mentioned inside
    a comment is not counted as a real dependency."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i+2]
        if two == "(*":
            depth += 1; i += 2; continue
        if two == "*)" and depth > 0:
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)

def module_set(dirpath, only_mods):
    """The project's module basenames: from _CoqProject if present, else every
    *.v in the directory."""
    if only_mods is not None:
        return only_mods
    return {f[:-2] for f in os.listdir(dirpath) if f.endswith(".v")}

def unimported_modules(dirpath, modset):
    """Sorted modules in `modset` that no OTHER module in `modset` Require's."""
    imported = set()
    for mod in sorted(modset):
        vp = os.path.join(dirpath, mod + ".v")
        try:
            text = strip_coq_comments(open(vp, encoding="utf-8").read())
        except OSError:
            continue
        for m in _REQUIRE_RE.finditer(text):
            from_pfx = m.group(1) or ""
            if from_pfx not in ("", "xv6iris"):
                continue                       # requires from an external tree
            for tok in m.group(2).split():
                parts = tok.split(".")
                base, tok_pfx = parts[-1], ".".join(parts[:-1])
                if tok_pfx not in ("", "xv6iris"):
                    continue                   # externally-qualified module
                if base in modset and base != mod:
                    imported.add(base)
    return sorted(m for m in modset if m not in imported)

def print_unimported(dirpath, modset):
    unimp = unimported_modules(dirpath, modset)
    print(f"\n== {len(unimp)} module file(s) imported by nothing else "
          f"(of {len(modset)}) ==")
    print("   Expected here: build LEAVES / top-level targets -- adequacy, "
          "whole-system theorems, Print-Assumptions/smoke files. A module that "
          "is NOT a deliberate top-level target is a dead-FILE candidate.")
    for m in unimp:
        print(f"  {m}.v")

def line_index(vpath):
    """Byte-offset -> 1-based line lookup for a .v file."""
    try:
        data = open(vpath, "rb").read()
    except OSError:
        return None
    starts = [0]
    for i, b in enumerate(data):
        if b == 0x0A:
            starts.append(i + 1)
    return starts

def off_to_line(starts, off):
    if starts is None:
        return "?"
    return bisect.bisect_right(starts, off)

DEF_RE = re.compile(r"^([a-z]+)\s+(\d+):(\d+)\s+(\S+)\s+(\S+)\s*$")
REF_RE = re.compile(r"^R(\d+):(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=".", help="directory with .glob and .v files")
    ap.add_argument("--all", action="store_true", help="also report implicit kinds")
    ap.add_argument("--kinds", default="", help="comma list of glob kinds to report")
    ap.add_argument("--triage", action="store_true",
                    help="group by heuristic category instead of by file")
    ap.add_argument("--files-only", action="store_true",
                    help="only list .v files imported by nothing else (skip the "
                         "per-definition analysis)")
    ap.add_argument("--no-files", action="store_true",
                    help="skip the trailing unreferenced-.v-file report")
    args = ap.parse_args()
    d = args.dir

    only_mods = coqproject_modules(d)

    if args.files_only:
        print_unimported(d, module_set(d, only_mods))
        return

    globs = sorted(g for g in os.listdir(d) if g.endswith(".glob"))
    if only_mods is not None:
        globs = [g for g in globs if g[:-5] in only_mods]

    defs = []                 # (module, secpath, name, kind, glob-basename, off)
    refs = set()              # (module, secpath, name)
    for g in globs:
        gp = os.path.join(d, g)
        module = None
        for line in open(gp):
            line = line.rstrip("\n")
            if line.startswith("F"):
                module = line[1:]
                continue
            m = REF_RE.match(line)
            if m:
                _, _, rmod, rsec, rname, _ = m.groups()
                if rname != "<>":
                    refs.add((rmod, rsec, rname))
                continue
            m = DEF_RE.match(line)
            if m and module is not None:
                kind, s, _e, sec, name = m.groups()
                if kind in ("var", "binder", "sec"):
                    continue
                defs.append((module, sec, name, kind, g[:-5], int(s)))

    want = set()
    if args.kinds:
        want = set(args.kinds.split(","))
    else:
        want = set(PRIMARY)
        if args.all:
            want |= IMPLICIT

    # a def is dead if (module, secpath, name) is referenced nowhere
    dead0 = [row for row in defs
             if row[3] in want and (row[0], row[1], row[2]) not in refs]

    lineidx = {}
    def loc(gbase, off):
        if gbase not in lineidx:
            lineidx[gbase] = line_index(os.path.join(d, gbase + ".v"))
        return f"{gbase}.v:{off_to_line(lineidx[gbase], off)}"

    # honor an explicit keep-marker: a (* ... KEEP-UNREFERENCED ... *) comment in
    # the definition's own header (scanning up until the previous proof/def/section)
    # opts a deliberately-unreferenced definition OUT of the dead report.
    _flines = {}
    def keep_marked(gbase, off):
        vp = os.path.join(d, gbase + ".v")
        if gbase not in _flines:
            try: _flines[gbase] = open(vp, encoding="utf-8").read().split("\n")
            except OSError: _flines[gbase] = []
        fl = _flines[gbase]
        if not fl: return False
        ln = off_to_line(lineidx.setdefault(gbase, line_index(vp)), off)  # 1-based
        i = ln - 2  # line directly above the definition (0-based)
        stop = re.compile(r"^\s*(Lemma|Theorem|Corollary|Definition|Fixpoint|"
                          r"Global\s+Instance|Instance|Proof|Section|End|Qed|Defined|Admitted)\b")
        steps = 0
        while i >= 0 and steps < 14:
            line = fl[i]
            if "KEEP-UNREFERENCED" in line:
                return True
            if stop.match(line) or line.rstrip().endswith(("Qed.", "Defined.", "Admitted.")):
                break
            i -= 1; steps += 1
        return False

    kept = [r for r in dead0 if keep_marked(r[4], r[5])]
    dead = [r for r in dead0 if not keep_marked(r[4], r[5])]

    if not args.triage:
        by_file = {}
        for module, sec, name, kind, gbase, off in dead:
            by_file.setdefault(gbase, []).append((off, name, kind, sec))
        total = 0
        for gbase in sorted(by_file):
            print(f"\n### {gbase}.v  ({len(by_file[gbase])} unreferenced)")
            for off, name, kind, sec in sorted(by_file[gbase]):
                secnote = "" if sec == "<>" else f"  [in {sec}]"
                print(f"  {loc(gbase,off):<28} {KIND_LABEL.get(kind,kind):<16} {name}{secnote}")
                total += 1
    else:
        cats = {}
        for module, sec, name, kind, gbase, off in dead:
            cats.setdefault(category(name, kind), []).append((gbase, off, name, kind))
        order = ["auto-generated (eliminator/projection) -- NOT dead",
                 "smoke-test instantiation (concrete-register example)",
                 "top-level spec? (whole-function / step WP -- maybe intentional)",
                 "helper candidate -- likely reviewable for removal"]
        total = 0
        for cat in order:
            rows = cats.get(cat, [])
            if not rows:
                continue
            print(f"\n===== {cat}  ({len(rows)}) =====")
            for gbase, off, name, kind in sorted(rows, key=lambda r: (r[0], r[1])):
                print(f"  {loc(gbase,off):<28} {KIND_LABEL.get(kind,kind):<16} {name}")
                total += 1

    kinds_desc = ",".join(sorted(want))
    nfiles = len({r[4] for r in dead})
    print(f"\n== {total} unreferenced {kinds_desc} across {nfiles} files "
          f"(of {len(globs)} globs scanned) ==")
    if kept:
        print(f"   ({len(kept)} unreferenced def(s) suppressed by KEEP-UNREFERENCED marker: "
              + ", ".join(sorted(r[2] for r in kept)) + ")")
    print("NB: heuristic categories are hints, not verdicts. Instances/Notations, "
          "hint-DB-only lemmas, and not-yet-consumed top-level theorems can appear "
          "here. Use --all for implicit kinds, drop --triage for by-file view.")

    if not args.no_files:
        print_unimported(d, module_set(d, only_mods))

TOPLEVEL_RE = re.compile(
    r"^(wp_acquire$|wp_holding|wp_entry_boot$|wp_kernelvec$|wp_spin$|wp_start$|wp_memset_s|"
    r"wp_push_off$|wp_step_|wp_.*_intr$|kernelvec_handler_spec$|intr_inv|kernel_window$|"
    r"fetch_from_pts$|wp_add_real|.*_handler_spec$|wp_csrw_.*_gpr$)")
SMOKE_RE = re.compile(r"(_x\d+|^Unnamed_thm$|^wp_[a-z]+_x\d)")

def category(name, kind):
    if kind in ("scheme", "proj", "inst", "not", "ind", "constr"):
        return "auto-generated (eliminator/projection) -- NOT dead"
    if SMOKE_RE.search(name):
        return "smoke-test instantiation (concrete-register example)"
    if TOPLEVEL_RE.match(name):
        return "top-level spec? (whole-function / step WP -- maybe intentional)"
    return "helper candidate -- likely reviewable for removal"

if __name__ == "__main__":
    main()

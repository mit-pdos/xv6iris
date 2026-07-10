#!/usr/bin/env python3
"""detect_unused_imports.py -- find removable Coq `Require Import` modules.

Problem
-------
A `Require Import M` line can be genuinely *needed* even when no NAME from M is
ever written in the file, because M may contribute, invisibly to a text search:

  * typeclass `Instance`s      (resolved by `apply`/`typeclasses eauto`),
  * `Notation`s               (parsing/printing),
  * `Hint`s                   (auto/eauto/autorewrite databases),
  * `Canonical Structure`s / `Coercion`s.

None of those appear as name references in the compiler's `.glob` output, so a
pure glob/grep "is this name used?" check yields FALSE "unused" verdicts.  The
ONLY reliable test is: delete the import, recompile the file, and see whether it
still builds.

Method (glob-shortlist + build-confirm)
---------------------------------------
1. Parse each `.v` for import statements and map every imported module token to
   its full logical path (respecting the `-R <dir> <prefix>` mappings in
   `_CoqProject`), e.g.
       From stdpp Require Import gmap          -> stdpp.gmap
       From iris.proofmode Require Import proofmode -> iris.proofmode.proofmode
       Require Import RiscvModelBytes          -> xv6iris.RiscvModelBytes
       From Kernel Require KernelSyms          -> Kernel.KernelSyms  (no Import)

2. SHORTLIST (fast, `.glob`-only): read the file's `.glob`, collect every `R`
   (reference) line's defining libname, EXCLUDING kind==`lib` refs (those are the
   import/qualifier sites themselves, not "usage that needs an Import").  A module
   whose logical path contributes no non-`lib` reference is a *candidate* unused
   import -- this only NARROWS the set to build-test; it never decides.

3. CONFIRM (`--verify`, correct): for each file, remove ALL candidate modules at
   once and `make <file>.vo`.  If it still builds, every candidate is genuinely
   removable.  If it fails, fall back to removing candidates one at a time.  A
   candidate that still builds when removed is REMOVABLE; one that breaks the
   build was actually NEEDED (an instance/notation/hint false positive).  The
   file is ALWAYS restored to its original bytes afterwards (and its `.vo`
   rebuilt from the original so the tree stays green).

Caveats
-------
* `Require Export ...` re-exports to DOWNSTREAM files, so a single-file `make` is
  insufficient to prove it removable.  Export lines are SKIPPED by default
  (`--include-export` + `--full-make` would be required to test them safely).
* Shortlist false-negative: if a name defined in M is referenced but is ALSO
  reachable through another (transitive) import, glob still attributes the ref to
  M, so M is not shortlisted and a real removal can be missed.  Pass `--all` to
  build-test every import module (ignoring the glob shortlist) for completeness
  at the cost of many more compiles.

Scope
-----
By DEFAULT the checker only considers imports of THIS package's own modules --
those whose logical path carries the local `-R . <prefix>` prefix (here
`xv6iris.`).  Imports from other packages (SailStdpp, Riscv, stdpp, iris.*,
Kernel, Stdlib, ...) are skipped, since removing a stray external import is
low-value and its provenance is noisier.  Pass `--include-external` to test
those too.

Usage
-----
  detect_unused_imports.py --dir .                  # list glob-only candidates (local pkg)
  detect_unused_imports.py --dir . --verify         # build-confirm candidates
  detect_unused_imports.py --dir . --verify --all   # build-test ALL local imports
  detect_unused_imports.py --dir . --verify --include-external   # also other packages
  detect_unused_imports.py --dir . --verify --files WpAdd.v WpAmo.v
  detect_unused_imports.py --dir . --verify --report unused_imports_report.md
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# Build command.
# ---------------------------------------------------------------------------
# The project's documented build is `make -f CoqMakefile <file>.vo`.  For
# import-testing we instead call `coqc` DIRECTLY with the same load paths (the
# `-R`/`-arg` lines of _CoqProject) so that recompiling one file NEVER triggers
# a recursive rebuild of its dependencies (make would, if we touch a .v that is
# a dependency of another) -- this keeps every test hermetic and fast.  Set
# XV6_USE_MAKE=1 to fall back to the make-based build instead.
SWITCH = os.environ.get("XV6_SWITCH", "/shared/xv6rocq")
OPAM_PREFIX = ["opam", "exec", "--switch", SWITCH, "--"]
USE_MAKE = os.environ.get("XV6_USE_MAKE") == "1"

# Kinds of Coq stdlib prefixes we recognise as "already fully-qualified" logical
# paths (so we do NOT prepend the local `-R .` prefix to them).
KNOWN_LIB_PREFIXES = (
    "SailStdpp", "Riscv", "Kernel", "stdpp", "iris", "Stdlib", "Corelib",
    "Coq", "Ltac2", "elpi", "RecordUpdate", "Equations",
)


# ---------------------------------------------------------------------------
# Import-statement parsing.
# ---------------------------------------------------------------------------
@dataclass
class ImportStmt:
    lineno: int            # 1-based line number in the .v file
    raw: str               # exact original line text (without trailing newline)
    kind: str              # 'import' | 'export' | 'require'  (Import / Export / bare)
    from_prefix: str | None  # the `From X` prefix, or None
    modules: list[str]     # module tokens exactly as written on the line


# One statement per line (verified: no multi-line Require in this codebase).
_STMT_RE = re.compile(
    r"""^\s*
        (?:From\s+(?P<from>[\w.]+)\s+)?      # optional  From X
        Require\s+
        (?P<mode>Import\s+|Export\s+)?        # optional  Import / Export
        (?P<mods>[\w.\s]+?)                    # module tokens
        \s*\.\s*$                              # terminating period
    """,
    re.VERBOSE,
)


def parse_imports(text: str) -> list[ImportStmt]:
    stmts: list[ImportStmt] = []
    for i, line in enumerate(text.splitlines(), start=1):
        m = _STMT_RE.match(line)
        if not m:
            continue
        mode = (m.group("mode") or "").strip()
        kind = {"Import": "import", "Export": "export", "": "require"}[mode]
        mods = m.group("mods").split()
        stmts.append(
            ImportStmt(
                lineno=i,
                raw=line,
                kind=kind,
                from_prefix=m.group("from"),
                modules=mods,
            )
        )
    return stmts


def logical_path(stmt: ImportStmt, token: str, local_prefix: str) -> str:
    """Full logical (dotted) module path for one module `token` of `stmt`."""
    if stmt.from_prefix:
        return f"{stmt.from_prefix}.{token}"
    # Bare `Require [Import] token`.
    head = token.split(".", 1)[0]
    if head in KNOWN_LIB_PREFIXES:
        return token
    # Local module referenced by short name -> prepend the `-R .` prefix.
    return f"{local_prefix}.{token}" if local_prefix else token


# ---------------------------------------------------------------------------
# _CoqProject: discover the `-R <dir> <prefix>` for the tool's own directory.
# ---------------------------------------------------------------------------
def local_prefix_for_dir(dir_path: str) -> str:
    cp = os.path.join(dir_path, "_CoqProject")
    if not os.path.isfile(cp):
        return ""
    with open(cp) as f:
        for line in f:
            parts = line.split()
            # -R <dir> <prefix>   (also accept -Q)
            if len(parts) >= 3 and parts[0] in ("-R", "-Q"):
                d = parts[1]
                if os.path.abspath(os.path.join(dir_path, d)) == os.path.abspath(dir_path):
                    return parts[2]
    return ""


def coqc_flags(dir_path: str) -> list[str]:
    """The `-R/-Q/-arg` load-path flags from _CoqProject, for direct coqc runs."""
    cp = os.path.join(dir_path, "_CoqProject")
    flags: list[str] = []
    if not os.path.isfile(cp):
        return flags
    with open(cp) as f:
        toks = f.read().split()
    i = 0
    while i < len(toks):
        t = toks[i]
        if t in ("-R", "-Q") and i + 2 < len(toks):
            flags += [t, toks[i + 1], toks[i + 2]]
            i += 3
        elif t == "-arg" and i + 1 < len(toks):
            flags.append(toks[i + 1])   # unwrap: -arg X -> X passed to coqc
            i += 2
        else:
            i += 1
    return flags


# ---------------------------------------------------------------------------
# .glob parsing: set of libnames with a non-`lib` reference.
# ---------------------------------------------------------------------------
def referenced_libnames(glob_path: str) -> set[str]:
    """Return defining-module libnames that have >=1 non-`lib` R reference.

    A `Require Import M` emits an  `R... M <> <> lib`  self-reference at the
    import site, so `lib`-kind refs are excluded -- only "real" usages (def,
    thm, notation, constr, ind, var, mod, ...) count as evidence that a module
    is needed for the shortlist.
    """
    used: set[str] = set()
    if not os.path.isfile(glob_path):
        return used
    with open(glob_path, errors="replace") as f:
        for line in f:
            if not line.startswith("R"):
                continue
            # R<start>:<end> <libname> <secpath> <name> <kind>
            parts = line.rstrip("\n").split(" ")
            if len(parts) < 5:
                continue
            libname, kind = parts[1], parts[-1]
            if kind == "lib":
                continue
            used.add(libname)
    return used


def is_referenced(full_path: str, used: set[str]) -> bool:
    """True if `full_path` (or a sub-module of it) has a non-lib reference."""
    if full_path in used:
        return True
    prefix = full_path + "."
    return any(u.startswith(prefix) for u in used)


# ---------------------------------------------------------------------------
# Per-file analysis.
# ---------------------------------------------------------------------------
@dataclass
class Candidate:
    stmt: ImportStmt
    token: str
    full_path: str


@dataclass
class FileResult:
    vfile: str
    candidates: list[Candidate] = field(default_factory=list)
    removable: list[Candidate] = field(default_factory=list)   # build-confirmed
    needed: list[Candidate] = field(default_factory=list)      # false positives
    verified: bool = False
    jointly_removable: bool = True   # do all `removable` compile when dropped together?
    note: str = ""


def analyze_file(dir_path: str, vfile: str, local_prefix: str,
                 include_export: bool, use_all: bool,
                 local_only: bool = True) -> FileResult:
    path = os.path.join(dir_path, vfile)
    with open(path) as f:
        text = f.read()
    glob = os.path.join(dir_path, vfile[:-2] + ".glob")
    used = referenced_libnames(glob)

    res = FileResult(vfile=vfile)
    for stmt in parse_imports(text):
        if stmt.kind == "export" and not include_export:
            continue
        # Bare `Require` (no Import): removing it can break qualified accesses in
        # non-obvious ways; still a valid candidate, build-confirm decides.
        for token in stmt.modules:
            fp = logical_path(stmt, token, local_prefix)
            # By default only consider imports of THIS package's own modules
            # (logical prefix == local_prefix, e.g. `xv6iris.`).  External
            # packages (SailStdpp, Riscv, stdpp, iris.*, Kernel, Stdlib, ...)
            # are skipped -- pass --include-external to test them too.
            if local_only and local_prefix and not fp.startswith(local_prefix + "."):
                continue
            if use_all or not is_referenced(fp, used):
                res.candidates.append(Candidate(stmt=stmt, token=token, full_path=fp))
    return res


# ---------------------------------------------------------------------------
# File rewriting for build-tests.
# ---------------------------------------------------------------------------
def rewrite_without(text: str, drop: list[Candidate]) -> str:
    """Return `text` with the given (stmt,token) pairs removed.

    Drops individual module tokens from their statement; if a statement loses
    all its modules, the whole line is deleted.
    """
    # Group tokens to drop per line number.
    by_line: dict[int, set[str]] = {}
    stmt_by_line: dict[int, ImportStmt] = {}
    for c in drop:
        by_line.setdefault(c.stmt.lineno, set()).add(c.token)
        stmt_by_line[c.stmt.lineno] = c.stmt

    out_lines: list[str] = []
    for i, line in enumerate(text.splitlines(), start=1):
        if i not in by_line:
            out_lines.append(line)
            continue
        stmt = stmt_by_line[i]
        remaining = [m for m in stmt.modules if m not in by_line[i]]
        if not remaining:
            continue  # delete whole line
        # Rebuild the statement line, preserving From/Import/Export shape.
        head = ""
        if stmt.from_prefix:
            head += f"From {stmt.from_prefix} "
        head += "Require "
        if stmt.kind == "import":
            head += "Import "
        elif stmt.kind == "export":
            head += "Export "
        out_lines.append(head + " ".join(remaining) + ".")
    trailing_nl = "\n" if text.endswith("\n") else ""
    return "\n".join(out_lines) + trailing_nl


def build(dir_path: str, vfile: str, flags: list[str] | None = None) -> tuple[bool, str]:
    """Compile <vfile> (writing its .vo/.glob). Return (ok, error_text).

    Uses `coqc` directly (no dependency recursion) unless XV6_USE_MAKE=1.
    """
    if USE_MAKE:
        cmd = OPAM_PREFIX + ["make", "-f", "CoqMakefile", vfile[:-2] + ".vo"]
    else:
        cmd = OPAM_PREFIX + ["coqc"] + (flags or []) + [vfile]
    proc = subprocess.run(
        cmd, cwd=dir_path,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    out = proc.stdout
    # coqc/make both exit non-zero on failure; `***` guards make-style errors.
    ok = proc.returncode == 0 and "***" not in out
    return ok, out


def verify_file(dir_path: str, res: FileResult, flags: list[str]) -> None:
    """Build-confirm which candidates of `res` are genuinely removable."""
    if not res.candidates:
        res.verified = True
        return
    path = os.path.join(dir_path, res.vfile)
    with open(path) as f:
        original = f.read()
    backup = original

    def write(cands):
        with open(path, "w") as f:
            f.write(rewrite_without(original, cands))

    def restore_and_rebuild():
        with open(path, "w") as f:
            f.write(backup)
        build(dir_path, res.vfile, flags)  # leave a correct .vo behind

    try:
        # First: try removing ALL candidates at once (1 compile).
        write(res.candidates)
        ok, _ = build(dir_path, res.vfile, flags)
        if ok:
            res.removable = list(res.candidates)
            res.verified = True
            res.jointly_removable = True
            return
        # Fall back: one candidate at a time (each removed from the ORIGINAL,
        # i.e. with every OTHER import still present).  This answers "is X
        # redundant given the rest?".
        for c in res.candidates:
            write([c])
            ok, _ = build(dir_path, res.vfile, flags)
            if ok:
                res.removable.append(c)
            else:
                res.needed.append(c)
        # Individually-redundant does not guarantee JOINTLY removable (two
        # imports might each cover for the other).  Confirm the whole
        # `removable` set drops together; if not, greedily shrink it until the
        # file compiles, moving the culprits back into `needed`.
        if len(res.removable) > 1:
            write(res.removable)
            ok, _ = build(dir_path, res.vfile, flags)
            if ok:
                res.jointly_removable = True
            else:
                res.jointly_removable = False
                keep = list(res.removable)
                # Greedily remove one at a time from the drop-set until it builds.
                while keep:
                    write(keep)
                    ok, _ = build(dir_path, res.vfile, flags)
                    if ok:
                        break
                    moved = keep.pop()          # this one is NOT jointly-droppable
                    res.needed.append(moved)
                res.removable = keep
        res.verified = True
    finally:
        restore_and_rebuild()


# ---------------------------------------------------------------------------
# Checkpointing (crash-resilient / partial-harvest across a long verify run).
# ---------------------------------------------------------------------------
def _cand_dict(c: Candidate) -> dict:
    return {"token": c.token, "full_path": c.full_path,
            "lineno": c.stmt.lineno, "raw": c.stmt.raw}


def result_to_dict(r: FileResult) -> dict:
    return {
        "vfile": r.vfile,
        "verified": r.verified,
        "jointly_removable": r.jointly_removable,
        "candidates": [_cand_dict(c) for c in r.candidates],
        "removable": [_cand_dict(c) for c in r.removable],
        "needed": [_cand_dict(c) for c in r.needed],
    }


def save_checkpoint(path: str, results: dict[str, FileResult]) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump({k: result_to_dict(v) for k, v in results.items()}, f, indent=1)
    os.replace(tmp, path)


def load_checkpoint(path: str) -> dict[str, dict]:
    if not os.path.isfile(path):
        return {}
    with open(path) as f:
        return json.load(f)


class _DictCand:
    """Lightweight Candidate reconstructed from a checkpoint dict."""
    def __init__(self, d):
        self.token = d["token"]
        self.full_path = d["full_path"]
        self.stmt = type("S", (), {"lineno": d["lineno"], "raw": d["raw"]})()


def result_from_dict(d: dict) -> FileResult:
    r = FileResult(vfile=d["vfile"])
    r.verified = d["verified"]
    r.jointly_removable = d.get("jointly_removable", True)
    r.candidates = [_DictCand(c) for c in d["candidates"]]
    r.removable = [_DictCand(c) for c in d["removable"]]
    r.needed = [_DictCand(c) for c in d["needed"]]
    return r


# ---------------------------------------------------------------------------
# Reporting.
# ---------------------------------------------------------------------------
def render_report(results: list[FileResult], verified_mode: bool) -> str:
    lines: list[str] = []
    lines.append("# Unused-import report")
    lines.append("")
    total_removable = sum(len(r.removable) for r in results)
    files_with = [r for r in results if r.removable]
    total_needed = sum(len(r.needed) for r in results)
    if verified_mode:
        verified = [r for r in results if r.verified]
        lines.append(f"- Files build-verified: **{len(verified)}** "
                     f"(of {len(results)} analysed).")
        lines.append(f"- Build-confirmed **jointly**-removable imports: "
                     f"**{total_removable}** across **{len(files_with)}** files "
                     f"(each file's listed set was compiled with all of them "
                     f"removed together).")
        lines.append(f"- Glob candidates that build-testing showed are NEEDED "
                     f"(false positives -- instances/notations/hints): "
                     f"**{total_needed}**.")
        not_joint = [r for r in results if not r.jointly_removable]
        if not_joint:
            lines.append(f"- Files where some individually-redundant imports were "
                         f"NOT jointly removable (interdependence): "
                         f"{', '.join(r.vfile for r in not_joint)}.")
    else:
        total_cand = sum(len(r.candidates) for r in results)
        lines.append(f"- Glob-only candidates (NOT build-confirmed): "
                     f"**{total_cand}** across "
                     f"**{len([r for r in results if r.candidates])}** files.")
    lines.append("")

    if verified_mode:
        lines.append("## Build-confirmed removable imports")
        lines.append("")
        for r in results:
            if not r.removable:
                continue
            lines.append(f"### {r.vfile}")
            for c in r.removable:
                lines.append(f"- `{c.token}`  (logical `{c.full_path}`) "
                             f"-- line {c.stmt.lineno}: `{c.stmt.raw.strip()}`")
            lines.append("")
        lines.append("## Glob candidates that were actually NEEDED "
                     "(instances / notations / hints)")
        lines.append("")
        any_needed = False
        for r in results:
            if not r.needed:
                continue
            any_needed = True
            lines.append(f"### {r.vfile}")
            for c in r.needed:
                lines.append(f"- `{c.token}`  (logical `{c.full_path}`) "
                             f"-- line {c.stmt.lineno}: `{c.stmt.raw.strip()}`")
            lines.append("")
        if not any_needed:
            lines.append("_(none)_")
            lines.append("")
    else:
        lines.append("## Glob-only candidates (require --verify to confirm)")
        lines.append("")
        for r in results:
            if not r.candidates:
                continue
            lines.append(f"### {r.vfile}")
            for c in r.candidates:
                lines.append(f"- `{c.token}`  (logical `{c.full_path}`) "
                             f"-- line {c.stmt.lineno}: `{c.stmt.raw.strip()}`")
            lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dir", default=".", help="directory of .v files (default: .)")
    ap.add_argument("--verify", action="store_true",
                    help="build-confirm candidates (else: fast glob-only listing)")
    ap.add_argument("--all", action="store_true",
                    help="build-test EVERY import, ignoring the glob shortlist")
    ap.add_argument("--include-external", action="store_true",
                    help="also check imports of OTHER packages (SailStdpp, Riscv, "
                         "stdpp, iris.*, Kernel, Stdlib). Default: only this "
                         "package's own modules (local `-R .` prefix).")
    ap.add_argument("--include-export", action="store_true",
                    help="also consider `Require Export` lines (needs --full-make "
                         "to be sound; unsafe with single-file verify)")
    ap.add_argument("--files", nargs="*", default=None,
                    help="restrict to these .v files (default: all in --dir)")
    ap.add_argument("--report", default=None,
                    help="write the markdown report to this path (also prints)")
    ap.add_argument("--checkpoint", default=None,
                    help="JSON file of per-file results; written after each file "
                         "and reused on restart (crash-resilient / partial harvest)")
    args = ap.parse_args()

    dir_path = os.path.abspath(args.dir)
    if shutil.which("opam") is None:
        print("warning: `opam` not found; --verify will fail", file=sys.stderr)

    local_prefix = local_prefix_for_dir(dir_path)
    flags = coqc_flags(dir_path)
    if args.files:
        vfiles = sorted(args.files)
    else:
        vfiles = sorted(f for f in os.listdir(dir_path) if f.endswith(".v"))

    ckpt: dict[str, FileResult] = {}
    if args.checkpoint:
        for k, v in load_checkpoint(args.checkpoint).items():
            ckpt[k] = result_from_dict(v)

    results: list[FileResult] = []
    for vf in vfiles:
        if args.verify and vf in ckpt and ckpt[vf].verified:
            print(f"[skip] {vf}: from checkpoint", file=sys.stderr, flush=True)
            results.append(ckpt[vf])
            continue
        res = analyze_file(dir_path, vf, local_prefix,
                           args.include_export, args.all,
                           local_only=not args.include_external)
        if args.verify and res.candidates:
            print(f"[verify] {vf}: {len(res.candidates)} candidate(s)...",
                  file=sys.stderr, flush=True)
            verify_file(dir_path, res, flags)
        results.append(res)
        if args.checkpoint and args.verify:
            ckpt[vf] = res
            save_checkpoint(args.checkpoint, ckpt)

    report = render_report(results, verified_mode=args.verify)
    print(report)
    if args.report:
        with open(args.report, "w") as f:
            f.write(report + "\n")
        print(f"\n[wrote {args.report}]", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

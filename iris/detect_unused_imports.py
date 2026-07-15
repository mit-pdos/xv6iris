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

   Two rules keep the shortlist honest (each was a large false-positive source):

   a. GLOB FRESHNESS.  A missing `.glob` reads as "this file references nothing",
      which flags EVERY import; a `.glob` that does not match its `.v` misses any
      use added since the last build.  Neither is evidence of an unused import, so
      a file whose glob is missing/stale is reported as UNANALYSED (rebuild it, or
      pass `--all`, which build-tests and so needs no glob).  Freshness is decided
      on the `.v`'s md5, which coqc stamps into the glob's `DIGEST` line -- mtime
      would call a glob stale after a byte-identical `cp`/`git checkout`.
      `--allow-stale` opts back into trusting an out-of-date glob.

   b. EXPORT CLOSURE.  glob attributes a reference to the module that DEFINES the
      name, but `Require Export` makes a name reachable through an importer.  If
      `A.v` does `Require Export B` and our file does `Require Import A` and uses
      a name defined in B, glob records only a ref to B -- so A looks unused while
      removing it actually breaks the build (this is exactly what the `WpGpr*`
      shims do here).  Such an import is therefore not reported as REMOVABLE but
      as a REWRITE: nothing defined in A itself is used, so the fix is to import
      B -- the module actually providing the name -- directly, dropping A's
      forwarding indirection.  `--verify` build-tests that rewrite, not a bare
      deletion.  The closure is read from each module's own source, resolved
      through the `-R/-Q` load paths and the opam `user-contrib` tree; a module
      whose source cannot be found has an UNKNOWN closure and is conservatively
      never flagged.

3. CONFIRM (`--verify`, correct): for each file, apply ALL candidate edits at once
   (a removal drops its module; a rewrite drops it and adds the imports it
   forwards to) and rebuild.  If it still builds, every candidate is genuinely
   applicable.  If it fails, fall back to one candidate at a time.  A candidate
   that still builds is CONFIRMED; one that breaks the build was actually NEEDED
   (an instance/notation/hint false positive).  The file is ALWAYS restored to its
   original bytes afterwards (and its `.vo` rebuilt from the original so the tree
   stays green).

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
                                                    # (also covers unbuilt files)
  detect_unused_imports.py --dir . --allow-stale    # shortlist from out-of-date globs
  detect_unused_imports.py --dir . --verify --include-external   # also other packages
  detect_unused_imports.py --dir . --verify --files WpAdd.v WpAmo.v
  detect_unused_imports.py --dir . --verify --report unused_imports_report.md
  detect_unused_imports.py --dir . --verify --apply   # delete them; then `make`
"""
from __future__ import annotations

import argparse
import hashlib
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


def load_path_mappings(dir_path: str) -> list[tuple[str, str]]:
    """The `(directory, logical-prefix)` pairs a module name resolves through.

    The `-R/-Q` lines of _CoqProject, plus the opam switch's `user-contrib` tree
    (logical prefix "") so external packages (stdpp, iris, SailStdpp, Stdlib...)
    resolve too.
    """
    maps: list[tuple[str, str]] = []
    cp = os.path.join(dir_path, "_CoqProject")
    if os.path.isfile(cp):
        with open(cp) as f:
            toks = strip_comments(f.read()).split()
        i = 0
        while i < len(toks):
            if toks[i] in ("-R", "-Q") and i + 2 < len(toks):
                maps.append((os.path.join(dir_path, toks[i + 1]), toks[i + 2]))
                i += 3
            else:
                i += 1
    user_contrib = os.path.join(SWITCH, "_opam", "lib", "coq", "user-contrib")
    if os.path.isdir(user_contrib):
        maps.append((user_contrib, ""))
    return maps


def strip_comments(text: str) -> str:
    """Drop `#` comments from a _CoqProject."""
    return "\n".join(line.split("#", 1)[0] for line in text.splitlines())


def resolve_module_source(full_path: str, maps: list[tuple[str, str]]) -> str | None:
    """Filesystem path of the `.v` defining logical module `full_path`, if found."""
    for directory, prefix in maps:
        if prefix and full_path == prefix:
            rest = ""
        elif prefix:
            if not full_path.startswith(prefix + "."):
                continue
            rest = full_path[len(prefix) + 1:]
        else:
            rest = full_path
        if not rest:
            continue
        cand = os.path.join(directory, *rest.split(".")) + ".v"
        if os.path.isfile(cand):
            return cand
    return None


class ExportGraph:
    """Transitive `Require Export` closure of a logical module path.

    `closure(M)` returns `(modules, unknown)`: every module whose names `Import M`
    brings into scope, and whether some source along the way could not be resolved
    (in which case the closure is incomplete and the caller must stay conservative).
    """

    def __init__(self, maps: list[tuple[str, str]]):
        self.maps = maps
        self._direct: dict[str, set[str] | None] = {}
        self._closure: dict[str, tuple[frozenset[str], bool]] = {}

    def direct_exports(self, full_path: str) -> set[str] | None:
        """Modules `full_path` re-exports directly; None if its source is missing."""
        if full_path in self._direct:
            return self._direct[full_path]
        src = resolve_module_source(full_path, self.maps)
        if src is None:
            self._direct[full_path] = None
            return None
        # A module's own `-R .` prefix is everything up to its last component.
        own_prefix = full_path.rsplit(".", 1)[0] if "." in full_path else ""
        out: set[str] = set()
        try:
            with open(src, errors="replace") as f:
                text = f.read()
        except OSError:
            self._direct[full_path] = None
            return None
        for stmt in parse_imports(text):
            if stmt.kind != "export":
                continue
            for token in stmt.modules:
                out.add(logical_path(stmt, token, own_prefix))
        self._direct[full_path] = out
        return out

    def closure(self, full_path: str) -> tuple[frozenset[str], bool]:
        if full_path in self._closure:
            return self._closure[full_path]
        # Seed with a self-referential entry so an Export cycle terminates.
        self._closure[full_path] = (frozenset([full_path]), False)
        seen = {full_path}
        unknown = False
        direct = self.direct_exports(full_path)
        if direct is None:
            unknown = True
        else:
            for m in direct:
                sub, sub_unknown = self.closure(m)
                seen |= sub
                unknown = unknown or sub_unknown
        result = (frozenset(seen), unknown)
        self._closure[full_path] = result
        return result


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


def classify_import(full_path: str, used: set[str],
                    graph: ExportGraph) -> tuple[str, list[str]] | None:
    """How (if at all) `Require Import full_path` is actionable.

    Returns None when the import is needed as written, else `(kind, via)`:

      ('remove',  [])    -- neither the module nor anything it re-exports is
                            referenced: a candidate for deletion.
      ('rewrite', [M..]) -- NO name defined in the module itself is referenced,
                            but names it re-exports are.  The import is doing
                            nothing but forwarding, so the candidate is to import
                            the modules actually providing those names directly
                            (see rule (b)).  `via` is the minimal such set: any
                            member reachable by Export from another is dropped,
                            since importing the latter already brings it in.

    An unresolvable Export closure yields None (conservative: never flagged).
    """
    modules, unknown = graph.closure(full_path)
    if unknown:
        return None
    if is_referenced(full_path, used):
        return None                       # the module itself provides a name
    via = {m for m in modules if m != full_path and is_referenced(m, used)}
    if not via:
        return ("remove", [])
    # Keep only maximal elements: drop any X already re-exported by another
    # member Y, since `Import Y` brings X's names along anyway.
    minimal = [x for x in via
               if not any(y != x and x in graph.closure(y)[0] for y in via)]
    return ("rewrite", sorted(minimal))


def import_line(full_path: str, local_prefix: str) -> str:
    """Source text of a `Require Import` bringing in logical module `full_path`."""
    if local_prefix and full_path.startswith(local_prefix + "."):
        return f"Require Import {full_path[len(local_prefix) + 1:]}."
    head, _, rest = full_path.partition(".")
    if rest and head in KNOWN_LIB_PREFIXES:
        return f"From {head} Require Import {rest}."
    return f"Require Import {full_path}."


def glob_status(dir_path: str, vfile: str) -> str:
    """'fresh' | 'stale' | 'missing' -- is the file's `.glob` usable as evidence?

    coqc stamps the `.v`'s md5 into the glob's leading `DIGEST` line, so freshness
    is decided on CONTENT.  That is what we want: mtime would call a glob stale
    after a `cp`/`git checkout`/verify-restore that changed no bytes, and every
    such false 'stale' silently costs the file its analysis.
    """
    path = os.path.join(dir_path, vfile)
    glob = os.path.join(dir_path, vfile[:-2] + ".glob")
    if not os.path.isfile(glob):
        return "missing"
    try:
        with open(glob, errors="replace") as f:
            first = f.readline().split()
        with open(path, "rb") as f:
            digest = hashlib.md5(f.read()).hexdigest()
    except OSError:
        return "missing"
    if len(first) == 2 and first[0] == "DIGEST":
        return "fresh" if first[1] == digest else "stale"
    # No DIGEST line (unexpected): fall back to the mtime comparison.
    return "stale" if os.path.getmtime(path) > os.path.getmtime(glob) else "fresh"


# ---------------------------------------------------------------------------
# Per-file analysis.
# ---------------------------------------------------------------------------
@dataclass
class Candidate:
    stmt: ImportStmt
    token: str
    full_path: str
    kind: str = "remove"               # 'remove' | 'rewrite'
    via: list[str] = field(default_factory=list)   # 'rewrite': import these instead


@dataclass
class FileResult:
    vfile: str
    candidates: list[Candidate] = field(default_factory=list)
    removable: list[Candidate] = field(default_factory=list)   # build-confirmed
    needed: list[Candidate] = field(default_factory=list)      # false positives
    verified: bool = False
    jointly_removable: bool = True   # do all `removable` compile when dropped together?
    note: str = ""
    glob_state: str = "fresh"        # 'fresh' | 'stale' | 'missing'
    analysed: bool = True            # False => no usable evidence, NOT "no candidates"


def analyze_file(dir_path: str, vfile: str, local_prefix: str,
                 include_export: bool, use_all: bool,
                 graph: ExportGraph,
                 local_only: bool = True,
                 allow_stale: bool = False) -> FileResult:
    path = os.path.join(dir_path, vfile)
    with open(path) as f:
        text = f.read()
    glob = os.path.join(dir_path, vfile[:-2] + ".glob")
    used = referenced_libnames(glob)

    res = FileResult(vfile=vfile)
    res.glob_state = glob_status(dir_path, vfile)
    # `--all` build-tests every import and never consults the glob, so its verdict
    # does not depend on glob freshness.  The shortlist does: an absent/outdated
    # glob is not evidence of non-use, it is absence of evidence (rule (a)).
    if not use_all and res.glob_state != "fresh":
        if not (res.glob_state == "stale" and allow_stale):
            res.analysed = False
            res.note = f"{res.glob_state} .glob -- rebuild the file, or use --all"
            return res
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
            if use_all:
                res.candidates.append(Candidate(stmt=stmt, token=token, full_path=fp))
                continue
            verdict = classify_import(fp, used, graph)
            if verdict is None:
                continue
            kind, via = verdict
            res.candidates.append(Candidate(stmt=stmt, token=token, full_path=fp,
                                            kind=kind, via=via))
    return res


# ---------------------------------------------------------------------------
# File rewriting for build-tests.
# ---------------------------------------------------------------------------
def apply_edits(text: str, edits: list[Candidate], local_prefix: str) -> str:
    """Return `text` with each candidate's proposed edit applied.

    Every candidate drops its own module token from its statement (deleting the
    line if nothing is left).  A 'rewrite' candidate additionally emits the
    imports it forwards to, on their own line after the original statement --
    a separate line because the replacement may need a different `From` prefix.
    """
    # Group tokens to drop per line number.
    by_line: dict[int, set[str]] = {}
    stmt_by_line: dict[int, ImportStmt] = {}
    added_by_line: dict[int, list[str]] = {}
    for c in edits:
        by_line.setdefault(c.stmt.lineno, set()).add(c.token)
        stmt_by_line[c.stmt.lineno] = c.stmt
        for m in c.via:
            line = import_line(m, local_prefix)
            if line not in added_by_line.setdefault(c.stmt.lineno, []):
                added_by_line[c.stmt.lineno].append(line)

    out_lines: list[str] = []
    for i, line in enumerate(text.splitlines(), start=1):
        if i not in by_line:
            out_lines.append(line)
            continue
        stmt = stmt_by_line[i]
        remaining = [m for m in stmt.modules if m not in by_line[i]]
        if remaining:
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
        out_lines.extend(added_by_line.get(i, []))
    trailing_nl = "\n" if text.endswith("\n") else ""
    return "\n".join(out_lines) + trailing_nl


def apply_removals(dir_path: str, vfile: str, confirmed, local_prefix: str,
                   include_rewrites: bool = False) -> int:
    """Apply the build-confirmed edits of `confirmed` to `vfile` on disk.

    Re-parses the file and re-matches each candidate by (lineno, token), so this
    works both for freshly-verified results and for ones reloaded from a
    checkpoint (whose `stmt` is a stub carrying only lineno/raw).  A candidate
    that no longer matches means the file moved under us since it was verified;
    that is a hard error rather than a silent skip -- applying a stale removal
    would delete the wrong line.

    Only 'remove' candidates are applied unless `include_rewrites`.  A 'rewrite'
    is not dead code: the import forwards a name that IS used, so deleting it
    breaks the build (what --verify confirmed is the re-point, not a deletion),
    and re-pointing it is a layering judgement -- the re-exporting shims in this
    tree are deliberate.  Each candidate's `kind`/`via` must therefore be carried
    through here; rebuilding it as a bare Candidate would silently downgrade a
    verified rewrite into an unverified deletion.
    """
    todo = [c for c in confirmed
            if getattr(c, "kind", "remove") == "remove" or include_rewrites]
    if not todo:
        return 0
    path = os.path.join(dir_path, vfile)
    with open(path) as f:
        text = f.read()
    stmts = {s.lineno: s for s in parse_imports(text)}
    edits: list[Candidate] = []
    for c in todo:
        stmt = stmts.get(c.stmt.lineno)
        if stmt is None or c.token not in stmt.modules:
            raise SystemExit(
                f"apply: {vfile}:{c.stmt.lineno} no longer matches the verified "
                f"import of `{c.token}` -- the file changed since verification; "
                f"re-run without a stale --checkpoint"
            )
        edits.append(Candidate(stmt=stmt, token=c.token, full_path=c.full_path,
                               kind=getattr(c, "kind", "remove"),
                               via=list(getattr(c, "via", []))))
    with open(path, "w") as f:
        f.write(apply_edits(text, edits, local_prefix))
    return len(edits)


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


def verify_file(dir_path: str, res: FileResult, flags: list[str],
                local_prefix: str) -> None:
    """Build-confirm which of `res`'s candidate edits actually still compile."""
    if not res.candidates:
        res.verified = True
        return
    path = os.path.join(dir_path, res.vfile)
    with open(path) as f:
        original = f.read()
    backup = original

    def write(cands):
        with open(path, "w") as f:
            f.write(apply_edits(original, cands, local_prefix))

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
            "lineno": c.stmt.lineno, "raw": c.stmt.raw,
            "kind": c.kind, "via": list(c.via)}


def describe(c: Candidate) -> str:
    """One report bullet for a candidate."""
    where = (f"- `{c.token}`  (logical `{c.full_path}`) "
             f"-- line {c.stmt.lineno}: `{c.stmt.raw.strip()}`")
    if c.kind == "rewrite":
        where += "\n  - provides no referenced name itself; import instead: " + \
                 ", ".join(f"`{m}`" for m in c.via)
    return where


def result_to_dict(r: FileResult) -> dict:
    return {
        "vfile": r.vfile,
        "verified": r.verified,
        "jointly_removable": r.jointly_removable,
        "glob_state": r.glob_state,
        "analysed": r.analysed,
        "note": r.note,
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
        self.kind = d.get("kind", "remove")
        self.via = d.get("via", [])
        self.stmt = type("S", (), {"lineno": d["lineno"], "raw": d["raw"]})()


def result_from_dict(d: dict) -> FileResult:
    r = FileResult(vfile=d["vfile"])
    r.verified = d["verified"]
    r.jointly_removable = d.get("jointly_removable", True)
    r.glob_state = d.get("glob_state", "fresh")
    r.analysed = d.get("analysed", True)
    r.note = d.get("note", "")
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
    n_rewrite = sum(1 for r in results for c in r.candidates
                    if getattr(c, "kind", "remove") == "rewrite")
    if verified_mode:
        verified = [r for r in results if r.verified]
        n_rw = sum(1 for r in results for c in r.removable
                   if getattr(c, "kind", "remove") == "rewrite")
        lines.append(f"- Files build-verified: **{len(verified)}** "
                     f"(of {len(results)} analysed).")
        lines.append(f"- Build-confirmed **jointly**-applicable edits: "
                     f"**{total_removable}** across **{len(files_with)}** files "
                     f"({total_removable - n_rw} removals, {n_rw} re-points at "
                     f"the module providing the name) -- each file's listed set "
                     f"was compiled with all of them applied together.")
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
                     f"**{len([r for r in results if r.candidates])}** files "
                     f"({total_cand - n_rewrite} to remove, {n_rewrite} to "
                     f"re-point at the module providing the name).")
    unanalysed = [r for r in results if not r.analysed]
    if unanalysed:
        lines.append(f"- Files SKIPPED for lack of usable `.glob` evidence: "
                     f"**{len(unanalysed)}** (see below) -- their imports are "
                     f"neither confirmed used nor unused.")
    lines.append("")

    if verified_mode:
        lines.append("## Build-confirmed edits")
        lines.append("")
        for r in results:
            if not r.removable:
                continue
            lines.append(f"### {r.vfile}")
            for c in r.removable:
                lines.append(describe(c))
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
                lines.append(describe(c))
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
                lines.append(describe(c))
            lines.append("")

    unanalysed = [r for r in results if not r.analysed]
    if unanalysed:
        lines.append("## Files skipped (no usable `.glob`)")
        lines.append("")
        lines.append("A missing/outdated `.glob` is absence of evidence, not "
                     "evidence of an unused import -- flagging these files' "
                     "imports would be a false positive.  Rebuild them (or pass "
                     "`--all` to build-test their imports without a glob).")
        lines.append("")
        for r in unanalysed:
            lines.append(f"- `{r.vfile}` -- {r.note}")
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
                    help="build-test EVERY import, ignoring the glob shortlist "
                         "(needs no .glob, so it also covers unbuilt files)")
    ap.add_argument("--allow-stale", action="store_true",
                    help="shortlist from a .glob older than its .v (may report "
                         "imports used only by edits made since the last build)")
    ap.add_argument("--apply", action="store_true",
                    help="DELETE the build-confirmed removable imports from the "
                         ".v files (requires --verify; the glob shortlist alone "
                         "is ~half false positives and must never be applied). "
                         "Only 'remove' candidates are applied: a 'rewrite' is a "
                         "layering judgement (the re-exporting shims here are "
                         "deliberate), so it is reported for a human and applied "
                         "only under --apply-rewrites. "
                         "Single-file compiles do not prove the WHOLE tree still "
                         "builds -- `Require` is transitive for LOADING, so a "
                         "downstream file may reference a module this one pulled "
                         "in.  Always run a full `make` afterwards.")
    ap.add_argument("--apply-rewrites", action="store_true",
                    help="with --apply, ALSO re-point build-confirmed 'rewrite' "
                         "candidates at the module providing the name (off by "
                         "default: it rewrites deliberate shim imports)")
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

    if args.apply and not args.verify:
        ap.error("--apply requires --verify (refusing to delete unconfirmed "
                 "glob candidates)")

    dir_path = os.path.abspath(args.dir)
    if shutil.which("opam") is None:
        print("warning: `opam` not found; --verify will fail", file=sys.stderr)

    local_prefix = local_prefix_for_dir(dir_path)
    flags = coqc_flags(dir_path)
    graph = ExportGraph(load_path_mappings(dir_path))
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
                           args.include_export, args.all, graph,
                           local_only=not args.include_external,
                           allow_stale=args.allow_stale)
        if args.verify and res.candidates:
            print(f"[verify] {vf}: {len(res.candidates)} candidate(s)...",
                  file=sys.stderr, flush=True)
            verify_file(dir_path, res, flags, local_prefix)
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

    # Apply LAST: verify_file() restores every file it touched, so the on-disk
    # text is the original one the candidates' line numbers refer to.
    if args.apply:
        n_imports = n_files = 0
        for r in results:
            k = apply_removals(dir_path, r.vfile, r.removable, local_prefix,
                               include_rewrites=args.apply_rewrites)
            if k:
                n_files += 1
                n_imports += k
                print(f"[apply] {r.vfile}: removed {k} import(s)",
                      file=sys.stderr, flush=True)
        # NB: `.github/workflows/dead-imports.yml` greps this exact wording to
        # build its commit message -- keep the phrasing in sync with it.
        print(f"[apply] removed {n_imports} import(s) across {n_files} file(s)",
              file=sys.stderr)
        skipped = sum(1 for r in results for c in r.removable
                      if getattr(c, "kind", "remove") == "rewrite")
        if skipped and not args.apply_rewrites:
            print(f"[apply] left {skipped} confirmed re-point(s) for a human "
                  f"(see the report; --apply-rewrites applies them)",
                  file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

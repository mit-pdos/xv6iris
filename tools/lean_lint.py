#!/usr/bin/env python3
"""Source lints for the Lean tree (run by tools/ci/lint.sh; no toolchain needed).

Each lint guards something the BUILD cannot tell you, because the build is
green either way:

  sorry      no `sorry` / `admit` token in Xv6/ or MachCSL/ (outside comments
             and strings).  A `sorry` only WARNS at build time; this is the
             Lean counterpart of grepping for `Admitted`.
  axiom      no `axiom` declaration in Xv6/ or MachCSL/.  (The model's
             RiscvExtras.lean has the Sail externs; they are outside these
             trees and the axiom audit accounts for them.)
  native     no `native_decide` (it adds `Lean.ofReduceBool` to the trusted
             base; the baseline has only `bv_decide` certificates).
  options    no file-level `set_option autoImplicit true` (the lakefile turns
             it off; a file turning it back on lets a typo become a variable).
  drift      MODULE DRIFT: every .lean file under Xv6/ and MachCSL/ is
             reached, through imports, from the roots lake builds (Xv6.lean,
             MachCSL.lean).  A file that is not is compiled by NOBODY -- a
             proof in it is a claim no build has checked, and CI would stay
             green over it.  This is Rocq's `_CoqProject` drift check
             (tools/proof_coverage.py --check there).  A file that is out of
             the build ON PURPOSE must say so with a row in
             tools/ci/lint_allow.txt; a row naming a file that does not
             exist, or one that IS built, is an error too.
             Also: an `import Xv6.…`/`import MachCSL.…` of a module with no
             file, and a module imported twice by one file.

vtest-lean/ (the device-conformance suite, outside the proof build) gets the
`sorry`, `axiom` and `options` lints only: a test there passes by compiling,
so a `sorry` would be a green test that checked nothing; its `native_decide`
is intentional, and which of its files are built is tools/vtest's business.

Rocq's comment lint (tools/comment_quote_check.py) has no counterpart: Lean
does not lex string literals inside comments, so a quotation cannot swallow a
comment terminator.

Usage: tools/lean_lint.py [--repo DIR] [--only LINT ...]
Exit status 1 when any lint finds something.
"""
import argparse
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREES = ["Xv6", "MachCSL"]
ROOTS = ["Xv6", "MachCSL"]           # the lake default targets
# Trees outside the proof build that still must not fake a result.  vtest-lean/
# (the device-conformance suite, its own `Vtest` lake library) gets the
# `sorry`, `axiom` and `options` lints only: a test passes by COMPILING, so a
# `sorry` there would be a green test that checked nothing.  Its
# `native_decide` is how those tests evaluate the model and is intentional;
# and which of its files are built is its own manifest's business
# (tools/vtest), not the drift lint's.
SIDE_TREES = {"vtest-lean": ("sorry", "axiom", "options")}


def blank_comments_and_strings(src):
    """Replace comments (`--`, nested `/- -/`) and string literals by spaces,
    keeping every newline, so offsets and line numbers are unchanged."""
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
        elif c == '"':
            out[i] = " "
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    if src[i + 1] != "\n":
                        out[i + 1] = " "
                    out[i] = " "
                    i += 2
                    continue
                if src[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        elif c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == "\\" and "'" in src[i + 2:i + 8])):
            # a character literal ('"', '\n', '\x41'); an identifier's prime is
            # never followed by this shape because the char before it is a letter
            if i > 0 and (src[i - 1].isalnum() or src[i - 1] in "_'!?"):
                i += 1
                continue
            j = src.index("'", i + 2 if src[i + 1] != "\\" else i + 3)
            for k in range(i, j + 1):
                out[k] = " "
            i = j + 1
        elif c == "«":
            j = src.find("»", i)
            i = (j + 1) if j >= 0 else n      # a quoted identifier: code, but skip its contents
        else:
            i += 1
    return "".join(out)


def lean_files(repo, trees=TREES):
    out = []
    for t in trees:
        for dp, _, fs in os.walk(os.path.join(repo, t)):
            for f in sorted(fs):
                if f.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(dp, f), repo))
    return sorted(out)


# a token that is not part of a longer identifier (Lean identifiers may hold . _ ' ! ?)
def _token(word):
    return re.compile(r"(?<![\w.'!?«])%s(?![\w'!?»])" % re.escape(word))


TOKEN_LINTS = [
    ("sorry", _token("sorry"), "`sorry`"),
    ("sorry", _token("admit"), "`admit` (the tactic is `sorry`)"),
    ("sorry", _token("sorryAx"), "`sorryAx`"),
    ("native", _token("native_decide"), "`native_decide`"),
]
AXIOM_RE = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)?(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*axiom[ \t]", re.M)
AUTOIMPL_RE = re.compile(r"set_option[ \t]+(?:relaxedAutoImplicit|autoImplicit)[ \t]+true")
CANDIDATE_RE = re.compile(r"sorry|admit|native_decide|axiom|utoImplicit")
IMPORT_RE = re.compile(r"^[ \t]*(?:public[ \t]+|meta[ \t]+|private[ \t]+)*import[ \t]+(?:all[ \t]+)?(\S+)", re.M)


def lint_text(path, src):
    """-> [(lint, path, line, message)] for the per-file token lints."""
    # the blanking pass is a character loop; skip it for the (many, some huge)
    # files in which no lint could fire even counting comments
    if not CANDIDATE_RE.search(src):
        return []
    code = blank_comments_and_strings(src)
    out = []

    def line_of(off):
        return code.count("\n", 0, off) + 1

    for lint, rx, what in TOKEN_LINTS:
        for m in rx.finditer(code):
            out.append((lint, path, line_of(m.start()), what))
    for m in AXIOM_RE.finditer(code):
        out.append(("axiom", path, line_of(m.end()), "an `axiom` declaration"))
    for m in AUTOIMPL_RE.finditer(code):
        out.append(("options", path, line_of(m.start()), "`" + " ".join(m.group(0).split()) + "`"))
    return out


def imports_of(src):
    """The modules a file imports.  Imports are the file's header: the scan
    stops at the first line that is neither an import, a comment nor blank
    (so it never walks the megabytes of a generated image)."""
    out, depth = [], 0
    for line in src.split("\n"):
        s = line
        if depth:
            if "-/" not in s:
                continue
            depth, s = 0, s.split("-/", 1)[1]
        s = s.split("--")[0].strip()
        if s.startswith("/-"):
            if "-/" not in s[2:]:
                depth = 1
            continue
        if not s or s in ("module", "prelude"):
            continue
        m = IMPORT_RE.match(s)
        if not m:
            break
        out.append(m.group(1))
    return out


def module_of(rel):
    return rel[:-len(".lean")].replace(os.sep, ".")


def read_allow(path):
    """tools/ci/lint_allow.txt: `<file> # reason` rows -> [file]."""
    rows = []
    if os.path.exists(path):
        for raw in open(path, encoding="utf-8"):
            line = raw.split("#")[0].strip()
            if line:
                rows.append(line)
    return rows


def lint_drift(repo, sources, allow):
    """sources: {relpath: text} for every .lean of the trees plus the root files."""
    out = []
    mod_file = {module_of(p): p for p in sources}
    imports = {}
    for p, src in sources.items():
        imps = imports_of(src)
        seen = set()
        for i in imps:
            if i in seen:
                out.append(("drift", p, 0, f"imports {i} twice"))
            seen.add(i)
            if i.split(".")[0] in TREES and i not in mod_file:
                out.append(("drift", p, 0, f"imports {i}, which has no file"))
        imports[module_of(p)] = imps
    reached, stack = set(), [r for r in ROOTS if r in mod_file]
    for r in ROOTS:
        if r not in mod_file:
            out.append(("drift", r + ".lean", 0, "the root file lake builds is missing"))
    while stack:
        m = stack.pop()
        if m in reached:
            continue
        reached.add(m)
        stack.extend(i for i in imports.get(m, ()) if i in mod_file)
    allowed = set(allow)
    for m, p in sorted(mod_file.items()):
        if m not in reached and p not in allowed:
            out.append(("drift", p, 0,
                        "is not reached from Xv6.lean / MachCSL.lean, so no build compiles it; "
                        "import it, or add a row to tools/ci/lint_allow.txt saying it is out "
                        "of the build on purpose"))
    for p in sorted(allowed):
        if p not in sources:
            out.append(("drift", p, 0, "tools/ci/lint_allow.txt names it, but no such file exists "
                                       "-- drop the stale row"))
        elif module_of(p) in reached:
            out.append(("drift", p, 0, "tools/ci/lint_allow.txt says it is out of the build, "
                                       "but it is imported -- the row is a lie about the build"))
    return out


def run(repo, only=None):
    files = lean_files(repo)
    sources = {}
    for p in files + [r + ".lean" for r in ROOTS]:
        full = os.path.join(repo, p)
        if os.path.exists(full):
            sources[p] = open(full, encoding="utf-8").read()
    found = []
    nside = 0
    for p in files:
        found += lint_text(p, sources[p])
    found += lint_drift(repo, sources, read_allow(os.path.join(repo, "tools/ci/lint_allow.txt")))
    for tree, lints in SIDE_TREES.items():
        if not os.path.isdir(os.path.join(repo, tree)):
            continue
        side = lean_files(repo, [tree])
        for p in side:
            with open(os.path.join(repo, p), encoding="utf-8") as fh:
                found += [f for f in lint_text(p, fh.read()) if f[0] in lints]
        nside += len(side)
    if only:
        found = [f for f in found if f[0] in only]
    return found, len(files) + nside


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--only", nargs="+", choices=("sorry", "axiom", "native", "options", "drift"))
    a = ap.parse_args(argv)
    found, nfiles = run(os.path.abspath(a.repo), a.only)
    for lint, path, line, msg in found:
        where = f"{path}:{line}" if line else path
        print(f"lint[{lint}]: {where}: {msg}")
    names = a.only or ["sorry", "axiom", "native", "options", "drift"]
    if found:
        print(f"lint: {len(found)} finding(s) in {nfiles} files ({', '.join(names)})")
        return 1
    print(f"lint: ok ({nfiles} files; {', '.join(names)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

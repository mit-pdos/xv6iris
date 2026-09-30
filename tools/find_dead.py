#!/usr/bin/env python3
"""find_dead.py -- declarations the top theorems do not depend on.

The Lean counterpart of Rocq's iris/find_dead.py (main).  That tool reads
`.glob` files and reports definitions whose NAME no file references.  This
one reads `envfacts.tsv` -- the output of tools/ci/EnvFacts.lean, a
metaprogram over the elaborated environment -- and reports declarations that
are not in the CONE of the top theorems (tools/ci/roots.txt): reachable
through no chain of types and proof terms from a theorem the project claims.

That is a stronger and a more exact notion than "unreferenced":

  * a lemma used only by another dead lemma is dead here (the glob tool
    calls it live);
  * a use through a typeclass instance, a `simp` set, an auto-bound argument
    or a tactic-generated term IS an edge, because the edge is read off the
    proof term the elaborator produced, not off the source text.  The glob
    tool's biggest false-positive classes (hint-database lemmas, module
    signature obligations) do not arise.

What would still be a false positive is suppressed rather than left to the
reader, and counted:

  * INSTANCES, and what only instances use.  An instance no reached term
    resolved is unused today, but instances are declared for whoever needs
    them next; they are reported only with --all.
  * METAPROGRAMS (syntax, macros, elaborators, simprocs) and what only they
    use: they run at elaboration time and leave no edge in any term.
  * the ALLOWLIST tools/ci/dead_allow.txt (demos, tools): declarations,
    modules or namespaces that are roots in their own right.
  * a `KEEP-UNREFERENCED` marker in the comment right above a declaration.

Only Xv6/ and MachCSL/ are analysed.  vtest-lean/ (the `Vtest` library) is a
test suite with no top theorem of its own: its modules are not loaded, and a
declaration of MachCSL that only a vtest uses is reported here as unreached
-- which is what it is, for the proofs.

Generated declarations (recursors, projections, equation lemmas, matchers,
`deriving` output) are never listed: they are not removable on their own.

The rest is TRIAGED (--triage), heuristically -- hints, not verdicts:

  wholly unreached modules   no declaration of the module is reached: a
                             dead-FILE candidate (or a top-level result that
                             is not in roots.txt yet)
  generated files            image data / address equations nothing uses yet
  contracts                  a Spec structure, a `wp_…_body`, a Link theorem:
                             a stated or linked result nothing consumes
  `rfl` lemmas               NOT known dead: `simp`/`dsimp` use a lemma proved
                             by `rfl` definitionally and leave no reference to
                             it in the term, so the cone cannot see the use
  attribute-tagged           a `@[simp]`/`@[k_addr]`/... lemma no reached
                             proof ever fired
  named elsewhere            a helper whose name occurs elsewhere in the
                             sources: used by another dead declaration, named
                             in a `simp` list that did not need it, or in a
                             comment
  helper candidates          everything else: outside the cone AND named
                             nowhere -- likely reviewable for removal

The run ends with the whole-FILE reports: the modules no other module
imports (expected: the roots' umbrella leaves -- top theorems, demos), and
the wholly unreached ones.

INFORMATIONAL: always exits 0 (like Rocq's step, which is
`continue-on-error`).  Read the counts in the trailing `==` line before
trusting a clean report: an empty facts file reports nothing.

Usage:
    tools/find_dead.py [--facts envfacts.tsv] [--triage] [--all] [--format text|md]
                       [--kinds thm,def] [--files-only] [--no-files] [--top N]
"""
import argparse
import os
import re
import sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

KIND_LABEL = {"thm": "theorem", "def": "def", "opaque": "opaque", "axiom": "axiom",
              "ind": "inductive", "struct": "structure", "class": "class", "inst": "instance"}
PRIMARY = {"thm", "def", "opaque", "axiom", "ind", "struct", "class"}

CAT_MODULE = "wholly unreached module"
CAT_GEN = "generated file (image data / address equations)"
CAT_CONTRACT = "contract (Spec structure / body / Link theorem) nothing consumes"
CAT_RFL = "`rfl` lemma -- simp/dsimp use it without leaving a term: NOT known dead"
CAT_ATTR = "attribute-tagged lemma no reached proof fired"
CAT_NAMED = "helper whose name appears elsewhere (a dead proof, a simp list, a comment)"
CAT_HELPER = "helper candidate, named nowhere else -- likely reviewable for removal"
CAT_ORDER = [CAT_GEN, CAT_RFL, CAT_CONTRACT, CAT_ATTR, CAT_NAMED, CAT_HELPER]

BODY_RE = re.compile(r"(^|\.)(wp_\w+_body|wp[A-Z]\w*Body)$")
IFACE_RE = re.compile(r"(^|\.)[A-Z][A-Z0-9_]+$")


class Decl:
    __slots__ = ("module", "name", "kind", "line", "reach", "flags")

    def __init__(self, module, name, kind, line, reach, flags):
        self.module, self.name, self.kind = module, name, kind
        self.line, self.reach, self.flags = line, reach, flags


def load(path):
    """-> (decls, imports {module: [import]}, roots [(name, kind)], cone size)."""
    decls, imports, roots, cone = [], {}, [], 0
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            p = raw.rstrip("\n").split("\t")
            if p[0] == "C":
                decls.append(Decl(p[1], p[2], p[3], int(p[4]), int(p[5]),
                                  set(p[6].split(",")) if len(p) > 6 and p[6] else set()))
            elif p[0] == "G":
                imports[p[1]] = [x for x in p[2].split(",") if x] if len(p) > 2 else []
            elif p[0] == "ROOT":
                roots.append((p[1], p[2]))
            elif p[0] == "N":
                cone = int(p[2])
    return decls, imports, roots, cone


def module_path(repo, module):
    return os.path.join(repo, module.replace(".", os.sep) + ".lean")


class Sources:
    """Source lines, read lazily (for the KEEP marker and the triage)."""

    def __init__(self, repo):
        self.repo, self.cache = repo, {}

    def lines(self, module):
        if module not in self.cache:
            try:
                with open(module_path(self.repo, module), encoding="utf-8") as f:
                    self.cache[module] = f.read().split("\n")
            except OSError:
                self.cache[module] = []
        return self.cache[module]

    def generated(self, module):
        return any("AUTO-GENERATED" in l for l in self.lines(module)[:6])

    def keep_marked(self, d):
        """A `KEEP-UNREFERENCED` in the declaration's own header: the comment
        block directly above it (up to the previous declaration)."""
        ls = self.lines(d.module)
        i, steps = d.line - 2, 0
        stop = re.compile(r"^\s*(theorem|lemma|def|instance|structure|inductive|class|abbrev|"
                          r"opaque|axiom|end|namespace|section)\b")
        while 0 <= i < len(ls) and steps < 14:
            if "KEEP-UNREFERENCED" in ls[i]:
                return True
            if stop.match(ls[i]):
                break
            i -= 1
            steps += 1
        return False

    IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")

    def mentions(self, modules):
        """{identifier component: number of occurrences in the sources of
        `modules`} -- generated files excluded (they are megabytes of data and
        name nothing but themselves).  A declaration's own statement is one."""
        if getattr(self, "_mentions", None) is None:
            cnt = defaultdict(int)
            for m in modules:
                if self.generated(m):
                    continue
                for tok in self.IDENT_RE.findall("\n".join(self.lines(m))):
                    cnt[tok] += 1
            self._mentions = cnt
        return self._mentions

    def attributed(self, d):
        ls = self.lines(d.module)
        for i in (d.line - 1, d.line - 2):
            if 0 <= i < len(ls) and ls[i].lstrip().startswith("@["):
                return True
        return False


def category(d, src, modules=()):
    if src.generated(d.module):
        return CAT_GEN
    if "rfl" in d.flags:
        return CAT_RFL
    base = d.module.split(".")[-1]
    if ((d.kind in ("struct", "class") and IFACE_RE.search(d.name)) or BODY_RE.search(d.name)
            or (d.kind == "def" and "prop" in d.flags
                and (IFACE_RE.search(d.name) or base.startswith("Spec")))
            or (d.kind == "thm" and (base.startswith("Link") or base.endswith("Link")))):
        return CAT_CONTRACT
    if d.kind == "thm" and src.attributed(d):
        return CAT_ATTR
    if src.mentions(modules).get(d.name.split(".")[-1], 0) > 1:
        return CAT_NAMED
    return CAT_HELPER


def analyze(decls, want, src):
    """-> dict(dead, kept, implicit, allowed, dead_modules, n_modules)."""
    by_mod = defaultdict(list)
    for d in decls:
        by_mod[d.module].append(d)
    # a module none of whose declarations is live in ANY sense
    dead_modules = sorted(m for m, ds in by_mod.items() if all(d.reach == 0 for d in ds))
    cand = [d for d in decls if d.reach == 0 and d.kind in want]
    kept = [d for d in cand if src.keep_marked(d)]
    keptset = set(id(d) for d in kept)
    dead = [d for d in cand if id(d) not in keptset]
    return dict(dead=dead, kept=kept,
                implicit=[d for d in decls if d.reach in (3, 4)],
                allowed=[d for d in decls if d.reach == 2],
                dead_modules=dead_modules, n_modules=len(by_mod), by_mod=by_mod)


def unimported(imports, roots=("Xv6", "MachCSL")):
    """Local modules that no other local module imports, the umbrella roots'
    own import lists aside (every module is in one of those)."""
    imported = set()
    for m, imps in imports.items():
        if m in roots:
            continue
        imported.update(imps)
    return sorted(m for m in imports if m not in imported and m not in roots)


def fmt_decl(d):
    return f"  {d.module.replace('.', '/')}.lean:{d.line:<6} {KIND_LABEL.get(d.kind, d.kind):<10} {d.name}"


def render_text(res, imports, roots, cone, a, src):
    out = []
    w = out.append
    dead, dm = res["dead"], set(res["dead_modules"])
    if a.files_only:
        dead = []
    total = len(dead)
    if not a.files_only and not a.triage:
        by_file = defaultdict(list)
        for d in dead:
            by_file[d.module].append(d)
        for m in sorted(by_file):
            tag = "  [WHOLLY UNREACHED]" if m in dm else ""
            w(f"\n### {m.replace('.', '/')}.lean  ({len(by_file[m])} unreached){tag}")
            for d in sorted(by_file[m], key=lambda d: d.line):
                w(fmt_decl(d))
    elif not a.files_only:
        inmod = [d for d in dead if d.module in dm]
        if inmod:
            cnt = defaultdict(int)
            for d in inmod:
                cnt[d.module] += 1
            w(f"\n===== {CAT_MODULE}s  ({len(inmod)} declarations in {len(cnt)} modules) =====")
            for m in sorted(cnt):
                w(f"  {m.replace('.', '/')}.lean  ({cnt[m]})")
        cats = defaultdict(list)
        for d in dead:
            if d.module not in dm:
                cats[category(d, src, res["by_mod"])].append(d)
        for cat in CAT_ORDER:
            rows = cats.get(cat, [])
            if not rows:
                continue
            w(f"\n===== {cat}  ({len(rows)}) =====")
            shown = sorted(rows, key=lambda d: (d.module, d.line))
            if a.top and len(shown) > a.top:
                for d in shown[:a.top]:
                    w(fmt_decl(d))
                w(f"  ... {len(shown) - a.top} more (drop --top, or run without --triage for the by-file view)")
            else:
                for d in shown:
                    w(fmt_decl(d))
    if not a.files_only:
        nfiles = len({d.module for d in dead})
        kinds = ",".join(sorted(a.want))
        w(f"\n== {total} unreached {kinds} across {nfiles} files "
          f"(of {res['n_modules']} modules scanned; cone of the top theorems: {cone} constants) ==")
        w("   roots: " + ", ".join(r for r, k in roots if k == "top"))
        imp = res["implicit"]
        if imp:
            ni = sum(1 for d in imp if d.reach == 3)
            w(f"   ({ni} declaration(s) live only through an instance no reached term resolved, "
              f"{len(imp) - ni} only through a metaprogram: not listed"
              + ("" if a.all else "; --all lists the instances") + ")")
        if res["allowed"]:
            w(f"   ({len(res['allowed'])} declaration(s) live only through tools/ci/dead_allow.txt: "
              + ", ".join(r for r, k in roots if k == "allow") + ")")
        if res["kept"]:
            w(f"   ({len(res['kept'])} suppressed by a KEEP-UNREFERENCED marker: "
              + ", ".join(sorted(d.name for d in res["kept"])) + ")")
        w("NB: the categories are hints, not verdicts.  A top-level result that is not in "
          "tools/ci/roots.txt yet, and everything only it uses, is reported here as dead.")
    if not a.no_files:
        un = unimported(imports)
        w(f"\n== {len(un)} module file(s) imported by nothing but the umbrella "
          f"(of {len(imports)}) ==")
        w("   Expected here: build LEAVES -- the top theorems' files, demos, smoke files.  "
          "A module that is NOT a deliberate top-level target is a dead-FILE candidate; "
          "`*` marks the ones with no reached declaration.")
        for m in un:
            w(f"  {'*' if m in dm else ' '} {m.replace('.', '/')}.lean")
        w(f"\n== {len(dm)} module(s) with no reached declaration ==")
        for m in sorted(dm):
            w(f"  {m.replace('.', '/')}.lean  ({len(res['by_mod'][m])} declarations)")
    return "\n".join(out)


def render_md(res, imports, roots, cone, a, src):
    dead, dm = res["dead"], set(res["dead_modules"])
    out = ["## Dead-code report (Lean, informational)\n"]
    w = out.append
    nfiles = len({d.module for d in dead})
    w(f"**{len(dead)} declarations** in {nfiles} files are outside the cone of the top theorems "
      f"({cone} constants; {res['n_modules']} modules scanned).  Heuristic triage -- hints, not verdicts:\n")
    cats = defaultdict(list)
    for d in dead:
        cats[CAT_MODULE if d.module in dm else category(d, src, res["by_mod"])].append(d)
    w("| category | declarations | files |")
    w("|---|---|---|")
    for cat in [CAT_MODULE] + CAT_ORDER:
        rows = cats.get(cat, [])
        if rows:
            w(f"| {cat} | {len(rows)} | {len({d.module for d in rows})} |")
    w("")
    imp = res["implicit"]
    ni = sum(1 for d in imp if d.reach == 3)
    w(f"Not listed: {ni} live only through an unresolved instance, {len(imp) - ni} only through a "
      f"metaprogram, {len(res['allowed'])} through `tools/ci/dead_allow.txt`, "
      f"{len(res['kept'])} marked `KEEP-UNREFERENCED`.\n")
    cnt = defaultdict(int)
    for d in dead:
        cnt[d.module] += 1
    top = sorted(cnt.items(), key=lambda kv: -kv[1])[:a.top or 20]
    w("<details><summary>Files with the most unreached declarations</summary>\n")
    w("| file | unreached | of | |")
    w("|---|---|---|---|")
    for m, n in top:
        w(f"| `{m.replace('.', '/')}.lean` | {n} | {len(res['by_mod'][m])} | "
          f"{'wholly unreached' if m in dm else ''} |")
    w("\n</details>\n")
    un = unimported(imports)
    w(f"<details><summary>{len(dm)} modules with no reached declaration; "
      f"{len(un)} imported by nothing but the umbrella</summary>\n")
    w("No reached declaration: " + (", ".join(f"`{m}`" for m in sorted(dm)) or "none") + "\n")
    w("Imported by nothing else (`*` = also no reached declaration): "
      + (", ".join(f"`{m}`{'*' if m in dm else ''}" for m in un) or "none") + "\n")
    w("</details>\n")
    w("The full list is in the step log (`tools/find_dead.py --triage`).")
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--facts", default=None,
                    help="envfacts.tsv from tools/ci/envfacts.sh (default: .lake/ci/envfacts.tsv)")
    ap.add_argument("--all", action="store_true", help="also list instances nothing resolved")
    ap.add_argument("--kinds", default="", help="comma list of kinds (thm,def,opaque,ind,struct,class,inst)")
    ap.add_argument("--triage", action="store_true", help="group by heuristic category, not by file")
    ap.add_argument("--files-only", action="store_true", help="only the whole-file reports")
    ap.add_argument("--no-files", action="store_true", help="skip the whole-file reports")
    ap.add_argument("--format", choices=("text", "md"), default="text")
    ap.add_argument("--top", type=int, default=0, help="cap each triage category at N rows")
    ap.add_argument("--out", help="write the report here as well as to stdout")
    a = ap.parse_args(argv)
    repo = os.path.abspath(a.repo)
    facts = a.facts or os.path.join(repo, ".lake", "ci", "envfacts.tsv")
    if not os.path.exists(facts):
        print(f"find_dead: {facts} does not exist (produce it with tools/ci/envfacts.sh on a built "
              "tree); NOTHING was analysed")
        return 0
    decls, imports, roots, cone = load(facts)
    a.want = set(a.kinds.split(",")) if a.kinds else set(PRIMARY)
    src = Sources(repo)
    if a.all:
        # an instance nothing resolved: reach 3 by construction of the facts
        for d in decls:
            if d.kind == "inst" and d.reach == 3:
                d.reach = 0
        a.want = a.want | {"inst"}
    res = analyze(decls, a.want, src)
    text = (render_md if a.format == "md" else render_text)(res, imports, roots, cone, a, src)
    print(text)
    if a.out:
        with open(a.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())

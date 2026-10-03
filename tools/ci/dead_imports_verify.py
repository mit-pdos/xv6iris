#!/usr/bin/env python3
"""Build-confirm a set of import edits: apply them, build, and back off whatever the
build refutes, until the tree is green.

Usage: tools/ci/dead_imports_verify.py EDITS NEEDS_TSV OUT_DIR [--max-rounds N]

EDITS is `Mod -Imp` / `Mod +Imp` lines (tools/import_shake.py's edits_dead.txt, cut to
the files we edit); NEEDS_TSV is tools/ImportNeeds.lean's output for the tree as it is
on disk, which gives the ORIGINAL import graph (`M` lines) and which module declares
each constant (`D` lines).  Run by tools/ci/dead_imports.sh --apply.

WHY.  The needs analysis sees the elaborated environment, not the source text.  A name
that a file mentions only where it leaves no trace in a term -- a `simp [foo]` argument
that simp did not use, an identifier inside a tactic that fails over to another branch --
is invisible to it, yet still has to resolve: drop the import that provided it and the
file stops compiling ("Unknown identifier").  The same happens downstream, to a module
whose own imports are untouched, when an upstream module stops importing the provider.
Import order can also change which module's derived declarations meet first
("environment already contains").  Rocq's sweep had the same problem and the same cure:
nothing lands that the build has not confirmed.

EACH ROUND restores the original text of every file touched, applies the current edits,
and runs `lake build Xv6 MachCSL` (lake keeps going past a failed module, so one round
sees every independent failure).  Each failing module M is fixed -- or, for a clash,
the module that now re-declares the name (see build()):
  1. M names identifiers declared by modules P of its ORIGINAL import closure that it no
     longer sees, or re-declares what P declared (a clash): undo M's own removal of P if
     it made one, else re-add P to M (once).
  2. else, M has removals of its own: drop them (its re-adds stay).
  3. else: drop every edit to M and to every module of M's original import closure --
     M then sees exactly the environment it was built against before.
Every round removes edits or adds a re-add that is tried at most once, and the edit
set with nothing left is the original (green) tree, so this terminates.  A failure that
step 3 cannot explain (no edit left to drop) means the tree was not green to begin
with: the originals are restored and the exit status is 1.

On success the confirmed edits are applied to the tree and written to
OUT_DIR/edits_verified.txt; the per-round build logs are OUT_DIR/verify-<n>.log.
"""
import argparse, collections, os, re, subprocess, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from apply_import_edits import path_of  # noqa: E402

LOCAL = ("Xv6.", "MachCSL.")


def load_needs(path):
    imports, decl_mod = {}, {}
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "M":
            imports[f[1]] = [x for x in f[2].split(",") if x] if len(f) > 2 else []
        elif f[0] == "D" and len(f) > 2:
            for d in f[2].split():
                decl_mod.setdefault(d, f[1])
    return imports, decl_mod


def closure(imports, m):
    seen, stack = set(), list(imports.get(m, []))
    while stack:
        x = stack.pop()
        if x not in seen:
            seen.add(x)
            stack.extend(imports.get(x, []))
    return seen


def read_edits(path):
    out = []
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            m, op = line.split()
            out.append((m, op[0], op[1:]))
    return out


def write_edits(path, edits):
    with open(path, "w", encoding="utf-8") as f:
        for m, op, imp in edits:
            f.write(f"{m} {op}{imp}\n")


def apply(edits, originals, root, out):
    for p, text in originals.items():
        with open(p, "w", encoding="utf-8") as f:
            f.write(text)
    if edits:
        tmp = os.path.join(out, "edits_round.txt")
        write_edits(tmp, edits)
        subprocess.run([sys.executable, os.path.join(root, "tools/apply_import_edits.py"), tmp, root],
                       check=True, stdout=subprocess.DEVNULL)


ERR = re.compile(r"^error: ((?:Xv6|MachCSL)(?:/\S+?)?\.lean):\d+:\d+: (.*)$")
FAIL = re.compile(r"^✖ \[\d+/\d+\] Building (\S+)")
UNKNOWN = re.compile(r"Unknown (?:identifier|constant) `([^`]+)`")
CLASH = re.compile(r"import (\S+) failed, environment already contains '([^']+)' from (\S+)")


def local(m):
    return m in ("Xv6", "MachCSL") or m.startswith(LOCAL)


def build(root, log, imports, decl_mod):
    """Build; return (status, failed modules, {module to fix: what it must see again}).

    What a target must see again is a set of ("name", identifier) and
    ("module", module) items.  A module whose own text is at fault is its own
    target, with the unknown identifiers it names.  An `environment already
    contains N from A` error on importing B is not the importer's fault: N is
    an auxiliary declaration that A and B (or B's closure) now BOTH add --
    `bv_decide`'s `X.enumToBitVec` is the case in this tree, which is why
    MachCSL/BvEnumSatp.lean exists -- and the tree built before, so originally
    one of them saw the other's and did not add its own.  That one has lost
    the import: when A was in B's original closure, B must see A again; when B
    was in A's, A must see B.  (When the second declarer is deeper in B's
    closure, B's own build fails on the same clash one level down, and the next
    round fixes that.)  Neither: B is the target, with nothing to see."""
    with open(log, "w", encoding="utf-8") as f:
        rc = subprocess.run(["lake", "build", "Xv6", "MachCSL"], cwd=root,
                            stdout=f, stderr=subprocess.STDOUT).returncode
    return (rc,) + parse(log, imports, decl_mod)


def parse(log, imports, decl_mod):
    failed, own = set(), collections.defaultdict(set)
    victims, targets = set(), collections.defaultdict(set)
    for line in open(log, encoding="utf-8", errors="replace"):
        line = line.rstrip("\n")
        m = FAIL.match(line)
        if m and local(m.group(1)):
            failed.add(m.group(1))
        m = ERR.match(line)
        if not m:
            continue
        mod = m.group(1)[:-len(".lean")].replace("/", ".")
        failed.add(mod)
        c = CLASH.search(m.group(2))
        if c:
            victims.add(mod)
            b, n, a = c.groups()
            if a in closure(imports, b):
                targets[b].add(("module", a))
            elif b in closure(imports, a):
                targets[a].add(("module", b))
            else:
                targets[b]   # a target, with nothing to see again
            continue
        own[mod].update(("name", u) for u in UNKNOWN.findall(m.group(2)))
    for mod in failed:
        if mod in own or mod not in victims:
            targets[mod].update(own.get(mod, ()))
    return failed, {t: ns for t, ns in targets.items() if local(t)}


def provider(name, decl_mod, cands):
    """The module declaring `name` (as written: possibly unqualified, or qualified
    relative to an open namespace), among the modules cands."""
    if name in decl_mod and decl_mod[name] in cands:
        return decl_mod[name]
    suffix = "." + name
    hits = {mod for d, mod in decl_mod.items() if d.endswith(suffix) and mod in cands}
    return hits.pop() if len(hits) == 1 else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("edits")
    ap.add_argument("needs")
    ap.add_argument("out")
    ap.add_argument("--root", default=".")
    ap.add_argument("--max-rounds", type=int, default=20)
    a = ap.parse_args()
    root = a.root
    imports, decl_mod = load_needs(a.needs)
    edits = read_edits(a.edits)
    proposed = set(edits)
    originals = {}
    for m, _, _ in edits:
        p = path_of(root, m)
        if p not in originals:
            originals[p] = open(p, encoding="utf-8").read()
    readded = set()   # modules given a step-2 re-add already
    dropped = collections.Counter()

    for rnd in range(1, a.max_rounds + 1):
        apply(edits, originals, root, a.out)
        log = os.path.join(a.out, f"verify-{rnd}.log")
        rc, failed, targets = build(root, log, imports, decl_mod)
        if rc == 0 and not failed:
            write_edits(os.path.join(a.out, "edits_verified.txt"), edits)
            rm = sum(op == "-" for _, op, _ in edits)
            add = sum(op == "+" for _, op, _ in edits)
            files = len({m for m, _, _ in edits})
            print(f"dead-imports: verified in {rnd} build(s): {rm} removal(s) and {add} re-add(s) "
                  f"across {files} file(s); {len(proposed - set(edits))} of the {len(proposed)} "
                  f"proposed edits were refuted by the build, {len(set(edits) - proposed)} re-add(s) "
                  f"were added for it")
            for k, n in sorted(dropped.items()):
                print(f"dead-imports:   {k}: {n}")
            return 0
        print(f"dead-imports: round {rnd}: {len(failed)} module(s) fail to build: "
              + " ".join(sorted(failed)[:12]) + (" ..." if len(failed) > 12 else ""))
        before = list(edits)
        for m in sorted(targets):
            own_rm = [e for e in edits if e[0] == m and e[1] == "-"]
            cl = closure(imports, m)
            cur = (set(imports.get(m, [])) - {i for x, op, i in own_rm}) \
                | {i for x, op, i in edits if x == m and op == "+"}
            provs = {provider(x, decl_mod, cl) if kind == "name" else x if x in cl else None
                     for kind, x in targets[m]}
            provs.discard(None)
            provs -= cur
            generated = open(path_of(root, m), encoding="utf-8").readline().startswith("-- AUTO-GENERATED")
            # 1. The names it is missing come back: by undoing its own removal of
            #    their declarer if it made one, else (once) by importing the declarer.
            undo = [e for e in own_rm if e[2] in provs]
            if undo:
                edits = [e for e in edits if e not in undo]
                dropped["removals undone (a name the file sees)"] += len(undo)
                continue
            if provs and m not in readded and not generated:
                readded.add(m)
                for p in sorted(provs):
                    edits.append((m, "+", p))
                # m had no edits before, or its file would be there already: on disk is the original
                originals.setdefault(path_of(root, m), open(path_of(root, m), encoding="utf-8").read())
                dropped["re-adds (a name the file sees)"] += len(provs)
                continue
            # 2. Its own removals go.
            if own_rm:
                edits = [e for e in edits if e not in own_rm]
                dropped["removals undone (the file fails)"] += len(own_rm)
                continue
            # 3. Everything it sees is put back as it was.
            scope = cl | {m}
            n = len(edits)
            edits = [e for e in edits if e[0] not in scope]
            dropped["edits undone (a closure reverted)"] += n - len(edits)
        if edits == before:
            apply([], originals, root, a.out)
            print(f"dead-imports: the build fails with no edit left to blame (see {log}); "
                  "the tree is restored", file=sys.stderr)
            return 1
    apply([], originals, root, a.out)
    print(f"dead-imports: no green edit set after {a.max_rounds} rounds; the tree is restored",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())

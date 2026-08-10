#!/usr/bin/env python3
"""Report declarations that VANISHED from a file relative to a git ref.

The characteristic silent failure of an interface sweep is not a broken
proof -- that shows up as a red build.  It is a file that compiles because
something was quietly dropped: a lemma deleted instead of restated, a
`Module Type` seal that lost a `Parameter`, a proof closed with `Admitted`.
None of those fail a build, and all of them change what the tree claims to
have proved.

Usage:
    tools/lemma_diff.py [--ref REF] [--dir DIR] [FILE ...]

With no FILEs, checks every tracked *.v under DIR (default iris/) that
differs from REF (default HEAD).  Exit status is 1 if anything is reported,
so it can gate a commit.

What it reports, per file:
  GONE      a top-level declaration present at REF and absent now
  ADMITTED  a proof closed with Admitted / admit / Abort
  NEWAXIOM  an Axiom / Parameter / Hypothesis not present at REF

Renaming a lemma deliberately shows up as one GONE plus (usually) nothing
else, so read the report rather than treating it as a pass/fail oracle --
it is a prompt to justify each line, which is the point.
"""

import argparse
import os
import re
import subprocess
import sys

# Top-level (column 0) declarations only: a `Local Lemma` inside a section is
# still reachable by qualified name, so it counts, but an indented `assert`
# or a tactic-level name does not.
DECL = re.compile(
    # \s* : declarations inside a Section are indented, and a column-0
    # anchor made the tool blind to ALL of them -- a false green on
    # exactly the sweeps it exists to guard (found 2026-08-10, when it
    # reported CLEAN across two deleted Section-local lemmas).
    r"^\s*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*"
    r"(Lemma|Theorem|Corollary|Remark|Fact|Proposition|Definition|Fixpoint"
    r"|CoFixpoint|Inductive|Record|Class|Instance|Axiom|Parameter|Hypothesis"
    r"|Module Type|Module|Notation|Ltac)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)

ADMIT = re.compile(r"^\s*(Admitted|Abort)\s*\.|(?<![A-Za-z_])admit\s*\.", re.MULTILINE)

ASSUMED = {"Axiom", "Parameter", "Hypothesis"}


def decls(text):
    """Map name -> keyword for every top-level declaration."""
    out = {}
    for kw, name in DECL.findall(text):
        out.setdefault(name, kw)
    return out


def at_ref(ref, path):
    try:
        return subprocess.run(
            ["git", "show", f"{ref}:{path}"],
            capture_output=True, text=True, check=True,
        ).stdout
    except subprocess.CalledProcessError:
        return None  # new file at this ref


def changed_files(ref, directory):
    out = subprocess.run(
        ["git", "diff", "--name-only", ref, "--", directory],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    # UNTRACKED files are invisible to `git diff --name-only <ref>` -- and a
    # brand-new file is exactly where a new Axiom hides (found 2026-08-10:
    # a bridging Axiom in a new Link file was not counted; the tool said
    # "2 things to justify" when the honest count was 3).  Union them in.
    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", directory],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    return sorted(set(p for p in out + untracked if p.endswith(".v")))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--dir", default="iris")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()

    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    os.chdir(root)

    paths = args.files or changed_files(args.ref, args.dir)
    if not paths:
        print(f"no *.v differs from {args.ref} under {args.dir}/")
        return 0

    findings = 0
    for path in sorted(paths):
        if not os.path.exists(path):
            print(f"{path}: DELETED outright")
            findings += 1
            continue
        new = open(path).read()
        old = at_ref(args.ref, path)
        lines = []

        # A NEW file (old is None) must still be scanned: every assumed-kind
        # declaration in it is a NEW assumption.  Skipping it hid a bridging
        # Axiom in a brand-new Link file (2026-08-10, the same audit that
        # found the untracked-file gap above).
        before = decls(old) if old is not None else {}
        after = decls(new)
        for name, kw in before.items():
            if name not in after:
                lines.append(f"  GONE      {kw} {name}")
        for name, kw in after.items():
            if kw in ASSUMED and name not in before:
                lines.append(f"  NEWAXIOM  {kw} {name}")

        for m in ADMIT.finditer(new):
            ln = new.count("\n", 0, m.start()) + 1
            lines.append(f"  ADMITTED  line {ln}: {m.group(0).strip()}")

        if lines:
            print(f"{path}")
            for line in lines:
                print(line)
            findings += len(lines)

    print()
    if findings:
        print(f"{len(paths)} file(s) checked -- {findings} thing(s) to justify")
        return 1
    print(f"{len(paths)} file(s) checked -- CLEAN "
          f"(nothing dropped, nothing admitted, no new assumption)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

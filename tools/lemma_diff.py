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
  GONE      a declaration present at REF and absent now
  ADMITTED  a proof closed with Admitted / admit / Abort
  NEWAXIOM  an Axiom / Parameter / Hypothesis not present at REF

"Declaration" means one the file still CLAIMS after it is compiled, wherever
it sits in the file's Section / Module nesting -- in this tree almost every
lemma is indented two spaces inside a `Section ... End`, and the sealing
`Parameter`s of a `Module Type` are indented too, so column 0 alone sees
almost nothing.  What is deliberately NOT a declaration: anything inside a
comment, anything between `Proof.` and its `Qed.` (a proof script's own
names die with the proof), and `Let` (discharged at `End`, never nameable
from outside).

Renaming a lemma deliberately shows up as one GONE plus (usually) nothing
else, so read the report rather than treating it as a pass/fail oracle --
it is a prompt to justify each line, which is the point.
"""

import argparse
import os
import re
import subprocess
import sys

# Leading whitespace is allowed because a `Lemma` inside a `Section` is still
# reachable by qualified name, so it counts -- and in this tree that is where
# essentially every lemma lives.  Indentation therefore cannot be the filter
# that keeps out tactic-level names; two structural filters do that instead
# (see `strip_comments` and `strip_proofs`), because after them the only
# things left starting a line with one of these keywords ARE declarations.
# `Let` is excluded on purpose: a section's `Let` is discharged at `End` and
# never becomes a name, so losing one is not losing a claim.  `Notation`
# matches only the abbreviation form (`Notation name := ...`); the string
# form has no identifier to track.
DECL = re.compile(
    r"^[ \t]*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*"
    r"(Lemma|Theorem|Corollary|Remark|Fact|Proposition|Example"
    r"|Definition|Fixpoint"
    r"|CoFixpoint|Inductive|Record|Class|Instance|Axiom|Parameter|Hypothesis"
    r"|Module Type|Module|Notation|Ltac)\s+"
    # The tail is Unicode-aware because Iris names end in Σ: truncating
    # `bioΣ` to `bio` merges it with any sibling `bio`, and a merged key is a
    # deletion this tool cannot see.  The head stays ASCII, so widening the
    # tail cannot start a match that did not already start.
    r"([A-Za-z_][\w']*)",
    re.MULTILINE,
)

# Fed comment-stripped but NOT proof-stripped text: the `Admitted.` this is
# hunting for is precisely a proof terminator, while the design notes discuss
# `admit` in prose constantly.  Blanking preserves offsets, so the reported
# line number is still the line number in the real file.
ADMIT = re.compile(r"^\s*(Admitted|Abort)\s*\.|(?<![A-Za-z_])admit\s*\.", re.MULTILINE)

# A proof script, blanked whole.  The names it binds (`assert (H : ...)`,
# `set (x := ...)`, a nested `Definition` in a `Local Ltac`) are gone by the
# `Qed.`, so a diff in them is a proof rewrite, not a lost claim.  `Next
# Obligation` opens a body that need not repeat `Proof.`.  Non-greedy, so an
# unterminated `Proof` can only swallow up to the next terminator; that is
# the failure mode to prefer, since the alternative is scanning tactic text.
PROOF = re.compile(
    # NOT [Set Default Proof Using "Type".] -- that is a command, not a proof
    # opener, and treating it as one blanks the whole file up to the first
    # [Qed], which HIDES every deletion in between (a false NEGATIVE, the
    # dangerous direction).  Found stage C8, when a restructuring moved the
    # first [Qed] 100 lines down and the tool started reporting a lemma that
    # is still there.
    r"(?<![\w'])(?<!Default )(?:Proof|Next\s+Obligation)(?![\w'])"
    r".*?(?<![\w'])(?:Qed|Defined|Admitted|Abort|Save)(?![\w'])\s*\.",
    re.DOTALL,
)

ASSUMED = {"Axiom", "Parameter", "Hypothesis"}


def blank(text, start, end):
    """Overwrite text[start:end] with spaces, keeping newlines.

    Offsets and line numbers survive, so a stripped copy can still be used to
    report a line number in the original.
    """
    return text[:start] + re.sub(r"[^\n]", " ", text[start:end]) + text[end:]


def strip_comments(text):
    """Blank every (* ... *), which nests and may contain string literals.

    Prose is the dominant source of line-initial keywords in this tree: the
    header comments are indented and full of sentences like "Definition of
    the escrow", which would otherwise each register as a declaration named
    `of`.  String literals outside comments are left alone (a `Notation`
    needs them) but are skipped over, so a `(*` inside one opens nothing.
    """
    out, i, n, depth = list(text), 0, len(text), 0
    while i < n:
        if text[i] == '"':
            j = i + 1
            while j < n:                      # "" is an escaped quote
                if text[j] == '"' and not (j + 1 < n and text[j + 1] == '"'):
                    j += 1
                    break
                j += 2 if text[j] == '"' else 1
            if depth:
                for k in range(i, j):
                    if text[k] != "\n":
                        out[k] = " "
            i = j
        elif text.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        else:
            if depth and text[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def strip_proofs(text):
    """Blank every `Proof. ... Qed.`  Run this AFTER `strip_comments`."""
    for m in reversed(list(PROOF.finditer(text))):
        text = blank(text, m.start(), m.end())
    return text


def decls(text):
    """Map name -> keyword for every declaration the file still claims.

    Takes comment-stripped text (see `read`).
    """
    out = {}
    for kw, name in DECL.findall(strip_proofs(text)):
        out.setdefault(name, kw)
    return out


def read(path):
    return strip_comments(open(path).read())


def at_ref(ref, path):
    try:
        return strip_comments(subprocess.run(
            ["git", "show", f"{ref}:{path}"],
            capture_output=True, text=True, check=True,
        ).stdout)
    except subprocess.CalledProcessError:
        return None  # new file at this ref


def changed_files(ref, directory):
    out = subprocess.run(
        ["git", "diff", "--name-only", ref, "--", directory],
        capture_output=True, text=True, check=True,
    ).stdout.split()
    return [p for p in out if p.endswith(".v")]


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
        new = read(path)
        old = at_ref(args.ref, path)
        lines = []

        if old is not None:
            before, after = decls(old), decls(new)
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

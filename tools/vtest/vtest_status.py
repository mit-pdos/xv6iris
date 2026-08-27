#!/usr/bin/env python3
"""Which device-conformance tests (``vtest-rocq/``) passed, and which are known red.

This is the reporter half of the CI step; the build is the other half.  CI
compiles EVERY test in ``vtest-rocq/_CoqProject`` with ``make -k`` -- so one red
test does not hide the rest -- and then runs this, which decides what the
result means and prints the table.

WHY THE VERDICT IS NOT SIMPLY "make exited 0".  A red conformance test is a
FINDING about the model, not a broken build (see ``tools/vtest/README.md``), and
some of the findings are open by decision rather than by neglect.  So the
expected outcome of the suite is recorded in ``vtest-rocq/expected-pass.txt``
and this script compares against it:

  * a bare name there is EXPECTED TO PASS -- its failure is a REGRESSION and
    fails the build;
  * ``!Name  reason`` is KNOWN RED -- still compiled, still reported, with the
    reason next to it, but its failure is not fatal;
  * a known-red test that PASSES is reported as such, loudly, since the list
    is then stale -- but it does not fail the build either.

Every test must appear in the manifest, exactly once.  A test in
``_CoqProject`` that the manifest does not mention is an error rather than a
silent default: a new test would otherwise arrive as "expected to pass" (a
surprise regression the day it lands red) or as "known red" (uncovered
forever), and which one it should be is the author's call.

WHAT COUNTS AS A PASS is the presence of ``<Name>.vo``.  A test is a
``vm_cast_no_check``d equation between the model's reached state and the
capture, so compiling the file IS running the test -- there is nothing to
check afterwards.

THAT CRITERION IS ONLY SOUND ON A TREE WHOSE ``.vo`` THIS RUN PRODUCED, which
is why ``make vtest-check-ci`` deletes them before building.  A failed
recompile does NOT remove the previous ``.vo``: coq_makefile's
``.DELETE_ON_ERROR`` takes out the ``.glob`` coqc had started writing and
leaves a ``.vo`` the run never touched (verified -- a deliberately broken
``PlicTie.v`` was reported green off the previous run's output), and a
self-hosted runner keeps the gitignored artifacts between runs.  ``--log``
therefore does double duty: it supplies each failure's error text, and a
target the log says failed is counted as failed whatever is on disk.  Pass it.

WHICH FILES ARE TESTS is derived, not listed: the generator writes
``<Name>Gen.v`` beside every ``<Name>.v``, so a test is a module whose
``Gen`` sibling the project file also lists.  The rest (``VTest``, ``VSched``,
``VBoot``, ``VConc``, ``VNode``) is the harness, and if any of it failed then
no test ran at all -- reported as such rather than as 56 failures.

Usage:
  vtest_status.py [--repo R] [--log make.log] [--md] [--out FILE]
"""
import argparse
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# The areas of tools/vtest/README.md's naming scheme, in reporting order.  A
# test's area is the first CamelCase component of its module name, lowercased
# (`DiskIdentQnum` -> disk), which is that scheme read backwards.
AREAS = ["core", "disk", "uart", "plic", "conc", "pt"]


def coqproject_modules(path):
    """The module names vtest-rocq/_CoqProject lists, in order."""
    mods = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or line.startswith("-"):
                continue
            if line.endswith(".v"):
                mods.append(line[:-2])
    return mods


def split_tests(modules):
    """(tests, harness): a test is a module with a generated `Gen` sibling."""
    listed = set(modules)
    tests = [m for m in modules if m + "Gen" in listed]
    known = set(tests) | {t + "Gen" for t in tests}
    return tests, [m for m in modules if m not in known]


def read_manifest(path):
    """(expected_pass, known_red, problems) from expected-pass.txt.

    `known_red` maps the test name to its reason; a row with no reason is
    accepted but flagged, since an unexplained exclusion is the thing this
    file exists to prevent.
    """
    expected, red, problems = [], {}, []
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            if line.startswith("!"):
                parts = line[1:].split(None, 1)
                name, reason = parts[0], parts[1].strip() if len(parts) > 1 else ""
                if not reason:
                    problems.append(f"expected-pass.txt:{lineno}: `!{name}` gives "
                                    f"no reason for being known red")
                red[name] = reason or "_no reason given_"
            elif re.fullmatch(r"[A-Za-z0-9_]+", line):
                expected.append(line)
            else:
                problems.append(f"expected-pass.txt:{lineno}: not a name, a "
                                f"`!name reason` row, or a comment: {line!r}")
    return expected, red, problems


def build_errors(log_path):
    """module -> the first error Rocq or make reported for it."""
    errs = {}
    if not log_path or not os.path.exists(log_path):
        return errs
    with open(log_path, errors="replace") as f:
        lines = f.read().splitlines()
    # Rocq: `File "./Foo.v", line 12, characters 0-9:` then `Error: ...`.
    for i, line in enumerate(lines):
        m = re.match(r'File "\./([A-Za-z0-9_]+)\.v", line (\d+)', line)
        if not m:
            continue
        mod, at = m.group(1), m.group(2)
        for nxt in lines[i + 1:i + 4]:
            if nxt.startswith("Error:"):
                errs.setdefault(mod, f"line {at}: {nxt[len('Error:'):].strip()}")
                break
    # make, for a target that died without Rocq saying why (a killed worker).
    for line in lines:
        m = re.search(r"\*\*\* \[[^]]*: ([A-Za-z0-9_]+)\.vo\] Error", line)
        if m:
            errs.setdefault(m.group(1), "the compile failed with no Rocq error "
                                        "(killed? out of memory?)")
    return errs


def area_of(name):
    m = re.match(r"[A-Z][a-z0-9]*", name)
    a = m.group(0).lower() if m else ""
    return a if a in AREAS else "other"


def truncate(text, width=110):
    text = " ".join(text.split())
    return text if len(text) <= width else text[:width - 1] + "…"


def render(tests, expected, red, failed, errs, harness_missing, problems, md):
    """The report.  `md` picks GitHub-flavoured markdown over plain text."""
    out = []
    h1, h2, code = ("## ", "### ", "`") if md else ("== ", "-- ", "")

    regressions = [t for t in tests if t in failed and t in expected]
    red_failing = [t for t in tests if t in failed and t in red]
    red_passing = [t for t in tests if t not in failed and t in red]

    out.append(f"{h1}Device conformance ({code}vtest-rocq/{code})")
    out.append("")
    out.append(f"{len(tests)} test programs, each checked against the QEMU capture "
               f"checked in beside it ({code}*Gen.v{code}) -- **no QEMU is run "
               f"here**, so this is a regression test of the model against "
               f"executions already recorded from real hardware.  A test passes "
               f"by COMPILING: it is an equation between the model's reached "
               f"state and the capture.")
    out.append("")

    if harness_missing:
        out.append(f"> :x: **The harness did not build** "
                   f"({', '.join(harness_missing)}), so NO test ran.  The table "
                   f"below is not a result about the model.")
        out.append("")

    passed = len(tests) - len(failed)
    verdict = (f"**{passed} of {len(tests)} pass.**  "
               f"{len(red_failing)} known red, {len(regressions)} REGRESSED")
    if red_passing:
        verdict += f", {len(red_passing)} unexpectedly green"
    out.append(verdict + ".")
    out.append("")

    # Per-area counts.  The area is what the test is ABOUT (README's scheme).
    out.append("| area | pass | known red | regressed |")
    out.append("|---|---|---|---|")
    for a in AREAS + (["other"] if any(area_of(t) == "other" for t in tests) else []):
        ts = [t for t in tests if area_of(t) == a]
        if not ts:
            continue
        out.append(f"| `{a}` | {sum(1 for t in ts if t not in failed)}/{len(ts)} | "
                   f"{sum(1 for t in ts if t in red_failing)} | "
                   f"{sum(1 for t in ts if t in regressions)} |")
    out.append(f"| **total** | **{passed}/{len(tests)}** | **{len(red_failing)}** | "
               f"**{len(regressions)}** |")
    out.append("")

    if regressions and harness_missing:
        # Naming all 56 here would be noise: they failed because the harness
        # did, and none of them says anything about the model.
        out.append(f"{h2}:x: {len(regressions)} tests counted as failed")
        out.append("")
        out.append("Every one of them is downstream of the harness above; fix "
                   "that and re-read this report.")
        out.append("")
    elif regressions:
        out.append(f"{h2}:x: REGRESSIONS -- expected to pass, did not")
        out.append("")
        out.append("These fail the build.  Either the model changed under the "
                   "test, or the capture did.")
        out.append("")
        out.append("| test | what the build said |")
        out.append("|---|---|")
        for t in regressions:
            out.append(f"| `{t}` | {truncate(errs.get(t, 'no error in the build log'))} |")
        out.append("")

    if red_failing:
        out.append(f"{h2}Known red -- reported, not fatal")
        out.append("")
        out.append(f"Listed in {code}vtest-rocq/expected-pass.txt{code}; the "
                   f"findings table in {code}tools/vtest/README.md{code} is the "
                   f"authority on each.")
        out.append("")
        out.append("| test | why it is expected to fail | what the build said |")
        out.append("|---|---|---|")
        for t in red_failing:
            out.append(f"| `{t}` | {red[t]} | "
                       f"{truncate(errs.get(t, 'no error in the build log'), 70)} |")
        out.append("")

    if red_passing:
        out.append(f"{h2}:warning: Unexpectedly green")
        out.append("")
        out.append(f"These are listed as known red and PASSED.  Drop the "
                   f"{code}!{code} from their rows in "
                   f"{code}vtest-rocq/expected-pass.txt{code} so a future "
                   f"regression is caught: " +
                   ", ".join(f"`{t}`" for t in red_passing) + ".")
        out.append("")

    # Manifest problems -- an unmentioned test included, which main() has
    # already turned into a `problems` row (and a nonzero exit).
    if problems:
        out.append(f"{h2}:x: The manifest and the project file disagree")
        out.append("")
        for p in problems:
            out.append(f"* {p}")
        out.append("")

    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO, help="repository root")
    ap.add_argument("--log", help="the `make -k` build log, for the error text")
    ap.add_argument("--md", action="store_true", help="GitHub-flavoured markdown")
    ap.add_argument("--out", help="write here instead of stdout")
    args = ap.parse_args()

    vtest = os.path.join(args.repo, "vtest-rocq")
    modules = coqproject_modules(os.path.join(vtest, "_CoqProject"))
    tests, harness = split_tests(modules)
    expected, red, problems = read_manifest(os.path.join(vtest, "expected-pass.txt"))

    stray = [n for n in list(expected) + list(red) if n not in tests]
    for n in stray:
        problems.append(f"expected-pass.txt names `{n}`, which is not a test in "
                        f"vtest-rocq/_CoqProject")
    for n in [n for n in expected if n in red]:
        problems.append(f"expected-pass.txt lists `{n}` both ways")
    # A test the manifest does not mention is an error, not a default -- see
    # the header.  Counted here rather than only rendered, so it fails the run.
    for t in tests:
        if t not in expected and t not in red:
            problems.append(f"`{t}` is a test in vtest-rocq/_CoqProject that "
                            f"expected-pass.txt does not mention -- add it as a "
                            f"bare name (expected to pass) or as "
                            f"`!{t}  <reason>`")

    errs = build_errors(args.log)

    def did_not_build(name):
        # Either half is enough: no .vo means it did not build, and an error in
        # the log means it did not build in THIS run even if a stale .vo is
        # sitting there (see the header).
        return (not os.path.exists(os.path.join(vtest, name + ".vo"))
                or name in errs)

    failed = {t for t in tests if did_not_build(t)}
    harness_missing = [h for h in harness if did_not_build(h)]

    report = render(tests, expected, red, failed, errs, harness_missing,
                    problems, args.md)
    if args.out:
        with open(args.out, "w") as f:
            f.write(report)
    else:
        sys.stdout.write(report)

    regressions = sorted(failed & set(expected))
    rc = 0
    if harness_missing:
        print(f"vtest harness did not build: {', '.join(harness_missing)}",
              file=sys.stderr)
        rc = 1
    if regressions:
        print(f"{len(regressions)} conformance test(s) expected to pass FAILED: "
              f"{', '.join(regressions)}", file=sys.stderr)
        rc = 1
    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        rc = 1
    if rc == 0:
        print(f"{len(tests) - len(failed)}/{len(tests)} conformance tests pass; "
              f"{len(failed)} known red.", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())

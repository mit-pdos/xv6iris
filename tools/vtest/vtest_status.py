#!/usr/bin/env python3
"""Which device-conformance tests (``vtest-rocq/``) passed, as a report.

This is the reporter half of the CI step; the build is the other half.  CI
compiles EVERY test in ``vtest-rocq/_CoqProject`` with ``make -k`` -- so one red
test does not hide the rest -- and then runs this, which turns the result into
a per-area table naming each failure and its error, and exits nonzero if any
test failed.

WHY A REPORTER AT ALL, when `make` already returns nonzero.  Two things it
cannot do: with ``-k`` the failures are scattered through a 1900-line log, and
GitHub's step summary is where a reader looks.  Every test failing is a
failure, so there is no policy here -- no list of expected reds.  There is
none to keep: the suite's convention (``tools/vtest/README.md``, "Recording a
divergence") is that a KNOWN divergence is pinned on BOTH sides -- the model's
wrong value, the hardware's value, and a ``<>`` between them -- which is green
today and goes red the day the model moves.  So the eleven open findings are
theorems about the disagreement rather than red tests, and a red test here is
always news.

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


def render(tests, failed, errs, harness_missing, md):
    """The report.  `md` picks GitHub-flavoured markdown over plain text."""
    out = []
    h1, h2, code = ("## ", "### ", "`") if md else ("== ", "-- ", "")
    fails = [t for t in tests if t in failed]

    out.append(f"{h1}Device conformance ({code}vtest-rocq/{code})")
    out.append("")
    out.append(f"{len(tests)} test programs, each checked against the QEMU capture "
               f"checked in beside it ({code}*Gen.v{code}) -- **no QEMU is run "
               f"here**, so this is a regression test of the model against "
               f"executions already recorded from real hardware.  A test passes "
               f"by COMPILING: it is an equation between the model's reached "
               f"state and the capture.  A KNOWN divergence is not a red test -- "
               f"it is pinned on both sides and proved unequal, so it goes red "
               f"only when the model moves.")
    out.append("")

    if harness_missing:
        out.append(f"> :x: **The harness did not build** "
                   f"({', '.join(harness_missing)}), so NO test ran.  The table "
                   f"below is not a result about the model.")
        out.append("")

    out.append(f"**{len(tests) - len(fails)} of {len(tests)} pass.**"
               + (f"  {len(fails)} FAILED." if fails else ""))
    out.append("")

    # Per-area counts.  The area is what the test is ABOUT (README's scheme).
    out.append("| area | pass | failed |")
    out.append("|---|---|---|")
    for a in AREAS + (["other"] if any(area_of(t) == "other" for t in tests) else []):
        ts = [t for t in tests if area_of(t) == a]
        if not ts:
            continue
        out.append(f"| `{a}` | {sum(1 for t in ts if t not in failed)}/{len(ts)} | "
                   f"{sum(1 for t in ts if t in failed)} |")
    out.append(f"| **total** | **{len(tests) - len(fails)}/{len(tests)}** | "
               f"**{len(fails)}** |")
    out.append("")

    if fails and harness_missing:
        # Naming all 56 here would be noise: they failed because the harness
        # did, and none of them says anything about the model.
        out.append(f"{h2}:x: {len(fails)} tests counted as failed")
        out.append("")
        out.append("Every one of them is downstream of the harness above; fix "
                   "that and re-read this report.")
        out.append("")
    elif fails:
        out.append(f"{h2}:x: Failed")
        out.append("")
        out.append("Either the model changed under the test, or the capture "
                   "did.  A divergence from the hardware is recorded by pinning "
                   "both values (see the findings table in "
                   f"{code}tools/vtest/README.md{code}), never by leaving a "
                   "test red.")
        out.append("")
        out.append("| test | what the build said |")
        out.append("|---|---|")
        for t in fails:
            out.append(f"| `{t}` | {truncate(errs.get(t, 'no error in the build log'))} |")
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
    errs = build_errors(args.log)

    def did_not_build(name):
        # Either half is enough: no .vo means it did not build, and an error in
        # the log means it did not build in THIS run even if a stale .vo is
        # sitting there (see the header).
        return (not os.path.exists(os.path.join(vtest, name + ".vo"))
                or name in errs)

    failed = {t for t in tests if did_not_build(t)}
    harness_missing = [h for h in harness if did_not_build(h)]

    report = render(tests, failed, errs, harness_missing, args.md)
    if args.out:
        with open(args.out, "w") as f:
            f.write(report)
    else:
        sys.stdout.write(report)

    if harness_missing:
        print(f"vtest harness did not build: {', '.join(harness_missing)}",
              file=sys.stderr)
        return 1
    if failed:
        print(f"{len(failed)} conformance test(s) FAILED: "
              f"{', '.join(sorted(failed))}", file=sys.stderr)
        return 1
    print(f"all {len(tests)} conformance tests pass.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

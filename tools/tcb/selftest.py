#!/usr/bin/env python3
"""tools/tcb/selftest.py -- THE TRUSTED-BASE CHECK MUST FAIL ON A DOCTORED BASELINE.

Run by `tools/ci/tcb.sh --self-test` (CI step `tcb`, after the real check).  It
copies tools/tcb/expected.json, doctors the copy in three ways -- one constant's
content hash altered, one constant removed, one bogus constant added under an
existing declaration -- runs the native tool (tools/tcb/Tcb.lean) against the copy
through `XV6_TCB_EXPECTED`, in its own output directory `$XV6_CI_OUT/tcb-selftest/`
so the real tcb.json / tcb.md survive, and requires: exit status 1, and the
problems in its tcb.json to be EXACTLY the three expected ones (the altered
constant CHANGED, the removed one ENTERED the trusted base, the bogus one LEFT
it), with no module / axiom / opaque problem.  So a tool that stopped comparing
content, or compared it wrongly, fails the step even while the real check passes.

Exit status: 0 when the check failed as it must; 1 otherwise (the reasons are
printed); 2 on a usage or setup error.  The pure parts (`doctor`, `judge`) are
unit-tested by tools/tests/test_tcb_selftest.py, without Lean.

    python3 tools/tcb/selftest.py [--baseline PATH] [--exe PATH]
"""
import argparse
import copy
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASELINE = ROOT / "tools" / "tcb" / "expected.json"
EXE = ROOT / "tools" / "tcb" / ".lake" / "build" / "bin" / "tcb"
BOGUS_SUFFIX = ".selftestBogusConstant"
SET_MARK = "the statement's trusted base"   # the module / axiom / opaque problems say this


def flip_hex(h):
    """A different 16-digit hash: the last digit changed."""
    last = "1" if h[-1] == "0" else "0"
    return h[:-1] + last


def doctor(baseline):
    """Return (doctored copy, expectation).  Deterministic: the declarations are taken in
    name order; the first loses the hash of its first constant to `flip_hex`, the second
    loses its first constant, the third gains a bogus one.  The expectation names the
    constant the tool must report under each verdict."""
    b = copy.deepcopy(baseline)
    decls = b.get("declarations")
    if not isinstance(decls, dict) or len(decls) < 3:
        raise ValueError("the baseline needs a `declarations` map with at least 3 declarations")
    units = sorted(decls)
    changed_unit, removed_unit, bogus_unit = units[0], units[1], units[2]
    changed_const = sorted(decls[changed_unit])[0]
    decls[changed_unit][changed_const] = flip_hex(decls[changed_unit][changed_const])
    removed_const = sorted(decls[removed_unit])[0]
    del decls[removed_unit][removed_const]
    if not decls[removed_unit]:
        del decls[removed_unit]
    bogus_const = bogus_unit + BOGUS_SUFFIX
    decls[bogus_unit][bogus_const] = "0123456789abcdef"
    return b, {"changed": changed_const, "entered": removed_const, "left": bogus_const}


def patterns(expect):
    """What each of the three problems must contain (the tool's message forms)."""
    return {
        "changed": "the content of `%s` CHANGED" % expect["changed"],
        "entered": "`%s` ENTERED the trusted base" % expect["entered"],
        "left": "`%s` LEFT the trusted base" % expect["left"],
    }


def judge(problems, expect):
    """The reasons the problem list is NOT exactly the three expected ones (empty = pass)."""
    reasons = []
    if len(problems) != 3:
        reasons.append("expected exactly 3 problems, got %d" % len(problems))
    for verdict, pat in patterns(expect).items():
        hits = [p for p in problems if pat in p]
        if len(hits) != 1:
            reasons.append("expected one problem containing %r (%s), got %d" % (pat, verdict, len(hits)))
    for p in problems:
        if SET_MARK in p:
            reasons.append("a module/axiom/opaque problem appeared: %s" % p)
    return reasons


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--baseline", type=Path, default=BASELINE)
    ap.add_argument("--exe", type=Path, default=EXE)
    args = ap.parse_args(argv)
    out = Path(os.environ.get("XV6_CI_OUT", ".lake/ci"))
    if not out.is_absolute():
        out = ROOT / out
    selfdir = out / "tcb-selftest"
    selfdir.mkdir(parents=True, exist_ok=True)
    try:
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f)
        doctored, expect = doctor(baseline)
    except (OSError, ValueError) as e:
        print("tcb self-test: cannot doctor %s: %s" % (args.baseline, e))
        return 2
    if not args.exe.is_file():
        print("tcb self-test: no tool at %s (tools/ci/tcb.sh builds it)" % args.exe)
        return 2
    doctored_path = selfdir / "expected.json"
    with open(doctored_path, "w", encoding="utf-8") as f:
        json.dump(doctored, f, indent=1)
        f.write("\n")
    env = dict(os.environ, XV6_TCB_EXPECTED=str(doctored_path), XV6_CI_OUT=str(selfdir))
    env.pop("XV6_TCB_UPDATE", None)
    r = subprocess.run(["lake", "env", str(args.exe)], cwd=ROOT, env=env, capture_output=True, text=True)
    with open(selfdir / "tcb-run.log", "w", encoding="utf-8") as f:
        f.write(r.stdout)
        f.write(r.stderr)
    reasons = []
    if r.returncode != 1:
        reasons.append("expected exit status 1 from the doctored run, got %d" % r.returncode)
    try:
        with open(selfdir / "tcb.json", encoding="utf-8") as f:
            report = json.load(f)
        problems = report.get("problems", [])
        if report.get("ok") is not False:
            reasons.append("tcb.json says ok=%r, expected false" % report.get("ok"))
        reasons += judge(problems, expect)
    except (OSError, ValueError) as e:
        problems = []
        reasons.append("no readable tcb.json from the doctored run: %s" % e)
    print("tcb self-test: doctored %s -> %s" % (args.baseline, doctored_path))
    print("  altered the hash of `%s`, removed `%s`, added `%s`"
          % (expect["changed"], expect["entered"], expect["left"]))
    for p in problems:
        print("  reported: " + p)
    if reasons:
        print("tcb self-test FAILED: the check did not fail as it must")
        for why in reasons:
            print("  - " + why)
        if r.returncode != 1 or not problems:
            print("  tool output (tail):")
            for line in (r.stdout + r.stderr).splitlines()[-15:]:
                print("    " + line)
        return 1
    print("tcb self-test ok: the check fails on a doctored baseline, naming exactly the three doctored constants")
    return 0


if __name__ == "__main__":
    sys.exit(main())

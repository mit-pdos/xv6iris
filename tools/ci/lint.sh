#!/usr/bin/env bash
# tools/ci/lint.sh -- every source check that needs no Lean toolchain, in one
# place.  Seconds; run it before the build (CI) and before a commit.
#
#   layering   tools/check_layering.sh: the Spec/Proof/Link import discipline
#              (a Spec imports no Code/Proof/Link file, a Proof no other
#              Proof or Link, and only Link files import Proof files)
#   sorry      no `sorry`/`admit` in Xv6/, MachCSL/ or vtest-lean/
#   axiom      no `axiom` declaration there
#   native     no `native_decide`
#   options    no file turning `autoImplicit` back on
#   drift      every .lean under Xv6/ and MachCSL/ is imported from the
#              roots lake builds (a file that is not is checked by nobody)
#   toolchain  the pins agree: lean-toolchain of the package, of the model
#              and of lean-sail; lakefile.toml's iris revision and
#              lake-manifest.json's (tools/ci/toolchain_check.sh)
#   roots      tools/ci/roots.txt (the cone the coverage and dead-code
#              reports are about) and tools/audit/baseline.json (the theorems
#              whose axioms are audited) name the same top theorems
#
# The five middle lints are tools/lean_lint.py (see its docstring for what
# each guards).  Rocq's tools/comment_quote_check.py has no counterpart:
# Lean does not lex strings inside comments.
#
# EVERY lint runs even after one fails, so one run reports everything; the
# exit status is non-zero if any did.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
rc=0
tools/check_layering.sh || rc=1
python3 tools/lean_lint.py || rc=1
tools/ci/toolchain_check.sh || rc=1
python3 - <<'PY' || rc=1
import json, os, sys
roots = [l.split("#")[0].strip() for l in open("tools/ci/roots.txt", encoding="utf-8")]
roots = {r for r in roots if r}
if not os.path.exists("tools/audit/baseline.json"):
    print("roots: ok (%d top theorems; no tools/audit/baseline.json to compare with)" % len(roots))
    sys.exit(0)
audited = {t["name"] for t in json.load(open("tools/audit/baseline.json"))["theorems"]}
bad = 0
for n in sorted(roots - audited):
    print("roots: %s is in tools/ci/roots.txt but its axioms are not audited (tools/audit/baseline.json)" % n); bad = 1
for n in sorted(audited - roots):
    print("roots: %s is audited (tools/audit/baseline.json) but is not a root of the coverage cone (tools/ci/roots.txt)" % n); bad = 1
if not bad:
    print("roots: ok (%d top theorems, the audited ones)" % len(roots))
sys.exit(bad)
PY
if [ "$rc" -eq 0 ]; then echo "lint.sh: all lints passed"; else echo "lint.sh: FAILED (see above)"; fi
exit "$rc"

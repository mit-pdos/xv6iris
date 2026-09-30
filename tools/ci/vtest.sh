#!/usr/bin/env bash
# tools/ci/vtest.sh <command> -- THE DEVICE-CONFORMANCE SUITE (vtest-lean/).
# Rocq: the Makefile's vtest-* targets and CI step "Device conformance tests
# (vtest-rocq/, checked-in captures)".
#
# The machine's device and platform model -- the two UARTs, the PLIC, the
# virtio disk, and the Sail hart as the language runs it -- is re-checked
# against behaviours CAPTURED from QEMU (and from the VisionFive 2 board and
# the CVA6 RTL): each capture is a theorem that the language has an execution
# showing what the platform showed.  The captures are CHECKED IN, so nothing
# here runs QEMU except `gen`.  See tools/vtest/README.md.
#
#   check      build the green set (vtest-lean/Vtest.lean); lake's own status.
#              Rocq `make vtest-check`.
#   check-ci   WHAT CI RUNS.  Deletes every run proof's build products, builds
#              the green set (lake keeps going past a red proof, so one red run
#              does not hide the rest), then prints THE RUN TABLE and lets
#              `vtest.py table --check` be the verdict.  The table is appended
#              to $GITHUB_STEP_SUMMARY when that is set.
#              Rocq `make vtest-check-ci` + the CI step's summary.
#   passes     ATTEMPT every run's proof (green or not), flip the ones that
#              failed to the other form (agree <-> stuck) and attempt those,
#              then rewrite Vtest.lean with the ones that held and print the
#              table.  Rocq `make vtest-passes`.
#   table      print the table (text), from whatever is built.  Rocq `make vtest-table`.
#   explain [--all | <PLAT/Mod>...]   say WHY runs are red: DONE with which
#              result words differing, STUCK at which pc on which access,
#              BUDGET at which pc.  `--all` = every run with no proof.
#   gen [names|--all]   RE-RUN QEMU and rewrite the QEMU captures (needs
#              qemu-system-riscv64 and the riscv64 toolchain; never CI).
#              Rocq `make vtest-gen`.
#   runs       re-render every checked-in capture and proof (no QEMU).
#              Rocq `make vtest-runs`.
#
# EXIT STATUS: `check` is lake's; `check-ci` is non-zero iff a module the green
# set imports did not compile (i.e. a proof that used to hold stopped holding,
# or the harness broke).  A run with NO proof is a FINDING, not a failure: it
# is absent from Vtest.lean and its row in the table says `no proof`.
#
# Needs a machine sized for a Lean build (README: "Build"): run it on
# a build server or in CI, e.g.
#   tools/ci/vtest.sh check-ci
# Needs only `lake build MachCSL.Lang`'s cone (the model and the device
# language), not the proof tree.  Measured on the VM: the whole suite, 150
# run proofs, builds in ~10 s of wall clock (7 min of CPU) once the cone is
# built.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
export XV6_CI_OUT="${XV6_CI_OUT:-.lake/ci}"
mkdir -p "$XV6_CI_OUT"
VT="python3 tools/vtest/vtest.py"
LOG="${VTEST_LOG:-$XV6_CI_OUT/vtest-check.log}"

cmd="${1:-}"; shift || true
case "$cmd" in
  check)
    exec lake build Vtest
    ;;
  check-ci)
    # THE .olean ARE DELETED FIRST, and that is what makes "this run passed"
    # mean anything: the table reads the filesystem, and a FAILED rebuild
    # leaves the previous .olean in place.
    $VT clean-passes
    # lake's status is DISCARDED: the table is the report and the verdict.
    lake build Vtest > "$LOG" 2>&1 || true
    grep -E '^(error|✖)' "$LOG" | head -60 || true
    rc=0
    $VT table --check || rc=$?
    # The markdown table is regenerated rather than captured, so that a
    # failure above still leaves a table in the summary saying WHICH runs
    # are red.
    $VT table --format md > "$XV6_CI_OUT/vtest.md" || true
    if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
      cat "$XV6_CI_OUT/vtest.md" >> "$GITHUB_STEP_SUMMARY"
    fi
    if [ "$rc" -ne 0 ]; then
      echo "::error::A device-conformance proof stopped compiling; see $LOG and $XV6_CI_OUT/vtest.md." >&2
    fi
    exit "$rc"
    ;;
  passes)
    $VT passes --reset
    $VT clean-passes
    # every Pass module, not only the green ones: a proof that is not named
    # cannot even be TRIED.  lake keeps going past the red ones.
    lake build $($VT modules --kind pass) > "$XV6_CI_OUT/vtest-passes.log" 2>&1 || true
    # the ones that failed as "agree" are re-emitted as "stuck" and tried once
    $VT passes --built @olean
    missing="$($VT modules --kind missing)"
    if [ -n "$missing" ]; then
      lake build $missing >> "$XV6_CI_OUT/vtest-passes.log" 2>&1 || true
    fi
    # a run that holds in neither form goes back to "agree": that is the
    # claim it fails, and the one `explain` speaks to
    $VT passes --built @olean > /dev/null
    $VT project --from-build
    lake build Vtest >> "$XV6_CI_OUT/vtest-passes.log" 2>&1 || true
    $VT table
    ;;
  table)
    exec $VT table "$@"
    ;;
  explain)
    f="$($VT explain "$@")" || exit 1
    lake build Vtest.Diag $(grep -o 'Vtest\.[A-Z0-9]*\.[A-Za-z0-9]*Run' "$f" | sort -u) > /dev/null 2>&1 || true
    exec lake env lean "$f"
    ;;
  gen)
    exec $VT gen "${@:---all}"
    ;;
  runs)
    exec $VT runs
    ;;
  *)
    sed -n '2,45p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac

# Weak port — orchestrator resume (2026-10-06 21:20)

Resume note for the orchestrator. The owner's task: port the Rocq weak-memory development (the tip of the
weak line, jj change `xxvzwolszwmp` in `../xv6iris-spinlock`) to Lean on top of the lean branch. The port
lives in the jj workspace `weak` (`/home/bsdinis/dev/xv6iris-weak`, on top of `zplvqknr`). At the end, squash
all the `weak (WIP): …` commits into one commit on `zpl` and create the bookmark `weak`. Everything must be
fully proved (no sorry, axiom or native_decide).

## State

- **Done:** 209 of 537 live files (38.9%), 193.9k of 341.7k Rocq lines (56.8%). The tip is green: `lake
  build MachCSL Xv6 Weak` gives 2,986 jobs, and `tools/ci/lint.sh` passes.
- **Running:** nothing. All workers were wound down for the 5-hour limit, which resets Wed 00:20. There are
  no partially ported files.
- **Usage:** the weekly pool is at 86% (resets Mon 12:00). The port has used about 0.39 weekly points per 1k
  Rocq lines. Estimate to finish: ~58 points at the measured rate, 90–180 realistically.

## Orchestration kit: `/home/bsdinis/dev/weak-orch/` (stable, outside jj)

The kit moved here from the old session scratchpad.

| File | What it is |
|---|---|
| `sched.py` | Ready set. Run `python3 sched.py done.txt prog.txt`. DAG: `notes/weak-port-dag.json`. |
| `merge.sh` | `merge.sh SLOT "Mod Mod2" x`. Copies `Weak/<Mod>.lean` (+ `MachCSL/WeakAux*`) from `../xv6iris-weak-SLOT` to the tip, adds the `Weak.lean` imports, builds and lints on GCP. Prints `MERGE-FAILED` and exits 1 on failure. **Never pipe its output** (the exit status is lost). |
| `reslot.sh` | `reslot.sh SLOT [--force]`. Recreates workspace `../xv6iris-weak-SLOT` at the tip. Refuses when the slot has uncommitted changes, unless `--force` (a worker may be running there). |
| `depcheck.sh` | `depcheck.sh SLOT Mod`. Checks the deps exist in the slot. |
| `done.txt` / `prog.txt` | Done files / in-progress files (`Name slot [PARTIAL\|RESUME]`). |
| `skip.txt` | Files not ported. |
| `open_questions.txt` | Owner questions with their answers. |
| `stageC_prompt.txt` | The design-consult brief (below). |
| `parked/` | Parked partial files. |

- **Slots:** w1–w15 (`../xv6iris-weak-w<N>`).
- **Merge pattern after a green merge:** `cd ../xv6iris-weak && jj commit Weak Weak.lean -m "weak (WIP): <files>"`.
  Then append the base name to `done.txt`, delete its line from `prog.txt`, and run `reslot.sh SLOT --force`.
  Merge serially, one at a time.
- **Builds run only on GCP:** `~/.local/bin/lean-gcp -C <ws> <cmd>`. Never run `lake build` locally.

**Worker prompt template** (always `model: opus`, background):

> Workspace: /home/bsdinis/dev/xv6iris-weak-wN. FIRST read …/notes/weak-port-protocol.md (incl. "Cross-file
> facts") and follow it exactly (never git/jj, no subagents, builds only via `~/.local/bin/lean-gcp -C <ws> …`,
> do not edit Weak.lean, fully proved, duplicated-name rule + Lean-only helpers file-qualified; no Mathlib
> tactics). ASSIGNMENT: port Rocq <F>.v (<n> lines; split as <F>2 if a part elaborates > ~2 min or exceeds ~1500
> lines) to Weak/<F>.lean. <headers to read / reuse hints>. REPORT per protocol.

After each report, add any new cross-file fact to `notes/weak-port-protocol.md` and commit it with
`jj commit notes -m …`.

## Rules (owner)

- **Workers are Opus.** Never use Fable workers. One fresh Fable advisor per design consult is allowed.
- **5-hour pool:** launch nothing at ≳90%. At ≥95% (owner, 2026-10-07), SendMessage every worker to reach a green point
  (keep only fully proved declarations, write `PROGRESS-<F>.md`), report, and stop. To resume, back up
  `Weak/<F>*.lean` and `PROGRESS-*`, reslot, restore the files, then start a "RESUME" worker.
- **Weekly pool:** no cap ("go crazy, no limit"; still reported at status).
- **Status** (on "status"): give
  - % of files done **and** % of lines done;
  - % of files and lines targeted by running agents;
  - the usage estimate to completion;
  - open questions, last, through the AskUserQuestion menu.

  Every progress update shows files% **and** lines%.
- **Questions never block the port:** park only the files they affect.

## NEXT: Stage C (owner decision 2026-10-06 21:10)

**The decision:** D1 is reversed. Instruction fetches leave the AxSL/RVWMO graph tier and go through the
per-hart i-cache view (`itv`, `fence.i`), as the Lean machine tier already does. The owner's goals: verify the
main assumptions first, and keep it as simple as possible. This is recorded in
`notes/weak-port-architecture.md` ("Stage C").

Consequences:

- **The fetch-inertness bridge goes.** That means `lbFetchInert`, `candFetchInert(F)`, `emFetchInert`,
  `hullRunFetchInert`, `t2linFetchInert`, `fconfFetchInert`, `wfetchSite` and `hlblRealizesAx`'s extra
  conjunct. These are DELETED, not carried, so Q5 is superseded.
- **Q4 stays,** on the i-cache view: text never written, or the `fence.i` discipline (`efetchItvOk`,
  `fetchSrcOk`).

Steps:

1. **Design consult.** Spawn ONE fresh advisor (`model: fable`) with the brief in
   `/home/bsdinis/dev/weak-orch/stageC_prompt.txt`. It writes `notes/weak-port-o2-stageC.md`, covering
   - the assumption check (RVWMO/Zifencei; the Lean machine tier; no Rocq theorem depending on fetches as
     graph events, e.g. the g10/g40 counts and `lblIdent`; whether xv6 runs fresh code without `fence.i`);
   - the simplest design;
   - the ordered rework list of merged files (about 49 mention the fetch path);
   - the impact on unported files;
   - cost and owner questions.

   Show the owner the verdict and the design, and ask any questions it raises through the menu.
2. **Safe files, in parallel with the consult.** Launch these six ready files, which do not touch the
   fetch-in-graph path (checked against their Rocq sources): WkFetchPeel, WkTimerinit, AxDevGraphWit,
   AxToken, AxReadAll, AxInstrFacts.
3. **HELD until the design is approved:** AxLifting (uses AStepFetch), AxGateWp, WeakRvwmoCycWit,
   WeakRvwmoProgress (the supply/site chain), plus any later file on the fetch-in-graph path (Ax*
   graph/spike files and the WeakRvwmo* chain). Use the consult's list.
4. **Rework lane.** After approval, run the rework of the merged files in the consult's order. Use one
   sequential lane, or 2–3 lanes if independent. Each step is one Opus worker per file group, merged through
   `merge.sh`.
5. **Resume the port** on the new design. Update the protocol's "Cross-file facts" to delete the
   fetch-inertness entries.

## Critical path

AxWp is done. 314 files were downstream of it, and the Ax tier fans out from AxToken, AxLifting,
AxReadAll, AxInstrFacts, AxGateWp and others. Re-run `sched.py` after each merge.

## Update 2026-10-06 23:49: account changed, limits reset

- **New usage baseline:** both pools were at 0% at 193.9k Rocq lines done. Measure the rate against this
  account's seven_day from that point.
- **Launched:** the Stage C design consult (advisor) and six safe files in w1–w6: WkFetchPeel, WkTimerinit,
  AxDevGraphWit, AxToken, AxReadAll, AxInstrFacts. Each prompt says to STOP if the file relies on fetches
  being graph events.

## Update 2026-10-07 00:45: Stage C approved, rework running

- **Design:** notes/weak-port-o2-stageC.md. The rulings are in notes/weak-port-architecture.md: Q-C1 admin
  label; Q-C2 delete the oracle params; Q-C3 delete pstepNoFetch/pfFetchLoadOk; Q-C4 wlblRen fixes LIFetch.
- **Integration workspace:** `../xv6iris-weak-sc` (jj workspace `weak-sc`), forked from the tip.
- **Lane order:**
  1. L1a: items 1–3, plus item 21 if pstepNoFetch breaks it. RUNNING.
  2. L1b: items 4–8.
  3. Then lane 2 (items 9–18), in a sc2 workspace forked from sc, in parallel with lane 3 (items 19–20) in sc.
  4. Copy the lane 3 files into sc2, then do the full build plus lint.
  5. Copy the changed Weak/* into the tip, build, and commit as "weak (WIP): Stage C rework".
- **Commits:** after each lane is green, commit in the sc workspace (`jj commit Weak -m …`).
- **New ports:** keep going at the tip only for files off the fetch path. At the Stage C merge, re-check
  them against the new APIs.
- **Held until lane 1 and item 13 are done:** AxLifting, AxGateWp, AxInstr, AxWpdLift, WeakRvwmoCycWit,
  WeakRvwmoProgress.

## Update 2026-10-07 01:20: Stage C parallelized (owner: "as parallel as possible")

The real dependency order among the Stage C files comes from the DAG.

- **Critical path to AxLifting** (286 files wait on it):
  1. WeakRvwmoSupply
  2. ConfWit2
  3. Adm
  4. AxPair
  5. AxOpsem
  6. AxWp

  AxPair imports Supply, ConfWit2 and Adm, so lane "1b" could not go first.
- **Mechanics:** `sc` is the Stage C tip. Each worker runs in its own fork, created with
  `weak-orch/forksc.sh scN` from sc's @-. Results go back through `weak-orch/mergesc.sh SRC "Mods" msg`, which
  copies the files, builds those modules in sc, and commits in sc. Downstream may stay red until its own wave.
- **In sc:** lane 1a and AxDeps/AxGate are committed. AxOpsem has parked, uncommitted edits
  (PROGRESS-StageC-L1bA.md).
- **Running:**

  | Workspace | Work |
  |---|---|
  | sc2 | Supply (critical) |
  | sc3 | SrvwmoCapstone |
  | sc4 | Ax witness files |
  | sc5 | AxSpinSpike/Run, then AxScCat |
  | sc6 | Rvwmo witness files |

- **Next waves after Supply:**
  - [ConfWit2 → Adm] ∥ [Cert → Cert2 → Cert3/3b → Cert4] ∥ [LinInd, Fab, FabInd]
  - then [AxPair → AxOpsem (resume) → AxWp + importers] ∥ [Lin2] ∥ [Glue → Glue2]
  - then Capstone, then Walk/2/3, then CycWit/Progress.
- **AxLifting/AxInstr/AxWpdLift:** port them in a fork as soon as AxWp lands.

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

## Update 2026-10-07 ~03:00: Stage C MERGED into the tip

- **Merged:** commit "Stage C rework". 44 files, full build green (3,011 jobs), lint passes.
- **Protocol notes:** the stale fetch-inertness entries are replaced by one Stage C entry.
- **The sc workspaces** (`xv6iris-weak-sc*`) are side history now. Workers still running in sc3 (AxLifting) and
  sc4 (AxInstr) are merged into the tip with `merge.sh sc3 AxLifting x` (merge.sh accepts any slot name).
- **Open owner questions:**
  - Q6: `pstepNoFetch` stays in WeakRobustMain.
  - Q7: AxSfence/AxSfence2 sfence representation. AxSfence2 is HELD.

## Update 2026-10-07 15:57: idle until the 19:00 five-hour reset

- **Done:** 358/537 files; the tip is green (3,148 jobs), lint passes, roots unchanged. Nothing running.
- **At the reset, in this order:**
  1. Q12 fix-up worker (owner: change the existing lemmas): restate AxSpinRow `rowStuckR`/`rowStuckOfFirst`/`wpdMStuck`/`firstEv` and AxEpiChainSdLd `wpdOfClosedRunGM` with the fetch pin, fix the merged importers, then add `row_stuck_of_chain` to AxSpinVA. Then AxSpinVA2.
  2. Launch the ready set: AxSymCtl, AxSymMem, AxSpineOk4, AxDataX, AxSpinProt5, AxSpinProt4 (+ whatever sched.py lists).
  3. RESUME the parked partials: AxEpiSound3, AxScRun3 (`weak-orch/parked/`, PROGRESS files inside).
- **Lessons from today:** never pre-warn about the limit in launch prompts (workers stop early); reslot or depcheck right before every launch; workers must grep the tip for every new short name.

## Update 2026-10-07 20:02: wind-down at 95%; next reset Thu 00:00

- Done ~413/537. Winding down: AxSymMem3 (w3), AxEpiRet (w1, may touch AxCjrReach), AxWalk3 (w4) → PROGRESS files; park and RESUME at reset.
- At the reset: (1) RESUME the three parked files; (2) Q16 rework worker (AxSymCtl5: EvB "fetch with no image bytes ⇒ stuck" constructor + capstone); (3) launch the ready set: AxDataX7 (CRITICAL chain), AxWalk7, AxPtwModel, AxDataX5, AxDataX8, AxRelease7, AxRelease8, AxSpinH5, AxSpinH3, AxSpinX6 + whatever sched.py lists. Use weak-orch/prep.sh in the same step as each launch.
- 20:2x: all three wound down and parked in weak-orch/parked/: AxWalk3 (14/34 + CertWP kit), AxEpiRet (part 1 merged: AxCjrReach memWrite exit + AxEpiRetb; capstone pending), AxSymMem3 (27/29 proved but `wpCldspC` kernel check ~300 s — resume worker must fix or isolate it in a Lean-only AxSymMem3b before merge; Q17 on dropped `wp_cpuid_c`). Nothing running.

## Update 2026-10-08 01:05: stopped launching at 90%; next reset Thu 05:00
- Merged through AxSpinPO batch; ~475/537. Running (will wind down at 95%): see weak-orch/prog.txt.
- At 05:00: RESUME every parked partial (weak-orch/parked/, prog.txt RESUME lines), then the ready set from sched.py with the CRITICAL CHAIN first (AxSpinE6 → E8 → AxSpinPO* → AxSpinAp*), each slot via weak-orch/prep.sh in the same step. Wakeups: watch5h 30 101, at.sh 05:01, crons 05:03 + 05:17.
- Open owner questions to ask at next status: Q18 (allocpid inlined), Q19 (Cert sfence arm), INFO-DROP AxEpiRetFwd (14 trivial-instance decls).
- 01:1x wind-down: parked in weak-orch/parked/: AxSpinE6 (8/13; Q20 on Xx_ret), Q19 (11 files green in w5; merge blocked only by AxCertP2 needing `cSf` cases in `AxCertP2.cinv` (CInvO announce arm) and in the bridge induction at ~line 902 — use `AxCert2.wpdSfNodeM`; a pinned bridge may need a twin like `AxCondM2.wpdPinSf`), AxSymMem3 (resume). At 05:00: FIRST a worker in w5 to add the AxCertP2 cSf cases and merge Q19 (11 files + AxCertP2); then E6 resume (Q20 provisional), AxCertP3, AxSpinXP, AxSpinAp6, AxSpinHd6/6b/6c + sched.py.
- AxSymMem3 resume: cause of 300 s found (see protocol KERNEL BLOW-UP); fix plan in parked/AxSymMem3/PROGRESS; Q17 not started.

## Update 2026-10-08 01:2x: owner answers Q18–Q20; plan for the 05:00 window
1. w5: AxCertP2 `cSf` cases, then merge Q19 (11 parked files + AxCertP2).
2. Q20 DESIGN CONSULT (one fresh Fable advisor, advisory only): how to make diverted fetches outside kernel text no-image fetches so FirstRd/frNf make them stuck — which image (graph `gxImg` vs `imgS σi`) must be restricted to kernel text, what premises AxSpinE3 (`wpdOffrowM` HGimg)/E4/E5/E6 change, impact on merged files. Then one rework worker, then resume AxSpinE6 (parked) and continue E8 → AxSpinPO*.
3. Q18: one worker designs + reworks the Ap line against allocproc's inlined copy (Ap..Ap5 rework, then Ap6..Ap9), cross-checking every word against Xv6/KernelImage.lean.
4. AxSymMem3 resume (perf fix per protocol KERNEL BLOW-UP; Q17 wp_cpuid_c).
5. Ready set: AxCertP3, AxSpinXP, AxSpinHd6/6b/6c (+ sched.py); AxSpinAp6 HELD for Q18.

## Update 2026-10-08 06:35 — Q22 (4-byte alignment) found; plan for the 10:00 reset
- 537 merged; running: AxSpinCtl3 (w7), AxSpinAp9 (w4), AxSpinPO6 (w2), AxSpinAqr (w6). Remaining after these: see sched.py.
- **Q22:** `textAt4S` requires 4-aligned pc; in this kernel ~half of 4-byte words are 2 mod 4 (mycpu, push_off, allocproc/allocpid, initlock, sched, swtch, …). Theorems over those texts are vacuous (AxSpinE8f.mycpuTextFalse). Provisional fix: generalize to 2-aligned 4-byte text (two-halfword fetch), then re-run non-vacuity certs.
- **At 10:00 (first launch):** one fresh Fable advisor with brief `~/dev/weak-orch/q22_prompt.txt`; then the Q22 rework lane per its notes (notes/weak-port-q22-align.md); and any parked/ready files.
- 06:4x: 95% reached → wind-down. 539 merged. AxSpinAp9 (w4) and AxSpinPO6 (w2) told to park green (PROGRESS-*.md). READY but not launched: AxSpinRow3 (must reuse AxSpinCtl3 `wJalSlot/wBranchSlot/wEpilogue5`, take/supply `wBrTaken`). At 10:00: Q22 consult first, then resume Ap9/PO6 (back up Weak/<F>*.lean + PROGRESS, reslot, restore, RESUME worker), launch Row3.
- 06:5x: PO6 merged (540). AxSpinAp9 parked green in ~/dev/weak-orch/parked/AxSpinAp9/ (partial: defs/address lemmas done; `wpdAllocpidCs` pending — plan in PROGRESS-AxSpinAp9.md; Q18 notes in parked/Q18). Nothing running. 10:00 wave: (1) Q22 Fable consult (q22_prompt.txt); (2) RESUME AxSpinAp9 (prep.sh w4 AxSpinAp9 AxSpinAp9.lean after restoring the parked file + PROGRESS files); (3) AxSpinRow3. Note Q22 may make Ap/PO/acquire wpds vacuous — Ap9/Row3 proceed anyway; the Q22 rework fixes text predicates underneath.
- 08:1x owner rulings: Q22 fix (consult first at 10:00), Q18a-c / Q20' / Q21 / all INFO accepted.

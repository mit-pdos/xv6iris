# PROGRESS — S0-P part (2), milestone 1: machine v2 over the litmus corpus (label level)

Worker: Opus (S0P2), 2026-11-02. Workspace `/home/bsdinis/dev/xv6iris-pcsl2`. Plan of record rev 7 (§1A, §8 S0-P).

## Defects of machine v2 found by the corpus (each with its fix status)

**S0P2-F1 — FIXED. Acquire load forwarded from an own plain store got view `t` (STRONGER, K1M class).**
- Where: `Weak/Prom/Machine.lean` `fwdView` (was `if aq then t else …`, ~line 267).
- Found by: 116 tests, all `MR=STRONGER MH=STRONGER` (`RELAX/PosWRPAq` 69, `RELAX/Rfi` 23, `RELAX/PosWR` 15,
  `SAFE/*[ws-rf]paq*` 6, `ATOMICS/SAFE_PosWRXAq` 3). Example `RELAX/PosWRPAq/SB+pospaq-addraqps`:
  `sw x5,0(x6); lw.aq x7,0(x6); xor; add; lw x9,0(x11)` ‖ symmetric, `exists (0:x9=0 /\ 1:x9=0)`: reference and herd
  Sometimes, machine Never.
- Spec: no RVWMO ppo rule orders a po-earlier PLAIN store before an acquire load that reads it (rule 5,
  rvwmo.adoc:287 "a has an acquire annotation", orders the acquire before LATER operations; rule 7 needs both RCsc,
  and a release store is already under `ldPre`'s `wVRel`); the load value axiom lets the load return "Stores that
  write that byte and that precede i in program order". PARM `FwdItem.read_view` (papers/pulte/coq/Promising.v:528–531)
  gives the forward view except for an EXCLUSIVE write on RISC-V (v2's exclusive forward view is already `ts`, M1).
- Fix: a forwarded byte gets the forward view whatever `aq` (argument kept, unused). Mark after fix: FAITHFUL.
  After the fix all 116 agree with the reference and herd.

**S0P2-F2 — FIXED. Mismatched LR/SC: the SC could precede the store its LR read (WEAKER).**
- Where: `Weak/Prom/Machine.lean` `memStep.sc` (new premise `∀ t ∈ R.rvTs, t < ts`, ~line 578);
  `MachExplore.succ` `.sc` mirrors it.
- Found by: `HAND/LR-SC-diff-loc4` (`MR=WEAKER`; the machine agreed with herd's appendix cat, the known appendix bug):
  P1 `sw.rl x7,0(z); lr.w x9,0(z); sc.w x2,x1,0(x)`: the LR forwards from the own `sw.rl` at `tf`; the SC to `x`
  could take `ts < tf` (`exclOk`'s window `(tf, ts-1]` empty; the forward view is below `tf`), closing a cycle the
  reference forbids.
- Spec: Atomicity Axiom, rvwmo.adoc:330–334 "s is a store to byte x, and r returns a value written by s, then s must
  precede w in the global memory order". For matched pairs `cohBelow` already implied it. Mark after fix: FAITHFUL.

**S0P2-D3 — OPEN (not fixed: label-alphabet change, needs a decision). LR/SC and Zalasr second annotation dropped
(WEAKER).**
- Where: `PLabel.LExLoad`/`LLoad` have no release bit, `LExStore`/`LStore` no acquire bit (Machine.lean §7); Emit.lean
  passes only `akAcq ak` (ramRead/ramWrite). So `lr.aqrl` (release-RCsc), `sc.aqrl` (acquire-RCsc), `l*.aqrl`,
  `s*.aqrl` lose one annotation.
- Found by: `HAND/LR-SC-NOT-FENCE` (`lr.w.aq.rl; sc.w.aq.rl` between `sw a` and `lw b`, both harts,
  `exists (c=1 /\ d=1 /\ 0:x7=0 /\ 1:x7=0)`): reference and herd Never, machine Sometimes (SB through the pair).
- Spec: rvwmo.adoc:124–128 "An AMO, lr, or sc instruction with both aq and rl set has both acquire-RCsc and
  release-RCsc annotations"; rules 5/6 (rvwmo.adoc:287–288). Either missing bit alone lets the SB outcome through.
- Fix proposal (not applied): `LExLoad aq rl …` with `rl → ldPre ⊔ vrOld ⊔ vwOld` (rule 6) and the RCsc `wVRel`
  raise; `LExStore aq rl …` with the acquire post (`vrNew/vwNew ⊔= ts`, rule 5); same for Zalasr `LLoad`/`LStore`;
  Emit must pass both bits from the access kind. Touches the alphabet, two arms each, and Emit: reported, not done.

## Results (`~/dev/weak-orch/promising/litmus/`)

- `machine-cap8.txt` (final, after F1/F2; machine + reference outcome sets + herd States, ≤ 8 memory instructions):
  7907 files, 7869 compared, 19 parse-out-of-scope (same as S0P1), 19 over the cap.
  - machine vs reference (OUTCOME SETS, projected on herd's state keys ∪ condition keys): **7868 eq, 1 WEAKER**
    (D3). Verdicts: Never 4908, Sometimes 2950, Always 10 agree; 1 differs (D3).
  - machine vs herd (appendix cat + LrScDiffOk): 7862 eq, 3 herd-has-more (`LR-SC-diff-loc3`, `LR-SC-diff-loc4`,
    `PPOLDSTLD02` — the three known appendix-weaker tests, notes/riscv-model-bugs.md; machine = reference),
    1 machine-has-more (D3), 3 `na` (herd timed out: `ATOMICS/CO/2+2W+…sxx…`; machine Never = old herd logs).
- `machine-cap99-noref.txt` (machine vs herd, no cap): all 7888 parsed files; the 19 over-cap tests are compared
  too: all eq with herd or herd timed out (6 more `na`, machine Never). Same 4 disagreements.
- `machine-run1-prefix.txt` (before F1/F2): 116 STRONGER (F1), LR-SC-diff-loc4 WEAKER (F2), D3.
  `machine-run2-afterF1F2.txt`: intermediate (herd duplicate-name lookup not yet fixed: SF_THESIS/HAND/CoWR `na`).
- No test hit an explorer budget; no run was dropped as out of scope (no misaligned access); `varsOkB` held on every
  reference path; every closure reached its fixpoint at iteration 2.
- Time: machine 185–226 CPU-s for the whole corpus (interpreted, `lean --run`; 27 s wall on 80 shards);
  reference outcome sets 10 265 CPU-s (≈ 4 min wall on 80 shards).

## Done (green)

- `Weak/Prom/MachExplore.lean` — `Mach.succ img log i prom ws t`: every `memStep` whose label instantiates template
  `t`, as a plain function over v2's types with v2's own post-state functions; Bool transcriptions of every premise
  (`writesInB`, `exclOkB`, `invalReadB`, `loadOkB`, `cohBelowB`, `promHas`); complete read-candidate generator
  (`readCands`, argument in the header; candidates are filtered by `loadOkB`, so only completeness rests on it).
- `Weak/Prom/MachLitmus.lean` — label-level front end (table + Sail-gap list 1–8 in the header), explorer
  (promises-first normal form; per-hart message-list closure `sigmaAll`; arrangements `arrange`; per-hart DFS
  `hartRuns`; outcome product `outcomesM`).
- `Weak/Prom/MachOracle.lean` — driver `<repo> <herd.logs> <cap> <shard> <shards> [noref]`; reference outcome sets
  via RefCheck's enumerator (`refOutcomes`, every consistent candidate); herd `States` (k-th block of a name for the
  k-th file of that name, LC_ALL=C path order).
- Machine.lean: F1, F2 (above). Emit.lean rebuilds unchanged. Lint: only the expected drift findings.

## Explorer completeness (what milestone 1's exactness rests on; to be proved in milestone 2)

1. `PF.validRun_factorL` (promises-first normal form; append-stability + own-promise-monotonicity, Machine.lean
   header). 2. `succ` complete per template (MachExplore header). 3. NOTA: a message's address/data/existence depend
   only on answers below its EXT bound, so value chains have ≤ K messages and `sigmaAll`'s domain covers every valid
   run (the corpus reaches the fixpoint anyway, but a fixpoint alone does not exclude self-justifying values: NOTA
   does). 4. `arrange`'s pruning (own overlapping messages in program order) follows from `cohBelow` + `coh` monotone.

## Next

- Milestone 2: prove `explorerStep_sound` (`succ` ⊆ `memStep`: five Bool↔Prop lemmas + `contains ↔ ∈`), emit run
  certificates (promise events in M order + per-hart traces) checked against `validRun`; then the completeness side
  (`PF.validRun_factorL`, NOTA, `readCands`).
- Milestone 3: the same corpus through `pstepV2` (Sail): fetch labels, split AMOs (`amoSplitFused`), decoder sources
  vs litmus operands, `match_reservation` both ways, parked FENCE.TSO half.
- D3: owner/coordinator decision on the alphabet change.

## Runner (was `litmus-appx/run.sh`; `litmus-appx/` = `model-results/herd.logs` (copy of
herdcheck/herd-appendix-lrscdiffok.logs) + `tests/` of litmus-tests-riscv 08728edc, created in the workspace for the
VM sync and deleted after the runs)

```sh
N=$1; X=$2; rm -rf /tmp/machor; mkdir -p /tmp/machor; k=0
while [ $k -lt $N ]; do
  (lake env lean --run Weak/Prom/MachOracle.lean litmus-appx litmus-appx/model-results/herd.logs ${CAP:-8} $k $N $X \
     > /tmp/machor/out-$k.txt 2>&1; echo "exit $?" >> /tmp/machor/out-$k.txt) &
  k=$((k+1)); done; wait
k=0; while [ $k -lt $N ]; do cat /tmp/machor/out-$k.txt; k=$((k+1)); done
```

# PROGRESS — AmoSplit (`amoSplitFused`, S1M-proof, plan rev 7 §1 M10 (4), NA-5)

Worker: Opus (AmoSplit). Workspace `/home/bsdinis/dev/xv6iris-pcsl3` (at qxqkyqrz). Brief:
`~/dev/weak-orch/promising/AmoSplit_prompt.txt`.

## Status (top): GREEN, DONE; no kill criterion fired
- Build: `lake build Weak.Prom.AmoSplitCheck` green (imports AmoSplitV2 and AmoSplitLit). `#print axioms` of every
  theorem below: propext, Classical.choice, Quot.sound. No sorry/axiom/native_decide/opaque/implemented_by.
- Kill criterion (program-specific named inputs): NOT fired. One named SCOPE premise, `amoTightV2 ps` (a fact about
  Sail's `execute_AMO` over reachable states, like `translationOff`), only for the `pstepV2` instance; none for
  the generic theorems or the litmus corollaries.

## Statements
- Step level (plan M10 (4) literally), `AS.amoSplitFused_mem` (AmoSplit.lean): with `regOnly asrc`, `regOnly vsrc`
  and `ws.wRmw = none`,
  `memStep ws (LRmw aq rl base tvs data asrc vsrc) (some ts) ws' prom' ↔
   ∃ ws1, memStep ws (LAmoLd aq base tvs asrc) none ws1 prom ∧ memStep ws1 (LAmoSt rl base data asrc vsrc) (some ts) ws' prom'`.
  (`split_rmw` also gives: a write half at base' after a read at base forces base' = base.)
- Run level, generic over the program half (AmoSplit.lean):
  - `fusedToSplit` (premise `FuseOk`): every valid fused run is a valid split run with the SAME final config,
    traces related by `TrRel` (each `LRmw` ↦ `LAmoLd`, `LSilent`*, `LAmoSt`, same fulfil ts).
  - `splitToFused` (premise `SplitOk`: invariant, non-half steps are fused steps, silent/read steps fabric-free,
    TIGHTNESS, read+silents+write is a fused `LRmw`): every valid split run has a fused run with the same image,
    final memory, fabric, agent count; traces `TrRelP`; every final agent equal, or the hart is between its halves
    (`pendS`, slot full). `splitToFused_closed`: if no hart ends between its halves (`closedS`), SAME final config.
    Proof: `validRun_factorL`, then a simulation where the fused copy waits at the read half (`AgRel`/`SRel`).
  - `fuseStep pstepS` = the canonical fused program; `splitOk_fuse`, `fuseOk_fuse`.
- Emission v2 (AmoSplitV2.lean): `pstepV2_fab` (non-`LDev` steps neither read nor move the fabric) and
  `pstepV2_amoSrcs` (AMO-half sources register-only) PROVED by unfolding Emit.lean; `amoSplitFused` (both
  directions, closed runs), `amoSplitFused_behavior` (`pmBehavior (fuseStep pstepV2) cfg ↔ pmBehavior pstepV2 cfg ∧
  closedS cfg`), `amoSplitFused_any` (general form), all under `amoTightV2 ps`.
- Corollaries (AmoSplitLit.lean): `litStepS` = `litStep` with each AMO emitted as Sail does (`LAmoLd aq`, queued
  `LAmoSt rl`, then `rd`, `LInstr`); `fuseOk_lit`, `splitOk_lit` PROVED (no premise);
  `Cmp.rvwmo_complete_split` = `rvwmo_complete`'s full conclusion over `litStepS`;
  `Cmp.litS_of_lit` = every `lit_`-shaped property of finished `litStep` runs holds of finished `litStepS` runs.

## Findings (incl. wRmw, M10 (1)/(3))
- `wRmw` behaves as needed: empty at `psInit`, filled only by `amoLd`, emptied by `amoSt`/`LInstr`, kept by every
  other arm (`memStep_rmw_none`); the fused post-state equals the split one exactly when the slot is empty at the
  read (always, in tight runs). `amoSt` checks base and width and carries aq (`rmAq`).
- NOT checked by the machine: that the write half's address sources equal the read's (the fused label has one
  `asrc`) — needed as part of tightness; true for v2 (both `depsAddr` of the same bits, and the premise).
- `regOnly` needed: with `DLdRes` in a half's sources the pair and the fused step differ (the write half sees the
  read's `wLdv`). Emission v2's AMO sources are `DReg` lists (proved).
- FALSE as literally briefed: "no other event of the hart between the halves" — Sail emits `LSilent` steps between
  them (`rX_bits rs2`), and other harts interleave; both handled (silent chain, simulation). For `amocas` the pair
  is NOT one fused op: a failed compare has no write (or a write-back after `LRegW rd`), so `amoTightV2` excludes
  it (the Sail runner STOPs on it). A trap between halves would also leave a dangling read (not ruled out here).
- The corollary connects `rvwmo_complete` to the split litmus front end `litStepS`; there is still no theorem
  relating `litStep`/`litStepS` to `pstepV2` (that link is S0P3's empirical Sail = label level).

## Workspace edits
- NEW `Weak/Prom/AmoSplit.lean`, `Weak/Prom/AmoSplitV2.lean`, `Weak/Prom/AmoSplitLit.lean`,
  `Weak/Prom/AmoSplitCheck.lean` (`#print axioms` only). No existing Lean file edited.
- COPIED `model/Lean_RV64D/LeanRV64D/ZkrControl.lean` verbatim from `~/dev/xv6iris-pcsl5` (Regen's new Zkr module;
  missing here although `ZicsrInsts.lean` imports it, so nothing importing the model built; the only difference
  between the two `model/` trees — same finding as pcsl6's PROGRESS-HavocProm.md). The coordinator should check
  the merged chain carries it.

## Log
- 2026-11-04: `Weak.Prom.AmoSplit` GREEN (`amoSplitFused_mem`, `splitToFused`, `splitToFused_closed`,
  `fusedToSplit`).
- 2026-11-04: `Weak.Prom.AmoSplitV2` GREEN (`pstepV2_fab`, `pstepV2_amoSrcs`, `splitOk_v2`, `amoSplitFused`,
  `amoSplitFused_behavior`, `amoSplitFused_any`).
- 2026-11-04: `Weak.Prom.AmoSplitLit` GREEN (`rvwmo_complete_split`, `litS_of_lit`); `AmoSplitCheck` axioms clean.

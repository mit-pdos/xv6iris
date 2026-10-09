/-
Weak: **THEOREM 2, STAGE 2 / certificate (a-): THE PREFIX WITNESS APPLIED** — Theorem 1 of
stage 2 (`allocpid2Distinct2`, AxSpinT2b2: `allocpidOpen2` with a phantom, empty-row third hart)
instantiated on the concrete prefix-witness graph `AxSpinT2p1c.gAm`: hart A (0, proc[0]) stopped
just after its `sw nextpid` (row length 101, inside its critical section), hart B (1, proc[1])
stopped just after ONE failed `amoswap.w.aq` (row length 38; holding's long arm passed), C = 2 a
phantom with an empty row.  Every premise is discharged; the final theorem
`allocpidPrefixCert` has NO hypotheses.

Lean-only (no Rocq source).  Stage-2 design `notes/weak-lb-thm2-stage2.md` §C row `AxSpinT2e1`
(certificate (a-); computation half `AxSpinT2p1*`) and acceptance (ii): `allocpidOpen2` APPLIED
with B INCOMPLETE — the prefix family (rows that stop mid-segment, inside the spin loop) is
exercised.

## What this file proves

**`allocpidPrefixCert`**, at `GD = gtAdGd gAm`, `q_A = q0`, `q_B = qB1`:
```
  ¬ t2Cut GD 0 (sZ 0) (pEx 0) ∧ ¬ t2Cut GD 1 (sZ 1) (pEx 1) ∧
  ¬ t2Complete GD 0 (sZ 0) (pEx 0) ∧ ¬ t2Complete GD 1 (sZ 1) (pEx 1)
```
The two `¬ t2Cut` conjuncts are taken from the CONCLUSION of `allocpid2Distinct2` (not from
AxSpinT2p1c's direct `notCutA1`/`notCutB1`, which the bundle also has): the point of the
certificate is that the stage-2 premises are jointly satisfiable on prefix rows.  The two
`¬ t2Complete` conjuncts (from `AxSpinT2p1c.prefixWitness`) are stated so that the reader sees
the other three conjuncts of `allocpid2Distinct2` (`t2Complete → npSrc`, both complete →
distinct pids) are VACUOUS on this run: neither hart is complete, so they are dropped.  Their
non-vacuous exercise is certificate (a′) on full rows (`allocpidOpenCert`, stage 1; stage-2
re-plumbing is `AxSpinT2c6`'s row in the design).

## How

Premises of `allocpid2Distinct2` (A, B, C = 0, 1, 2; `Sf = sZ`, `pf = pEx`, `ptp = ptpX`,
`σi = σX`, `T = tX`, `satp0 = satpX`, `n0 = 1`):
* model: `AxSpinT2p1c.catAm`, `ctrlAm`; `Hharts` (gmo ⊆ {0, 1}) by one `decide +kernel` over the
  interleaving `il1`; `HrowC` = `AxSpinT2p1.growC1`;
* layout / image: `AxSpinT2c1.layHyp3`, `AxSpinT2c5.al3`, `Himgc` / `Himgn` from AxSpinT2c5's
  `imgClb` / `imgNp` (same image `img`, rewritten by `rfl`), `HimgNoff` from `prefixWitness`;
* text / translation: AxSpinT2c5's eight text facts, `mapOk3`, `AxSpinT2pt.satpXFacts`,
  `textFixed` = `AxSpinT2p1.textFixed1`;
* rows / pins: `prefixWitness` (`allocPre`, `AllocPins2`);
* (Q-S2-B, 2026-10-08: the capstone no longer has the source-alignment premises
  `HsrcAlA`/`HsrcAlB` — protocol full-width lk->cpu writes, AxSpinX deviation 8 — so nothing is
  discharged for them here);
* entry: `AxSpinT2e3.entryR` (`entryOk`, incl. `ctrlOkSW`; graph-independent);
* run: `AxSpinT2p1c.runAm` (step counts / final states chosen per hart; ends at the row end,
  `¬ midState`).

## Pins / honesty
* No drive is re-run: every run fact comes through `AxSpinT2p1c.runAm` (AxSpinT2p1a/b's `runA`/
  `runB`), never a `match`/`decide` on `emsA`/`emsB`.
* C is a phantom (empty row), so this certificate does not exercise C's freedom (that is
  certificates (b) / (p-lk)).  The kept pins of `AllocPins2` hold on this run (the checker
  `pins2B`), and the inherited (a′) scope applies (kvmmake-shaped `tX`, warm TLB, image).
* Prefix closure stays informal (Q-S2-6): the cut-off rows are simply the graph's rows.

Reused: `allocpid2Distinct2` (AxSpinT2b2), `AxSpinT2p1c.gAm`/`catAm`/`ctrlAm`/`runAm`/
`prefixWitness`, `AxSpinT2p1.growC1`/`textFixed1`/`il1`, `catTAd`, `AxSpinT2e3.entryR`, `AxSpinT2c1.layHyp3`/`sZ`/`q0`/`ptpX`, `AxSpinT2c5.*` (text,
`mapOk3`, `al3`, `imgClb`, `imgNp`, `σX`), `AxSpinT2pt.satpXFacts`.
Names: `allocpidPrefixCert` (Lean-only, grepped absent); helpers `Weak.AxSpinT2q2.*`.
-/
import Weak.AxSpinT2b2
import Weak.AxSpinT2p1c
import Weak.AxSpinT2e3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2p1 AxSpinT2p1c
open AxSpinT2c1 (q0 sZ ptpX layHyp3)

namespace AxSpinT2q2

/-- The layout of the prefix witness. -/
def lay : Xlay := xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX

theorem imgAm : gAm.gtG.gxImg = fun a => some (AxSpinT2c1.img a) := rfl

theorem imgG3 : (AxSpinT2c1.gT3 []).gtG.gxImg = fun a => some (AxSpinT2c1.img a) := rfl

/-- `Himgc` on the prefix-witness graph (`lk->cpu` = 0 in the image). -/
theorem imgClbAm : ∀ a, a ∈ clb lay → gAm.gtG.gxImg a = some b0 := by
  intro a ha
  have H := AxSpinT2c5.imgClb [] lay rfl a ha
  rw [imgG3] at H
  rw [imgAm]
  exact H

/-- `Himgn` (n0 = 1) on the prefix-witness graph. -/
theorem imgNpAm : ∀ (j : Nat) a v, (npb lay)[j]? = some a →
    (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[j]? = some v → gAm.gtG.gxImg a = some v := by
  intro j a v h1 h2
  have H := AxSpinT2c5.imgNp [] lay rfl j a v h1 h2
  rw [imgG3] at H
  rw [imgAm]
  exact H

/-- `Hharts` of Theorem 1: only harts 0 and 1 emit memory events (C = 2 is a phantom). -/
theorem harts2 : ∀ e, e ∈ gAm.gtG.gxGmo → e.1 ∈ [(0 : Agent), 1] := by
  intro e he
  have H : il1.all (fun e : Geid => decide (e.1 ∈ [(0 : Agent), 1])) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 H e he)

theorem stK (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) :
    (AxEpiRun.st cpu m rs ib k).atK = k := rfl

end AxSpinT2q2

set_option maxHeartbeats 1600000 in
/-- **Certificate (a-): the stage-2 capstone APPLIED on PREFIX rows, no hypotheses.**  On the
concrete prefix-witness graph (A stopped after `sw nextpid`, B after one failed claim, C a
phantom), Theorem 1 of stage 2 gives: neither A nor B ends at a taken panic / `intr_on` arm.
Neither row is complete (so the `t2Complete →` conjuncts of the capstone are vacuous here and
dropped). -/
theorem allocpidPrefixCert :
    ¬ t2Cut (gtAdGd gAm) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ t2Cut (gtAdGd gAm) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    ¬ t2Complete (gtAdGd gAm) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ t2Complete (gtAdGd gAm) 1 (sZ 1) (AxSpinT2a.pEx 1) := by
  obtain ⟨-, -, HpA, HpB, HqA, HqB, -, -, HnA', HnB', HimgN⟩ := prefixWitness
  obtain ⟨uA, rsA, ibA, nA, HrA, -⟩ := runAm 0 (by decide)
  obtain ⟨uB, rsB, ibB, nB, HrB, -⟩ := runAm 1 (by decide)
  have H := allocpid2Distinct2 gAm 0 1 2 sZ AxSpinT2a.pEx ptpX q0 qB1 AxSpinT2c5.σX tX
    (BitVec.ofNat 64 satpX) 1
    (fun i => AxEpiRun.st (cpuOf i) (.pure ()) (regsE i) ibNone 0)
    (fun i => if i = 0 then
        AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA (AxOpsem.grow (gtAdGd gAm) 0).length
      else
        AxEpiRun.st (cpuOf 1) (.pure uB) rsB ibB (AxOpsem.grow (gtAdGd gAm) 1).length)
    (fun i => if i = 0 then nA else nB)
    catAm ctrlAm AxSpinT2q2.harts2 (growC1 _) layHyp3 (AxSpinT2c5.al3 0) (AxSpinT2c5.al3 1)
    AxSpinT2q2.imgClbAm (by decide) AxSpinT2q2.imgNpAm HimgN
    AxSpinT2c5.acquireTextX AxSpinT2c5.mycpuTextX AxSpinT2c5.pushOffTextX
    AxSpinT2c5.holdingTextX AxSpinT2c5.popOffTextX AxSpinT2c5.releaseTextX
    AxSpinT2c5.allocpidTextX AxSpinT2c5.tailTextX
    (textFixed1 _ 0 (by decide)) (textFixed1 _ 1 (by decide))
    satpXFacts.1 satpXFacts.2.1 satpXFacts.2.2
    (AxSpinT2c5.mapOk3 0 (by decide)) (AxSpinT2c5.mapOk3 1 (by decide))
    HpA HpB HqA HqB
    (AxSpinT2e3.entryR 0 (by decide)) (AxSpinT2e3.entryR 1 (by decide))
    (fun _ nm i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact HrA Xv6N nm
      · exact HrB Xv6N nm)
    (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact AxSpinT2q2.stK _ _ _ _ _)
    (AxSpinT2c1.finNotMid _ _ _ _ _) (AxSpinT2c1.finNotMid _ _ _ _ _)
  obtain ⟨Hcut, -, -, -⟩ := H
  exact ⟨Hcut 0 (by decide), Hcut 1 (by decide), HnA', HnB'⟩

end Weak

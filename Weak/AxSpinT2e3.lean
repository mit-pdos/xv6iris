/-
Weak: **THEOREM 2 / certificate (b), NON-VACUOUS: `allocpidRaceCert`** — the unlocked nextpid
racer's WPd at the joint xv6 protocol is NOT provable on the CONCRETE race graph
`AxSpinT2e3.gRace` (AxSpinT2e1's literal 3-hart run with the drives of `AxSpinT2c2` (A) and
`AxSpinT2e2` (B)): a statement with NO hypotheses, by applying AxSpinT2d's reductio
`allocpidRaceUnprovable` with EVERY premise discharged.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-design.md` §A.4, §C.6 (b) (in
../xv6iris-lbthm2).

## What this file proves

§1 ENTRY.  `ctrl0`/`ctrl1`: `ctrlOkSW tX satpX (regsE h)` (the S-mode / SIE = 0 regime + PMP W
of the warm entry registers; the TLB conjunct is `AxSpinT2c5.tlbExactW`) — the conjunct of
`entryOk` AxSpinT2c1 / AxSpinT2pt leave open; `entryR`: AxSpinT2a's `entryOk` for harts 0 / 1
(PC = allocproc + 0x38, sp = `sZ h`, s1 = `&proc[h]`, tp = `h`, warm TLB by
`AxSpinT2c1.entryHit`).
§2 `textFixedR` (`HfixA`/`HfixB` on the race graph, from `AxSpinT2e1.readsOff`).
§3 **`allocpidRaceCert`**:
  `¬ (∀ Hinv Hann nm, ⊢ xv6Init L (gtAdGd gRace) nm 2 -∗ WPd_{protXv6 L} ⟨hp cpu0 rcM0 zeroRegs, 0⟩ {{True}})`
  with `L = xlayXv6 0 1 2 sZ pEx ptpX`.  The premises of `allocpidRaceUnprovable`: consistency /
  ctrl closure (`AxSpinT2e1.catR`/`ctrlR`, generic `graphOfSc` lemmas on the drives' emissions),
  harts, layout (`AxSpinT2c1.layHyp3`, `sZAl`), image (`AxSpinT2c5.imgClb`/`imgNp`, n0 = 1),
  text (`AxSpinT2c5.*TextX`), `textFixedR`, translation (`AxSpinT2pt.satpXFacts`,
  `AxSpinT2c5.mapOk3`), rows (`AxSpinT2e1.fullA`/`fullBG`), pins (`pinsA`/`pinsBG`), entry
  (`entryR`), runs (`AxSpinT2e1.runAR`, `AxSpinT2e2.runB`, ending at an instruction boundary,
  `AxSpinT2c1.finNotMid`), and the race (`rowCEq`, `rfRace`, `ltRace`).

## Pins / honesty
* The scope pins of Theorem 2 (AllocPins: Option V arms, Q18b `≠ 1000` / no wrap / no
  collision) all HOLD on B's race row (nextpid read 3), so the refutation is inside the
  theorem's scope; what fails is only `npSrc` for B (AxSpinT2d.raceNotSrc).
* Inherited scope of (a′)'s machinery: `tX` is kvmmake-SHAPED with A = D preset, the TLB is
  warm, the image models only text / page tables / nextpid (AxSpinT2pt, AxSpinT2c1 headers).
* C is the hand-node racer of AxSpinT2d (start state `⟨hp cpu0 rcM0 zeroRegs, 0⟩`, verbatim).
* No drive is re-run here: the runs come from read-backs over variable drive results.

Reused: `allocpidRaceUnprovable` (AxSpinT2d), `AxSpinT2e1.*`, `AxSpinT2e2.runB`,
`AxSpinT2c2.emsA`, `AxSpinT2c1.layHyp3`/`sZAl`/`entryHit`/`finNotMid`/`q0`/`sZ`/`ptpX`,
`AxSpinT2c5.*`, `AxSpinT2pt.regsE`/`satpXFacts`/`satpX`, tactic `ax_epi_ledger_krfl`.
Names: Lean-only; `allocpidRaceCert` (grepped absent), helpers in `Weak.AxSpinT2e3`.
-/
import Weak.AxSpinT2e2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt

namespace AxSpinT2e3

/-! # 1. Entry -/

set_option maxHeartbeats 0 in
theorem ctrl0 : ctrlOkSW tX (BitVec.ofNat 64 satpX) (regsE 0) := by
  unfold ctrlOkSW ctrlOkS AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts pmpW
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    AxSpinT2c5.tlbExactW, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first | decide +kernel | ax_epi_ledger_krfl

set_option maxHeartbeats 0 in
theorem ctrl1 : ctrlOkSW tX (BitVec.ofNat 64 satpX) (regsE 1) := by
  unfold ctrlOkSW ctrlOkS AxSpineOk6.pmpOk AxSpineOk6.sconfMsFacts pmpW
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    AxSpinT2c5.tlbExactW, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first | decide +kernel | ax_epi_ledger_krfl

/-- AxSpinT2a's `entryOk` for harts 0 and 1 at their warm entry state. -/
theorem entryR (h : Agent) (hh : h < 2) :
    entryOk tX (BitVec.ofNat 64 satpX) h (AxSpinT2c1.sZ h) (AxSpinT2a.pEx h)
      (AxEpiRun.st (cpuOf h) (.pure ()) (regsE h) ibNone 0) := by
  match h, hh with
  | 0, _ =>
    exact ⟨regsE 0, ibNone, rfl, ctrl0, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, AxSpinT2c1.entryHit 0 (by decide)⟩
  | 1, _ =>
    exact ⟨regsE 1, ibNone, rfl, ctrl1, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, AxSpinT2c1.entryHit 1 (by decide)⟩

/-! # 2. `textFixed` on the race graph -/

theorem textFixedR (E : List (List Eitem)) (h : Agent) (hh : h < 3) :
    textFixed (gtAdGd (AxSpinT2e1.gT E)) h (imgS AxSpinT2c5.σX) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · have H := AxSpinT2c5.imgAgree [] a b hab
    rw [show (gtAdGd (AxSpinT2c1.gT3 [])).gdG.gxImg = fun a => some (AxSpinT2c1.img a) from rfl]
      at H
    rw [show (gtAdGd (AxSpinT2e1.gT E)).gdG.gxImg = fun a => some (AxSpinT2c1.img a) from rfl]
    exact H
  intro k lb aq base n vs hk hr hi
  rw [AxSpinT2e1.growR] at hk
  have H := List.all_eq_true.1 (List.all_eq_true.1 AxSpinT2e1.readsOff h (List.mem_range.2 hh))
    lb (List.mem_of_getElem? hk)
  rw [hr] at H
  simp only [hi, Option.isNone_some] at H
  cases H

/-! # 3. The certificate -/

theorem imgG (E : List (List Eitem)) :
    (AxSpinT2e1.gT E).gtG.gxImg = fun a => some (AxSpinT2c1.img a) := rfl

theorem imgG3 : (AxSpinT2c1.gT3 []).gtG.gxImg = fun a => some (AxSpinT2c1.img a) := rfl

/-- AxSpinT2b `Himgc` on the race graph. -/
theorem imgClbR (E : List (List Eitem)) (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) :
    ∀ a, a ∈ clb L → (AxSpinT2e1.gT E).gtG.gxImg a = some b0 := by
  intro a ha
  have H := AxSpinT2c5.imgClb [] L hL a ha
  rw [imgG3] at H
  rw [imgG]
  exact H

/-- AxSpinT2b `Himgn` (n0 = 1) on the race graph. -/
theorem imgNpR (E : List (List Eitem)) (L : Xlay) (hL : L.xlNp = AxSpinT2a.zNp) :
    ∀ (j : Nat) a v, (npb L)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 1))[j]? = some v →
        (AxSpinT2e1.gT E).gtG.gxImg a = some v := by
  intro j a v h1 h2
  have H := AxSpinT2c5.imgNp [] L hL j a v h1 h2
  rw [imgG3] at H
  rw [imgG]
  exact H

theorem stK (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) :
    (AxEpiRun.st cpu m rs ib k).atK = k := rfl

/-- THE CONCRETE RACE GRAPH (A's and B's recorded emissions, C's hand emission). -/
noncomputable def gRace : GdexecT :=
  AxSpinT2e1.gT [AxSpinT2c2.emsA, AxSpinT2e2.emsB, AxSpinT2e1.emsC]

/-- The layout of the race. -/
def lay : Xlay := xlayXv6 0 1 2 AxSpinT2c1.sZ AxSpinT2a.pEx AxSpinT2c1.ptpX

end AxSpinT2e3

set_option maxHeartbeats 800000 in
/-- **CERTIFICATE (b), NON-VACUOUS: `allocpidRaceCert`.**  On the concrete race graph (A runs
xv6's allocpid segment, B claims pid_lock, the unlocked racer C bumps nextpid 2 → 3, B reads 3),
the racer's WPd at the joint xv6 protocol is NOT provable.  No hypotheses. -/
theorem allocpidRaceCert :
    ¬ (∀ [InvGS_gen .hasNoLC AxSpinX7.xv6GF] [AxannotGS AxSpinX7.xv6GF] (nm : Xv6N),
        ⊢ xv6Init AxSpinT2e3.lay (gtAdGd AxSpinT2e3.gRace) nm 2 -∗
          @tierAWpd AxSpinX7.xv6GF .hasNoLC _ _ (xv6Pol AxSpinT2e3.gRace)
            (gtAdGd AxSpinT2e3.gRace) Xv6N Unit (protXv6 AxSpinT2e3.lay) nm
            ⟨hp cpu0 AxSpinT2d.rcM0 zeroRegs, 0⟩ .MaybeStuck 2 (fun _ => iprop(True))) := by
  obtain ⟨uA, rsA, ibA, hokA, HrA⟩ := AxSpinT2e1.runAR
  obtain ⟨uB, rsB, ibB, hokB, HrB⟩ := AxSpinT2e2.runB
  obtain ⟨nA, HnA⟩ := HrA [AxSpinT2c2.emsA, AxSpinT2e2.emsB, AxSpinT2e1.emsC]
  obtain ⟨nB, HnB⟩ := HrB [AxSpinT2c2.emsA, AxSpinT2e2.emsB, AxSpinT2e1.emsC]
  have hL : AxSpinT2e3.lay.xlLk = AxSpinT2a.zLk := rfl
  have hN : AxSpinT2e3.lay.xlNp = AxSpinT2a.zNp := rfl
  exact allocpidRaceUnprovable AxSpinT2e3.gRace 0 1 2 AxSpinT2c1.sZ AxSpinT2a.pEx
    AxSpinT2c1.ptpX AxSpinT2c1.q0 AxSpinT2c1.q0 AxSpinT2c5.σX tX (BitVec.ofNat 64 satpX) 1
    (fun i => AxEpiRun.st (cpuOf i) (.pure ()) (regsE i) ibNone 0)
    (fun i => if i = 0 then
        AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA (AxOpsem.grow (gtAdGd AxSpinT2e3.gRace) 0).length
      else
        AxEpiRun.st (cpuOf 1) (.pure uB) rsB ibB (AxOpsem.grow (gtAdGd AxSpinT2e3.gRace) 1).length)
    (fun i => if i = 0 then nA else nB) AxSpinT2e1.tsC AxSpinT2e1.wC
    (AxSpinT2e1.catR _ _ hokA hokB) (AxSpinT2e1.ctrlR _ _ hokA hokB)
    (AxSpinT2e1.hartsIn _) AxSpinT2c1.layHyp3 (AxSpinT2c1.sZAl 0) (AxSpinT2c1.sZAl 1)
    (AxSpinT2e3.imgClbR _ AxSpinT2e3.lay hL) (by decide) (AxSpinT2e3.imgNpR _ AxSpinT2e3.lay hN)
    AxSpinT2c5.acquireTextX AxSpinT2c5.mycpuTextX AxSpinT2c5.pushOffTextX
    AxSpinT2c5.holdingTextX AxSpinT2c5.popOffTextX AxSpinT2c5.releaseTextX
    AxSpinT2c5.allocpidTextX AxSpinT2c5.tailTextX
    (AxSpinT2e3.textFixedR _ 0 (by decide)) (AxSpinT2e3.textFixedR _ 1 (by decide))
    satpXFacts.1 satpXFacts.2.1 satpXFacts.2.2
    (AxSpinT2c5.mapOk3 0 (by decide)) (AxSpinT2c5.mapOk3 1 (by decide))
    (AxSpinT2e1.fullA _) (AxSpinT2e1.fullBG _) (AxSpinT2e1.pinsA _) (AxSpinT2e1.pinsBG _)
    (AxSpinT2e3.entryR 0 (by decide)) (AxSpinT2e3.entryR 1 (by decide))
    (fun _ nm i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact HnA (cpuOf 0) Xv6N nm
      · exact HnB (cpuOf 1) Xv6N nm)
    (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact AxSpinT2e3.stK _ _ _ _ _)
    (AxSpinT2c1.finNotMid _ _ _ _ _) (AxSpinT2c1.finNotMid _ _ _ _ _)
    (AxSpinT2e1.rowCEq _) (AxSpinT2e1.rfRace _) (AxSpinT2e1.ltRace _)

end Weak

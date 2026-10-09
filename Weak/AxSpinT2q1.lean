/-
Weak: **THEOREM 2, STAGE 2 / certificate (a′): `allocpidOpen2` APPLIED** — the stage-2 capstone
(AxSpinT2b2) instantiated on the SAME concrete 3-hart serial run as stage 1's certificate
(AxSpinT2c: harts A, B, C = 0, 1, 2 on proc[0..2], nextpid 1 → 2 → 3 → 4, C := the same
allocpid segment; rows, graph `gT3`, runs `AxSpinT2c2.runA` / `AxSpinT2c3.runB` /
`AxSpinT2c4.runC`, image `AxSpinT2c5.σX`).  Every premise of `allocpidOpen2` is discharged; the
final theorem `allocpidOpen2Cert` has NO hypotheses.  It is the non-vacuity certificate of
stage 2 on FULL rows (design `notes/weak-lb-thm2-stage2.md` §C row `AxSpinT2c6`, acceptance (i);
the file name `AxSpinT2c6` was not used — this is `AxSpinT2q1`).

Lean-only (no Rocq source).

## What this file proves

§1 THE STAGE-2 PREMISES of (a′), at every emission `E` (`q = AxSpinT2c1.q0`, h ∈ {0, 1, 2}):
  `preG : allocPre (grow (gtAdGd (gT3 E)) h) q0 h (sZ h) (pEx h)` — stage 1's FULL rows are in the
    prefix family (`preOfFullPins` on `AxSpinT2c1.fullG` / `pinsG`: the five panic / `intr_on`
    gates, push_off's branch bit and the 18 reload gates are passed, read off stage 1's pins);
  `pins2G : AllocPins2 (gtAdGd (gT3 E)) h q0` (`pins2OfPins` on `pinsG`);
  `imgNoffG : HimgNoff (gtAdGd (gT3 E)).gdG.gxImg 0 1` (`cpus[].noff = 0` in the graph image,
    `AxSpinT2p1.himgNoff`);
  (Q-S2-B, 2026-10-08: the capstone's source-alignment premises `HsrcAlA`/`HsrcAlB` are gone —
    protocol full-width lk->cpu writes, AxSpinX deviation 8 — and their discharge `srcAlG` with
    it); kept, informational: `clAlG : clAligned (clb L)` (every `lk->cpu` write of the graph is
    acquire's full 8-byte `sd`), ONE `decide +kernel` of `AxSpinT2p1.clAlB` on the untagged
    graph `gR3` (rows E-independent, `gtGEq3`).
§2 **`allocpidOpen2Cert`** (NO hypotheses), at `GD = gtAdGd (gT3 [emsA, emsB, emsC])`,
`L = xlayXv6 0 1 2 sZ pEx ptpX`:
  `¬ t2Cut GD 0 (sZ 0) (pEx 0) ∧ ¬ t2Cut GD 1 (sZ 1) (pEx 1) ∧
   npSrc GD.gdG L (0, t2KBd q0) (0, t2KA q0) ∧ npSrc GD.gdG L (1, t2KBd q0) (1, t2KA q0) ∧
   t2Complete GD 0 … ∧ t2Complete GD 1 … ∧ pidOf GD 0 q0 ≠ pidOf GD 1 q0 ∧
   pidOf GD 0 q0 = some (wbytes 4 1#32) ∧ pidOf GD 1 q0 = some (wbytes 4 2#32)`
— the cut conjuncts, the `npSrc` conjuncts and `≠` come from `allocpidOpen2` (its `t2Complete →`
premises discharged by `AxSpinT2c1.completeG`, so not vacuous); the pid words are
`AxSpinT2c.pidLit`.

## Pins / honesty

* No drive is re-evaluated: every fact about `drvA/B/C` / `emsA/B/C` comes through
  `AxSpinT2c2.runA` / `AxSpinT2c3.runB` / `AxSpinT2c4.runC` (read-backs over a variable drive
  result); the kernel check `clAlLit` evaluates only the untagged literal graph
  `gR3` (no emission).
* On full rows `¬ t2Cut` is also derivable WITHOUT the capstone (`AxSpinT2f.notCutOfComplete`);
  the certificate's content is that ALL of `allocpidOpen2`'s premises (incl. the new
  `HimgNoff`, guarded pins) are jointly satisfiable on a real-machine run.  It does
  not exercise C's freedom (C is the same allocpid) nor the prefix family (rows are complete):
  those are certificates (p-lk) (AxSpinT2p2*) and (a-) (AxSpinT2p1*).
* Scope inherited from (a′) (AxSpinT2c header): `tX` kvmmake-shaped with A = D preset, warm TLB,
  image = text / tables / nextpid.

Reused: `allocpidOpen2` (AxSpinT2b2), `preOfFullPins`/`pins2OfPins`/`HimgNoff` (AxSpinT2f),
`AxSpinT2p1.clAlB`/`clAlOfB`/`clbEq`/`himgNoff`,
`AxSpinT2c.s0X`/`satpE`/`entryOkE`/`hartsX`/`pick3*`/`stAtK`/`wpdC`/`pidLit`, `AxSpinT2c1.*`
(`gT3`, `rows3`, `il3`, `rowsFixed`, `cat3`, `ctrl3`, `fullG`, `pinsG`, `completeG`, `layHyp3`,
`finNotMid`, `img`, `sZ`, `q0`, `ptpX`), `AxSpinT2c5.*` (text premises, `textFixedX`, `mapOk3`,
`imgClb`, `imgNp`, `al3`), `AxSpinT2pt.satpXFacts`, `AxSpinT2b.mem3`.
Names: `allocpidOpen2Cert` (Lean-only, grepped absent); helpers in the namespace
`Weak.AxSpinT2q1`.
-/
import Weak.AxSpinT2b2
import Weak.AxSpinT2c
import Weak.AxSpinT2p1

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2c1 AxSpinT2c5 AxSpinT2c

namespace AxSpinT2q1

/-! # 1. The stage-2 premises of (a′) -/

section prem
variable (E : List (List Eitem)) (h : Agent) (hh : h < 3)
include hh

/-- **`allocPre`**: (a′)'s full rows are in the prefix family (all gates passed). -/
theorem preG : allocPre (AxOpsem.grow (gtAdGd (gT3 E)) h) q0 h (sZ h) (AxSpinT2a.pEx h) :=
  preOfFullPins (fullG E h hh) (pinsG E h hh)

/-- **`AllocPins2`**: the kept pins (Q18b, `ppArm`, the interim `rlEnd`), from stage 1's. -/
theorem pins2G : AllocPins2 (gtAdGd (gT3 E)) h q0 := pins2OfPins (pinsG E h hh)

end prem

/-- **`HimgNoff`** on (a′)'s graph image (`cpus[].noff = 0`). -/
theorem imgNoffG (E : List (List Eitem)) : HimgNoff (gtAdGd (gT3 E)).gdG.gxImg 0 1 :=
  AxSpinT2p1.himgNoff 0 1

/-- The untagged (a′) graph (emission-independent). -/
def gR3 : Gexec := ⟨fun a => some (img a), rows3, il3⟩

theorem gtGEq3 (E : List (List Eitem)) : (gT3 E).gtG = gR3 := by
  show (⟨fun a => some (img a), scProg rows3 (sim img rows3 il3).sOut, il3⟩ : Gexec) = gR3
  rw [rowsFixed]; rfl

/-- Every `lk->cpu` write of (a′)'s graph is full-width (acquire's `sd`). -/
theorem clAlLit : AxSpinT2p1.clAlB gR3 (clRange (AxSpinT2a.zLk + 16) 8) = true := by
  decide +kernel

/-- The global form `clAligned` (every `lk->cpu` write of (a′)'s graph is full-width — the
run's writes have the shape `protXv6`'s `CLFULL` demands; informational since Q-S2-B). -/
theorem clAlG (E : List (List Eitem)) (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) :
    clAligned (clb L) (gtAdGd (gT3 E)).gdG := by
  rw [AxSpinT2p1.clbEq L hL]
  show clAligned _ (gT3 E).gtG
  rw [gtGEq3]
  exact AxSpinT2p1.clAlOfB _ _ clAlLit

end AxSpinT2q1

open AxSpinT2q1 AxSpinT2c2 AxSpinT2c3 AxSpinT2c4

/-! # 2. THE CERTIFICATE -/

set_option maxHeartbeats 1600000 in
/-- **Certificate (a′) for stage 2: `allocpidOpen2` APPLIED, no hypotheses.**  On the concrete
3-hart serial run of xv6's real inlined allocpid (harts 0, 1, 2 on proc[0..2], C := the same
segment), at the drives' own emission: neither A nor B ends at a taken panic / `intr_on` cut, A's
and B's nextpid reads are sourced by the gmo-latest nextpid write before their claim, both rows
are complete, and the stored pids are distinct — concretely 1 and 2. -/
theorem allocpidOpen2Cert :
    ¬ t2Cut (gtAdGd (gT3 [emsA, emsB, emsC])) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ t2Cut (gtAdGd (gT3 [emsA, emsB, emsC])) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    npSrc (gtAdGd (gT3 [emsA, emsB, emsC])).gdG (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)
      (0, t2KBd q0) (0, t2KA q0) ∧
    npSrc (gtAdGd (gT3 [emsA, emsB, emsC])).gdG (xlayXv6 0 1 2 sZ AxSpinT2a.pEx ptpX)
      (1, t2KBd q0) (1, t2KA q0) ∧
    t2Complete (gtAdGd (gT3 [emsA, emsB, emsC])) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    t2Complete (gtAdGd (gT3 [emsA, emsB, emsC])) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 0 q0 ≠ pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 1 q0 ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 0 q0 = some (WeakInterpProj.wbytes 4 1#32) ∧
    pidOf (gtAdGd (gT3 [emsA, emsB, emsC])) 1 q0 = some (WeakInterpProj.wbytes 4 2#32) := by
  obtain ⟨uA, rsA, ibA, -, okA, runA'⟩ := runA
  obtain ⟨uB, rsB, ibB, -, okB, runB'⟩ := runB
  obtain ⟨uC, rsC, ibC, -, okC, runC'⟩ := runC
  obtain ⟨nA, HnA⟩ := runA' [emsA, emsB, emsC]
  obtain ⟨nB, HnB⟩ := runB' [emsA, emsB, emsC]
  obtain ⟨nC, HnC⟩ := runC' [emsA, emsB, emsC]
  have HconsT := cat3 emsA emsB emsC okA okB okC
  have Hcl := ctrl3 emsA emsB emsC okA okB okC
  obtain ⟨hmode, hasid, hppn⟩ := satpXFacts
  obtain ⟨sN, hsN⟩ : ∃ f : Agent → Athread, f = pick3
    (AxEpiRun.st (cpuOf 0) (.pure uA) rsA ibA
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 0).length)
    (AxEpiRun.st (cpuOf 1) (.pure uB) rsB ibB
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 1).length)
    (AxEpiRun.st (cpuOf 2) (.pure uC) rsC ibC
      (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) 2).length) := ⟨_, rfl⟩
  have Hrun : ∀ (_ : AxannotGS AxSpinX7.xv6GF) (nm : Xv6N) i, i ∈ [(0 : Agent), 1, 2] →
      nsteps (tierAAstep (gtAdGd (gT3 [emsA, emsB, emsC])) nm i) (pick3 nA nB nC i) (s0X i)
        (sN i) := by
    intro _ nm i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [hsN, pick3Z, pick3Z]; exact HnA (cpuOf 0) Xv6N nm
    · rw [hsN, pick3O, pick3O]; exact HnB (cpuOf 1) Xv6N nm
    · rw [hsN, pick3T, pick3T]; exact HnC (cpuOf 2) Xv6N nm
  have Hend : ∀ i, i ∈ [(0 : Agent), 1, 2] →
      (sN i).atK = (AxOpsem.grow (gtAdGd (gT3 [emsA, emsB, emsC])) i).length := by
    intro i Hi
    rcases AxSpinT2b.mem3 Hi with rfl | rfl | rfl
    · rw [hsN, pick3Z]; exact stAtK _ _ _ _ _
    · rw [hsN, pick3O]; exact stAtK _ _ _ _ _
    · rw [hsN, pick3T]; exact stAtK _ _ _ _ _
  have H := allocpidOpen2 (gT3 [emsA, emsB, emsC]) 0 1 2 sZ AxSpinT2a.pEx ptpX q0 q0 σX tX satpE 1
    s0X sN (pick3 nA nB nC) HconsT Hcl (hartsX _) layHyp3 (al3 0) (al3 1)
    (imgClb _ _ rfl) (by decide) (imgNp _ _ rfl) (imgNoffG _)
    acquireTextX mycpuTextX pushOffTextX holdingTextX popOffTextX releaseTextX allocpidTextX
    tailTextX (textFixedX _ 0 (by decide)) (textFixedX _ 1 (by decide)) hmode hasid hppn
    (mapOk3 0 (by decide)) (mapOk3 1 (by decide))
    (preG _ 0 (by decide)) (preG _ 1 (by decide)) (pins2G _ 0 (by decide)) (pins2G _ 1 (by decide))
    (entryOkE 0 (by decide)) (entryOkE 1 (by decide)) rfl Hrun Hend
    (by rw [hsN, pick3Z]; exact finNotMid _ _ _ _ _) (by rw [hsN, pick3O]; exact finNotMid _ _ _ _ _)
    (fun nm => wpdC _ nm (catTAd _ HconsT))
  obtain ⟨Hcut, HsA, HsB, Hpid⟩ := H
  have HcA := completeG [emsA, emsB, emsC] 0 (by decide)
  have HcB := completeG [emsA, emsB, emsC] 1 (by decide)
  obtain ⟨Hne, -⟩ := Hpid HcA HcB
  obtain ⟨Hp0, Hp1, -⟩ := pidLit [emsA, emsB, emsC]
  exact ⟨Hcut 0 (by simp), Hcut 1 (by simp), HsA HcA, HsB HcB, HcA, HcB, Hne, Hp0, Hp1⟩

end Weak

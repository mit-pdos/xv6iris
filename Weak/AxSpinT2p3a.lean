/-
Weak: **THEOREM 2, STAGE 2 / certificate (p-stk): THE DRIVE OF HART A ON THE RELOAD-CUT ROW,
THE CONCRETE GRAPH AND ITS PREMISE BUNDLE** — ONE `decide +kernel` running `drive2` (the
proved-sound driver, AxScRun2: it re-runs the REAL `riscvStep` against the graph's row) on
`AxSpinT2p3.rowAS` (9 items: the 8 spills, then mycpu's `ld ra, 8(sp)` loading C's planted
`push_off + 0x30` into `ra`) from the warm entry state `(.pure (), AxSpinT2pt.regsE 0)`; then
`gStk` = the (p-stk) graph at the recorded emissions (A's, the phantom B's empty one, C's hand
emission) and on it every premise the computation half supplies, with `t2Cut A` HOLDING via
`reloadMis` at `.poMy1`.

Lean-only (no Rocq source).  Design `notes/weak-lb-thm2-pins.md` §P1 (p-stk); template
`AxSpinT2p2a`.  The reductio through `allocpidOpen2` is the later capstone's.

## What this file proves

`chkA : AxSpinT2p1.chkG rowsS 0 rowAS drvA = true` (THE evaluation); `runA :
AxSpinT2p1.RunOk rowsS ilS 0 (regsE 0) emsA` (read-back over a VARIABLE drive result).
`gStk := gTS [emsA, [], emsCS]`; `catStk : rvwmoCatConsistentT gStk`, `ctrlStk : ctrlClosed
gStk` (GENERIC `graphOfSc` lemmas); `hartsStk`; `runStkA` (A's RUN premise on `gStk` from
`AxEpiRun.st (cpuOf 0) (.pure ()) (regsE 0) ibNone 0` to the row end, `.pure`, `¬ midState`);
`runStkB` (the phantom: 0 steps, row end 0); `runStkC` (C's run `⟨hp cpu rcMS zeroRegs, 0⟩ →
⟨hp cpu hlt zeroRegs, 1⟩` in 1 `astepAnyNfGv` step, row end 1); and the bundle **`stkCert`**:
  `allocPre (grow (gtAdGd gStk) 0) q0 0 (sZ 0) (pEx 0)` ∧ A's three non-interim `AllocPins2`
  fields (`npNowrap`, `npNcoll`, `ppArm`, verbatim) ∧ `LEN A = rlPos .poMy1 q0` ∧
  `¬ rlGateOk .poMy1 (grow …) q0` ∧ `reloadMis …` ∧ `t2Cut (gtAdGd gStk) 0 (sZ 0) (pEx 0)` ∧
  `¬ entersPanic …` ∧ `¬ intrOnCut …` ∧ `¬ t2Complete …` ∧
  (B: `allocPre (grow (gtAdGd gStk) 1) q0 1 …` ∧ `AllocPins2 … 1 q0` ∧ `¬ t2Cut … 1 …`) ∧
  `HimgNoff` ∧ `grow (gtAdGd gStk) 2 = rcRowS`.
Plus `notPinsStk : ¬ AllocPins2 (gtAdGd gStk) 0 q0` (the interim `rlEnd`; `AxSpinT2p3` header).

## Pins / honesty
* Every proof mentioning `drvA` / `emsA` goes through `runA`.  Scope and the `AllocPins2`
  deviation as `AxSpinT2p3`.

Reused: `AxSpinT2p1.drvG`/`chkG`/`runOfChkG`/`catOf`/`ctrlOf`, `AxSpinT2p3.*`,
`AxSpinT2c1.emsOf`/`finNotMid`.  Names: Lean-only, `Weak.AxSpinT2p3a.*`.
-/
import Weak.AxSpinT2p3

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2p3
open AxSpinT2c1 (hartOkB q0 sZ)

namespace AxSpinT2p3a

/-- Hart A's drive on its reload-cut row. -/
noncomputable def drvA : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  AxSpinT2p1.drvG rowAS (regsE 0)

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkA : AxSpinT2p1.chkG rowsS 0 rowAS drvA = true := by decide +kernel

/-- Hart A's emission. -/
noncomputable def emsA : List Eitem := AxSpinT2c1.emsOf drvA

/-- Hart A's run premise (no re-evaluation). -/
theorem runA : AxSpinT2p1.RunOk rowsS ilS 0 (regsE 0) emsA :=
  AxSpinT2p1.runOfChkG rowsS ilS 0 rowAS (regsE 0) drvA growAS rfl chkA

/-- THE CONCRETE (p-stk) GRAPH. -/
noncomputable def gStk : GdexecT := gTS [emsA, [], emsCS]

theorem okA : hartOkB rowsS 0 emsA = true := by
  obtain ⟨_, _, _, h, _⟩ := runA; exact h

/-- Consistency of the concrete graph, by the GENERIC SC lemma. -/
theorem catStk : rvwmoCatConsistentT gStk := AxSpinT2p1.catOf rowsS ilS _ _ _ shilS okA okBS okCS

/-- Ctrl closure of the concrete graph. -/
theorem ctrlStk : ctrlClosed gStk := AxSpinT2p1.ctrlOf rowsS ilS _ _ _ okA okBS okCS

theorem hartsStk : ∀ e, e ∈ gStk.gtG.gxGmo → e.1 ∈ [0, 1, 2] := hartsS _

/-- A's RUN premise on the concrete graph (to the row end = right after the reload, an
instruction boundary). -/
theorem runStkA : ∃ (u : Unit) (rs : RegFile) (ib : Ibch) (n : Nat),
    (∀ (N : Type) (nm : N), nsteps (tierAAstep (gtAdGd gStk) nm 0) n
      (AxEpiRun.st (cpuOf 0) (.pure ()) (regsE 0) ibNone 0)
      (AxEpiRun.st (cpuOf 0) (.pure u) rs ib (AxOpsem.grow (gtAdGd gStk) 0).length)) ∧
    ¬ midState (AxEpiRun.st (cpuOf 0) (.pure u) rs ib (AxOpsem.grow (gtAdGd gStk) 0).length) := by
  obtain ⟨u, rs, ib, -, H⟩ := runA
  obtain ⟨n, Hn⟩ := H [emsA, [], emsCS]
  exact ⟨u, rs, ib, n, fun N nm => Hn _ N nm, AxSpinT2c1.finNotMid _ _ _ _ _⟩

/-- The phantom B: 0 steps, its row end is 0. -/
theorem runStkB (N : Type) (nm : N) (s : Athread) (hs : s.atK = 0) :
    nsteps (tierAAstep (gtAdGd gStk) nm 1) 0 s s ∧
      s.atK = (AxOpsem.grow (gtAdGd gStk) 1).length := by
  refine ⟨nsteps_O _, ?_⟩
  unfold gStk; rw [growBS, hs]; rfl

/-- C's run (`HrowC` ⇒ 1 step, row consumed). -/
theorem runStkC (cpu : CPU) :
    nsteps (astepAnyNfGv (gtAdGd gStk) 2) 1 ⟨hp cpu rcMS zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 1⟩ ∧
    (AxOpsem.grow (gtAdGd gStk) 2).length = 1 :=
  ⟨rcRunS cpu _ 2 (growCS _), by unfold gStk; rw [growCS]; rfl⟩

/-- HONEST: the merged `AllocPins2` (interim `rlEnd`) excludes A's row on the concrete graph. -/
theorem notPinsStk : ¬ AllocPins2 (gtAdGd gStk) 0 q0 := notPinsAS _

/-- **THE (p-stk) CERTIFICATE, premise bundle**: on the concrete graph A is a family row (with
the non-interim guarded pins) whose `.poMy1` reload read C's planted value — `t2Cut` via
`reloadMis`, no panic / `intr_on` cut; the phantom B is a (trivial) family row at no cut; the
image premise holds; C's row is the racer's. -/
theorem stkCert :
    allocPre (AxOpsem.grow (gtAdGd gStk) 0) q0 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    (∀ vs, graphValue (gtAdGd gStk) (0, t2KBd q0) = some vs →
      (wordOfBytes 4 vs : BitVec 32) ≠ 1000#32 ∧ (wordOfBytes 4 vs : BitVec 32).toNat + 1 < 2 ^ 32) ∧
    (∀ vs, graphValue (gtAdGd gStk) (0, t2KBd q0) = some vs → ∀ j, j < 64 → ∀ v,
      graphValue (gtAdGd gStk) (0, t2KBd q0 + 1 + j) = some v →
        (wordOfBytes 4 v : BitVec 32) ≠ wordOfBytes 4 vs) ∧
    (∀ vn, graphValue (gtAdGd gStk) (0, t2KPp q0 + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = q0.c) ∧
    (AxOpsem.grow (gtAdGd gStk) 0).length = rlPos .poMy1 q0 ∧
    ¬ rlGateOk .poMy1 (AxOpsem.grow (gtAdGd gStk) 0) q0 ∧
    reloadMis (gtAdGd gStk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    t2Cut (gtAdGd gStk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ entersPanic (gtAdGd gStk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ intrOnCut (gtAdGd gStk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ t2Complete (gtAdGd gStk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    allocPre (AxOpsem.grow (gtAdGd gStk) 1) q0 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    AllocPins2 (gtAdGd gStk) 1 q0 ∧ ¬ t2Cut (gtAdGd gStk) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    HimgNoff (gtAdGd gStk).gdG.gxImg 0 1 ∧
    AxOpsem.grow (gtAdGd gStk) 2 = rcRowS :=
  ⟨preAS _, npNowrapAS _, npNcollAS _, ppArmAS _,
    by unfold gStk; rw [growAS]; exact sizesS.2.2, gateAS _, misAS _, cutAS _,
    notPanicAS _, notIntrAS _, notCompleteAS _, preBS _, pinsBS _, notCutBS _, imgNoffS _,
    growCS _⟩

end AxSpinT2p3a

end Weak

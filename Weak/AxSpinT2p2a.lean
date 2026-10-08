/-
Weak: **THEOREM 2, STAGE 2 / certificate (p-lk): THE DRIVE OF HART A ON THE CUT ROW, THE
CONCRETE GRAPH AND ITS PREMISE BUNDLE** — ONE `decide +kernel` running `drive2` (the proved-sound
driver, AxScRun2: it re-runs the REAL `riscvStep` against the graph's row) on
`AxSpinT2p2.rowA2` (37 items, through holding's long arm, reading C's forged lock word and
`lk->cpu`) from the warm entry state `(.pure (), AxSpinT2pt.regsE 0)`; then `gLk` = the (p-lk)
graph at the recorded emissions (A's, the phantom B's empty one, C's hand emission) and on it
every premise the computation half supplies, with `t2Cut A` HOLDING at `.aq`.

Lean-only (no Rocq source).  Stage-2 design `notes/weak-lb-thm2-stage2.md` §C (certificate
(p-lk), here `AxSpinT2p2*`; see `AxSpinT2p2`'s header for the two-store racer deviation).  The
reductio through `allocpidOpen2` is the later capstone's.

## What this file proves

`chkA : AxSpinT2p1.chkG rows2 0 rowA2 drvA = true` (THE evaluation); `runA :
AxSpinT2p1.RunOk rows2 il2 0 (regsE 0) emsA` (read-back over a VARIABLE drive result).
`gLk := gT2 [emsA, [], emsC2]`; `catLk : rvwmoCatConsistentT gLk`, `ctrlLk : ctrlClosed gLk`
(GENERIC `graphOfSc` lemmas); `runLkA` (A's RUN premise on `gLk` from
`AxEpiRun.st (cpuOf 0) (.pure ()) (regsE 0) ibNone 0` to the row end, `.pure`, `¬ midState`);
`runLkB` (the phantom: 0 steps, row end 0); `runLkC` (C's run `⟨hp cpu rcM0 zeroRegs, 0⟩ →
⟨hp cpu hlt zeroRegs, 2⟩` in 2 `astepAnyNfGv` steps, row end 2); and the bundle **`cutCert`**:
  `allocPre (grow (gtAdGd gLk) 0) qA2 0 (sZ 0) (pEx 0)` ∧ `AllocPins2 (gtAdGd gLk) 0 qA2` ∧
  `t2Cut (gtAdGd gLk) 0 (sZ 0) (pEx 0)` ∧ `entersPanic …` ∧ `¬ t2Complete …` ∧
  (B: `allocPre (grow (gtAdGd gLk) 1) q0 1 …` ∧ `AllocPins2 … 1 q0` ∧ `¬ t2Cut … 1 …`) ∧
  `HimgNoff` ∧ `clSrcAligned (clb L) (gtAdGd gLk).gdG (0, t2KHd qA2 + 4)` (for any `L` at
  pid_lock) ∧ `grow (gtAdGd gLk) 2 = rcRow`.

## Pins / honesty
* Every proof mentioning `drvA` / `emsA` goes through `runA`.  Scope as `AxSpinT2p2`.

Reused: `AxSpinT2p1.drvG`/`chkG`/`runOfChkG`/`catOf`/`ctrlOf`, `AxSpinT2p2.*`,
`AxSpinT2c1.emsOf`/`finNotMid`.  Names: Lean-only, `Weak.AxSpinT2p2a.*`.
-/
import Weak.AxSpinT2p2

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open AxSpinT2pt AxSpinT2p2
open AxSpinT2c1 (hartOkB q0 sZ)

namespace AxSpinT2p2a

/-- Hart A's drive on its cut row. -/
noncomputable def drvA : Option (SailM Unit × RegFile × Ibch × Nat × List Eitem) :=
  AxSpinT2p1.drvG rowA2 (regsE 0)

/-- **THE DRIVE CHECK** (one kernel evaluation of `drive2`). -/
theorem chkA : AxSpinT2p1.chkG rows2 0 rowA2 drvA = true := by decide +kernel

/-- Hart A's emission. -/
noncomputable def emsA : List Eitem := AxSpinT2c1.emsOf drvA

/-- Hart A's run premise (no re-evaluation). -/
theorem runA : AxSpinT2p1.RunOk rows2 il2 0 (regsE 0) emsA :=
  AxSpinT2p1.runOfChkG rows2 il2 0 rowA2 (regsE 0) drvA growA2 rfl chkA

/-- THE CONCRETE (p-lk) GRAPH. -/
noncomputable def gLk : GdexecT := gT2 [emsA, [], emsC2]

theorem okA : hartOkB rows2 0 emsA = true := by
  obtain ⟨_, _, _, h, _⟩ := runA; exact h

/-- Consistency of the concrete graph, by the GENERIC SC lemma. -/
theorem catLk : rvwmoCatConsistentT gLk := AxSpinT2p1.catOf rows2 il2 _ _ _ shil2 okA okB2 okC2

/-- Ctrl closure of the concrete graph. -/
theorem ctrlLk : ctrlClosed gLk := AxSpinT2p1.ctrlOf rows2 il2 _ _ _ okA okB2 okC2

theorem hartsLk : ∀ e, e ∈ gLk.gtG.gxGmo → e.1 ∈ [0, 1, 2] := harts2 _

/-- A's RUN premise on the concrete graph (to the row end = the cut, an instruction boundary). -/
theorem runLkA : ∃ (u : Unit) (rs : RegFile) (ib : Ibch) (n : Nat),
    (∀ (N : Type) (nm : N), nsteps (tierAAstep (gtAdGd gLk) nm 0) n
      (AxEpiRun.st (cpuOf 0) (.pure ()) (regsE 0) ibNone 0)
      (AxEpiRun.st (cpuOf 0) (.pure u) rs ib (AxOpsem.grow (gtAdGd gLk) 0).length)) ∧
    ¬ midState (AxEpiRun.st (cpuOf 0) (.pure u) rs ib (AxOpsem.grow (gtAdGd gLk) 0).length) := by
  obtain ⟨u, rs, ib, -, H⟩ := runA
  obtain ⟨n, Hn⟩ := H [emsA, [], emsC2]
  exact ⟨u, rs, ib, n, fun N nm => Hn _ N nm, AxSpinT2c1.finNotMid _ _ _ _ _⟩

/-- The phantom B: 0 steps, its row end is 0. -/
theorem runLkB (N : Type) (nm : N) (s : Athread) (hs : s.atK = 0) :
    nsteps (tierAAstep (gtAdGd gLk) nm 1) 0 s s ∧ s.atK = (AxOpsem.grow (gtAdGd gLk) 1).length := by
  refine ⟨nsteps_O _, ?_⟩
  unfold gLk; rw [growB2, hs]; rfl

/-- C's run (`HrowC` ⇒ 2 steps, row consumed). -/
theorem runLkC (cpu : CPU) :
    nsteps (astepAnyNfGv (gtAdGd gLk) 2) 2 ⟨hp cpu rcM0 zeroRegs, 0⟩ ⟨hp cpu hlt zeroRegs, 2⟩ ∧
    (AxOpsem.grow (gtAdGd gLk) 2).length = 2 :=
  ⟨rcRun cpu _ 2 (growC2 _), by unfold gLk; rw [growC2]; rfl⟩

/-- **THE (p-lk) CERTIFICATE, premise bundle**: on the concrete graph A is a family row with its
guarded pins whose holding gate took the PANIC arm (`t2Cut` at `.aq`), the phantom B is a
(trivial) family row at no cut, the image premise holds, the racy read's sources are full-width
(Q-S2-B), and C's row is the racer's. -/
theorem cutCert (L : Xlay) (hL : L.xlLk = AxSpinT2a.zLk) :
    allocPre (AxOpsem.grow (gtAdGd gLk) 0) qA2 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    AllocPins2 (gtAdGd gLk) 0 qA2 ∧
    (AxOpsem.grow (gtAdGd gLk) 0).length = cutPos .aq qA2 ∧
    ¬ t2GateOk .aq (AxOpsem.grow (gtAdGd gLk) 0) qA2 0 ∧
    t2Cut (gtAdGd gLk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    entersPanic (gtAdGd gLk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    ¬ t2Complete (gtAdGd gLk) 0 (sZ 0) (AxSpinT2a.pEx 0) ∧
    allocPre (AxOpsem.grow (gtAdGd gLk) 1) q0 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    AllocPins2 (gtAdGd gLk) 1 q0 ∧ ¬ t2Cut (gtAdGd gLk) 1 (sZ 1) (AxSpinT2a.pEx 1) ∧
    HimgNoff (gtAdGd gLk).gdG.gxImg 0 1 ∧
    AxSpinT2g.clSrcAligned (clb L) (gtAdGd gLk).gdG (0, t2KHd qA2 + 4) ∧
    AxOpsem.grow (gtAdGd gLk) 2 = rcRow :=
  ⟨preA2 _, pinsA2 _, by unfold gLk; rw [growA2]; exact sizes2.2.2, gateA2 _, (cutA2 _).2,
    panicA2 _, notCompleteA2 _, preB2 _, pinsB2 _, notCutB2 _, imgNoff2 _, srcAl2 _ L hL,
    growC2 _⟩

end AxSpinT2p2a

end Weak

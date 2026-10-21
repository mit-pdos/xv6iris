/-
Weak: **the S-R `DomAt` lift — finding F-DomAt-1, machine-checked** (ruling [OWN.150];
`PROGRESS-DomAt.md` §0.1).  Lean-only, no Rocq twin.  A leaf: nothing imports this file.

**Spec, stated first.**  riscv.cat lets a load read an own store that is still buffered (rfi is not in
`ob`), so the store may be gmo-AFTER the load even when the load is an acquire: `[AQ];po;[M]` (rule 5) orders
only what FOLLOWS the acquire.  Graph `aqd` (bytes `A = 0`, `B = 1`, `C = 2`, image 0):
* hart 0: `s: sb A = 1`; `h: lb B` (reads `W`); `r': lr.aq A` (an `LLoad true`, reads `s`); `r: lb C` (reads 0);
* hart 1: `W: sb B = 1`;  hart 2: `n: sb C = 1`;
* gmo `r' < r < n < s < W < h` (so gmo|W = `n, s, W`).
It is RVWMO-consistent (`aqdCat`).  Under S-P (landings in GF's write order) every walk lands `s` BEFORE
`r'` steps (`aqForced`: `q s < q W < p h < p r'`, since `h` reads the foreign `W`), so `r'` reads `s` from the
log, and its `.aq` view update lifts hart 0's read view to `s`'s landing position, past `n`'s: `r` then
reads `C`'s image at NO timestamp (`aqStranded`, on the forced prefix).  Hence S-P + S-R needs the census
`SbOrdR.NoAqLd` (xv6 has no LR/SC), or S-K, or top reads for `.aq` loads (`PROGRESS-DomAt.md` §0.1).

Spec: FAITHFUL (theorems about the existing model; nothing assumed).  Lean-only helpers `SbDomLit.*`.
-/
import Weak.SpikeSR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbDomLit

def aqdProg : List (List Lbl) :=
  [[LStore false 0 [b1] .WCplain, LLoad false 1 [3] [b1], LLoad true 0 [2] [b1], LLoad false 2 [0] [b0]],
   [LStore false 1 [b1] .WCplain],
   [LStore false 2 [b1] .WCplain]]

def aqdGmo : List Geid := [(0, 2), (0, 3), (2, 0), (0, 0), (1, 0), (0, 1)]

def aqd : Gdexec := AxLitmus.mkgd aqdProg aqdGmo []

/-- **`aqd` IS RVWMO-CONSISTENT** (the faithful cat model). -/
theorem aqdCat : rvwmoCatConsistent aqd := catConsistentBSound _ (by decide +kernel)

/-- **S-P FORCES `s` TO LAND BEFORE THE ACQUIRE LOAD**: for any positions with program order, `h`'s
foreign source landed before `h`, and GF's write order, `q n < q s < p r'`. -/
theorem aqForced (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo aqd.gdG e1 e2 → p e1 < p e2)
    (hh : SBAcqP.lpos aqd.gdG p q (1, 0) < p (0, 1)) (hw : SpikeSP.CoGmoW aqd.gdG p q) :
    q (2, 0) < q (0, 0) ∧ q (0, 0) < p (0, 2) := by
  have hl : ∀ e, e = (0, 0) ∨ e = (1, 0) ∨ e = (2, 0) → SBAcqP.lpos aqd.gdG p q e = q e := by
    rintro e (rfl | rfl | rfl) <;> (unfold SBAcqP.lpos; exact if_pos (by decide +kernel))
  have a1 := hw (2, 0) (0, 0) ((glblBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((gmoLtBSpec _ _ _).1 (by decide +kernel))
  have a2 := hw (0, 0) (1, 0) ((glblBSpec _ _ _).1 (by decide +kernel))
    ((glblBSpec _ _ _).1 (by decide +kernel)) ((gmoLtBSpec _ _ _).1 (by decide +kernel))
  have a3 := hpo (0, 1) (0, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  rw [hl _ (.inr (.inr rfl)), hl _ (.inl rfl)] at a1
  rw [hl _ (.inl rfl), hl _ (.inr (.inl rfl))] at a2
  rw [hl _ (.inr (.inl rfl))] at hh
  omega

/-- The forced prefix (GF's write order `n, s, W`; `h` reads `W`; `r'` reads `s` from the log). -/
def stepsAq : List (Estep × List Nat) :=
  [(⟨2, LStore false 2 [b1] .WCplain⟩, [2]), (⟨0, LStore false 0 [b1] .WCplain⟩, [0]),
   (⟨1, LStore false 1 [b1] .WCplain⟩, [1]), (⟨0, LLoad false 1 [3] [b1]⟩, []),
   (⟨0, LLoad true 0 [2] [b1]⟩, [])]

/-- The prefix is an `SbCand` run (GF's labels verbatim). -/
theorem aqRunB : SpikeSR.runOkBS (SbCandLit.σ0 aqd.gdG.gxImg) stepsAq = true := by decide +kernel

/-- **STRANDED**: after the forced prefix, `r` reads `C`'s image `0` at no timestamp. -/
theorem aqStranded :
    ((SbCand.statesOf (SbCandLit.σ0 aqd.gdG.gxImg) stepsAq).getLast?.map (fun σ =>
      (List.range 4).all (fun t => !SpikeSR.staleRdB σ.ms.msImg σ.ms.msLog (σ.ms.msWs 0) false (σ.sb 0) 2 [t]
        [b0]))) = some true := by
  decide +kernel

end SbDomLit

end Weak

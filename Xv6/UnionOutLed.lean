/-
**THE UNION APPLICATION'S LEDGER** -- the cone-reached part of Rocq
`UnionOut.v` §6 (`/shared/xv6rocq/iris/UnionOut.v`, pinned 1900b8a43):
`FileOut.file_led`'s shape at the union's discipline, with the pipeline byte
ledger's era map beside the file's, and its conclusion `UnionOutPure.union_phi`.

* `unionPhiRes` (the conclusion's body at the era's boot states, pinned),
  `unionLed` (the ledger), `unionClAll` (the birth's yield), and
  `unionLed_phi` (the conclusion's read at the end of the run).

## DEVIATIONS from Rocq

1. **DU9: the taint counter cases on `lmDisc ulmG h` CLASSICALLY** (Rocq:
   `decide` against the constructive `UnionDecU.lm_disc_ulmG_dec`, whose
   only purpose is to keep `Classical` out of the audit; Lean's audited
   baseline already has `Classical.choice`).
2. **Scope**: the reached declarations of §6 (`union_phi_res`, `union_led`,
   `union_cl_all`, `union_led_phi`) and their `Timeless` instances.  Not
   ported (unreached from `union_adequacy_closed`): `union_era_split`,
   `union_led_init`, `union_led_pow`, `union_led_tx`, `union_led_rx`,
   `union_birth_all` -- and so none of FileOut's ledger motion lemmas they
   read (FileOutClaim deviation 1).
3. `mono_nat_auth_own γ 1 n` is `MonoNat.auth_own γ (DFrac.own 1) (.ofNat n)`
   (EchoOut deviation 5); `ghost_map_auth γ 1 ∅` is `γ ↪●MAP ∅`.  Rocq's
   section parameter `ug` is an explicit first argument (UnionOut deviation 2).
-/
import Xv6.UnionOut
import Xv6.UnionOutPure

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

set_option linter.unusedSectionVars false

section UnionOutLed
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF] [FileOutG GF] [PipeOutG GF]

/-- The conclusion's body at the era's boot states, their last pinned (Rocq
`union_phi_res`). -/
def unionPhiRes (ug : UnionGn) (h : List Obs) : IProp GF :=
  iprop(∃ s0s : List Fstate, ⌜lmDisc ulmG h → unionPhiBody h s0s⌝ ∗ f0Pinned ug.ugnFile h s0s)

instance unionPhiRes_timeless (ug : UnionGn) (h : List Obs) :
    Timeless (unionPhiRes (GF := GF) ug h) := by
  unfold unionPhiRes; infer_instance

open Classical in
/-- THE LEDGER (Rocq `union_led`): `FileOut.file_led` at the union's
discipline, the pipeline byte ledger's era map beside the file's.  The
counter cases on the discipline classically (deviation 1). -/
noncomputable def unionLed (ug : UnionGn) (h : List Obs) : IProp GF :=
  iprop(MonoNat.auth_own (fgnEcho ug.ugnFile).taint (DFrac.own 1)
      (.ofNat (if lmDisc ulmG h then 0 else 1))
    ∗ pinMap (fgnEcho ug.ugnFile) h
    ∗ f0Map ug.ugnFile h
    ∗ peraMap (ugnPipe ug) h
    ∗ flAuth ug.ugnFile.fgnCl (eflOf h)
    ∗ (unionPhiRes ug h ∨ fileTaint (hlc := hlc) ug.ugnFile.fgnCl))

instance unionLed_timeless (ug : UnionGn) (h : List Obs) :
    Timeless (unionLed (hlc := hlc) (GF := GF) ug h) := by
  unfold unionLed; infer_instance

/-- THE BIRTH'S YIELD (Rocq `union_cl_all`). -/
def unionClAll (ug : UnionGn) : IProp GF :=
  iprop(fileClAll (hlc := hlc) ug.ugnFile ∗ (ug.ugnPera ↪●MAP (∅ : RegMapF PipeEra)))

/-- THE CONCLUSION'S READ at the end of the run (Rocq `union_led_phi`). -/
theorem unionLed_phi (ug : UnionGn) (h : List Obs) :
    unionLed (hlc := hlc) (GF := GF) ug h ⊢ ⌜unionPhi h⌝ := by
  unfold unionLed
  iintro ⟨Hcnt, -, -, -, -, Hphi⟩
  icases Hphi with (Hphi | HT)
  · unfold unionPhiRes
    icases Hphi with ⟨%s0s, %hb, -⟩
    ipureintro
    exact unionPhi_of_body h s0s hb
  · unfold fileTaint echoTaint fgnEcho
    ihave %hv := MonoNat.auth_lb_own_valid _ _ _ _ $$ Hcnt HT
    ipureintro
    intro hd
    exfalso
    have hle := (MaxNat.le_toNat _ _).mp hv.2
    simp only [if_pos hd] at hle
    exact absurd hle (by decide)

end UnionOutLed

end Xv6

/-
Weak/Prom: **G4 target (5) on track (a): the NEGATIVE CHECK** (stage S4a; plan rev 7 §4 G4 (5): "two plain readers of
one release cannot both obtain an exclusive R [R1.6].  This is proved against the pre-allocated invariant, where a
reader may hold `invAt t γ_t σ_t` before t's deposit"; §3 "Frontier elimination, restated": the rule `⟦s⟧R ∗ ⌜s ≤
WF⌝ ⊢ R` for iProp R "duplicates exclusive resources … So two harts could each obtain R").

The frontier rule of track (a) gives only PERSISTENT facts (`frontA` is `Persistent`: every `t ≤ WF` is `shot`, and
`Valid(WF)`), so both readers of a release may learn `shot g t`.  The resource itself is in the pre-allocated slot
(OwnALib.lean `slotInv`), and the only way out of it is `slot_claim`, which leaves the claim token behind.  Hence:
* `slot_two_readers`: a hart that already holds the slot's exclusive `R` and a second claim token cannot coexist
  with the slot — after one claim, a second claim attempt is contradictory, whatever the order of deposit and
  reads (before the deposit the slot still holds `pend t`, which contradicts `shot t`).
* `frontA_dup`: the frontier rule's output duplicates (it is the PURE/PERSISTENT part of plan §3 only).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALib

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- The frontier rule's output is persistent: two readers may both have it. -/
theorem frontA_dup (g : AGN) (π : Proto) (img : Image) (M : List PMsg) (ws : PState) :
    frontA (GF := GF) g π img M ws ⊢ frontA g π img M ws ∗ frontA g π img M ws := by
  iintro #H
  iframe H

/-- **G4 (5)**: two readers of one release cannot both obtain an exclusive `R`: holding `R` (one claim) together
with a claim token (a second claim attempt) contradicts the slot once `t` is shot. -/
theorem slot_two_readers (g : AGN) (t : Nat) (R : IProp GF) (γc : GName) (hR : R ∗ R ⊢ False) :
    slotInv (GF := GF) g t R γc ∗ shot g t ∗ R ∗ token γc ∗ £ 1 ⊢ |={⊤}=> False := by
  iintro ⟨#Hs, #Hsh, HR, Ht, Hc⟩
  unfold slotInv
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, -⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot slotN t)) (P := iprop(pend g t ∨ (shot g t ∗ (R ∨ token γc)))))
    $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, (HR' | Ht')⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · iexfalso; iapply hR; iframe HR HR'
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- The concrete instance: `R` an exclusive token. -/
theorem slot_two_readers_tok (g : AGN) (t : Nat) (γR γc : GName) :
    slotInv (GF := GF) g t (token γR) γc ∗ shot g t ∗ token γR ∗ token γc ∗ £ 1 ⊢ |={⊤}=> False :=
  slot_two_readers g t (token γR) γc (token_exclusive γR)

end Weak.Prom.OA

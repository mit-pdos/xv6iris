/-
Weak/Prom: **deciding experiment E-a for gate G4 — track (a) WITHOUT free mode: the shared base** (stage E-a; owner
ruling [OWN.P11] "G4. Do B"; G4-review.md §1, §5 A-1, §6 condition 1; plan rev 7 §3 "Points-to, a hypothesis to
validate", R-a1, R-a5).

Every E-a verdict is proved with the DEAD SET EMPTY: the adequacy is instantiated at `Dd := fun _ => False`, so the
doom box's free mode (`dfree`, OwnAWp.lean) can never be entered, and no `deadInv` / `dead_doom` / `doomD` is used.
Instead every message's `pend` has an OWNER fixed by the BYTES IT TOUCHES (per-byte ownership from boot):
* the bytes of a lock word are owned by the LOCK PROTOCOL: its per-message slots hold the `pend`s of the messages
  touching the word; a message touching a live lock word that is not a lock operation can never be deposited, so
  its slot keeps the `pend` for good (`lkJunk`: the lock invariant owns the word; it is NEVER opened to doom —
  only a reader that sees it FULFILLED (below its frontier) uses it, `junk_shot`);
* the bytes of a data location are owned by its points-to (`pend` of every later message touching them, whatever
  its shape, author or content), which moves with ownership;
* everything else belongs to its boot owner, which never writes it (the `pend`s are simply kept and never used).
What this file provides:
* `fulT_shot` — with the dead set empty, a fulfilled message is SHOT (free mode is unreachable);
* `lkJunk`, `junk_alloc`, `junk_shot`;
* `tchB m a n` — "message `m` writes one of the bytes `a .. a+n-1`" (the per-byte owner test) and its facts;
* `bsl_peel` — the setup's partition of the `pend` family by owners.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAHold

namespace Weak.Prom.OA.E

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. Touching bytes -/

/-- Message `m` writes one of the bytes `a, …, a + n - 1`. -/
def tchB (m : PMsg) (a : Int) (n : Nat) : Bool := (List.range n).any (fun j => (m.byteAt (a + j)).isSome)

theorem tchB_of {m : PMsg} {a : Int} {n j : Nat} (hj : j < n) (h : (m.byteAt (a + j)).isSome = true) :
    tchB m a n = true :=
  List.any_eq_true.2 ⟨j, List.mem_range.2 hj, h⟩

theorem tchB_iff {m : PMsg} {a : Int} {n : Nat} :
    tchB m a n = true ↔ ∃ j, j < n ∧ (m.byteAt (a + j)).isSome = true := by
  unfold tchB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, List.mem_range.1 hj, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, List.mem_range.2 hj, h⟩

/-- A byte outside `[pa, pa + |data|)` is not written. -/
theorem byteAt_none {m : PMsg} {a : Int} (h : a < m.pa ∨ m.pa + m.data.length ≤ a) : m.byteAt a = none := by
  unfold PMsg.byteAt
  split
  · apply List.getElem?_eq_none; omega
  · rfl

/-- A message whose range is disjoint from `[a, a + n)` does not touch it. -/
theorem tchB_far {m : PMsg} {a : Int} {n : Nat} (h : m.pa + m.data.length ≤ a ∨ a + n ≤ m.pa) :
    tchB m a n = false := by
  cases hc : tchB m a n
  · rfl
  · obtain ⟨j, hj, hs⟩ := tchB_iff.1 hc
    rw [byteAt_none (by omega)] at hs; cases hs

/-- A message that touches `[a, a + n)` and lies in `[p, p + k)` covers no byte outside it. -/
theorem byteAt_in {m : PMsg} {p : Int} {k : Nat} {x : Int} (hp : m.pa = p) (hk : m.data.length = k)
    (hx : (m.byteAt x).isSome = true) : p ≤ x ∧ x < p + k := by
  refine Classical.byContradiction fun hc => ?_
  rw [byteAt_none (by rw [hp, hk]; omega)] at hx; cases hx

/-! ## 2. Free mode is unreachable; junk slots -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **WITH THE DEAD SET EMPTY, A FULFILLED MESSAGE IS SHOT**: `fulT g t = shot g t ∨ (dfree g ∗ …)`, and `dfree`
contradicts the doom box (its free branch needs a dead witness, `g.dd s`, which is `False`). -/
theorem fulT_shot (g : AGN) (M : List PMsg) (hdd : g.dd = fun _ => False) (t : Nat) :
    doomInv (GF := GF) g M ∗ fulT g t ⊢ |={⊤}=> shot g t := by
  iintro ⟨#Hdoom, #Hf⟩
  unfold fulT
  icases Hf with (#Hs | ⟨#Hfr, _⟩)
  · imodintro; iexact Hs
  unfold doomInv
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hdoom with ⟨Hb, -⟩
  icases Hb with (⟨-, Hp⟩ | ⟨-, %s, -, -, (Hp | ⟨-, %hd⟩)⟩)
  · iexfalso; iapply dfpend_dfree; iframe Hp Hfr
  · iexfalso; iapply dfpend_dfree; iframe Hp Hfr
  · rw [hdd] at hd; exact hd.elim

/-- The frontier rule at one timestamp, with the dead set empty: the message is SHOT. -/
theorem frontS (g : AGN) (M : List PMsg) (hdd : g.dd = fun _ => False) {π : Proto} {img : Image} {ws : PState}
    (t : Nat) (ht : 1 ≤ t ∧ t ≤ M.length ∧ t ≤ wfr ws) :
    doomInv (GF := GF) g M ∗ frontA g π img M ws ⊢ |={⊤}=> shot g t := by
  iintro ⟨#Hdoom, #Hfr⟩
  ihave #Hft := frontA_get t $$ Hfr %ht
  iapply fulT_shot g M hdd t
  iframe Hdoom Hft

def junkN : Namespace := ndot nroot "promJunk"

/-- **A LOCK WORD'S NON-LOCK-OPERATION MESSAGE**: the lock protocol owns the word, and such a message can never be
deposited, so its slot keeps the `pend` for good. -/
def lkJunk (g : AGN) (t : Nat) : IProp GF := inv (ndot junkN t) (pend g t)

instance (g : AGN) (t : Nat) : Persistent (lkJunk (GF := GF) g t) := by unfold lkJunk; infer_instance

theorem junk_alloc (g : AGN) (t : Nat) : pend (GF := GF) g t ⊢ |={⊤}=> lkJunk g t := by
  iintro Hp
  unfold lkJunk
  iapply inv_alloc
  inext; iexact Hp

/-- A junk message seen FULFILLED is absurd. -/
theorem junk_shot (g : AGN) (t : Nat) : lkJunk (GF := GF) g t ∗ shot g t ⊢ |={⊤}=> False := by
  iintro ⟨#Hj, #Hs⟩
  unfold lkJunk
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hj with ⟨Hp, -⟩
  iexfalso; iapply pend_shot; iframe Hp Hs

end res

/-! ## 3. Partitioning the `pend` family by owners -/

section peel

variable {GF : BundledGFunctors}

/-- Peel the elements satisfying `p` off a filtered big separating conjunction (`p` implies the remainder
predicate `r`). -/
theorem bsl_peel (F : Nat → IProp GF) (p r : Nat → Bool) (hr : ∀ t, p t = true → r t = true) (l : List Nat) :
    ([∗list] t ∈ l.filter r, F t) ⊢ ([∗list] t ∈ l.filter p, F t) ∗
      [∗list] t ∈ l.filter (fun t => r t && !p t), F t := by
  refine (bsl_filter_split F p (l.filter r)).trans ?_
  rw [filter_filter_of (r := p) (fun t => by cases hp : p t <;> cases hr' : r t <;> simp_all) l,
    filter_filter_of (r := fun t => r t && !p t) (fun t => rfl) l]

end peel

end Weak.Prom.OA.E

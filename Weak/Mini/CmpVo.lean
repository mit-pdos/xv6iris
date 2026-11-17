/-
Weak/Mini: **L4 MiniCmp — timestamps and the memory of a gmo list** (mini plan rev 4 §2 L4; Pulte et al. PLDI'19
AtoP: "promise every write in gmo order first"; `view_of_eid`).

For a list `g` (a finite execution's gmo, `MCut.g`): `voL A g e`, the number of stores of `g` up to and including
`e` (a store's timestamp; a load's "view"), and `memL A g`, the stores of `g` in order as messages.  The facts:
a store's message sits at its timestamp (`voL_mem`), every message is some store's (`memL_get`), and earlier in
`g` means a smaller-or-equal timestamp, strictly smaller before a store (`voL_lt`).
Imports: only `Weak.Mini.CmpBase` and `Weak.Mini.Mach`.  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpBase
import Weak.Mini.Mach

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

/-- 1 for a store, 0 otherwise. -/
def stc (A : MEvs) (e : EvId) : Nat := if (A.ev e).kind = .st then 1 else 0

/-- THE TIMESTAMP of `e` in the order `g` (Pulte `view_of_eid`): the number of stores of `g` up to `e`. -/
def voL (A : MEvs) : List EvId → EvId → Nat
  | [], _ => 0
  | x :: t, e => if x = e then stc A x else stc A x + voL A t e

/-- The message of store `w`: its word, at its address, by its hart. -/
def msgOf (A : MEvs) (w : EvId) : MMsg := ⟨(A.ev w).pa, (A.ev w).v, w.1⟩

/-- THE MEMORY of the order `g`: its stores, in order, as messages. -/
def memL (A : MEvs) (g : List EvId) : List MMsg :=
  (g.filter (fun x => decide ((A.ev x).kind = .st))).map (msgOf A)

variable {A : MEvs}

theorem stc_st {e : EvId} (h : (A.ev e).kind = .st) : stc A e = 1 := by simp [stc, h]

theorem stc_le : ∀ (g : List EvId) {e : EvId}, e ∈ g → stc A e ≤ voL A g e
  | [], _, h => by simp at h
  | x :: t, e, h => by
    unfold voL; split
    · rename_i hx; subst hx; exact Nat.le_refl _
    · rename_i hx
      have : e ∈ t := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      have := stc_le t this; omega

theorem posIn_cons (x : EvId) (t : List EvId) (e : EvId) :
    posIn (x :: t) e = if x = e then 0 else posIn t e + 1 := rfl

/-- Earlier in `g`: at most the timestamp, strictly less before a store. -/
theorem voL_lt : ∀ (g : List EvId) {a b : EvId}, a ∈ g → b ∈ g → posIn g a < posIn g b →
    voL A g a + stc A b ≤ voL A g b
  | [], _, _, h, _, _ => by simp at h
  | x :: t, a, b, ha, hb, hp => by
    rw [posIn_cons, posIn_cons] at hp
    have hxb : x ≠ b := by intro h; rw [if_pos h] at hp; omega
    rw [if_neg hxb] at hp
    have hb' : b ∈ t := by
      rcases List.mem_cons.1 hb with h | h
      · exact absurd h.symm hxb
      · exact h
    unfold voL
    rw [if_neg hxb]
    split
    · rename_i hxa; subst hxa; have := stc_le (A := A) t hb'; omega
    · rename_i hxa
      rw [if_neg hxa] at hp
      have ha' : a ∈ t := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hxa
        · exact h
      have := voL_lt t ha' hb' (by omega); omega

theorem memL_cons (x : EvId) (t : List EvId) :
    memL A (x :: t) = if (A.ev x).kind = .st then msgOf A x :: memL A t else memL A t := by
  unfold memL; rw [List.filter_cons]; split <;> simp_all

/-- A store's message sits at its timestamp. -/
theorem voL_mem : ∀ (g : List EvId) {e : EvId}, e ∈ g → (A.ev e).kind = .st →
    1 ≤ voL A g e ∧ (memL A g)[voL A g e - 1]? = some (msgOf A e)
  | [], _, h, _ => by simp at h
  | x :: t, e, h, hs => by
    unfold voL
    rw [memL_cons]
    split
    · rename_i hx; subst hx; rw [stc_st hs, if_pos hs]; simp
    · rename_i hx
      have he : e ∈ t := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨h1, h2⟩ := voL_mem t he hs
      split
      · rename_i hxs
        rw [stc_st hxs]
        refine ⟨by omega, ?_⟩
        rw [show 1 + voL A t e - 1 = (voL A t e - 1) + 1 by omega]
        simpa using h2
      · rename_i hxs
        have : stc A x = 0 := by simp [stc, hxs]
        rw [this, Nat.zero_add]; exact ⟨h1, h2⟩

/-- Every message is some store's, at that store's timestamp. -/
theorem memL_get : ∀ (g : List EvId), g.Nodup → ∀ {t : Nat} {m : MMsg}, (memL A g)[t]? = some m →
    ∃ w ∈ g, (A.ev w).kind = .st ∧ voL A g w = t + 1 ∧ m = msgOf A w
  | [], _, t, m, h => by simp [memL] at h
  | x :: g, hnd, t, m, h => by
    have hnd' := (List.nodup_cons.1 hnd)
    rw [memL_cons] at h
    split at h
    · rename_i hxs
      cases t with
      | zero =>
        simp at h
        exact ⟨x, List.mem_cons_self, hxs, by simp [voL, stc_st hxs], h.symm⟩
      | succ t =>
        simp at h
        obtain ⟨w, hw, h1, h2, h3⟩ := memL_get g hnd'.2 h
        have hxw : x ≠ w := fun he => hnd'.1 (he ▸ hw)
        refine ⟨w, List.mem_cons_of_mem _ hw, h1, ?_, h3⟩
        simp only [voL, if_neg hxw, stc_st hxs, h2]; omega
    · rename_i hxs
      obtain ⟨w, hw, h1, h2, h3⟩ := memL_get g hnd'.2 h
      have hxw : x ≠ w := fun he => hnd'.1 (he ▸ hw)
      refine ⟨w, List.mem_cons_of_mem _ hw, h1, ?_, h3⟩
      simp only [voL, if_neg hxw, stc, if_neg hxs, h2]; omega

end Weak.Mini.Cmp

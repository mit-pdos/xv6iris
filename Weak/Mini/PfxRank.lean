/-
Weak/Mini: **L5 MiniPfx — gmo is a ranking; finite gmo lists satisfy progress** (mini plan rev 4 §2 L5: "finite by
progress").

From `gmoOk` and the PROGRESS AXIOM (rvwmo.adoc:350–351 "No memory operation may be preceded in the global memory
order by an infinite sequence of other memory operations", Ref.lean `progressAx`):
* `preds_finite` — every memory operation has finitely many gmo-predecessors (else an injective sequence of them);
* `rk e` — their number; on memory operations `gmo a b ↔ rk a < rk b` (`gmo_iff_rk`);
* `progress_of_list` — a gmo that only relates elements of a finite list satisfies progress (the cut's side).
Transcribed from Weak/Prom/PfxRank.lean (not imported).  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpVo

namespace Weak.Mini.Pfx

open Weak.Mini Weak.Mini.Cmp

theorem nodup_length_le : ∀ (l L : List EvId), l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, L, hn, hs => by
    have ha : a ∈ L := hs a List.mem_cons_self
    have hnt : t.Nodup := (List.nodup_cons.1 hn).2
    have hat : a ∉ t := (List.nodup_cons.1 hn).1
    have hsub : ∀ x ∈ t, x ∈ L.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hat (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs x (List.mem_cons_of_mem _ hx))
    have := nodup_length_le t (L.erase a) hnt hsub
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < L.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Duplicate-free copy of a list. -/
def ndL : List EvId → List EvId
  | [] => []
  | a :: t => if a ∈ ndL t then ndL t else a :: ndL t

theorem mem_ndL : ∀ (l : List EvId) (a : EvId), a ∈ ndL l ↔ a ∈ l
  | [], a => by simp [ndL]
  | b :: t, a => by
    unfold ndL
    split
    · rename_i hb
      rw [mem_ndL t a, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact (mem_ndL t a).1 hb
        · exact h
    · rw [List.mem_cons, mem_ndL t a, List.mem_cons]

theorem nodup_ndL : ∀ (l : List EvId), (ndL l).Nodup
  | [] => List.nodup_nil
  | b :: t => by
    unfold ndL
    split
    · exact nodup_ndL t
    · rename_i hb
      exact List.nodup_cons.2 ⟨hb, nodup_ndL t⟩

/-- A gmo relating only elements of a finite list satisfies the progress axiom. -/
theorem progress_of_list {A : MEvs} (g : List EvId) (hg : ∀ a b, A.gmo a b → a ∈ g) : A.progressAx := by
  intro e _ ⟨f, hinj, hb⟩
  let l := (List.range (g.length + 1)).map f
  have hnd : l.Nodup :=
    List.pairwise_map.2 (List.nodup_range.imp (fun h1 h2 => h1 (hinj _ _ h2)))
  have hsub : ∀ x ∈ l, x ∈ g := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx
    exact hg _ _ (hb n)
  have := nodup_length_le l g hnd hsub
  simp [l] at this; omega

open Classical in
/-- Every memory operation has finitely many gmo-predecessors (the progress axiom). -/
theorem preds_finite {A : MEvs} (hp : A.progressAx) {e : EvId} (he : A.isMem e) :
    ∃ L : List EvId, ∀ a, A.gmo a e → a ∈ L := by
  apply Classical.byContradiction
  intro hne
  have H : ∀ L : List EvId, ∃ a, A.gmo a e ∧ a ∉ L := by
    intro L
    apply Classical.byContradiction
    intro h2
    apply hne
    refine ⟨L, fun a ha => ?_⟩
    apply Classical.byContradiction
    intro h3
    exact h2 ⟨a, ha, h3⟩
  let g : Nat → List EvId := fun n => Nat.rec [] (fun _ l => l ++ [Classical.choose (H l)]) n
  let f : Nat → EvId := fun n => Classical.choose (H (g n))
  have hgs : ∀ n, g (n + 1) = g n ++ [f n] := fun n => rfl
  have hg : ∀ n m, m < n → f m ∈ g n := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rw [hgs]
      rcases Nat.lt_or_ge m n with h1 | h1
      · exact List.mem_append_left _ (ih m h1)
      · have : m = n := by omega
        subst this
        exact List.mem_append_right _ (List.mem_singleton_self _)
  have hnot : ∀ n, f n ∉ g n := fun n => (Classical.choose_spec (H (g n))).2
  refine hp e he ⟨f, fun n m hnm => ?_, fun n => (Classical.choose_spec (H (g n))).1⟩
  rcases Nat.lt_trichotomy n m with h1 | h1 | h1
  · exact absurd (hnm ▸ hg m n h1) (hnot m)
  · exact h1
  · exact absurd (hnm.symm ▸ hg n m h1) (hnot n)

open Classical in
/-- The gmo-predecessors of `e` (duplicate-free; empty without a finite superset). -/
noncomputable def preds (A : MEvs) (e : EvId) : List EvId :=
  if h : ∃ L : List EvId, ∀ a, A.gmo a e → a ∈ L then (ndL (Classical.choose h)).filter (fun a => decide (A.gmo a e))
  else []

open Classical in
theorem mem_preds {A : MEvs} (hp : A.progressAx) {e : EvId} (he : A.isMem e) (a : EvId) :
    a ∈ preds A e ↔ A.gmo a e := by
  have h := preds_finite hp he
  unfold preds
  rw [dif_pos h, List.mem_filter, mem_ndL, decide_eq_true_eq]
  exact ⟨fun h1 => h1.2, fun h1 => ⟨Classical.choose_spec h a h1, h1⟩⟩

theorem nodup_preds (A : MEvs) (e : EvId) : (preds A e).Nodup := by
  unfold preds
  split
  · exact (nodup_ndL _).filter _
  · exact List.nodup_nil

/-- THE RANK of a memory operation: its number of gmo-predecessors. -/
noncomputable def rk (A : MEvs) (e : EvId) : Nat := (preds A e).length

section

variable {A : MEvs} (hg : A.gmoOk) (hp : A.progressAx)
include hg hp

theorem rk_lt {a b : EvId} (h : A.gmo a b) : rk A a < rk A b := by
  obtain ⟨ha, hb⟩ := hg.1 a b h
  have hnd : (a :: preds A a).Nodup :=
    List.nodup_cons.2 ⟨fun hm => MEvsF.gmo_irr hg a ((mem_preds hp ha a).1 hm), nodup_preds A a⟩
  have hsub : ∀ x ∈ a :: preds A a, x ∈ preds A b := by
    intro x hx
    rw [mem_preds hp hb]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h
    · exact MEvsF.gmo_trans hg ((mem_preds hp ha x).1 hx) h
  have := nodup_length_le _ _ hnd hsub
  simp only [List.length_cons] at this
  unfold rk; omega

/-- On memory operations, gmo IS the rank order. -/
theorem gmo_iff_rk {a b : EvId} (ha : A.isMem a) (hb : A.isMem b) : A.gmo a b ↔ rk A a < rk A b := by
  refine ⟨rk_lt hg hp, fun h => ?_⟩
  by_cases hab : a = b
  · subst hab; omega
  · rcases MEvsF.gmo_total hg ha hb hab with h1 | h1
    · exact h1
    · have := rk_lt hg hp h1; omega

theorem rk_inj {a b : EvId} (ha : A.isMem a) (hb : A.isMem b) (h : rk A a = rk A b) : a = b := by
  apply Classical.byContradiction
  intro hab
  rcases MEvsF.gmo_total hg ha hb hab with h1 | h1
  · have := rk_lt hg hp h1; omega
  · have := rk_lt hg hp h1; omega

end

/-- Strictly sorted lists: position order is key order. -/
theorem posIn_lt_iff (f : EvId → Nat) : ∀ (g : List EvId), g.Pairwise (fun x y => f x < f y) → ∀ {a b : EvId},
    a ∈ g → b ∈ g → (posIn g a < posIn g b ↔ f a < f b)
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | x :: t, hp, a, b, ha, hb => by
    have hp' := List.pairwise_cons.1 hp
    rw [posIn_cons, posIn_cons]
    by_cases hxa : x = a
    · subst hxa
      by_cases hxb : x = b
      · subst hxb; simp
      · rw [if_pos rfl, if_neg hxb]
        have hbt : b ∈ t := by rcases List.mem_cons.1 hb with h | h; exact absurd h.symm hxb; exact h
        have := hp'.1 b hbt; constructor <;> intro <;> omega
    · rw [if_neg hxa]
      have hat : a ∈ t := by rcases List.mem_cons.1 ha with h | h; exact absurd h.symm hxa; exact h
      by_cases hxb : x = b
      · subst hxb
        rw [if_pos rfl]
        have := hp'.1 a hat; constructor <;> intro <;> omega
      · rw [if_neg hxb]
        have hbt : b ∈ t := by rcases List.mem_cons.1 hb with h | h; exact absurd h.symm hxb; exact h
        rw [← posIn_lt_iff f t hp'.2 hat hbt]; omega

end Weak.Mini.Pfx

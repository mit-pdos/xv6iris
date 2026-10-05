/-
**The quota table's geometry** (NI M3 quotas Q-1; design "M3 quotas" F4,
the "five-interior-page lemma").

`PTree.shapeQ` (`UPtDefs`) confines a table's interior pages to two paths:
the user region's (root index 0, then 0: every vpn below 512, so every user
page below the quota `uQuota` = 768 KiB ≤ 2 MiB) and the top pages' (root
index 255, then 511: `TRAMPOLINE` and `TRAPFRAME`).  So a quota table has
at most `ptNodesMax` = 5 interior pages (`pages_le_of_shapeQ`), and a walk
to a quota vpn (`vpnQ`) keeps the shape (`shapeQ_fill`, `shapeQ_setLeaf`).
With `uLeafRegion` (every user leaf below `uQpages`) the user leaves are at
most `uQpages` (`uLeafCnt_le`), so a table's weight `ptW = ptNodesMax +
uQpages` covers every page it may ever own.

Imports only definitional files.
-/
import Xv6.UPtDefs

namespace Xv6

open MachCSL Iris.Std

/-! ## Counting a flatMap with few live indices -/

theorem sum_map_eq_zero {α : Type} (l : List α) (g : α → Nat) (h : ∀ x ∈ l, g x = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem sum_map_le_one {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup) (g : α → Nat) (b : α)
    (hg : ∀ x ∈ l, x ≠ b → g x = 0) : (l.map g).sum ≤ g b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = b
    · subst hx
      rw [sum_map_eq_zero l g (fun y hy => hg y (List.mem_cons_of_mem _ hy)
        (fun e => hnd.1 (e ▸ hy)))]
      omega
    · rw [hg x (List.mem_cons_self) hx]
      have := ih hnd.2 (fun y hy => hg y (List.mem_cons_of_mem _ hy))
      omega

theorem sum_map_le_two {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup) (g : α → Nat) (a b : α)
    (hg : ∀ x ∈ l, x ≠ a → x ≠ b → g x = 0) : (l.map g).sum ≤ g a + g b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      have := sum_map_le_one l hnd.2 g b (fun y hy hyb => hg y (List.mem_cons_of_mem _ hy)
        (fun e => hnd.1 (e ▸ hy)) hyb)
      omega
    · by_cases hxb : x = b
      · subst hxb
        have := sum_map_le_one l hnd.2 g a (fun y hy hya => hg y (List.mem_cons_of_mem _ hy) hya
          (fun e => hnd.1 (e ▸ hy)))
        omega
      · rw [hg x (List.mem_cons_self) hxa hxb]
        have := ih hnd.2 (fun y hy => hg y (List.mem_cons_of_mem _ hy))
        omega

/-! ## The five interior pages -/

theorem PTree.pages_succ (lvl : Nat) (t : PTree) :
    t.pages (lvl + 1) = t.base :: allIdx.flatMap (fun i => match t.kids i with
      | some c => c.pages lvl | none => []) := rfl

/-- A level-1 node with children at one index only: two pages at most. -/
theorem PTree.pages_one_le (c : PTree) (j : BitVec 9) (h : ∀ i, (c.kids i).isSome → i = j) :
    (c.pages 1).length ≤ 2 := by
  rw [PTree.pages_succ, List.length_cons, List.length_flatMap]
  have hle := sum_map_le_one allIdx allIdx_nodup
    (fun i => (match c.kids i with | some g => g.pages 0 | none => [] : List (BitVec 44)).length) j
    (by
      intro x _ hx
      cases hk : c.kids x with
      | none => simp only [List.length_nil]
      | some g => exact absurd (h x (by rw [hk]; rfl)) hx)
  have hj : ((match c.kids j with | some g => g.pages 0 | none => []) : List (BitVec 44)).length ≤ 1 := by
    cases c.kids j <;> simp [PTree.pages]
  omega

/-- **THE FIVE-INTERIOR-PAGE LEMMA** (design F4): a quota table owns at
most `ptNodesMax` = 5 interior pages -- the root, two level-1 nodes and two
level-0 nodes. -/
theorem PTree.pages_le_of_shapeQ (t : PTree) (h : t.shapeQ) : (t.pages 2).length ≤ ptNodesMax := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [PTree.pages_succ, List.length_cons, List.length_flatMap]
  have hle := sum_map_le_two allIdx allIdx_nodup
    (fun i => (match t.kids i with | some c => c.pages 1 | none => [] : List (BitVec 44)).length) 0#9 255#9
    (by
      intro x _ hx0 hx1
      cases hk : t.kids x with
      | none => simp only [List.length_nil]
      | some c =>
        rcases h0 x (by rw [hk]; rfl) with e | e
        · exact absurd e hx0
        · exact absurd e hx1)
  have hA : ((match t.kids 0#9 with | some c => c.pages 1 | none => []) : List (BitVec 44)).length ≤ 2 := by
    cases hk : t.kids 0#9 with
    | none => simp
    | some c => exact PTree.pages_one_le c 0#9 (h1 c hk)
  have hB : ((match t.kids 255#9 with | some c => c.pages 1 | none => []) : List (BitVec 44)).length ≤ 2 := by
    cases hk : t.kids 255#9 with
    | none => simp
    | some c => exact PTree.pages_one_le c 511#9 (h2 c hk)
  unfold ptNodesMax
  omega

/-! ## The shape is kept -/

theorem PTree.kids_setKid (t c : PTree) (i j : BitVec 9) :
    (t.setKid i c).kids j = if j = i then some c else t.kids j := rfl

theorem PTree.kids_setEnt (t : PTree) (i : BitVec 9) (v : BitVec 64) :
    (t.setEnt i v).kids = t.kids := rfl

theorem PTree.shapeQ_zeroNode (b : BitVec 44) : (PTree.zeroNode b).shapeQ :=
  ⟨fun _ h => by simp [PTree.zeroNode] at h, fun _ h => by simp [PTree.zeroNode] at h,
    fun _ h => by simp [PTree.zeroNode] at h⟩

/-- The user region's path: root index 0, then 0. -/
theorem vpnIdx_user (vpn : BitVec 27) (h : vpn.toNat < uQpages) :
    vpnIdx vpn 2 = 0#9 ∧ vpnIdx vpn 1 = 0#9 := by
  have h' : vpn.toNat < 512 := by unfold uQpages at h; omega
  have hlt : vpn < 512#27 := by
    rw [BitVec.lt_def]; simpa using h'
  unfold vpnIdx
  constructor <;> (revert hlt; bv_decide)

/-- The top pages' path: root index 255, then 511. -/
theorem vpnIdx_top (vpn : BitVec 27) (h : vpn = tfVpn ∨ vpn = trampVpn) :
    vpnIdx vpn 2 = 255#9 ∧ vpnIdx vpn 1 = 511#9 := by
  rcases h with rfl | rfl <;> decide

/-- A quota vpn's path is one of the two. -/
theorem vpnIdx_q (vpn : BitVec 27) (h : vpnQ vpn) :
    (vpnIdx vpn 2 = 0#9 ∧ vpnIdx vpn 1 = 0#9) ∨ (vpnIdx vpn 2 = 255#9 ∧ vpnIdx vpn 1 = 511#9) := by
  rcases h with h | h
  · exact Or.inl (vpnIdx_user vpn h)
  · exact Or.inr (vpnIdx_top vpn h)

/-- The level-1 node a walk fills keeps its one live index. -/
theorem PTree.kids_fill_one (c : PTree) (vpn : BitVec 27) (fr : List (BitVec 44)) (j : BitVec 9)
    (hj : vpnIdx vpn 1 = j) (hc : ∀ i, (c.kids i).isSome → i = j) :
    ∀ i, ((c.fill 1 vpn fr).1.kids i).isSome → i = j := by
  intro i hi
  simp only [PTree.fill] at hi
  cases hk : c.kids (vpnIdx vpn 1) with
  | some g =>
    rw [hk] at hi
    simp only [PTree.kids_setKid] at hi
    split at hi
    · rename_i h; rw [h, hj]
    · exact hc i hi
  | none =>
    rw [hk] at hi
    cases fr with
    | nil => exact hc i hi
    | cons b fr' =>
      simp only [PTree.kids_setKid, PTree.kids_setEnt] at hi
      split at hi
      · rename_i h; rw [h, hj]
      · exact hc i hi

/-- A fresh level-1 node filled for a quota vpn has its one live index. -/
theorem PTree.kids_fill_zero_one (b : BitVec 44) (vpn : BitVec 27) (fr : List (BitVec 44)) (j : BitVec 9)
    (hj : vpnIdx vpn 1 = j) :
    ∀ i, (((PTree.zeroNode b).fill 1 vpn fr).1.kids i).isSome → i = j :=
  PTree.kids_fill_one _ vpn fr j hj (fun i h => by simp [PTree.zeroNode] at h)

/-- **A walk to a quota vpn keeps the quota shape.** -/
theorem PTree.shapeQ_fill (t : PTree) (vpn : BitVec 27) (fr : List (BitVec 44))
    (hv : vpnQ vpn) (hs : t.shapeQ) : (t.fill 2 vpn fr).1.shapeQ := by
  obtain ⟨h0, h1, h2⟩ := hs
  have hidx := vpnIdx_q vpn hv
  -- the root's kid at `vpnIdx vpn 2` is the only one that changes
  have key : ∀ (c' : PTree), (∀ i, (c'.kids i).isSome →
        i = (if vpnIdx vpn 2 = 0#9 then 0#9 else 511#9)) →
      (t.setKid (vpnIdx vpn 2) c').shapeQ ∧
      ∀ w : BitVec 64, ((t.setEnt (vpnIdx vpn 2) w).setKid (vpnIdx vpn 2) c').shapeQ := by
    intro c' hc'
    have hgoal : ∀ (u : PTree), u.kids = t.kids → (u.setKid (vpnIdx vpn 2) c').shapeQ := by
      intro u hu
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [PTree.kids_setKid] at hi
        split at hi
        · rename_i h; rw [h]; rcases hidx with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> simp
        · rw [hu] at hi; exact h0 i hi
      · intro c hc i hi
        rw [PTree.kids_setKid] at hc
        split at hc
        · rename_i h
          cases hc
          have := hc' i hi
          rw [if_pos h.symm] at this; exact this
        · rw [hu] at hc; exact h1 c hc i hi
      · intro c hc i hi
        rw [PTree.kids_setKid] at hc
        split at hc
        · rename_i h
          cases hc
          have := hc' i hi
          rcases hidx with ⟨e, -⟩ | ⟨e, -⟩
          · rw [← h] at e; exact absurd e (by decide)
          · rw [if_neg (by rw [← h]; decide)] at this; exact this
        · rw [hu] at hc; exact h2 c hc i hi
    exact ⟨hgoal t rfl, fun w => hgoal _ rfl⟩
  have hj : vpnIdx vpn 1 = (if vpnIdx vpn 2 = 0#9 then 0#9 else 511#9) := by
    rcases hidx with ⟨e2, e1⟩ | ⟨e2, e1⟩
    · rw [if_pos e2, e1]
    · rw [if_neg (by rw [e2]; decide), e1]
  simp only [PTree.fill]
  cases hk : t.kids (vpnIdx vpn 2) with
  | some c =>
    simp only
    refine (key _ ?_).1
    refine PTree.kids_fill_one c vpn fr _ hj ?_
    intro i hi
    rcases hidx with ⟨e2, e1⟩ | ⟨e2, e1⟩
    · rw [if_pos e2]; rw [e2] at hk; exact h1 c hk i hi
    · rw [if_neg (by rw [e2]; decide)]; rw [e2] at hk; exact h2 c hk i hi
  | none =>
    cases fr with
    | nil => exact ⟨h0, h1, h2⟩
    | cons b fr' =>
      simp only
      exact (key ((PTree.zeroNode b).fill 1 vpn fr').1 (PTree.kids_fill_zero_one b vpn fr' _ hj)).2 _

/-- Writing a leaf keeps the shape (no child moves). -/
theorem PTree.shapeQ_setLeaf (t : PTree) (vpn : BitVec 27) (v : BitVec 64) (hs : t.shapeQ) :
    (t.setLeaf 2 vpn v).shapeQ := by
  obtain ⟨h0, h1, h2⟩ := hs
  -- a level-1 node keeps its kids' pattern
  have one : ∀ c : PTree, ∀ i, ((c.setLeaf 1 vpn v).kids i).isSome → (c.kids i).isSome := by
    intro c i hi
    simp only [PTree.setLeaf] at hi
    cases hk : c.kids (vpnIdx vpn 1) with
    | some g =>
      rw [hk] at hi
      simp only [PTree.kids_setKid] at hi
      split at hi
      · rename_i h; rw [h, hk]; rfl
      · exact hi
    | none => rw [hk] at hi; exact hi
  simp only [PTree.setLeaf]
  cases hk : t.kids (vpnIdx vpn 2) with
  | none => exact ⟨h0, h1, h2⟩
  | some c =>
    simp only
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [PTree.kids_setKid] at hi
      split at hi
      · rename_i h; rw [← h] at hk; exact h0 i (by rw [hk]; rfl)
      · exact h0 i hi
    · intro c' hc' i hi
      rw [PTree.kids_setKid] at hc'
      split at hc'
      · rename_i h
        cases hc'
        rw [← h] at hk
        exact h1 c hk i (one c i hi)
      · exact h1 c' hc' i hi
    · intro c' hc' i hi
      rw [PTree.kids_setKid] at hc'
      split at hc'
      · rename_i h
        cases hc'
        rw [← h] at hk
        exact h2 c hk i (one c i hi)
      · exact h2 c' hc' i hi

/-! ## The user leaves -/

/-- At most `uQpages` user leaves. -/
theorem uLeafCnt_le (L : RegMapF (BitVec 64)) : uLeafCnt L ≤ uQpages := by
  unfold uLeafCnt
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- **The weight is exact**: a quota table's pages and user leaves fit its
weight, so its credits are the weight's unspent part. -/
theorem ptW_fits (t : PTree) (L : RegMapF (BitVec 64)) (h : t.shapeQ) :
    (t.pages 2).length + uLeafCnt L ≤ ptW := by
  have := PTree.pages_le_of_shapeQ t h
  have := uLeafCnt_le L
  unfold ptW; omega

/-! ## Counting the user leaves across a change -/

theorem filter_length_congr (l : List Nat) (p q : Nat → Bool) (h : ∀ x ∈ l, p x = q x) :
    (l.filter p).length = (l.filter q).length := by
  rw [List.filter_congr h]

theorem filter_length_flip (l : List Nat) (hnd : l.Nodup) (p q : Nat → Bool) (k : Nat) (hk : k ∈ l)
    (hpq : ∀ x ∈ l, x ≠ k → p x = q x) (hp : p k = false) (hq : q k = true) :
    (l.filter q).length = (l.filter p).length + 1 := by
  induction l with
  | nil => exact absurd hk List.not_mem_nil
  | cons x l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    by_cases hx : x = k
    · subst hx
      rw [hp, hq]
      simp only [if_true, Bool.false_eq_true, if_false, List.length_cons]
      rw [filter_length_congr l q p (fun y hy => (hpq y (List.mem_cons_of_mem _ hy)
        (fun e => hnd.1 (e ▸ hy))).symm)]
    · have hk' : k ∈ l := by
        rcases List.mem_cons.mp hk with e | e
        · exact absurd e.symm hx
        · exact e
      rw [hpq x List.mem_cons_self hx]
      have := ih hnd.2 hk' (fun y hy hyk => hpq y (List.mem_cons_of_mem _ hy) hyk)
      cases q x <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

/-- Two leaf maps with the same user keys have the same user leaves. -/
theorem uLeafCnt_congr (L L' : RegMapF (BitVec 64))
    (h : ∀ k, k < uQpages → (get? L k).isSome = (get? L' k).isSome) :
    uLeafCnt L = uLeafCnt L' := by
  unfold uLeafCnt
  exact filter_length_congr _ _ _ (fun x hx => h x (List.mem_range.mp hx))

/-- A new user leaf counts one more. -/
theorem uLeafCnt_insert_new (L : RegMapF (BitVec 64)) (k : Nat) (w : BitVec 64)
    (hk : k < uQpages) (hn : get? L k = none) :
    uLeafCnt (insert L k w) = uLeafCnt L + 1 := by
  unfold uLeafCnt
  refine filter_length_flip _ List.nodup_range _ _ k (List.mem_range.mpr hk) ?_ (by simp [hn])
    (by simp [get?_insert_eq rfl])
  intro x _ hx
  rw [get?_insert_ne (fun h => hx h.symm)]

/-- A leaf replaced, or above the quota, counts nothing new. -/
theorem uLeafCnt_insert_same (L : RegMapF (BitVec 64)) (k : Nat) (w : BitVec 64)
    (hk : uQpages ≤ k ∨ (get? L k).isSome) :
    uLeafCnt (insert L k w) = uLeafCnt L := by
  apply uLeafCnt_congr
  intro x hx
  by_cases e : x = k
  · subst e
    rcases hk with hk | hk
    · omega
    · rw [get?_insert_eq rfl, hk]; rfl
  · rw [get?_insert_ne (fun h => e h.symm)]

/-- A user leaf removed counts one less. -/
theorem uLeafCnt_delete (L : RegMapF (BitVec 64)) (k : Nat)
    (hk : k < uQpages) (hs : (get? L k).isSome) :
    uLeafCnt (delete L k) + 1 = uLeafCnt L := by
  unfold uLeafCnt
  refine (filter_length_flip _ List.nodup_range _ _ k (List.mem_range.mpr hk) ?_ (by simp [get?_delete_eq rfl])
    hs).symm
  intro x _ hx
  rw [get?_delete_ne (fun h => hx h.symm)]

/-- Removing a non-user key counts nothing. -/
theorem uLeafCnt_delete_same (L : RegMapF (BitVec 64)) (k : Nat)
    (hk : uQpages ≤ k ∨ get? L k = none) :
    uLeafCnt (delete L k) = uLeafCnt L := by
  apply uLeafCnt_congr
  intro x hx
  by_cases e : x = k
  · subst e
    rcases hk with hk | hk
    · omega
    · rw [get?_delete_eq rfl, hk]
  · rw [get?_delete_ne (fun h => e h.symm)]

theorem uLeafRegion_insert (L : RegMapF (BitVec 64)) (k : Nat) (w : BitVec 64) (h : uLeafRegion L)
    (hk : k < uQpages ∨ k = tfVpn.toNat ∨ k = trampVpn.toNat) : uLeafRegion (insert L k w) := by
  intro x v hx
  by_cases e : x = k
  · subst e; exact hk
  · rw [get?_insert_ne (fun h => e h.symm)] at hx; exact h x v hx

theorem uLeafRegion_delete (L : RegMapF (BitVec 64)) (k : Nat) (h : uLeafRegion L) :
    uLeafRegion (delete L k) := by
  intro x v hx
  by_cases e : x = k
  · subst e; rw [get?_delete_eq rfl] at hx; cases hx
  · rw [get?_delete_ne (fun h => e h.symm)] at hx; exact h x v hx

end Xv6

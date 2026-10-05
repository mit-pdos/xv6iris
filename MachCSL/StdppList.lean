/-
MachCSL: **THE STDPP LIST SHIM** -- the stdpp list lemmas the weak-memory
port uses, under their stdpp names, stated over Lean's `List` (gap note
`notes/weak-port-iris-gaps.md`, §1d "list lemmas" and §G3 "List shim").

Every lemma of stdpp's `list.v` / `list_numbers.v` / `sorting.v` that the
Rocq weak files (`Weak*.v`, `Ax*.v`, `Wk*.v` at `../xv6iris-spinlock/iris`,
comments stripped) mention is here, under its stdpp name in the namespace
`MachCSL.Stdpp` (`open MachCSL.Stdpp` to use them unqualified; with `open
List` as well, qualify the few that also exist in core, e.g. `take_drop`).
Most are one-line restatements of a core/Batteries lemma; the table says
which.  The statements keep stdpp's SHAPE (argument order, conjunct order,
direction) over the Lean vocabulary below, and their data arguments are
implicit (stdpp's are explicit; Lean code writes `lookup_lt_Some h`).

**Vocabulary** (stdpp → Lean):

| stdpp | Lean |
|---|---|
| `l !! i` | `l[i]?` |
| `l !!! i` (`Inhabited`) | `l[i]!` |
| `<[i:=x]> l` | `l.set i x` |
| `f <$> l`, `omap f l`, `imap f l` | `l.map f`, `l.filterMap f`, `l.mapIdx f` |
| `mjoin ls`, `l ≫= f` | `ls.flatten`, `l.flatMap f` |
| `seq j n`, `seqZ m n` | `List.range' j n`, `MachCSL.Stdpp.seqZ m n` |
| `zip_with f l k`, `l.*1` / `l.*2` | `List.zipWith f l k`, `l.map Prod.fst` / `l.map Prod.snd` |
| `last l` | `l.getLast?` |
| `list_find P l` | `MachCSL.Stdpp.listFind p l` |
| `remove_dups l` | `MachCSL.Stdpp.removeDups l` (stdpp's: keeps LAST occurrences) |
| `sum_list_with f l`, `sum_list l` | `MachCSL.Stdpp.sumListWith f l` (`= (l.map f).sum`), `l.sum` |
| `mapM f l` (option) | `l.mapM f` |
| `option_list o`, `reverse l`, `replicate n x`, `foldl` | `o.toList`, `l.reverse`, `List.replicate n x`, `List.foldl` |
| `filter P l` (`P` with `Decision`) | `l.filter p`, `p : α → Bool`; `P x` ↦ `p x = true`, `¬P x` ↦ `p x = false` |
| `is_Some o` | `o.isSome` |
| `Forall P l`, `Exists P l` | `∀ x ∈ l, P x`, `∃ x ∈ l, P x` |
| `Forall2 P l k` | `List.Forall₂ P l k` (Batteries) |
| `NoDup l` | `l.Nodup` |
| `l ≡ₚ k`, `l ⊆+ k`, `l ⊆ k` | `List.Perm l k`, `List.Subperm l k` (Batteries), `l ⊆ k` |
| `l1 `prefix_of` l2` | `List.IsPrefix l1 l2` (`<+:`) |
| `Sorted R l`, `StronglySorted R l` | `List.IsChain R l` (Batteries), `List.Pairwise R l` |
| `merge_sort R l` | `List.mergeSort l le`, `le : α → α → Bool` |
| `pred n`, `S n` | `n - 1`, `n + 1` |

**Name map** (stdpp name → the core/Batteries fact it restates; "proof"
means a short proof here):

| stdpp | Lean | stdpp | Lean |
|---|---|---|---|
| `lookup_lt_Some` | `List.getElem?_eq_some_iff` | `elem_of_cons` | `List.mem_cons` |
| `elem_of_nil`, `not_elem_of_nil` | `List.not_mem_nil` | `elem_of_list_singleton` | `List.mem_singleton` |
| `elem_of_app` | `List.mem_append` | `elem_of_list_lookup(_1/_2)` | `List.mem_iff_getElem?` |
| `list_lookup_fmap` | `List.getElem?_map` | `length_fmap` | `List.length_map` |
| `lookup_lt_is_Some(_1/_2)` | `List.isSome_getElem?` | `length_app` | `List.length_append` |
| `elem_of_list_filter` | `List.mem_filter` | `lookup_app_l(_Some)` | `List.getElem?_append_left` |
| `lookup_app_r` | `List.getElem?_append_right` | `lookup_app_Some` | `List.getElem?_append` |
| `elem_of_seq` | `List.mem_range'_1` | `elem_of_list_fmap(_1)` | `List.mem_map` |
| `lookup_nil` | `List.getElem?_nil` | `list_lookup_insert` | `List.getElem?_set_self` |
| `list_lookup_insert_ne` | `List.getElem?_set_ne` | `lookup_ge_None(_1/_2)` | `List.getElem?_eq_none_iff` |
| `length_replicate` | `List.length_replicate` | `list_eq` | `List.ext_getElem?` |
| `length_seq` | `List.length_range'` | `Forall_forall`, `Exists_exists` | `Iff.rfl` |
| `elem_of_take`, `lookup_take(_Some/_ge)` | `List.getElem?_take` | `take_ge` | `List.take_of_length_le` |
| `NoDup_singleton` | `List.nodup_cons` | `fmap_app` | `List.map_append` |
| `list_insert_insert` | `List.set_set` | `NoDup_lookup`, `NoDup_alt` | proof |
| `NoDup_cons(_1_1/_1_2)` | `List.nodup_cons` | `NoDup_app` | `List.nodup_append` |
| `lookup_seq(_lt/_ge)` | `List.getElem?_range'` | `take_S_r` | `List.take_succ` |
| `filter_app` | `List.filter_append` | `filter_cons(_True/_False)` | `List.filter_cons(_of_pos/_of_neg)` |
| `fmap_cons`, `fmap_nil` | `List.map_cons`, `List.map_nil` | `length_take(_le)` | `List.length_take(_of_le)` |
| `list_fmap_ext` | `List.map_congr_left` | `take_drop` | `List.take_append_drop` |
| `Forall_singleton/_app/_nil/_cons(_1/_2)/_nil_2` | `List.forall_mem_cons`, `List.forall_mem_append` | `Forall_lookup(_1/_2)` | `List.mem_iff_getElem?` |
| `last_Some` | `List.getLast?_eq_some_iff` | `last_snoc` | `List.getLast?_concat` |
| `last_None`, `last_is_Some` | `List.getLast?_eq_none_iff`, `List.getLast?_isSome` | `last_lookup` | `List.getLast?_eq_getElem?` |
| `last_Some_elem_of` | `List.mem_of_getLast?` | `fmap_last` | `List.getLast?_map` |
| `last_filter_Some` | proof | `list_lookup_total_correct/_alt/_lookup_total_lt/_total_fmap` | `List.getElem!_eq_getElem?_getD` |
| `list_find(_Some/_None/_elem_of/_app_l)` | proof | `NoDup_filter` | `List.Nodup.sublist`, `List.filter_sublist` |
| `lookup_zip_with(_Some)` | `List.getElem?_zipWith(_eq_some)` | `filter_nil` | `List.filter_nil` |
| `take_0`, `drop_0`, `take_nil` | `List.take_zero`, `List.drop_zero`, `List.take_nil` | `list_lookup_imap` | `List.getElem?_mapIdx` |
| `list_fmap_compose` | `List.map_map` | `length_insert` | `List.length_set` |
| `NoDup_Permutation` | `List.perm_ext_iff_of_nodup` | `list_lookup_middle` | `List.getElem?_append_right` |
| `NoDup_seq` | `List.nodup_range'` | `take_app_le` | `List.take_append_of_le_length` |
| `elem_of_list_join` | `List.mem_flatten` | `drop_S`, `take_drop_middle` | `List.drop_eq_getElem_cons` |
| `lookup_drop` | `List.getElem?_drop` | `list_fmap_id` | `List.map_id` |
| `foldl_app` | `List.foldl_append` | `elem_of_lookup_imap` | `List.getElem?_mapIdx` |
| `length_Permutation_proper` | `List.Perm.length_eq` | `zip_fst_snd` | proof |
| `seqZ`, `elem_of_seqZ` | proof | `list_fmap_insert` | `List.map_set` |
| `drop_ge` | `List.drop_of_length_le` | `NoDup_submseteq` | `List.subperm_of_subset` |
| `NoDup_fmap(_2/_2_strong)` | `List.Pairwise.map`, `List.Pairwise.of_map` | `submseteq_length` | `List.Subperm.length_le` |
| `submseteq_length_Permutation` | `List.Subperm.perm_of_length_le` | `fst_zip`, `snd_zip` | `List.map_fst_zip`, `List.map_snd_zip` |
| `lookup_replicate(_2)` | `List.getElem?_replicate` | `lookup_cons` | `List.getElem?_cons` |
| `list_insert_commute` | `List.set_comm` | `length_drop` | `List.length_drop` |
| `elem_of_list_omap`, `omap_app` | `List.mem_filterMap`, `List.filterMap_append` | `prefix_nil`, `prefix_take` | `List.nil_prefix`, `List.take_prefix` |
| `prefix_length` | `List.IsPrefix.length_le` | `prefix_app_r`, `prefix_app`, `prefix_cons` | `List.prefix_append`, `List.prefix_append_right_inj`, `List.prefix_cons_inj` |
| `elem_of_prefix`, `prefix_lookup_Some` | `List.IsPrefix.subset`, proof | `length_zip_with` | `List.length_zipWith` |
| `fmap_take` | `List.map_take` | `take_take_drop` | `List.take_add` |
| `take_take` | `List.take_take` | `not_elem_of_cons` | `List.mem_cons` |
| `list_filter_iff`, `list_filter_filter` | `List.filter_congr`, `List.filter_filter` | `insert_app_l`, `insert_app_r_alt` | `List.set_append_left`, `List.set_append_right` |
| `insert_take_drop` | `List.set_eq_take_append_cons_drop` | `take_app_length` | `List.take_left'` |
| `nil_length_inv` | `List.eq_nil_of_length_eq_zero` | `mapM_Some(_1/_2)` | proof (`List.mapM_cons`) |
| `list_eq_same_length` | `List.ext_getElem?` | `elem_of_remove_dups`, `NoDup_remove_dups` | proof |
| `elem_of_list_split` | `List.append_of_mem` | `drop_app_le`, `drop_app` | `List.drop_append_of_le_length`, `List.drop_append` |
| `Forall2_*` (13 names), `Forall_Forall2_diag`, `list_omap_ext` | proof (Batteries `List.forall₂_cons`) | `length_imap`, `imap_app` | `List.length_mapIdx`, `List.mapIdx_append` |
| `elem_of_zip_with`, `elem_of_lookup_zip_with_1` | `List.getElem?_zipWith_eq_some` | `elem_of_list_bind` | `List.mem_flatMap` |
| `elem_of_Permutation` | `List.perm_middle`, `List.Perm.mem_iff` | `StronglySorted_unique_strong` | `List.Perm.eq_of_pairwise` |
| `zip_with_fmap_r` | `List.zipWith_map_right` | `not_Forall_Exists` | classical |
| `merge_sort_Permutation` | `List.mergeSort_perm` | `Sorted_merge_sort` | `List.pairwise_mergeSort` |
| `Sorted_StronglySorted` | `List.IsChain.pairwise` | `length_join`, `join_app` | `List.length_flatten`, `List.flatten_append` |
| `fmap_S_seq` | `List.range'_succ` | `elem_of_replicate` | `List.mem_replicate` |
| `drop_drop` | `List.drop_drop` | `app_inj_1` | `List.append_inj` |
| `Forall_fmap` | `List.forall_mem_map` | | |

Not aliased (no lemma to alias): the definitions `foldl`, `replicate`,
`reverse`, `option_list`, `prefix`, `list_subseteq`, `imap`, `mapM`,
`merge_sort`, `last` (vocabulary above), and `eval` (a `ring`-reflection
helper of stdpp's `list.v`, not a list operation).

**Deviations from stdpp:**

* `Sorted_merge_sort` takes transitivity as well as totality (`List.pairwise_mergeSort`
  does); stdpp's needs totality only.  Every `R` the weak files sort by is
  an order.
* `filter`/`list_find` predicates are `Bool`-valued (stdpp: a decidable
  `Prop`); `¬P x` is `p x = false`.
* `Forall`/`Exists` are the bounded quantifiers, so `Forall_forall`,
  `Exists_exists` are `Iff.rfl` and the `Forall_*` constructors are the
  `List.forall_mem_*` facts.
-/
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Perm

namespace MachCSL.Stdpp

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Definitions stdpp has and core does not -/

/-- stdpp's `list_find`: the first index whose element satisfies `p`, with
the element. -/
def listFind (p : α → Bool) : List α → Option (Nat × α)
  | [] => none
  | x :: l => if p x then some (0, x) else (listFind p l).map (fun q => (q.1 + 1, q.2))

/-- stdpp's `remove_dups`: drop every element that occurs again later. -/
def removeDups [DecidableEq α] : List α → List α
  | [] => []
  | x :: l => if x ∈ l then removeDups l else x :: removeDups l

/-- stdpp's `seqZ m len`: the integers `m, m+1, …, m+len-1` (empty for
`len ≤ 0`). -/
def seqZ (m len : Int) : List Int := (List.range len.toNat).map (fun (i : Nat) => m + (i : Int))

/-- stdpp's `sum_list_with f l`. -/
def sumListWith (f : α → Nat) (l : List α) : Nat := (l.map f).sum

/-! ## Membership -/

theorem elem_of_cons {l : List α} {x y : α} : x ∈ y :: l ↔ x = y ∨ x ∈ l := List.mem_cons

theorem elem_of_nil {x : α} : x ∈ ([] : List α) ↔ False := by simp

theorem not_elem_of_nil {x : α} : x ∉ ([] : List α) := List.not_mem_nil

theorem not_elem_of_cons {l : List α} {x y : α} : x ∉ y :: l ↔ x ≠ y ∧ x ∉ l := by simp

theorem elem_of_list_singleton {x y : α} : x ∈ [y] ↔ x = y := List.mem_singleton

theorem elem_of_app {l1 l2 : List α} {x : α} : x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2 := List.mem_append

theorem elem_of_list_lookup {l : List α} {x : α} : x ∈ l ↔ ∃ i : Nat, l[i]? = some x :=
  List.mem_iff_getElem?

theorem elem_of_list_lookup_1 {l : List α} {x : α} : x ∈ l → ∃ i : Nat, l[i]? = some x :=
  List.mem_iff_getElem?.1

theorem elem_of_list_lookup_2 {l : List α} {i : Nat} {x : α} : l[i]? = some x → x ∈ l :=
  fun h => List.mem_iff_getElem?.2 ⟨i, h⟩

theorem elem_of_list_fmap {f : α → β} {l : List α} {x : β} :
    x ∈ l.map f ↔ ∃ y, x = f y ∧ y ∈ l := by
  rw [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, e.symm, hy⟩, fun ⟨y, e, hy⟩ => ⟨y, hy, e.symm⟩⟩

theorem elem_of_list_fmap_1 {f : α → β} {l : List α} {x : α} : x ∈ l → f x ∈ l.map f :=
  List.mem_map_of_mem

theorem elem_of_list_filter {p : α → Bool} {l : List α} {x : α} :
    x ∈ l.filter p ↔ p x = true ∧ x ∈ l := by
  rw [List.mem_filter]; exact And.comm

theorem elem_of_seq {j n k : Nat} : k ∈ List.range' j n ↔ j ≤ k ∧ k < j + n := List.mem_range'_1

theorem elem_of_list_join {x : α} {ls : List (List α)} : x ∈ ls.flatten ↔ ∃ l, x ∈ l ∧ l ∈ ls := by
  rw [List.mem_flatten]
  exact ⟨fun ⟨l, h1, h2⟩ => ⟨l, h2, h1⟩, fun ⟨l, h1, h2⟩ => ⟨l, h2, h1⟩⟩

theorem elem_of_list_bind {f : α → List β} {x : β} {l : List α} :
    x ∈ l.flatMap f ↔ ∃ y, x ∈ f y ∧ y ∈ l := by
  rw [List.mem_flatMap]
  exact ⟨fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩, fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩⟩

theorem elem_of_list_omap {f : α → Option β} {l : List α} {y : β} :
    y ∈ l.filterMap f ↔ ∃ x, x ∈ l ∧ f x = some y := List.mem_filterMap

theorem elem_of_replicate {n : Nat} {x y : α} : y ∈ List.replicate n x ↔ y = x ∧ n ≠ 0 := by
  rw [List.mem_replicate]; exact And.comm

theorem elem_of_list_split {l : List α} {x : α} : x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2 :=
  List.append_of_mem

theorem elem_of_take {x : α} {n : Nat} {l : List α} :
    x ∈ l.take n ↔ ∃ i : Nat, l[i]? = some x ∧ i < n := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, h⟩
    rw [List.getElem?_take] at h
    split at h
    · exact ⟨i, h, ‹_›⟩
    · exact absurd h (by simp)
  · rintro ⟨i, h, hi⟩
    exact ⟨i, by rw [List.getElem?_take, if_pos hi, h]⟩

theorem elem_of_Permutation {l : List α} {x : α} : x ∈ l ↔ ∃ k, List.Perm l (x :: k) := by
  constructor
  · intro h
    obtain ⟨s, t, rfl⟩ := List.append_of_mem h
    exact ⟨s ++ t, List.perm_middle⟩
  · rintro ⟨k, hp⟩
    exact hp.mem_iff.2 (List.mem_cons_self)

/-! ## Lookup -/

theorem lookup_nil {i : Nat} : ([] : List α)[i]? = none := by simp

theorem lookup_cons {x : α} {l : List α} {i : Nat} :
    (x :: l)[i]? = match i with | 0 => some x | i + 1 => l[i]? := by
  cases i <;> rfl

theorem lookup_lt_Some {l : List α} {i : Nat} {x : α} : l[i]? = some x → i < l.length :=
  fun h => (List.getElem?_eq_some_iff.1 h).1

theorem lookup_lt_is_Some {l : List α} {i : Nat} : l[i]?.isSome ↔ i < l.length := by simp

theorem lookup_lt_is_Some_1 {l : List α} {i : Nat} : l[i]?.isSome → i < l.length :=
  lookup_lt_is_Some.1

theorem lookup_lt_is_Some_2 {l : List α} {i : Nat} : i < l.length → l[i]?.isSome :=
  lookup_lt_is_Some.2

theorem lookup_ge_None {l : List α} {i : Nat} : l[i]? = none ↔ l.length ≤ i :=
  List.getElem?_eq_none_iff

theorem lookup_ge_None_1 {l : List α} {i : Nat} : l[i]? = none → l.length ≤ i :=
  lookup_ge_None.1

theorem lookup_ge_None_2 {l : List α} {i : Nat} : l.length ≤ i → l[i]? = none :=
  lookup_ge_None.2

theorem list_eq {l1 l2 : List α} : (∀ i : Nat, l1[i]? = l2[i]?) → l1 = l2 := List.ext_getElem?

theorem list_eq_same_length {l1 l2 : List α} {n : Nat} (h2 : l2.length = n) (h1 : l1.length = n)
    (H : ∀ (i : Nat) x y, i < n → l1[i]? = some x → l2[i]? = some y → x = y) : l1 = l2 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    exact congrArg some (H i _ _ hi (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _))
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem list_lookup_fmap {f : α → β} {l : List α} {i : Nat} : (l.map f)[i]? = l[i]?.map f :=
  List.getElem?_map

theorem lookup_app_l {l1 l2 : List α} {i : Nat} : i < l1.length → (l1 ++ l2)[i]? = l1[i]? :=
  List.getElem?_append_left

theorem lookup_app_r {l1 l2 : List α} {i : Nat} :
    l1.length ≤ i → (l1 ++ l2)[i]? = l2[i - l1.length]? :=
  List.getElem?_append_right

theorem lookup_app_l_Some {l1 l2 : List α} {i : Nat} {x : α} :
    l1[i]? = some x → (l1 ++ l2)[i]? = some x :=
  fun h => by rw [lookup_app_l (lookup_lt_Some h), h]

theorem lookup_app_Some {l1 l2 : List α} {i : Nat} {x : α} :
    (l1 ++ l2)[i]? = some x ↔ l1[i]? = some x ∨ (l1.length ≤ i ∧ l2[i - l1.length]? = some x) := by
  by_cases hi : i < l1.length
  · rw [lookup_app_l hi]
    exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd h'.1 (by omega))⟩
  · rw [lookup_app_r (by omega), lookup_ge_None_2 (l := l1) (by omega)]
    exact ⟨fun h => Or.inr ⟨by omega, h⟩, fun h => h.elim (fun h' => by simp at h') And.right⟩

theorem list_lookup_middle {l1 l2 : List α} {x : α} {n : Nat} :
    n = l1.length → (l1 ++ x :: l2)[n]? = some x := by
  rintro rfl; simp

theorem lookup_take {l : List α} {n i : Nat} : i < n → (l.take n)[i]? = l[i]? :=
  List.getElem?_take_of_lt

theorem lookup_take_ge {l : List α} {n i : Nat} : n ≤ i → (l.take n)[i]? = none :=
  List.getElem?_take_eq_none

theorem lookup_take_Some {l : List α} {n i : Nat} {a : α} :
    (l.take n)[i]? = some a ↔ l[i]? = some a ∧ i < n := by
  rw [List.getElem?_take]
  by_cases hi : i < n
  · simp [hi]
  · simp [hi]

theorem lookup_drop {l : List α} {n i : Nat} : (l.drop n)[i]? = l[n + i]? := List.getElem?_drop

theorem lookup_seq_lt {j n i : Nat} : i < n → (List.range' j n)[i]? = some (j + i) := by
  intro h; rw [List.getElem?_range' h]; simp

theorem lookup_seq_ge {j n i : Nat} : n ≤ i → (List.range' j n)[i]? = none := by
  intro h; rw [List.getElem?_eq_none_iff, List.length_range']; exact h

theorem lookup_seq {j n i j' : Nat} : (List.range' j n)[i]? = some j' ↔ j' = j + i ∧ i < n := by
  by_cases hi : i < n
  · rw [lookup_seq_lt hi]; simp only [Option.some.injEq]; exact ⟨fun h => ⟨h.symm, hi⟩, fun h => h.1.symm⟩
  · rw [lookup_seq_ge (by omega)]; simp only [reduceCtorEq, false_iff]; omega

theorem lookup_replicate_2 {n : Nat} {x : α} {i : Nat} : i < n → (List.replicate n x)[i]? = some x :=
  List.getElem?_replicate_of_lt

theorem lookup_replicate {n : Nat} {x y : α} {i : Nat} :
    (List.replicate n x)[i]? = some y ↔ y = x ∧ i < n := by
  rw [List.getElem?_replicate]
  by_cases hi : i < n
  · simp only [hi, if_true, Option.some.injEq, and_true]; exact eq_comm
  · simp [hi]

theorem lookup_zip_with {f : α → β → γ} {l : List α} {k : List β} {i : Nat} :
    (List.zipWith f l k)[i]? = (l[i]?).bind (fun x => (k[i]?).bind (fun y => some (f x y))) := by
  rw [List.getElem?_zipWith]
  cases l[i]? <;> cases k[i]? <;> rfl

theorem lookup_zip_with_Some {f : α → β → γ} {l : List α} {k : List β} {i : Nat} {z : γ} :
    (List.zipWith f l k)[i]? = some z ↔ ∃ x y, z = f x y ∧ l[i]? = some x ∧ k[i]? = some y := by
  rw [List.getElem?_zipWith_eq_some]
  exact ⟨fun ⟨x, y, h1, h2, h3⟩ => ⟨x, y, h3.symm, h1, h2⟩,
    fun ⟨x, y, h1, h2, h3⟩ => ⟨x, y, h2, h3, h1.symm⟩⟩

theorem elem_of_lookup_zip_with_1 {f : α → β → γ} {l : List α} {k : List β} {z : γ} :
    z ∈ List.zipWith f l k → ∃ (i : Nat) (x : α) (y : β), z = f x y ∧ l[i]? = some x ∧ k[i]? = some y := by
  intro h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  obtain ⟨x, y, h1, h2, h3⟩ := lookup_zip_with_Some.1 hi
  exact ⟨i, x, y, h1, h2, h3⟩

theorem elem_of_zip_with {f : α → β → γ} {l : List α} {k : List β} {z : γ} :
    z ∈ List.zipWith f l k → ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ k := by
  intro h
  obtain ⟨i, x, y, h1, h2, h3⟩ := elem_of_lookup_zip_with_1 h
  exact ⟨x, y, h1, elem_of_list_lookup_2 h2, elem_of_list_lookup_2 h3⟩

theorem list_lookup_imap {f : Nat → α → β} {l : List α} {i : Nat} :
    (l.mapIdx f)[i]? = l[i]?.map (f i) := List.getElem?_mapIdx

theorem elem_of_lookup_imap {f : Nat → α → β} {l : List α} {x : β} :
    x ∈ l.mapIdx f ↔ ∃ (i : Nat) (y : α), x = f i y ∧ l[i]? = some y := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, h⟩
    rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, e⟩ := h
    exact ⟨i, y, e.symm, hy⟩
  · rintro ⟨i, y, e, hy⟩
    exact ⟨i, by rw [List.getElem?_mapIdx, hy, e]; rfl⟩

/-! ## Total lookup (`!!!`) -/

theorem list_lookup_total_alt [Inhabited α] {l : List α} {i : Nat} :
    l[i]! = (l[i]?).getD default := List.getElem!_eq_getElem?_getD

theorem list_lookup_total_correct [Inhabited α] {l : List α} {i : Nat} {x : α} :
    l[i]? = some x → l[i]! = x := by
  intro h; rw [List.getElem!_eq_getElem?_getD, h]; rfl

theorem list_lookup_lookup_total_lt [Inhabited α] {l : List α} {i : Nat} :
    i < l.length → l[i]? = some l[i]! := by
  intro h; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem list_lookup_total_fmap [Inhabited α] [Inhabited β] {f : α → β} {l : List α} {i : Nat} :
    i < l.length → (l.map f)[i]! = f l[i]! := by
  intro h
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

/-! ## Insert (`<[i:=x]>`, i.e. `List.set`) -/

theorem list_lookup_insert {l : List α} {i : Nat} {x : α} :
    i < l.length → (l.set i x)[i]? = some x := List.getElem?_set_self

theorem list_lookup_insert_ne {l : List α} {i j : Nat} {x : α} :
    i ≠ j → (l.set i x)[j]? = l[j]? := fun h => List.getElem?_set_ne h

theorem list_insert_insert {l : List α} {i : Nat} {x y : α} :
    (l.set i y).set i x = l.set i x := List.set_set _

theorem list_insert_commute {l : List α} {i j : Nat} {x y : α} :
    i ≠ j → (l.set j y).set i x = (l.set i x).set j y :=
  fun h => List.set_comm _ _ (Ne.symm h)

theorem length_insert {l : List α} {i : Nat} {x : α} : (l.set i x).length = l.length :=
  List.length_set

theorem list_fmap_insert {f : α → β} {l : List α} {i : Nat} {x : α} :
    (l.set i x).map f = (l.map f).set i (f x) := List.map_set

theorem insert_app_l {l1 l2 : List α} {i : Nat} {x : α} :
    i < l1.length → (l1 ++ l2).set i x = l1.set i x ++ l2 :=
  fun h => List.set_append_left i x h

theorem insert_app_r_alt {l1 l2 : List α} {i : Nat} {x : α} :
    l1.length ≤ i → (l1 ++ l2).set i x = l1 ++ l2.set (i - l1.length) x :=
  fun h => List.set_append_right i x h

theorem insert_take_drop {l : List α} {i : Nat} {x : α} :
    i < l.length → l.set i x = l.take i ++ x :: l.drop (i + 1) := by
  intro h; rw [List.set_eq_take_append_cons_drop, if_pos h]

/-! ## Length -/

theorem length_fmap {f : α → β} {l : List α} : (l.map f).length = l.length := List.length_map f

theorem length_app {l l' : List α} : (l ++ l').length = l.length + l'.length := List.length_append

theorem length_replicate {n : Nat} {x : α} : (List.replicate n x).length = n :=
  List.length_replicate

theorem length_seq {m n : Nat} : (List.range' m n).length = n := List.length_range'

theorem length_take {l : List α} {n : Nat} : (l.take n).length = min n l.length := List.length_take

theorem length_take_le {l : List α} {n : Nat} : n ≤ l.length → (l.take n).length = n :=
  List.length_take_of_le

theorem length_drop {l : List α} {n : Nat} : (l.drop n).length = l.length - n := List.length_drop

theorem length_zip_with {f : α → β → γ} {l : List α} {k : List β} :
    (List.zipWith f l k).length = min l.length k.length := List.length_zipWith

theorem length_imap {f : Nat → α → β} {l : List α} : (l.mapIdx f).length = l.length :=
  List.length_mapIdx

theorem length_join {ls : List (List α)} : ls.flatten.length = (ls.map List.length).sum :=
  List.length_flatten

theorem length_Permutation_proper {l1 l2 : List α} : List.Perm l1 l2 → l1.length = l2.length :=
  List.Perm.length_eq

theorem nil_length_inv {l : List α} : l.length = 0 → l = [] := List.eq_nil_of_length_eq_zero

/-! ## map / filter / omap / imap / join / zip -/

theorem fmap_nil {f : α → β} : ([] : List α).map f = [] := List.map_nil

theorem fmap_cons {f : α → β} {x : α} {l : List α} : (x :: l).map f = f x :: l.map f :=
  List.map_cons

theorem fmap_app {f : α → β} {l1 l2 : List α} : (l1 ++ l2).map f = l1.map f ++ l2.map f :=
  List.map_append

theorem fmap_take {f : α → β} {n : Nat} {l : List α} : (l.take n).map f = (l.map f).take n :=
  List.map_take

theorem list_fmap_id {l : List α} : l.map id = l := List.map_id l

theorem list_fmap_compose {f : α → β} {g : β → γ} {l : List α} :
    l.map (g ∘ f) = (l.map f).map g := List.map_map.symm

theorem list_fmap_ext {f g : α → β} {l : List α} :
    (∀ (i : Nat) x, l[i]? = some x → f x = g x) → l.map f = l.map g := by
  intro H
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, h⟩ := List.mem_iff_getElem?.1 hx
  exact H i x h

theorem filter_nil {p : α → Bool} : ([] : List α).filter p = [] := List.filter_nil

theorem filter_cons {p : α → Bool} {x : α} {l : List α} :
    (x :: l).filter p = if p x then x :: l.filter p else l.filter p := List.filter_cons

theorem filter_cons_True {p : α → Bool} {x : α} {l : List α} :
    p x = true → (x :: l).filter p = x :: l.filter p := List.filter_cons_of_pos

theorem filter_cons_False {p : α → Bool} {x : α} {l : List α} :
    p x = false → (x :: l).filter p = l.filter p :=
  fun h => List.filter_cons_of_neg (by simp [h])

theorem filter_app {p : α → Bool} {l1 l2 : List α} :
    (l1 ++ l2).filter p = l1.filter p ++ l2.filter p := List.filter_append _ _

theorem list_filter_iff {p1 p2 : α → Bool} {l : List α} :
    (∀ x, p1 x = true ↔ p2 x = true) → l.filter p1 = l.filter p2 := by
  intro H
  apply List.filter_congr
  intro x _
  cases h1 : p1 x <;> cases h2 : p2 x <;> simp_all

theorem list_filter_filter {p1 p2 : α → Bool} {l : List α} :
    (l.filter p2).filter p1 = l.filter (fun a => p1 a && p2 a) := List.filter_filter

theorem omap_app {f : α → Option β} {l1 l2 : List α} :
    (l1 ++ l2).filterMap f = l1.filterMap f ++ l2.filterMap f := List.filterMap_append

theorem imap_app {f : Nat → α → β} {l1 l2 : List α} :
    (l1 ++ l2).mapIdx f = l1.mapIdx f ++ l2.mapIdx (fun n => f (l1.length + n)) := by
  rw [List.mapIdx_append]
  congr 2
  funext n
  rw [Nat.add_comm]

theorem join_app {l1 l2 : List (List α)} : (l1 ++ l2).flatten = l1.flatten ++ l2.flatten :=
  List.flatten_append

theorem foldl_app {f : α → β → α} {l k : List β} {a : α} :
    (l ++ k).foldl f a = k.foldl f (l.foldl f a) := List.foldl_append

theorem zip_with_fmap_r {δ : Type _} {f : α → β → γ} {g : δ → β} {l : List α} {kD : List δ} :
    List.zipWith f l (kD.map g) = List.zipWith (fun x z => f x (g z)) l kD :=
  List.zipWith_map_right

theorem zip_fst_snd {lk : List (α × β)} : List.zip (lk.map Prod.fst) (lk.map Prod.snd) = lk := by
  induction lk with
  | nil => rfl
  | cons p t ih => simp [ih]

theorem fst_zip {l : List α} {k : List β} : l.length ≤ k.length → (List.zip l k).map Prod.fst = l :=
  List.map_fst_zip

theorem snd_zip {l : List α} {k : List β} : k.length ≤ l.length → (List.zip l k).map Prod.snd = k :=
  List.map_snd_zip

theorem fmap_S_seq {j n : Nat} : (List.range' j n).map Nat.succ = List.range' (j + 1) n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [List.range'_succ, List.map_cons, ih]

theorem list_omap_ext {δ : Type _} {f : α → Option β} {g : δ → Option β} {l1 : List α}
    {l2 : List δ} : List.Forall₂ (fun a b => f a = g b) l1 l2 → l1.filterMap f = l2.filterMap g := by
  intro h
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.filterMap_cons, hab, ih]

/-! ## take / drop -/

theorem take_0 {l : List α} : l.take 0 = [] := List.take_zero

theorem drop_0 {l : List α} : l.drop 0 = l := List.drop_zero

theorem take_nil {n : Nat} : ([] : List α).take n = [] := List.take_nil

theorem take_drop {i : Nat} {l : List α} : l.take i ++ l.drop i = l := List.take_append_drop i l

theorem take_ge {l : List α} {n : Nat} : l.length ≤ n → l.take n = l := List.take_of_length_le

theorem drop_ge {l : List α} {n : Nat} : l.length ≤ n → l.drop n = [] := List.drop_of_length_le

theorem take_S_r {l : List α} {n : Nat} {x : α} :
    l[n]? = some x → l.take (n + 1) = l.take n ++ [x] := by
  intro h; rw [List.take_add_one, h]; rfl

theorem drop_S {l : List α} {x : α} {n : Nat} : l[n]? = some x → l.drop n = x :: l.drop (n + 1) := by
  intro h
  obtain ⟨hn, e⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.drop_eq_getElem_cons hn, e]

theorem take_drop_middle {l : List α} {i : Nat} {x : α} :
    l[i]? = some x → l.take i ++ x :: l.drop (i + 1) = l := by
  intro h; rw [← drop_S h, List.take_append_drop]

theorem take_app_le {l k : List α} {n : Nat} : n ≤ l.length → (l ++ k).take n = l.take n :=
  List.take_append_of_le_length

theorem take_app_length {l k : List α} : (l ++ k).take l.length = l := List.take_left' rfl

theorem drop_app_le {l k : List α} {n : Nat} : n ≤ l.length → (l ++ k).drop n = l.drop n ++ k :=
  List.drop_append_of_le_length

theorem drop_app {l k : List α} {n : Nat} : (l ++ k).drop n = l.drop n ++ k.drop (n - l.length) :=
  List.drop_append

theorem take_take {l : List α} {n m : Nat} : (l.take m).take n = l.take (min n m) := List.take_take

theorem take_take_drop {l : List α} {n m : Nat} : l.take n ++ (l.drop n).take m = l.take (n + m) :=
  List.take_add.symm

theorem drop_drop {l : List α} {n1 n2 : Nat} : (l.drop n2).drop n1 = l.drop (n2 + n1) :=
  List.drop_drop

theorem app_inj_1 {l1 k1 l2 k2 : List α} :
    l1.length = k1.length → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2 :=
  fun hl h => List.append_inj h hl

/-! ## last -/

theorem last_Some {l : List α} {x : α} : l.getLast? = some x ↔ ∃ l', l = l' ++ [x] :=
  List.getLast?_eq_some_iff

theorem last_snoc {x : α} {l : List α} : (l ++ [x]).getLast? = some x := List.getLast?_concat

theorem last_None {l : List α} : l.getLast? = none ↔ l = [] := List.getLast?_eq_none_iff

theorem last_is_Some {l : List α} : l.getLast?.isSome ↔ l ≠ [] := List.getLast?_isSome

theorem last_lookup {l : List α} : l.getLast? = l[l.length - 1]? := List.getLast?_eq_getElem?

theorem last_Some_elem_of {l : List α} {x : α} : l.getLast? = some x → x ∈ l :=
  List.mem_of_getLast?

theorem fmap_last {f : α → β} {l : List α} : (l.map f).getLast? = l.getLast?.map f :=
  List.getLast?_map

theorem last_filter_Some {p : α → Bool} {l : List α} {x : α} :
    (l.filter p).getLast? = some x → ∃ l1 l2, l = l1 ++ x :: l2 ∧ ∀ z ∈ l2, p z = false := by
  induction l with
  | nil => simp
  | cons a t ih =>
    intro h
    by_cases ht : (t.filter p).getLast? = none
    · have hnil : t.filter p = [] := List.getLast?_eq_none_iff.1 ht
      have hall : ∀ z ∈ t, p z = false := by
        intro z hz
        have := List.filter_eq_nil_iff.1 hnil z hz
        simpa using this
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, hnil] at h
        simp only [List.getLast?_singleton, Option.some.injEq] at h
        subst h
        exact ⟨[], t, rfl, hall⟩
      · rw [List.filter_cons_of_neg ha, hnil] at h
        simp at h
    · have hsome : (t.filter p).getLast? = some x := by
        by_cases ha : p a = true
        · rw [List.filter_cons_of_pos ha] at h
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 ht
          rw [List.getLast?_cons, hy] at h
          simp only [Option.getD_some] at h
          rw [hy, h]
        · rw [List.filter_cons_of_neg ha] at h
          exact h
      obtain ⟨l1, l2, e, hz⟩ := ih hsome
      exact ⟨a :: l1, l2, by rw [e]; rfl, hz⟩

/-! ## list_find -/

theorem list_find_Some {p : α → Bool} {l : List α} {i : Nat} {x : α} :
    listFind p l = some (i, x) ↔
      l[i]? = some x ∧ p x = true ∧ ∀ (j : Nat) y, l[j]? = some y → j < i → p y = false := by
  induction l generalizing i with
  | nil => simp [listFind]
  | cons a t ih =>
    by_cases ha : p a = true
    · simp only [listFind, ha, if_true, Option.some.injEq, Prod.mk.injEq]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, true_and, Nat.not_lt_zero,
          false_imp_iff, imp_true_iff, and_true]
        constructor
        · intro h; subst h; exact ⟨rfl, ha⟩
        · intro h; exact h.1
      | succ i =>
        constructor
        · intro h; exact absurd h.1 (by omega)
        · rintro ⟨_, _, H⟩
          have := H 0 a rfl (Nat.succ_pos i)
          rw [ha] at this
          exact absurd this (by decide)
    · have ha' : p a = false := by simpa using ha
      simp only [listFind, ha', Bool.false_eq_true, if_false, Option.map_eq_some_iff,
        Prod.exists, Prod.mk.injEq]
      cases i with
      | zero =>
        simp only [Nat.add_one_ne_zero, false_and, and_false, exists_false, false_iff,
          List.getElem?_cons_zero, Option.some.injEq, not_and]
        intro e; subst e; rw [ha']; simp
      | succ i =>
        simp only [Nat.add_right_cancel_iff, List.getElem?_cons_succ]
        constructor
        · rintro ⟨i', x', h, rfl, rfl⟩
          obtain ⟨h1, h2, h3⟩ := ih.1 h
          refine ⟨h1, h2, ?_⟩
          intro j y hj hji
          cases j with
          | zero => simp at hj; subst hj; exact ha'
          | succ j => exact h3 j y hj (by omega)
        · rintro ⟨h1, h2, h3⟩
          refine ⟨i, x, ih.2 ⟨h1, h2, fun j y hj hji => h3 (j + 1) y hj (by omega)⟩, rfl, rfl⟩

theorem list_find_None {p : α → Bool} {l : List α} :
    listFind p l = none ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil => simp [listFind]
  | cons a t ih =>
    by_cases ha : p a = true
    · simp [listFind, ha]
    · have ha' : p a = false := by simpa using ha
      simp [listFind, ha', ih]

theorem list_find_elem_of {p : α → Bool} {l : List α} {x : α} :
    x ∈ l → p x = true → (listFind p l).isSome := by
  intro hx hp
  cases h : listFind p l with
  | some _ => rfl
  | none =>
    have := list_find_None.1 h x hx
    rw [hp] at this
    exact absurd this (by decide)

theorem list_find_app_l {p : α → Bool} {l1 l2 : List α} {i : Nat} {x : α} :
    listFind p l1 = some (i, x) → listFind p (l1 ++ l2) = some (i, x) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := list_find_Some.1 h
  refine list_find_Some.2 ⟨lookup_app_l_Some h1, h2, ?_⟩
  intro j y hj hji
  have hj' : j < l1.length := Nat.lt_trans hji (lookup_lt_Some h1)
  rw [lookup_app_l hj'] at hj
  exact h3 j y hj hji

/-! ## Forall / Exists (bounded quantifiers) -/

theorem Forall_forall {P : α → Prop} {l : List α} : (∀ x ∈ l, P x) ↔ ∀ x, x ∈ l → P x := Iff.rfl

theorem Exists_exists {P : α → Prop} {l : List α} : (∃ x ∈ l, P x) ↔ ∃ x, x ∈ l ∧ P x := Iff.rfl

theorem Forall_nil {P : α → Prop} : (∀ x ∈ ([] : List α), P x) ↔ True := by simp

theorem Forall_nil_2 {P : α → Prop} : ∀ x ∈ ([] : List α), P x := fun _ h => absurd h List.not_mem_nil

theorem Forall_cons {P : α → Prop} {x : α} {l : List α} :
    (∀ y ∈ x :: l, P y) ↔ P x ∧ ∀ y ∈ l, P y := List.forall_mem_cons

theorem Forall_cons_1 {P : α → Prop} {x : α} {l : List α} :
    (∀ y ∈ x :: l, P y) → P x ∧ ∀ y ∈ l, P y := List.forall_mem_cons.1

theorem Forall_cons_2 {P : α → Prop} {x : α} {l : List α} :
    P x → (∀ y ∈ l, P y) → ∀ y ∈ x :: l, P y := fun h1 h2 => List.forall_mem_cons.2 ⟨h1, h2⟩

theorem Forall_singleton {P : α → Prop} {x : α} : (∀ y ∈ [x], P y) ↔ P x := by simp

theorem Forall_app {P : α → Prop} {l1 l2 : List α} :
    (∀ x ∈ l1 ++ l2, P x) ↔ (∀ x ∈ l1, P x) ∧ (∀ x ∈ l2, P x) := List.forall_mem_append

theorem Forall_fmap {f : α → β} {P : β → Prop} {l : List α} :
    (∀ x ∈ l.map f, P x) ↔ ∀ x ∈ l, P (f x) := List.forall_mem_map

theorem Forall_lookup {P : α → Prop} {l : List α} :
    (∀ x ∈ l, P x) ↔ ∀ (i : Nat) x, l[i]? = some x → P x :=
  ⟨fun H _ x h => H x (elem_of_list_lookup_2 h),
    fun H x hx => let ⟨i, h⟩ := List.mem_iff_getElem?.1 hx; H i x h⟩

theorem Forall_lookup_1 {P : α → Prop} {l : List α} {i : Nat} {x : α} :
    (∀ y ∈ l, P y) → l[i]? = some x → P x := fun H h => Forall_lookup.1 H i x h

theorem Forall_lookup_2 {P : α → Prop} {l : List α} :
    (∀ (i : Nat) x, l[i]? = some x → P x) → ∀ x ∈ l, P x := Forall_lookup.2

theorem not_Forall_Exists {P : α → Prop} {l : List α} : ¬ (∀ x ∈ l, P x) → ∃ x ∈ l, ¬ P x :=
  fun h => Classical.byContradiction fun h' =>
    h fun x hx => Classical.byContradiction fun hp => h' ⟨x, hx, hp⟩

/-! ## Forall2 (`List.Forall₂`) -/

section Forall2
variable {P : α → β → Prop}

theorem Forall2_cons_2 {x : α} {l : List α} {y : β} {k : List β} :
    P x y → List.Forall₂ P l k → List.Forall₂ P (x :: l) (y :: k) := List.Forall₂.cons

theorem Forall2_cons_1 {x : α} {l : List α} {y : β} {k : List β} :
    List.Forall₂ P (x :: l) (y :: k) → P x y ∧ List.Forall₂ P l k := List.forall₂_cons.1

theorem Forall2_nil_inv_l {k : List β} : List.Forall₂ P [] k → k = [] := by
  intro h; cases h; rfl

theorem Forall2_length {l : List α} {k : List β} : List.Forall₂ P l k → l.length = k.length := by
  intro h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Forall2_impl {Q : α → β → Prop} {l : List α} {k : List β} :
    List.Forall₂ P l k → (∀ x y, P x y → Q x y) → List.Forall₂ Q l k := by
  intro h H
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (H _ _ hab) ih

theorem Forall2_lookup_l {l : List α} {k : List β} {i : Nat} {x : α} :
    List.Forall₂ P l k → l[i]? = some x → ∃ y, k[i]? = some y ∧ P x y := by
  intro h
  induction h generalizing i with
  | nil => simp
  | @cons a b _ _ hab _ ih =>
    cases i with
    | zero => intro hx; simp at hx; subst hx; exact ⟨b, rfl, hab⟩
    | succ i => intro hx; exact ih hx

theorem Forall2_lookup_r {l : List α} {k : List β} {i : Nat} {y : β} :
    List.Forall₂ P l k → k[i]? = some y → ∃ x, l[i]? = some x ∧ P x y := by
  intro h
  induction h generalizing i with
  | nil => simp
  | @cons a b _ _ hab _ ih =>
    cases i with
    | zero => intro hy; simp at hy; subst hy; exact ⟨a, rfl, hab⟩
    | succ i => intro hy; exact ih hy

theorem Forall2_same_length_lookup_2 {l : List α} {k : List β} :
    l.length = k.length → (∀ (i : Nat) x y, l[i]? = some x → k[i]? = some y → P x y) →
      List.Forall₂ P l k := by
  induction l generalizing k with
  | nil => intro hl _; cases k with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons a t ih =>
    intro hl H
    cases k with
    | nil => simp at hl
    | cons b k =>
      refine .cons (H 0 a b rfl rfl) (ih (by simpa using hl) ?_)
      intro i x y hx hy
      exact H (i + 1) x y hx hy

theorem Forall2_same_length_lookup {l : List α} {k : List β} :
    List.Forall₂ P l k ↔
      l.length = k.length ∧ ∀ (i : Nat) x y, l[i]? = some x → k[i]? = some y → P x y := by
  constructor
  · intro h
    refine ⟨Forall2_length h, fun i x y hx hy => ?_⟩
    obtain ⟨y', hy', hp⟩ := Forall2_lookup_l h hx
    rw [hy] at hy'
    cases hy'
    exact hp
  · rintro ⟨hl, H⟩
    exact Forall2_same_length_lookup_2 hl H

theorem Forall2_app_inv_l {l1 l2 : List α} {k : List β} :
    List.Forall₂ P (l1 ++ l2) k ↔
      ∃ k1 k2, List.Forall₂ P l1 k1 ∧ List.Forall₂ P l2 k2 ∧ k = k1 ++ k2 := by
  induction l1 generalizing k with
  | nil =>
    constructor
    · intro h; exact ⟨[], k, .nil, h, rfl⟩
    · rintro ⟨k1, k2, h1, h2, rfl⟩; cases h1; exact h2
  | cons a t ih =>
    constructor
    · intro h
      cases h with
      | @cons _ b _ k' hab h' =>
        obtain ⟨k1, k2, h1, h2, rfl⟩ := ih.1 h'
        exact ⟨b :: k1, k2, .cons hab h1, h2, rfl⟩
    · rintro ⟨k1, k2, h1, h2, rfl⟩
      cases h1 with
      | cons hab h1' => exact .cons hab (ih.2 ⟨_, k2, h1', h2, rfl⟩)

theorem Forall2_fmap_r {δ : Type _} {f : δ → β} {Q : α → β → Prop} {k : List α} {l : List δ} :
    List.Forall₂ Q k (l.map f) ↔ List.Forall₂ (fun x y => Q x (f y)) k l := by
  induction k generalizing l with
  | nil =>
    cases l with
    | nil => simp
    | cons b l => constructor <;> intro h <;> cases h
  | cons a t ih =>
    cases l with
    | nil => constructor <;> intro h <;> cases h
    | cons b l => simp [ih]

end Forall2

theorem Forall_Forall2_diag {Q : α → α → Prop} {l : List α} :
    (∀ x ∈ l, Q x x) → List.Forall₂ Q l l := by
  induction l with
  | nil => intro _; exact .nil
  | cons a t ih =>
    intro H
    exact .cons (H a List.mem_cons_self) (ih fun x hx => H x (List.mem_cons_of_mem a hx))

/-! ## mapM (option) -/

theorem mapM_Some {f : α → Option β} {l : List α} {k : List β} :
    l.mapM f = some k ↔ List.Forall₂ (fun x y => f x = some y) l k := by
  induction l generalizing k with
  | nil =>
    cases k with
    | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
    | cons b k =>
      constructor
      · intro h; rw [List.mapM_nil] at h; cases h
      · intro h; cases h
  | cons a t ih =>
    cases k with
    | nil =>
      constructor
      · intro h
        rw [List.mapM_cons] at h
        revert h
        cases f a <;> cases List.mapM f t <;> simp
      · intro h; cases h
    | cons b k =>
      rw [List.forall₂_cons, ← ih, List.mapM_cons]
      cases f a <;> cases List.mapM f t <;> simp

theorem mapM_Some_1 {f : α → Option β} {l : List α} {k : List β} :
    l.mapM f = some k → List.Forall₂ (fun x y => f x = some y) l k := mapM_Some.1

theorem mapM_Some_2 {f : α → Option β} {l : List α} {k : List β} :
    List.Forall₂ (fun x y => f x = some y) l k → l.mapM f = some k := mapM_Some.2

/-! ## NoDup (`List.Nodup`) -/

theorem NoDup_singleton {x : α} : [x].Nodup := List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

theorem NoDup_cons {x : α} {l : List α} : (x :: l).Nodup ↔ x ∉ l ∧ l.Nodup := List.nodup_cons

theorem NoDup_cons_1_1 {x : α} {l : List α} : (x :: l).Nodup → x ∉ l := fun h => (List.nodup_cons.1 h).1

theorem NoDup_cons_1_2 {x : α} {l : List α} : (x :: l).Nodup → l.Nodup := fun h => (List.nodup_cons.1 h).2

theorem NoDup_app {l k : List α} :
    (l ++ k).Nodup ↔ l.Nodup ∧ (∀ x, x ∈ l → x ∉ k) ∧ k.Nodup := by
  rw [List.nodup_append]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun x hx hk => h3 x hx x hk rfl, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h1, h2, fun a ha b hb e => h3 a ha (e ▸ hb)⟩

theorem NoDup_lookup {l : List α} {i j : Nat} {x : α} :
    l.Nodup → l[i]? = some x → l[j]? = some x → i = j := by
  induction l generalizing i j with
  | nil => intro _ hi; simp at hi
  | cons a t ih =>
    intro hnd hi hj
    rw [List.nodup_cons] at hnd
    cases i <;> cases j
    · rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hi; exact absurd (elem_of_list_lookup_2 hj) hnd.1
    · simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
      subst hj; exact absurd (elem_of_list_lookup_2 hi) hnd.1
    · simp only [List.getElem?_cons_succ] at hi hj
      exact congrArg (· + 1) (ih hnd.2 hi hj)

theorem NoDup_alt {l : List α} :
    l.Nodup ↔ ∀ (i j : Nat) x, l[i]? = some x → l[j]? = some x → i = j := by
  refine ⟨fun h i j x => NoDup_lookup h, ?_⟩
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro H
    rw [List.nodup_cons]
    refine ⟨fun ha => ?_, ih fun i j x hi hj => ?_⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
      have := H 0 (j + 1) a rfl hj
      omega
    · have := H (i + 1) (j + 1) x hi hj
      omega

theorem NoDup_filter {p : α → Bool} {l : List α} : l.Nodup → (l.filter p).Nodup :=
  fun h => h.sublist List.filter_sublist

theorem NoDup_seq {j n : Nat} : (List.range' j n).Nodup := List.nodup_range'

theorem NoDup_fmap_2 {f : α → β} (hf : Function.Injective f) {l : List α} :
    l.Nodup → (l.map f).Nodup :=
  fun h => List.Pairwise.map f (fun _ _ hne e => hne (hf e)) h

theorem NoDup_fmap_2_strong {f : α → β} {l : List α} :
    (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) → l.Nodup → (l.map f).Nodup := by
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons a t ih =>
    intro H hnd
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih (fun x y hx hy => H x y (List.mem_cons_of_mem a hx)
      (List.mem_cons_of_mem a hy)) hnd.2⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    exact hnd.1 (H y a (List.mem_cons_of_mem a hy) List.mem_cons_self e ▸ hy)

theorem NoDup_fmap {f : α → β} (hf : Function.Injective f) {l : List α} :
    (l.map f).Nodup ↔ l.Nodup :=
  ⟨fun h => List.Pairwise.of_map f (fun _ _ hne e => hne (congrArg f e)) h, NoDup_fmap_2 hf⟩

theorem NoDup_Permutation {l k : List α} :
    l.Nodup → k.Nodup → (∀ x, x ∈ l ↔ x ∈ k) → List.Perm l k :=
  fun h1 h2 H => (List.perm_ext_iff_of_nodup h1 h2).2 H

theorem NoDup_submseteq {l k : List α} :
    l.Nodup → (∀ x, x ∈ l → x ∈ k) → List.Subperm l k :=
  fun h H => List.subperm_of_subset h (fun x hx => H x hx)

theorem submseteq_length {l1 l2 : List α} : List.Subperm l1 l2 → l1.length ≤ l2.length :=
  List.Subperm.length_le

theorem submseteq_length_Permutation {l1 l2 : List α} :
    List.Subperm l1 l2 → l2.length ≤ l1.length → List.Perm l1 l2 :=
  List.Subperm.perm_of_length_le

/-! ## remove_dups -/

theorem elem_of_remove_dups [DecidableEq α] {l : List α} {x : α} : x ∈ removeDups l ↔ x ∈ l := by
  induction l with
  | nil => simp [removeDups]
  | cons a t ih =>
    by_cases ha : a ∈ t
    · simp only [removeDups, ha, if_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ha
        · exact h
    · simp [removeDups, ha, ih]

theorem NoDup_remove_dups [DecidableEq α] {l : List α} : (removeDups l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    by_cases ha : a ∈ t
    · simp only [removeDups, ha, if_true]; exact ih
    · simp only [removeDups, ha, if_false]
      exact List.nodup_cons.2 ⟨fun h => ha (elem_of_remove_dups.1 h), ih⟩

/-! ## seqZ -/

theorem elem_of_seqZ {m n k : Int} : k ∈ seqZ m n ↔ m ≤ k ∧ k < m + n := by
  simp only [seqZ, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k - m).toNat, by omega, by omega⟩

/-! ## Prefixes (`List.IsPrefix`) -/

theorem prefix_nil {l : List α} : List.IsPrefix [] l := List.nil_prefix

theorem prefix_length {l1 l2 : List α} : List.IsPrefix l1 l2 → l1.length ≤ l2.length :=
  List.IsPrefix.length_le

theorem prefix_app_r {l1 l2 l3 : List α} : List.IsPrefix l1 l2 → List.IsPrefix l1 (l2 ++ l3) :=
  fun h => h.trans (List.prefix_append l2 l3)

theorem prefix_app {k l1 l2 : List α} : List.IsPrefix l1 l2 → List.IsPrefix (k ++ l1) (k ++ l2) :=
  (List.prefix_append_right_inj k).2

theorem prefix_cons {x : α} {l1 l2 : List α} :
    List.IsPrefix l1 l2 → List.IsPrefix (x :: l1) (x :: l2) := (List.prefix_cons_inj x).2

theorem prefix_take {l : List α} {n : Nat} : List.IsPrefix (l.take n) l := List.take_prefix n l

theorem elem_of_prefix {l1 l2 : List α} {x : α} : x ∈ l1 → List.IsPrefix l1 l2 → x ∈ l2 :=
  fun hx h => h.subset hx

theorem prefix_lookup_Some {l1 l2 : List α} {i : Nat} {x : α} :
    l1[i]? = some x → List.IsPrefix l1 l2 → l2[i]? = some x := by
  rintro hx ⟨k, rfl⟩
  exact lookup_app_l_Some hx

/-! ## Sorting -/

theorem merge_sort_Permutation {le : α → α → Bool} {l : List α} : List.Perm (List.mergeSort l le) l :=
  List.mergeSort_perm l le

theorem StronglySorted_merge_sort {le : α → α → Bool}
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {l : List α} :
    List.Pairwise (fun a b => le a b = true) (List.mergeSort l le) :=
  List.pairwise_mergeSort trans total l

theorem Sorted_merge_sort {le : α → α → Bool}
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {l : List α} :
    List.IsChain (fun a b => le a b = true) (List.mergeSort l le) :=
  (StronglySorted_merge_sort trans total).isChain

theorem Sorted_StronglySorted {R : α → α → Prop} [Trans R R R] {l : List α} :
    List.IsChain R l → List.Pairwise R l := List.IsChain.pairwise

theorem StronglySorted_unique_strong {R : α → α → Prop} {l1 l2 : List α} :
    (∀ x1 x2, x1 ∈ l1 → x2 ∈ l2 → R x1 x2 → R x2 x1 → x1 = x2) →
      List.Pairwise R l1 → List.Pairwise R l2 → List.Perm l1 l2 → l1 = l2 :=
  fun H h1 h2 hp => List.Perm.eq_of_pairwise H h1 h2 hp

end MachCSL.Stdpp

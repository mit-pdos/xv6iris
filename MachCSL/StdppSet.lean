/-
MachCSL: **THE STDPP FINITE-SET LEMMAS** the weak-memory port needs, stated
under their stdpp names (camelCase), over iris-lean's abstract set interface
(`Iris.Std.LawfulSet` / `LawfulFiniteSet`, `Iris/Std/GenSets.lean`).
Inventory: `notes/weak-port-iris-gaps.md` section G2 (the weak files make
about 1000 calls into stdpp's `sets`/`fin_sets`, and 838 `set_solver`
calls, whose tactic is `MachCSL/SetSolver.lean`).

**Representation** (the SC port's choice, kept): Rocq's `gset A` is
`Std.ExtTreeSet A compare` (abbreviated `MachCSL.GSet A` below), whose
`LawfulSet`/`LawfulFiniteSet` instances are iris-lean's
(`Iris/Std/GenSetsInstances.lean`); the key type carries `Ord` +
`Std.TransOrd` + `Std.LawfulEqOrd` where Rocq's carries `Countable` (G4).
Every lemma here is stated for ANY `[LawfulSet S A]` (or
`[LawfulFiniteSet S A]`), so it applies to `GSet`, to iris-lean's `CoPset`
(masks) and to any other lawful set.

**Name map** (stdpp → here; the `_L` Leibniz variants merge into the plain
name, since sets are compared with `=`):

| stdpp | Lean |
|---|---|
| `elem_of_union` / `_l` / `_r`, `not_elem_of_union` | `elemOfUnion` / `elemOfUnionL` / `elemOfUnionR`, `notElemOfUnion` |
| `elem_of_singleton`, `not_elem_of_singleton` | `elemOfSingleton`, `notElemOfSingleton` |
| `elem_of_empty`, `not_elem_of_empty` | `elemOfEmpty`, `notElemOfEmpty` |
| `elem_of_intersection`, `elem_of_difference`, `not_elem_of_difference` | `elemOfIntersection`, `elemOfDifference`, `notElemOfDifference` |
| `elem_of_subseteq`, `elem_of_weaken`, `elem_of_disjoint`, `set_eq` | `elemOfSubseteq`, `elemOfWeaken`, `elemOfDisjoint`, `setEq` |
| `elem_of_list_to_set`, `list_to_set_nil/cons/app` | `elemOfListToSet`, `listToSetNil/Cons/App` |
| `empty_subseteq`, `singleton_subseteq_l`, `singleton_subseteq` | `emptySubseteq`, `singletonSubseteqL`, `singletonSubseteq` |
| `union_subseteq`, `union_least`, `union_subseteq_l/r`, `union_mono(_l/_r)` | `unionSubseteq`, `unionLeast`, `unionSubseteqL/R`, `unionMono(L/R)` |
| `intersection_subseteq_l/r`, `subseteq_difference_l`, `difference_subseteq` | `intersectionSubseteqL/R`, `subseteqDifferenceL`, `differenceSubseteq` |
| `subseteq_empty`, `subseteq_antisym` (`anti_symm`), `subseteq_trans` (`transitivity`) | `subseteqEmpty`, `subseteqAntisymm`, `subseteqTrans` |
| `union_empty_l/r(_L)`, `union_comm(_L)`, `union_assoc(_L)`, `union_idemp(_L)` | `unionEmptyL/R`, `unionComm`, `unionAssoc`, `unionIdemp` |
| `intersection_empty_l/r`, `intersection_comm` | `intersectionEmptyL/R`, `intersectionComm` |
| `difference_empty`, `difference_diag`, `difference_disjoint(_L)`, `union_difference(_L)`, `difference_union` | `differenceEmpty`, `differenceDiag`, `differenceDisjoint`, `unionDifference`, `differenceUnion` |
| `disjoint_singleton_l/r`, `disjoint_union_l/r`, `disjoint_sym` | `disjointSingletonL/R`, `disjointUnionL/R`, `disjointSym` |
| `⋃ l`, `union_list_nil/cons`, `elem_of_union_list` | `unionList l`, `unionListNil/Cons`, `elemOfUnionList` |
| `elements`, `elem_of_elements`, `elements_empty`, `NoDup_elements` | `FiniteSet.toList`, `elemOfElements`, `elementsEmpty`, `nodupElements` |
| `size_empty`, `size_empty_inv`, `size_singleton`, `size_list_to_set` | `sizeEmpty`, `sizeEmptyInv`, `sizeSingleton`, `sizeListToSet` |
| `subseteq_size`, `size_difference`, `size_union` | `subseteqSize`, `sizeDifference`, `sizeUnion` |
| `elem_of_filter`, `filter_union(_L)`, `filter_empty(_L)`, `filter_singleton` | `elemOfFilter`, `filterUnion`, `filterEmpty`, `filterSingleton` |

**Deviations from Rocq** (spelling, not design):

* stdpp's `filter P X` takes a decidable `Prop` predicate; iris-lean's
  `FiniteSet.filter` takes `p : A → Bool`, so `elemOfFilter` reads
  `p x = true`.  A Rocq `filter (λ x, P x)` becomes `filter (fun x => decide (P x))`.
* stdpp's `⋃` over a list is `unionList` (a `foldr`), defined here.
* `fin_to_set` (G5), the `set_map`/`set_bind`/`set_fold` families (0 weak
  uses) and `gset_disj` (iris-lean's `DisjointLeibnizSet`, a camera) are not
  here.
* The stdpp lemma's explicit arguments are implicit here, except where a
  premise would otherwise leave them undetermined; the order of the
  hypotheses is stdpp's.
-/
import Iris.Std.GenSets
import Iris.Std.GenSetsInstances

namespace MachCSL

open Iris.Std Iris.Std.LawfulSet

/-- Rocq's `gset A`: the SC port's finite-set representation. -/
abbrev GSet (A : Type _) [Ord A] : Type _ := Std.ExtTreeSet A compare

section Sets

variable {S : Type _} {A : Type _} [LawfulSet S A]

/-! ### Membership -/

theorem elemOfUnion {X Y : S} {x : A} : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y := mem_union
theorem elemOfUnionL {X Y : S} {x : A} (h : x ∈ X) : x ∈ X ∪ Y := mem_union.2 (.inl h)
theorem elemOfUnionR {X Y : S} {x : A} (h : x ∈ Y) : x ∈ X ∪ Y := mem_union.2 (.inr h)
theorem notElemOfUnion {X Y : S} {x : A} : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y := by
  rw [mem_union]; exact not_or
theorem elemOfSingleton {x y : A} : x ∈ ({y} : S) ↔ x = y := mem_singleton
theorem notElemOfSingleton {x y : A} : x ∉ ({y} : S) ↔ x ≠ y := by
  rw [mem_singleton]
theorem elemOfEmpty {x : A} : x ∈ (∅ : S) ↔ False := ⟨fun h => mem_empty h, False.elim⟩
theorem notElemOfEmpty {x : A} : x ∉ (∅ : S) := mem_empty
theorem elemOfIntersection {X Y : S} {x : A} : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y := mem_inter
theorem elemOfDifference {X Y : S} {x : A} : x ∈ X \ Y ↔ x ∈ X ∧ x ∉ Y := mem_diff
theorem notElemOfDifference {X Y : S} {x : A} : x ∉ X \ Y ↔ x ∉ X ∨ x ∈ Y := by
  rw [mem_diff]; constructor
  · intro h; by_cases hx : x ∈ X
    · exact .inr (Classical.byContradiction fun hy => h ⟨hx, hy⟩)
    · exact .inl hx
  · rintro (h | h) ⟨h1, h2⟩
    · exact h h1
    · exact h2 h

theorem elemOfSubseteq {X Y : S} : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := Iff.rfl
theorem elemOfWeaken {X Y : S} {x : A} (h : x ∈ X) (hs : X ⊆ Y) : x ∈ Y := hs x h
theorem elemOfDisjoint {X Y : S} : X ## Y ↔ ∀ x, x ∈ X → x ∈ Y → False :=
  ⟨fun h x h1 h2 => h x ⟨h1, h2⟩, fun h x ⟨h1, h2⟩ => h x h1 h2⟩
theorem setEq {X Y : S} : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y :=
  ⟨fun h _ => h ▸ Iff.rfl, LawfulSet.ext⟩

theorem elemOfListToSet {x : A} {l : List A} : x ∈ (ofList l : S) ↔ x ∈ l := mem_ofList.symm
theorem listToSetNil : (ofList [] : S) = ∅ := ofList_nil
theorem listToSetCons {x : A} {l : List A} : (ofList (x :: l) : S) = {x} ∪ ofList l := by
  rw [ofList_cons, insert_union]
theorem listToSetApp {l1 l2 : List A} : (ofList (l1 ++ l2) : S) = ofList l1 ∪ ofList l2 :=
  ofList_concat

/-! ### Inclusion -/

theorem emptySubseteq {X : S} : (∅ : S) ⊆ X := empty_subset
theorem singletonSubseteqL {x : A} {X : S} : ({x} : S) ⊆ X ↔ x ∈ X :=
  ⟨fun h => h x (mem_singleton.2 rfl), fun h y hy => (mem_singleton.1 hy) ▸ h⟩
theorem singletonSubseteq {x y : A} : ({x} : S) ⊆ {y} ↔ x = y := by
  rw [singletonSubseteqL, mem_singleton]
theorem unionSubseteq {X Y Z : S} : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
  ⟨fun h => ⟨fun x hx => h x (mem_union.2 (.inl hx)), fun x hx => h x (mem_union.2 (.inr hx))⟩,
   fun ⟨h1, h2⟩ x hx => (mem_union.1 hx).elim (h1 x) (h2 x)⟩
theorem unionLeast {X Y Z : S} (h1 : X ⊆ Z) (h2 : Y ⊆ Z) : X ∪ Y ⊆ Z := unionSubseteq.2 ⟨h1, h2⟩
theorem unionSubseteqL {X Y : S} : X ⊆ X ∪ Y := union_subset_left
theorem unionSubseteqR {X Y : S} : Y ⊆ X ∪ Y := union_subset_right
theorem unionMono {X1 X2 Y1 Y2 : S} (h1 : X1 ⊆ X2) (h2 : Y1 ⊆ Y2) : X1 ∪ Y1 ⊆ X2 ∪ Y2 :=
  fun x hx => (mem_union.1 hx).elim (fun h => mem_union.2 (.inl (h1 x h)))
    (fun h => mem_union.2 (.inr (h2 x h)))
theorem unionMonoL {X1 X2 Y : S} (h : X1 ⊆ X2) : X1 ∪ Y ⊆ X2 ∪ Y := unionMono h subset_refl
theorem unionMonoR {X Y1 Y2 : S} (h : Y1 ⊆ Y2) : X ∪ Y1 ⊆ X ∪ Y2 := unionMono subset_refl h
theorem intersectionSubseteqL {X Y : S} : X ∩ Y ⊆ X := inter_subset_left
theorem intersectionSubseteqR {X Y : S} : X ∩ Y ⊆ Y := inter_subset_right
theorem differenceSubseteq {X Y : S} : X \ Y ⊆ X := diff_subset_left
theorem subseteqDifferenceL {X Y Z : S} (h : X ⊆ Z) : X \ Y ⊆ Z :=
  subset_trans diff_subset_left h
theorem subseteqEmpty {X : S} : X ⊆ ∅ ↔ X = ∅ :=
  ⟨fun h => LawfulSet.ext fun x => ⟨fun hx => h x hx, fun hx => (mem_empty hx).elim⟩,
   fun h => h ▸ subset_refl⟩
theorem subseteqAntisymm {X Y : S} (h1 : X ⊆ Y) (h2 : Y ⊆ X) : X = Y := eq_subset h1 h2
theorem subseteqTrans {X Y Z : S} (h1 : X ⊆ Y) (h2 : Y ⊆ Z) : X ⊆ Z := subset_trans h1 h2

/-! ### Algebra -/

theorem unionEmptyL {X : S} : ∅ ∪ X = X := union_empty_left
theorem unionEmptyR {X : S} : X ∪ ∅ = X := union_empty_right
theorem unionComm {X Y : S} : X ∪ Y = Y ∪ X := union_comm
theorem unionAssoc {X Y Z : S} : X ∪ (Y ∪ Z) = X ∪ Y ∪ Z := union_assoc
theorem unionIdemp {X : S} : X ∪ X = X := union_idem
theorem intersectionEmptyL {X : S} : ∅ ∩ X = ∅ := inter_empty_left
theorem intersectionEmptyR {X : S} : X ∩ ∅ = ∅ := inter_empty_right
theorem intersectionComm {X Y : S} : X ∩ Y = Y ∩ X := inter_comm
theorem differenceEmpty {X : S} : X \ ∅ = X := diff_empty
theorem differenceDiag {X : S} : X \ X = ∅ := diff_all
theorem differenceDisjoint {X Y : S} (h : X ## Y) : X \ Y = X := diff_subset_disj h
theorem unionDifference {X Y : S} (h : X ⊆ Y) : Y = X ∪ Y \ X := (subset_union_diff h).symm
theorem differenceUnion {X Y : S} : X \ Y ∪ Y = X ∪ Y := by
  refine LawfulSet.ext fun x => ?_
  simp only [mem_union, mem_diff]
  by_cases h : x ∈ Y <;> simp [h]

theorem disjointSingletonL {x : A} {X : S} : ({x} : S) ## X ↔ x ∉ X := disjoint_singleton_left
theorem disjointSingletonR {x : A} {X : S} : X ## ({x} : S) ↔ x ∉ X := disjoint_singleton_right
theorem disjointUnionL {X Y Z : S} : (X ∪ Y) ## Z ↔ X ## Z ∧ Y ## Z := disjoint_union_left
theorem disjointUnionR {X Y Z : S} : Z ## (X ∪ Y) ↔ Z ## X ∧ Z ## Y := disjoint_union_right
theorem disjointSym {X Y : S} (h : X ## Y) : Y ## X := disjoint_symm h

/-! ### Union of a list of sets (stdpp `⋃`) -/

/-- stdpp's `⋃ Xs` (`union_list`): the union of a list of sets. -/
def unionList (Xs : List S) : S := Xs.foldr (· ∪ ·) ∅

theorem unionListNil : unionList ([] : List S) = ∅ := rfl
theorem unionListCons {X : S} {Xs : List S} : unionList (X :: Xs) = X ∪ unionList Xs := rfl
theorem elemOfUnionList {Xs : List S} {x : A} : x ∈ unionList Xs ↔ ∃ X, X ∈ Xs ∧ x ∈ X := by
  induction Xs with
  | nil => simp only [unionList, List.foldr_nil, List.not_mem_nil, false_and, exists_false,
      iff_false]; exact mem_empty
  | cons Y Ys ih =>
    rw [unionListCons, mem_union, ih]
    constructor
    · rintro (h | ⟨X, hX, hx⟩)
      · exact ⟨Y, List.mem_cons_self, h⟩
      · exact ⟨X, List.mem_cons_of_mem _ hX, hx⟩
    · rintro ⟨X, hX, hx⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact .inl hx
      · exact .inr ⟨X, hX, hx⟩

end Sets

section FinSets

variable {S : Type _} {A : Type _} [LawfulFiniteSet S A]

open FiniteSet

/-! ### Elements, size, filter -/

theorem elemOfElements {X : S} {x : A} : x ∈ toList X ↔ x ∈ X := FiniteSet.mem_toList
theorem elementsEmpty : toList (∅ : S) = [] := FiniteSet.toList_empty
theorem nodupElements {X : S} : (toList X).Nodup := FiniteSet.toList_nodup

theorem sizeEmpty : size (∅ : S) = 0 := size_empty.2 rfl
theorem sizeEmptyInv {X : S} (h : size X = 0) : X = ∅ := size_empty.1 h
theorem sizeSingleton {x : A} : size ({x} : S) = 1 := size_singleton
theorem sizeUnion {X Y : S} (h : X ## Y) : size (X ∪ Y) = size X + size Y := (size_union h).symm
theorem subseteqSize {X Y : S} (h : X ⊆ Y) : size X ≤ size Y := size_subset h
theorem sizeDifference {X Y : S} (h : Y ⊆ X) : size (X \ Y) = size X - size Y := by
  have hd : (X \ Y) ## Y := fun x ⟨h1, h2⟩ => (mem_diff.1 h1).2 h2
  have hu : (X \ Y) ∪ Y = X := by
    refine LawfulSet.ext fun x => ?_
    rw [mem_union, mem_diff]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact h x h2
    · intro hx; by_cases hy : x ∈ Y
      · exact .inr hy
      · exact .inl ⟨hx, hy⟩
  have := size_union hd
  rw [hu] at this
  omega
theorem sizeListToSet {l : List A} (h : l.Nodup) : size (ofList l : S) = l.length := by
  unfold size
  exact ((toList_ofList (S := S) h).length_eq).symm

theorem elemOfFilter {p : A → Bool} {X : S} {x : A} : x ∈ filter p X ↔ p x = true ∧ x ∈ X := by
  rw [mem_filter]; exact And.comm
theorem filterUnion {p : A → Bool} {X Y : S} : filter p (X ∪ Y) = filter p X ∪ filter p Y :=
  filter_union p X Y
theorem filterEmpty {p : A → Bool} : filter p (∅ : S) = ∅ := filter_empty p
theorem filterSingleton {p : A → Bool} {x : A} :
    filter p ({x} : S) = if p x then {x} else ∅ := filter_singleton p x

end FinSets

end MachCSL

/-
MachCSL: **THE STDPP FINITE-MAP LEMMAS** the weak-memory port needs, stated
under their stdpp names (camelCase), over iris-lean's abstract map interface
(`Iris.Std.LawfulPartialMap` / `LawfulFiniteMap`, `Iris/Std/PartialMap.lean`).
Inventory: `notes/weak-port-iris-gaps.md` section G2 (the weak files make
737 calls to 57 distinct `fin_maps`/`fin_map_dom` names; the set side and
`set_solver` are `MachCSL/StdppSet.lean` and `MachCSL/SetSolver.lean`).

**Representation** (the SC port's choice, kept): Rocq's `gmap K V` is
`Std.ExtTreeMap K V compare`, written `MachCSL.GMapF K V` (the type-constructor
form, which is what `MachCSL.RegMapF` is at `K := Nat`; see `GMapF` for why), through
iris-lean's `LawfulFiniteMap` instance (`Iris/Std/HeapInstances.lean`), and
the operations are iris-lean's `PartialMap` ones -- the spelling the whole SC
tree already uses (1174 `get?`, 385 `insert` sites).  Rocq's `dom m : gset K`
is `FiniteMap.dom_set m`, whose result type is any lawful set (`GSet K` in
practice; the lemmas leave it generic so `rw` fixes it from the goal).  Every
lemma is stated for ANY `[LawfulPartialMap M K]` (`[LawfulFiniteMap M K]`
when it needs `toList`/`dom`), so it applies to `RegMapF`, `AddrMapF`,
`StampMapF` and `GMapF` alike.

**Spelling map** (Rocq → Lean): `m !! i` → `get? m i`; `<[i:=x]> m` →
`insert m i x`; `delete i m` → `delete m i`; `{[i := x]}` → `{[i := x]}`
(`open Iris.Std.PartialMap`); `m1 ∪ m2` / `∖` / `∩` / `⊆` / `##ₘ` → the
same symbols; `f <$> m` → `PartialMap.map f m`; `filter P m` →
`PartialMap.filter φ m` (`φ : K → V → Bool`); `union_with f` →
`PartialMap.merge op`; `map_to_list` → `FiniteMap.toList`; `list_to_map` →
`PartialMap.ofList`; `gset_to_gmap x X` → `FiniteMap.ofSet x X`; `kmap` →
`FiniteMap.kmap`; `is_Some (m !! i)` → `(get? m i).isSome`.

**Name map** (stdpp → here; `_L` variants merge into the plain name):

| stdpp | Lean |
|---|---|
| `lookup_empty`, `lookup_insert`, `lookup_insert_ne`, `lookup_insert_Some/None/is_Some` | `lookupEmpty`, `lookupInsert`, `lookupInsertNe`, `lookupInsertSome/None/IsSome` |
| `lookup_singleton`, `_ne`, `_Some`, `_None` | `lookupSingleton`, `lookupSingletonNe`, `lookupSingletonSome`, `lookupSingletonNone` |
| `lookup_delete`, `_ne`, `_Some`, `_None` | `lookupDelete`, `lookupDeleteNe`, `lookupDeleteSome`, `lookupDeleteNone` |
| `lookup_union`, `_l`, `_r`, `_Some_l`, `_Some`, `_None`, `lookup_union_with` | `lookupUnion`, `lookupUnionL`, `lookupUnionR`, `lookupUnionSomeL`, `lookupUnionSome`, `lookupUnionNone`, `lookupUnionWith` |
| `lookup_difference`, `_Some`, `_None`, `lookup_intersection` | `lookupDifference`, `lookupDifferenceSome`, `lookupDifferenceNone`, `lookupIntersection` |
| `lookup_fmap`, `map_lookup_filter`, `map_lookup_filter_Some/None` | `lookupFmap`, `mapLookupFilter`, `mapLookupFilterSome/None` |
| `lookup_weaken`, `map_subseteq_spec`, `map_eq`, `map_eq_iff` | `lookupWeaken`, `mapSubseteqSpec`, `mapEq`, `mapEqIff` |
| `insert_union_singleton_l/r`, `insert_union_l`, `insert_id`, `insert_insert`, `insert_commute` | `insertUnionSingletonL/R`, `insertUnionL`, `insertId`, `insertInsert`, `insertCommute` |
| `insert_empty`, `insert_non_empty`, `insert_mono`, `insert_subseteq`, `insert_subseteq_r` | `insertEmpty`, `insertNonEmpty`, `insertMono`, `insertSubseteq`, `insertSubseteqR` |
| `delete_notin`, `delete_idemp`, `delete_insert`, `delete_insert_ne`, `delete_insert_delete` | `deleteNotin`, `deleteIdemp`, `deleteInsert`, `deleteInsertNe`, `deleteInsertDelete` |
| `insert_delete`, `insert_delete_insert`, `delete_empty`, `delete_singleton`, `delete_subseteq` | `insertDelete`, `insertDeleteInsert`, `deleteEmpty`, `deleteSingleton`, `deleteSubseteq` |
| `map_empty`, `map_union_empty`/`left_id_L`/`right_id_L`, `map_union_assoc`, `map_union_comm` | `mapEmpty`, `mapUnionEmptyL/R`, `mapUnionAssoc`, `mapUnionComm` |
| `map_union_subseteq_l/r`, `map_difference_diag`, `map_difference_empty` | `mapUnionSubseteqL/R`, `mapDifferenceDiag`, `mapDifferenceEmpty` |
| `map_disjoint_spec`, `map_disjoint_empty_l/r`, `map_disjoint_singleton_l/r`, `map_disjoint_sym` | `mapDisjointSpec`, `mapDisjointEmptyL/R`, `mapDisjointSingletonL/R`, `mapDisjointSym` |
| `fmap_empty`, `fmap_insert`, `fmap_delete`, `fmap_union` | `fmapEmpty`, `fmapInsert`, `fmapDelete`, `fmapUnion` |
| `elem_of_dom`, `elem_of_dom_2`, `not_elem_of_dom(_1/_2)` | `elemOfDom`, `elemOfDom2`, `notElemOfDom(1/2)` |
| `dom_empty(_L)`, `dom_empty_iff(_L)`, `dom_empty_inv(_L)`, `dom_singleton(_L)`, `dom_insert(_L)` | `domEmpty`, `domEmptyIff`, `domEmptyInv`, `domSingleton`, `domInsert` |
| `dom_delete(_L)`, `dom_union(_L)`, `dom_difference(_L)`, `dom_intersection(_L)`, `dom_fmap(_L)` | `domDelete`, `domUnion`, `domDifference`, `domIntersection`, `domFmap` |
| `dom_filter_subseteq`, `dom_list_to_map(_L)`, `subseteq_dom`, `map_disjoint_dom`, `dom_gset_to_gmap` | `domFilterSubseteq`, `domListToMap`, `subseteqDom`, `mapDisjointDom`, `domGsetToGmap` |
| `elem_of_map_to_list`, `map_to_list_empty`, `NoDup_fst_map_to_list` | `elemOfMapToList`, `mapToListEmpty`, `nodupFstMapToList` |
| `elem_of_list_to_map_1/2`, `not_elem_of_list_to_map`, `lookup_gset_to_gmap(_Some/_None)` | `elemOfListToMap1/2`, `notElemOfListToMap`, `lookupGsetToGmap(Some/None)` |
| `lookup_kmap`, `lookup_kmap_None`, `map_ind` | `lookupKmap`, `lookupKmapNone`, `mapInd` |

**Deviations from Rocq** (spelling, not design):

* `union_with f` (stdpp `f : A → A → option A`) is iris-lean's
  `merge op` (`op : K → V → V → V`, total): `lookupUnionWith` is
  `Option.merge`.  A Rocq `union_with` whose `f` can return `None` has no
  direct counterpart and must be restated.
* `filter P m` takes `φ : K → V → Bool` (stdpp: a decidable `Prop` on
  pairs); `omap` is `PartialMap.filterMap` (`V → Option V`, value type
  preserved) or `bindAlter`.
* `map_fold` is `FiniteMap.mapFold` (a fold over `toList`, in unspecified
  order); stdpp's `map_fold_ind` / `map_fold_insert_L` are not ported (0
  weak uses).  `lookup_total` (`!!!`) on maps is `PartialMap.getD` (0 map
  uses; the 437 weak `!!!` are lists, G3).
* Explicit stdpp arguments are implicit here; premises keep stdpp's order.
-/
import MachCSL.StdppSet
import Iris.Std.PartialMap
import Iris.Std.HeapInstances

namespace MachCSL

open Iris.Std Iris.Std.PartialMap Iris.Std.LawfulPartialMap

/-- Rocq's `gmap K` as a TYPE CONSTRUCTOR (`MachCSL.RegMapF` is `GMapF Nat`): write a
map's type as `GMapF K V`, never as `Std.ExtTreeMap K V compare`, or the lemmas'
`M V` (`M : Type → Type`) cannot be unified with it (a higher-order pattern
Lean does not solve). -/
abbrev GMapF (K : Type _) [Ord K] : Type _ → Type _ := fun V => Std.ExtTreeMap K V compare

section Maps

variable {K : Type _} {M : Type _ → Type _} [LawfulPartialMap M K] {V V' : Type _}

/-! ### Lookup -/

theorem lookupEmpty {i : K} : get? (∅ : M V) i = none := get?_empty i
theorem lookupInsert {m : M V} {i : K} {x : V} : get? (insert m i x) i = some x :=
  get?_insert_eq rfl
theorem lookupInsertNe {m : M V} {i j : K} {x : V} (h : i ≠ j) :
    get? (insert m i x) j = get? m j := get?_insert_ne h
theorem lookupInsertSome {m : M V} {i j : K} {x y : V} :
    get? (insert m i x) j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ get? m j = some y) := by
  by_cases h : i = j
  · subst h; rw [get?_insert_eq rfl]; simp
  · rw [get?_insert_ne h]; simp [h]
theorem lookupInsertNone {m : M V} {i j : K} {x : V} :
    get? (insert m i x) j = none ↔ get? m j = none ∧ i ≠ j := by
  by_cases h : i = j
  · subst h; rw [get?_insert_eq rfl]; simp
  · rw [get?_insert_ne h]; simp [h]
theorem lookupInsertIsSome {m : M V} {i j : K} {x : V} :
    (get? (insert m i x) j).isSome ↔ i = j ∨ (i ≠ j ∧ (get? m j).isSome) := by
  by_cases h : i = j
  · subst h; rw [get?_insert_eq rfl]; simp
  · rw [get?_insert_ne h]; simp [h]

theorem lookupSingleton {i : K} {x : V} : get? ({[i := x]} : M V) i = some x :=
  get?_singleton_eq rfl
theorem lookupSingletonNe {i j : K} {x : V} (h : i ≠ j) : get? ({[i := x]} : M V) j = none :=
  get?_singleton_ne h
theorem lookupSingletonSome {i j : K} {x y : V} :
    get? ({[i := x]} : M V) j = some y ↔ i = j ∧ x = y := by
  by_cases h : i = j
  · subst h; rw [get?_singleton_eq rfl]; simp
  · rw [get?_singleton_ne h]; simp [h]
theorem lookupSingletonNone {i j : K} {x : V} : get? ({[i := x]} : M V) j = none ↔ i ≠ j := by
  by_cases h : i = j
  · subst h; rw [get?_singleton_eq rfl]; simp
  · rw [get?_singleton_ne h]; simp [h]

theorem lookupDelete {m : M V} {i : K} : get? (delete m i) i = none := get?_delete_eq rfl
theorem lookupDeleteNe {m : M V} {i j : K} (h : i ≠ j) : get? (delete m i) j = get? m j :=
  get?_delete_ne h
theorem lookupDeleteSome {m : M V} {i j : K} {y : V} :
    get? (delete m i) j = some y ↔ i ≠ j ∧ get? m j = some y := by
  by_cases h : i = j
  · subst h; rw [get?_delete_eq rfl]; simp
  · rw [get?_delete_ne h]; simp [h]
theorem lookupDeleteNone {m : M V} {i j : K} :
    get? (delete m i) j = none ↔ i = j ∨ get? m j = none := by
  by_cases h : i = j
  · subst h; rw [get?_delete_eq rfl]; simp
  · rw [get?_delete_ne h]; simp [h]

theorem lookupUnion {m1 m2 : M V} {i : K} :
    get? (m1 ∪ m2) i = (get? m1 i).orElse (fun _ => get? m2 i) := get?_union
theorem lookupUnionL {m1 m2 : M V} {i : K} (h : get? m2 i = none) :
    get? (m1 ∪ m2) i = get? m1 i := by
  rw [get?_union, h]; cases get? m1 i <;> rfl
theorem lookupUnionR {m1 m2 : M V} {i : K} (h : get? m1 i = none) :
    get? (m1 ∪ m2) i = get? m2 i := by
  rw [get?_union, h]; rfl
theorem lookupUnionSomeL {m1 m2 : M V} {i : K} {x : V} (h : get? m1 i = some x) :
    get? (m1 ∪ m2) i = some x := by
  rw [get?_union, h]; rfl
theorem lookupUnionSome {m1 m2 : M V} {i : K} {x : V} :
    get? (m1 ∪ m2) i = some x ↔ get? m1 i = some x ∨ (get? m1 i = none ∧ get? m2 i = some x) := by
  rw [get?_union]; cases get? m1 i <;> simp [Option.orElse]
theorem lookupUnionNone {m1 m2 : M V} {i : K} :
    get? (m1 ∪ m2) i = none ↔ get? m1 i = none ∧ get? m2 i = none := get?_union_none
theorem lookupUnionWith {op : K → V → V → V} {m1 m2 : M V} {i : K} :
    get? (merge op m1 m2) i = Option.merge (op i) (get? m1 i) (get? m2 i) := get?_merge

theorem lookupDifference {m1 m2 : M V} {i : K} :
    get? (m1 \ m2) i = if (get? m2 i).isSome then none else get? m1 i := get?_difference
theorem lookupDifferenceSome {m1 m2 : M V} {i : K} {x : V} :
    get? (m1 \ m2) i = some x ↔ get? m1 i = some x ∧ get? m2 i = none := by
  rw [get?_difference]; cases get? m2 i <;> simp
theorem lookupDifferenceNone {m1 m2 : M V} {i : K} :
    get? (m1 \ m2) i = none ↔ get? m1 i = none ∨ (get? m2 i).isSome := by
  rw [get?_difference]; cases get? m2 i <;> simp
theorem lookupIntersection {m1 m2 : M V} {i : K} :
    get? (m1 ∩ m2) i = if (get? m2 i).isSome then get? m1 i else none := get?_intersection

theorem lookupFmap {f : V → V'} {m : M V} {i : K} :
    get? (PartialMap.map f m) i = (get? m i).map f := get?_map
theorem mapLookupFilter {φ : K → V → Bool} {m : M V} {i : K} :
    get? (PartialMap.filter φ m) i = (get? m i).bind (fun v => if φ i v then some v else none) :=
  get?_filter
theorem mapLookupFilterSome {φ : K → V → Bool} {m : M V} {i : K} {x : V} :
    get? (PartialMap.filter φ m) i = some x ↔ get? m i = some x ∧ φ i x = true := by
  rw [get?_filter]
  cases h : get? m i with
  | none => simp
  | some v => by_cases hp : φ i v = true <;> simp [hp] <;> grind
theorem mapLookupFilterNone {φ : K → V → Bool} {m : M V} {i : K} :
    get? (PartialMap.filter φ m) i = none ↔ ∀ x, get? m i = some x → φ i x = false := by
  rw [get?_filter]
  cases h : get? m i with
  | none => simp
  | some v => by_cases hp : φ i v = true <;> simp [hp]

theorem mapSubseteqSpec {m1 m2 : M V} :
    m1 ⊆ m2 ↔ ∀ i x, get? m1 i = some x → get? m2 i = some x := Iff.rfl
theorem lookupWeaken {m1 m2 : M V} {i : K} {x : V} (h : get? m1 i = some x) (hs : m1 ⊆ m2) :
    get? m2 i = some x := hs i x h
theorem mapEqIff {m1 m2 : M V} : m1 = m2 ↔ ∀ i, get? m1 i = get? m2 i :=
  ⟨fun h _ => h ▸ rfl, fun h => equiv_iff_eq.mp h⟩
theorem mapEq {m1 m2 : M V} (h : ∀ i, get? m1 i = get? m2 i) : m1 = m2 := equiv_iff_eq.mp h
theorem mapEmpty {m : M V} : m = ∅ ↔ ∀ i, get? m i = none := eq_empty_iff

/-! ### Insert and delete -/

theorem insertUnionSingletonL {m : M V} {i : K} {x : V} : insert m i x = {[i := x]} ∪ m := by
  refine mapEq fun j => ?_
  rw [get?_union]
  by_cases h : i = j
  · rw [get?_insert_eq h, get?_singleton_eq h]; rfl
  · rw [get?_insert_ne h, get?_singleton_ne h]; rfl
theorem insertUnionSingletonR {m : M V} {i : K} {x : V} (h : get? m i = none) :
    insert m i x = m ∪ {[i := x]} := by
  refine mapEq fun j => ?_
  rw [get?_union]
  by_cases hj : i = j
  · subst hj; rw [get?_insert_eq rfl, get?_singleton_eq rfl, h]; rfl
  · rw [get?_insert_ne hj, get?_singleton_ne hj]; cases get? m j <;> rfl
theorem insertUnionL {m1 m2 : M V} {i : K} {x : V} :
    insert (m1 ∪ m2) i x = insert m1 i x ∪ m2 := union_insert_left
theorem insertId {m : M V} {i : K} {x : V} (h : get? m i = some x) : insert m i x = m :=
  insert_get? h
theorem insertInsert {m : M V} {i : K} {x y : V} : insert (insert m i y) i x = insert m i x :=
  insert_insert_same
theorem insertCommute {m : M V} {i j : K} {x y : V} (h : i ≠ j) :
    insert (insert m j y) i x = insert (insert m i x) j y := (insert_insert_comm (Ne.symm h))
theorem insertEmpty {i : K} {x : V} : insert (∅ : M V) i x = {[i := x]} := rfl
theorem insertNonEmpty {m : M V} {i : K} {x : V} : insert m i x ≠ ∅ := insert_ne_empty
theorem insertMono {m1 m2 : M V} {i : K} {x : V} (h : m1 ⊆ m2) :
    insert m1 i x ⊆ insert m2 i x := insert_subset_insert h
theorem insertSubseteq {m : M V} {i : K} {x : V} (h : get? m i = none) : m ⊆ insert m i x :=
  subset_insert h
theorem insertSubseteqR {m1 m2 : M V} {i : K} {x : V} (h : get? m1 i = none) (hs : m1 ⊆ m2) :
    m1 ⊆ insert m2 i x := by
  intro j v hj
  have hij : i ≠ j := fun e => by subst e; rw [h] at hj; cases hj
  rw [get?_insert_ne hij]; exact hs j v hj

theorem deleteNotin {m : M V} {i : K} (h : get? m i = none) : delete m i = m := delete_of_get? h
theorem deleteIdemp {m : M V} {i : K} : delete (delete m i) i = delete m i := delete_delete
theorem deleteInsert {m : M V} {i : K} {x : V} (h : get? m i = none) :
    delete (insert m i x) i = m := delete_insert_cancel h
theorem deleteInsertNe {m : M V} {i j : K} {x : V} (h : i ≠ j) :
    delete (insert m j x) i = insert (delete m i) j x := delete_insert_of_ne (Ne.symm h)
theorem deleteInsertDelete {m : M V} {i : K} {x : V} :
    delete (insert m i x) i = delete m i := delete_insert
theorem insertDelete {m : M V} {i : K} {x : V} (h : get? m i = some x) :
    insert (delete m i) i x = m := insert_delete_cancel h
theorem insertDeleteInsert {m : M V} {i : K} {x : V} :
    insert (delete m i) i x = insert m i x := insert_delete
theorem deleteEmpty {i : K} : delete (∅ : M V) i = ∅ := delete_empty
theorem deleteSingleton {i : K} {x : V} : delete ({[i := x]} : M V) i = ∅ := delete_singleton_eq
theorem deleteSubseteq {m : M V} {i : K} : delete m i ⊆ m := delete_subset_self

/-! ### Union, difference, disjointness -/

theorem mapUnionEmptyL {m : M V} : (∅ : M V) ∪ m = m := union_empty_left
theorem mapUnionEmptyR {m : M V} : m ∪ (∅ : M V) = m := union_empty_right
theorem mapUnionAssoc {m1 m2 m3 : M V} : m1 ∪ (m2 ∪ m3) = m1 ∪ m2 ∪ m3 := by
  refine mapEq fun j => ?_
  simp only [get?_union]
  cases get? m1 j <;> rfl

theorem mapDisjointSpec {m1 m2 : M V} :
    m1 ##ₘ m2 ↔ ∀ i x y, get? m1 i = some x → get? m2 i = some y → False := by
  constructor
  · intro h i x y h1 h2; exact h i ⟨by simp [h1], by simp [h2]⟩
  · intro h i ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h2
    exact h i x y hx hy
theorem mapDisjointSym {m1 m2 : M V} (h : m1 ##ₘ m2) : m2 ##ₘ m1 := PartialMap.disjoint_comm h
theorem mapDisjointEmptyL {m : M V} : (∅ : M V) ##ₘ m := disjoint_empty_left m
theorem mapDisjointEmptyR {m : M V} : m ##ₘ (∅ : M V) := disjoint_empty_right m
theorem mapDisjointSingletonL {m : M V} {i : K} {x : V} :
    ({[i := x]} : M V) ##ₘ m ↔ get? m i = none := by
  rw [mapDisjointSpec]
  constructor
  · intro h; cases hm : get? m i with
    | none => rfl
    | some y => exact (h i x y lookupSingleton hm).elim
  · intro h j a b ha hb
    obtain ⟨rfl, rfl⟩ := lookupSingletonSome.1 ha
    rw [h] at hb; cases hb
theorem mapDisjointSingletonR {m : M V} {i : K} {x : V} :
    m ##ₘ ({[i := x]} : M V) ↔ get? m i = none :=
  ⟨fun h => mapDisjointSingletonL.1 (mapDisjointSym h),
   fun h => mapDisjointSym (mapDisjointSingletonL.2 h)⟩

theorem mapUnionComm {m1 m2 : M V} (h : m1 ##ₘ m2) : m1 ∪ m2 = m2 ∪ m1 := by
  refine mapEq fun j => ?_
  simp only [get?_union]
  cases h1 : get? m1 j <;> cases h2 : get? m2 j <;> try rfl
  exact (mapDisjointSpec.1 h j _ _ h1 h2).elim
theorem mapUnionSubseteqL {m1 m2 : M V} : m1 ⊆ m1 ∪ m2 := fun _ _ h => lookupUnionSomeL h
theorem mapUnionSubseteqR {m1 m2 : M V} (h : m1 ##ₘ m2) : m2 ⊆ m1 ∪ m2 := by
  rw [mapUnionComm h]; exact mapUnionSubseteqL
theorem mapDifferenceDiag {m : M V} : m \ m = ∅ := by
  refine mapEq fun j => ?_
  rw [get?_difference, get?_empty]
  cases get? m j <;> rfl
theorem mapDifferenceEmpty {m : M V} : m \ (∅ : M V) = m := by
  refine mapEq fun j => ?_
  rw [get?_difference, get?_empty]; rfl

/-! ### Fmap -/

theorem fmapEmpty {f : V → V'} : PartialMap.map f (∅ : M V) = (∅ : M V') := map_empty
theorem fmapInsert {f : V → V'} {m : M V} {i : K} {x : V} :
    PartialMap.map f (insert m i x) = insert (PartialMap.map f m) i (f x) := map_insert
theorem fmapDelete {f : V → V'} {m : M V} {i : K} :
    PartialMap.map f (delete m i) = delete (PartialMap.map f m) i := map_delete
theorem fmapUnion {f : V → V'} {m1 m2 : M V} :
    PartialMap.map f (m1 ∪ m2) = PartialMap.map f m1 ∪ PartialMap.map f m2 := map_union

theorem notElemOfListToMap {l : List (K × V)} {i : K} :
    i ∉ l.map Prod.fst ↔ get? (PartialMap.ofList l : M V) i = none := by
  induction l with
  | nil => simp [PartialMap.ofList, get?_empty]
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    rw [LawfulPartialMap.ofList_cons, List.map_cons, List.mem_cons, not_or, ih]
    by_cases h : k = i
    · subst h; rw [get?_insert_eq rfl]; simp
    · rw [get?_insert_ne h]; simp [Ne.symm h]
end Maps

section FinMaps

variable {K : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] {V V' : Type _}
variable {S : Type _} [LawfulSet S K]

open FiniteMap LawfulSet

/-! ### Domain -/

theorem elemOfDom {m : M V} {i : K} : i ∈ (dom_set m : S) ↔ (get? m i).isSome := LawfulFiniteMap.mem_dom_set
theorem elemOfDom2 {m : M V} {i : K} {x : V} (h : get? m i = some x) : i ∈ (dom_set m : S) :=
  LawfulFiniteMap.mem_dom_set.2 (by simp [h])
theorem notElemOfDom {m : M V} {i : K} : i ∉ (dom_set m : S) ↔ get? m i = none := by
  rw [LawfulFiniteMap.mem_dom_set]; simp
theorem notElemOfDom1 {m : M V} {i : K} (h : i ∉ (dom_set m : S)) : get? m i = none :=
  notElemOfDom.1 h
theorem notElemOfDom2 {m : M V} {i : K} (h : get? m i = none) : i ∉ (dom_set m : S) :=
  notElemOfDom.2 h

theorem domEmpty : (dom_set (∅ : M V) : S) = ∅ :=
  LawfulSet.ext fun i => by rw [LawfulFiniteMap.mem_dom_set, get?_empty]; simp [mem_empty]
theorem domEmptyIff {m : M V} : (dom_set m : S) = ∅ ↔ m = ∅ := by
  constructor
  · intro h; refine mapEq fun i => ?_
    have : i ∉ (dom_set m : S) := by rw [h]; exact mem_empty
    rw [notElemOfDom.1 this, get?_empty]
  · intro h; subst h; exact domEmpty
theorem domEmptyInv {m : M V} (h : (dom_set m : S) = ∅) : m = ∅ := domEmptyIff.1 h
theorem domSingleton {i : K} {x : V} : (dom_set ({[i := x]} : M V) : S) = {i} :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_singleton]
    by_cases h : i = j
    · subst h; rw [get?_singleton_eq rfl]; simp
    · rw [get?_singleton_ne h]; simp [Ne.symm h]
theorem domInsert {m : M V} {i : K} {x : V} :
    (dom_set (insert m i x) : S) = {i} ∪ dom_set m :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_union, mem_singleton, LawfulFiniteMap.mem_dom_set]
    by_cases h : i = j
    · subst h; rw [get?_insert_eq rfl]; simp
    · rw [get?_insert_ne h]; simp [Ne.symm h]
theorem domDelete {m : M V} {i : K} : (dom_set (delete m i) : S) = dom_set m \ {i} :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_diff, mem_singleton, LawfulFiniteMap.mem_dom_set]
    by_cases h : i = j
    · subst h; rw [get?_delete_eq rfl]; simp
    · rw [get?_delete_ne h]; simp [Ne.symm h]
theorem domUnion {m1 m2 : M V} : (dom_set (m1 ∪ m2) : S) = dom_set m1 ∪ dom_set m2 :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_union, LawfulFiniteMap.mem_dom_set, LawfulFiniteMap.mem_dom_set, get?_union]
    cases get? m1 j <;> simp [Option.orElse]
theorem domDifference {m1 m2 : M V} : (dom_set (m1 \ m2) : S) = dom_set m1 \ dom_set m2 :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_diff, LawfulFiniteMap.mem_dom_set, LawfulFiniteMap.mem_dom_set, get?_difference]
    cases get? m2 j <;> simp
theorem domIntersection {m1 m2 : M V} : (dom_set (m1 ∩ m2) : S) = dom_set m1 ∩ dom_set m2 :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, mem_inter, LawfulFiniteMap.mem_dom_set, LawfulFiniteMap.mem_dom_set, get?_intersection]
    cases get? m2 j <;> simp
theorem domFmap {f : V → V'} {m : M V} : (dom_set (PartialMap.map f m) : S) = dom_set m :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, LawfulFiniteMap.mem_dom_set, get?_map]; cases get? m j <;> rfl
theorem domFilterSubseteq {φ : K → V → Bool} {m : M V} :
    (dom_set (PartialMap.filter φ m) : S) ⊆ dom_set m := fun j hj => by
  rw [LawfulFiniteMap.mem_dom_set, get?_filter] at hj; rw [LawfulFiniteMap.mem_dom_set]
  cases h : get? m j <;> simp_all
theorem subseteqDom {m1 m2 : M V} (h : m1 ⊆ m2) : (dom_set m1 : S) ⊆ dom_set m2 := fun j hj => by
  rw [LawfulFiniteMap.mem_dom_set] at hj ⊢
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hj
  rw [h j x hx]; rfl
theorem mapDisjointDom {m1 m2 : M V} : m1 ##ₘ m2 ↔ (dom_set m1 : S) ## dom_set m2 := by
  constructor
  · intro h j ⟨h1, h2⟩; rw [LawfulFiniteMap.mem_dom_set] at h1 h2; exact h j ⟨h1, h2⟩
  · intro h j ⟨h1, h2⟩; exact h j ⟨LawfulFiniteMap.mem_dom_set.2 h1, LawfulFiniteMap.mem_dom_set.2 h2⟩
theorem domListToMap {l : List (K × V)} :
    (dom_set (PartialMap.ofList l : M V) : S) = LawfulSet.ofList (l.map Prod.fst) :=
  LawfulSet.ext fun j => by
    rw [LawfulFiniteMap.mem_dom_set, ← mem_ofList]
    induction l with
    | nil => simp [PartialMap.ofList, get?_empty]
    | cons kv l ih =>
      obtain ⟨k, v⟩ := kv
      rw [LawfulPartialMap.ofList_cons, List.map_cons, List.mem_cons, ← ih]
      by_cases h : k = j
      · subst h; rw [get?_insert_eq rfl]; simp
      · rw [get?_insert_ne h]; simp [Ne.symm h]

/-! ### Map to list, list to map, set to map -/

theorem elemOfMapToList {m : M V} {i : K} {x : V} : (i, x) ∈ toList m ↔ get? m i = some x :=
  toList_get
theorem mapToListEmpty : toList (∅ : M V) = [] := toList_empty
theorem nodupFstMapToList {m : M V} : ((toList m).map Prod.fst).Nodup := toList_noDupKeys

theorem elemOfListToMap2 [DecidableEq K] {l : List (K × V)} {i : K} {x : V}
    (h : get? (PartialMap.ofList l : M V) i = some x) : (i, x) ∈ l := LawfulFiniteMap.mem_of_mem_ofList h
theorem elemOfListToMap1 [DecidableEq K] {l : List (K × V)} {i : K} {x : V}
    (hnd : (l.map Prod.fst).Nodup) (h : (i, x) ∈ l) :
    get? (PartialMap.ofList l : M V) i = some x := get?_ofList_some h hnd

section GsetToGmap
variable {S' : Type _} [LawfulFiniteSet S' K]

theorem lookupGsetToGmapSome [DecidableEq K] {a : V} {X : S'} {i : K} (h : i ∈ X) :
    get? (FiniteMap.ofSet (M := M) a X) i = some a := LawfulFiniteMap.get?_ofSet_of_mem h
theorem lookupGsetToGmapNone {a : V} {X : S'} {i : K} (h : i ∉ X) :
    get? (FiniteMap.ofSet (M := M) a X) i = none := LawfulFiniteMap.get?_ofSet_of_not_mem h
theorem lookupGsetToGmap [DecidableEq K] {a : V} {X : S'} {i : K} :
    get? (FiniteMap.ofSet (M := M) a X) i = if i ∈ X then some a else none := by
  split
  · exact LawfulFiniteMap.get?_ofSet_of_mem ‹_›
  · exact LawfulFiniteMap.get?_ofSet_of_not_mem ‹_›
theorem domGsetToGmap {a : V} {X : S'} : (dom_set (FiniteMap.ofSet (M := M) a X) : S') = X :=
  LawfulSet.ext fun j => by
    classical
    rw [LawfulFiniteMap.mem_dom_set]
    by_cases h : j ∈ X
    · rw [LawfulFiniteMap.get?_ofSet_of_mem h]; simp [h]
    · rw [LawfulFiniteMap.get?_ofSet_of_not_mem h]; simp [h]
end GsetToGmap

/-! ### Key renaming, induction -/

theorem lookupKmap {M' : Type _ → Type _} {K' : Type _} [LawfulPartialMap M' K'] [DecidableEq K']
    {f : K → K'} (hf : Function.Injective f) {m : M V} {i : K} :
    get? (FiniteMap.kmap (M' := M') f m) (f i) = get? m i := by
  unfold FiniteMap.kmap
  have hnd := LawfulFiniteMap.noDupKeys_map_key (V := V) hf (toList_noDupKeys (m := m))
  cases h : get? m i with
  | some v =>
    exact get?_ofList_some (List.mem_map.2 ⟨(i, v), toList_get.2 h, rfl⟩) hnd
  | none =>
    refine get?_ofList_none ?_ hnd
    rintro ⟨v, hv⟩
    obtain ⟨⟨k, w⟩, hkw, he⟩ := List.mem_map.1 hv
    simp only [Prod.mk.injEq] at he
    obtain ⟨hk, rfl⟩ := he
    rw [hf hk] at hkw
    have h2 := toList_get.1 hkw
    rw [h] at h2; cases h2
theorem lookupKmapNone {M' : Type _ → Type _} {K' : Type _} [LawfulPartialMap M' K']
    {f : K → K'} {m : M V} {j : K'} (h : ∀ i, f i = j → get? m i = none) :
    get? (FiniteMap.kmap (M' := M') f m) j = none := by
  unfold FiniteMap.kmap
  refine notElemOfListToMap.1 fun hj => ?_
  rw [List.map_map, List.mem_map] at hj
  obtain ⟨⟨k, w⟩, hkw, he⟩ := hj
  have hk : f k = j := he
  have h2 := toList_get.1 hkw
  rw [h k hk] at h2; cases h2
theorem mapInd [DecidableEq K] {P : M V → Prop} (hemp : P ∅)
    (hins : ∀ i x m, get? m i = none → P m → P (insert m i x)) (m : M V) : P m :=
  LawfulFiniteMap.induction_on hemp hins m

end FinMaps

end MachCSL

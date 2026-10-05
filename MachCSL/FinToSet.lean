/-
MachCSL: stdpp's finite-type enumeration at `Fin n` -- `fin_enum`/`enum`
and `fin_to_set` (Rocq stdpp `fin.v` / `finite.v` / `fin_sets.v`; the weak
files' `fin_enum_lookup`, `fin_enum_lookup_nat`, `fin_enum_length` (local
lemmas, `Weak*.v`), `cpu_enum_*`; gap G5/"G8" of
`notes/weak-port-iris-gaps.md`).

THE ONE FINITE TYPE THE WEAK FILES ENUMERATE IS `CPU := fin NCPU`.  Every
`fin_to_set` hit (31) is `(fin_to_set CPU : gset CPU)` under a `[∗ set]`,
every `elem_of_fin_to_set` (6) discharges the membership side condition of
`big_sepS_delete`, and every `enum CPU`/`fin_enum` (60) is the list of
harts in index order with its `lookup`/`length`/`NoDup` facts.  So the
port is `Fin n`-only:

* `finEnum n := List.finRange n` (stdpp `fin_enum n`, and `enum (fin n)`,
  which stdpp's `fin_finite` instance makes the same list);
* `finToSet n : ExtTreeSet (Fin n) compare` (stdpp `fin_to_set (fin n) :
  gset (fin n)`), the `ofList` of that list, so it is a `LawfulFiniteSet`
  and the iris-lean `[∗set]` lemmas apply to it as they do to any
  `ExtTreeSet`; `finToSet_toList_perm` turns `[∗set] ∈ finToSet n` into
  `[∗list] ∈ finEnum n` through `bigSepS_elements` and a permutation.

Decidable `∀ i : Fin n, P i` (stdpp's `Finite`-indexed `Decision`) is core's
`Nat.decidableForallFin`; nothing here.

Name mapping: stdpp `fin_enum`/`fin_to_set` are definitions, so they are
camelCased (`finEnum`, `finToSet`) and lemma names carry them as one
component: `fin_enum_lookup` is `finEnum_lookup`, `elem_of_fin_to_set` is
`elem_of_finToSet`, `NoDup_enum` is `NoDup_finEnum`.

Deviations from Rocq.
1. ONLY `Fin n` (stdpp: any `Finite A`).  A weak `Finite` instance other
   than `fin` gets its own enumeration when ported (there is none in the
   cone; the 3 `Finite` hits are prose about `discrete_fun_included_spec`).
2. `gset (fin n)` IS `ExtTreeSet (Fin n) compare` (core's `Ord (Fin n)`,
   with `TransOrd`/`LawfulEqOrd` from core), the tree's finite-set type.
3. `fin_enum n !! fin_to_nat i` IS `(finEnum n)[i.val]?`.
-/
import Iris.Std.GenSetsInstances

namespace MachCSL

open Std

/-! ## The enumeration -/

/-- stdpp `fin_enum n` (= `enum (fin n)`): the elements of `Fin n` in order. -/
def finEnum (n : Nat) : List (Fin n) := List.finRange n

theorem finEnum_length (n : Nat) : (finEnum n).length = n := List.length_finRange

theorem elem_of_finEnum {n : Nat} (i : Fin n) : i ∈ finEnum n := List.mem_finRange i

theorem NoDup_finEnum (n : Nat) : (finEnum n).Nodup := by
  unfold finEnum
  induction n with
  | zero => rw [List.finRange_zero]; exact List.nodup_nil
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨k, _, hk⟩ := List.mem_map.1 h
      exact Fin.succ_ne_zero k hk
    · exact List.pairwise_map.2 (List.Pairwise.imp (fun hne heq => hne (Fin.succ_inj.1 heq)) ih)

/-- The weak files' `fin_enum_lookup`: hart `i` sits at index `i`. -/
theorem finEnum_lookup {n : Nat} (i : Fin n) : (finEnum n)[i.val]? = some i := by
  unfold finEnum
  have h : i.val < (List.finRange n).length := by rw [List.length_finRange]; exact i.2
  rw [List.getElem?_eq_getElem h, List.getElem_finRange]
  exact congrArg some (Fin.ext rfl)

/-- The weak files' `fin_enum_lookup_nat`: the hart at index `j` is `j`. -/
theorem finEnum_lookup_nat {n : Nat} (j : Nat) (x : Fin n) (h : (finEnum n)[j]? = some x) :
    x.val = j := by
  unfold finEnum at h
  obtain ⟨hj, hx⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem_finRange] at hx
  rw [← hx]
  rfl

/-! ## The set -/

/-- stdpp `fin_to_set (fin n) : gset (fin n)` (deviation 2). -/
def finToSet (n : Nat) : ExtTreeSet (Fin n) compare := ExtTreeSet.ofList (finEnum n) compare

theorem elem_of_finToSet {n : Nat} (i : Fin n) : i ∈ finToSet n := by
  unfold finToSet
  rw [ExtTreeSet.mem_ofList, List.contains_iff_mem]
  exact elem_of_finEnum i

theorem size_finToSet (n : Nat) : (finToSet n).size = n := by
  unfold finToSet
  rw [ExtTreeSet.size_ofList, finEnum_length]
  exact List.Pairwise.imp (fun hne heq => hne (LawfulEqCmp.eq_of_compare heq)) (NoDup_finEnum n)

/-- The set's elements are the enumeration, up to order: the bridge from
`[∗set] c ∈ finToSet n` to `[∗list] c ∈ finEnum n`. -/
theorem finToSet_toList_perm (n : Nat) : (finToSet n).toList.Perm (finEnum n) := by
  have h1 : (finToSet n).toList.Nodup :=
    List.Pairwise.imp (fun h hab => h (LawfulEqCmp.compare_eq_iff_eq.2 hab))
      ExtTreeSet.distinct_toList
  refine List.perm_iff_count.2 fun a => ?_
  rw [List.Nodup.count h1, List.Nodup.count (NoDup_finEnum n),
    if_pos (ExtTreeSet.mem_toList.2 (elem_of_finToSet a)), if_pos (elem_of_finEnum a)]

end MachCSL

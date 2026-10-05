/-
MachCSL: **`set_solver`** -- the replacement for stdpp's `set_solver`, which
the Rocq weak-memory files call 838 times (128 files; the SC files 72
times, replaced there one by one with named lemmas -- `Xv6/BmapDefs` dev. 4,
`Xv6/IcacheEscrowPoolMove` dev. 4 -- which does not scale; see
`notes/weak-port-iris-gaps.md` section G2).

**How it works** (stdpp's own recipe, `set_unfold` + a first-order solver):

1. `set_solver_unfold` (a `simp only … at *`, usable on its own) rewrites every set-valued
   statement, in the goal AND every hypothesis, down to MEMBERSHIP: `x ∈ X ∪
   Y` → `x ∈ X ∨ x ∈ Y`, `∩` → `∧`, `\` → `∧ ¬`, `{y}` → `x = y`, `∅` →
   `False`, `ofList l` (`list_to_set`) → list membership, `X ⊆ Y` → `∀ x, x ∈
   X → x ∈ Y`, `X ## Y` → `∀ x, x ∈ X → x ∈ Y → False`, `X = Y` (sets) → `∀
   x, x ∈ X ↔ x ∈ Y`, `dom_set` of `∅`/`{[i := v]}`/`insert`/`delete`/`∪`/`\`/`∩`/
   `map` → the set operation, then `i ∈ dom_set m` → `(get? m i).isSome`;
   list membership (`::`, `++`, `[]`, `[a]`), `filter`, `toList`
   (`elements`), `⋃` (`unionList`) and `insert`/`delete` on sets likewise.
   The masks (`CoPset`: `∪ ∩ \ {p} ∅ ⊤ ⊆`) get the same treatment.  The
   same pass rewrites every membership to the CONTAINER'S OWN `Membership`
   instance (`setSolver_gsetMem`, `setSolver_coPsetMem`): the generic
   lemmas produce the `LawfulSet`-derived one, which is defeq but which
   `grind` would treat as a different predicate.
2. `grind` closes the resulting first-order goal: congruence closure over
   the membership atoms and the equalities between elements, case splits,
   and E-matching instantiation of the `∀`-hypotheses the unfolding
   produced (a subset or set-equality hypothesis is used at every element the
   goal mentions).

`set_solver [l₁, …]` first rewrites with the extra simp lemmas `lᵢ` (a local
definition to unfold, a characterisation lemma such as Rocq's
`elem_of_lob_succ_of`), as Rocq's `set_solver` picks up `SetUnfold`
instances.  `set_solver!`-style variants are not provided (no Rocq use).

**Coverage** (the test section below: 52 goals, most taken from the weak
files with their Rocq file:line): membership/inclusion/equality/disjointness over
`∪ ∩ \ {x} ∅`, with hypotheses of the same shapes; list membership of
literal lists and `NoDup`-derived disequalities; `list_to_set`; `dom` of
inserted/deleted/singleton maps; masks.  **What it does not do** (as
Rocq's): `size` arithmetic, `set_fold`/`map_fold`, reasoning through an
opaque function (give its characterisation as an extra lemma), lookups
under `insert` (use `simp [lookupInsert…]`), and set statements hidden
under an Iris modality (state the pure fact first, as the gaps note
recommends: `set_solver` in proof mode cost minutes in Rocq).

**Deviations from Rocq**: Rocq's tactic is a `naive_solver` loop over the
`SetUnfold` type-class database; this one is a fixed simp set plus `grind`.
It fails (rather than looping) on goals it cannot close.  Rocq's
`set_solver by tac` is `set_solver [lemmas]`, or `tac` first.  Rocq's
`gmap K V` must be written `GMapF K V` for the `dom` rules to fire
(`MachCSL/StdppMap.lean`, `GMapF`).  A set type other than `GSet` /
`CoPset` needs its own instance-normalisation lemma added to the simp set
(or passed as `set_solver [..]`).  Membership in a map, `k ∈ m`, is
unfolded only through iris-lean's `PartialMap` instance (`setSolver_mapMem`),
not `ExtTreeMap`'s own; write `(get? m k).isSome` or `k ∈ dom_set m`.
-/
import MachCSL.StdppMap
import Iris.Std.CoPset
import Iris.Std.Namespaces

namespace MachCSL

open Iris.Std Iris.Std.PartialMap

/-! ### The unfolding lemmas (instance-level facts the simp set needs) -/

section Unfold
variable {S : Type _} {A : Type _} [LawfulSet S A]

theorem setSolver_subset {X Y : S} : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := Iff.rfl
theorem setSolver_ssubset {X Y : S} : X ⊂ Y ↔ X ≠ Y ∧ ∀ x, x ∈ X → x ∈ Y := Iff.rfl
theorem setSolver_disjoint {X Y : S} : X ## Y ↔ ∀ x, x ∈ X → x ∈ Y → False := elemOfDisjoint
theorem setSolver_empty {x : A} : x ∈ (∅ : S) ↔ False := elemOfEmpty
end Unfold

theorem setSolver_mapMem {K V : Type _} {M : Type _ → Type _} [PartialMap M K] {m : M V} {k : K} :
    k ∈ m ↔ (get? m k).isSome = true := Iff.rfl

/-- Instance normalisation.  The generic lemmas' right-hand sides speak of
`x ∈ X` through the `LawfulSet`-derived `Membership` instance, while the
hypotheses a user writes about a `GSet` / `CoPset` use the container's own
instance; the two are defeq but `grind`'s congruence closure keeps them
apart, so every membership is rewritten to the native instance first. -/
theorem setSolver_gsetMem {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {X : Std.ExtTreeSet α cmp} {x : α} :
    @Membership.mem α (Std.ExtTreeSet α cmp) (@Set.toMembership _ _ LawfulSet.toSet) X x ↔ x ∈ X :=
  Iff.rfl
theorem setSolver_coPsetMem {X : CoPset} {p : Pos} :
    @Membership.mem Pos CoPset (@Set.toMembership _ _ LawfulSet.toSet) X p ↔ p ∈ X := Iff.rfl

theorem setSolver_coPset_subset {X Y : CoPset} : X ⊆ Y ↔ ∀ p, p ∈ X → p ∈ Y := Iff.rfl
theorem setSolver_coPset_top {p : Pos} : p ∈ (⊤ : CoPset) ↔ True :=
  ⟨fun _ => trivial, fun _ => CoPset.mem_full⟩
theorem setSolver_coPset_empty {p : Pos} : p ∈ (∅ : CoPset) ↔ False :=
  ⟨fun h => CoPset.mem_empty h, False.elim⟩

/-! ### The tactic -/

/-- `set_solver`: unfold set statements (goal and hypotheses) to membership,
then close the first-order residue with `grind`.  `set_solver [l, …]` adds
simp lemmas to the unfolding.  See the file header. -/
syntax (name := setSolver) "set_solver" (" [" withoutPosition(Lean.Parser.Tactic.simpLemma,*) "]")? :
  tactic

/-- The unfolding step of `set_solver` (the simp set; see the header), optionally
with extra simp lemmas. -/
syntax (name := setSolverUnfold) "set_solver_unfold"
  (" [" withoutPosition(Lean.Parser.Tactic.simpLemma,*) "]")? : tactic

macro_rules
  | `(tactic| set_solver_unfold) => `(tactic| set_solver_unfold [ne_eq])
  | `(tactic| set_solver_unfold [$ls,*]) => `(tactic| (
      try simp only [$ls,*,
        -- sets
        LawfulSet.mem_union, LawfulSet.mem_inter, LawfulSet.mem_diff, LawfulSet.mem_singleton,
        setSolver_empty, LawfulSet.mem_insert, LawfulSet.mem_delete, elemOfListToSet,
        setSolver_subset, setSolver_ssubset, setSolver_disjoint, setEq, elemOfUnionList,
        FiniteSet.mem_toList, elemOfFilter,
        -- `GSet`'s own `insert`/`erase`, and the instance normalisation
        Std.ExtTreeSet.insert_eq_insert, Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_erase, Std.ExtTreeSet.not_mem_empty,
        Std.compare_eq_iff_eq, setSolver_gsetMem, setSolver_coPsetMem,
        -- map domains
        domEmpty, domSingleton, domInsert, domDelete, domUnion, domDifference, domIntersection,
        domFmap, elemOfDom, setSolver_mapMem,
        -- lists
        List.mem_cons, List.mem_append, List.not_mem_nil, List.mem_singleton, List.mem_filter,
        -- masks
        CoPset.in_union, CoPset.in_inter, CoPset.in_diff, CoPset.in_singleton,
        setSolver_coPset_subset, setSolver_coPset_top, setSolver_coPset_empty] at *))

macro_rules
  | `(tactic| set_solver) => `(tactic| (
      set_solver_unfold
      first
        | done
        | grind))
  | `(tactic| set_solver [$ls,*]) => `(tactic| (
      set_solver_unfold [$ls,*]
      first
        | done
        | grind))

/-! ### Tests: goals from the Rocq weak files (file:line of the `set_solver` call) -/

section Tests

variable {A : Type} [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]

-- AxLockAdeq.v:428 (`L4_ne_wx_wrel`): a `NoDup_cons` head is not in the tail.
example (wx wrel acq rx : A) (Hn : wx ∉ [wrel, acq, rx]) : wx ≠ wrel := by set_solver
-- AxLockAdeq.v:441
example (wx wrel acq rx : A) (Hn : wrel ∉ [acq, rx]) : wrel ≠ acq := by set_solver
-- AxLockAdeq.v:452
example (acq rx : A) (Hn : acq ∉ [rx]) : acq ≠ rx := by set_solver
-- WeakStore.v:457 (`winsl_lookup_out`), both side conditions.
example (z z0 : A) (zs : List A) (Hz : z ∉ z0 :: zs) : z0 ≠ z := by set_solver
example (z z0 : A) (zs : List A) (Hz : z ∉ z0 :: zs) : z ∉ zs := by set_solver
-- AxLockAdeq.v:473 (`lob_succ_wx`): a singleton's member is the element.
example (e wrel : A) (Hin : e ∈ ({wrel} : GSet A)) : e = wrel := by set_solver
-- AxLockAdeq.v:474: a member of `{y}` equal to `x` makes `x = y`.
example (wx wrel : A) (Hin : wx ∈ ({wrel} : GSet A)) : wx = wrel := by set_solver
-- AxLockAdeq.v:478: membership in a literal singleton.
example (wrel : A) : wrel ∈ ({wrel} : GSet A) := by set_solver
-- AxLockAdeq.v:479 (`rewrite -Hgmo_perm /L4`): a member of a literal list.
example (wx wrel acq rx : A) : wrel ∈ [wx, wrel, acq, rx] := by set_solver
-- AxLockAdeq.v:512: nothing is in `∅`.
example (e : A) (Hin : e ∈ (∅ : GSet A)) : False := by set_solver
-- AxLockAdeq.v:649 (`axpol_wf_L4`): the prefix `[]` contributes no element.
example (e : A) (P : A → Prop) : ∀ x, x ∈ ([] : List A) → P x := by set_solver
-- AxLockAdeq.v:663 (`Hdom_eq0`): two domains after `dom_insert_L`.
example (a b c d : A) :
    ({a} ∪ ({b} ∪ ({c} ∪ ({d} ∪ ∅))) : GSet A) = {d} ∪ ({c} ∪ ({b} ∪ ({a} ∪ ∅))) := by
  set_solver
-- AxLockAdeq.v:666 (`Hdom0`): `list_to_set L4 ⊆ dom na0`.
example (a b c d : A) :
    (LawfulSet.ofList [a, b, c, d] : GSet A) ⊆ {a} ∪ ({b} ∪ ({c} ∪ ({d} ∪ ∅))) := by set_solver
-- AxLockAdeq.v:684: an element of a four-key domain is one of the keys.
example (e0 a b c d : A) (H : e0 ∈ ({a} ∪ ({b} ∪ ({c} ∪ ({d} ∪ ∅))) : GSet A))
    (h1 : e0 ≠ a) (h2 : e0 ≠ b) (h3 : e0 ≠ c) (h4 : e0 ≠ d) : False := by set_solver
-- AxLockAdeq.v:721 (`big_sepS_elem_of` side): `r_x ∈ list_to_set L4`.
example (wx wrel acq rx : A) : rx ∈ (LawfulSet.ofList [wx, wrel, acq, rx] : GSet A) := by set_solver
-- AxLockAdeq.v:925 (`big_sepS_insert` side): `x ∉ {[L]}` from `x ≠ L`.
example (x L : A) (h : x ≠ L) : x ∉ ({L} : GSet A) := by set_solver
-- AxLockAdeq.v:1356 (`D_of4_init`): the empty claimed set has no member.
example (e : A) : e ∉ (∅ : GSet A) := by set_solver
-- AxSched.v:179 (`visited_snoc`): `list_to_set (l ++ [e]) = {[e]} ∪ list_to_set l`.
example (l : List A) (e : A) :
    (LawfulSet.ofList (l ++ [e]) : GSet A) = {e} ∪ LawfulSet.ofList l := by set_solver
-- AxSched.v:228: the empty domain is inside anything.
example (X : GSet A) : (∅ : GSet A) ⊆ X := by set_solver
-- AxSched.v:324: membership pushed through a snoc of the visited set.
example (r e : A) (vis : GSet A) (Hsnoc : r ∈ ({e} ∪ vis : GSet A)) (Hne : r ≠ e) : r ∈ vis := by
  set_solver
-- AxSched.v:348 (after `dom_insert_L`): the new key joins the domain.
example (e : A) (D : GSet A) (vis : GSet A) (H : vis ⊆ D) : {e} ∪ vis ⊆ {e} ∪ D := by set_solver
-- AxSched.v:352: `apply Hnin; set_solver` -- a member of a subset.
example (e : A) (X Y : GSet A) (Hsub : X ⊆ Y) (Hin : e ∈ X) : e ∈ Y := by set_solver
-- AxSched.v:402 (after `dom_delete_L`): deleting a key not in the set.
example (r : A) (vis D : GSet A) (H : vis ⊆ D) (Hr : r ∉ vis) : vis ⊆ D \ {r} := by set_solver
-- AxSched.v:462: a member of an empty domain is absurd.
example (e : A) (D : GSet A) (Hd : D = ∅) (Hbad : e ∈ D) : False := by set_solver
-- AxSched.v:559: `{[r]} ⊆ dom D` from `r ∈ dom D`.
example (r : A) (D : GSet A) (Hr0 : r ∈ D) : ({r} : GSet A) ⊆ D := by set_solver
-- WeakPromise.v:1298: the promise set returns after inserting and removing `ts`.
example (ts : A) (P : GSet A) (Hts : ts ∉ P) : ({ts} ∪ P) \ {ts} = P := by set_solver
-- WeakPromise.v:1141: an element of `{[ts]} ∪ P` other than `ts` is in `P`.
example (ts ts' : A) (P : GSet A) (H : ts' ∈ P) : ts' ∈ ({ts} ∪ P : GSet A) := by set_solver
-- AxLedgerG.v:280: `e0 ≠ e` from a membership/non-membership pair.
example (e e0 : A) (X : GSet A) (H0 : e0 ∈ X) (H : e ∉ X) : e0 ≠ e := by set_solver
-- AxLedgerG.v:877: union is commutative (Leibniz).
example (X Y : GSet A) : X ∪ Y = Y ∪ X := by set_solver
-- AxDefer2.v:119 (`gsrc_d`): disjoint singleton union.
example (x : A) (X Y : GSet A) (H : x ∉ Y) (Hd : X ## Y) : ({x} ∪ X) ## Y := by set_solver
-- AxSpinProt.v:818: `j ∉ dom ∅`.
example {V : Type} (j : A) : j ∉ (FiniteMap.dom_set (∅ : GMapF A V) : GSet A) := by set_solver
-- AxSpinProt.v:827: domain of an inserted map.
example {V : Type} (i j : A) (v : V) (m : GMapF A V) (Hm2 : j ∈ (FiniteMap.dom_set m : GSet A)) :
    j ∈ (FiniteMap.dom_set (insert m i v) : GSet A) := by set_solver
-- AxSpinProt.v:827, with the domain given by a hypothesis (`rewrite Hm2`).
example {V : Type} (i : A) (v : V) (m : GMapF A V) (Z : GSet A)
    (Hm2 : (FiniteMap.dom_set m : GSet A) = Z) :
    (FiniteMap.dom_set (insert m i v) : GSet A) = {i} ∪ Z := by set_solver
-- AxLockAdeq.v:684 (`elem_of_dom_2` then `dom_insert_L`): a key of a singleton map.
example {V : Type} (e0 a : A) (v : V)
    (H : e0 ∈ (FiniteMap.dom_set ({[a := v]} : GMapF A V) : GSet A)) : e0 = a := by set_solver
-- AxSched.v:402 (`dom_delete_L`): a deleted key leaves the domain.
example {V : Type} (r : A) (D : GMapF A V) :
    r ∉ (FiniteMap.dom_set (delete D r) : GSet A) := by set_solver
-- intersection and difference (AxEpiSoundFwd.v / AxTierA.v shapes).
example (x : A) (X Y Z : GSet A) (H : x ∈ X ∩ Y) (Hz : Z ⊆ X \ Y) : x ∉ Z := by set_solver
example (X Y : GSet A) : X ∩ Y ⊆ X ∪ Y := by set_solver
example (X Y Z : GSet A) (h1 : X ⊆ Y) (h2 : Y ⊆ Z) : X ⊆ Z := by set_solver
example (X Y : GSet A) (h : X ⊆ Y) : Y = X ∪ (Y \ X) := by set_solver
-- AxLockAdeq.v:214 (`fupd_mask_intro` side): mask inclusions.
example (E : CoPset) (N : CoPset) : E \ N ⊆ E := by set_solver
example (E1 E2 : CoPset) (h : E1 ⊆ E2) : E1 ⊆ ⊤ ∪ E2 := by set_solver
-- AxSpinProt.v:827 (`ghost_map_insert` loop): the domain invariant after an insert.
example {V : Type} (i : A) (v : V) (m : GMapF A V) (Z : GSet A)
    (Hm2 : ∀ j, j ∈ (FiniteMap.dom_set m : GSet A) ↔ j ∈ Z) :
    ∀ j, j ∈ (FiniteMap.dom_set (insert m i v) : GSet A) ↔ j = i ∨ j ∈ Z := by set_solver
-- AxSched.v:307 (`visited_snoc`, rewritten): the visited set grows by one.
example (e r : A) (vis vis' : GSet A) (Hs : vis' = {e} ∪ vis) (Hr : r ∈ vis) : r ∈ vis' := by
  set_solver
-- AxSched.v:409: `apply Hnin; set_solver` with the element substituted.
example (e1 : A) (vis : GSet A) (Hnin : e1 ∉ ({e1} ∪ vis : GSet A)) : False := by
  set_solver
-- `{[a; b]}` (Rocq) as Lean's set-builder notation, through `GSet`'s own `insert`.
example (a b : A) : a ∈ ({a, b} : GSet A) ∧ b ∈ ({a, b} : GSet A) := by set_solver
example (a b c : A) (h : c ∈ ({a, b} : GSet A)) (ha : c ≠ a) : c = b := by set_solver
-- `elements` and `filter` (AxTokLedger.v shapes).
example (X : GSet A) (x : A) (h : x ∈ FiniteSet.toList X) : x ∈ X ∪ {x} := by set_solver
example (p : A → Bool) (X : GSet A) (x : A) (h : x ∈ FiniteSet.filter p X) : x ∈ X ∧ p x := by
  set_solver
-- the difference is disjoint from what it removes (`disjoint_difference_r`).
example (X Y : GSet A) : (X \ Y) ## Y := by set_solver
-- masks: a namespace inside `⊤`, a mask minus a namespace inside the mask.
example (N : Namespace) : (↑N : CoPset) ⊆ ⊤ := by set_solver
example (E : CoPset) (N : Namespace) (h : (↑N : CoPset) ⊆ E) : E \ ↑N ∪ ↑N ⊆ E := by set_solver
-- an extra unfolding lemma (Rocq's `elem_of_lob_succ_of` shape).
example (f : A → GSet A) (succ : A → A) (hf : ∀ a x, x ∈ f a ↔ x = succ a) (a : A) :
    f a = {succ a} := by set_solver [hf]

-- it FAILS (does not loop) on a false goal.
example (X Y : GSet A) : True := by
  fail_if_success (have : X ⊆ X ∩ Y := by set_solver)
  trivial

end Tests

end MachCSL

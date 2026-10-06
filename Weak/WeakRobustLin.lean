/-
Weak: **the topological linearization of the dependency graph** (M6 W2b,
slice 1: the induction backbone).

Rocq: `iris/WeakRobustLin.v` @ xxvzwolszwmp.

The Rocq header, in substance: `Weak/WeakRobustGraph.lean` builds the dependency
relation `gdep = gpo ∪ grf` over a traced behavior's event set, and the
acyclicity file proves it ACYCLIC under the per-class premises.  This file turns
that acyclicity into the object W2b's delay-simulation inducts over: a LIST of
all the bundle's events, duplicate-free, complete, and topologically sorted —
every `gdep` edge points strictly forward.

THE FOUR DELIVERABLES.  (1) THE EVENT ENUMERATION `gevEnum`: every well-formed
event `(i, k)` of a `Ptraces` bundle, built by an explicit offset recursion
(`gevEnumFrom`); `nodupGevEnum`, `elemOfGevEnum` (`e ∈ gevEnum TS ↔ gevWf TS e`)
and `lengthGevEnum` (the sum of the trace lengths).  (2) DECIDABILITY of the
graph relations (`gevWfDec`, `gevReadsDec`, the `gpo`/`grf`/`gdep` instances and
their `DecidableRel` wrappers): every quantifier is bounded by a list lookup, so
the sort below is constructive (no classical choice is used to split cases).
(3) THE LINEARIZATION `gdepToposort`: the generic finite topological sort
(`topoScan` — the decidability spend; `topoChain` — walking back along
predecessors; `WeakRobustLin.topoMin` — pigeonhole; `WeakRobustLin.topoSortAux`
— pop a minimal element and recurse).  (4) THE INDUCTION PRINCIPLE
`toposortInd`: each step knows that ALL of its `gdep`-predecessors are already
in the processed prefix.  The increments: `gevIndex` (a position function),
prefix closure (`topoPrefixClosed`, `topoPredDone`, `topoNotInPrefix`) and
per-agent monotonicity (`topoAgentLt`, `topoAgentMono`, `topoGdepForward`).

DEPENDENCY-FREE like its parents: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1 (`NoDup_x` ↦
   `nodupX`, `elem_of_x` ↦ `elemOfX`).  The Rocq names of this file listed in
   `notes/weak-port-dupnames.json` (`topo_min`, `topo_sort_aux`, `gpo_dec`,
   `grf_dec`) are FILE-QUALIFIED (`WeakRobustLin.topoMin`, …).
2. VOCABULARY: as `WeakRobustGraph` deviation 2; `l !! i` ↦ `l[i]?`, `NoDup` ↦
   `List.Nodup`, `seq 0 n` ↦ `List.range' 0 n`, `sum_list_with` ↦
   `MachCSL.Stdpp.sumListWith`, `Exists P l` ↦ `∃ x ∈ l, P x`, `Decision` ↦
   `Decidable`, `RelDecision` ↦ `DecidableRel`, `list_find (λ x, x = e)` ↦
   `listFind (fun x => decide (x = e))`, `fst <$> o` ↦ `o.map Prod.fst`.
3. SECTION `topo_generic`: the context `A R` is explicit per lemma (`A`
   implicit, `R` explicit as in Rocq); the `RelDecision R` instance argument is
   taken exactly by the lemmas that use it (`topoScan`, `topoMin`,
   `topoSortAux`, `topoSort`), not by `topoChain` (Rocq's section closing drops
   it there as unused).  Section `lin`'s `P D` are implicit variables.
4. `toposortInd`: the step hypothesis's bound variable `done` is renamed `dn`
   (`done` is a tactic keyword in Lean).  Its "past the end" case reads
   `length order ≤ n` off `order[n]? = none` directly (`lookup_ge_None_1`)
   instead of Rocq's `not_lt` detour; statement unchanged.
5. The Decidable instances are ordinary (transparent) instance definitions;
   Rocq's are `Qed`-opaque.  No statement depends on this.

**Rocq → Lean name map.**  `topo_scan` ↦ `topoScan`; `topo_chain` ↦
`topoChain`; `topo_min` ↦ `WeakRobustLin.topoMin`; `topo_sort_aux` ↦
`WeakRobustLin.topoSortAux`; `topo_sort` ↦ `topoSort`; `gev_enum_from` ↦
`gevEnumFrom`; `gev_enum` ↦ `gevEnum`; `elem_of_gev_enum_from` ↦
`elemOfGevEnumFrom`; `gev_enum_from_ge` ↦ `gevEnumFromGe`;
`NoDup_gev_enum_from` ↦ `nodupGevEnumFrom`; `length_gev_enum_from` ↦
`lengthGevEnumFrom`; `elem_of_gev_enum` ↦ `elemOfGevEnum`; `NoDup_gev_enum` ↦
`nodupGevEnum`; `length_gev_enum` ↦ `lengthGevEnum`; `gev_wf_dec` ↦
`gevWfDec`; `gev_ts_eq_dec` ↦ `gevTsEqDec`; `gev_reads_dec` ↦ `gevReadsDec`;
`gpo_dec` ↦ `WeakRobustLin.gpoDec`; `grf_dec` ↦ `WeakRobustLin.grfDec`;
`gdep_dec` ↦ `gdepDec`; `gpo_rel_dec` ↦ `gpoRelDec`; `grf_rel_dec` ↦
`grfRelDec`; `gdep_rel_dec` ↦ `gdepRelDec`; `topo_order` ↦ `topoOrder`;
`gdep_toposort` ↦ `gdepToposort`; `gdep_toposort_pack` ↦ `gdepToposortPack`;
`gev_index` ↦ `gevIndex`; `gev_index_Some` ↦ `gevIndexSome`; `gev_index_None`
↦ `gevIndexNone`; `gev_index_lookup` ↦ `gevIndexLookup`; `topo_order_index` ↦
`topoOrderIndex`; `topo_order_index_unique` ↦ `topoOrderIndexUnique`;
`topo_prefix_closed` ↦ `topoPrefixClosed`; `topo_pred_done` ↦ `topoPredDone`;
`topo_not_in_prefix` ↦ `topoNotInPrefix`; `topo_agent_lt` ↦ `topoAgentLt`;
`topo_agent_mono` ↦ `topoAgentMono`; `topo_gdep_forward` ↦ `topoGdepForward`;
`toposort_ind` ↦ `toposortInd`.

**Not ported:** nothing.
-/
import Weak.WeakRobustGraph

namespace Weak

open MachCSL MachCSL.Stdpp

/-! ## DELIVERABLE 3, part 1: the GENERIC finite topological sort

Nothing here mentions `Gev`: the sort needs only a decidable acyclic relation
and a duplicate-free finite carrier. -/

/-- THE DECIDABILITY SPEND.  Scanning `scan` (a sublist of the carrier `rem`),
either some element of `rem` has no R-predecessor in `rem`, or every scanned
element has one.  The case split is the `Decidable` instance, not excluded
middle. -/
theorem topoScan {A : Type _} (R : A → A → Prop) [DecidableRel R] (rem : List A) :
    ∀ scan : List A, (∀ x, x ∈ scan → x ∈ rem) →
      (∃ m, m ∈ rem ∧ ∀ x, x ∈ rem → ¬ R x m) ∨
      (∀ m, m ∈ scan → ∃ x, x ∈ rem ∧ R x m) := by
  intro scan
  induction scan with
  | nil =>
    intro _
    right
    intro m hm
    exact absurd hm List.not_mem_nil
  | cons a scan ih =>
    intro hsub
    have hsub' : ∀ x, x ∈ scan → x ∈ rem := fun x hx => hsub x (List.mem_cons_of_mem a hx)
    rcases Decidable.em (∃ x ∈ rem, R x a) with hex | hex
    · rcases ih hsub' with hmin | hall
      · exact Or.inl hmin
      · right
        intro m hm
        rcases List.mem_cons.1 hm with rfl | hm
        · obtain ⟨x, hx, hR⟩ := hex
          exact ⟨x, hx, hR⟩
        · exact hall m hm
    · left
      refine ⟨a, hsub a List.mem_cons_self, ?_⟩
      intro x hx hR
      exact hex ⟨x, hx, hR⟩

/-- THE CHAIN.  If every element of `rem` has an R-predecessor in `rem`, one can
walk backwards from any element for any number of steps; LATER entries are
`tc R`-predecessors of EARLIER ones. -/
theorem topoChain {A : Type _} (R : A → A → Prop) (rem : List A) :
    (∀ m, m ∈ rem → ∃ x, x ∈ rem ∧ R x m) →
    ∀ n y, y ∈ rem → ∃ l : List A,
      l.length = n + 1 ∧ (∀ z, z ∈ l → z ∈ rem) ∧ l[0]? = some y ∧
      (∀ (i j : Nat) x z, i < j → l[i]? = some x → l[j]? = some z → tc R z x) := by
  intro hall n
  induction n with
  | zero =>
    intro y hy
    refine ⟨[y], rfl, ?_, rfl, ?_⟩
    · intro z hz
      rw [List.mem_singleton.1 hz]
      exact hy
    · intro i j x z hij _ hj
      have := lookup_lt_Some hj
      simp only [List.length_singleton] at this
      omega
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx, hR⟩ := hall y hy
    obtain ⟨l, hlen, hin, h0, hord⟩ := ih x hx
    refine ⟨y :: l, by rw [List.length_cons, hlen], ?_, rfl, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact hin z hz
    · intro i j x' z hij hi hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        cases j with
        | zero => omega
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          cases j with
          | zero =>
            rw [h0] at hj
            cases hj
            exact tc_once hR
          | succ j =>
            have hzx : tc R z x := hord 0 (j + 1) x z (by omega) h0 hj
            exact tc_r hzx hR
      | succ i =>
        cases j with
        | zero => omega
        | succ j =>
          simp only [List.getElem?_cons_succ] at hi hj
          exact hord i j x' z (by omega) hi hj

/-- THE MINIMAL ELEMENT, by pigeonhole: a chain of length `|rem| + 1` is
duplicate-free (acyclicity) and included in `rem`, which is impossible. -/
theorem WeakRobustLin.topoMin {A : Type _} (R : A → A → Prop) [DecidableRel R]
    (rem : List A) :
    (∀ x, ¬ tc R x x) → rem ≠ [] → rem.Nodup →
    ∃ m, m ∈ rem ∧ ∀ x, x ∈ rem → ¬ R x m := by
  intro hacyc hne _
  rcases topoScan R rem rem (fun _ h => h) with hmin | hall
  · exact hmin
  · exfalso
    cases rem with
    | nil => exact hne rfl
    | cons y rem' =>
      obtain ⟨l, hlen, hin, _, hord⟩ :=
        topoChain R (y :: rem') hall (y :: rem').length y List.mem_cons_self
      have hnd' : l.Nodup := by
        refine NoDup_alt.2 ?_
        intro i j x hi hj
        rcases Nat.lt_trichotomy i j with hlt | heq | hgt
        · exact absurd (hord i j x x hlt hi hj) (hacyc x)
        · exact heq
        · exact absurd (hord j i x x hgt hj hi) (hacyc x)
      have hle : l.length ≤ (y :: rem').length := submseteq_length (NoDup_submseteq hnd' hin)
      omega

/-- THE SORT, by induction on the carrier's length: pop a minimal element,
recurse. -/
theorem WeakRobustLin.topoSortAux {A : Type _} (R : A → A → Prop) [DecidableRel R] :
    (∀ x, ¬ tc R x x) →
    ∀ n (rem : List A), rem.length = n → rem.Nodup →
    ∃ order : List A, order.Nodup ∧ (∀ e, e ∈ order ↔ e ∈ rem) ∧
      (∀ (i j : Nat) x y, order[i]? = some x → order[j]? = some y → R x y → i < j) := by
  intro hacyc n
  induction n with
  | zero =>
    intro rem hlen _
    rw [nil_length_inv hlen]
    refine ⟨[], List.nodup_nil, fun _ => Iff.rfl, ?_⟩
    intro i j x y hi
    simp at hi
  | succ n ih =>
    intro rem hlen hnd
    have hne : rem ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨m, hm, hmin⟩ := WeakRobustLin.topoMin R rem hacyc hne hnd
    obtain ⟨l1, l2, rfl⟩ := elem_of_list_split hm
    have hlen' : (l1 ++ l2).length = n := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    have hsplit : (l1 ++ l2).Nodup ∧ m ∉ l1 ++ l2 := by
      obtain ⟨h1, h2, h3⟩ := NoDup_app.1 hnd
      obtain ⟨h3, h4⟩ := NoDup_cons.1 h3
      refine ⟨NoDup_app.2 ⟨h1, fun x hx hx2 => h2 x hx (List.mem_cons_of_mem m hx2), h4⟩, ?_⟩
      intro hc
      rcases List.mem_append.1 hc with hc | hc
      · exact h2 m hc List.mem_cons_self
      · exact h3 hc
    obtain ⟨hnd', hmnot⟩ := hsplit
    obtain ⟨order, hndo, hmem, hord⟩ := ih (l1 ++ l2) hlen' hnd'
    refine ⟨m :: order, ?_, ?_, ?_⟩
    · exact NoDup_cons.2 ⟨fun h => hmnot ((hmem m).1 h), hndo⟩
    · intro e
      rw [List.mem_cons, hmem, List.mem_append, List.mem_append, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · intro i j x y hi hj hR
      cases j with
      | zero =>
        -- the head is minimal: nothing in the carrier points AT it
        exfalso
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        have hx : x ∈ m :: order := elem_of_list_lookup_2 hi
        refine hmin x ?_ hR
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_append.2 (Or.inr List.mem_cons_self)
        · rcases List.mem_append.1 ((hmem x).1 hx) with h | h
          · exact List.mem_append.2 (Or.inl h)
          · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h))
      | succ j =>
        cases i with
        | zero => omega
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi hj
          have := hord i j x y hi hj hR
          omega

theorem topoSort {A : Type _} (R : A → A → Prop) [DecidableRel R] (rem : List A) :
    (∀ x, ¬ tc R x x) → rem.Nodup →
    ∃ order : List A, order.Nodup ∧ (∀ e, e ∈ order ↔ e ∈ rem) ∧
      (∀ (i j : Nat) x y, order[i]? = some x → order[j]? = some y → R x y → i < j) :=
  fun hacyc hnd => WeakRobustLin.topoSortAux R hacyc rem.length rem rfl hnd

section Lin

variable {P D : Type}

/-! ## DELIVERABLE 1: THE EVENT ENUMERATION -/

/-- All events of the trace list `Ts`, whose first trace is agent `i`. -/
def gevEnumFrom (i : Nat) : List (Atrace P D) → List Gev
  | [] => []
  | T :: Ts' => (List.range' 0 T.atEvs.length).map (fun k => (i, k)) ++ gevEnumFrom (i + 1) Ts'

def gevEnum (TS : Ptraces P D) : List Gev := gevEnumFrom 0 TS.ptTrs

theorem elemOfGevEnumFrom (i : Nat) (Ts : List (Atrace P D)) (e : Gev) :
    e ∈ gevEnumFrom i Ts ↔
    ∃ j T, Ts[j]? = some T ∧ e.1 = i + j ∧ e.2 < T.atEvs.length := by
  induction Ts generalizing i with
  | nil => simp [gevEnumFrom]
  | cons T Ts ih =>
    rw [gevEnumFrom, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨k, hk, rfl⟩ | ⟨j, T', hT, hj, hlt⟩)
      · rw [elem_of_seq] at hk
        exact ⟨0, T, rfl, by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨j + 1, T', by simpa using hT, by omega, hlt⟩
    · rintro ⟨j, T', hT, hj, hlt⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hT
        subst hT
        left
        refine ⟨e.2, ?_, Prod.ext (by dsimp only; omega) rfl⟩
        rw [elem_of_seq]
        omega
      | succ j =>
        right
        exact ⟨j, T', by simpa using hT, by omega, hlt⟩

theorem gevEnumFromGe (i : Nat) (Ts : List (Atrace P D)) (e : Gev) :
    e ∈ gevEnumFrom i Ts → i ≤ e.1 := by
  intro h
  obtain ⟨j, T, _, hj, _⟩ := (elemOfGevEnumFrom i Ts e).1 h
  omega

theorem nodupGevEnumFrom (i : Nat) (Ts : List (Atrace P D)) : (gevEnumFrom i Ts).Nodup := by
  induction Ts generalizing i with
  | nil => exact List.nodup_nil
  | cons T Ts ih =>
    rw [gevEnumFrom]
    refine NoDup_app.2 ⟨?_, ?_, ih (i + 1)⟩
    · exact NoDup_fmap_2_strong (fun k1 k2 _ _ heq => (Prod.mk.inj heq).2) NoDup_seq
    · intro e he he2
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 he
      have := gevEnumFromGe (i + 1) Ts _ he2
      dsimp only at this
      omega

theorem lengthGevEnumFrom (i : Nat) (Ts : List (Atrace P D)) :
    (gevEnumFrom i Ts).length = sumListWith (fun T => T.atEvs.length) Ts := by
  induction Ts generalizing i with
  | nil => rfl
  | cons T Ts ih =>
    rw [gevEnumFrom, List.length_append, List.length_map, List.length_range', ih]
    simp only [sumListWith, List.map_cons, List.sum_cons]

/-- COMPLETENESS: the enumeration is exactly the set of well-formed events. -/
theorem elemOfGevEnum (TS : Ptraces P D) (e : Gev) : e ∈ gevEnum TS ↔ gevWf TS e := by
  rw [gevEnum, elemOfGevEnumFrom, gevWfBounds]
  constructor
  · rintro ⟨j, T, hT, hj, hlt⟩
    have he : e.1 = j := by omega
    exact ⟨T, by rw [he]; exact hT, hlt⟩
  · rintro ⟨T, hT, hlt⟩
    exact ⟨e.1, T, hT, by omega, hlt⟩

theorem nodupGevEnum (TS : Ptraces P D) : (gevEnum TS).Nodup := nodupGevEnumFrom 0 _

/-- The CARDINALITY: the sum of the trace lengths. -/
theorem lengthGevEnum (TS : Ptraces P D) :
    (gevEnum TS).length = sumListWith (fun T => T.atEvs.length) TS.ptTrs :=
  lengthGevEnumFrom 0 _

/-! ## DELIVERABLE 2: DECIDABILITY of the graph relations

Every quantifier is bounded by a list lookup, so all of these are plain
`Decidable` instances. -/

instance gevWfDec (TS : Ptraces P D) (e : Gev) : Decidable (gevWf TS e) :=
  inferInstanceAs (Decidable ((gevEv TS e).isSome = true))

instance gevTsEqDec (TS : Ptraces P D) (e : Gev) (o : Option Nat) :
    Decidable (gevTs TS e = o) := inferInstance

instance gevReadsDec (TS : Ptraces P D) (e : Gev) (a : Int) (ts : Nat) :
    Decidable (gevReads TS e a ts) :=
  match h : gevLb TS e with
  | some l =>
    if hin : (a, ts) ∈ lbReads l then isTrue ⟨l, h, hin⟩
    else isFalse (by
      intro hr
      obtain ⟨l', hl', hin'⟩ := hr
      rw [h] at hl'
      cases hl'
      exact hin hin')
  | none => isFalse (by
      intro hr
      obtain ⟨l', hl', _⟩ := hr
      rw [h] at hl'
      cases hl')

instance WeakRobustLin.gpoDec (TS : Ptraces P D) (e1 e2 : Gev) :
    Decidable (WeakRobustGraph.gpo TS e1 e2) :=
  inferInstanceAs (Decidable (e1.1 = e2.1 ∧ e1.2 < e2.2 ∧ gevWf TS e1 ∧ gevWf TS e2))

/-- `grf`'s two existentials are bounded: `ts` by the source's `gevTs` (ONE
option) and `a` by the reader's `lbReads` (a concrete list). -/
instance WeakRobustLin.grfDec (TS : Ptraces P D) (e1 e2 : Gev) :
    Decidable (WeakRobustGraph.grf TS e1 e2) :=
  match hts : gevTs TS e1 with
  | none => isFalse (by
      intro hg
      obtain ⟨_, _, h, _⟩ := hg
      rw [hts] at h
      cases h)
  | some ts =>
    match hl : gevLb TS e2 with
    | none => isFalse (by
        intro hg
        obtain ⟨_, _, _, l', hl', _⟩ := hg
        rw [hl] at hl'
        cases hl')
    | some l =>
      if hex : ∃ p ∈ lbReads l, p.2 = ts then
        isTrue (by
          obtain ⟨⟨a, t⟩, hin, ht⟩ := hex
          dsimp only at ht
          subst ht
          exact ⟨t, a, hts, l, hl, hin⟩)
      else
        isFalse (by
          intro hg
          obtain ⟨ts', a, hts', l', hl', hin⟩ := hg
          rw [hts] at hts'
          cases hts'
          rw [hl] at hl'
          cases hl'
          exact hex ⟨(a, ts), hin, rfl⟩)

instance gdepDec (TS : Ptraces P D) (e1 e2 : Gev) : Decidable (gdep TS e1 e2) :=
  inferInstanceAs (Decidable (WeakRobustGraph.gpo TS e1 e2 ∨ WeakRobustGraph.grf TS e1 e2))

instance gpoRelDec (TS : Ptraces P D) : DecidableRel (WeakRobustGraph.gpo TS) :=
  fun _ _ => inferInstance
instance grfRelDec (TS : Ptraces P D) : DecidableRel (WeakRobustGraph.grf TS) :=
  fun _ _ => inferInstance
instance gdepRelDec (TS : Ptraces P D) : DecidableRel (gdep TS) :=
  fun _ _ => inferInstance

/-! ## DELIVERABLE 3: THE LINEARIZATION -/

/-- The packaged form of the conclusion. -/
def topoOrder (TS : Ptraces P D) (order : List Gev) : Prop :=
  order.Nodup ∧
  (∀ e, e ∈ order ↔ gevWf TS e) ∧
  (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → gdep TS x y → i < j)

theorem gdepToposort (TS : Ptraces P D) :
    gdepAcyclic TS →
    ∃ order : List Gev,
      order.Nodup ∧
      (∀ e, e ∈ order ↔ gevWf TS e) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → gdep TS x y → i < j) := by
  intro hacyc
  obtain ⟨order, hnd, hmem, hord⟩ := topoSort (gdep TS) (gevEnum TS) hacyc (nodupGevEnum TS)
  refine ⟨order, hnd, fun e => (hmem e).trans (elemOfGevEnum TS e), ?_⟩
  intro x y i j hi hj hd
  exact hord i j x y hi hj hd

theorem gdepToposortPack (TS : Ptraces P D) :
    gdepAcyclic TS → ∃ order, topoOrder TS order := by
  intro hacyc
  obtain ⟨order, h1, h2, h3⟩ := gdepToposort TS hacyc
  exact ⟨order, h1, h2, h3⟩

/-! ## INCREMENT (a): `gevIndex` — each wf event's position -/

def gevIndex (order : List Gev) (e : Gev) : Option Nat :=
  (listFind (fun x => decide (x = e)) order).map Prod.fst

theorem gevIndexSome (order : List Gev) (e : Gev) :
    e ∈ order → ∃ i, gevIndex order e = some i ∧ order[i]? = some e := by
  intro he
  have hf := list_find_elem_of (p := fun x => decide (x = e)) he (by simp)
  obtain ⟨⟨i, x⟩, hf⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨hl, hx, _⟩ := list_find_Some.1 hf
  have hxe : x = e := of_decide_eq_true hx
  subst hxe
  exact ⟨i, by rw [gevIndex, hf]; rfl, hl⟩

theorem gevIndexNone (order : List Gev) (e : Gev) : e ∉ order → gevIndex order e = none := by
  intro he
  have hf : listFind (fun x => decide (x = e)) order = none := by
    refine list_find_None.2 (fun x hx => ?_)
    have hne : x ≠ e := fun h => he (h ▸ hx)
    simpa using hne
  rw [gevIndex, hf]
  rfl

/-- THE CHARACTERIZATION: on a duplicate-free list the index is exactly the
lookup position. -/
theorem gevIndexLookup (order : List Gev) (i : Nat) (e : Gev) :
    order.Nodup → order[i]? = some e → gevIndex order e = some i := by
  intro hnd hi
  obtain ⟨i', hidx, hi'⟩ := gevIndexSome order e (elem_of_list_lookup_2 hi)
  rw [hidx, NoDup_lookup hnd hi' hi]

/-- Every wf event has a position, and it is unique. -/
theorem topoOrderIndex (TS : Ptraces P D) (order : List Gev) (e : Gev) :
    topoOrder TS order → gevWf TS e →
    ∃ i, gevIndex order e = some i ∧ order[i]? = some e := by
  intro ho hwf
  exact gevIndexSome order e ((ho.2.1 e).2 hwf)

theorem topoOrderIndexUnique (TS : Ptraces P D) (order : List Gev) (i j : Nat) (e : Gev) :
    topoOrder TS order → order[i]? = some e → order[j]? = some e → i = j :=
  fun ho hi hj => NoDup_lookup ho.1 hi hj

/-! ## INCREMENT (b): PREFIX CLOSURE

No `gdep` edge points from OUTSIDE a prefix of `order` INTO it. -/

theorem topoPrefixClosed (TS : Ptraces P D) (order : List Gev) (n : Nat) (x y : Gev) :
    topoOrder TS order → gdep TS x y → y ∈ order.take n → x ∈ order.take n := by
  intro ho hd hy
  obtain ⟨_, hmem, hord⟩ := ho
  obtain ⟨j, hj, hjn⟩ := elem_of_take.1 hy
  have hxwf := (gdepWf TS x y hd).1
  obtain ⟨i, hi⟩ := elem_of_list_lookup_1 ((hmem x).2 hxwf)
  have hlt : i < j := hord x y i j hi hj hd
  exact elem_of_take.2 ⟨i, hi, by omega⟩

/-- The same fact at the exact step the induction takes: when `e` sits at
position `n`, every `gdep`-predecessor of `e` is already in `take n order`. -/
theorem topoPredDone (TS : Ptraces P D) (order : List Gev) (n : Nat) (e : Gev) :
    topoOrder TS order → order[n]? = some e →
    ∀ e', gdep TS e' e → e' ∈ order.take n := by
  intro ho hn e' hd
  obtain ⟨_, hmem, hord⟩ := ho
  have hwf := (gdepWf TS e' e hd).1
  obtain ⟨i, hi⟩ := elem_of_list_lookup_1 ((hmem e').2 hwf)
  have hlt : i < n := hord e' e i n hi hn hd
  exact elem_of_take.2 ⟨i, hi, hlt⟩

/-- …and the element at position `n` is fresh. -/
theorem topoNotInPrefix (TS : Ptraces P D) (order : List Gev) (n : Nat) (e : Gev) :
    topoOrder TS order → order[n]? = some e → e ∉ order.take n := by
  intro ho hn he
  obtain ⟨i, hi, hin⟩ := elem_of_take.1 he
  have heq : i = n := NoDup_lookup ho.1 hi hn
  omega

/-! ## INCREMENT (c): PER-AGENT MONOTONICITY -/

theorem topoAgentLt (TS : Ptraces P D) (order : List Gev) (i j : Nat) (x y : Gev) :
    topoOrder TS order → order[i]? = some x → order[j]? = some y →
    x.1 = y.1 → x.2 < y.2 → i < j := by
  intro ho hi hj hag hk
  obtain ⟨_, hmem, hord⟩ := ho
  exact hord x y i j hi hj (Or.inl ⟨hag, hk, (hmem x).1 (elem_of_list_lookup_2 hi),
    (hmem y).1 (elem_of_list_lookup_2 hj)⟩)

theorem topoAgentMono (TS : Ptraces P D) (order : List Gev) (i j : Nat) (x y : Gev) :
    topoOrder TS order → order[i]? = some x → order[j]? = some y →
    x.1 = y.1 → (i < j ↔ x.2 < y.2) := by
  intro ho hi hj hag
  refine ⟨?_, topoAgentLt TS order i j x y ho hi hj hag⟩
  intro hij
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact hlt
  · -- equal step index and equal agent: the SAME event, so i = j
    exfalso
    have hxy : x = y := Prod.ext hag heq
    subst hxy
    have := topoOrderIndexUnique TS order i j x ho hi hj
    omega
  · exfalso
    have := topoAgentLt TS order j i y x ho hj hi hag.symm hgt
    omega

/-- A same-agent `gdep` edge is a forward step in `order` (the shape
`gdepSameAgentLt` hands over). -/
theorem topoGdepForward (TS : Ptraces P D) (order : List Gev) (i j : Nat) (x y : Gev) :
    topoOrder TS order → order[i]? = some x → order[j]? = some y →
    gdep TS x y → i < j :=
  fun ho hi hj hd => ho.2.2 x y i j hi hj hd

/-! ## DELIVERABLE 4: THE INDUCTION PRINCIPLE -/

theorem toposortInd (TS : Ptraces P D) (Q : List Gev → Prop) :
    gdepAcyclic TS →
    Q [] →
    (∀ dn e,
       Q dn →
       gevWf TS e → e ∉ dn →
       (∀ e', gdep TS e' e → e' ∈ dn) →
       Q (dn ++ [e])) →
    ∃ order,
      Q order ∧
      order.Nodup ∧
      (∀ e, e ∈ order ↔ gevWf TS e) ∧
      (∀ x y (i j : Nat), order[i]? = some x → order[j]? = some y → gdep TS x y → i < j) := by
  intro hacyc hnil hstep
  obtain ⟨order, ho⟩ := gdepToposortPack TS hacyc
  have hpre : ∀ n, Q (order.take n) := by
    intro n
    induction n with
    | zero => rw [take_0]; exact hnil
    | succ n ih =>
      cases hn : order[n]? with
      | some e =>
        rw [take_S_r hn]
        exact hstep _ e ih ((ho.2.1 e).1 (elem_of_list_lookup_2 hn))
          (topoNotInPrefix TS order n e ho hn)
          (fun e' hd => topoPredDone TS order n e ho hn e' hd)
      | none =>
        -- past the end: the prefix does not grow
        have hge : order.length ≤ n := lookup_ge_None_1 hn
        rw [take_ge (show order.length ≤ n + 1 by omega)]
        rw [take_ge hge] at ih
        exact ih
  obtain ⟨hnd, hmem, hord⟩ := ho
  refine ⟨order, ?_, hnd, hmem, hord⟩
  have hfull := hpre order.length
  rwa [take_ge (Nat.le_refl _)] at hfull

end Lin

end Weak

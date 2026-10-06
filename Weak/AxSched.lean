/-
Weak: **the JOINT gmo SCHEDULER** (design rev 7 §5; review-fetch Q4).  PURE (no Iris).

Rocq: `iris/AxSched.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE PROBLEM.  `AxAdequacy.adequacy_ord`'s phase 2 walks `G.gxGmo` left to right because every
`ob` edge is gmo-forward (`obCatSubGmo`).  The rev-7 "ctrl gate" (`AxGate`) breaks that for
READS: a read gmo-earlier than an open ctrl gate of its OWN hart must be DEFERRED (its flow
equation fired later, against a snapshot taken at its own gmo position) and re-inserted later,
once the gate's sources have been processed.  `AxTieProc.isProcOrder` names the SETTING a valid
such reordering (a PROCESSING ORDER, a permutation of `G.gxGmo`) must satisfy; this file
CONSTRUCTS one via a small-step scheduler and proves it meets that setting, plus termination
and exactly-once processing.

THE SCHEDULER.  Walk `G.gxGmo` index `n = 0,1,2,…`.  At each `e := G.gxGmo[n]?`: either COMMIT
it (append to `sProc`) or, if `e` is a PLAIN read, DEFER it (park it in the pending map `sD`,
keyed by `n` — the snapshot marker) to be FLUSHED later without consuming a gmo index.  NO event
of a LOCKED hart (one with a pending deferred read) may commit (`stepCommit`'s `Hclear` — the
task-(A) fix: it used to guard writes only), flushing happens in po order (`stepFlush`'s
`Hfirst`), and a read may only be deferred if it is gmo-before every po-later write of its hart
(`stepDefer`'s `HgateOK`) — exactly what a genuine ctrl-gate source is, by
`AxGate.gateStoreAfter` (§6).

  §1  the state `Sstate`, the per-hart frontier VIEWS (`hfLockSrcs`/`hfLocked`/`hfRow`, derived
      from `sD`), and `schedStep`.
  §2  `visited`: the gmo-index-`n` prefix, as a set.
  §3  the invariant `AxSched.Inv` (NoDup, the visited-prefix partition into `sProc`/pending-`sD`,
      `sEverD` bookkeeping, the ORDER invariants `invOrdFresh`/`invOrdDef` — `isProcOrder`'s
      clauses 4/5 — PLUS `invOrdPpo`: an ever-deferred event precedes every committed
      `gppoCat6` successor) and its preservation `AxSched.invStep`.
  §4  `schedCorrect` (`isProcOrder` at any fully-processed reachable state), `schedOrdPpo`,
      `schedExactlyOnce`.
  §5  `schedTerminates`, via the lexicographic measure (remaining gmo events, |pending D|)
      encoded as one `Nat` (`msr`).
  §6  `gateSrcsNeverDeferred`: `HgateOK` for ONE later write, from `AxGate.gateStoreAfter`.

FINDINGS (kept from Rocq, §6 there).  (1) `gateSrcsNeverDeferred` discharges `HgateOK` for one
later write `(i, k)` at a time; iterating it over every later position of a real row (a routine
wrapper over the row position-indexing lemmas) is left to a following increment — the scheduler
§§1-5 only ASSUMES `HgateOK` per deferred read.  (2) Wiring `schedCorrect`'s output into
`adequacy_ord`'s per-event induction (over `sProc` instead of `G.gxGmo`) is new work for the Iris
shell.  (3) UPDATE (diagnosis (A)): the SAME-HART half of `AxAdequacyL`'s §4 gap (a deferred
read's `gppoCat6` later read committing ahead of it) is CLOSED by `Hclear`/`Hfirst`/`invOrdPpo`/
`schedOrdPpo`; the CROSS-HART half (via `gfr`) needs no fix (a `gfr` source is always a read,
and a read deposits nothing into `prot_inv`).

## Deviations from Rocq

1. NAMES: lowerCamelCase (map below).  The duplicated Rocq names (`notes/weak-port-dupnames.json`)
   `Inv` and `Inv_step` are FILE-QUALIFIED: `AxSched.Inv`, `AxSched.invStep`; the Lean-only
   helpers are file-qualified too (`AxSched.domG`, `AxSched.memDomG`, `AxSched.memDomGInsert`,
   `AxSched.memDomGDelete`, `AxSched.domGDelete`).
2. REPRESENTATION (the tree's shims): `gmap geid nat` ↦ `GMapF Geid Nat` (`MachCSL.StdppMap`),
   `gset geid` ↦ `GSet Geid` (`MachCSL.StdppSet`); `dom D` ↦ `AxSched.domG D`
   (= `FiniteMap.dom_set D : GSet Geid`); `D !! r` ↦ `get? D r`; `<[e := n]> D` ↦
   `PartialMap.insert D e n`; `delete r D` ↦ `PartialMap.delete D r`; `list_to_set` ↦
   `LawfulSet.ofList`; `filter`/`size` on sets ↦ `FiniteSet.filter`/`FiniteSet.size`;
   `gx_gmo G !! n` ↦ `G.gxGmo[n]?`; `S n` ↦ `n + 1`; `gpo` ↦ `WeakRvwmoGraph.gpo`.
3. SECTION: Rocq's `Section Sched` with `Context G Hgwf Hcat6gmo` and `Proof using All` on every
   lemma: in Lean every §2–§5 theorem takes `G Hgwf Hcat6gmo` (`include … in`), the definitions
   (`visited`, `schedStep`, `AxSched.Inv`, `msr`) take `G` only, and `Sstate`/`sst0`/`hf*` take
   neither — the same arities as the Rocq terms after the section closes.
   The unused ones would trip `linter.unusedSectionVars`, switched off for this file.
4. The scheduler step constructors are `schedStep.stepCommit/stepDefer/stepFlush`; the record
   constructor `Sst` is `Sstate.Sst`, `MkInv` is `AxSched.Inv.mkInv`.

**Name map.**  `sstate` `Sstate`, `Sst` `Sstate.Sst`, `s_n`/`s_D`/`s_everD`/`s_proc`
`sN`/`sD`/`sEverD`/`sProc`, `sst0`, `hf_lock_srcs` `hfLockSrcs`, `hf_locked` `hfLocked`, `hf_row`
`hfRow`, `sched_step` `schedStep` (`StepCommit`/`StepDefer`/`StepFlush` ↦
`stepCommit`/`stepDefer`/`stepFlush`), `visited`, `visited_0` `visited0`, `visited_snoc`
`visitedSnoc`, `visited_full` `visitedFull`, `elem_of_visited` `elemOfVisited`,
`visited_elem_gpos_lt` `visitedElemGposLt`, `Inv` `AxSched.Inv` (fields `inv_nodup` `invNodup`,
`inv_disj` `invDisj`, `inv_part` `invPart`, `inv_D_everD` `invDEverD`, `inv_everD_vis`
`invEverDVis`, `inv_everD_r` `invEverDR`, `inv_ord_fresh` `invOrdFresh`, `inv_ord_def`
`invOrdDef`, `inv_ord_ppo` `invOrdPpo`), `Inv_sst0` `invSst0`, `fresh_at` `freshAt`, `lpos_app_l`
`lposAppL`, `lt_in_app_l` `ltInAppL`, `lt_in_app_last` `ltInAppLast`, `Inv_step`
`AxSched.invStep`, `Inv_rtc` `invRtc`, `sched_correct` `schedCorrect`, `sched_ord_ppo`
`schedOrdPpo`, `sched_exactly_once` `schedExactlyOnce`, `msr`, `D_bound` `dBound`, `msr_mul_eq`
`msrMulEq`, `msr_step_lt` `msrStepLt`, `no_infinite_desc` `noInfiniteDesc`, `sched_terminates`
`schedTerminates`, `gate_srcs_never_deferred` `gateSrcsNeverDeferred`.

**Not ported:** nothing (the §7 `Print Assumptions` block has no Lean twin; the lint's axiom check
covers it).
-/
import Weak.AxGate
import Weak.AxTieProc
import MachCSL.StdppMap
import MachCSL.OrdKeys

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Wlabel

-- Rocq's `Proof using All`: every §2–§5 theorem takes the section hypotheses, used or not.
set_option linter.unusedSectionVars false

/-! # 1. The scheduler state and one step -/

/-- The core state.  `sN`: the gmo index the walker is about to look at.  `sD`: the CURRENTLY
PENDING deferred set, each pending event mapped to the gmo index it was deferred AT (the
snapshot marker).  `sEverD`: every event EVER deferred.  `sProc`: the committed processing
order so far, in commit order. -/
structure Sstate where
  Sst ::
  sN : Nat
  sD : GMapF Geid Nat
  sEverD : GSet Geid
  sProc : List Geid

def sst0 : Sstate := ⟨0, ∅, ∅, []⟩

/-- Rocq's `dom D`, at the scheduler's key/set types. -/
abbrev AxSched.domG (D : GMapF Geid Nat) : GSet Geid := FiniteMap.dom_set D

/-- DERIVED per-hart frontier: a hart is "locked at an open gate" exactly when it has a pending
deferred read; the gate's still-uncommitted sources are that hart's slice of `dom sD`. -/
def hfLockSrcs (st : Sstate) (i : Agent) : GSet Geid :=
  FiniteSet.filter (fun r : Geid => decide (r.1 = i)) (AxSched.domG st.sD)

def hfLocked (st : Sstate) (i : Agent) : Prop := hfLockSrcs st i ≠ ∅

def hfRow (st : Sstate) (i : Agent) : Nat :=
  (st.sProc.filter (fun e : Geid => decide (e.1 = i))).length + FiniteSet.size (hfLockSrcs st i)

/-- ONE SCHEDULER STEP.  `stepCommit`: the event at the walker's index commits, provided no
pending deferred read belongs to its hart (`Hclear`).  `stepDefer`: a PLAIN read is deferred,
provided it is gmo-before every po-later write of its hart (`HgateOK`).  `stepFlush`: a pending
read, po-earliest among its hart's pending ones (`Hfirst`), is committed without consuming a gmo
index. -/
inductive schedStep (G : Gexec) : Sstate → Sstate → Prop
  | stepCommit (n : Nat) (D : GMapF Geid Nat) (everD : GSet Geid) (proc : List Geid) (e : Geid)
      (He : G.gxGmo[n]? = some e)
      (Hclear : ∀ r, r ∈ AxSched.domG D → r.1 ≠ e.1) :
      schedStep G ⟨n, D, everD, proc⟩ ⟨n + 1, D, everD, proc ++ [e]⟩
  | stepDefer (n : Nat) (D : GMapF Geid Nat) (everD : GSet Geid) (proc : List Geid) (e : Geid)
      (He : G.gxGmo[n]? = some e)
      (Hr : ∃ l, gxLbl G e = some l ∧ lbIsR l = true ∧ lbIsW l = false)
      (HgateOK : ∀ e2, WeakRvwmoGraph.gpo G e e2 → glblIs G e2 lbIsW → gmoLt G e e2) :
      schedStep G ⟨n, D, everD, proc⟩ ⟨n + 1, PartialMap.insert D e n, {e} ∪ everD, proc⟩
  | stepFlush (n : Nat) (D : GMapF Geid Nat) (everD : GSet Geid) (proc : List Geid) (r : Geid)
      (m : Nat)
      (HD : get? D r = some m)
      (Hfirst : ∀ r' m', get? D r' = some m' → r'.1 = r.1 → ¬ WeakRvwmoGraph.gpo G r' r) :
      schedStep G ⟨n, D, everD, proc⟩ ⟨n, PartialMap.delete D r, everD, proc ++ [r]⟩

/-! # Lean-only: membership in `AxSched.domG` -/

theorem AxSched.memDomG {D : GMapF Geid Nat} {x : Geid} :
    x ∈ AxSched.domG D ↔ (get? D x).isSome := elemOfDom

theorem AxSched.memDomGInsert {D : GMapF Geid Nat} {x e : Geid} {n : Nat} :
    x ∈ AxSched.domG (PartialMap.insert D e n) ↔ x = e ∨ x ∈ AxSched.domG D := by
  show x ∈ (FiniteMap.dom_set (PartialMap.insert D e n) : GSet Geid) ↔
    x = e ∨ x ∈ (FiniteMap.dom_set D : GSet Geid)
  rw [domInsert, elemOfUnion, elemOfSingleton]

theorem AxSched.domGDelete {D : GMapF Geid Nat} {r : Geid} :
    AxSched.domG (PartialMap.delete D r) = AxSched.domG D \ {r} := domDelete

theorem AxSched.memDomGDelete {D : GMapF Geid Nat} {x r : Geid} :
    x ∈ AxSched.domG (PartialMap.delete D r) ↔ x ∈ AxSched.domG D ∧ x ≠ r := by
  rw [AxSched.domGDelete, elemOfDifference, elemOfSingleton]

/-! # 2. The visited prefix -/

def visited (G : Gexec) (n : Nat) : GSet Geid := LawfulSet.ofList (G.gxGmo.take n)

variable (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G)

include Hgwf Hcat6gmo in
theorem visited0 : visited G 0 = ∅ := by
  unfold visited
  rw [List.take_zero]
  exact listToSetNil

include Hgwf Hcat6gmo in
theorem visitedSnoc (n : Nat) (e : Geid) :
    G.gxGmo[n]? = some e → visited G (n + 1) = {e} ∪ visited G n := by
  intro Hn
  apply LawfulSet.ext
  intro x
  unfold visited
  rw [elemOfUnion, elemOfSingleton, elemOfListToSet, elemOfListToSet, take_S_r Hn,
    List.mem_append, List.mem_singleton]
  exact Or.comm

include Hgwf Hcat6gmo in
theorem visitedFull : visited G G.gxGmo.length = LawfulSet.ofList G.gxGmo := by
  unfold visited
  rw [List.take_of_length_le (Nat.le_refl _)]

include Hgwf Hcat6gmo in
theorem elemOfVisited (n : Nat) (e : Geid) : e ∈ visited G n ↔ e ∈ G.gxGmo.take n :=
  elemOfListToSet

include Hgwf Hcat6gmo in
theorem visitedElemGposLt (n : Nat) (e : Geid) : e ∈ visited G n → gpos G e < n := by
  intro Hv
  obtain ⟨j, Hj, Hjlt⟩ := elem_of_take.1 ((elemOfVisited G Hgwf Hcat6gmo n e).1 Hv)
  rw [gposOfLookup G j e Hgwf.1 Hj]
  exact Hjlt

/-! # 3. The scheduler invariant -/

structure AxSched.Inv (G : Gexec) (st : Sstate) : Prop where
  mkInv ::
  invNodup : st.sProc.Nodup
  invDisj : ∀ e, e ∈ st.sProc → e ∉ AxSched.domG st.sD
  invPart : ∀ e, e ∈ visited G st.sN ↔ e ∈ st.sProc ∨ e ∈ AxSched.domG st.sD
  invDEverD : AxSched.domG st.sD ⊆ st.sEverD
  invEverDVis : st.sEverD ⊆ visited G st.sN
  invEverDR : ∀ e, e ∈ st.sEverD →
    ∃ l, gxLbl G e = some l ∧ lbIsR l = true ∧ lbIsW l = false
  /-- Clause 4 of `isProcOrder`: a NEVER-deferred element keeps raw gmo order in `sProc`. -/
  invOrdFresh : ∀ e1 e2, e1 ∈ st.sProc → e2 ∈ st.sProc → e1 ∉ st.sEverD →
    gpos G e1 < gpos G e2 → ltIn st.sProc e1 e2
  /-- Clause 5: an EVER-deferred read precedes every committed po-later write of its hart. -/
  invOrdDef : ∀ r e, r ∈ st.sEverD → WeakRvwmoGraph.gpo G r e → glblIs G e lbIsW →
    e ∈ st.sProc → ltIn st.sProc r e
  /-- The task-(A) fix: an ever-deferred event precedes every committed `gppoCat6` successor. -/
  invOrdPpo : ∀ e1 e2, e1 ∈ st.sEverD → gppoCat6 G e1 e2 →
    e2 ∈ st.sProc → ltIn st.sProc e1 e2

include Hgwf Hcat6gmo in
theorem invSst0 : AxSched.Inv G sst0 := by
  refine AxSched.Inv.mkInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact List.nodup_nil
  · intro e h; exact absurd h List.not_mem_nil
  · intro e
    show e ∈ visited G 0 ↔ e ∈ ([] : List Geid) ∨ e ∈ AxSched.domG (∅ : GMapF Geid Nat)
    rw [visited0 G Hgwf Hcat6gmo, AxSched.memDomG, lookupEmpty]
    simp only [List.not_mem_nil, Option.isSome_none, Bool.false_eq_true, or_self, iff_false]
    exact notElemOfEmpty
  · apply elemOfSubseteq.2
    intro x hx
    rw [AxSched.memDomG] at hx
    exact absurd hx (by show ¬ (get? (∅ : GMapF Geid Nat) x).isSome; rw [lookupEmpty]; simp)
  · apply elemOfSubseteq.2
    intro x hx
    exact absurd hx notElemOfEmpty
  · intro x hx; exact absurd hx notElemOfEmpty
  · intro x _ hx; exact absurd hx List.not_mem_nil
  · intro r e _ _ _ he; exact absurd he List.not_mem_nil
  · intro e1 e2 _ _ he; exact absurd he List.not_mem_nil

include Hgwf Hcat6gmo in
/-- `e`'s freshness the instant the walker is AT it. -/
theorem freshAt (st : Sstate) (HI : AxSched.Inv G st) (e : Geid) :
    G.gxGmo[st.sN]? = some e → e ∉ st.sProc ∧ e ∉ AxSched.domG st.sD := by
  intro He
  have Hnv : e ∉ visited G st.sN := by
    intro Hin
    obtain ⟨j, Hj, Hjlt⟩ := elem_of_take.1 ((elemOfVisited G Hgwf Hcat6gmo _ _).1 Hin)
    have := NoDup_lookup Hgwf.1 Hj He
    omega
  exact ⟨fun h => Hnv ((HI.invPart e).2 (.inl h)), fun h => Hnv ((HI.invPart e).2 (.inr h))⟩

include Hgwf Hcat6gmo in
/-- A member of an already-NoDup list keeps its `lpos` after appending at the end. -/
theorem lposAppL (L L2 : List Geid) (e : Geid) :
    (L ++ L2).Nodup → e ∈ L → lpos (L ++ L2) e = lpos L e := by
  intro Hnd He
  obtain ⟨i, Hi, Heq⟩ := lposLookup L e He
  rw [Heq]
  apply lposOfLookup _ _ _ Hnd
  rw [List.getElem?_append_left (lookup_lt_Some Hi)]
  exact Hi

include Hgwf Hcat6gmo in
theorem ltInAppL (L L2 : List Geid) (x y : Geid) :
    (L ++ L2).Nodup → ltIn L x y → ltIn (L ++ L2) x y := by
  rintro Hnd ⟨Hx, Hy, Hlt⟩
  refine ⟨List.mem_append_left _ Hx, List.mem_append_left _ Hy, ?_⟩
  rw [lposAppL G Hgwf Hcat6gmo L L2 x Hnd Hx, lposAppL G Hgwf Hcat6gmo L L2 y Hnd Hy]
  exact Hlt

include Hgwf Hcat6gmo in
/-- ANY member of `L` precedes an element freshly appended at its end. -/
theorem ltInAppLast (L : List Geid) (x z : Geid) :
    (L ++ [z]).Nodup → x ∈ L → ltIn (L ++ [z]) x z := by
  intro Hnd Hx
  obtain ⟨i, Hi, _⟩ := lposLookup L x Hx
  have Hilt : i < L.length := lookup_lt_Some Hi
  have Hx1 : lpos (L ++ [z]) x = i := by
    apply lposOfLookup _ _ _ Hnd
    rw [List.getElem?_append_left Hilt]
    exact Hi
  have Hz1 : lpos (L ++ [z]) z = L.length := by
    apply lposOfLookup _ _ _ Hnd
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨List.mem_append_left _ Hx, List.mem_append_right _ (List.mem_singleton_self z), ?_⟩
  rw [Hx1, Hz1]
  exact Hilt

include Hgwf Hcat6gmo in
/-- THE MAIN PRESERVATION LEMMA. -/
theorem AxSched.invStep (st st' : Sstate) : AxSched.Inv G st → schedStep G st st' →
    AxSched.Inv G st' := by
  intro HI Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    have Hnd : proc.Nodup := HI.invNodup
    have Hdisj : ∀ x, x ∈ proc → x ∉ AxSched.domG D := HI.invDisj
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited G n := elemOfSubseteq.1 HI.invEverDVis
    have Hordf : ∀ e1 e2, e1 ∈ proc → e2 ∈ proc → e1 ∉ everD → gpos G e1 < gpos G e2 →
        ltIn proc e1 e2 := HI.invOrdFresh
    have Hordd : ∀ r e, r ∈ everD → WeakRvwmoGraph.gpo G r e → glblIs G e lbIsW →
        e ∈ proc → ltIn proc r e := HI.invOrdDef
    have Hordppo : ∀ e1 e2, e1 ∈ everD → gppoCat6 G e1 e2 → e2 ∈ proc → ltIn proc e1 e2 :=
      HI.invOrdPpo
    obtain ⟨Hfp, Hfd⟩ := freshAt G Hgwf Hcat6gmo _ HI e He
    have Hnd' : (proc ++ [e]).Nodup := by
      refine NoDup_app.2 ⟨Hnd, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hfp hx
    have HgposE : gpos G e = n := gposOfLookup G n e Hgwf.1 He
    -- a committed-or-pending visited event is not in `D` and not `proc` ⇒ contradiction helper
    have Hproc : ∀ x, x ∈ everD → x ∉ AxSched.domG D → x ∈ proc := by
      intro x hx hxD
      rcases (Hpart x).1 (HeDvis x hx) with h | h
      · exact h
      · exact absurd h hxD
    refine AxSched.Inv.mkInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Hnd'
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Hdisj x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        exact Hfd
    · intro x
      show x ∈ visited G (n + 1) ↔ x ∈ proc ++ [e] ∨ x ∈ AxSched.domG D
      rw [visitedSnoc G Hgwf Hcat6gmo n e He, elemOfUnion, elemOfSingleton, Hpart x,
        List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h)
        · exact .inr h
      · rintro ((h | h) | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    · exact HI.invDEverD
    · apply elemOfSubseteq.2
      intro x hx
      show x ∈ visited G (n + 1)
      rw [visitedSnoc G Hgwf Hcat6gmo n e He, elemOfUnion]
      exact .inr (HeDvis x hx)
    · exact HI.invEverDR
    · intro e1 e2 He1 He2 Hnin Hlt
      rcases List.mem_append.1 He1 with He1 | He1 <;>
        rcases List.mem_append.1 He2 with He2 | He2
      · exact ltInAppL G Hgwf Hcat6gmo proc [e] e1 e2 Hnd' (Hordf e1 e2 He1 He2 Hnin Hlt)
      · rw [List.mem_singleton] at He2
        rw [He2]
        exact ltInAppLast G Hgwf Hcat6gmo proc e1 e Hnd' He1
      · exfalso
        rw [List.mem_singleton] at He1
        have Hge : gpos G e2 < n :=
          visitedElemGposLt G Hgwf Hcat6gmo n e2 ((Hpart e2).2 (.inl He2))
        rw [He1, HgposE] at Hlt
        omega
      · exfalso
        rw [List.mem_singleton] at He1 He2
        rw [He1, He2] at Hlt
        exact Nat.lt_irrefl _ Hlt
    · intro r e0 Hr Hgpo Hw He0
      rcases List.mem_append.1 He0 with He0 | He0
      · exact ltInAppL G Hgwf Hcat6gmo proc [e] r e0 Hnd' (Hordd r e0 Hr Hgpo Hw He0)
      · rw [List.mem_singleton] at He0
        rw [He0] at Hgpo ⊢
        by_cases HrD : r ∈ AxSched.domG D
        · exact absurd Hgpo.1 (Hclear r HrD)
        · exact ltInAppLast G Hgwf Hcat6gmo proc r e Hnd' (Hproc r Hr HrD)
    · intro e1 e2 He1 Hpp He2
      rcases List.mem_append.1 He2 with He2 | He2
      · exact ltInAppL G Hgwf Hcat6gmo proc [e] e1 e2 Hnd' (Hordppo e1 e2 He1 Hpp He2)
      · rw [List.mem_singleton] at He2
        rw [He2] at Hpp ⊢
        by_cases He1D : e1 ∈ AxSched.domG D
        · exact absurd (gppoCat6Gpo G e1 e Hpp).1 (Hclear e1 He1D)
        · exact ltInAppLast G Hgwf Hcat6gmo proc e1 e Hnd' (Hproc e1 He1 He1D)
  | stepDefer n D everD proc e He Hr HgateOK =>
    have Hnd : proc.Nodup := HI.invNodup
    have Hdisj : ∀ x, x ∈ proc → x ∉ AxSched.domG D := HI.invDisj
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HDeD : ∀ x, x ∈ AxSched.domG D → x ∈ everD := elemOfSubseteq.1 HI.invDEverD
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited G n := elemOfSubseteq.1 HI.invEverDVis
    have HeDr : ∀ x, x ∈ everD → ∃ l, gxLbl G x = some l ∧ lbIsR l = true ∧ lbIsW l = false :=
      HI.invEverDR
    have Hordf : ∀ e1 e2, e1 ∈ proc → e2 ∈ proc → e1 ∉ everD → gpos G e1 < gpos G e2 →
        ltIn proc e1 e2 := HI.invOrdFresh
    have Hordd : ∀ r e, r ∈ everD → WeakRvwmoGraph.gpo G r e → glblIs G e lbIsW →
        e ∈ proc → ltIn proc r e := HI.invOrdDef
    have Hordppo : ∀ e1 e2, e1 ∈ everD → gppoCat6 G e1 e2 → e2 ∈ proc → ltIn proc e1 e2 :=
      HI.invOrdPpo
    obtain ⟨Hfp, _⟩ := freshAt G Hgwf Hcat6gmo _ HI e He
    have HgposE : gpos G e = n := gposOfLookup G n e Hgwf.1 He
    refine AxSched.Inv.mkInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Hnd
    · intro x hx hxD
      rcases AxSched.memDomGInsert.1 hxD with h | h
      · rw [h] at hx
        exact Hfp hx
      · exact Hdisj x hx h
    · intro x
      show x ∈ visited G (n + 1) ↔ x ∈ proc ∨ x ∈ AxSched.domG (PartialMap.insert D e n)
      rw [visitedSnoc G Hgwf Hcat6gmo n e He, elemOfUnion, elemOfSingleton, Hpart x,
        AxSched.memDomGInsert]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    · apply elemOfSubseteq.2
      intro x hx
      show x ∈ ({e} ∪ everD : GSet Geid)
      rw [elemOfUnion, elemOfSingleton]
      rcases AxSched.memDomGInsert.1 hx with h | h
      · exact .inl h
      · exact .inr (HDeD x h)
    · apply elemOfSubseteq.2
      intro x hx
      show x ∈ visited G (n + 1)
      rw [visitedSnoc G Hgwf Hcat6gmo n e He, elemOfUnion, elemOfSingleton]
      change x ∈ ({e} ∪ everD : GSet Geid) at hx
      rw [elemOfUnion, elemOfSingleton] at hx
      rcases hx with h | h
      · exact .inl h
      · exact .inr (HeDvis x h)
    · intro x hx
      change x ∈ ({e} ∪ everD : GSet Geid) at hx
      rw [elemOfUnion, elemOfSingleton] at hx
      rcases hx with h | h
      · rw [h]; exact Hr
      · exact HeDr x h
    · intro e1 e2 He1 He2 Hnin Hlt
      exact Hordf e1 e2 He1 He2 (fun h => Hnin (elemOfUnion.2 (.inr h))) Hlt
    · intro r e0 Hr0 Hgpo Hw He0
      change r ∈ ({e} ∪ everD : GSet Geid) at Hr0
      rw [elemOfUnion, elemOfSingleton] at Hr0
      rcases Hr0 with Hre | Hr0
      · exfalso
        rw [Hre] at Hgpo
        have Hlt0 : gpos G e < gpos G e0 := (HgateOK e0 Hgpo Hw).2.2
        have Hlt1 : gpos G e0 < n :=
          visitedElemGposLt G Hgwf Hcat6gmo n e0 ((Hpart e0).2 (.inl He0))
        omega
      · exact Hordd r e0 Hr0 Hgpo Hw He0
    · intro e1 e2 He1 Hpp He2
      change e1 ∈ ({e} ∪ everD : GSet Geid) at He1
      rw [elemOfUnion, elemOfSingleton] at He1
      rcases He1 with Hee | He1
      · exfalso
        rw [Hee] at Hpp
        have Hlt0 : gpos G e < gpos G e2 := (Hcat6gmo e e2 Hpp).2.2
        have Hlt1 : gpos G e2 < n :=
          visitedElemGposLt G Hgwf Hcat6gmo n e2 ((Hpart e2).2 (.inl He2))
        omega
      · exact Hordppo e1 e2 He1 Hpp He2
  | stepFlush n D everD proc r m HD Hfirst =>
    have Hnd : proc.Nodup := HI.invNodup
    have Hdisj : ∀ x, x ∈ proc → x ∉ AxSched.domG D := HI.invDisj
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HDeD : ∀ x, x ∈ AxSched.domG D → x ∈ everD := elemOfSubseteq.1 HI.invDEverD
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited G n := elemOfSubseteq.1 HI.invEverDVis
    have HeDr : ∀ x, x ∈ everD → ∃ l, gxLbl G x = some l ∧ lbIsR l = true ∧ lbIsW l = false :=
      HI.invEverDR
    have Hordf : ∀ e1 e2, e1 ∈ proc → e2 ∈ proc → e1 ∉ everD → gpos G e1 < gpos G e2 →
        ltIn proc e1 e2 := HI.invOrdFresh
    have Hordd : ∀ r e, r ∈ everD → WeakRvwmoGraph.gpo G r e → glblIs G e lbIsW →
        e ∈ proc → ltIn proc r e := HI.invOrdDef
    have Hordppo : ∀ e1 e2, e1 ∈ everD → gppoCat6 G e1 e2 → e2 ∈ proc → ltIn proc e1 e2 :=
      HI.invOrdPpo
    have Hr0dom : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hr0notp : r ∉ proc := fun h => Hdisj r h Hr0dom
    have Hnd' : (proc ++ [r]).Nodup := by
      refine NoDup_app.2 ⟨Hnd, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hr0notp hx
    have Hr0read := HeDr r (HDeD r Hr0dom)
    refine AxSched.Inv.mkInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Hnd'
    · intro x hx hxD
      rw [AxSched.memDomGDelete] at hxD
      rcases List.mem_append.1 hx with hx | hx
      · exact Hdisj x hx hxD.1
      · exact hxD.2 (List.mem_singleton.1 hx)
    · intro x
      show x ∈ visited G n ↔ x ∈ proc ++ [r] ∨ x ∈ AxSched.domG (PartialMap.delete D r)
      rw [Hpart x, AxSched.memDomGDelete, List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact .inl (.inl h)
        · by_cases hx : x = r
          · exact .inl (.inr hx)
          · exact .inr ⟨h, hx⟩
      · rintro ((h | h) | ⟨h, _⟩)
        · exact .inl h
        · rw [h]; exact .inr Hr0dom
        · exact .inr h
    · apply elemOfSubseteq.2
      intro x hx
      exact HDeD x (AxSched.memDomGDelete.1 hx).1
    · exact HI.invEverDVis
    · exact HI.invEverDR
    · intro e1 e2 He1 He2 Hnin Hlt
      rcases List.mem_append.1 He1 with He1 | He1 <;>
        rcases List.mem_append.1 He2 with He2 | He2
      · exact ltInAppL G Hgwf Hcat6gmo proc [r] e1 e2 Hnd' (Hordf e1 e2 He1 He2 Hnin Hlt)
      · rw [List.mem_singleton] at He2
        rw [He2]
        exact ltInAppLast G Hgwf Hcat6gmo proc e1 r Hnd' He1
      · exfalso
        rw [List.mem_singleton] at He1
        rw [He1] at Hnin
        exact Hnin (HDeD r Hr0dom)
      · exfalso
        rw [List.mem_singleton] at He1
        rw [He1] at Hnin
        exact Hnin (HDeD r Hr0dom)
    · intro r' e0 Hr' Hgpo Hw He0
      rcases List.mem_append.1 He0 with He0 | He0
      · exact ltInAppL G Hgwf Hcat6gmo proc [r] r' e0 Hnd' (Hordd r' e0 Hr' Hgpo Hw He0)
      · exfalso
        rw [List.mem_singleton] at He0
        obtain ⟨l, hl, _, hlw⟩ := Hr0read
        obtain ⟨l', hl', hw'⟩ := Hw
        rw [He0, hl] at hl'
        cases Option.some.inj hl'
        rw [hlw] at hw'
        exact Bool.false_ne_true hw'
    · intro e1 e2 He1 Hpp He2
      rcases List.mem_append.1 He2 with He2 | He2
      · exact ltInAppL G Hgwf Hcat6gmo proc [r] e1 e2 Hnd' (Hordppo e1 e2 He1 Hpp He2)
      · rw [List.mem_singleton] at He2
        rw [He2] at Hpp ⊢
        by_cases He1p : e1 ∈ proc
        · exact ltInAppLast G Hgwf Hcat6gmo proc e1 r Hnd' He1p
        · exfalso
          rcases (Hpart e1).1 (HeDvis e1 He1) with h | He1D
          · exact He1p h
          · obtain ⟨m', Hm'⟩ := Option.isSome_iff_exists.1 (AxSched.memDomG.1 He1D)
            have Hg := gppoCat6Gpo G e1 r Hpp
            exact Hfirst e1 m' Hm' Hg.1 Hg

/-! # 4. The main correctness theorem -/

include Hgwf Hcat6gmo in
theorem invRtc (st : Sstate) : rtc (schedStep G) sst0 st → AxSched.Inv G st := by
  intro h
  exact rtc_ind_r (fun st => AxSched.Inv G st) sst0 (invSst0 G Hgwf Hcat6gmo)
    (fun y z _ Hs Hy => AxSched.invStep G Hgwf Hcat6gmo y z Hy Hs) st h

include Hgwf Hcat6gmo in
/-- At a FULLY-PROCESSED reachable state (every gmo event visited, nothing pending), `sProc`
realizes `isProcOrder` for exactly the events ever deferred (tasks (c) and (d)). -/
theorem schedCorrect (st : Sstate) (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) :
    isProcOrder G (fun e => e ∈ st.sEverD) st.sProc := by
  have HI := invRtc G Hgwf Hcat6gmo st Hrun
  have Hvisall : visited G st.sN = LawfulSet.ofList G.gxGmo := by
    rw [Hfull]; exact visitedFull G Hgwf Hcat6gmo
  have Hdomempty : ∀ x, x ∉ AxSched.domG st.sD := by
    intro x hx
    rw [Hdone, AxSched.memDomG, lookupEmpty] at hx
    exact Bool.false_ne_true hx
  have Hin : ∀ e, e ∈ G.gxGmo → e ∈ st.sProc := by
    intro e he
    have Hev : e ∈ visited G st.sN := by rw [Hvisall, elemOfListToSet]; exact he
    rcases (HI.invPart e).1 Hev with h | h
    · exact h
    · exact absurd h (Hdomempty e)
  refine ⟨fun e => ⟨fun He => ?_, Hin e⟩, HI.invNodup, HI.invEverDR, ?_, ?_⟩
  · have Hev := (HI.invPart e).2 (.inl He)
    rw [Hvisall, elemOfListToSet] at Hev
    exact Hev
  · rintro e1 e2 He1 ⟨Hg1, Hg2, Hlt⟩
    exact HI.invOrdFresh e1 e2 (Hin e1 Hg1) (Hin e2 Hg2) He1 Hlt
  · intro r e Hr Hgpo Hw
    exact HI.invOrdDef r e Hr Hgpo Hw
      (Hin e (gwfMemGmo G e Hgwf (WeakRvwmoGraph.glblIsWGmem G e Hw)))

include Hgwf Hcat6gmo in
/-- THE NEW GUARANTEE (task (A)'s fix), at a fully-processed state: an ever-deferred event
precedes every `gppoCat6` successor of it (not stated by `isProcOrder`). -/
theorem schedOrdPpo (st : Sstate) (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) :
    ∀ e1 e2, e1 ∈ st.sEverD → gppoCat6 G e1 e2 → e2 ∈ G.gxGmo → ltIn st.sProc e1 e2 := by
  have HI := invRtc G Hgwf Hcat6gmo st Hrun
  intro e1 e2 He1 Hpp He2
  have Hvisall : visited G st.sN = LawfulSet.ofList G.gxGmo := by
    rw [Hfull]; exact visitedFull G Hgwf Hcat6gmo
  have Hev : e2 ∈ visited G st.sN := by rw [Hvisall, elemOfListToSet]; exact He2
  have Hep : e2 ∈ st.sProc := by
    rcases (HI.invPart e2).1 Hev with h | h
    · exact h
    · rw [Hdone, AxSched.memDomG, lookupEmpty] at h
      exact absurd h Bool.false_ne_true
  exact HI.invOrdPpo e1 e2 He1 Hpp Hep

include Hgwf Hcat6gmo in
/-- Task (d) standalone: every event is processed exactly once. -/
theorem schedExactlyOnce (st : Sstate) (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) :
    (∀ e, e ∈ st.sProc ↔ e ∈ G.gxGmo) ∧ st.sProc.Nodup := by
  obtain ⟨H1, H2, _⟩ := schedCorrect G Hgwf Hcat6gmo st Hrun Hfull Hdone
  exact ⟨H1, H2⟩

/-! # 5. Termination -/

/-- The lexicographic measure (remaining gmo events, |pending D|) as one `Nat`. -/
def msr (st : Sstate) : Nat :=
  (G.gxGmo.length - st.sN) * (G.gxGmo.length + 1) + FiniteSet.size (AxSched.domG st.sD)

include Hgwf Hcat6gmo in
theorem dBound (st : Sstate) : AxSched.Inv G st →
    FiniteSet.size (AxSched.domG st.sD) ≤ G.gxGmo.length := by
  intro HI
  have Hsub : AxSched.domG st.sD ⊆ (LawfulSet.ofList G.gxGmo : GSet Geid) := by
    apply elemOfSubseteq.2
    intro x hx
    have Hxv := elemOfSubseteq.1 HI.invEverDVis x (elemOfSubseteq.1 HI.invDEverD x hx)
    obtain ⟨j, hj, _⟩ := elem_of_take.1 ((elemOfVisited G Hgwf Hcat6gmo _ _).1 Hxv)
    rw [elemOfListToSet]
    exact elem_of_list_lookup_2 hj
  exact Nat.le_trans (subseteqSize Hsub) (Nat.le_of_eq (sizeListToSet Hgwf.1))

include Hgwf Hcat6gmo in
theorem msrMulEq (L n : Nat) : n < L → (L - n) * (L + 1) = (L - (n + 1)) * (L + 1) + (L + 1) := by
  intro Hn
  have Heq : L - n = (L - (n + 1)) + 1 := by omega
  rw [Heq, Nat.add_mul, Nat.one_mul]

include Hgwf Hcat6gmo in
theorem msrStepLt (st st' : Sstate) : AxSched.Inv G st → schedStep G st st' →
    msr G st' < msr G st := by
  intro HI Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    have Hnlt : n < G.gxGmo.length := lookup_lt_Some He
    unfold msr
    dsimp only
    rw [msrMulEq G Hgwf Hcat6gmo _ _ Hnlt]
    generalize (G.gxGmo.length - (n + 1)) * (G.gxGmo.length + 1) = X
    omega
  | stepDefer n D everD proc e He Hr HgateOK =>
    have HI' := AxSched.invStep G Hgwf Hcat6gmo _ _ HI
      (schedStep.stepDefer n D everD proc e He Hr HgateOK)
    have Hb' := dBound G Hgwf Hcat6gmo _ HI'
    dsimp only at Hb'
    have Hnlt : n < G.gxGmo.length := lookup_lt_Some He
    unfold msr
    dsimp only
    rw [msrMulEq G Hgwf Hcat6gmo _ _ Hnlt]
    generalize (G.gxGmo.length - (n + 1)) * (G.gxGmo.length + 1) = X at *
    omega
  | stepFlush n D everD proc r m HD Hfirst =>
    have Hr0 : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hsub1 : ({r} : GSet Geid) ⊆ AxSched.domG D := singletonSubseteqL.2 Hr0
    have Hge1 : 1 ≤ FiniteSet.size (AxSched.domG D) := by
      have := subseteqSize Hsub1
      rw [sizeSingleton] at this
      exact this
    have Hsize : FiniteSet.size (AxSched.domG (PartialMap.delete D r)) <
        FiniteSet.size (AxSched.domG D) := by
      rw [AxSched.domGDelete, sizeDifference Hsub1, sizeSingleton]
      omega
    unfold msr
    dsimp only
    exact Nat.add_lt_add_left Hsize _

include Hgwf Hcat6gmo in
theorem noInfiniteDesc (g : Nat → Nat) : (∀ n, g (n + 1) < g n) → False := by
  intro Hdec
  have H : ∀ k n, g n ≤ k → False := by
    intro k
    induction k with
    | zero => intro n hn; have := Hdec n; omega
    | succ k ih => intro n hn; have := Hdec n; exact ih (n + 1) (by omega)
  exact H (g 0) 0 (Nat.le_refl _)

include Hgwf Hcat6gmo in
/-- No infinite scheduler run starting at `sst0`. -/
theorem schedTerminates (f : Nat → Sstate) (Hf0 : f 0 = sst0)
    (Hstep : ∀ n, schedStep G (f n) (f (n + 1))) : False := by
  have Hreach : ∀ n, rtc (schedStep G) sst0 (f n) := by
    intro n
    induction n with
    | zero => rw [Hf0]; exact rtc_refl _
    | succ n ih => exact rtc_r ih (Hstep n)
  exact noInfiniteDesc G Hgwf Hcat6gmo (fun n => msr G (f n)) (fun n =>
    msrStepLt G Hgwf Hcat6gmo (f n) (f (n + 1))
      (invRtc G Hgwf Hcat6gmo (f n) (Hreach n)) (Hstep n))

/-! # 6. Writes are never deferred, from `AxGate` -/

/-- ONE representative later write, in `gateStoreAfter`'s own quantification shape: a genuine
ctrl-gate source is gmo-before it. -/
theorem gateSrcsNeverDeferred (GT : GdexecT) (i : Agent)
    (es1 : List Eitem) (srcs : List Dsrc) (esA esB : List Eitem) (it : Eitem) (k : Nat)
    (Hconf : gtRowConformant GT i (es1 ++ (LCtrl srcs, none) :: (esA ++ it :: esB)))
    (Hcons : rvwmoCatConsistentT GT)
    (Hbound : ∀ j, j ∈ dtsrcs (dstateTAfter dtInit es1) srcs → j < k)
    (Hpos : it.2 = some k) (Hw : elbIsW it.1 = true) :
    ∀ r, r ∈ gateSrcs i (dstateTAfter dtInit es1) srcs →
      WeakRvwmoGraph.gpo GT.gtG r (i, k) → glblIs GT.gtG (i, k) lbIsW →
      gmoLt GT.gtG r (i, k) :=
  fun r Hr _ _ => gateStoreAfter GT i es1 srcs esA esB it k Hconf Hcons Hbound Hpos Hw r Hr

end Weak

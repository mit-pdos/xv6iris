import MachCSL.Lang

/-! # The attempt–grant model of fairness

The basis for Lantana's fairness extension and for the liveness proof's assumptions about MachCSL's
runs.  The general theory (sections 1 and 3–5) uses MachCSL only through the pool's step relation
(section 2), and is kept apart from its instantiation to MachCSL's runs (sections 6–7).  It was
the probe `local-plan/liveness/probes/Fairness.lean` until 2026-11-05 (lane `xv6-liveness-now`,
milestone B1; the design documents that cite it by section and theorem name are
`local-plan/liveness/attempt-grant.md` and `fairness-base.md`; all of `local-plan/` is outside the
repository).  It was re-layered 2026-11-06 (lane `fairness-layers`): the state form of an action
is the base, and the thread's view is built on top of it.  Nothing in the trusted base imports
this directory (`MachCSL/Liveness/`); it is built by `lake build MachCSL` and checked by CI like
every module of the library.

**The idea.**  A fairness assumption is an *action*: an *enabling condition* `A` on configurations
and a *grant* relation `G` on steps.  Its trusted form is the textbook strong fairness
`SF := □◇ A → □◇ (A ∧ G)`, a statement about the run that names no thread.  `SF` is itself a
miss–hit pair.  A hit is a position where `A` holds and the step taken is a grant; a miss is a
position where `A` holds and the step taken is not a grant, whoever takes it.  The counter of the
pair resets at any grant, drops at any refused position and stays where `A` fails.  This is the
fundamental theory.  Telling a thread about an update of the counter at another thread's step is
the program logic's job.

A thread's view of the action restricts that pair to the thread's own steps.  An *attempt* is a
step of the thread from a configuration where `A` holds, and the thread's form is the
*attempt–grant* form `AttemptGrant := □◇ miss → □◇ hit` over its own attempts.  The restriction
is sound when every grant is one of the thread's transitions (*own grant*).  It loses nothing when
`A` persists and the thread is scheduled fairly.  The thread's counter stays at every other
thread's step.  That is a consequence of the restriction, not a rule of fairness, and it makes the
thread's view the cheap path for the logic.

**Map of the file.**

1. `MissHit`, layer 0: miss–hit fairness over two position predicates and its counter (`Fair`,
   `IsCounter`, `fair_iff_counter`), and restriction (`fair_mono`).  Pure arithmetic of positions.
2. The pool: configurations, a thread's step, a run (`Cfg`, `Step`, `Steps`, `PoolRun`,
   `StepsInfOften`).
3. `Action`, layer 1: the state form of an action `(A, G)`, with no thread anywhere (`hit`,
   `miss`, `SF`, `Response`, `WF`, `Certain`, `IsCounter`).  `SF` is miss–hit fairness
   (`sf_iff_fair`), hence the existence of a counter (`sf_iff_counter`), whose rules hold at any
   position.  A certain grant gives `SF` outright (`sf_of_certain`).
4. `Pair`, layer 2: a thread's pair of positions, with `Attempt` and `Hit` as primitives; the
   requirements R1 (`HitsAttempt`) and R2 (`OwnStep`); the counter and its rules, among them the
   stay at other threads' steps (`counter_stay_of_other`); restriction (`attemptGrant_of_fair`).
5. `Thread`, layer 3: the thread's view of an action, a pair of layer 2 by construction
   (`attempt`, `hit`, `miss`, `AttemptGrant`, `IsCounter`), and own grant (`OwnGrant`).
   * Soundness: under own grant, `SF` gives the attempt–grant form and the counter
     (`attemptGrant_of_sf`, `counter_of_sf`); the counter rules in terms of `A` and `G`.
   * Completeness: under persistence of `A` (`Persists`, from stability `Stable`) and fair
     scheduling, the attempt–grant form gives `SF` back (`sf_of_attemptGrant`), hence
     `sf_iff_attemptGrant`.
   * A grant certain at the thread's attempts (`Certain`): no misses, counter zero, `WF` from fair
     scheduling alone (`wf_of_certain`), `SF` with persistence as well (`sf_of_certain`).
6. `Era`, MachCSL's runs: liveness, generations, the power thread; persistence for an enabling
   condition that is a live thread's and is stable under every thread but the power thread
   (`persists_of_liveStable`), or under the steps that meet a side condition
   (`persists_of_liveStableUnder`, for a gate another thread can close).
7. The instances `Tick`, `Arm`, `Fresh`, `Hart`: each gives `enabled` (the `A`) and `grant` (the
   `G`, a step of the thread that states its transition), its `SF` (layer 1) and `AG` (layer 3)
   forms, and proves `ownGrant`, `live`, `stable`, `persists`, `sf_iff` and `counter_of_sf`.  Then
   the device tasks: `Dev`, a task at a gate, whose grant is certain at its attempts (`certain`,
   `counter_zero`, `wf`); and `Dma`, a DMA write under a reservation, an instance like `Hart`
   whose persistence is a protocol property.  `Fresh` (7.3) also proves that no step but a
   power-on lowers a coherence floor (`coh_mono`), the fact behind the logic's floor receipts
   (`MachCSL.floorLbAt`), in which its grant is consumed.  What a hit and a miss of `Hart` and a
   miss of `Dma` are in machine terms (`Hart.hit_iff`, `Hart.miss_iff`, `Dma.miss_iff`) is proved
   in `MachCSL/Liveness/Cycle.lean`.  It needs two machine facts: a blocked retry keeps the head,
   and an unblocked access is served.

Lantana takes one thing from each layer.  Its trace side implements layer 1, one counter per
declared action updated at every step (the owner's decision of 2026-11-06).  Its witness kind is
stated against layer 2.  Layer 3 is its cheap path, available when the declared action has own
grant, which all six instances of section 7 have.

**Naming policy.**  Namespaces are the layers.  Capitalised names are propositions about a whole
run or a relation (`SF`, `Response`, `WF`, `Certain`, `AttemptGrant`, `IsCounter`, `OwnGrant`,
`Stable`, `Persists`); lower-case names are position or configuration predicates (`attempt`,
`hit`, `miss`, `enabled`, `grant`).  Theorems read `conclusion_of_hypothesis`
(`attemptGrant_of_sf`, `counter_of_sf`, `sf_of_attemptGrant`) or `subject_property`
(`counter_reset`, `hit_miss_exclusive`), and equivalences read `x_iff_y` (`sf_iff_fair`,
`sf_iff_attemptGrant`).  A hypothesis has the same name everywhere: `hsf` for `Action.SF`, `hag`
for an attempt–grant form, `hown` for `OwnGrant`, `hsched` for `StepsInfOften`, `hper` for
`Persists`, `hstab` for stability, `hrun` for `PoolRun`, `hδ` for a counter, `hc` for `Certain`,
`h1` and `h2` for R1 and R2, and `hA`, `hG`, `hs` for the facts at a position (`A` holds, the step
is a grant, the thread steps).  Every instance uses the same names: `enabled`, `grant`,
`ownGrant`, `SF`, `AG`, `live`, `stable`, `persists`, `sf_iff`, `counter_of_sf`.
-/

namespace Fairness

/-! ## 1. Layer 0: miss–hit fairness over positions (`MissHit`)

Two position predicates, the hits and the misses, with no run and no thread.  Miss–hit fairness
says that infinitely many misses force infinitely many hits.  With hits and misses exclusive, it
is the existence of a counter that is zero at a hit, goes down by one at a miss and is unchanged
otherwise (`fair_iff_counter`).  Every layer above is an instance of this one.

The first four subsections are copied (read-only) from Lantana's ghost toy, in the Lantana
repository: `Lantana/Trace/FairScheduling.lean` (`Nat.exists_min`, `Nat.minWitness`),
`LantanaTest/GhostToy/Count.lean` (`firstHit?`, `countMiss`, `missBound`, `horizon`, `budget`
and the lemmas `fair_iff_counter` uses) and `LantanaTest/GhostToy/MissHit.lean` (`InfOften`,
`MH` = `Fair`, `IsMHCounter` = `IsCounter`, `mhCounter_spec` = `counter_spec`, `mh_of_counter` =
`fair_of_counter`, `mh_iff_counter` = `fair_iff_counter`); only what `fair_iff_counter` needs,
with a docstring added to each lemma that has none there.  The last two subsections, restriction
and what a counter bounds, are this file's own, added with the layers on 2026-11-06. -/

namespace MissHit

/-! ### Least witnesses -/

/-- A minimal witness of a satisfiable predicate on `Nat` (classical). -/
theorem exists_min {p : Nat → Prop} : ∀ n, p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k
  | n, hn => by
    classical
    by_cases h : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, hpk⟩ := h
      exact exists_min k hpk
    · exact ⟨n, hn, fun k hk hpk => h ⟨k, hk, hpk⟩⟩
termination_by n => n

/-- The least witness of a satisfiable predicate on `Nat`. -/
noncomputable def minWitness {p : Nat → Prop} (h : ∃ n, p n) : Nat :=
  Classical.choose (exists_min h.choose h.choose_spec)

/-- The least witness satisfies the predicate. -/
theorem minWitness_spec {p : Nat → Prop} (h : ∃ n, p n) : p (minWitness h) :=
  (Classical.choose_spec (exists_min h.choose h.choose_spec)).1

/-- Nothing below the least witness satisfies the predicate. -/
theorem minWitness_min {p : Nat → Prop} (h : ∃ n, p n) {k : Nat}
    (hk : k < minWitness h) : ¬ p k :=
  (Classical.choose_spec (exists_min h.choose h.choose_spec)).2 k hk

/-! ### Miss–hit fairness and counters -/

/-- `P` holds at infinitely many positions. -/
def InfOften (P : Nat → Prop) : Prop := ∀ n, ∃ m ≥ n, P m

/-- Miss–hit fairness: infinitely many misses force infinitely many hits (`□◇ miss → □◇ hit`). -/
def Fair (hit miss : Nat → Prop) : Prop := InfOften miss → InfOften hit

/-- The miss–hit counter: zero at a hit, down by one at a miss, unchanged otherwise. -/
def IsCounter (hit miss : Nat → Prop) (δ : Nat → Nat) : Prop :=
  (∀ n, hit n → δ n = 0) ∧ (∀ n, miss n → δ n = δ (n + 1) + 1) ∧
  (∀ n, ¬ hit n → ¬ miss n → δ n = δ (n + 1))

/-- A predicate that does not hold infinitely often fails from some position on. -/
theorem eventually_not_of_not_infOften {P : Nat → Prop} (h : ¬ InfOften P) :
    ∃ N, ∀ m ≥ N, ¬ P m :=
  Classical.byContradiction fun hc =>
    h fun n => Classical.byContradiction fun hn => hc ⟨n, fun m hm hP => hn ⟨m, hm, hP⟩⟩

/-- A predicate that does not fail from some position on holds infinitely often. -/
theorem infOften_of_not_eventually {P : Nat → Prop} (h : ¬ ∃ N, ∀ m ≥ N, ¬ P m) :
    InfOften P :=
  fun n => Classical.byContradiction fun hn => h ⟨n, fun m hm hP => hn ⟨m, hm, hP⟩⟩

/-! ### The oracle budget (`Count`) -/

section Defs

variable (hit miss : Nat → Prop)

open Classical in
/-- The first hit at or after `n`, if any. -/
noncomputable def firstHit? (n : Nat) : Option Nat :=
  if h : ∃ H, n ≤ H ∧ hit H then some (minWitness h) else none

open Classical in
/-- The number of misses in `[n, n + k)`. -/
noncomputable def countMiss (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if miss n then 1 else 0) + countMiss (n + 1) k

open Classical in
/-- The least time after which there are no misses, if there is one; `0` otherwise. -/
noncomputable def missBound : Nat :=
  if h : ∃ N, ∀ m ≥ N, ¬ miss m then minWitness h else 0

/-- The end of the counting window from `n`: the first hit at or after `n` if there is one,
else `max n (missBound miss)`. -/
noncomputable def horizon (n : Nat) : Nat :=
  match firstHit? hit n with
  | some H => H
  | none => max n (missBound miss)

/-- The oracle budget at `n`: the number of misses in `[n, horizon hit miss n)`. -/
noncomputable def budget (n : Nat) : Nat := countMiss miss n (horizon hit miss n - n)

end Defs

section Budget

variable {hit miss : Nat → Prop}

/-- `firstHit? hit n` is `H` exactly when `H` is the first hit at or after `n`. -/
theorem firstHit?_eq_some_iff {n H : Nat} :
    firstHit? hit n = some H ↔ n ≤ H ∧ hit H ∧ ∀ m, n ≤ m → m < H → ¬ hit m := by
  unfold firstHit?
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨(minWitness_spec h).1, (minWitness_spec h).2,
        fun _ hm hmH hhit => minWitness_min h hmH ⟨hm, hhit⟩⟩
    · rintro ⟨hnH, hH, hmin⟩
      apply Nat.le_antisymm
      · exact Nat.le_of_not_lt fun hlt => minWitness_min h hlt ⟨hnH, hH⟩
      · exact Nat.le_of_not_lt fun hlt =>
          hmin _ (minWitness_spec h).1 hlt (minWitness_spec h).2
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hnH, hH, -⟩
    exact h ⟨H, hnH, hH⟩

/-- `firstHit? hit n` is `none` exactly when there is no hit at or after `n`. -/
theorem firstHit?_eq_none_iff {n : Nat} :
    firstHit? hit n = none ↔ ∀ m ≥ n, ¬ hit m := by
  unfold firstHit?
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    obtain ⟨H, hnH, hH⟩ := h
    exact fun hno => hno H hnH hH
  · rename_i h
    simp only [true_iff]
    exact fun m hm hhit => h ⟨m, hm, hhit⟩

/-- At a hit, the first hit is the position itself. -/
theorem firstHit?_of_hit {n : Nat} (h : hit n) : firstHit? hit n = some n :=
  firstHit?_eq_some_iff.2 ⟨Nat.le_refl n, h, fun _ hm hmn => absurd hm (Nat.not_le.2 hmn)⟩

/-- Where there is no hit, the first hit comes strictly later. -/
theorem lt_of_firstHit?_eq_some {n H : Nat} (hn : ¬ hit n) (h : firstHit? hit n = some H) :
    n < H := by
  obtain ⟨hnH, hH, -⟩ := firstHit?_eq_some_iff.1 h
  exact Nat.lt_of_le_of_ne hnH fun e => hn (e ▸ hH)

/-- Past a position that is not a hit, the first hit is the same. -/
theorem firstHit?_succ_of_some {n H : Nat} (hn : ¬ hit n) (h : firstHit? hit n = some H) :
    firstHit? hit (n + 1) = some H := by
  obtain ⟨-, hH, hmin⟩ := firstHit?_eq_some_iff.1 h
  exact firstHit?_eq_some_iff.2 ⟨lt_of_firstHit?_eq_some hn h, hH,
    fun m hm hmH => hmin m (Nat.le_of_succ_le hm) hmH⟩

/-- With no hit at or after `n`, there is none at or after `n + 1` either. -/
theorem firstHit?_succ_of_none {n : Nat} (h : firstHit? hit n = none) :
    firstHit? hit (n + 1) = none :=
  firstHit?_eq_none_iff.2 fun m hm => firstHit?_eq_none_iff.1 h m (Nat.le_of_succ_le hm)

/-- An empty window has no misses. -/
@[simp] theorem countMiss_zero (n : Nat) : countMiss miss n 0 = 0 := rfl

/-- A window that starts at a miss counts it and the rest. -/
theorem countMiss_succ_of_miss {n : Nat} (h : miss n) (k : Nat) :
    countMiss miss n (k + 1) = countMiss miss (n + 1) k + 1 := by
  rw [countMiss, ite_eq_left h, Nat.add_comm]

/-- A window that starts at a position that is not a miss counts the rest only. -/
theorem countMiss_succ_of_not_miss {n : Nat} (h : ¬ miss n) (k : Nat) :
    countMiss miss n (k + 1) = countMiss miss (n + 1) k := by
  rw [countMiss, ite_eq_right h, Nat.zero_add]

/-- When the misses stop, there is none at or after `missBound miss`. -/
theorem missBound_spec (h : ∃ N, ∀ m ≥ N, ¬ miss m) {m : Nat} (hm : missBound miss ≤ m) :
    ¬ miss m := by
  unfold missBound at hm
  rw [dite_eq_left h] at hm
  exact minWitness_spec h m hm

/-- When the misses stop, every miss is before `missBound miss`. -/
theorem lt_missBound_of_miss (h : ∃ N, ∀ m ≥ N, ¬ miss m) {n : Nat} (hn : miss n) :
    n < missBound miss :=
  Nat.lt_of_not_le fun hle => missBound_spec h hle hn

/-- At a hit, the window ends where it starts. -/
theorem horizon_of_hit {n : Nat} (h : hit n) : horizon hit miss n = n := by
  simp only [horizon, firstHit?_of_hit h]

/-- Past a position that is not a hit and before the horizon, the horizon is the same. -/
theorem horizon_succ_of_lt {n : Nat} (hn : ¬ hit n) (hlt : n < horizon hit miss n) :
    horizon hit miss (n + 1) = horizon hit miss n := by
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh, firstHit?_succ_of_none hfh] at hlt ⊢
    omega
  · simp only [horizon, hfh, firstHit?_succ_of_some hn hfh]

/-- Past a position that is not a hit and at or past the horizon, the window from the next position
is empty. -/
theorem horizon_succ_of_le {n : Nat} (hn : ¬ hit n) (hle : horizon hit miss n ≤ n) :
    horizon hit miss (n + 1) = n + 1 := by
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh, firstHit?_succ_of_none hfh] at hle ⊢
    omega
  · simp only [horizon, hfh] at hle
    exact absurd hle (Nat.not_le.2 (lt_of_firstHit?_eq_some hn hfh))

/-- With hits and misses exclusive and the misses stopping where the hits stop, a miss is before the
horizon. -/
theorem lt_horizon_of_miss (hex : ∀ n, ¬ (hit n ∧ miss n))
    (hfin : ∀ n, (∀ m ≥ n, ¬ hit m) → ∃ N, ∀ m ≥ N, ¬ miss m)
    {n : Nat} (hm : miss n) : n < horizon hit miss n := by
  have hn : ¬ hit n := fun hh => hex n ⟨hh, hm⟩
  rcases hfh : firstHit? hit n with _ | H
  · simp only [horizon, hfh]
    have hN := lt_missBound_of_miss (hfin n (firstHit?_eq_none_iff.1 hfh)) hm
    omega
  · simp only [horizon, hfh]
    exact lt_of_firstHit?_eq_some hn hfh

/-- The budget is zero at a hit. -/
theorem budget_hit {n : Nat} (h : hit n) : budget hit miss n = 0 := by
  simp only [budget, horizon_of_hit h, Nat.sub_self, countMiss_zero]

/-- The budget's window from `n` and from `n + 1` end at the same horizon when `n` is not a hit
and the window is nonempty. -/
theorem budget_succ_of_lt {n : Nat} (hn : ¬ hit n) (hlt : n < horizon hit miss n) :
    budget hit miss n = countMiss miss n (horizon hit miss (n + 1) - (n + 1) + 1) := by
  rw [budget, horizon_succ_of_lt hn hlt]
  congr 1
  omega

/-- Under the same hypotheses, the budget drops by one at a miss. -/
theorem budget_miss (hex : ∀ n, ¬ (hit n ∧ miss n))
    (hfin : ∀ n, (∀ m ≥ n, ¬ hit m) → ∃ N, ∀ m ≥ N, ¬ miss m)
    {n : Nat} (hm : miss n) : budget hit miss n = budget hit miss (n + 1) + 1 := by
  have hn : ¬ hit n := fun hh => hex n ⟨hh, hm⟩
  rw [budget_succ_of_lt hn (lt_horizon_of_miss hex hfin hm), countMiss_succ_of_miss hm]
  rfl

/-- The budget is unchanged at a position that is neither a hit nor a miss. -/
theorem budget_step {n : Nat} (hn : ¬ hit n) (hm : ¬ miss n) :
    budget hit miss n = budget hit miss (n + 1) := by
  rcases Nat.lt_or_ge n (horizon hit miss n) with hlt | hle
  · rw [budget_succ_of_lt hn hlt, countMiss_succ_of_not_miss hm]
    rfl
  · rw [budget, budget, horizon_succ_of_le hn hle, Nat.sub_self,
      Nat.sub_eq_zero_of_le hle, countMiss_zero, countMiss_zero]

/-! ### Miss–hit fairness is the existence of a counter: the two main theorems -/

/-- Under miss–hit fairness, with hits and misses exclusive, `budget hit miss` is a miss–hit
counter. -/
theorem counter_spec (hex : ∀ n, ¬ (hit n ∧ miss n)) (hmh : Fair hit miss) :
    IsCounter hit miss (budget hit miss) := by
  refine ⟨fun n h => budget_hit h, fun n hm => budget_miss hex ?_ hm,
    fun n hh hm => budget_step hh hm⟩
  intro k hno
  apply Classical.byContradiction
  intro hfin
  obtain ⟨m, hm, hh⟩ := hmh (infOften_of_not_eventually hfin) k
  exact hno m hm hh

/-- A miss–hit counter gives miss–hit fairness. -/
theorem fair_of_counter {δ : Nat → Nat} (hδ : IsCounter hit miss δ) : Fair hit miss := by
  obtain ⟨-, hdec, hconst⟩ := hδ
  intro hinf
  apply Classical.byContradiction
  intro hno
  obtain ⟨N, hN⟩ := eventually_not_of_not_infOften hno
  have hmono : ∀ a k, N ≤ a → δ (a + k) ≤ δ a := by
    intro a k ha
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      have hhit : ¬ hit (a + k) := hN _ (Nat.le_trans ha (Nat.le_add_right a k))
      rw [← Nat.add_assoc]
      by_cases hm : miss (a + k)
      · have := hdec _ hm
        omega
      · have := hconst _ hhit hm
        omega
  have key : ∀ j, ∃ k, δ (N + k) + j ≤ δ N := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.le_refl _⟩
    | succ j ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨m, hm, hmiss⟩ := hinf (N + k)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      have h₁ := hdec _ hmiss
      have h₂ := hmono (N + k) d (Nat.le_add_right N k)
      have e : N + (k + d + 1) = N + k + d + 1 := by omega
      refine ⟨k + d + 1, ?_⟩
      rw [e]
      omega
  obtain ⟨k, hk⟩ := key (δ N + 1)
  omega

/-- Miss–hit fairness, with hits and misses exclusive, is the existence of a miss–hit
counter. -/
theorem fair_iff_counter (hex : ∀ n, ¬ (hit n ∧ miss n)) :
    Fair hit miss ↔ ∃ δ, IsCounter hit miss δ :=
  ⟨fun hmh => ⟨budget hit miss, counter_spec hex hmh⟩, fun ⟨_, hδ⟩ => fair_of_counter hδ⟩

end Budget

/-! ### Restriction

Fairness is monotone: more hits and fewer misses keep it (`fair_mono`).  It can also be read
through any set of *attempts* that contains the misses and is covered by the hits and the misses:
infinitely many attempts force infinitely many hits (`fair_iff_attempt`).  The layers above use
the two to restrict a fairness statement.  `SF` is fairness read through the positions where the
action is enabled, and a thread's view has the hits of `SF` and fewer misses. -/

/-- Holding infinitely often is monotone in the predicate. -/
theorem infOften_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (hP : InfOften P) : InfOften Q :=
  fun n => let ⟨m, hm, hPm⟩ := hP n; ⟨m, hm, h m hPm⟩

/-- Fairness is monotone: more hits and fewer misses keep it. -/
theorem fair_mono {hit hit' miss miss' : Nat → Prop} (hh : ∀ n, hit n → hit' n)
    (hm : ∀ n, miss' n → miss n) (h : Fair hit miss) : Fair hit' miss' :=
  fun hinf => infOften_mono hh (h (infOften_mono hm hinf))

/-- Fairness read through attempts: when every miss is an attempt and every attempt is a hit or a
miss, fairness says that infinitely many attempts force infinitely many hits. -/
theorem fair_iff_attempt {hit miss attempt : Nat → Prop} (hmiss : ∀ n, miss n → attempt n)
    (hatt : ∀ n, attempt n → hit n ∨ miss n) :
    Fair hit miss ↔ (InfOften attempt → InfOften hit) := by
  constructor
  · intro hf hinf
    apply Classical.byContradiction
    intro hno
    obtain ⟨N, hN⟩ := eventually_not_of_not_infOften hno
    apply hno
    apply hf
    intro n
    obtain ⟨m, hm, ham⟩ := hinf (n + N)
    have hhm : ¬ hit m := hN m (Nat.le_trans (Nat.le_add_left N n) hm)
    exact ⟨m, Nat.le_trans (Nat.le_add_right n N) hm, (hatt m ham).resolve_left hhm⟩
  · intro h hinf
    exact h (infOften_mono hmiss hinf)

/-! ### What a counter bounds

A miss has a positive counter, and until the next hit the counter dominates the misses to come.
These are the facts a thread consumes from its counter. -/

section Bounds

variable {hit miss : Nat → Prop} {δ : Nat → Nat} {n : Nat}

/-- A miss has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter hit miss δ) (h : miss n) : 0 < δ n := by
  have := hδ.2.1 n h
  omega

/-- The bound: with no hit in `[n, n + k)`, the misses in that window plus the counter at its end
are at most the counter at `n`. -/
theorem counter_bounds_misses (hδ : IsCounter hit miss δ) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < n + k → ¬ hit m) → δ (n + k) + countMiss miss n k ≤ δ n := by
  intro k
  induction k generalizing n with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hno
    have hn : ¬ hit n := hno n (Nat.le_refl n) (by omega)
    have ih' := ih (n + 1) (fun m hm1 hm2 => hno m (by omega) (by omega))
    have e : n + (k + 1) = n + 1 + k := by omega
    rw [e]
    rcases Classical.em (miss n) with hm | hm
    · rw [countMiss_succ_of_miss hm]
      have := hδ.2.1 n hm
      omega
    · rw [countMiss_succ_of_not_miss hm]
      have := hδ.2.2 n hn hm
      omega

end Bounds

end MissHit

/-! ## 2. The pool: configurations, a thread's step, a run

A configuration is MachCSL's thread pool and global state, and a run is a sequence of
configurations.  These definitions are all that the general theory (sections 1 and 3–5) takes from
MachCSL.  Layer 1 uses configurations only; layers 2 and 3 also use a thread's step. -/

open MachCSL Sail Sail.ArchSem LeanRV64D

/-- A configuration: the thread pool and the global state. -/
abbrev Cfg := List Expr × GState

/-- The thread at position `i` takes a primitive step from `c` to `c'`. -/
def Step (i : Nat) (c c' : Cfg) : Prop :=
  ∃ e obs e' efs, c.1[i]? = some e ∧ primStep (e, c.2) obs (e', c'.2, efs) ∧
    c'.1 = c.1.set i e' ++ efs

/-- The thread at position `i` steps at position `n` of the run `σ`. -/
def Steps (i : Nat) (σ : Nat → Cfg) (n : Nat) : Prop := Step i (σ n) (σ (n + 1))

/-- Every position of the run is a step of some thread. -/
def PoolRun (σ : Nat → Cfg) : Prop := ∀ n, ∃ j, Step j (σ n) (σ (n + 1))

/-- The thread at `i` steps infinitely often: what fair scheduling gives a live thread (and
what a corpse's self-loops give a dead one). -/
def StepsInfOften (i : Nat) (σ : Nat → Cfg) : Prop := ∀ n, ∃ m ≥ n, Steps i σ m

section Pool

variable {i j : Nat} {c c' : Cfg}

/-- A step of the thread at `j` leaves every other position of the pool as it was. -/
theorem step_get?_ne {e : Expr} (hs : Step j c c') (hji : j ≠ i) (he : c.1[i]? = some e) :
    c'.1[i]? = some e := by
  obtain ⟨_, _, e', efs, _, _, hc'⟩ := hs
  have hi : i < c.1.length := (List.getElem?_eq_some_iff.1 he).1
  rw [hc', List.getElem?_append_left (by simpa using hi), List.getElem?_set_ne hji, he]

end Pool

/-! ## 3. Layer 1: the state form of an action (`Action`)

An action is an enabling condition `A` on configurations and a grant relation `G` on pairs of
configurations.  Its strong fairness `SF` says that where `A` holds infinitely often, a grant
happens infinitely often.  `SF` is the trusted form of every fairness assumption, and it names no
thread.  This layer takes miss–hit fairness from layer 0 and configurations from the pool.

`SF` is itself a miss–hit pair (`sf_iff_fair`).  A hit is a position where `A` holds and the step
taken is a grant.  A miss is a position where `A` holds and the step taken is not a grant, whoever
takes it.  So `SF` is the existence of a counter (`sf_iff_counter`), and the counter moves at any
step, whoever takes it: it resets at a grant, drops at a refused position and stays where `A`
fails.  This is the fundamental theory of fairness in this file.

Lantana's trace side implements exactly this layer: one counter per declared action, updated at
every step (the owner's decision of 2026-11-06).  How a thread learns of an update of the counter
at another thread's step is the program logic's business.  Layer 3 (section 5) avoids the question
for the actions whose grant is one of the thread's own transitions. -/

namespace Action

/-! ### Definitions -/

/-- Position `n` is granted: `A` holds there and the step taken is a grant, whoever takes it. -/
def hit (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  A (σ n) ∧ G (σ n) (σ (n + 1))

/-- Position `n` is refused: `A` holds there and the step taken is not a grant, whoever takes
it. -/
def miss (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  A (σ n) ∧ ¬ G (σ n) (σ (n + 1))

/-- Strong fairness of the action: `A` holding infinitely often forces infinitely many grants.
The trusted form of every fairness assumption. -/
def SF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  MissHit.InfOften (fun n => A (σ n)) → MissHit.InfOften (hit A G σ)

/-- The response form: every position where `A` holds is followed by a granted position, at it
or later. -/
def Response (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → ∃ m ≥ n, hit A G σ m

/-- Weak fairness of the action: `A` holding from some position on forces infinitely many
grants. -/
def WF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  (∃ N, ∀ n, N ≤ n → A (σ n)) → MissHit.InfOften (hit A G σ)

/-- The grant is certain: every position where `A` holds is granted. -/
def Certain (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → G (σ n) (σ (n + 1))

/-- The counter of the action: zero at a granted position, one more at a refused position than at
the next, unchanged where `A` fails. -/
def IsCounter (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (δ : Nat → Nat) : Prop :=
  MissHit.IsCounter (hit A G σ) (miss A G σ) δ

variable {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat} {n : Nat}

/-! ### `SF` is miss–hit fairness, and the existence of a counter -/

/-- No position is both granted and refused. -/
theorem hit_miss_exclusive : ¬ (hit A G σ n ∧ miss A G σ n) := fun ⟨hh, hm⟩ => hm.2 hh.2

/-- `A` holds exactly at the granted and the refused positions. -/
theorem enabled_iff : A (σ n) ↔ hit A G σ n ∨ miss A G σ n :=
  ⟨fun hA => (Classical.em (G (σ n) (σ (n + 1)))).imp (And.intro hA) (And.intro hA),
    fun h => h.elim And.left And.left⟩

/-- `SF` is miss–hit fairness of the action's pair, read through the positions where `A`
holds. -/
theorem sf_iff_fair : SF A G σ ↔ MissHit.Fair (hit A G σ) (miss A G σ) :=
  (MissHit.fair_iff_attempt (fun _ hm => hm.1) fun _ hA => enabled_iff.1 hA).symm

/-- `SF` is the existence of a counter. -/
theorem sf_iff_counter : SF A G σ ↔ ∃ δ, IsCounter A G σ δ :=
  sf_iff_fair.trans (MissHit.fair_iff_counter fun _ => hit_miss_exclusive)

/-- `SF` gives a counter. -/
theorem counter_of_sf (hsf : SF A G σ) : ∃ δ, IsCounter A G σ δ := sf_iff_counter.1 hsf

/-- A counter gives `SF`. -/
theorem sf_of_counter (hδ : IsCounter A G σ δ) : SF A G σ := sf_iff_counter.2 ⟨δ, hδ⟩

/-! ### The counter rules, at any position of the run

At the step from `σ n` to `σ (n + 1)`, whoever takes it: if `A` holds and the step is a grant, the
counter resets; if `A` holds and the step is not a grant, it drops; if `A` fails, it stays. -/

/-- Reset: the counter is zero at a granted position. -/
theorem counter_reset (hδ : IsCounter A G σ δ) (hA : A (σ n)) (hG : G (σ n) (σ (n + 1))) :
    δ n = 0 :=
  hδ.1 n ⟨hA, hG⟩

/-- Drop: at a refused position the counter is one more than at the next position. -/
theorem counter_drop (hδ : IsCounter A G σ δ) (hA : A (σ n)) (hG : ¬ G (σ n) (σ (n + 1))) :
    δ n = δ (n + 1) + 1 :=
  hδ.2.1 n ⟨hA, hG⟩

/-- Stay: where `A` fails the counter is unchanged. -/
theorem counter_stay (hδ : IsCounter A G σ δ) (hA : ¬ A (σ n)) : δ n = δ (n + 1) :=
  hδ.2.2 n (fun h => hA h.1) (fun h => hA h.1)

/-- A refused position has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter A G σ δ) (h : miss A G σ n) : 0 < δ n :=
  MissHit.counter_pos_of_miss hδ h

/-- A position where `A` holds and the counter is zero is granted. -/
theorem hit_of_enabled_of_counter_zero (hδ : IsCounter A G σ δ) (hA : A (σ n)) (h0 : δ n = 0) :
    hit A G σ n :=
  (enabled_iff.1 hA).resolve_right fun h => Nat.ne_of_gt (counter_pos_of_miss hδ h) h0

/-- The bound: with no grant in `[n, n + k)`, the refused positions in that window plus the
counter at its end are at most the counter at `n`. -/
theorem counter_bounds_misses (hδ : IsCounter A G σ δ) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < n + k → ¬ hit A G σ m) →
      δ (n + k) + MissHit.countMiss (miss A G σ) n k ≤ δ n :=
  MissHit.counter_bounds_misses hδ n

/-! ### The variants: response, weak fairness, a certain grant

The response form gives `SF`, and `SF` gives weak fairness `WF`.  A certain grant has no refused
position, so it gives the response form and `SF` outright, and its counter is zero. -/

/-- The response form gives `SF`. -/
theorem sf_of_response (h : Response A G σ) : SF A G σ :=
  fun hinf n =>
    let ⟨m, hm, hAm⟩ := hinf n
    let ⟨k, hk, hhit⟩ := h m hAm
    ⟨k, Nat.le_trans hm hk, hhit⟩

/-- `SF` gives weak fairness. -/
theorem wf_of_sf (hsf : SF A G σ) : WF A G σ :=
  fun ⟨N, hN⟩ => hsf fun n => ⟨n + N, Nat.le_add_right n N, hN _ (Nat.le_add_left N n)⟩

/-- A certain grant gives the response form: every position where `A` holds is granted at
once. -/
theorem response_of_certain (hc : Certain A G σ) : Response A G σ :=
  fun n hA => ⟨n, Nat.le_refl n, hA, hc n hA⟩

/-- A certain grant gives `SF` outright. -/
theorem sf_of_certain (hc : Certain A G σ) : SF A G σ := sf_of_response (response_of_certain hc)

/-- With a certain grant the zero function is a counter: there is no refused position. -/
theorem counter_zero_of_certain (hc : Certain A G σ) : IsCounter A G σ (fun _ => 0) :=
  ⟨fun _ _ => rfl, fun n hm => absurd (hc n hm.1) hm.2, fun _ _ _ => rfl⟩

end Action

/-! ## 4. Layer 2: a thread's pair of positions (`Pair`)

Two position predicates of a run, the thread's attempts and its hits (the granted attempts), taken
as primitives.  A miss is a refused attempt.  The layer takes miss–hit fairness from layer 0: the
attempt–grant form `AttemptGrant` is the fairness of the pair `(Hit, Miss)`, and its counter is the
counter of layer 0.

The pair is a thread's when two requirements hold.  R1 (`HitsAttempt`) says a hit is an attempt.
R2 (`OwnStep`) says an attempt is a step of the thread at `i`.  Then the counter never moves at
another thread's step (`counter_stay_of_other`), and the thread can consume it at its own steps
alone.  The pair of layer 1, with the positions where `A` holds as attempts, meets R1 and not R2.
A pair whose misses are among those of a fair pair with the same hits is fair
(`attemptGrant_of_fair`).  Lantana's witness kind is stated against this layer. -/

namespace Pair

/-! ### Definitions -/

/-- The refused attempts. -/
def Miss (Attempt Hit : Nat → Prop) (n : Nat) : Prop := Attempt n ∧ ¬ Hit n

/-- The attempt–grant form: infinitely many refused attempts force infinitely many hits. -/
def AttemptGrant (Attempt Hit : Nat → Prop) : Prop := MissHit.Fair Hit (Miss Attempt Hit)

/-- The counter of the pair: zero at a hit, one more at a miss than at the next position,
unchanged otherwise. -/
def IsCounter (Attempt Hit : Nat → Prop) (δ : Nat → Nat) : Prop :=
  MissHit.IsCounter Hit (Miss Attempt Hit) δ

/-- R1: a hit is an attempt. -/
def HitsAttempt (Attempt Hit : Nat → Prop) : Prop := ∀ n, Hit n → Attempt n

/-- R2: the attempts are steps of the thread at `i`. -/
def OwnStep (i : Nat) (σ : Nat → Cfg) (Attempt : Nat → Prop) : Prop :=
  ∀ n, Attempt n → Steps i σ n

variable {i : Nat} {σ : Nat → Cfg} {Attempt Hit : Nat → Prop} {δ : Nat → Nat} {n : Nat}

/-! ### Hits, misses and attempts -/

/-- A miss is an attempt. -/
theorem miss_attempt (h : Miss Attempt Hit n) : Attempt n := h.1

/-- No position is both a hit and a miss. -/
theorem hit_miss_exclusive : ¬ (Hit n ∧ Miss Attempt Hit n) := fun ⟨hh, hm⟩ => hm.2 hh

/-- An attempt is a hit or a miss (R1). -/
theorem attempt_iff (h1 : HitsAttempt Attempt Hit) : Attempt n ↔ Hit n ∨ Miss Attempt Hit n :=
  ⟨fun ha => (Classical.em (Hit n)).imp_right (And.intro ha),
    fun h => h.elim (h1 n) miss_attempt⟩

/-- A hit is a step of the thread (R1 and R2). -/
theorem hit_steps (h1 : HitsAttempt Attempt Hit) (h2 : OwnStep i σ Attempt) (h : Hit n) :
    Steps i σ n :=
  h2 n (h1 n h)

/-- A miss is a step of the thread (R2). -/
theorem miss_steps (h2 : OwnStep i σ Attempt) (h : Miss Attempt Hit n) : Steps i σ n :=
  h2 n h.1

/-- The meaning: infinitely many attempts force infinitely many hits.  No requirement is
needed. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant Attempt Hit ↔ (MissHit.InfOften Attempt → MissHit.InfOften Hit) :=
  MissHit.fair_iff_attempt (fun _ => miss_attempt) fun n ha =>
    (Classical.em (Hit n)).imp_right (And.intro ha)

/-! ### The counter -/

/-- The attempt–grant form is the existence of a counter. -/
theorem attemptGrant_iff_counter : AttemptGrant Attempt Hit ↔ ∃ δ, IsCounter Attempt Hit δ :=
  MissHit.fair_iff_counter fun _ => hit_miss_exclusive

/-- The attempt–grant form gives a counter. -/
theorem counter_of_attemptGrant (hag : AttemptGrant Attempt Hit) :
    ∃ δ, IsCounter Attempt Hit δ :=
  attemptGrant_iff_counter.1 hag

/-- A counter gives the attempt–grant form. -/
theorem attemptGrant_of_counter (hδ : IsCounter Attempt Hit δ) : AttemptGrant Attempt Hit :=
  attemptGrant_iff_counter.2 ⟨δ, hδ⟩

/-- Reset: the counter is zero at a hit. -/
theorem counter_reset (hδ : IsCounter Attempt Hit δ) (h : Hit n) : δ n = 0 := hδ.1 n h

/-- Drop: at a miss the counter is one more than at the next position. -/
theorem counter_drop (hδ : IsCounter Attempt Hit δ) (h : Miss Attempt Hit n) :
    δ n = δ (n + 1) + 1 :=
  hδ.2.1 n h

/-- Stay: the counter is unchanged at a position that is not an attempt (R1). -/
theorem counter_stay_of_not_attempt (h1 : HitsAttempt Attempt Hit) (hδ : IsCounter Attempt Hit δ)
    (h : ¬ Attempt n) : δ n = δ (n + 1) :=
  hδ.2.2 n (fun hh => h (h1 n hh)) (fun hm => h hm.1)

/-- Stay: the counter is unchanged at every step that is not the thread's (R1 and R2).  The one
rule that names a thread. -/
theorem counter_stay_of_other (h1 : HitsAttempt Attempt Hit) (h2 : OwnStep i σ Attempt)
    (hδ : IsCounter Attempt Hit δ) (hs : ¬ Steps i σ n) : δ n = δ (n + 1) :=
  counter_stay_of_not_attempt h1 hδ fun ha => hs (h2 n ha)

/-- A miss has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter Attempt Hit δ) (h : Miss Attempt Hit n) : 0 < δ n :=
  MissHit.counter_pos_of_miss hδ h

/-- The base case of the thread's induction: an attempt made at counter zero is a hit. -/
theorem hit_of_attempt_of_counter_zero (hδ : IsCounter Attempt Hit δ) (ha : Attempt n)
    (h0 : δ n = 0) : Hit n :=
  Classical.byContradiction fun hh => Nat.ne_of_gt (counter_pos_of_miss hδ ⟨ha, hh⟩) h0

/-- The bound: until the next hit, the counter at `n` dominates the misses to come.  With no hit
in `[n, n + k)`, the misses in that window plus the counter at its end are at most the counter at
`n`. -/
theorem counter_bounds_misses (hδ : IsCounter Attempt Hit δ) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < n + k → ¬ Hit m) →
      δ (n + k) + MissHit.countMiss (Miss Attempt Hit) n k ≤ δ n :=
  MissHit.counter_bounds_misses hδ n

/-! ### Statements that give the attempt–grant form -/

/-- A response property gives the form: every attempt is followed by a hit, at the attempt or
later. -/
theorem attemptGrant_of_response (h : ∀ n, Attempt n → ∃ m ≥ n, Hit m) :
    AttemptGrant Attempt Hit :=
  fun hmiss n =>
    let ⟨m, hm, hmiss_m⟩ := hmiss n
    let ⟨k, hk, hhit⟩ := h m hmiss_m.1
    ⟨k, Nat.le_trans hm hk, hhit⟩

/-- A pair whose misses are among the misses of a fair pair with the same hits is fair: the
restriction of a fairness statement to a thread. -/
theorem attemptGrant_of_fair {Enabled : Nat → Prop} (hsub : ∀ n, Miss Attempt Hit n → Enabled n)
    (h : MissHit.Fair Hit Enabled) : AttemptGrant Attempt Hit :=
  MissHit.fair_mono (fun _ hh => hh) hsub h

end Pair

/-! ## 5. Layer 3: the thread's view of an action (`Thread`)

The thread's view restricts the action's pair of layer 1 to the thread's own steps.  An attempt is
a step of the thread at `i` from a configuration where `A` holds; a hit is a granted attempt; a
miss is a refused attempt.  The view is a thread's pair of layer 2 by construction: R1 and R2 hold
for every action (`hitsAttempt`, `ownStep`).  So its counter moves only at the thread's own steps
(`counter_stay_of_other`), and the thread can consume it there with no help from the logic.  This
is the cheap path, which Lantana takes for a declared action with own grant.

The view is sound under own grant (`OwnGrant`), which says that every grant is a step of the
thread.  Then the action's granted positions are the thread's hits, every miss of the thread is a
refused position of the action, and `SF` gives the attempt–grant form (`attemptGrant_of_sf`).  The
view loses nothing under persistence of `A` and fair scheduling of the thread
(`sf_of_attemptGrant`), so the two forms coincide (`sf_iff_attemptGrant`).  Without own grant a
grant may happen at another thread's step.  The thread must then use the counter of layer 1, and
the logic must tell it of the updates at the other threads' steps.

The two layers' certain grants differ.  At layer 1 a certain grant covers every position where `A`
holds, whoever steps, and gives `SF` outright (`Action.sf_of_certain`).  At layer 3 it covers the
thread's own attempts only (`Certain`); it gives the attempt–grant form outright, and `SF` only
with persistence and fair scheduling (`sf_of_certain`).  A device task at a gate (7.5) is the
layer-3 case. -/

namespace Thread

/-! ### Definitions -/

/-- The thread at `i` attempts at `n`: it steps there from a configuration where `A` holds. -/
def attempt (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := Steps i σ n ∧ A (σ n)

/-- The thread's attempt at `n` is granted: the thread steps from a configuration where `A` holds,
and its step is a grant. -/
def hit (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  attempt i A σ n ∧ G (σ n) (σ (n + 1))

/-- The thread's attempt at `n` is refused. -/
def miss (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  Pair.Miss (attempt i A σ) (hit i A G σ) n

/-- The attempt–grant form of the thread's view: infinitely many refused attempts force infinitely
many granted ones.  The form the logic consumes. -/
def AttemptGrant (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  Pair.AttemptGrant (attempt i A σ) (hit i A G σ)

/-- The counter of the thread's view: zero at a granted attempt, one more at a refused attempt
than at the next position, unchanged otherwise. -/
def IsCounter (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (δ : Nat → Nat) :
    Prop :=
  Pair.IsCounter (attempt i A σ) (hit i A G σ) δ

/-- Own grant: the grant is one of the thread's transitions.  The property that makes the thread's
view sound. -/
def OwnGrant (i : Nat) (G : Cfg → Cfg → Prop) : Prop := ∀ {c c' : Cfg}, G c c' → Step i c c'

/-- The grant is certain at the thread's attempts: every attempt of the thread at `i` is
granted. -/
def Certain (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, attempt i A σ n → G (σ n) (σ (n + 1))

/-- `A` is stable under every other thread's step. -/
def Stable (i : Nat) (A : Cfg → Prop) : Prop :=
  ∀ {j : Nat} {c c' : Cfg}, j ≠ i → Step j c c' → A c → A c'

/-- `A` persists along the run: where it holds, the thread steps now, or `A` still holds at the
next position, or `A` never holds again.  The general interface: it says nothing about how `A`
can be lost. -/
def Persists (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → Steps i σ n ∨ A (σ (n + 1)) ∨ ∀ m, n < m → ¬ A (σ m)

variable {i : Nat} {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat}
  {n : Nat}

/-! ### The pair is the thread's, by construction -/

/-- R1 holds for every action: a hit is an attempt. -/
theorem hitsAttempt : Pair.HitsAttempt (attempt i A σ) (hit i A G σ) := fun _ h => h.1

/-- R2 holds for every action: an attempt is a step of the thread. -/
theorem ownStep : Pair.OwnStep i σ (attempt i A σ) := fun _ h => h.1

/-- A miss is a step of the thread from a configuration where `A` holds that is not a grant. -/
theorem miss_iff : miss i A G σ n ↔ Steps i σ n ∧ A (σ n) ∧ ¬ G (σ n) (σ (n + 1)) :=
  ⟨fun ⟨⟨hs, hA⟩, hh⟩ => ⟨hs, hA, fun hG => hh ⟨⟨hs, hA⟩, hG⟩⟩,
    fun ⟨hs, hA, hG⟩ => ⟨⟨hs, hA⟩, fun hh => hG hh.2⟩⟩

/-- The meaning of the attempt–grant form: a thread that attempts infinitely often is granted
infinitely often. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant i A G σ ↔ (MissHit.InfOften (attempt i A σ) → MissHit.InfOften (hit i A G σ)) :=
  Pair.attemptGrant_iff_attempt

/-! ### Against the state form

A hit of the thread is a granted position of the action, and under own grant the converse holds.
A miss of the thread is a refused position of the action. -/

/-- A hit of the thread is a granted position of the action. -/
theorem action_hit_of_hit (h : hit i A G σ n) : Action.hit A G σ n := ⟨h.1.2, h.2⟩

/-- Under own grant, a granted position of the action is a hit of the thread. -/
theorem hit_of_action_hit (hown : OwnGrant i G) (h : Action.hit A G σ n) : hit i A G σ n :=
  ⟨⟨hown h.2, h.1⟩, h.2⟩

/-- Under own grant, the thread's hits are the action's granted positions. -/
theorem hit_iff_action_hit (hown : OwnGrant i G) : hit i A G σ n ↔ Action.hit A G σ n :=
  ⟨action_hit_of_hit, hit_of_action_hit hown⟩

/-- A miss of the thread is a refused position of the action. -/
theorem action_miss_of_miss (h : miss i A G σ n) : Action.miss A G σ n :=
  ⟨h.1.2, fun hG => h.2 ⟨h.1, hG⟩⟩

/-! ### Soundness: under own grant, `SF` gives the thread's counter -/

/-- **Soundness.**  Under own grant, `SF` gives the attempt–grant form.  It is `MissHit.fair_mono`
applied to `Action.sf_iff_fair`: the thread has the action's hits (`hit_of_action_hit`) and fewer
misses (`action_miss_of_miss`). -/
theorem attemptGrant_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    AttemptGrant i A G σ :=
  MissHit.fair_mono (fun _ => hit_of_action_hit hown) (fun _ => action_miss_of_miss)
    (Action.sf_iff_fair.1 hsf)

/-- Under own grant, the response form gives the attempt–grant form. -/
theorem attemptGrant_of_response (hown : OwnGrant i G) (h : Action.Response A G σ) :
    AttemptGrant i A G σ :=
  Pair.attemptGrant_of_response fun n ha =>
    let ⟨m, hm, hhit⟩ := h n ha.2
    ⟨m, hm, hit_of_action_hit hown hhit⟩

/-- The attempt–grant form gives a counter. -/
theorem counter_of_attemptGrant (hag : AttemptGrant i A G σ) : ∃ δ, IsCounter i A G σ δ :=
  Pair.counter_of_attemptGrant hag

/-- A counter gives the attempt–grant form. -/
theorem attemptGrant_of_counter (hδ : IsCounter i A G σ δ) : AttemptGrant i A G σ :=
  Pair.attemptGrant_of_counter hδ

/-- Under own grant, the trusted form gives the thread's counter. -/
theorem counter_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    ∃ δ, IsCounter i A G σ δ :=
  counter_of_attemptGrant (attemptGrant_of_sf hown hsf)

/-! ### The counter rules, in terms of `A` and `G`

At the step from `σ n` to `σ (n + 1)`: if the thread steps, `A` holds and the step is a grant, the
counter resets; if the thread steps, `A` holds and the step is not a grant, it drops; if `A`
fails, it stays; if another thread steps, it stays.  The stay at another thread's step needs no
hypothesis, because the pair is the thread's. -/

/-- Reset: the counter is zero at a granted attempt. -/
theorem counter_reset (hδ : IsCounter i A G σ δ) (hs : Steps i σ n) (hA : A (σ n))
    (hG : G (σ n) (σ (n + 1))) : δ n = 0 :=
  Pair.counter_reset hδ ⟨⟨hs, hA⟩, hG⟩

/-- Drop: at a refused attempt the counter is one more than at the next position. -/
theorem counter_drop (hδ : IsCounter i A G σ δ) (hs : Steps i σ n) (hA : A (σ n))
    (hG : ¬ G (σ n) (σ (n + 1))) : δ n = δ (n + 1) + 1 :=
  Pair.counter_drop hδ ⟨⟨hs, hA⟩, fun hh => hG hh.2⟩

/-- Stay: where `A` fails the counter is unchanged. -/
theorem counter_stay_of_not_enabled (hδ : IsCounter i A G σ δ) (hA : ¬ A (σ n)) :
    δ n = δ (n + 1) :=
  Pair.counter_stay_of_not_attempt hitsAttempt hδ fun ha => hA ha.2

/-- Stay: at every step that is not the thread's the counter is unchanged. -/
theorem counter_stay_of_other (hδ : IsCounter i A G σ δ) (hs : ¬ Steps i σ n) :
    δ n = δ (n + 1) :=
  Pair.counter_stay_of_other hitsAttempt ownStep hδ hs

/-- A refused attempt has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter i A G σ δ) (h : miss i A G σ n) : 0 < δ n :=
  Pair.counter_pos_of_miss hδ h

/-- The base case of the thread's induction: an attempt made at counter zero is granted. -/
theorem hit_of_attempt_of_counter_zero (hδ : IsCounter i A G σ δ) (ha : attempt i A σ n)
    (h0 : δ n = 0) : hit i A G σ n :=
  Pair.hit_of_attempt_of_counter_zero hδ ha h0

/-- The bound: with no granted attempt in `[n, n + k)`, the refused attempts in that window plus
the counter at its end are at most the counter at `n`. -/
theorem counter_bounds_misses (hδ : IsCounter i A G σ δ) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < n + k → ¬ hit i A G σ m) →
      δ (n + k) + MissHit.countMiss (miss i A G σ) n k ≤ δ n :=
  Pair.counter_bounds_misses hδ n

/-! ### Completeness: under persistence and fair scheduling, the view gives `SF` back

Past the last grant, `A` holding at a position persists to the thread's next step, which is then
a refused attempt.  So infinitely many positions where `A` holds give infinitely many misses of the
thread, and the attempt–grant form gives infinitely many grants.  Persistence follows from
stability under the other threads' steps on any run of the pool (`persists_of_stable`). -/

/-- Stability gives persistence on any run of the pool. -/
theorem persists_of_stable (hrun : PoolRun σ) (hstab : Stable i A) : Persists i A σ := by
  intro n hA
  obtain ⟨j, hs⟩ := hrun n
  by_cases hji : j = i
  · subst hji
    exact Or.inl hs
  · exact Or.inr (Or.inl (hstab hji hs hA))

/-- A pending attempt survives the other threads' steps: if `A` is stable and holds at `n`, it
holds at every later position reached by other threads' steps only, in particular at the
thread's next step. -/
theorem attempt_pending (hstab : Stable i A) (hA : A (σ n)) {k : Nat} (hnk : n ≤ k)
    (hothers : ∀ k', n ≤ k' → k' < k → ∃ j, j ≠ i ∧ Step j (σ k') (σ (k' + 1))) : A (σ k) := by
  induction k with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnk
    subst h0
    exact hA
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hnk with hlt | heq
    · have hk := ih (Nat.le_of_lt_succ hlt)
        (fun k' h1 h2 => hothers k' h1 (Nat.lt_succ_of_lt h2))
      obtain ⟨j, hji, hs⟩ := hothers k (Nat.le_of_lt_succ hlt) (Nat.lt_succ_self k)
      exact hstab hji hs hk
    · subst heq
      exact hA

/-- **Completeness.**  Under fair scheduling of the thread and persistence of `A`, the
attempt–grant form gives `SF`. -/
theorem sf_of_attemptGrant (hsched : StepsInfOften i σ) (hper : Persists i A σ)
    (hag : AttemptGrant i A G σ) : Action.SF A G σ := by
  intro hA
  apply Classical.byContradiction
  intro hno
  obtain ⟨N, hN⟩ := MissHit.eventually_not_of_not_infOften hno
  apply hno
  refine MissHit.infOften_mono (fun _ => action_hit_of_hit) (hag fun n₀ => ?_)
  obtain ⟨n, hn, hAn⟩ := hA (n₀ + N)
  obtain ⟨m, hm, hsm⟩ := hsched n
  obtain ⟨m', ⟨hnm', hsm'⟩, hmin⟩ :=
    MissHit.exists_min (p := fun m => n ≤ m ∧ Steps i σ m) m ⟨hm, hsm⟩
  have hAk : ∀ k, n ≤ k → k ≤ m' → A (σ k) := by
    intro k hnk hkm
    induction k with
    | zero =>
      have h0 : n = 0 := Nat.le_zero.1 hnk
      subst h0
      exact hAn
    | succ k ih =>
      rcases Nat.lt_or_eq_of_le hnk with hlt | heq
      · have hk := ih (Nat.le_of_lt_succ hlt) (Nat.le_of_succ_le hkm)
        rcases hper k hk with hs | hA' | hgone
        · exact absurd ⟨Nat.le_of_lt_succ hlt, hs⟩
            (hmin k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkm))
        · exact hA'
        · obtain ⟨m'', hm'', hA''⟩ := hA (k + 1)
          exact absurd hA'' (hgone m'' (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hm''))
      · subst heq
        exact hAn
  have hAm := hAk m' hnm' (Nat.le_refl _)
  refine ⟨m', Nat.le_trans (Nat.le_add_right n₀ N) (Nat.le_trans hn hnm'), ⟨hsm', hAm⟩, ?_⟩
  intro hhit
  exact hN m' (Nat.le_trans (Nat.le_add_left N n₀) (Nat.le_trans hn hnm'))
    (action_hit_of_hit hhit)

/-- Under own grant, persistence and fair scheduling, the trusted form and the attempt–grant form
coincide. -/
theorem sf_iff_attemptGrant (hown : OwnGrant i G) (hsched : StepsInfOften i σ)
    (hper : Persists i A σ) : Action.SF A G σ ↔ AttemptGrant i A G σ :=
  ⟨attemptGrant_of_sf hown, sf_of_attemptGrant hsched hper⟩

/-! ### A grant certain at the thread's own attempts

When every attempt of the thread is granted, the thread's view has no misses.  Its attempt–grant
form holds outright and its counter is identically zero.  Weak fairness follows from fair
scheduling alone, and `SF` from fair scheduling and persistence.  The device task at a gate (7.5)
waits on whoever opens the gate, which is an obligation and not a fairness assumption. -/

/-- With a grant certain at the thread's attempts there are no misses, so the attempt–grant form
holds outright. -/
theorem attemptGrant_of_certain (hc : Certain i A G σ) : AttemptGrant i A G σ := by
  intro hmiss
  obtain ⟨m, -, ha, hh⟩ := hmiss 0
  exact absurd ⟨ha, hc m ha⟩ hh

/-- With a grant certain at the thread's attempts the zero function is a counter: reset at every
granted attempt, stay elsewhere, never a drop. -/
theorem counter_zero_of_certain (hc : Certain i A G σ) : IsCounter i A G σ (fun _ => 0) := by
  unfold IsCounter Pair.IsCounter MissHit.IsCounter
  exact ⟨fun _ _ => rfl, fun n hm => absurd ⟨hm.1, hc n hm.1⟩ hm.2, fun _ _ _ => rfl⟩

/-- With a grant certain at the thread's attempts, weak fairness follows from fair scheduling
alone. -/
theorem wf_of_certain (hsched : StepsInfOften i σ) (hc : Certain i A G σ) : Action.WF A G σ := by
  rintro ⟨N, hN⟩ n
  obtain ⟨m, hm, hs⟩ := hsched (n + N)
  have hA : A (σ m) := hN m (Nat.le_trans (Nat.le_add_left N n) hm)
  exact ⟨m, Nat.le_trans (Nat.le_add_right n N) hm, hA, hc m ⟨hs, hA⟩⟩

/-- With a grant certain at the thread's attempts, `SF` follows from fair scheduling and
persistence. -/
theorem sf_of_certain (hsched : StepsInfOften i σ) (hper : Persists i A σ)
    (hc : Certain i A G σ) : Action.SF A G σ :=
  sf_of_attemptGrant hsched hper (attemptGrant_of_certain hc)

end Thread

/-! ## 6. MachCSL's runs: liveness, generations, the power thread (`Era`)

MachCSL has no values: a thread never finishes, and what ends its attempts is the end of its era.
Every enabling condition of the instances is a live thread's, and is stable under the steps of
every thread but the power thread.  The power thread breaks stability only by a cut, which bumps
the generation and so falsifies the condition for ever.  That gives persistence, the hypothesis
of layer 3's completeness (`Thread.Persists`).  The section is MachCSL's own; Lantana takes nothing
from it. -/

namespace Era

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The thread at `i` is live: a hart or a device thread of a live generation. -/
def liveAt (i : Nat) (c : Cfg) : Prop := ∃ e,
  ((∃ x m, c.1[i]? = some (.hart e x m)) ∨ (∃ d tid m, c.1[i]? = some (.dev e d tid m))) ∧
  threadLive c.2 e

/-- Stability under the steps of every thread but the power thread. -/
def StableExceptPower (i : Nat) (A : Cfg → Prop) : Prop :=
  ∀ {j : Nat} {c c' : Cfg}, j ≠ i → Step j c c' → (∀ e, c.1[j]? = some e → e ≠ .power) →
    A c → A c'

/-- Stability under the steps of every thread but the power thread that meet the side condition
`P` on the configurations before and after the step.  The form a gate that another thread can
close takes: `P` excludes the closing transitions (`MachCSL/Liveness/Gates.lean`). -/
def StableExceptPowerUnder (i : Nat) (P : Cfg → Cfg → Prop) (A : Cfg → Prop) : Prop :=
  ∀ {j : Nat} {c c' : Cfg}, j ≠ i → Step j c c' → (∀ e, c.1[j]? = some e → e ≠ .power) →
    P c c' → A c → A c'

/-- Stability outright is stability under any side condition. -/
theorem stableExceptPowerUnder_of_stable {A : Cfg → Prop} (P : Cfg → Cfg → Prop)
    (hstab : StableExceptPower i A) : StableExceptPowerUnder i P A :=
  fun hji hs hnp _ hA => hstab hji hs hnp hA

/-- A step of a thread that is not the power thread keeps the generation and the power bit. -/
theorem genPow_of_step (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) :
    c'.2.gen = c.2.gen ∧ c'.2.pow = c.2.pow := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ <;> exact ⟨rfl, rfl⟩
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> exact ⟨rfl, rfl⟩
  | power => exact absurd rfl (hnp _ he)

/-- A step of a thread that is not the power thread keeps every generation's liveness. -/
theorem threadLive_of_step (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power)
    (gen : Nat) : threadLive c'.2 gen ↔ threadLive c.2 gen := by
  obtain ⟨hg, hp⟩ := genPow_of_step hs hnp
  unfold threadLive
  rw [hg, hp]

/-- The generation never goes down. -/
theorem gen_mono (hs : Step j c c') : c.2.gen ≤ c'.2.gen := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ <;> exact Nat.le_refl _
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> exact Nat.le_refl _
  | power =>
    rcases hp with ⟨-, ⟨-, -, -, rfl⟩ | ⟨-, -, -, hb⟩⟩
    · exact Nat.le_succ _
    · exact Nat.le_of_eq hb.1.symm

/-- The generation an expression carries. -/
def Expr.gen? : Expr → Option Nat
  | .hart e _ _ => some e
  | .dev e _ _ _ => some e
  | .power => none

/-- The generation of the thread at `i`. -/
def genAt (i : Nat) (c : Cfg) : Option Nat := (c.1[i]?).bind Expr.gen?

/-- A step keeps the generation recorded at every position of the pool. -/
theorem genAt_step {e : Nat} (hs : Step j c c') (hg : genAt i c = some e) :
    genAt i c' = some e := by
  unfold genAt at hg ⊢
  cases hc : c.1[i]? with
  | none => simp [hc] at hg
  | some ex =>
    rw [hc] at hg
    by_cases hji : j = i
    · subst hji
      obtain ⟨ex0, obs, e', efs, he0, hp, hc'⟩ := hs
      rw [hc] at he0
      obtain rfl := Option.some.inj he0
      have hi : j < c.1.length := (List.getElem?_eq_some_iff.1 hc).1
      have hc'j : c'.1[j]? = some e' := by
        rw [hc', List.getElem?_append_left (by simpa using hi), List.getElem?_set_self hi]
      rw [hc'j]
      cases ex with
      | hart gen cpu m =>
        rcases hp with ⟨-, ⟨-, -, m', σ', rfl, -, -⟩ | ⟨-, -, rfl, -⟩⟩ <;> exact hg
      | dev gen d tid m =>
        rcases hp with ⟨-, m', σ', rfl, -, -⟩ | ⟨-, -, -, rfl, -⟩ <;> exact hg
      | power => simp [Expr.gen?] at hg
    · rw [step_get?_ne hs hji hc]
      exact hg

/-- The generation never goes down along a run of the pool. -/
theorem gen_mono_run (hrun : PoolRun σ) {n m : Nat} (hnm : n ≤ m) :
    (σ n).2.gen ≤ (σ m).2.gen := by
  induction m with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnm
    subst h0
    exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with hlt | heq
    · obtain ⟨j, hs⟩ := hrun m
      exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (gen_mono hs)
    · subst heq
      exact Nat.le_refl _

/-- The generation recorded at a position of the pool stays along a run of the pool. -/
theorem genAt_run (hrun : PoolRun σ) {e n m : Nat} (hnm : n ≤ m) (hg : genAt i (σ n) = some e) :
    genAt i (σ m) = some e := by
  induction m with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnm
    subst h0
    exact hg
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with hlt | heq
    · obtain ⟨j, hs⟩ := hrun m
      exact genAt_step hs (ih (Nat.le_of_lt_succ hlt))
    · subst heq
      exact hg

/-- A live thread carries the current generation, and the power is on. -/
theorem liveAt_gen (h : liveAt i c) : ∃ e, genAt i c = some e ∧ c.2.pow = true ∧ c.2.gen = e := by
  obtain ⟨e, hx | hd, hl⟩ := h
  · obtain ⟨x, m, hx⟩ := hx
    exact ⟨e, by simp [genAt, hx, Expr.gen?], hl.1, hl.2⟩
  · obtain ⟨d, tid, m, hd⟩ := hd
    exact ⟨e, by simp [genAt, hd, Expr.gen?], hl.1, hl.2⟩

/-- A power step while the thread at `i` is live is a cut: it bumps the generation. -/
theorem power_kills (hs : Step j c c') (hpj : c.1[j]? = some .power) (hl : liveAt i c) :
    c'.2.gen = c.2.gen + 1 := by
  obtain ⟨_, -, hpow, -⟩ := liveAt_gen hl
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨ex, obs, e', efs, he, hp, -⟩ := hs
  rw [hpj] at he
  obtain rfl := Option.some.inj he
  rcases hp with ⟨-, ⟨-, -, -, rfl⟩ | ⟨hoff, -, -, -⟩⟩
  · rfl
  · exact absurd hpow (by simpa using hoff)

/-- Persistence on a run of the pool, for an enabling condition that is a live thread's and is
stable under every step but the power thread's that meets the side condition `P`, on a run where
every step meets `P`. -/
theorem persists_of_liveStableUnder (hrun : PoolRun σ) {A : Cfg → Prop} {P : Cfg → Cfg → Prop}
    (hlive : ∀ c, A c → liveAt i c) (hstab : StableExceptPowerUnder i P A)
    (hP : ∀ n, P (σ n) (σ (n + 1))) : Thread.Persists i A σ := by
  intro n hA
  obtain ⟨j, hs⟩ := hrun n
  by_cases hji : j = i
  · subst hji
    exact Or.inl hs
  · by_cases hpw : (σ n).1[j]? = some .power
    · refine Or.inr (Or.inr fun m hnm hAm => ?_)
      obtain ⟨e, hg, -, hgen⟩ := liveAt_gen (hlive _ hA)
      obtain ⟨e', hg', -, hgen'⟩ := liveAt_gen (hlive _ hAm)
      have hge : genAt i (σ m) = some e := genAt_run hrun (Nat.le_of_lt hnm) hg
      rw [hg'] at hge
      obtain rfl := Option.some.inj hge
      have h1 := power_kills hs hpw (hlive _ hA)
      have h2 := gen_mono_run hrun (n := n + 1) (m := m) hnm
      omega
    · refine Or.inr (Or.inl (hstab hji hs ?_ (hP n) hA))
      intro e he hep
      exact hpw (hep ▸ he)

/-- Persistence on a run of the pool, for an enabling condition that is a live thread's and is
stable under every thread but the power thread. -/
theorem persists_of_liveStable (hrun : PoolRun σ) {A : Cfg → Prop}
    (hlive : ∀ c, A c → liveAt i c) (hstab : StableExceptPower i A) : Thread.Persists i A σ :=
  persists_of_liveStableUnder hrun hlive (stableExceptPowerUnder_of_stable (fun _ _ => True) hstab)
    fun _ => trivial

end Era

/-! ## 7. The instances

Each instance gives its enabling condition `enabled` (the `A`) and its grant relation `grant` (the
`G`), its trusted form `SF` (layer 1) and its proof form `AG` (layer 3).  Every `grant` begins
with the thread's step, `Step i c c'`, and then states the thread's transition, so every instance
has own grant and takes the cheap path of layer 3.  The first four instances prove: `ownGrant`,
the grant is one of the thread's transitions; `live`, the condition is a live thread's; `stable`,
it survives every thread's step but the power thread's; `persists`, from the two; `sf_iff`, the
two forms coincide under fair scheduling; `counter_of_sf`, the trusted form gives the thread's
counter.  The two device tasks (7.5, 7.6) prove what their persistence allows. -/

open Era (liveAt StableExceptPower)

/-! ### 7.1 The tick: a live hart at its cycle boundary; the restart carries the tick -/

namespace Tick

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The enabling condition: the thread at `i` is a live hart at its cycle boundary. -/
def enabled (i : Nat) (c : Cfg) : Prop :=
  ∃ e x, c.1[i]? = some (.hart e x (.pure ())) ∧ threadLive c.2 e

/-- The grant: the hart steps from its cycle boundary and restarts its cycle with a tick. -/
def grant (i : Nat) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e x ew, c.1[i]? = some (.hart e x (.pure ())) ∧
    c'.1[i]? = some (.hart e x (riscvStep true ew))

/-- The grant is one of the hart's transitions. -/
theorem ownGrant : Thread.OwnGrant i (grant i) := fun h => h.1

/-- Trusted: a hart at its boundary infinitely often restarts with the tick infinitely often. -/
abbrev SF (i : Nat) (σ : Nat → Cfg) : Prop := Action.SF (enabled i) (grant i) σ

/-- Proof form: infinitely many tickless restarts force infinitely many ticking ones. -/
abbrev AG (i : Nat) (σ : Nat → Cfg) : Prop := Thread.AttemptGrant i (enabled i) (grant i) σ

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i c) : liveAt i c :=
  let ⟨e, x, he, hl⟩ := h; ⟨e, Or.inl ⟨x, _, he⟩, hl⟩

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i) := by
  intro j c c' hji hs hnp h
  obtain ⟨e, x, he, hl⟩ := h
  exact ⟨e, x, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl⟩

/-- The enabling condition persists on every run of the pool. -/
theorem persists (hrun : PoolRun σ) : Thread.Persists i (enabled i) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) stable

/-- Under fair scheduling of the hart, the trusted form and the proof form coincide. -/
theorem sf_iff (hrun : PoolRun σ) (hsched : StepsInfOften i σ) : SF i σ ↔ AG i σ :=
  Thread.sf_iff_attemptGrant ownGrant hsched (persists hrun)

/-- The trusted form gives the hart's counter. -/
theorem counter_of_sf (hsf : SF i σ) : ∃ δ, Thread.IsCounter i (enabled i) (grant i) σ δ :=
  Thread.counter_of_sf ownGrant hsf

end Tick

/-! ### 7.2 A device's `choose` arm: the live root at the node; class `b` chosen -/

namespace Arm

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The continuation of a `choose` node at the answer `v`. -/
def at? {S T α : Type} : DevM S T α → Nat → Option (DevM S T α)
  | .op .choose k, v => some (k v)
  | _, _ => none

/-- The enabling condition: the thread at `i` is the live root of device `d` at the node. -/
def enabled (i : Nat) (d : DevId) (node : DevProg d) (c : Cfg) : Prop :=
  ∃ e, c.1[i]? = some (.dev e d rootTask node) ∧ threadLive c.2 e

/-- The grant: the root steps from the node and takes an answer of class `b` modulo `m`. -/
def grant (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e v, v % m = b ∧ c.1[i]? = some (.dev e d rootTask node) ∧
    c'.1[i]? = (at? node v).map (.dev e d rootTask)

/-- The grant is one of the root's transitions. -/
theorem ownGrant {d : DevId} {node : DevProg d} {m b : Nat} :
    Thread.OwnGrant i (grant i d node m b) := fun h => h.1

/-- Trusted: a root at the node infinitely often takes class `b` infinitely often. -/
abbrev SF (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d node) (grant i d node m b) σ

/-- Proof form: infinitely many steps of the root at the node that take another class force
infinitely many that take class `b`. -/
abbrev AG (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d node) (grant i d node m b) σ

variable {d : DevId} {node : DevProg d} {m b : Nat}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d node c) : liveAt i c :=
  let ⟨e, he, hl⟩ := h; ⟨e, Or.inr ⟨d, _, _, he⟩, hl⟩

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i d node) := by
  intro j c c' hji hs hnp h
  obtain ⟨e, he, hl⟩ := h
  exact ⟨e, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl⟩

/-- The enabling condition persists on every run of the pool. -/
theorem persists (hrun : PoolRun σ) : Thread.Persists i (enabled i d node) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) stable

/-- Under fair scheduling of the root, the trusted form and the proof form coincide. -/
theorem sf_iff (hrun : PoolRun σ) (hsched : StepsInfOften i σ) :
    SF i d node m b σ ↔ AG i d node m b σ :=
  Thread.sf_iff_attemptGrant ownGrant hsched (persists hrun)

/-- The trusted form gives the root's counter. -/
theorem counter_of_sf (hsf : SF i d node m b σ) :
    ∃ δ, Thread.IsCounter i (enabled i d node) (grant i d node m b) σ δ :=
  Thread.counter_of_sf ownGrant hsf

end Arm

/-! ### 7.3 The visibility of a store: a live hart at a plain load of `a` once store `t` exists;
the load sees `t` -/

namespace Fresh

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The thread at `i` is a live hart whose head event is a plain RAM load covering `a`. -/
def atLoad (i : Nat) (a : PAddr) (c : Cfg) : Prop := ∃ e x req k,
  c.1[i]? = some (.hart e x (.impure (.inl (.ok (.memRead req))) k)) ∧ threadLive c.2 e ∧
  akPlain req.accessKind = true ∧ ramBytes req.pa req.size ∧
  ∃ j, j < req.size ∧ a = req.pa + BitVec.ofNat 64 j

/-- The enabling condition: the load covers `a` and the store `t` has happened. -/
def enabled (i : Nat) (t : Nat) (a : PAddr) (c : Cfg) : Prop := atLoad i a c ∧ t ≤ c.2.m.top

/-- The grant: the hart takes the load and moves on to its continuation, and afterwards its view of
`a` is at or past `t`.  That view is the hart's coherence floor of `a`: its later loads of `a` read
at that view or a later one. -/
def grant (i t : Nat) (a : PAddr) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e x req k v, c.1[i]? = some (.hart e x (.impure (.inl (.ok (.memRead req))) k)) ∧
    c'.1[i]? = some (.hart e x (k v)) ∧ t ≤ (c'.2.m.hr x).coh a

/-- The grant is one of the hart's transitions. -/
theorem ownGrant {t : Nat} {a : PAddr} : Thread.OwnGrant i (grant i t a) := fun h => h.1

/-- Trusted: a hart at a load of `a` after store `t` infinitely often sees `t` infinitely
often (memory fairness). -/
abbrev SF (i t : Nat) (a : PAddr) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i t a) (grant i t a) σ

/-- Proof form: infinitely many loads of `a` after store `t` that do not see it force infinitely
many that do. -/
abbrev AG (i t : Nat) (a : PAddr) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i t a) (grant i t a) σ

variable {t : Nat} {a : PAddr}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i t a c) : liveAt i c :=
  let ⟨⟨e, x, _req, _k, he, hl, _⟩, _⟩ := h; ⟨e, Or.inl ⟨x, _, he⟩, hl⟩

/-! #### The top of the store order never goes down, except at a power-on -/

/-- Dropping a hart's store window keeps the store log. -/
theorem dropWindow_log (σ : MState) (cpu : CPU) : (σ.dropWindow cpu).log = σ.log := by
  unfold MState.dropWindow
  split
  · split <;> rfl
  · rfl

/-- An answered event of a hart keeps or raises the top of the store order. -/
theorem evStep_top {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    {v : InstructionEffect.ret o} (h : evStep cpu o σ v σ') : σ.top ≤ σ'.top := by
  cases o with
  | memRead req =>
    rcases h with ⟨-, w, ds', -, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
      ⟨-, -, tvn, w, -, -, -, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩
    all_goals exact Nat.le_refl _
  | memWrite req w a =>
    rcases h with ⟨-, ds', -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact Nat.le_refl _
    · simp [MState.top]
  | _ =>
    first
    | (obtain rfl := h; exact Nat.le_refl _)
    | (obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _)

/-- A blocked retry of a hart keeps the top of the store order. -/
theorem blockedStep_top {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    (h : blockedStep cpu o σ σ') : σ.top ≤ σ'.top := by
  cases o with
  | memRead req =>
    obtain ⟨-, -, rfl⟩ := h
    exact Nat.le_refl _
  | memWrite req w a =>
    obtain ⟨-, rfl⟩ := h
    split
    · exact Nat.le_refl _
    · simp only [MState.top, dropWindow_log]
      exact Nat.le_refl _
  | _ => exact h.elim

/-- A hart's step keeps or raises the top of the store order. -/
theorem hartStep_top {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') : σ.top ≤ σ'.top := by
  unfold hartStep at h
  split at h
  · obtain ⟨-, -, -, rfl⟩ := h
    simp only [MState.top, dropWindow_log]
    exact Nat.le_refl _
  · exact h.elim
  · rcases h with ⟨v, -, hev⟩ | ⟨hb, -⟩
    · exact evStep_top hev
    · exact blockedStep_top hb
  · obtain ⟨-, -, rfl⟩ := h
    exact Nat.le_refl _

/-- An answered device primitive keeps or raises the top of the store order. -/
theorem devOpStep_top {gen : Nat} {d : DevId} {o : DevOp (DevSt d) (DevTask d)} {σ σ' : MState}
    {v : o.ret} {obs : List Obs} {efs : List Expr} (h : devOpStep gen d o σ v σ' obs efs) :
    σ.top ≤ σ'.top := by
  cases o with
  | step g =>
    obtain ⟨s', os, -, -, rfl, -, -⟩ := h
    exact Nat.le_refl _
  | get =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Nat.le_refl _
  | choose =>
    obtain ⟨rfl, -, -⟩ := h
    exact Nat.le_refl _
  | dmaRead pa n =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Nat.le_refl _
  | dmaWrite g pa n w =>
    obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · simp [MState.top]
    · exact Nat.le_refl _
  | sample src =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Nat.le_refl _
  | setPin cpu mmode b =>
    obtain ⟨-, -, rfl⟩ := h
    cases mmode <;> exact Nat.le_refl _
  | fork t =>
    obtain ⟨-, -, rfl, -⟩ := h
    exact Nat.le_refl _
  | join tid =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Nat.le_refl _

/-- A device task's step keeps or raises the top of the store order. -/
theorem devStep_top {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) :
    σ.top ≤ σ'.top := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  · rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · exact devOpStep_top hop
    · exact Nat.le_refl _

/-- Every step of a thread that is not the power thread keeps or raises the top of the store
order (a power-on resets the memory, hence the exclusion). -/
theorem top_mono (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) :
    c.2.m.top ≤ c'.2.m.top := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · exact hartStep_top hst
    · exact Nat.le_refl _
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact devStep_top hst
    · exact Nat.le_refl _
  | power => exact absurd rfl (hnp _ he)

/-! #### The coherence floors never go down, except at a power-on

The floors of the hart that steps move at its loads only: a plain load reads at a view at or
above the footprint's floors (`HRead.cohOk`), an exclusive read at the top of the order, which
is at or above every floor while the step invariant holds (`HRead.bound`, part of `mmOk`).  Every
other step keeps every hart's read side, or only clears its acquire bit. -/

/-- Every coherence floor of every hart in `σ` is at or below the same floor in `σ'`. -/
def cohLe (σ σ' : MState) : Prop := ∀ x a, (σ.hr x).coh a ≤ (σ'.hr x).coh a

/-- Every coherence floor is at or below itself. -/
theorem cohLe_refl (σ : MState) : cohLe σ σ := fun _ _ => Nat.le_refl _

/-- Dropping a hart's store window keeps every hart's read side. -/
theorem dropWindow_hr (σ : MState) (cpu : CPU) : (σ.dropWindow cpu).hr = σ.hr := by
  unfold MState.dropWindow
  split
  · split <;> rfl
  · rfl

/-- A step that keeps every hart's read side keeps every coherence floor. -/
theorem cohLe_of_hr {σ σ' : MState} (h : σ'.hr = σ.hr) : cohLe σ σ' := fun x a => by
  rw [h]
  exact Nat.le_refl _

/-- A step that replaces one hart's read side by one whose floors are at or above the old ones. -/
theorem cohLe_updCpu {σ σ' : MState} {cpu : CPU} {hr' : HRead}
    (hσ : σ'.hr = updCpu σ.hr cpu hr') (h : ∀ a, (σ.hr cpu).coh a ≤ hr'.coh a) : cohLe σ σ' := by
  intro x a
  rw [hσ]
  simp only [updCpu]
  split
  · rename_i hx
    subst hx
    exact h a
  · exact Nat.le_refl _

/-- An answered event of a hart keeps or raises every coherence floor, provided every floor is at
or below the top of the order before the step. -/
theorem evStep_coh {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    {v : InstructionEffect.ret o} (h : evStep cpu o σ v σ') (hb : ∀ x, (σ.hr x).bound σ.top) :
    cohLe σ σ' := by
  cases o with
  | memRead req =>
    rcases h with ⟨-, w, ds', -, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
      ⟨-, -, tvn, w, -, -, hcoh, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩
    · exact cohLe_refl _
    · exact cohLe_refl _
    · refine cohLe_updCpu rfl fun a => ?_
      simp only [HRead.afterLoad]
      split
      · rename_i ha
        obtain ⟨j, hj, rfl⟩ := ha
        exact hcoh j hj
      · exact Nat.le_refl _
    · refine cohLe_updCpu rfl fun a => ?_
      simp only [HRead.afterExcl]
      split
      · exact (hb cpu).2 a
      · exact Nat.le_refl _
  | memWrite req w a =>
    rcases h with ⟨-, ds', -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact cohLe_refl _
    · exact cohLe_updCpu rfl fun _ => Nat.le_refl _
  | _ =>
    first
    | (obtain rfl := h; exact cohLe_refl _)
    | (obtain ⟨-, rfl⟩ := h; exact cohLe_refl _)

/-- A blocked retry of a hart keeps every coherence floor. -/
theorem blockedStep_coh {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    (h : blockedStep cpu o σ σ') : cohLe σ σ' := by
  cases o with
  | memRead req =>
    obtain ⟨-, -, rfl⟩ := h
    exact cohLe_refl _
  | memWrite req w a =>
    obtain ⟨-, rfl⟩ := h
    split
    · exact cohLe_refl _
    · exact cohLe_of_hr (dropWindow_hr _ _)
  | _ => exact h.elim

/-- A hart's step keeps or raises every coherence floor, provided every floor is at or below the
top of the order before the step. -/
theorem hartStep_coh {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') (hb : ∀ x, (σ.hr x).bound σ.top) : cohLe σ σ' := by
  unfold hartStep at h
  split at h
  · obtain ⟨-, -, -, rfl⟩ := h
    exact cohLe_of_hr (dropWindow_hr _ _)
  · exact h.elim
  · rcases h with ⟨v, -, hev⟩ | ⟨hbl, -⟩
    · exact evStep_coh hev hb
    · exact blockedStep_coh hbl
  · obtain ⟨-, -, rfl⟩ := h
    exact cohLe_refl _

/-- An answered device primitive keeps every coherence floor. -/
theorem devOpStep_coh {gen : Nat} {d : DevId} {o : DevOp (DevSt d) (DevTask d)} {σ σ' : MState}
    {v : o.ret} {obs : List Obs} {efs : List Expr} (h : devOpStep gen d o σ v σ' obs efs) :
    cohLe σ σ' := by
  cases o with
  | step g =>
    obtain ⟨s', os, -, -, rfl, -, -⟩ := h
    exact cohLe_refl _
  | get =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact cohLe_refl _
  | choose =>
    obtain ⟨rfl, -, -⟩ := h
    exact cohLe_refl _
  | dmaRead pa n =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact cohLe_refl _
  | dmaWrite g pa n w =>
    obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · exact cohLe_refl _
    · exact cohLe_refl _
  | sample src =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact cohLe_refl _
  | setPin cpu mmode b =>
    obtain ⟨-, -, rfl⟩ := h
    cases mmode <;> exact cohLe_refl _
  | fork t =>
    obtain ⟨-, -, rfl, -⟩ := h
    exact cohLe_refl _
  | join tid =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact cohLe_refl _

/-- A device task's step keeps every coherence floor. -/
theorem devStep_coh {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) :
    cohLe σ σ' := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact cohLe_refl _
    · split <;> exact cohLe_refl _
  · rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · exact devOpStep_coh hop
    · exact cohLe_refl _

/-- Every step of a thread that is not the power thread keeps or raises the coherence floor of
every byte of every hart, provided every floor is at or below the top of the order before the
step: the step invariant's `HRead.bound` (from `h : mmOk c.2.m`, it is `fun x => (h.2.1 x).2.2`).
A power-on resets every read side, hence the exclusion. -/
theorem coh_mono (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power)
    (hb : ∀ x, (c.2.m.hr x).bound c.2.m.top) : cohLe c.2.m c'.2.m := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · exact hartStep_coh hst hb
    · exact cohLe_refl _
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact devStep_coh hst
    · exact cohLe_refl _
  | power => exact absurd rfl (hnp _ he)

/-- A live hart at a load of `a` stays there across every other thread's step but the power
thread's. -/
theorem atLoad_stable (h : atLoad i a c) (hs : Step j c c') (hji : j ≠ i)
    (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) : atLoad i a c' := by
  obtain ⟨e, x, req, k, he, hl, hrest⟩ := h
  exact ⟨e, x, req, k, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl, hrest⟩

/-- The enabling condition survives every other thread's step but the power thread's: the load
stays, and the top of the store order does not go down. -/
theorem stable : StableExceptPower i (enabled i t a) :=
  fun hji hs hnp h => ⟨atLoad_stable h.1 hs hji hnp, Nat.le_trans h.2 (top_mono hs hnp)⟩

/-- The enabling condition persists on every run of the pool. -/
theorem persists (hrun : PoolRun σ) : Thread.Persists i (enabled i t a) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) stable

/-- Under fair scheduling of the hart, the trusted form and the proof form coincide. -/
theorem sf_iff (hrun : PoolRun σ) (hsched : StepsInfOften i σ) : SF i t a σ ↔ AG i t a σ :=
  Thread.sf_iff_attemptGrant ownGrant hsched (persists hrun)

/-- The trusted form gives the hart's counter. -/
theorem counter_of_sf (hsf : SF i t a σ) :
    ∃ δ, Thread.IsCounter i (enabled i t a) (grant i t a) σ δ :=
  Thread.counter_of_sf ownGrant hsf

end Fresh

/-! ### 7.4 Harts progress: a live hart at a pending RAM access; the access is served -/

namespace Hart

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The enabling condition: a live hart whose head event is a RAM store or an exclusive RAM read,
blocked or not (a pending access). -/
def enabled (i : Nat) (c : Cfg) : Prop := ∃ e x o k,
  c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)) ∧ threadLive c.2 e ∧
  match o with
  | .memRead req => akExcl req.accessKind = true ∧ ramBytes req.pa req.size
  | .memWrite req _ _ => ramBytes req.pa req.size
  | _ => False

/-- The pending access is blocked: its footprint is covered by another hart's blocking
reservation (`othersReserve`; an LR's reservation blocks nobody since lane `lr-nonblock`,
2026-11-04). -/
def blocked (i : Nat) (c : Cfg) : Prop := ∃ e x o k,
  c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)) ∧ threadLive c.2 e ∧
  match o with
  | .memRead req => akExcl req.accessKind = true ∧ ramBytes req.pa req.size ∧
      othersReserve c.2.m.resv x req.pa req.size
  | .memWrite req _ _ => ramBytes req.pa req.size ∧ othersReserve c.2.m.resv x req.pa req.size
  | _ => False

/-- The grant: the hart's step answers its head event, and the hart moves on to the continuation
with some answer.  At a pending access, that is the access served.  A blocked retry keeps the head
event in place, so it is not a grant. -/
def grant (i : Nat) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e x o k v, c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)) ∧
    c'.1[i]? = some (.hart e x (k v))

/-- The grant is one of the hart's transitions. -/
theorem ownGrant : Thread.OwnGrant i (grant i) := fun h => h.1

/-- Trusted: a hart with a pending access infinitely often has one served infinitely often
(RVWMO's Progress Axiom in the model's terms). -/
abbrev SF (i : Nat) (σ : Nat → Cfg) : Prop := Action.SF (enabled i) (grant i) σ

/-- Proof form: infinitely many blocked retries force infinitely many served accesses. -/
abbrev AG (i : Nat) (σ : Nat → Cfg) : Prop := Thread.AttemptGrant i (enabled i) (grant i) σ

/-- The Progress Axiom in response form: every pending access is eventually served. -/
abbrev ProgressAxiom (i : Nat) (σ : Nat → Cfg) : Prop := Action.Response (enabled i) (grant i) σ

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i c) : liveAt i c :=
  let ⟨e, x, _o, _k, he, hl, _⟩ := h; ⟨e, Or.inl ⟨x, _, he⟩, hl⟩

/-- A blocked access is pending. -/
theorem enabled_of_blocked (h : blocked i c) : enabled i c := by
  obtain ⟨e, x, o, k, he, hl, hm⟩ := h
  refine ⟨e, x, o, k, he, hl, ?_⟩
  cases o <;> first | exact hm | exact hm.1 | exact ⟨hm.1, hm.2.1⟩

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i) := by
  intro j c c' hji hs hnp h
  obtain ⟨e, x, o, k, he, hl, hrest⟩ := h
  exact ⟨e, x, o, k, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl, hrest⟩

/-- The enabling condition persists on every run of the pool. -/
theorem persists (hrun : PoolRun σ) : Thread.Persists i (enabled i) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) stable

/-- Under fair scheduling of the hart, the trusted form and the proof form coincide. -/
theorem sf_iff (hrun : PoolRun σ) (hsched : StepsInfOften i σ) : SF i σ ↔ AG i σ :=
  Thread.sf_iff_attemptGrant ownGrant hsched (persists hrun)

/-- The trusted form gives the hart's counter. -/
theorem counter_of_sf (hsf : SF i σ) : ∃ δ, Thread.IsCounter i (enabled i) (grant i) σ δ :=
  Thread.counter_of_sf ownGrant hsf

/-- The response form gives the proof form too. -/
theorem ag_of_progressAxiom (h : ProgressAxiom i σ) : AG i σ :=
  Thread.attemptGrant_of_response ownGrant h

end Hart

/-! ### 7.5 A device task at a gate: the grant is certain, no fairness assumption

A device task's head primitive is blocked (`devBlocked`) in three cases: a guard that does not
answer (or answers an unfaithful move), a join on an unfinished task, and a DMA write whose
footprint is under a blocking reservation (7.6, excluded here by `isDma`).  The first two are
*gates*.  What opens a gate is a change of shared state by another thread: the device state the
guard reads, or the joined task's end.  Once the gate is open, the task's step through it is
certain (`certain`, a grant certain at the thread's attempts in the sense of layer 3).  So the
action "a live task at an unblocked primitive; the primitive is answered" has no misses, its
counter is zero (`counter_zero`), and its weak fairness follows from fair scheduling (`wf`).  What
the task waits on is the opener's obligation.  Whether an open gate stays open until the task's
step (persistence) is a property of the protocol, the stable-gate lemma of the plan (`HANDOFF.md`
§6 task 5), proved gate by gate in `MachCSL/Liveness/Gates.lean`; with it the action's strong
fairness follows too (`sf_of_persists`). -/

namespace Dev

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- A DMA write, the one primitive a hart's reservation can block; handled by `Dma` (7.6). -/
def isDma {S T : Type} : DevOp S T → Prop
  | .dmaWrite _ _ _ _ => True
  | _ => False

/-- The enabling condition: the thread at `i` is a live task of device `d` at a primitive other
than a DMA write that is not blocked, that is, at an open gate (a guard that answers faithfully,
or a join on a finished task) or at a primitive that never blocks. -/
def enabled (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ e, ∃ (o : DevOp (DevSt d) (DevTask d)), ∃ k, c.1[i]? = some (.dev e d tid (.op o k)) ∧
    threadLive c.2 e ∧ ¬ isDma o ∧ ¬ devBlocked d o c.2.m

/-- The grant: the task steps, its primitive is answered, and the task continues with some
answer. -/
def grant (i : Nat) (d : DevId) (tid : TaskId) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e, ∃ (o : DevOp (DevSt d) (DevTask d)), ∃ k v,
    c.1[i]? = some (.dev e d tid (.op o k)) ∧ c'.1[i]? = some (.dev e d tid (k v))

/-- The grant is one of the task's transitions. -/
theorem ownGrant {d : DevId} {tid : TaskId} : Thread.OwnGrant i (grant i d tid) := fun h => h.1

/-- Strong fairness of a task at an unblocked primitive: answered infinitely often. -/
abbrev SF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d tid) (grant i d tid) σ

/-- Proof form: infinitely many unanswered steps at an unblocked primitive force infinitely many
answered ones.  It holds outright (`ag`). -/
abbrev AG (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d tid) (grant i d tid) σ

/-- Weak fairness of a task at an unblocked primitive.  Fair scheduling gives it (`wf`). -/
abbrev WF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.WF (enabled i d tid) (grant i d tid) σ

variable {d : DevId} {tid : TaskId}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d tid c) : liveAt i c :=
  let ⟨e, _, _, he, hl, _, _⟩ := h; ⟨e, Or.inr ⟨d, tid, _, he⟩, hl⟩

/-- A live task at an unblocked primitive is answered when it steps: the grant is certain at the
task's attempts. -/
theorem certain : Thread.Certain i (enabled i d tid) (grant i d tid) σ := by
  intro n ⟨hs, e, o, k, he, hl, _, hnb⟩
  refine ⟨hs, ?_⟩
  obtain ⟨ex, obs, e', efs, he', hp, hc'⟩ := hs
  rw [he] at he'
  obtain rfl := Option.some.inj he'
  have hi : i < (σ n).1.length := (List.getElem?_eq_some_iff.1 he).1
  have hc'i : (σ (n + 1)).1[i]? = some e' := by
    rw [hc', List.getElem?_append_left (by simpa using hi), List.getElem?_set_self hi]
  rcases hp with ⟨-, m', σ', rfl, hd, -⟩ | ⟨hnl, -⟩
  · simp only [devStep] at hd
    rcases hd with ⟨v, rfl, -⟩ | ⟨hb, -⟩
    · exact ⟨e, o, k, v, he, hc'i⟩
    · exact absurd hb hnb
  · exact absurd hl hnl

/-- The proof form holds outright: the task's view has no misses. -/
theorem ag : AG i d tid σ := Thread.attemptGrant_of_certain certain

/-- The task's counter is identically zero. -/
theorem counter_zero : Thread.IsCounter i (enabled i d tid) (grant i d tid) σ (fun _ => 0) :=
  Thread.counter_zero_of_certain certain

/-- Weak fairness of a device task at a gate needs no assumption: fair scheduling gives it. -/
theorem wf (hsched : StepsInfOften i σ) : WF i d tid σ := Thread.wf_of_certain hsched certain

/-- With the stable-gate property (persistence), strong fairness follows as well. -/
theorem sf_of_persists (hsched : StepsInfOften i σ)
    (hper : Thread.Persists i (enabled i d tid) σ) : SF i d tid σ :=
  Thread.sf_of_certain hsched hper certain

end Dev

/-! ### 7.6 A device's DMA write under a reservation: memory arbitration, as for harts

The third way a device primitive blocks is a DMA write whose footprint is under a blocking
reservation.  That is memory arbitration, the same situation as a hart's blocked access, and it
fits the model the same way.  The attempt is a live task's step at a DMA write whose guard answers
a faithful move into RAM; the grant is the task's step that serves the write; the miss is a
blocked retry.  Its `SF` is the Progress Axiom for the DMA agent.  xv6 may not need the
assumption: if no reservation ever covers a DMA buffer, a safety fact, the miss never happens. -/

namespace Dma

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The enabling condition: a live task of `d` at a DMA write whose guard answers a faithful move
and whose footprint is RAM; blocked or not. -/
def enabled (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ e g pa n w k, c.1[i]? = some (.dev e d tid (.op (.dmaWrite g pa n w) k)) ∧
    threadLive c.2 e ∧
    (∃ s', g (c.2.m.devs.st d) = some s' ∧ devObsOk d (c.2.m.devs.st d) s' []) ∧ ramBytes pa n

/-- The DMA write is blocked: some hart holds a blocking reservation over its footprint. -/
def blocked (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ e g pa n w k, c.1[i]? = some (.dev e d tid (.op (.dmaWrite g pa n w) k)) ∧
    threadLive c.2 e ∧
    (∃ s', g (c.2.m.devs.st d) = some s' ∧ devObsOk d (c.2.m.devs.st d) s' []) ∧ ramBytes pa n ∧
    anyReserve c.2.m.resv pa n

/-- The grant: the task's step answers the DMA write, and the task moves on to the continuation
with some answer.  At a pending DMA write, that is the write served.  A blocked retry keeps the
write in place, so it is not a grant. -/
def grant (i : Nat) (d : DevId) (tid : TaskId) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e g pa n w k v, c.1[i]? = some (.dev e d tid (.op (.dmaWrite g pa n w) k)) ∧
    c'.1[i]? = some (.dev e d tid (k v))

/-- The grant is one of the task's transitions. -/
theorem ownGrant {d : DevId} {tid : TaskId} : Thread.OwnGrant i (grant i d tid) := fun h => h.1

/-- Trusted: a task with a pending DMA write infinitely often has one served infinitely often. -/
abbrev SF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d tid) (grant i d tid) σ

/-- Proof form: infinitely many blocked retries of a DMA write force infinitely many served
ones. -/
abbrev AG (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d tid) (grant i d tid) σ

variable {d : DevId} {tid : TaskId}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d tid c) : liveAt i c :=
  let ⟨e, _, _, _, _, _, he, hl, _⟩ := h; ⟨e, Or.inr ⟨d, tid, _, he⟩, hl⟩

/-- A blocked DMA write is pending. -/
theorem enabled_of_blocked (h : blocked i d tid c) : enabled i d tid c :=
  let ⟨e, g, pa, n, w, k, he, hl, hg, hr, _⟩ := h; ⟨e, g, pa, n, w, k, he, hl, hg, hr⟩

/-- The trusted form gives the task's counter. -/
theorem counter_of_sf (hsf : SF i d tid σ) :
    ∃ δ, Thread.IsCounter i (enabled i d tid) (grant i d tid) σ δ :=
  Thread.counter_of_sf ownGrant hsf

/-- The two forms coincide under fair scheduling and persistence.  Persistence of this condition
is a protocol property (the guard's device state is shared), so it is a hypothesis here. -/
theorem sf_iff (hsched : StepsInfOften i σ) (hper : Thread.Persists i (enabled i d tid) σ) :
    SF i d tid σ ↔ AG i d tid σ :=
  Thread.sf_iff_attemptGrant ownGrant hsched hper

end Dma

end Fairness

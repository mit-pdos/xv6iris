/-! # The attempt–grant model of fairness: the general theory

The general theory of the attempt–grant model, layers 0 to 2, generic over a thread pool.  A pool
(section 3) is a type of configurations with a step relation for the thread at each position, and
the theory takes nothing else from a language.  MachCSL's instance, with its eras and its six
actions, is `MachCSL/Liveness/Fairness.lean`; this file imports nothing of MachCSL.

The file is a stopgap until Lantana's fairness extension.  The extension's milestone M1 ports it
over Lantana's traces, and its milestone M7 deletes it.  It was split from `Fairness.lean` on
2026-11-06 (lane `fairness-split`), whose header carries the history of both files.  The same day
(lane `fairness-ag`) layer 0 became the attempt–grant pair.  The layer of a thread's pair, which
sat between the state form and the thread's view, was folded into it.

**The idea.**  Fairness is about two predicates on positions, the *attempts* and the *grants*.  A
hit is a granted attempt, and a miss is a refused one.  Attempt–grant fairness says that infinitely
many misses force infinitely many hits, or equivalently that infinitely many attempts force
infinitely many hits.  It is the existence of a counter, the budget of refusals before the next
grant: zero at a hit, one more at a miss than at the next position, unchanged where there is no
attempt.  That is layer 0, and the two layers above are instances of it.

A fairness assumption is an *action*: an *enabling condition* `A` on configurations and a *grant*
relation `G` on steps.  Its trusted form is the textbook strong fairness
`SF := □◇ A → □◇ (A ∧ G)`, a statement about the run that names no thread.  `SF` is layer 0 with
the positions where `A` holds as the attempts and the steps in `G` as the grants.  Its counter
moves at any step, whoever takes it.  Telling a thread about an update of the counter at another
thread's step is the program logic's job.

A thread's view of the action is layer 0 with the thread's own steps from a configuration where `A`
holds as the attempts.  The restriction is sound when every grant is one of the thread's
transitions (*own grant*).  It loses nothing when `A` persists and the thread is scheduled fairly.
The thread's counter stays at every other thread's step, because its attempts are the thread's
steps.  That makes the thread's view the cheap path for the logic.

**Map of the file.**

1. `AttemptGrant`, layer 0: the attempt–grant pair over two position predicates (`hit`, `miss`,
   `Fair`, `IsCounter`, `Certain`).  Its meaning (`fair_iff_attempt`), its counter
   (`fair_iff_counter`) and the counter's rules, stated once for every layer; restriction
   (`fair_mono`); a certain grant (`fair_of_certain`).  The engine underneath, `MissHit`, is
   copied from Lantana's ghost toy.  Pure arithmetic of positions.
2. `Action`, layer 1: the state form of an action `(A, G)`, with no thread and no pool.  Its
   `grant` is a position predicate, and its `hit`, `miss`, `IsCounter` and `Certain` are layer 0's
   at the positions where `A` holds.  `SF`, `Response` and `WF` are stated directly.  `SF` is
   layer 0's fairness (`sf_iff_fair`), hence the existence of a counter (`sf_iff_counter`).  A
   certain grant gives `SF` outright (`sf_of_certain`).
3. The pool, abstractly: a class of configurations with a thread's step (`Pool`, `Pool.Step`), and
   a thread's step on a run, a run, fair scheduling (`Steps`, `PoolRun`, `StepsInfOften`).  A pair
   of layer 0 is one thread's when its attempts are that thread's steps (`AttemptGrant.OwnStep`),
   and its counter then stays at the other threads' steps (`AttemptGrant.counter_stay_of_other`).
4. `Thread`, layer 2: the thread's view of an action, layer 0 at the thread's attempts (`attempt`,
   `hit`, `miss`, `AttemptGrant`, `IsCounter`, `Certain`), a pair that is the thread's by
   construction (`ownStep`), and own grant (`OwnGrant`).
   * Soundness: under own grant, `SF` gives the attempt–grant form (`attemptGrant_of_sf`, a
     restriction) and the counter (`counter_of_sf`).
   * Completeness: under persistence of `A` (`Persists`, from stability `Stable`) and fair
     scheduling, the attempt–grant form gives `SF` back (`sf_of_attemptGrant`), hence
     `sf_iff_attemptGrant`.
   * A grant certain at the thread's attempts (`Certain`): no misses, counter zero, `WF` from fair
     scheduling alone (`wf_of_certain`), `SF` with persistence as well (`sf_of_certain`).

Lantana takes one thing from each layer.  Its witness kind is stated against layer 0.  Its trace
side implements layer 1, one counter per declared action updated at every step (the owner's
decision of 2026-11-06).  Layer 2 is its cheap path, available when the declared action has own
grant, which all six actions of `Fairness.lean` have.

**Naming policy.**  Namespaces are the layers.  Capitalised names are propositions about a whole
run or a relation (`Fair`, `SF`, `Response`, `WF`, `Certain`, `AttemptGrant`, `IsCounter`,
`OwnStep`, `OwnGrant`, `Stable`, `Persists`); lower-case names are position or configuration
predicates (`attempt`, `grant`, `hit`, `miss`, `enabled`).  The layers above layer 0 state their
pair as abbreviations of layer 0's, so layer 0's theorems apply to them as they stand; the layers
copy none of the rules, and restate by the thread's name only the three facts the documents cite
(`Thread.attemptGrant_iff_attempt`, `attemptGrant_of_certain`, `counter_zero_of_certain`).
Theorems read `conclusion_of_hypothesis` (`attemptGrant_of_sf`, `counter_of_sf`,
`sf_of_attemptGrant`) or `subject_property` (`counter_reset`, `hit_miss_exclusive`), and
equivalences read `x_iff_y` (`sf_iff_fair`, `sf_iff_attemptGrant`).  A hypothesis has the same name
everywhere: `hsf` for `Action.SF`, `hag` for an attempt–grant form (layer 0's `Fair` or the
thread's `AttemptGrant`), `hown` for `OwnGrant`, `hos` for `OwnStep`, `hsched` for `StepsInfOften`, `hper` for
`Persists`, `hstab` for stability, `hrun` for `PoolRun`, `hδ` for a counter, `hc` for `Certain`,
and `ha`, `hg`, `hA`, `hs` for the facts at a position (an attempt, a grant, `A` holds, the thread
steps).  The names every action of `Fairness.lean` has are in that file's header.
-/

namespace Fairness

/-! ## 1. Layer 0: the attempt–grant pair over positions (`AttemptGrant`)

The attempt–grant model itself: two predicates on positions, the attempts and the grants, and
nothing else, no run and no thread.  A hit is a granted attempt and a miss a refused attempt, so
hits and misses are exclusive and a hit is an attempt by construction.  Attempt–grant fairness
(`Fair`) says that infinitely many misses force infinitely many hits.  Its meaning is that
infinitely many attempts force infinitely many hits (`fair_iff_attempt`).  It is the existence of a
counter (`fair_iff_counter`), the budget of refusals before the next grant.  The counter's three
rules (`counter_reset`, `counter_drop`, `counter_stay`) are stated here once, for every layer.
Fairness survives shrinking the attempts to a subset that keeps every granted one (`fair_mono`),
and a certain grant gives it outright (`fair_of_certain`).  Lantana's witness kind is stated
against this layer.

### The engine: miss–hit fairness over two position predicates (`MissHit`)

Two position predicates, the hits and the misses.  Miss–hit fairness says that infinitely many
misses force infinitely many hits.  With hits and misses exclusive, it is the existence of a
counter that is zero at a hit, goes down by one at a miss and is unchanged otherwise
(`MissHit.fair_iff_counter`).  Layer 0 is this engine applied to the hits and the misses of an
attempt–grant pair.

The first four subsections are copied (read-only) from Lantana's ghost toy, in the Lantana
repository: `Lantana/Trace/FairScheduling.lean` (`Nat.exists_min`, `Nat.minWitness`),
`LantanaTest/GhostToy/Count.lean` (`firstHit?`, `countMiss`, `missBound`, `horizon`, `budget`
and the lemmas `fair_iff_counter` uses) and `LantanaTest/GhostToy/MissHit.lean` (`InfOften`,
`MH` = `Fair`, `IsMHCounter` = `IsCounter`, `mhCounter_spec` = `counter_spec`, `mh_of_counter` =
`fair_of_counter`, `mh_iff_counter` = `fair_iff_counter`); only what `fair_iff_counter` needs,
with a docstring added to each lemma that has none there.  The last subsection, `infOften_mono`,
is this file's own. -/

namespace MissHit

/-! #### Least witnesses -/

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

/-! #### Miss–hit fairness and counters -/

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

/-! #### The oracle budget (`Count`) -/

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

/-! #### Miss–hit fairness is the existence of a counter: the two main theorems -/

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

/-! #### Holding infinitely often is monotone -/

/-- Holding infinitely often is monotone in the predicate. -/
theorem infOften_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) (hP : InfOften P) : InfOften Q :=
  fun n => let ⟨m, hm, hPm⟩ := hP n; ⟨m, hm, h m hPm⟩

end MissHit

namespace AttemptGrant

/-! ### Definitions -/

/-- A granted attempt. -/
def hit (attempt grant : Nat → Prop) (n : Nat) : Prop := attempt n ∧ grant n

/-- A refused attempt. -/
def miss (attempt grant : Nat → Prop) (n : Nat) : Prop := attempt n ∧ ¬ grant n

/-- Attempt–grant fairness: infinitely many refused attempts force infinitely many granted
ones. -/
def Fair (attempt grant : Nat → Prop) : Prop :=
  MissHit.Fair (hit attempt grant) (miss attempt grant)

/-- The counter: zero at a granted attempt, one more at a refused attempt than at the next
position, unchanged where there is no attempt. -/
def IsCounter (attempt grant : Nat → Prop) (δ : Nat → Nat) : Prop :=
  MissHit.IsCounter (hit attempt grant) (miss attempt grant) δ

/-- Every attempt is granted. -/
def Certain (attempt grant : Nat → Prop) : Prop := ∀ n, attempt n → grant n

variable {attempt grant : Nat → Prop} {δ : Nat → Nat} {n : Nat}

/-! ### Hits, misses and the meaning of fairness -/

/-- No position is both a granted and a refused attempt. -/
theorem hit_miss_exclusive : ¬ (hit attempt grant n ∧ miss attempt grant n) :=
  fun ⟨hh, hm⟩ => hm.2 hh.2

/-- The attempts are exactly the granted and the refused attempts. -/
theorem attempt_iff : attempt n ↔ hit attempt grant n ∨ miss attempt grant n :=
  ⟨fun ha => (Classical.em (grant n)).imp (And.intro ha) (And.intro ha),
    fun h => h.elim And.left And.left⟩

/-- The meaning: infinitely many attempts force infinitely many granted ones. -/
theorem fair_iff_attempt :
    Fair attempt grant ↔ (MissHit.InfOften attempt → MissHit.InfOften (hit attempt grant)) := by
  constructor
  · intro hag hinf
    apply Classical.byContradiction
    intro hno
    obtain ⟨N, hN⟩ := MissHit.eventually_not_of_not_infOften hno
    apply hno
    apply hag
    intro n
    obtain ⟨m, hm, ham⟩ := hinf (n + N)
    have hhm : ¬ hit attempt grant m := hN m (Nat.le_trans (Nat.le_add_left N n) hm)
    exact ⟨m, Nat.le_trans (Nat.le_add_right n N) hm, (attempt_iff.1 ham).resolve_left hhm⟩
  · intro h hinf
    exact h (MissHit.infOften_mono (fun _ hm => hm.1) hinf)

/-- A response property gives fairness: every attempt is followed by a granted attempt, at it or
later. -/
theorem fair_of_response (h : ∀ n, attempt n → ∃ m ≥ n, hit attempt grant m) :
    Fair attempt grant :=
  fun hmiss n =>
    let ⟨m, hm, hmiss_m⟩ := hmiss n
    let ⟨k, hk, hhit⟩ := h m hmiss_m.1
    ⟨k, Nat.le_trans hm hk, hhit⟩

/-! ### The counter and its rules

Attempt–grant fairness is the existence of a counter.  At a granted attempt the counter resets, at
a refused attempt it drops by one, and where there is no attempt it stays.  The three rules are
the counter's definition (`isCounter_iff`). -/

/-- Attempt–grant fairness is the existence of a counter. -/
theorem fair_iff_counter : Fair attempt grant ↔ ∃ δ, IsCounter attempt grant δ :=
  MissHit.fair_iff_counter fun _ => hit_miss_exclusive

/-- Attempt–grant fairness gives a counter. -/
theorem counter_of_fair (hag : Fair attempt grant) : ∃ δ, IsCounter attempt grant δ :=
  fair_iff_counter.1 hag

/-- A counter gives attempt–grant fairness. -/
theorem fair_of_counter (hδ : IsCounter attempt grant δ) : Fair attempt grant :=
  MissHit.fair_of_counter hδ

/-- Reset: the counter is zero at a granted attempt. -/
theorem counter_reset (hδ : IsCounter attempt grant δ) (ha : attempt n) (hg : grant n) :
    δ n = 0 :=
  hδ.1 n ⟨ha, hg⟩

/-- Drop: at a refused attempt the counter is one more than at the next position. -/
theorem counter_drop (hδ : IsCounter attempt grant δ) (ha : attempt n) (hg : ¬ grant n) :
    δ n = δ (n + 1) + 1 :=
  hδ.2.1 n ⟨ha, hg⟩

/-- Stay: where there is no attempt the counter is unchanged. -/
theorem counter_stay (hδ : IsCounter attempt grant δ) (ha : ¬ attempt n) : δ n = δ (n + 1) :=
  hδ.2.2 n (fun h => ha h.1) (fun h => ha h.1)

/-- The counter, by its three rules. -/
theorem isCounter_iff : IsCounter attempt grant δ ↔
    (∀ n, attempt n → grant n → δ n = 0) ∧ (∀ n, attempt n → ¬ grant n → δ n = δ (n + 1) + 1) ∧
    (∀ n, ¬ attempt n → δ n = δ (n + 1)) :=
  ⟨fun hδ => ⟨fun _ => counter_reset hδ, fun _ => counter_drop hδ, fun _ => counter_stay hδ⟩,
    fun ⟨hreset, hdrop, hstay⟩ => ⟨fun n h => hreset n h.1 h.2, fun n h => hdrop n h.1 h.2,
      fun n hh hm => hstay n fun ha => (attempt_iff.1 ha).elim hh hm⟩⟩

/-! ### What a counter bounds

A refused attempt has a positive counter, so an attempt made at counter zero is granted.  Until the
next granted attempt the counter dominates the refused attempts to come.  These are the facts the
layers above consume from a counter. -/

/-- A refused attempt has a positive counter. -/
theorem counter_pos_of_miss (hδ : IsCounter attempt grant δ) (h : miss attempt grant n) :
    0 < δ n := by
  have := counter_drop hδ h.1 h.2
  omega

/-- The base case of a waiter's induction: an attempt made at counter zero is granted. -/
theorem grant_of_attempt_of_counter_zero (hδ : IsCounter attempt grant δ) (ha : attempt n)
    (h0 : δ n = 0) : grant n :=
  Classical.byContradiction fun hg => Nat.ne_of_gt (counter_pos_of_miss hδ ⟨ha, hg⟩) h0

/-- The bound: with no granted attempt in `[n, n + k)`, the refused attempts in that window plus
the counter at its end are at most the counter at `n`. -/
theorem counter_bounds_misses (hδ : IsCounter attempt grant δ) (n : Nat) :
    ∀ k, (∀ m, n ≤ m → m < n + k → ¬ hit attempt grant m) →
      δ (n + k) + MissHit.countMiss (miss attempt grant) n k ≤ δ n := by
  intro k
  induction k generalizing n with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hno
    have ih' := ih (n + 1) (fun m hm1 hm2 => hno m (by omega) (by omega))
    have e : n + (k + 1) = n + 1 + k := by omega
    rw [e]
    rcases Classical.em (attempt n) with ha | ha
    · have hg : ¬ grant n := fun hg => hno n (Nat.le_refl n) (by omega) ⟨ha, hg⟩
      rw [MissHit.countMiss_succ_of_miss ⟨ha, hg⟩]
      have := counter_drop hδ ha hg
      omega
    · rw [MissHit.countMiss_succ_of_not_miss fun hm => ha hm.1]
      have := counter_stay hδ ha
      omega

/-! ### Restriction

Shrinking the attempts to a subset that still contains every granted attempt keeps the granted
attempts and can only remove refused ones.  So it keeps fairness (`fair_mono`).  The thread's
view of section 4 is such a subset of the action's attempts when every grant is the thread's
step. -/

/-- Fairness survives shrinking the attempts to a subset that still contains every granted
attempt. -/
theorem fair_mono {attempt' : Nat → Prop} (hatt : ∀ n, attempt' n → attempt n)
    (hgr : ∀ n, attempt n → grant n → attempt' n) (hag : Fair attempt grant) :
    Fair attempt' grant :=
  fun hinf => MissHit.infOften_mono (fun n hh => ⟨hgr n hh.1 hh.2, hh.2⟩)
    (hag (MissHit.infOften_mono (fun n hm => ⟨hatt n hm.1, hm.2⟩) hinf))

/-! ### A certain grant

When every attempt is granted there is no refused attempt.  Fairness then holds outright, and the
zero function is a counter. -/

/-- A certain grant gives fairness outright. -/
theorem fair_of_certain (hc : Certain attempt grant) : Fair attempt grant := by
  intro hmiss
  obtain ⟨m, -, ha, hg⟩ := hmiss 0
  exact absurd (hc m ha) hg

/-- With a certain grant the zero function is a counter: it resets at every granted attempt and
stays elsewhere, and never drops. -/
theorem counter_zero_of_certain (hc : Certain attempt grant) :
    IsCounter attempt grant (fun _ => 0) :=
  ⟨fun _ _ => rfl, fun n hm => absurd (hc n hm.1) hm.2, fun _ _ _ => rfl⟩

end AttemptGrant

/-! ## 2. Layer 1: the state form of an action (`Action`)

An action is an enabling condition `A` on configurations and a grant relation `G` on pairs of
configurations.  Its strong fairness `SF` says that where `A` holds infinitely often, a grant
happens infinitely often.  `SF` is the trusted form of every fairness assumption, and it names no
thread.  The layer uses configurations only, and no pool.

The action is layer 0 with the positions where `A` holds as the attempts (`enabled`) and the
steps in `G` as the grants (`grant`).  A hit is a position where `A` holds and the step taken is a
grant; a miss is a position where `A` holds and the step taken is not a grant, whoever takes it.
`SF` is layer 0's fairness of that pair (`sf_iff_fair`), so it is the existence of a counter
(`sf_iff_counter`).  The counter moves at any step, whoever takes it: it resets at a grant, drops
at a refused position and stays where `A` fails.

The layer's `hit`, `miss`, `IsCounter` and `Certain` are abbreviations of layer 0's, so layer 0's
theorems apply to them as they stand, and the layer copies none of them.  For example, from
`hδ : Action.IsCounter A G σ δ`, `hA : A (σ n)` and `hG : G (σ n) (σ (n + 1))`, the reset rule
`AttemptGrant.counter_reset hδ hA hG` gives `δ n = 0`.

Lantana's trace side implements exactly this layer: one counter per declared action, updated at
every step (the owner's decision of 2026-11-06).  How a thread learns of an update of the counter
at another thread's step is the program logic's business.  Layer 2 (section 4) avoids the question
for the actions whose grant is one of the thread's own transitions. -/

namespace Action

variable {Cfg : Type}

/-! ### Definitions -/

/-- The step at `n` is a grant: `G` relates the configuration at `n` to the next one, whoever takes
the step. -/
def grant (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := G (σ n) (σ (n + 1))

/-- The positions where `A` holds: the action's attempts. -/
abbrev enabled (A : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := A (σ n)

/-- Position `n` is granted: `A` holds there and the step taken is a grant, whoever takes it. -/
abbrev hit (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.hit (enabled A σ) (grant G σ) n

/-- Position `n` is refused: `A` holds there and the step taken is not a grant, whoever takes
it. -/
abbrev miss (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.miss (enabled A σ) (grant G σ) n

/-- The counter of the action: zero at a granted position, one more at a refused position than at
the next, unchanged where `A` fails. -/
abbrev IsCounter (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (δ : Nat → Nat) :
    Prop :=
  AttemptGrant.IsCounter (enabled A σ) (grant G σ) δ

/-- The grant is certain: every position where `A` holds is granted. -/
abbrev Certain (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Certain (enabled A σ) (grant G σ)

/-- Strong fairness of the action, the textbook statement: `A` holding infinitely often forces
infinitely many grants.  The trusted form of every fairness assumption; a statement about the
run, naming no thread. -/
def SF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  MissHit.InfOften (enabled A σ) → MissHit.InfOften (hit A G σ)

/-- The response form: every position where `A` holds is followed by a granted position, at it
or later. -/
def Response (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → ∃ m ≥ n, hit A G σ m

/-- Weak fairness of the action: `A` holding from some position on forces infinitely many
grants. -/
def WF (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  (∃ N, ∀ n, N ≤ n → A (σ n)) → MissHit.InfOften (hit A G σ)

variable {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat}

/-! ### `SF` is layer 0's fairness, and the existence of a counter -/

/-- `SF` is layer 0's fairness at the action's attempts: this is layer 0's meaning
(`AttemptGrant.fair_iff_attempt`). -/
theorem sf_iff_fair : SF A G σ ↔ AttemptGrant.Fair (enabled A σ) (grant G σ) :=
  AttemptGrant.fair_iff_attempt.symm

/-- `SF` is the existence of a counter. -/
theorem sf_iff_counter : SF A G σ ↔ ∃ δ, IsCounter A G σ δ :=
  sf_iff_fair.trans AttemptGrant.fair_iff_counter

/-- `SF` gives a counter. -/
theorem counter_of_sf (hsf : SF A G σ) : ∃ δ, IsCounter A G σ δ := sf_iff_counter.1 hsf

/-- A counter gives `SF`. -/
theorem sf_of_counter (hδ : IsCounter A G σ δ) : SF A G σ := sf_iff_counter.2 ⟨δ, hδ⟩

/-! ### The variants: response, weak fairness, a certain grant

The response form gives `SF`, and `SF` gives weak fairness `WF`.  A certain grant has no refused
position, so it gives the response form and `SF` outright, and its counter is zero
(`AttemptGrant.counter_zero_of_certain`). -/

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

end Action

/-! ## 3. The pool, and a pair that is one thread's

A pool is a type of configurations with a step relation for the thread at each position, and a
run is a sequence of configurations.  The class `Pool` is all that the general theory takes from
a language.  Sections 1 and 2 use no pool; this section and section 4 use a thread's step. -/

/-- A thread pool: configurations, and the step of the thread at a position.  All the general
theory takes from a language.  MachCSL's instance is in `Fairness.lean`; Lantana's will be its
traces. -/
class Pool (Cfg : Type) where
  /-- The thread at position `i` steps from `c` to `c'`. -/
  Step : Nat → Cfg → Cfg → Prop

section Run

variable {Cfg : Type} [Pool Cfg]

/-- The thread at position `i` steps at position `n` of the run `σ`. -/
def Steps (i : Nat) (σ : Nat → Cfg) (n : Nat) : Prop := Pool.Step i (σ n) (σ (n + 1))

/-- Every position of the run is a step of some thread. -/
def PoolRun (σ : Nat → Cfg) : Prop := ∀ n, ∃ j, Pool.Step j (σ n) (σ (n + 1))

/-- The thread at `i` steps infinitely often: what fair scheduling gives a live thread (and
what a corpse's self-loops give a dead one). -/
def StepsInfOften (i : Nat) (σ : Nat → Cfg) : Prop := ∀ n, ∃ m ≥ n, Steps i σ m

end Run

/-! ### A pair that is one thread's

A pair of layer 0 is the thread's at `i` when its attempts are steps of that thread
(`AttemptGrant.OwnStep`).  Then its counter never moves at another thread's step
(`AttemptGrant.counter_stay_of_other`), and the thread can consume it at its own steps alone.  The
thread's view of section 4 is such a pair for every action (`Thread.ownStep`).  The action's pair
of layer 1 need not be one, because the step at a position where `A` holds may be any thread's. -/

namespace AttemptGrant

variable {Cfg : Type} [Pool Cfg] {i : Nat} {σ : Nat → Cfg} {attempt grant : Nat → Prop}
  {δ : Nat → Nat} {n : Nat}

/-- The attempts are steps of the thread at `i`: the pair is the thread's. -/
def OwnStep (i : Nat) (σ : Nat → Cfg) (attempt : Nat → Prop) : Prop :=
  ∀ n, attempt n → Steps i σ n

/-- A thread's pair has a counter that never moves at another thread's step.  The one rule that
names a thread. -/
theorem counter_stay_of_other (hos : OwnStep i σ attempt) (hδ : IsCounter attempt grant δ)
    (hs : ¬ Steps i σ n) : δ n = δ (n + 1) :=
  counter_stay hδ fun ha => hs (hos n ha)

end AttemptGrant

/-! ## 4. Layer 2: the thread's view of an action (`Thread`)

The thread's view is layer 0 with the thread's own attempts.  An attempt is a step of the thread at
`i` from a configuration where `A` holds, and a grant is a step in `G`, as at layer 1.  A hit is
a granted attempt and a miss a refused one.  The view's attempts are the thread's steps for every
action (`ownStep`), so its counter moves only at the thread's own steps (`counter_stay_of_other`),
and the thread can consume it there with no help from the logic.  This is the cheap path, which
Lantana takes for a declared action with own grant.  Like layer 1, the layer states its pair as
abbreviations of layer 0's and copies none of its rules; it restates by the thread's name the three
facts the documents cite (`attemptGrant_iff_attempt`, `attemptGrant_of_certain`,
`counter_zero_of_certain`).

The view is sound under own grant (`OwnGrant`), which says that every grant is a step of the
thread.  Then the thread's attempts are the positions where `A` holds, cut down to the thread's
steps, and they keep every granted position.  That is layer 0's restriction (`fair_mono`), and
`SF` gives the attempt–grant form (`attemptGrant_of_sf`).  The view loses nothing under
persistence of `A` and fair scheduling of the thread (`sf_of_attemptGrant`), so the two forms
coincide (`sf_iff_attemptGrant`).  Without own grant a grant may happen at another thread's step.
The thread must then use the counter of layer 1, and the logic must tell it of the updates at the
other threads' steps.

The two layers' certain grants differ.  At layer 1 a certain grant covers every position where `A`
holds, whoever steps, and gives `SF` outright (`Action.sf_of_certain`).  At layer 2 it covers the
thread's own attempts only (`Certain`); it gives the attempt–grant form outright, and `SF` only
with persistence and fair scheduling (`sf_of_certain`).  A device task at a gate
(`Fairness.lean` 5.5) is the layer-2 case. -/

namespace Thread

variable {Cfg : Type} [Pool Cfg]

/-! ### Definitions -/

/-- The thread at `i` attempts at `n`: it steps there from a configuration where `A` holds. -/
abbrev attempt (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  Steps i σ n ∧ A (σ n)

/-- The thread's attempt at `n` is granted: the thread steps from a configuration where `A` holds,
and its step is a grant. -/
abbrev hit (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.hit (attempt i A σ) (Action.grant G σ) n

/-- The thread's attempt at `n` is refused. -/
abbrev miss (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop :=
  AttemptGrant.miss (attempt i A σ) (Action.grant G σ) n

/-- The attempt–grant form of the thread's view: infinitely many refused attempts force infinitely
many granted ones.  The form the logic consumes on the cheap path. -/
abbrev AttemptGrant (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Fair (attempt i A σ) (Action.grant G σ)

/-- The counter of the thread's view: zero at a granted attempt, one more at a refused attempt
than at the next position, unchanged where the thread does not attempt. -/
abbrev IsCounter (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg)
    (δ : Nat → Nat) : Prop :=
  AttemptGrant.IsCounter (attempt i A σ) (Action.grant G σ) δ

/-- The grant is certain at the thread's attempts: every attempt of the thread at `i` is
granted. -/
abbrev Certain (i : Nat) (A : Cfg → Prop) (G : Cfg → Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  AttemptGrant.Certain (attempt i A σ) (Action.grant G σ)

/-- Own grant: the grant is one of the thread's transitions.  The property that makes the thread's
view sound. -/
def OwnGrant (i : Nat) (G : Cfg → Cfg → Prop) : Prop :=
  ∀ {c c' : Cfg}, G c c' → Pool.Step i c c'

/-- `A` is stable under every other thread's step. -/
def Stable (i : Nat) (A : Cfg → Prop) : Prop :=
  ∀ {j : Nat} {c c' : Cfg}, j ≠ i → Pool.Step j c c' → A c → A c'

/-- `A` persists along the run: where it holds, the thread steps now, or `A` still holds at the
next position, or `A` never holds again.  The general interface: it says nothing about how `A`
can be lost. -/
def Persists (i : Nat) (A : Cfg → Prop) (σ : Nat → Cfg) : Prop :=
  ∀ n, A (σ n) → Steps i σ n ∨ A (σ (n + 1)) ∨ ∀ m, n < m → ¬ A (σ m)

variable {i : Nat} {A : Cfg → Prop} {G : Cfg → Cfg → Prop} {σ : Nat → Cfg} {δ : Nat → Nat}
  {n : Nat}

/-! ### The pair is the thread's, and the action's at the thread's steps -/

/-- The attempts are steps of the thread, for every action. -/
theorem ownStep : AttemptGrant.OwnStep i σ (attempt i A σ) := fun _ h => h.1

/-- A miss is a step of the thread from a configuration where `A` holds that is not a grant. -/
theorem miss_iff : miss i A G σ n ↔ Steps i σ n ∧ A (σ n) ∧ ¬ G (σ n) (σ (n + 1)) :=
  ⟨fun ⟨⟨hs, hA⟩, hg⟩ => ⟨hs, hA, hg⟩, fun ⟨hs, hA, hg⟩ => ⟨⟨hs, hA⟩, hg⟩⟩

/-- A hit of the thread is a step of the thread at a granted position of the action. -/
theorem hit_iff_steps_action_hit : hit i A G σ n ↔ Steps i σ n ∧ Action.hit A G σ n :=
  ⟨fun ⟨⟨hs, hA⟩, hg⟩ => ⟨hs, hA, hg⟩, fun ⟨hs, hA, hg⟩ => ⟨⟨hs, hA⟩, hg⟩⟩

/-- A miss of the thread is a step of the thread at a refused position of the action. -/
theorem miss_iff_steps_action_miss : miss i A G σ n ↔ Steps i σ n ∧ Action.miss A G σ n :=
  miss_iff

/-- The meaning of the attempt–grant form: a thread that attempts infinitely often is granted
infinitely often. -/
theorem attemptGrant_iff_attempt :
    AttemptGrant i A G σ ↔ (MissHit.InfOften (attempt i A σ) → MissHit.InfOften (hit i A G σ)) :=
  AttemptGrant.fair_iff_attempt

/-! ### Soundness: under own grant, `SF` gives the thread's counter -/

/-- **Soundness.**  Under own grant, `SF` gives the attempt–grant form.  It is layer 0's
restriction `AttemptGrant.fair_mono` applied to `Action.sf_iff_fair`: the thread's attempts are
among the positions where `A` holds, and under own grant they contain every granted one. -/
theorem attemptGrant_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    AttemptGrant i A G σ :=
  AttemptGrant.fair_mono (fun _ ha => ha.2) (fun _ hA hg => ⟨hown hg, hA⟩)
    (Action.sf_iff_fair.1 hsf)

/-- Under own grant, the response form gives the attempt–grant form. -/
theorem attemptGrant_of_response (hown : OwnGrant i G) (h : Action.Response A G σ) :
    AttemptGrant i A G σ :=
  attemptGrant_of_sf hown (Action.sf_of_response h)

/-- Under own grant, the trusted form gives the thread's counter. -/
theorem counter_of_sf (hown : OwnGrant i G) (hsf : Action.SF A G σ) :
    ∃ δ, IsCounter i A G σ δ :=
  AttemptGrant.counter_of_fair (attemptGrant_of_sf hown hsf)

/-- Stay: at every step that is not the thread's the counter is unchanged. -/
theorem counter_stay_of_other (hδ : IsCounter i A G σ δ) (hs : ¬ Steps i σ n) :
    δ n = δ (n + 1) :=
  AttemptGrant.counter_stay_of_other ownStep hδ hs

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
    (hothers : ∀ k', n ≤ k' → k' < k → ∃ j, j ≠ i ∧ Pool.Step j (σ k') (σ (k' + 1))) :
    A (σ k) := by
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
  refine MissHit.infOften_mono (fun _ hh => ⟨hh.1.2, hh.2⟩) (hag fun n₀ => ?_)
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
  intro hg
  exact hN m' (Nat.le_trans (Nat.le_add_left N n₀) (Nat.le_trans hn hnm')) ⟨hAm, hg⟩

/-- Under own grant, persistence and fair scheduling, the trusted form and the attempt–grant form
coincide. -/
theorem sf_iff_attemptGrant (hown : OwnGrant i G) (hsched : StepsInfOften i σ)
    (hper : Persists i A σ) : Action.SF A G σ ↔ AttemptGrant i A G σ :=
  ⟨attemptGrant_of_sf hown, sf_of_attemptGrant hsched hper⟩

/-! ### A grant certain at the thread's own attempts

When every attempt of the thread is granted, the thread's view has no misses.  Its attempt–grant
form holds outright and its counter is identically zero.  Weak fairness follows from fair
scheduling alone, and `SF` from fair scheduling and persistence.  The device task at a gate
(`Fairness.lean` 5.5) waits on whoever opens the gate, which is an obligation and not a fairness
assumption. -/

/-- With a grant certain at the thread's attempts there are no misses, so the attempt–grant form
holds outright. -/
theorem attemptGrant_of_certain (hc : Certain i A G σ) : AttemptGrant i A G σ :=
  AttemptGrant.fair_of_certain hc

/-- With a grant certain at the thread's attempts the zero function is a counter: reset at every
granted attempt, stay elsewhere, never a drop. -/
theorem counter_zero_of_certain (hc : Certain i A G σ) : IsCounter i A G σ (fun _ => 0) :=
  AttemptGrant.counter_zero_of_certain hc

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

/-! ## 6. The schedule as a proof instrument: fair labelling

Every run on which each thread is fairly scheduled admits a schedule that is fair as well
(`exists_fair_schedule`).  A *schedule* names one stepping thread at each position of the run.  A
schedule is fair when every thread active infinitely often is named infinitely often at positions
where it is active.  Fair scheduling is the relational assumption `Action.SF` of the thread step:
a thread active infinitely often steps infinitely often.

No run and no assumption names the thread that takes a step, but the adequacy proof needs one.
Each step must have an owner whose fuel pays for it while the other threads' scheduling counters
drop.  A step that changes the configuration has a forced owner.  A no-op step can be a step of
several threads at once, and the schedule chooses its owner.  The theorem says that the choice can
be made fairly, so the adequacy proof may assume a fair schedule although no hypothesis mentions
one.

Position `n` is a *claim* of thread `i` when `i` is active at `n` and the step taken at `n` is one
of `i`'s steps (`FairLabel.claim`).  Fair scheduling says that a thread active infinitely often has
infinitely many claims, and the schedule must give each such thread infinitely many of them.  A
position may be claimed by several threads, and infinitely many threads may appear over time.  A
priority by index or by count would therefore let fresh threads starve an old one.

The construction is diagonal.  Stage `s` visits the threads `0, 1, …, s` in order
(`FairLabel.visit`).  A frontier starts at 0 and only moves forward (`FairLabel.front`).  A visited
thread with a claim at or beyond the frontier takes the least such claim, and the frontier moves
just past it.  A visited thread with no such claim is skipped.  Two visits never take the same
position, because each taken position lies between the frontier before its visit and the frontier
after it (`FairLabel.takes_unique`).  A thread with infinitely many claims is visited at every stage
from its index on, and at each visit it finds a claim beyond the frontier.  It therefore takes
positions as far out as wanted (`FairLabel.exists_takes_ge`).  The schedule names at a taken
position the thread that took it, and at any other position some thread that steps there, which
exists because the run is a run of the pool (`FairLabel.sched`).

The construction is classical.  The names in `FairLabel` are auxiliary, and only the theorem is
meant for use. -/

namespace FairLabel

/-! ### The diagonal visit order -/

/-- The visit order, as pairs (stage, thread).  Stage `s` visits the threads `0, 1, …, s` in order,
and stage `s + 1` follows. -/
def visit : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 =>
    if (visit k).2 < (visit k).1 then ((visit k).1, (visit k).2 + 1) else ((visit k).1 + 1, 0)

/-- Within a stage, the visits run through the threads in order. -/
theorem visit_add {k s : Nat} (hk : visit k = (s, 0)) : ∀ j, j ≤ s → visit (k + j) = (s, j)
  | 0, _ => hk
  | j + 1, hj => by
    rw [← Nat.add_assoc, visit, visit_add hk j (Nat.le_of_succ_le hj)]
    exact ite_eq_left hj

/-- Every stage `s` begins, at a visit numbered at least `s`. -/
theorem exists_visit_stage : ∀ s, ∃ k, s ≤ k ∧ visit k = (s, 0)
  | 0 => ⟨0, Nat.le_refl 0, rfl⟩
  | s + 1 => by
    obtain ⟨k, hsk, hk⟩ := exists_visit_stage s
    refine ⟨k + s + 1, Nat.succ_le_succ (Nat.le_trans hsk (Nat.le_add_right k s)), ?_⟩
    rw [visit, visit_add hk s (Nat.le_refl s)]
    exact ite_eq_right (Nat.lt_irrefl s)

/-- Every thread is visited infinitely often: thread `i` at every stage from `i` on. -/
theorem visit_infOften (i : Nat) : MissHit.InfOften (fun k => (visit k).2 = i) := by
  intro n
  obtain ⟨k, hk, hv⟩ := exists_visit_stage (i + n)
  refine ⟨k + i, by omega, ?_⟩
  show (visit (k + i)).2 = i
  rw [visit_add hv i (Nat.le_add_right i n)]

/-! ### The frontier and the positions taken -/

variable {Cfg : Type} [Pool Cfg] (active : Nat → Cfg → Prop) (σ : Nat → Cfg)

/-- Position `n` is a claim of thread `i`: the thread is active at `n`, and the step taken at `n`
is one of its steps. -/
def claim (i n : Nat) : Prop := active i (σ n) ∧ Pool.Step i (σ n) (σ (n + 1))

open Classical in
/-- The frontier before visit `k`.  The thread visited at `k` takes its least claim at or beyond
the frontier, if it has one, and the frontier moves just past that claim.  Otherwise the frontier
stays. -/
noncomputable def front : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if h : ∃ p, front k ≤ p ∧ claim active σ (visit k).2 p then MissHit.minWitness h + 1
    else front k

/-- Visit `k` takes position `n`: `n` is a claim of the visited thread at or beyond the frontier,
and the frontier moves just past `n`. -/
def takes (k n : Nat) : Prop :=
  front active σ k ≤ n ∧ claim active σ (visit k).2 n ∧ front active σ (k + 1) = n + 1

variable {active σ}

/-- The frontier never moves back at a visit. -/
theorem front_le_succ (k : Nat) : front active σ k ≤ front active σ (k + 1) := by
  rw [front]
  split
  · next h => exact Nat.le_succ_of_le (MissHit.minWitness_spec h).1
  · exact Nat.le_refl _

/-- The frontier never moves back. -/
theorem front_mono {k k' : Nat} (h : k ≤ k') : front active σ k ≤ front active σ k' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (front_le_succ _)

/-- A visited thread with a claim at or beyond the frontier takes the least such claim. -/
theorem takes_of_exists {k : Nat}
    (h : ∃ p, front active σ k ≤ p ∧ claim active σ (visit k).2 p) :
    takes active σ k (MissHit.minWitness h) :=
  ⟨(MissHit.minWitness_spec h).1, (MissHit.minWitness_spec h).2, by rw [front, dite_eq_left h]⟩

/-- Two visits never take the same position.  A taken position lies between the frontier before
its visit and the frontier after it, and the frontier never moves back. -/
theorem takes_unique {k k' n : Nat} (h : takes active σ k n) (h' : takes active σ k' n) :
    k = k' := by
  obtain ⟨hle, -, hsucc⟩ := h
  obtain ⟨hle', -, hsucc'⟩ := h'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := front_mono (active := active) (σ := σ) (k := k + 1) hlt
    omega
  · exact heq
  · have := front_mono (active := active) (σ := σ) (k := k' + 1) hgt
    omega

/-- A thread with infinitely many claims takes positions as far out as wanted.  The frontier at
its visits grows without bound: at each visit the thread finds a claim beyond the frontier, takes
it and moves the frontier past it, and its next visit comes later. -/
theorem exists_takes_ge {i : Nat} (hcl : MissHit.InfOften (claim active σ i)) (N : Nat) :
    ∃ k n, (visit k).2 = i ∧ N ≤ n ∧ takes active σ k n := by
  have hfront : ∀ N, ∃ k, (visit k).2 = i ∧ N ≤ front active σ k := by
    intro N
    induction N with
    | zero =>
      obtain ⟨k, _, hk⟩ := visit_infOften i 0
      exact ⟨k, hk, Nat.zero_le _⟩
    | succ N ih =>
      obtain ⟨k, hk, hN⟩ := ih
      obtain ⟨p, hp, hcp⟩ := hcl (front active σ k)
      obtain ⟨hle, -, hsucc⟩ := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
      obtain ⟨k', hk', hv⟩ := visit_infOften i (k + 1)
      have := front_mono (active := active) (σ := σ) hk'
      exact ⟨k', hv, by omega⟩
  obtain ⟨k, hk, hN⟩ := hfront N
  obtain ⟨p, hp, hcp⟩ := hcl (front active σ k)
  have ht := takes_of_exists (k := k) ⟨p, hp, hk ▸ hcp⟩
  exact ⟨k, _, hk, Nat.le_trans hN ht.1, ht⟩

/-! ### The schedule -/

open Classical in
/-- The schedule: at a taken position, the thread that took it; at any other position, some thread
that steps there. -/
noncomputable def sched (hrun : PoolRun σ) (n : Nat) : Nat :=
  if h : ∃ k, takes active σ k n then (visit h.choose).2 else (hrun n).choose

/-- The schedule names a stepping thread at every position. -/
theorem sched_step (hrun : PoolRun σ) (n : Nat) :
    Pool.Step (sched (active := active) hrun n) (σ n) (σ (n + 1)) := by
  rw [sched]
  split
  · next h => exact h.choose_spec.2.1.2
  · exact (hrun n).choose_spec

/-- At a taken position, the schedule names the thread that took it. -/
theorem sched_of_takes (hrun : PoolRun σ) {k n : Nat} (h : takes active σ k n) :
    sched (active := active) hrun n = (visit k).2 := by
  have hex : ∃ k, takes active σ k n := ⟨k, h⟩
  rw [sched, dite_eq_left hex, takes_unique hex.choose_spec h]

end FairLabel

/-- **Fair labelling.**  A run of the pool on which every thread is fairly scheduled in the
relational sense (`Action.SF` of the thread step: a thread active infinitely often steps infinitely
often) admits a schedule, one stepping thread per position, under which every thread active
infinitely often is named infinitely often while active.  The adequacy proof uses the schedule for
its per-thread bookkeeping; no assumption mentions it. -/
theorem exists_fair_schedule {Cfg : Type} [Pool Cfg] {active : Nat → Cfg → Prop} {σ : Nat → Cfg}
    (hrun : PoolRun σ)
    (hsf : ∀ i, Action.SF (active i) (fun c c' => Pool.Step i c c') σ) :
    ∃ sched : Nat → Nat, (∀ n, Pool.Step (sched n) (σ n) (σ (n + 1))) ∧
      ∀ i, MissHit.InfOften (fun n => active i (σ n)) →
        MissHit.InfOften (fun n => active i (σ n) ∧ sched n = i) := by
  refine ⟨FairLabel.sched (active := active) hrun, FairLabel.sched_step hrun, ?_⟩
  intro i hA N
  obtain ⟨k, n, hk, hN, ht⟩ := FairLabel.exists_takes_ge (hsf i hA) N
  exact ⟨n, hN, hk ▸ ht.2.1.1, (FairLabel.sched_of_takes hrun ht).trans hk⟩

end Fairness

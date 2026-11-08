import MachCSL.Lang
import MachCSL.Liveness.FairnessTheory

/-! # The attempt–grant model of fairness: MachCSL's instance

MachCSL's runs as an instance of the general theory of `MachCSL/Liveness/FairnessTheory.lean`
(layers 0 to 2, generic over a thread pool).  This file gives MachCSL's pool, its eras and the six
actions the liveness proof uses.  Five of the actions are assumptions: they are the `SF`
hypotheses of `Spec.Hyps` (`Tick`, `Arm`, `Fresh`, `Hart`, `Dma`).  The sixth, `Dev`, is derived:
its grant is certain at the task's attempts, and its forms are theorems.  The theory file is a
stopgap that Lantana's extension deletes; this file stays, retargeted to Lantana's traces.

Every enabling condition states the thread's shape through the two shared relations of section 4.
Every grant is the thread's own step plus the condition that decides it, never the program the
thread moves on to: a condition on the machine state before the step for an arbitration (`Hart`,
`Dma`), the enabling condition itself for a gate (`Dev`), and the value chosen for a choice
(`Tick`, `Arm`, `Fresh`).

The file was the probe `local-plan/liveness/probes/Fairness.lean` until 2026-11-05 (lane
`xv6-liveness-now`, milestone B1; the design documents that cite it by section and theorem name
are `local-plan/liveness/attempt-grant.md` and `fairness-base.md`; all of `local-plan/` is outside
the repository).  It was re-layered 2026-11-06 (lane `fairness-layers`): the state form of an
action is the base, and the thread's view is built on top of it.  The same day (lane
`fairness-split`) the general theory moved to `FairnessTheory.lean`, generic over the pool, and
this file kept MachCSL's instance; later that day (lane `fairness-ag`) the theory's layer 0 became
the attempt–grant pair, three layers in all.  On 2026-11-08 (lane `fairness-shape`) the thread's
shape was stated once and every grant became the thread's step plus the condition that decides
it.  Nothing in the trusted base imports this directory (`MachCSL/Liveness/`); it is built by
`lake build MachCSL` and checked by CI like every module of the library.

**Map of the file.**

1. MachCSL's pool: configurations and a thread's primitive step (`Cfg`, `Step`), which make a
   pool of the general theory (the instance of `Pool`), and a step of one thread leaves the
   others in place (`step_get?_ne`).
2. `Era`, MachCSL's runs: liveness, generations, the power thread; persistence for an enabling
   condition that is a live thread's and is stable under every thread but the power thread
   (`persists_of_liveStable`), or under the steps that meet a side condition
   (`persists_of_liveStableUnder`, for a gate another thread can close).
3. `Mem`, the store order and the coherence floors: no step but a power-on lowers the top of the
   store order (`Mem.top_mono`) or a coherence floor (`Mem.coh_mono`).
4. The thread's shape: a live hart running a program (`hartAt`) and a live device task running a
   program (`taskAt`), each a live thread's and stable under every other thread's step but the
   power thread's.
5. The actions `Tick`, `Arm`, `Fresh`, `Hart`: each gives `enabled` (the `A`) and `grant` (the
   `G`, the thread's step and the condition that decides it), its `SF` (layer 1) and `AG`
   (layer 2) forms, and proves `ownGrant`, `live`, `stable`, `persists`, `sf_iff` and
   `counter_of_sf`.  Then the device tasks: `Dev`, a task at a gate, whose grant is certain at its
   attempts (`answered`, `certain`, `counter_zero`, `wf`); and `Dma`, a DMA write under a
   reservation, an action like `Hart` whose persistence is a protocol property.  What a hit and a
   miss of `Hart` and `Dma` are in machine terms, an access served and a blocked retry that keeps
   the head, is proved in `MachCSL/Liveness/Cycle.lean`.

**Names.**  The file follows the naming policy of `FairnessTheory.lean`'s header.  Every action
uses the same names: `enabled`, `grant`, `ownGrant`, `SF`, `AG`, `live`; the four strong
assumptions (`Tick`, `Arm`, `Fresh`, `Hart`) add `stable`, `persists`, `sf_iff` and
`counter_of_sf`; `Dma` has `counter_of_sf` and an `sf_iff` that takes persistence as a
hypothesis; `Dev`, whose grant is certain, has `certain`, `ag`, `counter_zero`, `wf` and
`sf_of_persists`.  Each action but `Dev` also names the shape its condition is about:
`Tick.restart` (the hart's step from its boundary), `Arm.answer` (the root's step to an answer),
`Fresh.atLoad` (a hart at a plain load), `Hart.pending` (a hart at a pending access),
`Dma.atWrite` and `Dma.pending` (a task at a DMA write, and at a pending one).  The two
arbitrations, `Hart` and `Dma`, name their condition `blocked`.
-/

namespace Fairness

/-! ## 1. MachCSL's pool: configurations and a thread's step

A configuration is MachCSL's thread pool and global state, and the step of the thread at a
position is a primitive step of its expression.  The two make MachCSL's pool a pool of the
general theory (`FairnessTheory.lean` section 3).  A run is then a sequence of configurations, and
`Steps`, `PoolRun` and `StepsInfOften` are the theory's, read at this pool. -/

open MachCSL Sail Sail.ArchSem LeanRV64D

/-- A configuration: the thread pool and the global state. -/
abbrev Cfg := List Expr × GState

/-- The thread at position `i` takes a primitive step from `c` to `c'`. -/
def Step (i : Nat) (c c' : Cfg) : Prop :=
  ∃ e obs e' efs, c.1[i]? = some e ∧ primStep (e, c.2) obs (e', c'.2, efs) ∧
    c'.1 = c.1.set i e' ++ efs

/-- MachCSL's thread pool is a pool of the general theory. -/
instance : Pool Cfg := ⟨Step⟩

section Pool

variable {i j : Nat} {c c' : Cfg}

/-- A step of the thread at `j` leaves every other position of the pool as it was. -/
theorem step_get?_ne {e : Expr} (hs : Step j c c') (hji : j ≠ i) (he : c.1[i]? = some e) :
    c'.1[i]? = some e := by
  obtain ⟨_, _, e', efs, _, _, hc'⟩ := hs
  have hi : i < c.1.length := (List.getElem?_eq_some_iff.1 he).1
  rw [hc', List.getElem?_append_left (by simpa using hi), List.getElem?_set_ne hji, he]

end Pool

/-! ## 2. MachCSL's runs: liveness, generations, the power thread (`Era`)

MachCSL has no values: a thread never finishes, and what ends its attempts is the end of its era.
Every enabling condition of the actions is a live thread's, and is stable under the steps of
every thread but the power thread.  The power thread breaks stability only by a cut, which bumps
the generation and so falsifies the condition for ever.  That gives persistence, the hypothesis
of layer 2's completeness (`Thread.Persists`).  The section is MachCSL's own; Lantana takes nothing
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

/-! ## 3. The store order and the coherence floors never go down, except at a power-on

Two facts about the memory model, each for every step of a thread that is not the power thread (a
power-on resets the memory).  The top of the store order never goes down (`top_mono`); that keeps
`Fresh`'s enabling condition stable (`Fresh.stable`).  No coherence floor of any hart goes down,
while every floor is at or below the top (`coh_mono`); that is the fact behind the logic's floor
receipts (`MachCSL.floorLbAt`), in which `Fresh`'s grant is consumed. -/

namespace Mem

variable {j : Nat} {c c' : Cfg}

/-! ### The top of the store order -/

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

/-! ### The coherence floors

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

end Mem

/-! ## 4. The thread's shape: a live hart or task running a program

Every enabling condition is about the thread at a position: a live hart running a program, or a
live task of a device running a program.  The two relations below state that shape once.  Each is
a live thread's and survives every other thread's step but the power thread's, so every action's
`live` and `stable` is one line. -/

open Era (liveAt StableExceptPower)

section Shape

variable {i j : Nat} {c c' : Cfg} {x : CPU} {d : DevId} {tid : TaskId}

/-- The thread at `i` is a live hart `x` running the program `m`. -/
def hartAt (i : Nat) (c : Cfg) (x : CPU) (m : SailM Unit) : Prop :=
  ∃ e, c.1[i]? = some (.hart e x m) ∧ threadLive c.2 e

/-- The thread at `i` is a live task `tid` of device `d` running the program `m`. -/
def taskAt (i : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (c : Cfg) : Prop :=
  ∃ e, c.1[i]? = some (.dev e d tid m) ∧ threadLive c.2 e

/-- A hart running a program is a live thread. -/
theorem hartAt_live {m : SailM Unit} (h : hartAt i c x m) : liveAt i c :=
  let ⟨e, he, hl⟩ := h; ⟨e, Or.inl ⟨x, m, he⟩, hl⟩

/-- A task running a program is a live thread. -/
theorem taskAt_live {m : DevProg d} (h : taskAt i d tid m c) : liveAt i c :=
  let ⟨e, he, hl⟩ := h; ⟨e, Or.inr ⟨d, tid, m, he⟩, hl⟩

/-- A hart's program and liveness survive every other thread's step but the power thread's. -/
theorem hartAt_stable {m : SailM Unit} (h : hartAt i c x m) (hs : Step j c c') (hji : j ≠ i)
    (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) : hartAt i c' x m :=
  let ⟨e, he, hl⟩ := h; ⟨e, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl⟩

/-- A task's program and liveness survive every other thread's step but the power thread's. -/
theorem taskAt_stable {m : DevProg d} (h : taskAt i d tid m c) (hs : Step j c c') (hji : j ≠ i)
    (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) : taskAt i d tid m c' :=
  let ⟨e, he, hl⟩ := h; ⟨e, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl⟩

end Shape

/-! ## 5. The six actions

Each action gives its enabling condition `enabled` (the `A`) and its grant relation `grant` (the
`G`), its trusted form `SF` (layer 1) and its proof form `AG` (layer 2).  Every `enabled` is a
line on section 4's relations.  Every `grant` is the thread's step, `Step i c c'`, and the
condition that decides it, so every action has own grant and takes the cheap path of layer 2.  The
first four actions prove: `ownGrant`, the grant is one of the thread's transitions; `live`, the
condition is a live thread's; `stable`, it survives every thread's step but the power thread's;
`persists`, from the two; `sf_iff`, the two forms coincide under fair scheduling;
`counter_of_sf`, the trusted form gives the thread's counter.  The two device tasks (5.5, 5.6)
prove what their persistence allows. -/

/-! ### 5.1 The tick: a live hart at its cycle boundary; the restart carries the tick -/

namespace Tick

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The enabling condition: the thread at `i` is a live hart at its cycle boundary. -/
def enabled (i : Nat) (c : Cfg) : Prop := ∃ x, hartAt i c x (.pure ())

/-- The hart's step from its boundary that restarts its cycle with `tick`. -/
def restart (i : Nat) (tick : Bool) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e x ew, c.1[i]? = some (.hart e x (.pure ())) ∧
    c'.1[i]? = some (.hart e x (riscvStep tick ew))

/-- The grant: the restart carries the tick. -/
abbrev grant (i : Nat) : Cfg → Cfg → Prop := restart i true

/-- The grant is one of the hart's transitions. -/
theorem ownGrant : Thread.OwnGrant i (grant i) := fun h => h.1

/-- Trusted: a hart at its boundary infinitely often restarts with the tick infinitely often. -/
abbrev SF (i : Nat) (σ : Nat → Cfg) : Prop := Action.SF (enabled i) (grant i) σ

/-- Proof form: infinitely many tickless restarts force infinitely many ticking ones. -/
abbrev AG (i : Nat) (σ : Nat → Cfg) : Prop := Thread.AttemptGrant i (enabled i) (grant i) σ

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i c) : liveAt i c := let ⟨_, h⟩ := h; hartAt_live h

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i) :=
  fun hji hs hnp ⟨x, h⟩ => ⟨x, hartAt_stable h hs hji hnp⟩

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

/-! ### 5.2 A device's `choose` arm: the live root at the node; class `b` chosen -/

namespace Arm

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The continuation of a `choose` node at the answer `v`. -/
def at? {S T α : Type} : DevM S T α → Nat → Option (DevM S T α)
  | .op .choose k, v => some (k v)
  | _, _ => none

/-- The enabling condition: the thread at `i` is the live root of device `d` at the node. -/
def enabled (i : Nat) (d : DevId) (node : DevProg d) (c : Cfg) : Prop :=
  taskAt i d rootTask node c

/-- The root's step from the node to its continuation at the answer `v`. -/
def answer (i : Nat) (d : DevId) (node : DevProg d) (v : Nat) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∃ e, c.1[i]? = some (.dev e d rootTask node) ∧
    c'.1[i]? = (at? node v).map (.dev e d rootTask)

/-- The grant: an answer of class `b` modulo `m`. -/
def grant (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (c c' : Cfg) : Prop :=
  ∃ v, v % m = b ∧ answer i d node v c c'

/-- The grant is one of the root's transitions. -/
theorem ownGrant {d : DevId} {node : DevProg d} {m b : Nat} :
    Thread.OwnGrant i (grant i d node m b) := fun ⟨_, _, h⟩ => h.1

/-- Trusted: a root at the node infinitely often takes class `b` infinitely often. -/
abbrev SF (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d node) (grant i d node m b) σ

/-- Proof form: infinitely many steps of the root at the node that take another class force
infinitely many that take class `b`. -/
abbrev AG (i : Nat) (d : DevId) (node : DevProg d) (m b : Nat) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d node) (grant i d node m b) σ

variable {d : DevId} {node : DevProg d} {m b : Nat}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d node c) : liveAt i c := taskAt_live h

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i d node) :=
  fun hji hs hnp h => taskAt_stable h hs hji hnp

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

/-! ### 5.3 The visibility of a store: a live hart at a plain load of `a` once store `t` exists;
the load sees `t` -/

namespace Fresh

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The thread at `i` is a live hart whose head event is a plain RAM load covering `a`. -/
def atLoad (i : Nat) (a : PAddr) (c : Cfg) : Prop := ∃ x req k,
  hartAt i c x (.impure (.inl (.ok (.memRead req))) k) ∧ akPlain req.accessKind = true ∧
  ramBytes req.pa req.size ∧ ∃ j, j < req.size ∧ a = req.pa + BitVec.ofNat 64 j

/-- The enabling condition: the load covers `a` and the store `t` has happened. -/
def enabled (i : Nat) (t : Nat) (a : PAddr) (c : Cfg) : Prop := atLoad i a c ∧ t ≤ c.2.m.top

/-- The grant: the hart's own step, after which its view of `a`, its coherence floor, is at or
past `t`: the load read at a view that includes store `t`. -/
def grant (i t : Nat) (a : PAddr) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∀ x m, hartAt i c x m → t ≤ (c'.2.m.hr x).coh a

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
theorem live (h : enabled i t a c) : liveAt i c := let ⟨⟨_, _, _, h, _⟩, _⟩ := h; hartAt_live h

/-- The enabling condition survives every other thread's step but the power thread's: the load
stays, and the top of the store order does not go down. -/
theorem stable : StableExceptPower i (enabled i t a) :=
  fun hji hs hnp ⟨⟨x, req, k, h, hr⟩, ht⟩ =>
    ⟨⟨x, req, k, hartAt_stable h hs hji hnp, hr⟩, Nat.le_trans ht (Mem.top_mono hs hnp)⟩

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

/-! ### 5.4 Harts progress: a live hart at a pending RAM access; the access is not blocked -/

namespace Hart

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg} {x x' : CPU} {pa pa' : PAddr} {n n' : Nat}

/-- The thread at `i` is a live hart `x` whose head event is a RAM store or an exclusive RAM read
with footprint `(pa, n)`: a pending access. -/
def pending (i : Nat) (c : Cfg) (x : CPU) (pa : PAddr) (n : Nat) : Prop := ∃ o k,
  hartAt i c x (.impure (.inl (.ok o)) k) ∧ ramBytes pa n ∧
  match o with
  | .memRead req => akExcl req.accessKind = true ∧ pa = req.pa ∧ n = req.size
  | .memWrite req _ _ => pa = req.pa ∧ n = req.size
  | _ => False

/-- The enabling condition: the hart has a pending access, blocked or not. -/
def enabled (i : Nat) (c : Cfg) : Prop := ∃ x pa n, pending i c x pa n

/-- The arbitration condition: another hart's blocking reservation covers the footprint
(`othersReserve`; an LR's reservation blocks nobody since lane `lr-nonblock`, 2026-11-04). -/
def blocked (m : MState) (x : CPU) (pa : PAddr) (n : Nat) : Prop := othersReserve m.resv x pa n

/-- The grant: the hart's own step, at which its pending access is not blocked. -/
def grant (i : Nat) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∀ x pa n, pending i c x pa n → ¬ blocked c.2.m x pa n

/-- The grant is one of the hart's transitions. -/
theorem ownGrant : Thread.OwnGrant i (grant i) := fun h => h.1

/-- Trusted: a hart with a pending access infinitely often steps with it unblocked infinitely
often (RVWMO's Progress Axiom in the model's terms). -/
abbrev SF (i : Nat) (σ : Nat → Cfg) : Prop := Action.SF (enabled i) (grant i) σ

/-- Proof form: infinitely many steps at a blocked access force infinitely many at an unblocked
one. -/
abbrev AG (i : Nat) (σ : Nat → Cfg) : Prop := Thread.AttemptGrant i (enabled i) (grant i) σ

/-- The Progress Axiom in response form: every pending access eventually steps unblocked. -/
abbrev ProgressAxiom (i : Nat) (σ : Nat → Cfg) : Prop := Action.Response (enabled i) (grant i) σ

/-- A hart has at most one pending access: the hart and the footprint are its head event's. -/
theorem pending_unique (h : pending i c x pa n) (h' : pending i c x' pa' n') :
    x = x' ∧ pa = pa' ∧ n = n' := by
  obtain ⟨o, k, ⟨e, he, -⟩, -, hm⟩ := h
  obtain ⟨o', k', ⟨e', he', -⟩, -, hm'⟩ := h'
  rw [he] at he'
  obtain ⟨-, rfl, hmk⟩ := Expr.hart.inj (Option.some.inj he')
  injection hmk with ho
  injection ho with ho
  injection ho with ho
  subst ho
  refine ⟨rfl, ?_⟩
  cases o with
  | memRead req => exact ⟨hm.2.1.trans hm'.2.1.symm, hm.2.2.trans hm'.2.2.symm⟩
  | memWrite req w a => exact ⟨hm.1.trans hm'.1.symm, hm.2.trans hm'.2.symm⟩
  | _ => exact hm.elim

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i c) : liveAt i c := let ⟨_, _, _, _, _, h, _⟩ := h; hartAt_live h

/-- The enabling condition survives every other thread's step but the power thread's. -/
theorem stable : StableExceptPower i (enabled i) :=
  fun hji hs hnp ⟨x, pa, n, o, k, h, hr⟩ => ⟨x, pa, n, o, k, hartAt_stable h hs hji hnp, hr⟩

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

/-! ### 5.5 A device task at a gate: the grant is certain, no fairness assumption

A device task's head primitive is blocked (`devBlocked`) in three cases: a guard that does not
answer (or answers an unfaithful move), a join on an unfinished task, and a DMA write whose
footprint is under a blocking reservation (5.6, excluded here by `isDma`).  The first two are
*gates*.  What opens a gate is a change of shared state by another thread: the device state the
guard reads, or the joined task's end.  Once the gate is open, the task's step through it answers
the primitive (`answered`).  The grant is the task's step, so it is certain at the task's attempts
(`certain`, in the sense of layer 2): the action has no misses, its counter is zero
(`counter_zero`), and its weak fairness follows from fair scheduling (`wf`).  What the task waits
on is the opener's obligation.  Whether an open gate stays open until the task's step
(persistence) is a property of the protocol, the stable-gate lemma of the plan (`HANDOFF.md` §6
task 5), proved gate by gate in `MachCSL/Liveness/Gates.lean`; with it the action's strong
fairness follows too (`sf_of_persists`). -/

namespace Dev

variable {i : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- A DMA write, the one primitive a hart's reservation can block; handled by `Dma` (5.6). -/
def isDma {S T : Type} : DevOp S T → Prop
  | .dmaWrite _ _ _ _ => True
  | _ => False

/-- The enabling condition: the thread at `i` is a live task of device `d` at a primitive other
than a DMA write that is not blocked, that is, at an open gate (a guard that answers faithfully,
or a join on a finished task) or at a primitive that never blocks. -/
def enabled (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ o k, taskAt i d tid (.op o k) c ∧ ¬ isDma o ∧ ¬ devBlocked d o c.2.m

/-- The grant: the task's own step.  At an open gate the step answers the primitive
(`answered`). -/
def grant (i : Nat) (d : DevId) (tid : TaskId) (c c' : Cfg) : Prop := Step i c c'

/-- The grant is one of the task's transitions. -/
theorem ownGrant {d : DevId} {tid : TaskId} : Thread.OwnGrant i (grant i d tid) := fun h => h

/-- Strong fairness of a task at an unblocked primitive: it steps infinitely often. -/
abbrev SF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d tid) (grant i d tid) σ

/-- Proof form: every step of the task at an unblocked primitive is a grant, so it holds outright
(`ag`). -/
abbrev AG (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d tid) (grant i d tid) σ

/-- Weak fairness of a task at an unblocked primitive.  Fair scheduling gives it (`wf`). -/
abbrev WF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.WF (enabled i d tid) (grant i d tid) σ

variable {d : DevId} {tid : TaskId}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d tid c) : liveAt i c := let ⟨_, _, h, _⟩ := h; taskAt_live h

/-- A live task at an unblocked primitive is answered when it steps: it moves on to the
continuation at some answer. -/
theorem answered (h : enabled i d tid c) (hs : Step i c c') :
    ∃ e o k v, c.1[i]? = some (.dev e d tid (.op o k)) ∧ c'.1[i]? = some (.dev e d tid (k v)) := by
  obtain ⟨o, k, ⟨e, he, hl⟩, -, hnb⟩ := h
  obtain ⟨ex, obs, e', efs, he', hp, hc'⟩ := hs
  rw [he] at he'
  obtain rfl := Option.some.inj he'
  have hi : i < c.1.length := (List.getElem?_eq_some_iff.1 he).1
  have hc'i : c'.1[i]? = some e' := by
    rw [hc', List.getElem?_append_left (by simpa using hi), List.getElem?_set_self hi]
  rcases hp with ⟨-, m', σ', rfl, hd, -⟩ | ⟨hnl, -⟩
  · simp only [devStep] at hd
    rcases hd with ⟨v, rfl, -⟩ | ⟨hb, -⟩
    · exact ⟨e, o, k, v, he, hc'i⟩
    · exact absurd hb hnb
  · exact absurd hl hnl

/-- The grant is certain at the task's attempts: an attempt is a step. -/
theorem certain : Thread.Certain i (enabled i d tid) (grant i d tid) σ := fun _ ha => ha.1

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

/-! ### 5.6 A device's DMA write under a reservation: memory arbitration, as for harts

The third way a device primitive blocks is a DMA write whose footprint is under a blocking
reservation.  That is memory arbitration, the same situation as a hart's blocked access, and it
fits the model the same way.  The attempt is a live task's step at a pending DMA write, one whose
guard answers a faithful move into RAM; the grant is the task's step at which the write is not
blocked; the miss is a step at which it is, a blocked retry.  Its `SF` is the Progress Axiom for
the DMA agent.  xv6 may not need the assumption: if no reservation ever covers a DMA buffer, a
safety fact, the miss never happens. -/

namespace Dma

variable {i : Nat} {c : Cfg} {σ : Nat → Cfg}

/-- The thread at `i` is a live task `tid` of `d` at the DMA write with guard `g`, footprint
`(pa, n)` and word `w`. -/
def atWrite (i : Nat) (d : DevId) (tid : TaskId) (g : DevSt d → Option (DevSt d)) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (c : Cfg) : Prop :=
  ∃ k, taskAt i d tid (.op (.dmaWrite g pa n w) k) c

/-- A pending DMA write: at a DMA write whose guard answers a faithful move, into RAM. -/
def pending (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) (pa : PAddr) (n : Nat) : Prop :=
  ∃ g w, atWrite i d tid g pa n w c ∧
    (∃ s', g (c.2.m.devs.st d) = some s' ∧ devObsOk d (c.2.m.devs.st d) s' []) ∧ ramBytes pa n

/-- The enabling condition: the task has a pending DMA write, blocked or not. -/
def enabled (i : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ pa n, pending i d tid c pa n

/-- The arbitration condition: some hart's blocking reservation covers the footprint. -/
def blocked (m : MState) (pa : PAddr) (n : Nat) : Prop := anyReserve m.resv pa n

/-- The grant: the task's own step, at which its pending DMA write is not blocked. -/
def grant (i : Nat) (d : DevId) (tid : TaskId) (c c' : Cfg) : Prop :=
  Step i c c' ∧ ∀ pa n, pending i d tid c pa n → ¬ blocked c.2.m pa n

/-- The grant is one of the task's transitions. -/
theorem ownGrant {d : DevId} {tid : TaskId} : Thread.OwnGrant i (grant i d tid) := fun h => h.1

/-- Trusted: a task with a pending DMA write infinitely often steps with it unblocked infinitely
often. -/
abbrev SF (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d tid) (grant i d tid) σ

/-- Proof form: infinitely many steps at a blocked DMA write force infinitely many at an
unblocked one. -/
abbrev AG (i : Nat) (d : DevId) (tid : TaskId) (σ : Nat → Cfg) : Prop :=
  Thread.AttemptGrant i (enabled i d tid) (grant i d tid) σ

variable {d : DevId} {tid : TaskId}

/-- The enabling condition is a live thread's. -/
theorem live (h : enabled i d tid c) : liveAt i c :=
  let ⟨_, _, _, _, ⟨_, h⟩, _⟩ := h; taskAt_live h

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

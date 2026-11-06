import MachCSL.Liveness.Fairness
import MachCSL.Resources
import MachCSL.UWait

/-! # A hart's cycle on a run: finite cycles, the restart, the closure of the choice instances

Milestones B4 and B5 of lane `xv6-liveness-now`, on the fairness theory of
`MachCSL.Liveness.Fairness`, whose naming policy this file follows.  Nothing in the trusted base
imports it.

The file, in order:

1. `Cycle`, finite cycles.  The one-step subterm relation `Below` on lean-sail's free monad is
   well founded, so no sequence of computations descends along it for ever (`not_descends`).  A
   hart's step restarts its cycle at the boundary, descends at an event or a choice, or is a
   blocked retry that keeps its expression (`hartStep_cases`, `step_descends`, `retry`).  On a
   run of the pool where the thread steps infinitely often, a hart therefore reaches its live
   boundary, dies, or retries (`boundary_or_dead_or_retry`), and the plan's form follows
   (`boundary_of_live`).  Device programs (`DevM`) get the same relation, `DevM.Below`, which is
   irreflexive too (`DevM.below_irrefl`).
2. `Hart`, what a pending access's step is: the served arm of `evStep` when it is not blocked
   (`served_of_unblocked`), a blocked retry that leaves it blocked when it is
   (`pending_of_blocked`).  So the hart's step is a grant exactly when the access is not blocked
   (`grant_iff_not_blocked`).  The action's hit is then a served access (`hit_iff`).  The hart's
   miss, from the thread's view of the action (section 5 of `MachCSL.Liveness.FairnessTheory`), is a
   blocked retry (`miss_iff`).
3. The machine closure of the choice instances.  At each enabling condition the thread has a step
   for the outcomes named here, and each grant is such a step: both restarts at a
   live boundary (`Tick.exists_grant`, `Tick.exists_not_grant`; a restarted cycle is never empty,
   `Cycle.riscvStep_impure`), every answer at a `choose` node (`Arm.exists_answer`), a load at
   the top (`Fresh.exists_grant`), a served access (`Hart.exists_served`).  Every own step at a
   plain load takes the load, so `Fresh`'s grant is, under its enabling condition, the post-state
   floor alone (`Fresh.takes_load`, `Fresh.grant_iff_coh`).  Subsection 3.5 does for a DMA write
   what section 2 does for a hart's access: the task's step is a grant exactly when the write is
   not blocked, so the action's hit is a served write and the task's miss is a blocked retry
   (`Dma.hit_iff`, `Dma.miss_iff`).
4. `ramHist`, every RAM byte has a nonempty history, the fact the memory reads of section 3 need:
   it is not part of `mmOk` (which says the converse), it holds of a booted memory and every step
   keeps it (`ramHist_step`, `ramHist_run`).
5. Harts progress in response form (B5): strong fairness is the Progress Axiom relativised to the
   era (`Hart.sf_iff_progressOrCut`), and the Progress Axiom itself on a run where the hart, once
   live, stays live (`Hart.sf_iff_response`).  The era rank (`Era.rank`) makes liveness convex
   along a run.
-/

namespace Fairness

open MachCSL Sail Sail.ArchSem LeanRV64D

/-! ## 1. Finite cycles (`Cycle`) -/

namespace Cycle

universe u v w

/-- One step down a free-monad computation: the continuation `k r` of a node `.impure o k`, at
any answer `r`, is below the node. -/
inductive Below {Eff : Type v} [Effect.{u, v} Eff] {α : Type w} :
    FreeM Eff α → FreeM Eff α → Prop
  | cont (o : Eff) (k : Effect.ret o → FreeM Eff α) (r : Effect.ret o) : Below (k r) (.impure o k)

section Below

variable {Eff : Type v} [Effect.{u, v} Eff] {α : Type w}

/-- Every computation is accessible: it has no infinite descent below it. -/
theorem acc_below (m : FreeM Eff α) : Acc Below m := by
  induction m with
  | pure a => exact ⟨_, fun y h => by cases h⟩
  | impure o k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩

/-- `Below` is well founded. -/
theorem below_wf : WellFounded (@Below Eff _ α) := ⟨acc_below⟩

/-- No sequence of computations descends along `Below` at every position. -/
theorem not_descends (f : Nat → FreeM Eff α) : ¬ ∀ n, Below (f (n + 1)) (f n) := by
  intro h
  have key : ∀ m, Acc Below m → ∀ n, f n = m → False := by
    intro m hm
    induction hm with
    | intro m _ ih =>
      intro n hn
      exact ih (f (n + 1)) (hn ▸ h n) (n + 1) rfl
  exact key _ (acc_below _) 0 rfl

/-- Nothing is below itself. -/
theorem below_irrefl (m : FreeM Eff α) : ¬ Below m m := by
  intro h
  exact not_descends (fun _ => m) (fun _ => h)

end Below

/-! ### Device programs

A device program is `DevM` (`MachCSL/Dev/DevLang.lean`), an inductive of its own, so `Below` does
not apply to it and it gets its own one-step relation.  Only irreflexivity is used: a device
task's step that answers its primitive never leaves the program in place. -/

/-- One step down a device program: the continuation `k r` of a node `.op o k`, at any answer
`r`, is below the node. -/
inductive DevM.Below {S T α : Type} : DevM S T α → DevM S T α → Prop
  | cont (o : DevOp S T) (k : o.ret → DevM S T α) (r : o.ret) : DevM.Below (k r) (.op o k)

/-- Every device program is accessible: it has no infinite descent below it. -/
theorem DevM.acc_below {S T α : Type} (m : DevM S T α) : Acc DevM.Below m := by
  induction m with
  | pure a => exact ⟨_, fun y h => by cases h⟩
  | op o k ih => exact ⟨_, fun y h => by cases h; exact ih _⟩

/-- No device program is below itself. -/
theorem DevM.below_irrefl {S T α : Type} (m : DevM S T α) : ¬ DevM.Below m m := by
  intro h
  induction DevM.acc_below m with
  | intro m _ ih => exact ih m h h

/-! ### One step of a hart -/

/-- What one step of a hart's cycle does to its expression: at the boundary `.pure ()` the cycle
restarts (and the reservation is released unless it is an LR's); an event step or a choice
descends; a blocked retry keeps the expression.  A failure node has no step. -/
theorem hartStep_cases {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') :
    (m = .pure () ∧ (∃ tick ew : Bool, m' = riscvStep tick ew) ∧ σ' = σ.dropWindow cpu) ∨
    Below m' m ∨
    (∃ o k, m = .impure (.inl (.ok o)) k ∧ blockedStep cpu o σ σ' ∧ m' = m) := by
  cases m with
  | pure u =>
    obtain ⟨tick, ew, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, ⟨tick, ew, rfl⟩, rfl⟩
  | impure call k =>
    cases call with
    | inl e =>
      cases e with
      | error _ => exact h.elim
      | ok o =>
        rcases h with ⟨r, rfl, -⟩ | ⟨hb, rfl⟩
        · exact Or.inr (Or.inl (Below.cont _ k r))
        · exact Or.inr (Or.inr ⟨o, k, rfl, hb, rfl⟩)
    | inr n =>
      obtain ⟨r, rfl, -⟩ := h
      exact Or.inr (Or.inl (Below.cont _ k r))

variable {i j n : Nat} {c c' : Cfg} {σ : Nat → Cfg} {e : Nat} {x : CPU} {m : SailM Unit}

/-- The position a thread's step writes holds the thread's new expression. -/
theorem getElem?_set_append {p : List Expr} {ex e' : Expr} {efs : List Expr}
    (he : p[i]? = some ex) : (p.set i e' ++ efs)[i]? = some e' := by
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 he).1
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_set_self hi]

/-- A primitive step of the thread at `i` is a `Step` of the pool. -/
theorem step_of_primStep {ex e' : Expr} {obs : List Obs} {g' : GState} {efs : List Expr}
    (he : c.1[i]? = some ex) (hp : primStep (ex, c.2) obs (e', g', efs)) :
    Step i c (c.1.set i e' ++ efs, g') :=
  ⟨ex, obs, e', efs, he, hp, rfl⟩

/-- A step of the thread at `i`, a hart: the thread after it is the same hart, either live and
having taken a `hartStep`, or dead and unchanged (the corpse's self-loop). -/
theorem step_hart (hs : Step i c c') (he : c.1[i]? = some (.hart e x m)) :
    ∃ m', c'.1[i]? = some (.hart e x m') ∧
      ((threadLive c.2 e ∧ hartStep x m c.2.m m' c'.2.m ∧ c'.2 = { c.2 with m := c'.2.m }) ∨
       (¬ threadLive c.2 e ∧ m' = m ∧ c'.2 = c.2)) := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨ex, obs, e', efs, he', hp, hc'⟩ := hs
  simp only at he he' hc' ⊢
  rw [he] at he'
  obtain rfl := Option.some.inj he'
  obtain ⟨-, ⟨hl, -, m', σ', rfl, hst, rfl⟩ | ⟨hl, -, rfl, rfl⟩⟩ := hp
  · exact ⟨m', by rw [hc']; exact getElem?_set_append he, Or.inl ⟨hl, hst, rfl⟩⟩
  · exact ⟨m, by rw [hc']; exact getElem?_set_append he, Or.inr ⟨hl, rfl, rfl⟩⟩

/-- For a hart, liveness of its thread is liveness of its generation. -/
theorem liveAt_hart_iff (he : c.1[i]? = some (.hart e x m)) :
    Era.liveAt i c ↔ threadLive c.2 e := by
  constructor
  · rintro ⟨e', ⟨x', m', h⟩ | ⟨d, tid, m', h⟩, hl⟩
    · rw [he] at h
      cases h
      exact hl
    · rw [he] at h
      cases h
  · intro hl
    exact ⟨e, Or.inl ⟨x, m, he⟩, hl⟩

/-- The thread at `i` takes a blocked retry from `c` to `c'`: it steps as a live hart at a model
event, the event is blocked (`blockedStep`), and the hart's expression stays. -/
def retry (i : Nat) (c c' : Cfg) : Prop := Step i c c' ∧ ∃ e x o k,
  c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)) ∧ threadLive c.2 e ∧
  blockedStep x o c.2.m c'.2.m ∧ c'.1[i]? = c.1[i]?

/-- A live hart's step from an event node is a blocked retry exactly when it keeps the
expression: an event step descends, so it never does. -/
theorem retry_iff {o : InstructionEffect} {k : InstructionEffect.ret o → SailM Unit}
    (hs : Step i c c') (he : c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)))
    (hl : threadLive c.2 e) : retry i c c' ↔ c'.1[i]? = c.1[i]? := by
  constructor
  · rintro ⟨-, -, -, -, -, -, -, -, h⟩
    exact h
  · intro heq
    obtain ⟨m', he', ⟨-, hst, -⟩ | ⟨hd, -⟩⟩ := step_hart hs he
    · rcases hartStep_cases hst with ⟨h, -⟩ | hb | ⟨o', k', h, hbl, rfl⟩
      · cases h
      · rw [heq, he] at he'
        cases he'
        exact absurd hb (below_irrefl _)
      · exact ⟨hs, e, x, o', k', h ▸ he, hl, hbl, heq⟩
    · exact absurd hl hd

/-- A live hart's step from inside its cycle (not at the boundary) that is not a blocked retry
makes its expression descend: it was an event step or a choice. -/
theorem step_descends (hs : Step i c c') (he : c.1[i]? = some (.hart e x m))
    (hl : threadLive c.2 e) (hm : m ≠ .pure ()) (hnr : ¬ retry i c c') :
    ∃ m', c'.1[i]? = some (.hart e x m') ∧ Below m' m := by
  obtain ⟨m', he', ⟨-, hst, -⟩ | ⟨hd, -⟩⟩ := step_hart hs he
  · rcases hartStep_cases hst with ⟨h, -⟩ | hb | ⟨o, k, rfl, hbl, rfl⟩
    · exact absurd h hm
    · exact ⟨m', he', hb⟩
    · exact absurd ⟨hs, e, x, o, k, he, hl, hbl, by rw [he', he]⟩ hnr
  · exact absurd hl hd

/-- Until its own next step, the thread at `i` keeps its expression: fair scheduling gives that
step, and every step before it is another thread's (`step_get?_ne`). -/
theorem next_own (hrun : PoolRun σ) (hsched : StepsInfOften i σ) {ex : Expr}
    (he : (σ n).1[i]? = some ex) : ∃ s ≥ n, Steps i σ s ∧ (σ s).1[i]? = some ex := by
  obtain ⟨s0, hs0, hst0⟩ := hsched n
  obtain ⟨s, ⟨hns, hst⟩, hmin⟩ :=
    MissHit.exists_min (p := fun s => n ≤ s ∧ Steps i σ s) s0 ⟨hs0, hst0⟩
  refine ⟨s, hns, hst, ?_⟩
  have key : ∀ q, n ≤ q → q ≤ s → (σ q).1[i]? = some ex := by
    intro q hnq hqs
    induction q with
    | zero =>
      have h0 : n = 0 := Nat.le_zero.1 hnq
      subst h0
      exact he
    | succ q ih =>
      rcases Nat.lt_or_eq_of_le hnq with hlt | heq
      · have hq := ih (Nat.le_of_lt_succ hlt) (Nat.le_of_succ_le hqs)
        obtain ⟨j, hj⟩ := hrun q
        have hji : j ≠ i := by
          rintro rfl
          exact hmin q (Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hqs) ⟨Nat.le_of_lt_succ hlt, hj⟩
        exact step_get?_ne hj hji hq
      · subst heq
        exact he
  exact key s hns (Nat.le_refl s)

/-- Finite cycles.  On a run of the pool where the thread at `i` steps infinitely often, a
hart at `i` eventually reaches its cycle boundary live (`Tick.enabled`), or is dead, or takes a
blocked retry.  No hypothesis beyond the run and fair scheduling: a cycle's events and choices
descend in the well-founded `Below`, and a live hart at a failure node cannot step, so fair
scheduling rules it out. -/
theorem boundary_or_dead_or_retry (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (he : (σ n).1[i]? = some (.hart e x m)) :
    ∃ k ≥ n, Tick.enabled i (σ k) ∨ ¬ Era.liveAt i (σ k) ∨ retry i (σ k) (σ (k + 1)) := by
  have hacc := acc_below m
  induction hacc generalizing n with
  | intro m _ ih =>
    obtain ⟨s, hns, hs, hes⟩ := next_own hrun hsched he
    obtain ⟨m', he', ⟨hl, hst, -⟩ | ⟨hd, -, -⟩⟩ := step_hart hs hes
    · rcases hartStep_cases hst with ⟨rfl, -, -⟩ | hb | ⟨o, k, rfl, hbl, rfl⟩
      · exact ⟨s, hns, Or.inl ⟨e, x, hes, hl⟩⟩
      · obtain ⟨k, hk, hP⟩ := ih m' hb he'
        exact ⟨k, Nat.le_trans hns (Nat.le_trans (Nat.le_succ s) hk), hP⟩
      · exact ⟨s, hns, Or.inr (Or.inr ⟨hs, e, x, o, k, hes, hl, hbl, by rw [he', hes]⟩)⟩
    · exact ⟨s, hns, Or.inr (Or.inl fun h => hd ((liveAt_hart_iff hes).1 h))⟩

/-- Finite cycles, the "boundary or no longer live" form: if from `n` on no step of the hart is
a blocked retry, it eventually reaches its boundary live or is dead. -/
theorem boundary_or_dead (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (he : (σ n).1[i]? = some (.hart e x m))
    (hnr : ∀ k ≥ n, ¬ retry i (σ k) (σ (k + 1))) :
    ∃ k ≥ n, Tick.enabled i (σ k) ∨ ¬ Era.liveAt i (σ k) := by
  obtain ⟨k, hk, h | h | h⟩ := boundary_or_dead_or_retry hrun hsched he
  · exact ⟨k, hk, Or.inl h⟩
  · exact ⟨k, hk, Or.inr h⟩
  · exact absurd h (hnr k hk)

/-- Finite cycles, the plan's form.  On a run of the pool where the thread at `i` steps
infinitely often, a hart at `i` that stays live from `n` on and takes no blocked retry from `n`
on reaches its cycle boundary. -/
theorem boundary_of_live (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (he : (σ n).1[i]? = some (.hart e x m)) (hlive : ∀ k ≥ n, Era.liveAt i (σ k))
    (hnr : ∀ k ≥ n, ¬ retry i (σ k) (σ (k + 1))) :
    ∃ k ≥ n, Tick.enabled i (σ k) := by
  obtain ⟨k, hk, h | h⟩ := boundary_or_dead hrun hsched he hnr
  · exact ⟨k, hk, h⟩
  · exact absurd (hlive k hk) h

end Cycle

/-! ## 2. Harts progress: what a pending access's step is -/

namespace Hart

open Cycle

variable {i : Nat} {c c' : Cfg}

/-- The served arm of `evStep` at a pending RAM access: the RAM write, or the exclusive read at
the top, each when no other hart's blocking reservation covers the footprint. -/
abbrev served (cpu : CPU) (o : InstructionEffect) (σ : MState) :
    InstructionEffect.ret o → MState → Prop :=
  match o with
  | .memRead req => fun v σ' =>
      ramBytes req.pa req.size ∧ akExcl req.accessKind = true ∧
        ¬ othersReserve σ.resv cpu req.pa req.size ∧
        ∃ w : BitVec (8 * req.size), σ.mem.topBytes req.pa req.size w ∧ v = .ok (w, 0#req.numTag) ∧
          σ' = σ.afterExcl cpu req.pa req.size w (akAcq req.accessKind) (kindOf req.accessKind)
  | .memWrite req w _ => fun v σ' =>
      ramBytes req.pa req.size ∧ ¬ othersReserve σ.resv cpu req.pa req.size ∧
        v = .ok () ∧ σ' = σ.store cpu req.pa req.size w (akExcl req.accessKind)
  | _ => fun _ _ => False

/-- The served arm is an arm of `evStep`. -/
theorem evStep_of_served {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    {v : InstructionEffect.ret o} (h : served cpu o σ v σ') : evStep cpu o σ v σ' := by
  cases o with
  | memRead req => exact Or.inr (Or.inr (Or.inr h))
  | memWrite req w a => exact Or.inr h
  | _ => exact h.elim

/-- An exclusive read is neither a fetch nor a plain read. -/
theorem not_ifetch_of_excl {k : AK} (h : akExcl k = true) : akIfetch k = false := by
  cases hf : akIfetch k
  · rfl
  · rw [akExcl_of_ifetch k hf] at h
    exact absurd h (by decide)

theorem not_plain_of_excl {k : AK} (h : akExcl k = true) : akPlain k = false := by
  simp [akPlain, h]

/-- The head event is a RAM store or an exclusive RAM read: the events `enabled` names. -/
def ramAccess : InstructionEffect → Prop
  | .memRead req => akExcl req.accessKind = true ∧ ramBytes req.pa req.size
  | .memWrite req _ _ => ramBytes req.pa req.size
  | _ => False

/-- At a RAM store or an exclusive RAM read, every event step of the hart is the served arm:
never MMIO (the footprint is RAM and an MMIO access is never empty), never a fetch or a plain
read (the read is exclusive). -/
theorem served_of_evStep {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    {v : InstructionEffect.ret o} (hm : ramAccess o)
    (h : evStep cpu o σ v σ') : served cpu o σ v σ' := by
  cases o with
  | memRead req =>
    obtain ⟨hx, hr⟩ := hm
    rcases h with ⟨hd, w, ds', hrd, -⟩ | ⟨-, hf, -⟩ | ⟨-, hp, -⟩ | h
    · exact absurd hd (not_devBytes_of_ramBytes hr (devRead_pos hrd))
    · rw [not_ifetch_of_excl hx] at hf
      exact absurd hf (by decide)
    · rw [not_plain_of_excl hx] at hp
      exact absurd hp (by decide)
    · exact h
  | memWrite req w a =>
    rcases h with ⟨hd, ds', hwr, -⟩ | h
    · exact absurd hd (not_devBytes_of_ramBytes hm (devWrite_pos hwr))
    · exact h
  | _ => exact hm.elim

/-- Harts progress, the served step.  At a pending access (`enabled`) that is not blocked,
every step of the thread at `i` is the served arm of `evStep` (the RAM write or the exclusive
read at the top): the hart moves on to the continuation at the served answer. -/
theorem served_of_unblocked (hen : enabled i c) (hnb : ¬ blocked i c) (hs : Step i c c') :
    ∃ e x o k v, c.1[i]? = some (.hart e x (.impure (.inl (.ok o)) k)) ∧
      c'.1[i]? = some (.hart e x (k v)) ∧ c'.2 = { c.2 with m := c'.2.m } ∧
      served x o c.2.m v c'.2.m := by
  obtain ⟨e, x, o, k, he, hl, hm⟩ := hen
  have hra : ramAccess o := by cases o <;> exact hm
  obtain ⟨m', he', ⟨-, hst, hg⟩ | ⟨hd, -⟩⟩ := step_hart hs he
  · rcases hst with ⟨v, rfl, hev⟩ | ⟨hb, -⟩
    · exact ⟨e, x, o, k, v, he, he', hg, served_of_evStep hra hev⟩
    · refine absurd ⟨e, x, o, k, he, hl, ?_⟩ hnb
      cases o with
      | memRead req => exact ⟨hm.1, hm.2, hb.2.1⟩
      | memWrite req w a => exact ⟨hm, hb.1⟩
      | _ => exact hb.elim
  · exact absurd hl hd

/-- Another hart's reservations are untouched by a hart's own reservation update. -/
theorem othersReserve_updCpu {resv : CPU → Option Resv} {cpu : CPU} {r : Option Resv}
    {pa : PAddr} {n : Nat} :
    othersReserve (updCpu resv cpu r) cpu pa n ↔ othersReserve resv cpu pa n := by
  unfold othersReserve
  constructor
  · rintro ⟨c, hc, r', h, hr⟩
    exact ⟨c, hc, r', by simpa [updCpu, hc] using h, hr⟩
  · rintro ⟨c, hc, r', h, hr⟩
    exact ⟨c, hc, r', by simpa [updCpu, hc] using h, hr⟩

/-- A blocked retry leaves the other harts' reservations, so whether the access is blocked. -/
theorem othersReserve_blockedStep {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    (hb : blockedStep cpu o σ σ') {pa : PAddr} {n : Nat} :
    othersReserve σ'.resv cpu pa n ↔ othersReserve σ.resv cpu pa n := by
  cases o with
  | memRead req =>
    obtain ⟨-, -, rfl⟩ := hb
    exact othersReserve_updCpu
  | memWrite req w a =>
    obtain ⟨-, rfl⟩ := hb
    split
    · exact Iff.rfl
    · rw [MState.resv_dropWindow]
      exact othersReserve_updCpu
  | _ => exact hb.elim

/-- Harts progress, the pending step.  At a blocked access, every step of the thread at `i`
is a blocked retry: it keeps the hart's expression, the generation and the power bit (so the
hart stays live), and the access stays blocked.  The last is exact, not a case: a retry changes
only the hart's own reservation (dropped at an exclusive read, released unless an LR's at a
plain store), and the block is another hart's, so the hart's own steps never unblock it; only
another thread's step can. -/
theorem pending_of_blocked (hb : blocked i c) (hs : Step i c c') :
    retry i c c' ∧ c'.1[i]? = c.1[i]? ∧ c'.2.gen = c.2.gen ∧ c'.2.pow = c.2.pow ∧
      blocked i c' := by
  obtain ⟨e, x, o, k, he, hl, hm⟩ := hb
  obtain ⟨m', he', ⟨-, hst, hg⟩ | ⟨hd, -⟩⟩ := step_hart hs he
  · have hgp : c'.2.gen = c.2.gen ∧ c'.2.pow = c.2.pow := by rw [hg]; exact ⟨rfl, rfl⟩
    rcases hst with ⟨v, rfl, hev⟩ | ⟨hbl, rfl⟩
    · -- an event step would be the served arm, which needs the footprint free
      have hen : ramAccess o := by
        cases o with
        | memRead req => exact ⟨hm.1, hm.2.1⟩
        | memWrite req w a => exact hm.1
        | _ => exact hm.elim
      have hsv := served_of_evStep hen hev
      cases o with
      | memRead req => exact absurd hm.2.2 hsv.2.2.1
      | memWrite req w a => exact absurd hm.2 hsv.2.1
      | _ => exact hm.elim
    · have hl' : threadLive c'.2 e := by
        obtain ⟨h1, h2⟩ := hl
        exact ⟨hgp.2 ▸ h1, hgp.1 ▸ h2⟩
      have hsame : c'.1[i]? = c.1[i]? := by rw [he', he]
      refine ⟨⟨hs, e, x, o, k, he, hl, hbl, hsame⟩, hsame, hgp.1, hgp.2,
        e, x, o, k, he', hl', ?_⟩
      have hr := fun {pa : PAddr} {n : Nat} => othersReserve_blockedStep (pa := pa) (n := n) hbl
      cases o with
      | memRead req => exact ⟨hm.1, hm.2.1, hr.2 hm.2.2⟩
      | memWrite req w a => exact ⟨hm.1, hr.2 hm.2⟩
      | _ => exact hm.elim
  · exact absurd hl hd

/-- At a blocked access the pending access survives the hart's own step. -/
theorem enabled_of_blocked_step (hb : blocked i c) (hs : Step i c c') : enabled i c' :=
  enabled_of_blocked (pending_of_blocked hb hs).2.2.2.2

/-- At a pending access, the hart's own step is a grant exactly when the access is not blocked.
An unblocked access is served (`served_of_unblocked`).  A blocked retry keeps the head event in
place (`pending_of_blocked`), and a served step never does: the continuation is below the node
(`Cycle.below_irrefl`). -/
theorem grant_iff_not_blocked (hen : enabled i c) (hs : Step i c c') :
    grant i c c' ↔ ¬ blocked i c := by
  constructor
  · rintro ⟨-, e, x, o, k, v, he, he'⟩ hb
    have hsame := (pending_of_blocked hb hs).2.1
    rw [he', he] at hsame
    have hkv : k v = .impure (.inl (.ok o)) k := (Expr.hart.inj (Option.some.inj hsame)).2.2
    have hbelow := Below.cont _ k v
    rw [hkv] at hbelow
    exact below_irrefl _ hbelow
  · intro hnb
    obtain ⟨e, x, o, k, v, he, he', -, -⟩ := served_of_unblocked hen hnb hs
    exact ⟨hs, e, x, o, k, v, he, he'⟩

variable {σ : Nat → Cfg}

/-- The action's hit is exactly a served access: the hart's step at a pending access that is not
blocked. -/
theorem hit_iff {n : Nat} :
    Action.hit (enabled i) (grant i) σ n ↔ Steps i σ n ∧ enabled i (σ n) ∧ ¬ blocked i (σ n) :=
  ⟨fun ⟨hen, hg⟩ => ⟨hg.1, hen, (grant_iff_not_blocked hen hg.1).1 hg⟩,
   fun ⟨hs, hen, hnb⟩ => ⟨hen, (grant_iff_not_blocked hen hs).2 hnb⟩⟩

/-- The hart's miss, a refused attempt of its own (`Thread.miss`), is exactly a blocked retry. -/
theorem miss_iff {n : Nat} :
    Thread.miss i (enabled i) (grant i) σ n ↔ Steps i σ n ∧ blocked i (σ n) := by
  rw [Thread.miss_iff]
  constructor
  · rintro ⟨hs, hen, hng⟩
    exact ⟨hs, Classical.byContradiction fun hnb => hng ((grant_iff_not_blocked hen hs).2 hnb)⟩
  · rintro ⟨hs, hb⟩
    have hen := enabled_of_blocked hb
    exact ⟨hs, hen, fun hg => (grant_iff_not_blocked hen hs).1 hg hb⟩

end Hart

/-! ## 3. Machine closure of the choice instances

Each instance's enabling condition admits a step of the thread for every outcome the action
distinguishes.  The memory reads need the footprint's bytes to have histories: `ramHist`, every
RAM byte has a nonempty history.  It is not part of `mmOk`, which says the converse (every
history sits at a RAM byte) and that every history is well formed; it holds of a booted memory
and every step keeps it (`ramHist_step`, section 4). -/

/-- Every RAM byte has a nonempty history. -/
def ramHist (m : FlatMem) : Prop :=
  ∀ a : PAddr, inRam a 1 → ∃ (e : HEnt) (H : Hist), m[a]? = some (e :: H)

section Mem

variable {σ : MState} {pa : PAddr} {n : Nat}

theorem hist_of_ramHist (hh : ramHist σ.mem) (hr : ramBytes pa n) {j : Nat} (hj : j < n) :
    ∃ (e : HEnt) (H : Hist), σ.mem[pa + BitVec.ofNat 64 j]? = some (e :: H) :=
  hh _ (hr j hj)

/-- Where the footprint's bytes have well-formed histories, every agent reads some value at the
top of the order (every entry is visible there, `histOk_top_visible`). -/
theorem exists_readBytes_top (hmm : mmOk σ) (hh : ramHist σ.mem) (hr : ramBytes pa n)
    (ag : Agent) : ∃ w : BitVec (8 * n), σ.mem.readBytes ag σ.top pa n w := by
  obtain ⟨w, hw⟩ := exists_bv_of_bytes n
    (fun j => (σ.mem.read ag σ.top (pa + BitVec.ofNat 64 j)).getD 0#8)
  refine ⟨w, fun j hj => ?_⟩
  obtain ⟨e, H, hget⟩ := hist_of_ramHist hh hr hj
  have hvis := histOk_top_visible σ.log (e :: H) e (hmm.1 _ _ hget) List.mem_cons_self ag
  have hrd : σ.mem.read ag σ.top (pa + BitVec.ofNat 64 j) = some e.v := by
    unfold FlatMem.read
    rw [hget, Option.bind_some, Hist.read_cons_visible _ _ _ _ hvis]
  rw [hw j hj, hrd]
  rfl

/-- Where the footprint's bytes have histories, they are at the top of the order as the bytes of
some value. -/
theorem exists_topBytes (hh : ramHist σ.mem) (hr : ramBytes pa n) :
    ∃ w : BitVec (8 * n), σ.mem.topBytes pa n w := by
  obtain ⟨w, hw⟩ := exists_bv_of_bytes n
    (fun j => ((σ.mem[pa + BitVec.ofNat 64 j]?).bind Hist.top).getD 0#8)
  refine ⟨w, fun j hj => ?_⟩
  obtain ⟨e, H, hget⟩ := hist_of_ramHist hh hr hj
  rw [hw j hj, hget]
  rfl

end Mem

/-! ### 3.0 A restarted cycle is not empty -/

namespace Cycle

/-- `riscvStep` is not `pure`: its first node is a model event, the read of `mip` that opens
`try_step`'s per-cycle refresh `update_mip` (the walk `swp_update_mip` of
`MachCSL/WpStepHooks.lean` starts there too), so a restarted cycle takes at least one step before
its next boundary.  The head is found by reduction, without unfolding the model by hand. -/
theorem riscvStep_impure (tick ew : Bool) :
    ∃ k, riscvStep tick ew = .impure (.inl (.ok (.regRead .mip none))) k :=
  ⟨_, rfl⟩

/-! The two restarts differ: the tickless one is not a ticking one at any `exit_wait`.  The
witness is a walk of the user tier's runner (`MachCSL.runRW`) that a parked hart's whole cycle
completes (`MachCSL.uw_tryStep`) and that refuses the clock tick, whose last event writes `mtime`
outside the walk's footprint. -/

/-- A footprint that reads every register but the two PLIC wires (the oracle answers those) and
writes every register but `cur_privilege` and `mtime`. -/
def tickFoot : UFoot where
  Dr r := decide (r ≠ .sig_meip ∧ r ≠ .sig_seip)
  Dw r := decide (r ≠ .cur_privilege ∧ r ≠ .mtime)
  Dany _ := true
  noPriv := rfl

theorem runRW_bind_none_of {X Y : Type} (D : UFoot) (m : SailM X) (f : X → SailM Y)
    (h : ∀ orc s y, runRW D orc s (f y) = none) (orc : UOrc) (s : UWSt) :
    runRW D orc s (m >>= f) = none := by
  rw [runRW_bind]
  cases runRW D orc s m with
  | none => rfl
  | some r => exact h _ _ _

/-- The walk refuses the clock tick: it ends by writing `mtime`. -/
theorem runRW_tick_clock (orc : UOrc) (s : UWSt) :
    runRW tickFoot orc s (Functions.tick_clock ()) = none := by
  have hjp : ∀ orc s, runRW tickFoot orc s (do
      let t ← readReg Register.mtime
      writeReg Register.mtime (BitVec.addInt t 1)) = none := by
    intro orc s
    refine runRW_bind_none_of _ _ _ (fun orc s y => ?_) orc s
    rfl
  unfold Functions.tick_clock Functions.clint_tick_clock
  refine runRW_bind_none_of _ _ _ (fun orc s p => ?_) orc s
  refine runRW_bind_none_of _ _ _ (fun orc s b => ?_) orc s
  cases b
  · exact hjp orc s
  · exact runRW_bind_none_of _ _ _ (fun orc s v =>
      runRW_bind_none_of _ _ _ (fun orc s u => hjp orc s) orc s) orc s

/-- The two restarts differ: a tickless restart is not a ticking one, at any `exit_wait`.  The
parked cycle's walk rests on one `bv_decide` certificate of the user tier (`ucIp_mask`), an axiom
of the family the audit allows. -/
theorem riscvStep_false_ne_true (ew ew' : Bool) : riscvStep false ew ≠ riscvStep true ew' := by
  intro heq
  obtain ⟨f0⟩ : Nonempty RegFile := ⟨fun r => by cases r <;> exact default⟩
  let rs : RegFile :=
    ((((f0.set .misa 0x800000000014112D#64).set .cur_privilege .User).set .mstatus 0#64).set
      .hart_state (.HART_WAITING (.WAIT_WRS_STO, default))).set .written_trigger_index none
  let s : UWSt := ⟨fun _ => none, rs, fun _ => none, false⟩
  have hD : UcFoot tickFoot := by constructor <;> rfl
  have hW : UwFoot tickFoot := by constructor <;> rfl
  have hm : UcMisa tickFoot s := ⟨rfl, rfl⟩
  have htw : Functions._get_Mstatus_TW (s.file .mstatus) = 0#1 := by
    show Functions._get_Mstatus_TW 0#64 = 0#1
    decide
  obtain ⟨meip, seip, orc', h⟩ := uw_tryStep hD hW (UOrc.dflt f0) s .WAIT_WRS_STO default ew hm
    rfl htw (fun h => by cases h) rfl rfl
  have h1 : runRW tickFoot (UOrc.dflt f0) s (riscvStep false ew) =
      some ((), (uwLand ew .WAIT_WRS_STO s meip seip).2, orc') := by
    unfold riscvStep
    rw [runRW_bind_some _ _ _ _ _ _ _ _ h]
    rfl
  have h2 : runRW tickFoot (UOrc.dflt f0) s (riscvStep true ew') = none := by
    unfold riscvStep
    exact runRW_bind_none_of _ _ _ (fun orc s _ => runRW_tick_clock orc s) _ _
  rw [heq, h2] at h1
  exact absurd h1 (by simp)

end Cycle

/-! ### 3.1 The tick: both restarts exist at a live boundary -/

namespace Tick

open Cycle

variable {i : Nat} {c : Cfg}

/-- At a live boundary the hart restarts its cycle with any tick and any `exit_wait`. -/
theorem exists_restart (h : enabled i c) (tick ew : Bool) :
    ∃ c', Step i c c' ∧ ∃ e x, c.1[i]? = some (.hart e x (.pure ())) ∧
      c'.1[i]? = some (.hart e x (riscvStep tick ew)) := by
  obtain ⟨e, x, he, hl⟩ := h
  exact ⟨_, step_of_primStep he (primStep_hart_live (σ' := c.2.m.dropWindow x) hl
      ⟨tick, ew, rfl, rfl⟩), e, x, he, getElem?_set_append he⟩

/-- At a live boundary a ticking restart, a grant, exists. -/
theorem exists_grant (h : enabled i c) : ∃ c', Step i c c' ∧ grant i c c' := by
  obtain ⟨c', hs, e, x, he, he'⟩ := exists_restart h true false
  exact ⟨c', hs, hs, e, x, false, he, he'⟩

/-- At a live boundary a tickless restart, which is not a grant, exists
(`riscvStep_false_ne_true`). -/
theorem exists_not_grant (h : enabled i c) : ∃ c', Step i c c' ∧ ¬ grant i c c' := by
  obtain ⟨c', hs, e, x, he, he'⟩ := exists_restart h false false
  refine ⟨c', hs, ?_⟩
  rintro ⟨-, e', x', ew', -, he2⟩
  rw [he'] at he2
  exact riscvStep_false_ne_true false ew' (Expr.hart.inj (Option.some.inj he2)).2.2

end Tick

/-! ### 3.2 A device's `choose` arm: every answer exists -/

namespace Arm

open Cycle

variable {i : Nat} {c : Cfg} {d : DevId}

/-- At a live root at a `choose` node, the root continues with any answer. -/
theorem exists_answer {k : Nat → DevProg d} (h : enabled i d (.op .choose k) c) (v : Nat) :
    ∃ c', Step i c c' ∧ ∃ e, c.1[i]? = some (.dev e d rootTask (.op .choose k)) ∧
      c'.1[i]? = (at? (.op .choose k) v).map (.dev e d rootTask) := by
  obtain ⟨e, he, hl⟩ := h
  have hd : devStep e d rootTask (.op .choose k) c.2.m [] (k v) c.2.m [] :=
    Or.inl ⟨v, rfl, rfl, rfl, rfl⟩
  exact ⟨_, step_of_primStep he (primStep_dev_live hl hd), e, he, getElem?_set_append he⟩

/-- At a live root at a `choose` node, the grant of the class of any answer exists: the class
`b` modulo `m` is granted by the answer `b` when `b < m` (or `m = 0`). -/
theorem exists_grant {k : Nat → DevProg d} (h : enabled i d (.op .choose k) c) (m v : Nat) :
    ∃ c', Step i c c' ∧ grant i d (.op .choose k) m (v % m) c c' := by
  obtain ⟨c', hs, e, he, he'⟩ := exists_answer h v
  exact ⟨c', hs, hs, e, v, rfl, he, he'⟩

end Arm

/-! ### 3.3 The visibility of a store: a load at the top exists -/

namespace Fresh

open Cycle

variable {i : Nat} {c : Cfg} {a : PAddr}

/-- At a live hart's plain RAM load whose footprint's bytes have well-formed histories, a step
reading at the top of the order exists.  It takes the load, and the hart moves on to the
continuation at the value read.  After it the hart's coherence floor of every byte of the
footprint is the top, so the load has seen every store there is: the grant holds for every
store `t` up to the top. -/
theorem exists_grant (h : atLoad i a c) (hmm : mmOk c.2.m) (hh : ramHist c.2.m.mem) :
    ∃ c', Step i c c' ∧ ∀ t, t ≤ c.2.m.top → grant i t a c c' := by
  obtain ⟨e, x, req, k, he, hl, hp, hr, j, hj, rfl⟩ := h
  obtain ⟨w, hw⟩ := exists_readBytes_top hmm hh hr (hartAgent x)
  have hev : evStep x (.memRead req) c.2.m (.ok (w, 0#req.numTag))
      (c.2.m.afterLoad x req.pa req.size c.2.m.top) :=
    Or.inr (Or.inr (Or.inl ⟨hr, hp, c.2.m.top, w, (hmm.2.1 x).1, Nat.le_refl _,
      fun j' _ => ((hmm.2.1 x).2.2).2 _, hw, rfl, rfl⟩))
  have hs := step_of_primStep he (primStep_hart_live hl (Or.inl ⟨_, rfl, hev⟩))
  refine ⟨_, hs, fun t ht =>
    ⟨hs, e, x, req, k, .ok (w, 0#req.numTag), he, getElem?_set_append he, ?_⟩⟩
  show t ≤ (updCpu c.2.m.hr x ((c.2.m.hr x).afterLoad req.pa req.size c.2.m.top) x).coh _
  simp only [updCpu, ite_true, HRead.afterLoad]
  rw [ite_eq_left ⟨j, hj, rfl⟩]
  exact ht

/-- Every own step of a live hart at a plain RAM load takes the load: a plain load is never
blocked, since blocking needs an exclusive access, so the hart moves on to the continuation. -/
theorem takes_load {c' : Cfg} (h : atLoad i a c) (hs : Step i c c') :
    ∃ e x req k v, c.1[i]? = some (.hart e x (.impure (.inl (.ok (.memRead req))) k)) ∧
      c'.1[i]? = some (.hart e x (k v)) := by
  obtain ⟨e, x, req, k, he, hl, hp, -, -⟩ := h
  obtain ⟨m', he', ⟨-, hst, -⟩ | ⟨hd, -⟩⟩ := step_hart hs he
  · rcases hst with ⟨v, rfl, -⟩ | ⟨hb, -⟩
    · exact ⟨e, x, req, k, v, he, he'⟩
    · have hx : akExcl req.accessKind = true := hb.1
      rw [Hart.not_plain_of_excl hx] at hp
      exact absurd hp (by decide)
  · exact absurd hl hd

/-- Under the enabling condition and the hart's step, the grant is the post-state fact alone: the
hart's coherence floor of `a` is at or past `t` afterwards.  This was the grant's statement before
2026-11-06; the trusted hypothesis `Fresh.SF` means the same under both. -/
theorem grant_iff_coh {c' : Cfg} {t : Nat} (h : enabled i t a c) (hs : Step i c c') :
    grant i t a c c' ↔ ∃ e x m, c.1[i]? = some (.hart e x m) ∧ t ≤ (c'.2.m.hr x).coh a := by
  constructor
  · rintro ⟨-, e, x, req, k, v, he, -, ht⟩
    exact ⟨e, x, _, he, ht⟩
  · rintro ⟨e, x, m, he, ht⟩
    obtain ⟨e2, x2, req, k, v, he2, he2'⟩ := takes_load h.1 hs
    rw [he] at he2
    cases he2
    exact ⟨hs, e, x, req, k, v, he, he2', ht⟩

end Fresh

/-! ### 3.4 Harts progress: a served step exists at an unblocked access -/

namespace Hart

open Cycle

variable {i : Nat} {c : Cfg}

/-- At a pending access that is not blocked, a served step exists, a grant (the exclusive read
needs the footprint's bytes to have histories, for the value at the top).  The step is built from
the served arm of `evStep`; that it is a grant is `grant_iff_not_blocked`. -/
theorem exists_served (hen : enabled i c) (hnb : ¬ blocked i c) (hh : ramHist c.2.m.mem) :
    ∃ c', Step i c c' ∧ grant i c c' := by
  have hstep : ∃ c', Step i c c' := by
    obtain ⟨e, x, o, k, he, hl, hm⟩ := hen
    cases o with
    | memRead req =>
      obtain ⟨hx, hr⟩ := hm
      obtain ⟨w, hw⟩ := exists_topBytes hh hr
      have hev : evStep x (.memRead req) c.2.m (.ok (w, 0#req.numTag))
          (c.2.m.afterExcl x req.pa req.size w (akAcq req.accessKind) (kindOf req.accessKind)) :=
        Or.inr (Or.inr (Or.inr
          ⟨hr, hx, fun ho => hnb ⟨e, x, _, k, he, hl, hx, hr, ho⟩, w, hw, rfl, rfl⟩))
      exact ⟨_, step_of_primStep he (primStep_hart_live hl (Or.inl ⟨_, rfl, hev⟩))⟩
    | memWrite req w a =>
      have hev : evStep x (.memWrite req w a) c.2.m (.ok ())
          (c.2.m.store x req.pa req.size w (akExcl req.accessKind)) :=
        Or.inr ⟨hm, fun ho => hnb ⟨e, x, _, k, he, hl, hm, ho⟩, rfl, rfl⟩
      exact ⟨_, step_of_primStep he (primStep_hart_live hl (Or.inl ⟨_, rfl, hev⟩))⟩
    | _ => exact hm.elim
  obtain ⟨c', hs⟩ := hstep
  exact ⟨c', hs, (grant_iff_not_blocked hen hs).2 hnb⟩

end Hart

/-! ### 3.5 A device's DMA write: the task's miss is a blocked retry

A live device task's step takes one of two arms of `devStep`.  The answer arm moves the task on to
the continuation; the blocked arm (`devBlocked`) keeps its program.  At a DMA write whose guard
answers a faithful move into RAM, the blocked arm is exactly a blocking reservation over the
footprint (`anyReserve`), and the answer arm needs there to be none.  So the task's step is a grant
exactly when the write is not blocked, as for a hart's access in section 2. -/

namespace Dma

open Cycle

variable {i : Nat} {c c' : Cfg} {d : DevId} {tid : TaskId}

/-- At a pending DMA write, the task's own step is a grant exactly when the write is not blocked.
An unblocked write is served: the no-op arm needs the guard to fail or the footprint outside RAM.
A blocked write takes the blocked arm, which keeps the program, and a served step never does: the
continuation is below the node (`Cycle.DevM.below_irrefl`). -/
theorem grant_iff_not_blocked (hen : enabled i d tid c) (hs : Step i c c') :
    grant i d tid c c' ↔ ¬ blocked i d tid c := by
  obtain ⟨e, g, pa, n, w, k, he, hl, ⟨s', hg, hok⟩, hr⟩ := hen
  have hbl : blocked i d tid c ↔ anyReserve c.2.m.resv pa n := by
    constructor
    · rintro ⟨e2, g2, pa2, n2, w2, k2, he2, -, -, -, hany⟩
      rw [he] at he2
      cases he2
      exact hany
    · intro hany
      exact ⟨e, g, pa, n, w, k, he, hl, ⟨s', hg, hok⟩, hr, hany⟩
  rw [hbl]
  obtain ⟨ex, obs, e', efs, he1, hp, hc'⟩ := id hs
  rw [he] at he1
  obtain rfl := Option.some.inj he1
  have hc'i : c'.1[i]? = some e' := by
    rw [hc']
    exact getElem?_set_append he
  rcases hp with ⟨-, m', σ', rfl, hd, -⟩ | ⟨hnl, -⟩
  · simp only [devStep] at hd
    rcases hd with ⟨v, rfl, -, -, ⟨-, -, -, -, hnr, -⟩ | ⟨hno, -⟩⟩ | ⟨hb, rfl, -⟩
    · exact ⟨fun _ => hnr, fun _ => ⟨hs, e, g, pa, n, w, k, v, he, hc'i⟩⟩
    · rcases hno with hno | hno
      · rw [hg] at hno
        cases hno
      · exact absurd hr hno
    · obtain ⟨-, hany | ⟨-, s'', hg', hnok⟩⟩ := hb
      · refine ⟨fun hgr => absurd hgr ?_, fun h => absurd hany h⟩
        rintro ⟨-, e2, g2, pa2, n2, w2, k2, v, he2, he2'⟩
        rw [he] at he2
        cases he2
        rw [hc'i] at he2'
        have hkv : k v = .op (.dmaWrite g pa n w) k :=
          (eq_of_heq (Expr.dev.inj (Option.some.inj he2')).2.2.2).symm
        have hbelow := DevM.Below.cont (.dmaWrite g pa n w) k v
        rw [hkv] at hbelow
        exact absurd hbelow (DevM.below_irrefl _)
      · rw [hg] at hg'
        cases hg'
        exact absurd hok hnok
  · exact absurd hl hnl

variable {σ : Nat → Cfg}

/-- The task's miss, a refused attempt of its own (`Thread.miss`), is exactly a blocked retry. -/
theorem miss_iff {n : Nat} :
    Thread.miss i (enabled i d tid) (grant i d tid) σ n ↔ Steps i σ n ∧ blocked i d tid (σ n) := by
  rw [Thread.miss_iff]
  constructor
  · rintro ⟨hs, hen, hng⟩
    exact ⟨hs, Classical.byContradiction fun hnb => hng ((grant_iff_not_blocked hen hs).2 hnb)⟩
  · rintro ⟨hs, hb⟩
    have hen := enabled_of_blocked hb
    exact ⟨hs, hen, fun hg => (grant_iff_not_blocked hen hs).1 hg hb⟩

/-- The action's hit is exactly a served write: the task's step at a pending DMA write that is
not blocked. -/
theorem hit_iff {n : Nat} :
    Action.hit (enabled i d tid) (grant i d tid) σ n ↔
      Steps i σ n ∧ enabled i d tid (σ n) ∧ ¬ blocked i d tid (σ n) :=
  ⟨fun ⟨hen, hg⟩ => ⟨hg.1, hen, (grant_iff_not_blocked hen hg.1).1 hg⟩,
   fun ⟨hs, hen, hnb⟩ => ⟨hen, (grant_iff_not_blocked hen hs).2 hnb⟩⟩

end Dma

/-! ## 4. Every RAM byte keeps a history (`ramHist`)

A booted memory has a history at every RAM byte (the boot image covers RAM), and a step either
leaves the histories or pushes a store onto some (a hart's RAM store, a DMA write), so `ramHist`
holds along every run from a booted state, which is what the memory reads of section 3 need. -/

section RamHist

variable {j n m : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- A step's effect on the byte histories: none, or a store pushed onto the footprint. -/
def memMove (M M' : FlatMem) : Prop :=
  M' = M ∨ ∃ pa k w t ag, M' = M.writeBytes pa k w t ag

theorem ramHist_push {M : FlatMem} (h : ramHist M) (b : PAddr) (en : HEnt) :
    ramHist (M.push b en) := by
  intro a ha
  by_cases hab : a = b
  · subst hab
    exact ⟨en, _, FlatMem.push_get?_eq M a en⟩
  · rw [FlatMem.push_get?_ne M b a en hab]
    exact h a ha

theorem ramHist_writeBytes {M : FlatMem} (h : ramHist M) (pa : PAddr) (k : Nat)
    (w : BitVec (8 * k)) (t : Nat) (ag : Agent) : ramHist (M.writeBytes pa k w t ag) := by
  unfold FlatMem.writeBytes
  have key : ∀ (l : List Nat) (M : FlatMem), ramHist M →
      ramHist (l.foldl (fun (M : FlatMem) j => M.push (pa + BitVec.ofNat 64 j) ⟨t, ag, nthByte w j⟩) M) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons j l ih => exact fun M h => ih _ (ramHist_push h _ _)
  exact key _ M h

theorem ramHist_of_memMove {M M' : FlatMem} (h : ramHist M) (hm : memMove M M') : ramHist M' := by
  rcases hm with rfl | ⟨pa, k, w, t, ag, rfl⟩
  · exact h
  · exact ramHist_writeBytes h pa k w t ag

/-- The boot image's memory has a history at every RAM byte. -/
theorem ramHist_boot : ramHist (imgFlat bootImage) := by
  intro a ha
  rw [imgFlat_get?, ite_eq_left ha, bootImage_get?, ite_eq_left ha]
  exact ⟨_, [], rfl⟩

theorem evStep_mem {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    {v : InstructionEffect.ret o} (h : evStep cpu o σ v σ') : memMove σ.mem σ'.mem := by
  cases o with
  | memRead req =>
    rcases h with ⟨-, w, ds', -, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
      ⟨-, -, tvn, w, -, -, -, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩
    all_goals exact Or.inl rfl
  | memWrite req w a =>
    rcases h with ⟨-, ds', -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, _, _, _, rfl⟩
  | _ =>
    first
    | (obtain rfl := h; exact Or.inl rfl)
    | (obtain ⟨-, rfl⟩ := h; exact Or.inl rfl)

theorem blockedStep_mem {cpu : CPU} {o : InstructionEffect} {σ σ' : MState}
    (h : blockedStep cpu o σ σ') : memMove σ.mem σ'.mem := by
  cases o with
  | memRead req =>
    obtain ⟨-, -, rfl⟩ := h
    exact Or.inl rfl
  | memWrite req w a =>
    obtain ⟨-, rfl⟩ := h
    split
    · exact Or.inl rfl
    · exact Or.inl (MState.dropWindow_mem _ _)
  | _ => exact h.elim

theorem hartStep_mem {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') : memMove σ.mem σ'.mem := by
  unfold hartStep at h
  split at h
  · obtain ⟨-, -, -, rfl⟩ := h
    exact Or.inl (MState.dropWindow_mem _ _)
  · exact h.elim
  · rcases h with ⟨v, -, hev⟩ | ⟨hb, -⟩
    · exact evStep_mem hev
    · exact blockedStep_mem hb
  · obtain ⟨-, -, rfl⟩ := h
    exact Or.inl rfl

theorem devOpStep_mem {gen : Nat} {d : DevId} {o : DevOp (DevSt d) (DevTask d)} {σ σ' : MState}
    {v : o.ret} {obs : List Obs} {efs : List Expr} (h : devOpStep gen d o σ v σ' obs efs) :
    memMove σ.mem σ'.mem := by
  cases o with
  | step g =>
    obtain ⟨s', os, -, -, rfl, -, -⟩ := h
    exact Or.inl rfl
  | get =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Or.inl rfl
  | choose =>
    obtain ⟨rfl, -, -⟩ := h
    exact Or.inl rfl
  | dmaRead pa n =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Or.inl rfl
  | dmaWrite g pa n w =>
    obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · exact Or.inr ⟨_, _, _, _, _, rfl⟩
    · exact Or.inl rfl
  | sample src =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Or.inl rfl
  | setPin cpu mmode b =>
    obtain ⟨-, -, rfl⟩ := h
    cases mmode <;> exact Or.inl rfl
  | fork t =>
    obtain ⟨-, -, rfl, -⟩ := h
    exact Or.inl rfl
  | join tid =>
    obtain ⟨-, rfl, -, -⟩ := h
    exact Or.inl rfl

theorem devStep_mem {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) :
    memMove σ.mem σ'.mem := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact Or.inl rfl
    · split <;> exact Or.inl rfl
  · rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · exact devOpStep_mem hop
    · exact Or.inl rfl

/-- Every step keeps a history at every RAM byte: a power-on reloads the boot image, every other
step leaves the histories or pushes onto them. -/
theorem ramHist_step (hs : Step j c c') (h : ramHist c.2.m.mem) : ramHist c'.2.m.mem := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, -, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · exact ramHist_of_memMove h (hartStep_mem hst)
    · exact h
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact ramHist_of_memMove h (devStep_mem hst)
    · exact h
  | power =>
    rcases hp with ⟨-, ⟨-, -, -, rfl⟩ | ⟨-, -, -, hb⟩⟩
    · exact h
    · have hb' : bootShape g g' := hb
      show ramHist g'.m.mem
      rw [hb'.2.2.1.1]
      exact ramHist_boot

/-- Along a run of the pool, every RAM byte keeps a history. -/
theorem ramHist_run (hrun : PoolRun σ) (h : ramHist (σ n).2.m.mem) (hnm : n ≤ m) :
    ramHist (σ m).2.m.mem := by
  induction m with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnm
    subst h0
    exact h
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with hlt | heq
    · obtain ⟨j, hs⟩ := hrun m
      exact ramHist_step hs (ih (Nat.le_of_lt_succ hlt))
    · subst heq
      exact h

end RamHist

/-! ## 5. Harts progress in response form (B5)

The statements of the plan are per era: every component is `□(T → ◇(B ∨ off))`.  A power cut
while an access is pending ends the hart's generation, and the hart never attempts again, so
the strong fairness of the action holds vacuously from there while "the access is eventually
served" fails.  The exact correspondence is therefore with the response form relativised to
the era (`ProgressOrCut`); the unrelativised Progress Axiom follows on a run where the thread,
once live, stays live. -/

namespace Era

variable {i j n m k : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The era rank of a global state: twice the generation, plus one while the power is on.  It
never goes down, and a generation `e` is live exactly at rank `2 e + 1`. -/
def rank (g : GState) : Nat := 2 * g.gen + (if g.pow then 1 else 0)

theorem threadLive_iff_rank (g : GState) (e : Nat) : threadLive g e ↔ rank g = 2 * e + 1 := by
  unfold threadLive rank
  cases g.pow <;> simp <;> omega

/-- Every step keeps or raises the era rank: a cut raises it by one (generation up, power off),
a power-on by one (power on), every other step keeps the generation and the power bit. -/
theorem rank_mono (hs : Step j c c') : rank c.2 ≤ rank c'.2 := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ <;> exact Nat.le_refl _
  | dev gen d tid m =>
    rcases hp with ⟨-, m', σ', -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> exact Nat.le_refl _
  | power =>
    rcases hp with ⟨-, ⟨hon, -, -, rfl⟩ | ⟨hoff, -, -, hb⟩⟩
    · have hon' : g.pow = true := hon
      show rank g ≤ rank { g with gen := g.gen + 1, pow := false }
      simp only [rank, hon', ite_true, Bool.false_eq_true, ite_false]
      omega
    · have hoff' : g.pow = false := hoff
      have hb' : bootShape g g' := hb
      show rank g ≤ rank g'
      simp only [rank, hoff', hb'.1, hb'.2.1, ite_true, Bool.false_eq_true, ite_false]
      omega

theorem rank_mono_run (hrun : PoolRun σ) (hnm : n ≤ m) : rank (σ n).2 ≤ rank (σ m).2 := by
  induction m with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnm
    subst h0
    exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with hlt | heq
    · obtain ⟨j, hs⟩ := hrun m
      exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (rank_mono hs)
    · subst heq
      exact Nat.le_refl _

theorem liveAt_of_genAt {e : Nat} (hg : genAt i c = some e) (hl : threadLive c.2 e) :
    liveAt i c := by
  unfold genAt at hg
  cases hc : c.1[i]? with
  | none => simp [hc] at hg
  | some ex =>
    rw [hc] at hg
    cases ex with
    | hart gen cpu m =>
      simp only [Option.bind_some, Expr.gen?, Option.some.injEq] at hg
      subst hg
      exact ⟨gen, Or.inl ⟨cpu, m, hc⟩, hl⟩
    | dev gen d tid m =>
      simp only [Option.bind_some, Expr.gen?, Option.some.injEq] at hg
      subst hg
      exact ⟨gen, Or.inr ⟨d, tid, m, hc⟩, hl⟩
    | power => simp [Expr.gen?] at hg

/-- Liveness is convex along a run: a thread live at `n` and at `k ≥ n` is live at every
position in between (its era rank cannot leave `2 e + 1` and come back). -/
theorem liveAt_between (hrun : PoolRun σ) (hn : liveAt i (σ n)) (hk : liveAt i (σ k))
    (hnm : n ≤ m) (hmk : m ≤ k) : liveAt i (σ m) := by
  obtain ⟨e, hg, hp, hgen⟩ := liveAt_gen hn
  obtain ⟨e', hg', hp', hgen'⟩ := liveAt_gen hk
  have hgk := genAt_run hrun (Nat.le_trans hnm hmk) hg
  rw [hg'] at hgk
  have hee : e' = e := Option.some.inj hgk
  have r1 := (threadLive_iff_rank _ e).1 ⟨hp, hgen⟩
  have r2 := (threadLive_iff_rank _ e').1 ⟨hp', hgen'⟩
  have h1 := rank_mono_run hrun hnm
  have h2 := rank_mono_run hrun hmk
  exact liveAt_of_genAt (genAt_run hrun hnm hg) ((threadLive_iff_rank _ e).2 (by omega))

/-- A thread live at `n` and dead at `m ≥ n` is dead at every position from `m` on. -/
theorem dead_forever (hrun : PoolRun σ) (hn : liveAt i (σ n)) (hnm : n ≤ m)
    (hm : ¬ liveAt i (σ m)) (hmk : m ≤ k) : ¬ liveAt i (σ k) :=
  fun hk => hm (liveAt_between hrun hn hk hnm hmk)

/-- A step that keeps the thread at `i` live is not a cut: if it is the power thread's, the
thread at `i` was not live before it. -/
theorem not_power_of_live (hs : Step j c c') (hl : liveAt i c) (hl' : liveAt i c') :
    c.1[j]? ≠ some .power := by
  intro hpj
  have h1 := power_kills hs hpj hl
  obtain ⟨e, hg, -, hgen⟩ := liveAt_gen hl
  obtain ⟨e', hg', -, hgen'⟩ := liveAt_gen hl'
  rw [genAt_step hs hg] at hg'
  obtain rfl := Option.some.inj hg'
  omega

end Era

namespace Hart

open Cycle
open Era (liveAt)

variable {i n : Nat} {σ : Nat → Cfg}

/-- The Progress Axiom relativised to the era (`□(T → ◇(B ∨ off))`): every pending access is
eventually served, or the hart is eventually dead (its generation ended by a power cut). -/
def ProgressOrCut (i : Nat) (σ : Nat → Cfg) : Prop :=
  ∀ n, enabled i (σ n) → ∃ m ≥ n, Action.hit (enabled i) (grant i) σ m ∨ ¬ liveAt i (σ m)

/-- A pending access stays pending until it is served, as long as the hart is live: another
thread's step is not a cut (the hart stays live) and keeps the access (`stable`); the hart's
own unserved step is a blocked retry, which keeps it blocked (`pending_of_blocked`). -/
theorem enabled_until_hit (hrun : PoolRun σ) (hen : enabled i (σ n)) {k : Nat} (hnk : n ≤ k)
    (hno : ∀ m, n ≤ m → m < k → ¬ Action.hit (enabled i) (grant i) σ m)
    (hlive : ∀ m, n ≤ m → m ≤ k → liveAt i (σ m)) : enabled i (σ k) := by
  induction k with
  | zero =>
    have h0 : n = 0 := Nat.le_zero.1 hnk
    subst h0
    exact hen
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hnk with hlt | heq
    · have hnk' := Nat.le_of_lt_succ hlt
      have hk := ih hnk' (fun m h1 h2 => hno m h1 (Nat.lt_succ_of_lt h2))
        (fun m h1 h2 => hlive m h1 (Nat.le_succ_of_le h2))
      obtain ⟨j, hs⟩ := hrun k
      by_cases hji : j = i
      · subst hji
        have hb : blocked j (σ k) := Classical.byContradiction fun hnb =>
          hno k hnk' (Nat.lt_succ_self k) (hit_iff.2 ⟨hs, hk, hnb⟩)
        exact enabled_of_blocked_step hb hs
      · have hnp : ∀ e, (σ k).1[j]? = some e → e ≠ .power := by
          rintro e he rfl
          exact Era.not_power_of_live hs (hlive k hnk' (Nat.le_succ k))
            (hlive (k + 1) hnk (Nat.le_refl _)) he
        exact stable hji hs hnp hk
    · subst heq
      exact hen

/-- Strong fairness gives the era-relativised response.  On any run of the pool: if a
pending access were never served while the hart stays live, it would stay pending for ever, and
strong fairness would serve it.  No fair-scheduling hypothesis is needed: the hits strong
fairness provides are the thread's own steps, since a grant contains the step (`hit_iff`). -/
theorem progressOrCut_of_sf (hrun : PoolRun σ) (h : SF i σ) : ProgressOrCut i σ := by
  intro n hen
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ m, n ≤ m → ¬ Action.hit (enabled i) (grant i) σ m ∧ liveAt i (σ m) :=
    fun m hm => ⟨fun hh => hno ⟨m, hm, Or.inl hh⟩,
      Classical.byContradiction fun hd => hno ⟨m, hm, Or.inr hd⟩⟩
  have hall : ∀ k, n ≤ k → enabled i (σ k) := fun k hk =>
    enabled_until_hit hrun hen hk (fun m h1 _ => (hno' m h1).1) (fun m h1 _ => (hno' m h1).2)
  obtain ⟨m, hm, hhit⟩ :=
    h (fun N => ⟨N + n, Nat.le_add_right N n, hall _ (Nat.le_add_left n N)⟩) n
  exact (hno' m hm).1 hhit

/-- The era-relativised response gives strong fairness back, on any run of the pool: a hart
that is pending infinitely often is live infinitely often, so it never dies (liveness is
convex), and each pending position is followed by a hit. -/
theorem sf_of_progressOrCut (hrun : PoolRun σ) (h : ProgressOrCut i σ) : SF i σ := by
  intro hA N
  obtain ⟨n, hn, hen⟩ := hA N
  obtain ⟨m, hm, hhit | hd⟩ := h n hen
  · exact ⟨m, Nat.le_trans hn hm, hhit⟩
  · obtain ⟨n', hn', hen'⟩ := hA m
    exact absurd (Era.liveAt_between hrun (live hen) (live hen') hm hn') hd

/-- Strong fairness of harts progress is the era-relativised Progress Axiom, on every run of
the pool. -/
theorem sf_iff_progressOrCut (hrun : PoolRun σ) : SF i σ ↔ ProgressOrCut i σ :=
  ⟨progressOrCut_of_sf hrun, sf_of_progressOrCut hrun⟩

/-- The cut, first half: once the hart has died after being pending, strong fairness holds
vacuously (it is never pending again). -/
theorem sf_of_dead {m : Nat} (hrun : PoolRun σ) (hen : enabled i (σ n)) (hnm : n ≤ m)
    (hd : ¬ liveAt i (σ m)) : SF i σ := by
  intro hA
  obtain ⟨k, hk, hAk⟩ := hA m
  exact absurd (live hAk) (Era.dead_forever hrun (live hen) hnm hd hk)

/-- The cut, second half: a pending access cut off by the hart's death before it is served is
never served, so the unrelativised Progress Axiom fails on that run. -/
theorem not_progressAxiom_of_cut {m : Nat} (hrun : PoolRun σ) (hen : enabled i (σ n))
    (hnm : n ≤ m) (hno : ∀ k, n ≤ k → k < m → ¬ Action.hit (enabled i) (grant i) σ k)
    (hd : ¬ liveAt i (σ m)) : ¬ ProgressAxiom i σ := by
  intro hp
  obtain ⟨k, hk, hhit⟩ := hp n hen
  rcases Nat.lt_or_ge k m with hkm | hkm
  · exact hno k hk hkm hhit
  · exact Era.dead_forever hrun (live hen) hnm hd hkm (live hhit.1)

/-- On a run where the thread at `i`, once live, stays live (no cut ends its generation), strong
fairness gives the Progress Axiom in response form. -/
theorem response_of_sf (hrun : PoolRun σ)
    (hstay : ∀ k, liveAt i (σ k) → liveAt i (σ (k + 1))) (h : SF i σ) : ProgressAxiom i σ := by
  intro n hen
  obtain ⟨m, hm, hhit | hd⟩ := progressOrCut_of_sf hrun h n hen
  · exact ⟨m, hm, hhit⟩
  · refine absurd ?_ hd
    have key : ∀ d, liveAt i (σ (n + d)) := by
      intro d
      induction d with
      | zero => exact live hen
      | succ d ih => exact hstay _ ih
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact key d

/-- B5.  On a run of the pool where the thread at `i`, once live, stays live, strong
fairness of harts progress is the Progress Axiom in response form.  Without the hypothesis the
two differ exactly by the power cut (`sf_iff_progressOrCut`). -/
theorem sf_iff_response (hrun : PoolRun σ)
    (hstay : ∀ k, liveAt i (σ k) → liveAt i (σ (k + 1))) : SF i σ ↔ ProgressAxiom i σ :=
  ⟨response_of_sf hrun hstay, Action.sf_of_response⟩

end Hart

end Fairness

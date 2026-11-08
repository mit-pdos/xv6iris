import MachCSL.Liveness.Gates

/-! # The disk's protocol facts

Milestone C3 of lane `xv6-liveness-spec` (plan and brief in `local-plan/xv6-liveness-spec/`,
outside the repository).  The owner decided on 2026-11-05 that a task waiting at a disk gate waits
on the obligation of the task that closed it.  This file proves the facts about the disk's programs
that this mechanism rests on, along runs of the pool from the boot configuration (the power thread
alone): every device has at most one live root; every disk program ends within a fixed number of
its own steps; a head has at most one live serving task, and only while the head is in flight;
with at most two requests in flight, a serving task has at most one competitor.  It then turns these
facts into the closer-excluding hypotheses of the gate theorems of `Gates.lean`, so a caller
composes them with those theorems unchanged.  Two facts about the kernel are hypotheses here, to be
discharged by the kernel proof: the bound on requests in flight (`BoundedInflight`) and the MMIO
discipline while a request is in flight (taken inline as
`∀ n, (disk (σ n)).inflight ≠ [] → kernelStores (σ n)`, from which `NoBusyReset`, `NoWceOff` and
`NoConfigWrite` follow).  The file keeps the naming policy of `Fairness.lean`.

**Map of the file.**

1. The pool's bookkeeping.  Where a thread after a step comes from (`get?_step`, `dev_origin`,
   later `dev_step_at`); no thread is of a future generation (`genOk`); a device's task counter is
   positive while it has a live task (`nextOk`), so a fork never hands out the root's id
   (`fork_ne_root`); one live root per device (`oneRoot`).
2. Bounded paths.  `Bounded m k`: every path of `m` ends within `k` primitives.  The service of a
   request is bounded by `16` (`bounded_serve`; the fetch by `5`, `bounded_fetch`), an arm of the
   root loop by `7` (`bounded_arm`).  Along a run a task's bound goes down by one at each of its own
   moves (`boundedAt_step`, `bounded_run`), so it reaches its end within its bound (`pure_within`,
   `serve_within`, `arm_within`).  A move is a change of the thread at its position (`ownMoves`):
   an answered primitive always is one (`moved_of_answer`), a blocked retry or a dead task's
   self-loop never is.
3. The kernel's facts, stated: `BoundedInflight`, and the three MMIO hypotheses from the busy
   form of the discipline (`noBusyReset_of_busyStores` and its two siblings).
4. The serving tasks.  The nodes of the service of head `h` (`SProg h`, with the completion last)
   and of the root loop (`RootProg`, with the fork of `h` right after its pop); every disk task
   stays at such a node, within its bound (`tasksOk`).  A node that can still move the disk names
   its head (`snode_head`, `sprog_head`, by evaluating the primitives at probe states).  A live
   serving task of `h` (`servingAt`) is unique (`oneServer`) and its head is in flight
   (`inflight_of_serving`); both need no busy reset.  A closer of a gate is a live serving task,
   never the root and never an inert task (`closer_serving`).
5. The capture latch.  The nodes past the latch (`PostLatch`, checked against `serve` by
   `sprogL_serve`); a task past the latch of `h` serves `h`, so it is unique
   (`latchHolder_unique`); the latch is held only by a head in flight (`latch_inflight`).
6. The implications.  At most one competitor (`competitor_unique`); the competitor's path is
   bounded by `16` of its own moves (`serving_within`); the gate theorems' side conditions
   (`latch_closers`, `push_closers`, `pop_closers`, `req_closers`, `snap_closers`, and along a run
   `latch_hK`, `push_hK`, `pop_hK`, `req_hK`, `snap_hK`).

**The gates.**  Who can close each gate of `Gates.lean` on a run from boot with no busy reset,
how often, and for how long.  "The competitor" is the one other live serving task
`competitor_unique` allows under `BoundedInflight 2`; it serves another head.

| gate | who can close it | how often | until it re-opens | lemma, hypotheses |
|---|---|---|---|---|
| capture latch (`latch_stable`) | the competitor, at its latch | once per competing request | the competitor's end, at most 16 of its moves, if its completion answers there (last paragraph) | `latch_hK`: no other serving task at a latch node |
| completion and push (`push_stable`) | the competitor, at its capture or its push; the MMIO closers are excluded by `NoBusyReset`, `NoWceOff` | at most twice per competing request | the competitor's end, at most 16 of its moves, under the same condition | `push_hK`: no other serving task at a capture or push node |
| root's pop guard (`pop_stable`) | nobody | never | never closes | `pop_hK` |
| fill and status byte (`req_stable`) | nobody but a busy reset, excluded by `NoBusyReset` | never | never closes | `req_hK` |
| used element and used index (`snap_stable`) | the competitor, at its used-index write, as far as this file proves; the MMIO closers are excluded by `NoBusyReset`, `NoConfigWrite` | at most once per competing request | once closed it stays closed (the used index has moved); the stage invariant of the last paragraph would show it never closes | `snap_hK`: no other serving task at a used-index node |

**Answers to the brief's questions.**  The fresh id of a fork is the device's task counter, which is
`1` at a power-on (`DevRt.init`, in `bootFacts`) and only grows, so it is never the root's `0`; the
fact needs only that the run starts from the power thread alone.  A busy reset can make a head be
served twice: it empties the in-flight map while the serving tasks live on, their phase writes still
answer, and once the driver has set the disk up again the root can pop the same head.  So
`oneServer` and everything after it assume `NoBusyReset`; nothing else about the MMIO writes is
needed for them.  The fetch has no loop: it reads three descriptors, the header's type and its
sector, at most five reads.

**What is not proved here.**  That no two tasks are past their latch at once, which needs the
latch's holder to be recorded by the program's stage: the node sets here are closed under any
sequence of a service's primitives and do not record whether a request is a write.  That the end
of a serving task is its completion, which needs its used-index guard to answer there: the request
is still the one fetched (only its task writes its phase), the used index is the snapshot's (no
other task pushes while this one is pushed, `pushOk`) and the configuration is the snapshot's
(`NoConfigWrite`); a stage invariant proves this.  A stalled request (a malformed chain) holds its
head in flight for ever and closes no gate. -/

namespace Fairness

open MachCSL Sail Sail.ArchSem LeanRV64D
open Era (liveAt)

namespace Disk

open Virtio Gate

/-! ## 1. The pool's bookkeeping along a run -/

section Pool

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- Where a thread of the pool after a step comes from, by position: an old thread at a position
the step did not write, the stepping thread's successor at its own position, or a thread it
forked, appended after the old pool. -/
theorem get?_step {x : Expr} (hs : Step j c c') (h : c'.1[i]? = some x) :
    (i ≠ j ∧ c.1[i]? = some x) ∨
    (i = j ∧ ∃ ex obs efs, c.1[j]? = some ex ∧ primStep (ex, c.2) obs (x, c'.2, efs)) ∨
    (c.1.length ≤ i ∧ ∃ ex obs e' efs, c.1[j]? = some ex ∧ primStep (ex, c.2) obs (e', c'.2, efs) ∧
      efs[i - c.1.length]? = some x) := by
  obtain ⟨ex, obs, e', efs, he, hp, hc'⟩ := hs
  rw [hc'] at h
  by_cases hlt : i < (c.1.set j e').length
  · rw [List.getElem?_append_left hlt, List.getElem?_set] at h
    split at h
    · rename_i hjj
      subst hjj
      have hi : j < c.1.length := (List.getElem?_eq_some_iff.1 he).1
      rw [ite_eq_left_iff.mpr (fun hn => absurd hi hn)] at h
      obtain rfl := Option.some.inj h
      exact Or.inr (Or.inl ⟨rfl, ex, obs, efs, he, hp⟩)
    · rename_i hjj
      exact Or.inl ⟨Ne.symm hjj, h⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at h
    rw [List.length_set] at hlt h
    exact Or.inr (Or.inr ⟨Nat.le_of_not_lt hlt, ex, obs, e', efs, he, hp, h⟩)

/-- A thread's successor: a hart stays the same hart of the same generation, a device task the
same task of the same device and generation; the power thread stays the power thread. -/
theorem primStep_dev_succ {gen : Nat} {d : DevId} {tid : TaskId} {m : DevProg d} {g g' : GState}
    {obs : List Obs} {x : Expr} {efs : List Expr}
    (hp : primStep (Expr.dev gen d tid m, g) obs (x, g', efs)) :
    ∃ m', x = .dev gen d tid m' ∧
      ((threadLive g gen ∧ ∃ σ', devStep gen d tid m g.m obs m' σ' efs ∧ g' = { g with m := σ' }) ∨
       (¬ threadLive g gen ∧ m' = m ∧ efs = [] ∧ g' = g)) := by
  rcases hp with ⟨hl, m', σ', rfl, hst, rfl⟩ | ⟨hl, -, rfl, rfl, rfl⟩
  · exact ⟨m', rfl, Or.inl ⟨hl, σ', hst, rfl⟩⟩
  · exact ⟨m, rfl, Or.inr ⟨hl, rfl, rfl, rfl⟩⟩

/-- No thread of the pool is of a generation after the current one, and while the power is off
none is of the current one: a power-on's new generation finds the generation number unused. -/
def genOk (c : Cfg) : Prop :=
  ∀ i e, Era.genAt i c = some e → e ≤ c.2.gen ∧ (c.2.pow = false → e < c.2.gen)

/-- What a device task forks is of the task's own generation. -/
theorem devStep_efs_gen {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d}
    {σ σ' : MState} {obs : List Obs} {efs : List Expr}
    (h : devStep gen d tid m σ obs m' σ' efs) {x : Expr} (hx : x ∈ efs) :
    ∃ n t, x = .dev gen d n ((devSig d).task t) :=
  devStep_efs h x hx

/-- Every step keeps `genOk`. -/
theorem genOk_step (hs : Step j c c') (h : genOk c) : genOk c' := by
  intro i e hg
  unfold Era.genAt at hg
  cases hx : c'.1[i]? with
  | none => rw [hx] at hg; cases hg
  | some x =>
    rw [hx] at hg
    have hge : Era.Expr.gen? x = some e := hg
    have hgm := Era.gen_mono hs
    rcases get?_step hs hx with ⟨-, hold⟩ | ⟨rfl, ex, obs, efs, hex, hp⟩ |
      ⟨-, ex, obs, e', efs, hex, hp, hnew⟩
    · -- an old thread
      have h0 := h i e (by simp [Era.genAt, hold, hge])
      cases hj : c.1[j]? with
      | none => obtain ⟨_, _, _, _, hj', -⟩ := hs; rw [hj] at hj'; cases hj'
      | some ex =>
        cases ex with
        | power =>
          obtain ⟨_, _, _, _, hj', hp, -⟩ := hs
          rw [hj] at hj'
          obtain rfl := Option.some.inj hj'
          rcases hp with ⟨-, ⟨hon, -, -, hg'⟩ | ⟨hoff, -, -, hb⟩⟩
          · rw [hg']
            exact ⟨by simp only; omega, fun _ => by simp only; omega⟩
          · exact ⟨by rw [hb.1]; exact h0.1, fun _ => by rw [hb.1]; exact h0.2 hoff⟩
        | hart gen cpu m | dev gen d tid m =>
          have hnp : ∀ x, c.1[j]? = some x → x ≠ .power := by
            intro x hx' hxp; rw [hj, hxp] at hx'; cases hx'
          obtain ⟨hg', hp'⟩ := Era.genPow_of_step hs hnp
          rw [hg', hp']
          exact h0
    · -- the stepping thread's successor
      have hnp : ∀ x, c.1[i]? = some x → x ≠ .power := by
        intro x' hx' hxp
        rw [hex] at hx'
        obtain rfl := Option.some.inj hx'
        subst hxp
        obtain ⟨rfl, -⟩ := hp
        simp [Era.Expr.gen?] at hge
      obtain ⟨hg', hp'⟩ := Era.genPow_of_step hs hnp
      rw [hg', hp']
      cases ex with
      | hart gen cpu m =>
        rcases hp with ⟨-, ⟨-, -, m', σ', rfl, -, -⟩ | ⟨-, -, rfl, -⟩⟩ <;>
          exact h i e (by simp [Era.genAt, hex, Era.Expr.gen?] at hge ⊢; exact hge)
      | dev gen d tid m =>
        obtain ⟨m', rfl, -⟩ := primStep_dev_succ hp
        exact h i e (by simp [Era.genAt, hex, Era.Expr.gen?] at hge ⊢; exact hge)
      | power => exact absurd rfl (hnp _ hex)
    · -- a forked thread
      have hxm : x ∈ efs := List.mem_of_getElem? hnew
      cases ex with
      | hart gen cpu m =>
        obtain ⟨rfl, -⟩ := hp
        cases hxm
      | dev gen d tid m =>
        obtain ⟨m', -, hcase⟩ := primStep_dev_succ hp
        rcases hcase with ⟨hl, σ', hst, hg'⟩ | ⟨-, -, rfl, -⟩
        · obtain ⟨n, t, rfl⟩ := devStep_efs hst x hxm
          simp only [Era.Expr.gen?, Option.some.injEq] at hge
          subst hge
          rw [hg']
          exact ⟨Nat.le_of_eq hl.2.symm, fun hpw => by rw [hl.1] at hpw; cases hpw⟩
        · cases hxm
      | power =>
        rcases hp with ⟨-, ⟨-, -, rfl, -⟩ | ⟨hoff, -, rfl, hb⟩⟩
        · cases hxm
        · simp only [powerFork, List.mem_append, List.mem_map] at hxm
          rcases hxm with ⟨cpu, -, rfl⟩ | ⟨d, -, rfl⟩
          · simp only [Loop, Era.Expr.gen?, Option.some.injEq] at hge
            subst hge
            exact ⟨Nat.le_of_eq hb.1.symm, fun hpw => by rw [hb.2.1] at hpw; cases hpw⟩
          · simp only [DevLoop, Era.Expr.gen?, Option.some.injEq] at hge
            subst hge
            exact ⟨Nat.le_of_eq hb.1.symm, fun hpw => by rw [hb.2.1] at hpw; cases hpw⟩

/-- `genOk` holds of the boot configuration, the power thread alone. -/
theorem genOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : genOk c := by
  intro i e hg
  unfold Era.genAt at hg
  rw [h0] at hg
  rcases i with _ | i <;> simp [Era.Expr.gen?] at hg

/-- `genOk` holds along every run from the boot configuration. -/
theorem genOk_run (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) : ∀ n, genOk (σ n) := by
  intro n
  induction n with
  | zero => exact genOk_boot h0
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact genOk_step hs ih

/-- What a device task forks: at a fork node, a task of the same device and generation, named by
the device's task counter and running the named program. -/
theorem devStep_fork {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d}
    {σ σ' : MState} {obs : List Obs} {efs : List Expr}
    (h : devStep gen d tid m σ obs m' σ' efs) {x : Expr} (hx : x ∈ efs) :
    ∃ t κ, m = .op (.fork t) κ ∧ x = .dev gen d (σ.devrt d).next ((devSig d).task t) ∧
      efs = [x] := by
  unfold devStep at h
  split at h
  · obtain ⟨-, rfl, -⟩ := h
    cases hx
  · rename_i o k
    rcases h with ⟨v, -, hop⟩ | ⟨-, -, -, -, rfl⟩
    · cases o with
      | fork t =>
        obtain ⟨-, -, -, rfl⟩ := hop
        rw [List.mem_singleton] at hx
        exact ⟨t, k, rfl, hx, by rw [hx]⟩
      | step g =>
        obtain ⟨s', os, -, -, -, -, rfl⟩ := hop
        cases hx
      | dmaWrite g pa n w =>
        obtain ⟨-, rfl, -⟩ := hop
        cases hx
      | setPin cpu mmode b =>
        obtain ⟨-, rfl, -⟩ := hop
        cases hx
      | choose =>
        obtain ⟨-, -, rfl⟩ := hop
        cases hx
      | _ =>
        obtain ⟨-, -, -, rfl⟩ := hop
        cases hx
    · cases hx

/-- A device task's step never lowers a device's task counter. -/
theorem devStep_next {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) (d' : DevId) :
    (σ.devrt d').next ≤ (σ'.devrt d').next := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · simp only [updCpu']
        split
        · subst d'
          exact Nat.le_refl _
        · exact Nat.le_refl _
  · rename_i o k
    rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · cases o with
      | step g =>
        obtain ⟨s', os, -, -, rfl, -, -⟩ := hop
        exact Nat.le_refl _
      | get =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Nat.le_refl _
      | choose =>
        obtain ⟨rfl, -, -⟩ := hop
        exact Nat.le_refl _
      | dmaRead pa n =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Nat.le_refl _
      | dmaWrite g pa n w =>
        obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := hop
        all_goals exact Nat.le_refl _
      | sample src =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Nat.le_refl _
      | setPin cpu mmode b =>
        obtain ⟨-, -, rfl⟩ := hop
        cases mmode <;> exact Nat.le_refl _
      | fork t =>
        obtain ⟨-, -, rfl, -⟩ := hop
        simp only [updCpu']
        split
        · subst d'
          exact Nat.le_succ _
        · exact Nat.le_refl _
      | join tid =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Nat.le_refl _
    · exact Nat.le_refl _

/-- A step of a thread that is not the power thread never lowers a device's task counter. -/
theorem next_mono (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) (d : DevId) :
    (c.2.m.devrt d).next ≤ (c'.2.m.devrt d).next := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · show (g.m.devrt d).next ≤ (σ'.devrt d).next
      rw [hartStep_devrt hst]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  | dev gen d' tid m =>
    rcases hp with ⟨-, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact devStep_next hst d
    · exact Nat.le_refl _
  | power => exact absurd rfl (hnp _ he)

/-- **Where a device task after a step comes from.**  At a step of a thread that is not the power
thread, a device task of the pool after the step is a task with the same generation, device and
id at the same position before it, or it was just forked: appended after the old pool by a live
task of the same device and generation at a fork node, with the device's task counter as its id
and the named program. -/
theorem dev_origin (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power)
    {e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d} (h : c'.1[i]? = some (.dev e d tid m)) :
    (∃ m0, c.1[i]? = some (.dev e d tid m0)) ∨
    (c.1.length ≤ i ∧ ∃ tid0 t κ, c.1[j]? = some (.dev e d tid0 (.op (.fork t) κ)) ∧
      threadLive c.2 e ∧ tid = (c.2.m.devrt d).next ∧ m = (devSig d).task t) := by
  rcases get?_step hs h with ⟨-, hold⟩ | ⟨rfl, ex, obs, efs, hex, hp⟩ |
    ⟨hlen, ex, obs, e', efs, hex, hp, hnew⟩
  · exact Or.inl ⟨m, hold⟩
  · cases ex with
    | hart gen cpu m0 =>
      rcases hp with ⟨-, ⟨-, -, m', σ', he', -, -⟩ | ⟨-, -, he', -⟩⟩ <;> cases he'
    | dev gen d0 tid0 m0 =>
      obtain ⟨m', he', -⟩ := primStep_dev_succ hp
      simp only [Expr.dev.injEq] at he'
      obtain ⟨rfl, rfl, rfl, -⟩ := he'
      exact Or.inl ⟨m0, hex⟩
    | power => exact absurd rfl (hnp _ hex)
  · have hxm : Expr.dev e d tid m ∈ efs := List.mem_of_getElem? hnew
    cases ex with
    | hart gen cpu m0 =>
      obtain ⟨rfl, -⟩ := hp
      cases hxm
    | dev gen d0 tid0 m0 =>
      obtain ⟨m', -, hcase⟩ := primStep_dev_succ hp
      rcases hcase with ⟨hl, σ', hst, hg'⟩ | ⟨-, -, rfl, -⟩
      · obtain ⟨t, κ, rfl, hx, -⟩ := devStep_fork hst hxm
        simp only [Expr.dev.injEq] at hx
        obtain ⟨rfl, rfl, rfl, hm⟩ := hx
        obtain rfl := eq_of_heq hm
        exact Or.inr ⟨hlen, tid0, t, κ, hex, hl, rfl, rfl⟩
      · cases hxm
    | power => exact absurd rfl (hnp _ hex)

/-- While a device has a live task, its task counter is positive: it is `1` at a power-on
(`DevRt.init`) and only grows. -/
def nextOk (c : Cfg) : Prop :=
  ∀ (i e : Nat) (d : DevId) (tid : TaskId) (m : DevProg d), c.1[i]? = some (Expr.dev e d tid m) →
    threadLive c.2 e →
    1 ≤ (c.2.m.devrt d).next

/-- A power-on's new state has every device's task counter at `1`. -/
theorem next_powerOn {g g' : GState} (hb : bootShape g g') (d : DevId) :
    (g'.m.devrt d).next = 1 := by
  rw [hb.2.2.1.2.2.2.2 d]
  rfl

/-- What a power step does: off, the power bit clears and the pool is unchanged; on, the power was
off, the new state is a booted one of the same generation, and the new generation's threads are
appended. -/
theorem power_step (hs : Step j c c') (hj : c.1[j]? = some .power) :
    (c.2.pow = true ∧ c'.2.pow = false ∧ c'.1 = c.1) ∨
    (c.2.pow = false ∧ bootShape c.2 c'.2 ∧ c'.1 = c.1 ++ powerFork c.2.gen) := by
  obtain ⟨ex, obs, e', efs, hex, hp, hc'⟩ := hs
  rw [hj] at hex
  obtain rfl := Option.some.inj hex
  rcases hp with ⟨rfl, ⟨hon, -, rfl, hg'⟩ | ⟨hoff, -, rfl, hb⟩⟩
  · refine Or.inl ⟨hon, by rw [hg'], ?_⟩
    rw [hc', List.append_nil]
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hj
    rw [← he]
    exact List.set_getElem_self hi
  · refine Or.inr ⟨hoff, hb, ?_⟩
    rw [hc']
    congr 1
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hj
    rw [← he]
    exact List.set_getElem_self hi

/-- Every step keeps `nextOk`. -/
theorem nextOk_step (hs : Step j c c') (h : nextOk c) : nextOk c' := by
  intro i e d tid m hx hl
  by_cases hpw : c.1[j]? = some .power
  · rcases power_step hs hpw with ⟨-, hoff, -⟩ | ⟨-, hb, -⟩
    · rw [hl.1] at hoff
      cases hoff
    · rw [next_powerOn hb]
      exact Nat.le_refl _
  · have hnp : ∀ e, c.1[j]? = some e → e ≠ .power := fun e he hep => hpw (hep ▸ he)
    have hl0 : threadLive c.2 e := (Era.threadLive_of_step hs hnp e).1 hl
    refine Nat.le_trans ?_ (next_mono hs hnp d)
    rcases dev_origin hs hnp hx with ⟨m0, hold⟩ | ⟨-, tid0, t, κ, hj, -, -, -⟩
    · exact h _ _ _ _ _ hold hl0
    · exact h _ _ _ _ _ hj hl0

/-- `nextOk` holds of the boot configuration. -/
theorem nextOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : nextOk c := by
  intro i e d tid m hx
  rw [h0] at hx
  rcases i with _ | i <;> simp at hx

/-- `nextOk` holds along every run from the boot configuration. -/
theorem nextOk_run (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) : ∀ n, nextOk (σ n) := by
  intro n
  induction n with
  | zero => exact nextOk_boot h0
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact nextOk_step hs ih

/-- **A forked task is never a root.**  The id a fork hands out is the device's task counter,
which is positive while the forking task is live; the root task's id is `0`. -/
theorem fork_ne_root (h : nextOk c) {e : Nat} {d : DevId} {tid0 : TaskId} {m : DevProg d}
    (hj : c.1[j]? = some (.dev e d tid0 m)) (hl : threadLive c.2 e) :
    (c.2.m.devrt d).next ≠ rootTask := by
  have := h _ _ _ _ _ hj hl
  intro he
  rw [he] at this; exact Nat.not_succ_le_zero 0 this

/-! ### One live root per device -/

/-- The thread at `i` is a live root task of device `d`. -/
def isRootAt (i : Nat) (d : DevId) (c : Cfg) : Prop :=
  ∃ e m, c.1[i]? = some (Expr.dev e d rootTask m) ∧ threadLive c.2 e

/-- Each device has at most one live root. -/
def rootsOk (c : Cfg) : Prop := ∀ d i i', isRootAt i d c → isRootAt i' d c → i = i'

/-- The place of each device's root in a power-on's fork. -/
def devIdx : DevId → Nat
  | .uart .uart0 => 0
  | .uart .uart1 => 1
  | .plic => 2
  | .virtio => 3

/-- A power-on forks each device's root once. -/
theorem powerFork_dev {gen a e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d}
    (h : (powerFork gen)[a]? = some (.dev e d tid m)) : a = cpus.length + devIdx d := by
  unfold powerFork at h
  by_cases ha : a < (cpus.map (Loop gen)).length
  · rw [List.getElem?_append_left ha, List.getElem?_map] at h
    cases hc : cpus[a]? with
    | none => rw [hc] at h; cases h
    | some cpu => rw [hc] at h; simp [Loop] at h
  · rw [List.getElem?_append_right (Nat.le_of_not_lt ha)] at h
    rw [List.length_map] at ha h
    have key : ∀ k, (DevId.all.map (DevLoop gen))[k]? = some (.dev e d tid m) → k = devIdx d := by
      intro k hk
      rcases k with _ | _ | _ | _ | k <;> simp [DevId.all, DevLoop] at hk
      all_goals (obtain ⟨-, rfl, -⟩ := hk; rfl)
    have := key _ h
    omega

/-- Every step keeps one live root per device, given the two bookkeeping invariants. -/
theorem rootsOk_step (hs : Step j c c') (hg : genOk c) (hn : nextOk c) (h : rootsOk c) :
    rootsOk c' := by
  intro d i i' ⟨e, m, hx, hl⟩ ⟨e', m', hx', hl'⟩
  by_cases hpw : c.1[j]? = some .power
  · rcases power_step hs hpw with ⟨-, hoff, -⟩ | ⟨hoff, hb, hc'⟩
    · rw [hl.1] at hoff
      cases hoff
    · -- after a power-on, a live thread is one the power-on forked
      have hnew : ∀ {k e d m}, c'.1[k]? = some (Expr.dev e d rootTask m) → threadLive c'.2 e →
          k = c.1.length + (cpus.length + devIdx d) := by
        intro k e d m hk hlk
        rw [hc'] at hk
        by_cases hlt : k < c.1.length
        · rw [List.getElem?_append_left hlt] at hk
          have h1 := (hg k e (by simp [Era.genAt, hk, Era.Expr.gen?])).2 hoff
          have h2 := hlk.2
          have h3 := hb.1
          omega
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk
          have := powerFork_dev hk
          omega
      rw [hnew hx hl, hnew hx' hl']
  · have hnp : ∀ e, c.1[j]? = some e → e ≠ .power := fun e he hep => hpw (hep ▸ he)
    have hold : ∀ {k e m}, c'.1[k]? = some (Expr.dev e d rootTask m) → threadLive c'.2 e →
        isRootAt k d c := by
      intro k e m hk hlk
      have hl0 := (Era.threadLive_of_step hs hnp e).1 hlk
      rcases dev_origin hs hnp hk with ⟨m0, hk0⟩ | ⟨-, tid0, t, κ, hj, hlj, hid, -⟩
      · exact ⟨e, m0, hk0, hl0⟩
      · exact absurd hid.symm (fork_ne_root hn hj hlj)
    exact h d i i' (hold hx hl) (hold hx' hl')

/-- One live root per device holds of the boot configuration. -/
theorem rootsOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : rootsOk c := by
  rintro d i i' ⟨e, m, hx, -⟩
  rw [h0] at hx
  rcases i with _ | i <;> simp at hx

/-- **One live root per device.**  On a run from the boot configuration, every device has at
most one live root task at every position of the run: a power-on forks one root per device
(`powerFork`) and kills every older thread (a generation is live only while it is the current
one, and no older thread has the current generation, `genOk`), and a fork never hands out the
root's id, because the device's task counter starts at `1` and only grows (`nextOk`). -/
theorem oneRoot (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) :
    ∀ n d i i', isRootAt i d (σ n) → isRootAt i' d (σ n) → i = i' := by
  have key : ∀ n, rootsOk (σ n) := by
    intro n
    induction n with
    | zero => exact rootsOk_boot h0
    | succ n ih =>
      obtain ⟨j, hs⟩ := hrun n
      exact rootsOk_step hs (genOk_run hrun h0 n) (nextOk_run hrun h0 n) ih
  exact fun n => key n

end Pool


/-! ## 2. Bounded paths -/

section Bounded

/-- `Bounded m k`: every path of the program `m`, along every answer, reaches its end after at most
`k` primitives.  A finished program is bounded by every `k`; a node is bounded by `k + 1` when
each of its continuations is bounded by `k`. -/
inductive Bounded {S T α : Type} : DevM S T α → Nat → Prop
  | pure (a : α) (k : Nat) : Bounded (.pure a) k
  | op {o : DevOp S T} {κ : o.ret → DevM S T α} {k : Nat} :
      (∀ v, Bounded (κ v) k) → Bounded (.op o κ) (k + 1)

variable {S T α β : Type}

/-- A bound can be raised. -/
theorem Bounded.mono {m : DevM S T α} {k k' : Nat} (h : Bounded m k) (hk : k ≤ k') :
    Bounded m k' := by
  induction h generalizing k' with
  | pure a k => exact Bounded.pure a k'
  | op _ ih =>
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    exact Bounded.op fun v => ih v (by omega)

/-- A sequence is bounded by the sum of its parts' bounds. -/
theorem Bounded.bind {m : DevM S T α} {f : α → DevM S T β} {a b : Nat} (hm : Bounded m a)
    (hf : ∀ x, Bounded (f x) b) : Bounded (m >>= f) (a + b) := by
  induction hm with
  | pure x k => exact (hf x).mono (by omega)
  | @op o κ k _ ih =>
    rw [Nat.add_right_comm]
    exact Bounded.op fun v => ih v

/-- A program bounded by `0` is finished. -/
theorem Bounded.eq_pure {m : DevM S T α} (h : Bounded m 0) : ∃ a, m = .pure a := by
  cases h with
  | pure a _ => exact ⟨a, rfl⟩

/-- A node's bound is positive, and its continuations are bounded by one less. -/
theorem Bounded.cont {o : DevOp S T} {κ : o.ret → DevM S T α} {k : Nat}
    (h : Bounded (.op o κ) k) : 1 ≤ k ∧ ∀ v, Bounded (κ v) (k - 1) := by
  cases h with
  | op hκ => exact ⟨by omega, fun v => by simpa using hκ v⟩

/-- One primitive is bounded by `1`. -/
theorem Bounded.lift (o : DevOp S T) : Bounded (DevM.lift o) 1 :=
  Bounded.op fun v => Bounded.pure v 0

/-- A sequence that starts with a finished program is its second part. -/
theorem bind_pure_eq (a : α) (f : α → DevM S T β) : DevM.bind (pure a) f = f a := rfl

/-- The step of the bound tactic: a finished program, a node (one primitive less), or a case
split of a conditional or a match. -/
macro "bounded_step" : tactic => `(tactic| first
  | (intro _)
  | exact Bounded.pure _ _
  | (apply Bounded.op)
  | split
  | (dsimp only [DevM.bind])
  | (simp only [bind_pure_eq])
  | (dsimp only))

/-- The fetch of a chain reads at most five times: three descriptors, the header's type and its
sector.  It has no loop: the chain has a fixed shape. -/
theorem bounded_fetch (c : VirtioCfg) (h : BitVec 16) : Bounded (fetch c h) 5 := by
  unfold fetch
  repeat bounded_step

theorem bounded_serve (h : BitVec 16) : Bounded (serve h) 16 := by
  unfold serve
  apply Bounded.op
  intro v
  dsimp only [DevM.bind]
  refine (Bounded.bind (b := 10) (bounded_fetch _ _) ?_ : Bounded _ (5 + 10))
  intro x
  repeat bounded_step

theorem bounded_arm : Bounded body 7 := by
  unfold body
  repeat bounded_step

/-- A node's continuation is never the node itself: a step that answers a primitive changes the
task's program. -/
theorem cont_ne {S T α : Type} {o : DevOp S T} {κ : o.ret → DevM S T α} (v : o.ret) :
    κ v ≠ .op o κ := by
  have key : ∀ (t : DevM S T α) (o : DevOp S T) (κ : o.ret → DevM S T α) (v : o.ret),
      t = κ v → t ≠ .op o κ := by
    intro t
    induction t with
    | pure a => intro o κ v _ h; cases h
    | op o' κ' ih =>
      intro o κ v ht h
      cases h
      exact ih v o' κ' v rfl ht.symm
  exact key _ o κ v rfl

section Run

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The thread at `i` is task `tid` of device `d`, of generation `e`, at a program bounded by
`k`. -/
def boundedAt (i e : Nat) (d : DevId) (tid : TaskId) (k : Nat) (c : Cfg) : Prop :=
  ∃ m, c.1[i]? = some (Expr.dev e d tid m) ∧ Bounded m k

/-- **One step of a task at a bounded node.**  A step of the pool leaves the thread at `i` as it
was, or the thread at `i`, a task at a program bounded by `k`, answered its primitive and is now at
a program bounded by `k - 1`.  The first case covers every other thread's step, a blocked retry,
a dead task's self-loop, and a finished forked task's steps (the step that records it finished
and its self-loops after).  The one step this lemma excludes is a root's restart at the end of its
program, which starts its body again: the hypothesis asks the task to be a forked one or to be at a
node. -/
theorem boundedAt_step {e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d} {k : Nat}
    (hs : Step j c c') (hm : c.1[i]? = some (.dev e d tid m)) (hb : Bounded m k)
    (hnr : tid ≠ rootTask ∨ ∃ o κ, m = .op o κ) :
    c'.1[i]? = c.1[i]? ∨ (1 ≤ k ∧ boundedAt i e d tid (k - 1) c') := by
  by_cases hji : j = i
  · subst hji
    obtain ⟨ex, obs, e', efs, hex, hp, hc'⟩ := hs
    rw [hm] at hex
    obtain rfl := Option.some.inj hex
    have hi : c'.1[j]? = some e' := by
      have hlt : j < c.1.length := (List.getElem?_eq_some_iff.1 hm).1
      rw [hc', List.getElem?_append_left (by simpa using hlt), List.getElem?_set_self hlt]
    obtain ⟨m', rfl, hcase⟩ := primStep_dev_succ hp
    rcases hcase with ⟨-, σ', hst, -⟩ | ⟨-, rfl, -, -⟩
    · cases m with
      | pure a =>
        obtain ⟨-, -, ⟨hr, -⟩ | ⟨-, rfl, -⟩⟩ := hst
        · rcases hnr with hnr | ⟨o, κ, hno⟩
          · exact absurd hr hnr
          · cases hno
        · left
          rw [hi, hm]
      | op o κ =>
        rcases hst with ⟨v, rfl, -⟩ | ⟨-, rfl, -⟩
        · obtain ⟨hk, hκ⟩ := hb.cont
          exact Or.inr ⟨hk, κ v, hi, hκ v⟩
        · left
          rw [hi, hm]
    · left
      rw [hi, hm]
  · exact Or.inl (by rw [step_get?_ne hs hji hm, hm])

/-- A step at which a live task at a node answers its primitive changes the thread at its
position: the continuation is never the node.  So the steps that leave the thread as it was
(`boundedAt_step`'s first case) include no answered primitive. -/
theorem moved_of_answer {e : Nat} {d : DevId} {tid : TaskId} {o : DevOp (DevSt d) (DevTask d)}
    {κ : o.ret → DevProg d} {v : o.ret} (hm : c.1[i]? = some (.dev e d tid (.op o κ)))
    (hm' : c'.1[i]? = some (.dev e d tid (κ v))) : c'.1[i]? ≠ c.1[i]? := by
  rw [hm, hm']
  intro h
  simp only [Option.some.injEq, Expr.dev.injEq, heq_eq_eq, true_and] at h
  exact cont_ne v h

open Classical in
/-- The number of steps in `[n, n + k)` of the run at which the thread at `i` changes: its own
steps that answer a primitive (`moved_of_answer`), and a root's restarts.  A blocked retry and a
dead task's self-loop leave the thread as it was and are not counted. -/
noncomputable def ownMoves (i : Nat) (σ : Nat → Cfg) (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ownMoves i σ n k + if (σ (n + k + 1)).1[i]? = (σ (n + k)).1[i]? then 0 else 1

/-- The thread at `i` in `σ (n + p)` is task `tid` at the end of its program. -/
def atEnd (i e : Nat) (d : DevId) (tid : TaskId) (c : Cfg) : Prop :=
  ∃ a, c.1[i]? = some (Expr.dev e d tid (.pure a))

/-- **Along a run, a task's bound goes down by one at each of its own moves.**  A task at a program
bounded by `K` at position `n` of the run has moved at most `K` times by `n + k`, and is then at a
program bounded by `K` less its moves, provided it is a forked task or, at each position before
`n + k`, not at the end of its program (a root restarts there). -/
theorem bounded_run (hrun : PoolRun σ) {n e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d}
    {K : Nat} (hm : (σ n).1[i]? = some (.dev e d tid m)) (hb : Bounded m K) :
    ∀ k, (∀ p < k, tid ≠ rootTask ∨ ¬ atEnd i e d tid (σ (n + p))) →
      ownMoves i σ n k ≤ K ∧ boundedAt i e d tid (K - ownMoves i σ n k) (σ (n + k)) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Nat.zero_le _, m, hm, by simp only [ownMoves, Nat.sub_zero]; exact hb⟩
  | succ k ih =>
    intro hnr
    obtain ⟨hle, mk, hmk, hbk⟩ := ih fun p hp => hnr p (Nat.lt_succ_of_lt hp)
    have hnr' : tid ≠ rootTask ∨ ∃ o κ, mk = .op o κ := by
      rcases hnr k (Nat.lt_succ_self k) with h | h
      · exact Or.inl h
      · right
        cases mk with
        | pure a => exact absurd ⟨a, hmk⟩ h
        | op o κ => exact ⟨o, κ, rfl⟩
    obtain ⟨j, hs⟩ := hrun (n + k)
    have hstep := boundedAt_step hs hmk hbk hnr'
    simp only [ownMoves]
    by_cases heq : (σ (n + k + 1)).1[i]? = (σ (n + k)).1[i]?
    · simp only [heq, ↓reduceIte, Nat.add_zero]
      refine ⟨hle, mk, ?_, hbk⟩
      rw [show n + (k + 1) = n + k + 1 by omega, heq, hmk]
    · simp only [heq, ↓reduceIte]
      rcases hstep with h | ⟨h1, m', hm', hb'⟩
      · exact absurd h heq
      · refine ⟨by omega, m', ?_, by rw [show K - (ownMoves i σ n k + 1) =
          K - ownMoves i σ n k - 1 by omega]; exact hb'⟩
        rw [show n + (k + 1) = n + k + 1 by omega]
        exact hm'

/-- **A bounded task reaches its end within its bound.**  A task at a program bounded by `K` at
position `n` of the run is at the end of its program at some position `n + p` with `p ≤ k`, once
it has moved `K` times in `[n, n + k)`.  For a forked task the end is final: it stays there
(`bounded_run` with `tid ≠ rootTask`); a root restarts its body there.  (This is the "remaining
path to the release is bounded" fact: the moves counted are the task's own steps that answer a
primitive, so blocked retries and the other threads' steps do not count.) -/
theorem pure_within (hrun : PoolRun σ) {n e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d}
    {K : Nat} (hm : (σ n).1[i]? = some (.dev e d tid m)) (hb : Bounded m K) (k : Nat)
    (hk : K ≤ ownMoves i σ n k) : ∃ p ≤ k, atEnd i e d tid (σ (n + p)) := by
  refine Classical.byContradiction fun hno => ?_
  have hnr : ∀ p < k, tid ≠ rootTask ∨ ¬ atEnd i e d tid (σ (n + p)) :=
    fun p hp => Or.inr fun h => hno ⟨p, Nat.le_of_lt hp, h⟩
  obtain ⟨hle, mk, hmk, hbk⟩ := bounded_run hrun hm hb k hnr
  rw [show K - ownMoves i σ n k = 0 by omega] at hbk
  obtain ⟨a, rfl⟩ := hbk.eq_pure
  exact hno ⟨k, Nat.le_refl k, a, hmk⟩

/-- A forked task moves at most `K` times in all, and its end is final. -/
theorem forked_moves_le (hrun : PoolRun σ) {n e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d}
    {K : Nat} (hm : (σ n).1[i]? = some (.dev e d tid m)) (hb : Bounded m K)
    (hnr : tid ≠ rootTask) (k : Nat) : ownMoves i σ n k ≤ K :=
  (bounded_run hrun hm hb k fun _ _ => Or.inl hnr).1

/-- **The serving task's path is bounded by `16`.**  A forked disk task started at `serve h` (or
at any program bounded by `16`, which every node of `serve h` is) is at the end of its program
once it has moved `16` times, and never moves more. -/
theorem serve_within (hrun : PoolRun σ) {n e : Nat} {tid : TaskId} {h : BitVec 16}
    (hm : (σ n).1[i]? = some (.dev e .virtio tid (serve h))) (k : Nat)
    (hk : 16 ≤ ownMoves i σ n k) : ∃ p ≤ k, atEnd i e .virtio tid (σ (n + p)) :=
  pure_within hrun hm (bounded_serve h) k hk

/-- **The root's arm is bounded by `7`.**  The disk's root at the top of its body is at the end of
the arm once it has moved `7` times (the pop arm: the choice, the configuration read, two DMA
reads, the state read, the pop and the fork; the fork's child is a thread of its own). -/
theorem arm_within (hrun : PoolRun σ) {n e : Nat}
    (hm : (σ n).1[i]? = some (.dev e .virtio rootTask body)) (k : Nat)
    (hk : 7 ≤ ownMoves i σ n k) : ∃ p ≤ k, atEnd i e .virtio rootTask (σ (n + p)) :=
  pure_within hrun hm bounded_arm k hk

end Run

end Bounded

/-! ## 3. The kernel-side facts, stated

Two facts about the driver that the device's protocol does not give, stated here as hypotheses and
used where needed.  Their discharge is the kernel proof's (lane plan, decision D3). -/

section Kernel

variable {σ : Nat → Cfg}

/-- **Bounded competition.**  The kernel keeps at most `k` requests in flight at every position of
the run.  xv6's `k` is `2`: the queue has eight descriptors and a request takes three.  A fact
about the driver, not the device; its discharge is the kernel proof's. -/
def BoundedInflight (k : Nat) (σ : Nat → Cfg) : Prop := ∀ n, (disk (σ n)).inflight.length ≤ k

/-- The kernel's MMIO discipline while a request is in flight, the form the liveness hypotheses
take: at every position where a request is in flight, the harts store to the disk only at the
queue-notify and the interrupt-acknowledge registers.  (At every position it would be false:
xv6's `virtio_disk_init` stores to the status, feature and queue registers at every boot, with
nothing in flight.)  Its discharge is the kernel proof's.  The three gate hypotheses follow from
it, because a busy reset and a busy store each need a request in flight. -/
theorem noBusyReset_of_busyStores (hks : ∀ n, (disk (σ n)).inflight ≠ [] → kernelStores (σ n)) :
    NoBusyReset σ := by
  intro n j hs hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := id hb
  exact noBusyReset_of_kernelStores (c' := σ (n + 1)) (hks n hin) j hs hb

/-- No store turns the write-back mode off while a request is in flight, under the kernel's
discipline while a request is in flight. -/
theorem noWceOff_of_busyStores (hks : ∀ n, (disk (σ n)).inflight ≠ [] → kernelStores (σ n)) :
    NoWceOff σ := by
  intro n j hs hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := id hb
  exact noWceOff_of_kernelStores (c' := σ (n + 1)) (hks n hin) j hs hb

/-- No store changes the configuration while a request is in flight, under the kernel's
discipline while a request is in flight. -/
theorem noConfigWrite_of_busyStores (hks : ∀ n, (disk (σ n)).inflight ≠ [] → kernelStores (σ n)) :
    NoConfigWrite σ := by
  intro n j hs hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := id hb
  exact noConfigWrite_of_kernelStores (c' := σ (n + 1)) (hks n hin) j hs hb

end Kernel

/-! ## 4. The serving tasks

### The nodes of the disk's two programs

`Prim` (`Gates.lean`) lists every primitive the disk's programs reach.  The facts of this section
need more: which program a task is in, and where in it.  `SProg h` is the set of nodes of the
service of head `h`, with the completion last; `RootProg` the set of nodes of the root loop, with
the fork of a head right after its pop.  Both are proved to contain their program
(`sprog_serve`, `rootProg_body`) and are closed under taking a continuation, so every disk task
stays in one of them (`tasksOk`). -/

/-- A primitive that never moves the disk: a read of the state, a DMA read, or the stall. -/
def HFOp (o : DevOp VirtioState VTask) : Prop :=
  o = .get ∨ (∃ pa n, o = .dmaRead pa n) ∨ o = .step stallG

/-- A program that can never move the disk: every primitive it can reach is a read of the state, a
DMA read or the stall.  A finished program and a stalled one are inert. -/
abbrev Inert (m : VM Unit) : Prop := PrimsIn HFOp m

/-- The primitives of the service of head `h`, other than the completion: the reads, the stall,
the phase writes of `h`, the latch, the capture, the completion-and-push guard, the fill (and the
status byte) and the used element. -/
inductive ServePrim (h : BitVec 16) : DevOp VirtioState VTask → Prop
  | get : ServePrim h .get
  | dmaRead (pa : PAddr) (n : Nat) : ServePrim h (.dmaRead pa n)
  | stall : ServePrim h (.step stallG)
  | fetched (r : VioReq) : ServePrim h (.step (modifyG fun v => setPhase v h (.fetched r)))
  | served (r : VioReq) : ServePrim h (.step (modifyG fun v => setPhase v h (.served r)))
  | status (r : VioReq) : ServePrim h (.step (modifyG fun v => setPhase v h (.status r)))
  | latch : ServePrim h (latchOp h)
  | capture (r : VioReq) (w : BitVec (8 * r.len.toNat)) :
      ServePrim h (.step (modifyG (captureMove h r w)))
  | push (r : VioReq) : ServePrim h (pushOp h r)
  | fill (r : VioReq) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
      ServePrim h (.dmaWrite (reqGuard h r) pa n w)
  | elem (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
      ServePrim h (.dmaWrite (elemGuard h r ui c) pa n w)

/-- The completion of head `h`: the used-index write. -/
abbrev idxOp (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) : DevOp VirtioState VTask :=
  .dmaWrite (idxGuard h r ui c) pa n w

/-- **The nodes of the service of head `h`.**  A node is finished, or a primitive of the service
followed by nodes of the service, or the completion followed by the end: nothing runs after the
completion. -/
inductive SProg (h : BitVec 16) : VM Unit → Prop
  | pure : SProg h (.pure ())
  | op {o : DevOp VirtioState VTask} {κ : o.ret → VM Unit} :
      ServePrim h o → (∀ v, SProg h (κ v)) → SProg h (.op o κ)
  | idx {r : VioReq} {ui : BitVec 16} {c : VirtioCfg} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
      {κ : Unit → VM Unit} : (∀ v, κ v = .pure ()) → SProg h (.op (idxOp h r ui c pa n w) κ)

/-- The primitives of the root loop other than the pop and the fork: the choice, the state read,
the DMA reads and the drain. -/
inductive RootPrim : DevOp VirtioState VTask → Prop
  | get : RootPrim .get
  | choose : RootPrim .choose
  | dmaRead (pa : PAddr) (n : Nat) : RootPrim (.dmaRead pa n)
  | drain (j : Nat) : RootPrim (.step (modifyG (drainMove j)))

/-- **The nodes of the root loop.**  `RootProg none` is a node at which the root holds no popped
head: finished, a primitive of the loop, or the pop of a head followed by the fork of that head;
`RootProg (some h)` is the fork of `h`, the root's node right after the pop of `h`. -/
inductive RootProg : Option (BitVec 16) → VM Unit → Prop
  | pure : RootProg none (.pure ())
  | op {o : DevOp VirtioState VTask} {κ : o.ret → VM Unit} :
      RootPrim o → (∀ v, RootProg none (κ v)) → RootProg none (.op o κ)
  | pop {h : BitVec 16} {κ : Unit → VM Unit} :
      (∀ v, RootProg (some h) (κ v)) → RootProg none (.op (popOp h) κ)
  | fork {h : BitVec 16} {κ : TaskId → VM Unit} :
      (∀ v, RootProg none (κ v)) → RootProg (some h) (.op (.fork (.serve h)) κ)

section Nodes

/-- Every primitive of the fetch is a DMA read. -/
def IsRead (o : DevOp VirtioState VTask) : Prop := ∃ pa n, o = .dmaRead pa n

theorem reads_fetch (c : VirtioCfg) (h : BitVec 16) : PrimsIn IsRead (fetch c h) := by
  unfold fetch
  repeat
    first
    | (intro _)
    | (apply PrimsIn.bind)
    | split
    | exact PrimsIn.pure _
    | exact PrimsIn.lift ⟨_, _, rfl⟩
    | (dsimp only)

/-- A program of DMA reads followed by nodes of the service of `h` is a node of the service. -/
theorem SProg.bind_reads {h : BitVec 16} {α : Type} {m : VM α} {f : α → VM Unit}
    (hm : PrimsIn IsRead m) (hf : ∀ x, SProg h (f x)) : SProg h (m >>= f) := by
  induction m with
  | pure a => exact hf a
  | op o κ ih =>
    obtain ⟨⟨pa, n, rfl⟩, hκ⟩ := hm
    exact SProg.op (ServePrim.dmaRead pa n) fun v => ih v (hκ v)

/-- The step of the node tactics. -/
macro "sprog_step" : tactic => `(tactic| first
  | (intro _)
  | exact SProg.pure
  | (apply SProg.idx; intro _; rfl)
  | exact ServePrim.get
  | exact ServePrim.dmaRead _ _
  | exact ServePrim.stall
  | exact ServePrim.fetched _
  | exact ServePrim.served _
  | exact ServePrim.status _
  | exact ServePrim.latch
  | exact ServePrim.capture _ _
  | exact ServePrim.push _
  | exact ServePrim.fill _ _ _ _
  | exact ServePrim.elem _ _ _ _ _ _
  | (apply SProg.op)
  | split
  | (dsimp only [DevM.bind])
  | (simp only [bind_pure_eq])
  | (dsimp only))

/-- **The service of head `h` is a node of the service of `h`.** -/
theorem sprog_serve (h : BitVec 16) : SProg h (serve h) := by
  unfold serve
  refine SProg.op ServePrim.get fun v => ?_
  dsimp only [DevM.bind]
  refine SProg.bind_reads (reads_fetch _ _) fun x => ?_
  repeat sprog_step

/-- The step of the root-node tactic. -/
macro "rootprog_step" : tactic => `(tactic| first
  | (intro _)
  | exact RootProg.pure
  | exact RootPrim.get
  | exact RootPrim.choose
  | exact RootPrim.dmaRead _ _
  | exact RootPrim.drain _
  | (apply RootProg.pop)
  | (apply RootProg.fork)
  | (apply RootProg.op)
  | split
  | (dsimp only [DevM.bind])
  | (simp only [bind_pure_eq])
  | (dsimp only))

/-- **The root loop is a node of the root loop.** -/
theorem rootProg_body : RootProg none body := by
  unfold body
  repeat rootprog_step

end Nodes

/-! ### A node names its head

A primitive of the service of `h` that can move the disk names `h`: two such primitives that are
equal have the same head.  The primitives are functions, so the proof evaluates them at a probe
state where the first one answers, and reads the head off the answer (`snode_head`); a node that is
not inert names its head the same way (`sprog_head`). -/

section Heads

/-- The primitives of the service of `h`: `ServePrim` and the completion. -/
def SNode (h : BitVec 16) (o : DevOp VirtioState VTask) : Prop :=
  ServePrim h o ∨ ∃ r ui c pa n w, o = idxOp h r ui c pa n w

/-- Every primitive a node of the service of `h` can reach is one of the service's. -/
theorem SProg.nodes {h : BitVec 16} {m : VM Unit} (hm : SProg h m) : PrimsIn (SNode h) m := by
  induction hm with
  | pure => trivial
  | op ho _ ih => exact ⟨Or.inl ho, ih⟩
  | idx hκ =>
    refine ⟨Or.inr ⟨_, _, _, _, _, _, rfl⟩, fun v => ?_⟩
    rw [hκ v]
    trivial

/-- The empty probe: nothing in flight, the latch free, the cache empty. -/
def probe0 : VirtioState := Virtio.initial (fun _ => 0#8)

/-- A configuration in write-back mode. -/
def wceCfg : VirtioCfg := { cfg0 with dfeat := 512#32 }

/-- The probe at which head `h`'s completion-and-push guard answers: `h` in flight and holding the
latch, write-back mode, the cache empty. -/
def probePush (h : BitVec 16) : VirtioState :=
  { probe0 with inflight := [(h, .popped)], taken := some h, cfg := wceCfg }

/-- The probe at which head `h`'s DMA guards for request `r` answer. -/
def probeReq (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) : VirtioState :=
  { probe0 with inflight := [(h, .fetched r)], usedIdx := ui, cfg := c }

/-- Head `h'` in flight at a probe whose only request is head `h` is `h`. -/
theorem head_of_single {h h' : BitVec 16} {ph : VPhase} {v : VirtioState}
    (hv : v.inflight = [(h, ph)]) (h1 : (phase v h').isSome = true) : h = h' := by
  simp only [phase, alistGet, hv, List.find?_cons, List.find?_nil] at h1
  by_cases hh : h = h'
  · exact hh
  · simp [hh] at h1

/-- What a guarded update of the service of `h'` answers: a state whose in-flight map starts with
`h'` (the phase writes, the capture, the push), or the latch taken by `h'` with the in-flight map
unchanged.  The stall never answers. -/
theorem stepHead {h' : BitVec 16} {g : VirtioState → Option (VirtioState × List DevObs)}
    (hb : ServePrim h' (.step g)) {v s : VirtioState} {os : List DevObs}
    (hg : g v = some (s, os)) :
    s.inflight.head?.map Prod.fst = some h' ∨ (s.taken = some h' ∧ s.inflight = v.inflight) := by
  have hm : moves (.step g) v s := ⟨os, hg⟩
  cases hb with
  | stall => exact absurd hm stall_never
  | fetched r | served r | status r =>
    rw [moves_modify] at hm
    subst hm
    left
    simp [setPhase, alistSet]
  | latch =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact Or.inr ⟨rfl, rfl⟩
  | capture r w =>
    rw [moves_modify] at hm
    subst hm
    obtain ⟨cc, e⟩ := captureMove_eq h' r w v
    rw [e]
    left
    simp [setPhase, alistSet]
  | push r =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    left
    simp [setPhase, alistSet]

/-- What a DMA write of the service of `h'` needs to answer: `h'` in flight. -/
theorem dmaHead {h' : BitVec 16} {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} (hb : SNode h' (.dmaWrite g pa n w)) {v s : VirtioState}
    (hg : g v = some s) : (phase v h').isSome = true := by
  rcases hb with hb | ⟨r, ui, c, pa', n', w', he⟩
  · cases hb with
    | fill r pa n w => exact phase_isSome_of_reqOf (reqGuard_some.1 hg).1
    | elem r ui c pa n w => exact phase_isSome_of_reqOf (elemGuard_some.1 hg).1.1
  · cases he
    exact phase_isSome_of_reqOf (idxGuard_some.1 hg).1.1

/-- The completion-and-push guard of `h` answers at its probe. -/
theorem pushGuard_probe (h : BitVec 16) (r : VioReq) :
    pushGuard h r (probePush h) = some (setPhase (probePush h) h (.pushed r)) := by
  refine pushGuard_some.2 ⟨⟨?_, ?_, ?_⟩, rfl⟩
  · simp [phase, alistGet, probePush]
  · unfold completeOk
    split
    · simp [probePush, wce, wceCfg]
    · split
      · simp [probePush, probe0, Virtio.initial]
      · rfl
  · simp [pushOk, probePush, VPhase.isPushed]

/-- A request's record is read off its probe. -/
theorem reqOf_probe (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    reqOf (probeReq h r ui c) h = some r := by
  simp [reqOf, phase, alistGet, probeReq, VPhase.req]

/-- **A primitive of the service that can move the disk names its head.**  Two primitives of the
services of `h` and `h'` that are the same primitive, and not a read or the stall, have
`h = h'`. -/
theorem snode_head {h h' : BitVec 16} {o : DevOp VirtioState VTask} (h1 : SNode h o)
    (h2 : SNode h' o) (hhf : ¬ HFOp o) : h = h' := by
  -- a phase write of `h`, answering at the empty probe with `h` first in flight
  have viaPhase : ∀ {g : VirtioState → Option (VirtioState × List DevObs)} {ph : VPhase}
      {x : VirtioState}, g probe0 = some (setPhase x h ph, []) → x.taken = none →
      SNode h' (.step g) → h = h' := by
    intro g ph x hg hx hb
    rcases hb with hb | ⟨_, _, _, _, _, _, he⟩
    · rcases stepHead hb hg with h3 | ⟨h3, -⟩
      · simpa [setPhase, alistSet] using h3
      · simp [setPhase, hx] at h3
    · cases he
  -- a DMA write of `h`, answering at a probe whose only request is `h`
  have viaDma : ∀ {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat}
      {w : BitVec (8 * n)} {v s : VirtioState} {ph : VPhase}, v.inflight = [(h, ph)] →
      g v = some s → SNode h' (.dmaWrite g pa n w) → h = h' :=
    fun hv hg hb => head_of_single hv (dmaHead hb hg)
  rcases h1 with h1 | ⟨r, ui, c, pa, n, w, rfl⟩
  · cases h1 with
    | get => exact absurd (Or.inl rfl) hhf
    | dmaRead pa n => exact absurd (Or.inr (Or.inl ⟨pa, n, rfl⟩)) hhf
    | stall => exact absurd (Or.inr (Or.inr rfl)) hhf
    | fetched r => exact viaPhase (x := probe0) rfl rfl h2
    | served r => exact viaPhase (x := probe0) rfl rfl h2
    | status r => exact viaPhase (x := probe0) rfl rfl h2
    | capture r w =>
      obtain ⟨cc, e⟩ := captureMove_eq h r w probe0
      exact viaPhase (x := { probe0 with cache := cc }) (ph := .served r) (by simp only [modifyG, e])
        rfl h2
    | latch =>
      rcases h2 with hb | ⟨_, _, _, _, _, _, he⟩
      · have hg : guardG (captureGuard h) probe0 = some ({ probe0 with taken := some h }, []) := by
          simp [guardG, captureGuard, probe0, Virtio.initial]
        rcases stepHead hb hg with h3 | ⟨h3, -⟩
        · simp [probe0, Virtio.initial] at h3
        · exact (Option.some.inj h3)
      · cases he
    | push r =>
      rcases h2 with hb | ⟨_, _, _, _, _, _, he⟩
      · have hg : guardG (pushGuard h r) (probePush h) =
            some (setPhase (probePush h) h (.pushed r), []) := by
          simp [guardG, pushGuard_probe]
        rcases stepHead hb hg with h3 | ⟨h3, -⟩
        · simpa [setPhase, alistSet] using h3
        · simpa [setPhase, probePush] using h3
      · cases he
    | fill r pa n w =>
      exact viaDma (v := probeReq h r 0#16 cfg0) rfl
        (reqGuard_some.2 ⟨reqOf_probe h r _ _, rfl⟩) h2
    | elem r ui c pa n w =>
      exact viaDma (v := probeReq h r ui c) rfl
        (elemGuard_some.2 ⟨⟨reqOf_probe h r _ _, rfl, rfl⟩, rfl⟩) h2
  · exact viaDma (v := probeReq h r ui c) rfl
      (idxGuard_some.2 ⟨⟨reqOf_probe h r _ _, rfl, rfl⟩, rfl⟩) h2

/-- **A node of a service that can move the disk names its head.**  A program that is a node of
the services of `h` and of `h'` and is not inert has `h = h'`. -/
theorem sprog_head {h h' : BitVec 16} {m : VM Unit} (h1 : SProg h m) (h2 : SProg h' m)
    (hni : ¬ Inert m) : h = h' := by
  have key : ∀ {m : VM Unit}, PrimsIn (SNode h) m → PrimsIn (SNode h') m → ¬ Inert m → h = h' := by
    intro m
    induction m with
    | pure a => exact fun _ _ hni => absurd trivial hni
    | op o κ ih =>
      intro p1 p2 hni
      by_cases ho : HFOp o
      · have : ¬ ∀ v, Inert (κ v) := fun hk => hni ⟨ho, hk⟩
        obtain ⟨v, hv⟩ := Classical.not_forall.1 this
        exact ih v (p1.2 v) (p2.2 v) hv
      · exact snode_head p1.1 p2.1 ho
  exact key h1.nodes h2.nodes hni

end Heads

/-! ### The disk's tasks stay at nodes of its programs -/

section Tasks

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- A node of the service of `h` continues at nodes of the service of `h`. -/
theorem SProg.cont {h : BitVec 16} {o : DevOp VirtioState VTask} {κ : o.ret → VM Unit}
    (hm : SProg h (.op o κ)) (v : o.ret) : SProg h (κ v) := by
  cases hm with
  | op _ hκ => exact hκ v
  | idx hκ => rw [hκ v]; exact SProg.pure

/-- A node of the root loop continues at nodes of the root loop. -/
theorem RootProg.cont {oh : Option (BitVec 16)} {o : DevOp VirtioState VTask}
    {κ : o.ret → VM Unit} (hm : RootProg oh (.op o κ)) (v : o.ret) : ∃ oh', RootProg oh' (κ v) := by
  cases hm with
  | op _ hκ => exact ⟨_, hκ v⟩
  | pop hκ => exact ⟨_, hκ v⟩
  | fork hκ => exact ⟨_, hκ v⟩

/-- The root's node right after the pop of `h` is the fork of `h`. -/
theorem RootProg.some_eq {h : BitVec 16} {m : VM Unit} (hm : RootProg (some h) m) :
    ∃ κ, m = .op (.fork (.serve h)) κ ∧ ∀ v, RootProg none (κ v) := by
  cases hm with
  | fork hκ => exact ⟨_, rfl, hκ⟩

/-- A fork is no node at which the root holds no popped head. -/
theorem RootProg.not_fork {t : VTask} {κ : TaskId → VM Unit} (hm : RootProg none (.op (.fork t) κ)) :
    False := by
  cases hm with
  | op hp _ => cases hp

/-- The root holds a popped head at a node or it does not. -/
theorem RootProg.none_some {h : BitVec 16} {m : VM Unit} (h1 : RootProg none m)
    (h2 : RootProg (some h) m) : False := by
  obtain ⟨κ, rfl, -⟩ := h2.some_eq
  exact h1.not_fork

/-- The head the root holds at a node is the node's. -/
theorem RootProg.some_inj {h h' : BitVec 16} {m : VM Unit} (h1 : RootProg (some h) m)
    (h2 : RootProg (some h') m) : h = h' := by
  obtain ⟨κ, rfl, -⟩ := h1.some_eq
  obtain ⟨κ', he, -⟩ := h2.some_eq
  simp only [DevM.op.injEq, DevOp.fork.injEq, VTask.serve.injEq] at he
  exact he.1

/-- **Every disk task is at a node of the disk's programs, within their bounds.**  The root is at a
node of its loop, bounded by `7`; a forked task is at a node of the service of some head,
bounded by `16`. -/
def tasksOk (c : Cfg) : Prop :=
  ∀ (i e : Nat) (tid : TaskId) (m : DevProg .virtio), c.1[i]? = some (Expr.dev e .virtio tid m) →
    (tid = rootTask → (∃ oh, RootProg oh m) ∧ Bounded m 7) ∧
    (tid ≠ rootTask → (∃ h, SProg h m) ∧ Bounded m 16)

/-- **Where a device task after a step comes from**, at any step: an old thread at a position the
step did not write; the stepping task's successor, after a live step of its program or a dead
task's self-loop; the one task a live task at a fork node forked, appended at the end; or a root
a power-on forked, at the end of its (empty) program and of the new generation. -/
theorem dev_step_at {e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d} (hs : Step j c c')
    (hx : c'.1[i]? = some (.dev e d tid m)) :
    (i ≠ j ∧ c.1[i]? = some (.dev e d tid m)) ∨
    (i = j ∧ ∃ m0, c.1[j]? = some (.dev e d tid m0) ∧
      ((threadLive c.2 e ∧ ∃ obs σ' efs, devStep e d tid m0 c.2.m obs m σ' efs ∧
          c'.2 = { c.2 with m := σ' }) ∨
       (¬ threadLive c.2 e ∧ m = m0 ∧ c'.2 = c.2))) ∨
    (i = c.1.length ∧ ∃ tid0 t κ, c.1[j]? = some (.dev e d tid0 (.op (.fork t) κ)) ∧
      threadLive c.2 e ∧ tid = (c.2.m.devrt d).next ∧ m = (devSig d).task t) ∨
    (c.1.length ≤ i ∧ c.1[j]? = some .power ∧ c.2.pow = false ∧ tid = rootTask ∧ m = .pure () ∧
      e = c.2.gen) := by
  rcases get?_step hs hx with ⟨hne, hold⟩ | ⟨rfl, ex, obs, efs, hex, hp⟩ |
    ⟨hlen, ex, obs, e', efs, hex, hp, hnew⟩
  · exact Or.inl ⟨hne, hold⟩
  · cases ex with
    | hart gen cpu m0 =>
      rcases hp with ⟨-, ⟨-, -, m', σ', he', -, -⟩ | ⟨-, -, he', -⟩⟩ <;> cases he'
    | dev gen d0 tid0 m0 =>
      obtain ⟨m', he', hcase⟩ := primStep_dev_succ hp
      simp only [Expr.dev.injEq] at he'
      obtain ⟨rfl, rfl, rfl, hm⟩ := he'
      obtain rfl := eq_of_heq hm
      refine Or.inr (Or.inl ⟨rfl, m0, hex, ?_⟩)
      rcases hcase with ⟨hl, σ', hst, hg'⟩ | ⟨hl, rfl, -, hg'⟩
      · exact Or.inl ⟨hl, obs, σ', efs, hst, hg'⟩
      · exact Or.inr ⟨hl, rfl, hg'⟩
    | power =>
      obtain ⟨he', -⟩ := hp
      cases he'
  · have hxm : Expr.dev e d tid m ∈ efs := List.mem_of_getElem? hnew
    cases ex with
    | hart gen cpu m0 =>
      obtain ⟨rfl, -⟩ := hp
      cases hxm
    | dev gen d0 tid0 m0 =>
      obtain ⟨m', -, hcase⟩ := primStep_dev_succ hp
      rcases hcase with ⟨hl, σ', hst, -⟩ | ⟨-, -, rfl, -⟩
      · obtain ⟨t, κ, rfl, hx', rfl⟩ := devStep_fork hst hxm
        have hi : i - c.1.length = 0 := by
          rcases hk : i - c.1.length with _ | k
          · rfl
          · rw [hk] at hnew
            simp at hnew
        simp only [Expr.dev.injEq] at hx'
        obtain ⟨rfl, rfl, rfl, hm⟩ := hx'
        obtain rfl := eq_of_heq hm
        exact Or.inr (Or.inr (Or.inl ⟨by omega, tid0, t, κ, hex, hl, rfl, rfl⟩))
      · cases hxm
    | power =>
      rcases hp with ⟨-, ⟨-, -, rfl, -⟩ | ⟨hoff, -, rfl, hb⟩⟩
      · cases hxm
      · simp only [powerFork, List.mem_append, List.mem_map] at hxm
        rcases hxm with ⟨cpu, -, hxe⟩ | ⟨d', -, hxe⟩
        · cases hxe
        · simp only [DevLoop, Expr.dev.injEq] at hxe
          obtain ⟨rfl, rfl, rfl, hm⟩ := hxe
          obtain rfl := eq_of_heq hm
          exact Or.inr (Or.inr (Or.inr ⟨hlen, hex, hoff, rfl, rfl, rfl⟩))

/-- A device task's successor at its own position, after its own step. -/
theorem dev_succ {e : Nat} {d : DevId} {tid : TaskId} {m : DevProg d} (hs : Step j c c')
    (hj : c.1[j]? = some (.dev e d tid m)) :
    ∃ m', c'.1[j]? = some (.dev e d tid m') ∧
      ((threadLive c.2 e ∧ ∃ obs σ' efs, devStep e d tid m c.2.m obs m' σ' efs ∧
          c'.2 = { c.2 with m := σ' }) ∨
       (¬ threadLive c.2 e ∧ m' = m ∧ c'.2 = c.2)) := by
  obtain ⟨ex, obs, e', efs, hex, hp, hc'⟩ := hs
  rw [hj] at hex
  obtain rfl := Option.some.inj hex
  have hlt : j < c.1.length := (List.getElem?_eq_some_iff.1 hj).1
  have hi : c'.1[j]? = some e' := by
    rw [hc', List.getElem?_append_left (by simpa using hlt), List.getElem?_set_self hlt]
  obtain ⟨m', rfl, hcase⟩ := primStep_dev_succ hp
  refine ⟨m', hi, ?_⟩
  rcases hcase with ⟨hl, σ', hst, hg'⟩ | ⟨hl, rfl, -, hg'⟩
  · exact Or.inl ⟨hl, obs, σ', efs, hst, hg'⟩
  · exact Or.inr ⟨hl, rfl, hg'⟩

/-- Every step keeps every disk task at a node of the disk's programs, within their bounds. -/
theorem tasksOk_step (hs : Step j c c') (hn : nextOk c) (h : tasksOk c) : tasksOk c' := by
  intro i e tid m hx
  rcases dev_step_at hs hx with ⟨-, hold⟩ | ⟨rfl, m0, hj, hcase⟩ |
    ⟨-, tid0, t, κ, hj, hl, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl, -⟩
  · exact h _ _ _ _ hold
  · obtain ⟨hr, hf⟩ := h _ _ _ _ hj
    rcases hcase with ⟨-, obs, σ', efs, hst, -⟩ | ⟨-, rfl, -⟩
    · cases m0 with
      | pure a =>
        obtain ⟨-, -, ⟨hroot, rfl, -⟩ | ⟨hnr, rfl, -⟩⟩ := hst
        · exact ⟨fun _ => ⟨⟨none, rootProg_body⟩, bounded_arm⟩, fun hn' => absurd hroot hn'⟩
        · obtain ⟨⟨h0, -⟩, -⟩ := hf hnr
          exact ⟨fun h' => absurd h' hnr, fun _ => ⟨⟨h0, SProg.pure⟩, Bounded.pure _ _⟩⟩
      | op o κ =>
        rcases hst with ⟨v, rfl, -⟩ | ⟨-, rfl, -⟩
        · refine ⟨fun hr' => ?_, fun hnr => ?_⟩
          · obtain ⟨⟨oh, hrp⟩, hb⟩ := hr hr'
            exact ⟨hrp.cont v, (hb.cont.2 v).mono (by omega)⟩
          · obtain ⟨⟨h0, hsp⟩, hb⟩ := hf hnr
            exact ⟨⟨h0, hsp.cont v⟩, (hb.cont.2 v).mono (by omega)⟩
        · exact ⟨hr, hf⟩
    · exact ⟨hr, hf⟩
  · refine ⟨fun hr => absurd hr (fork_ne_root hn hj hl), fun _ => ?_⟩
    cases t with
    | serve h' => exact ⟨⟨h', sprog_serve h'⟩, bounded_serve h'⟩
  · exact ⟨fun _ => ⟨⟨none, RootProg.pure⟩, Bounded.pure _ _⟩, fun hn' => absurd rfl hn'⟩

/-- `tasksOk` holds of the boot configuration. -/
theorem tasksOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : tasksOk c := by
  intro i e tid m hx
  rw [h0] at hx
  rcases i with _ | i <;> simp at hx

/-- `tasksOk` holds along every run from the boot configuration. -/
theorem tasksOk_run (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) : ∀ n, tasksOk (σ n) := by
  intro n
  induction n with
  | zero => exact tasksOk_boot h0
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact tasksOk_step hs (nextOk_run hrun h0 n) ih

/-- `progs` holds of the boot configuration. -/
theorem progs_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : progs c := by
  intro i e tid m hx
  rw [h0] at hx
  rcases i with _ | i <;> simp at hx

end Tasks

/-! ### No two live serving tasks for the same head -/

section Owners

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- **The thread at `i` is a live serving task of head `h`**: a forked disk task, live, at a node
of the service of `h` that is not inert.  A finished task and a stalled one are inert and do not
count: neither can ever move the disk again, so neither closes a gate. -/
def servingAt (i : Nat) (h : BitVec 16) (c : Cfg) : Prop :=
  ∃ e tid m, c.1[i]? = some (Expr.dev e .virtio tid m) ∧ threadLive c.2 e ∧ tid ≠ rootTask ∧
    SProg h m ∧ ¬ Inert m

/-- The thread at `i` is the disk's live root at the fork of head `h`, right after the pop of
`h`. -/
def forkingAt (i : Nat) (h : BitVec 16) (c : Cfg) : Prop :=
  ∃ e m, c.1[i]? = some (Expr.dev e .virtio rootTask m) ∧ threadLive c.2 e ∧ RootProg (some h) m

/-- The thread at `i` holds head `h`: it serves it, or it is the root about to fork its service. -/
def ownsAt (i : Nat) (h : BitVec 16) (c : Cfg) : Prop := servingAt i h c ∨ forkingAt i h c

/-- **The ownership invariant.**  Every head has at most one holder, and a held head is in
flight. -/
def ownersOk (c : Cfg) : Prop :=
  (∀ h i i', ownsAt i h c → ownsAt i' h c → i = i') ∧
  (∀ h i, ownsAt i h c → (phase (disk c) h).isSome = true)

/-- The disk after a device step that moved the disk to `s'`. -/
theorem disk_of_setDev {σ' : MState} {s' : VirtioState} (hg' : c'.2 = { c.2 with m := σ' })
    (hσ : σ' = c.2.m.setDev .virtio s') : disk c' = s' := by
  show c'.2.m.devs.st .virtio = s'
  rw [hg', hσ]
  exact DevStates.set_same _ _ _

/-- A primitive of a service keeps every head in flight in flight (the completion is not one). -/
theorem servePrim_phase {h0 h : BitVec 16} {o : DevOp VirtioState VTask} {v v' : VirtioState}
    (hp : ServePrim h0 o) (hm : moves o v v') (hh : (phase v h).isSome = true) :
    (phase v' h).isSome = true := by
  cases hp with
  | get | dmaRead => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched r | served r | status r =>
    rw [moves_modify] at hm
    subst hm
    exact phase_isSome_setPhase hh
  | latch =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact hh
  | capture r w =>
    rw [moves_modify] at hm
    subst hm
    obtain ⟨cc, e⟩ := captureMove_eq h0 r w v
    rw [e]
    exact phase_isSome_setPhase hh
  | push r =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact phase_isSome_setPhase hh
  | fill r pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact hh
  | elem r ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact hh

/-- **What a step does to a head in flight.**  It stays in flight, or the step is the completion
of the head by its serving task, which holds the head no more after it. -/
theorem phase_step (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power)
    (ht : tasksOk c) (hp : progs c) (hR : noBusyReset c c') {h : BitVec 16}
    (hh : (phase (disk c) h).isSome = true) :
    (phase (disk c') h).isSome = true ∨ (servingAt j h c ∧ ¬ ownsAt j h c') := by
  rcases step_cases hs hnp hp with hd | ⟨e, tid, o, k, hj, hl, -, hm⟩ |
    ⟨e, cpu, req, w, tags, k, off, hj, hl, hdec, hw⟩
  · left
    rw [hd]
    exact hh
  · by_cases hr : tid = rootTask
    · subst hr
      obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
      left
      cases hrp with
      | op hpr _ =>
        cases hpr with
        | get | choose | dmaRead => exact hm.elim
        | drain j' =>
          rw [moves_modify] at hm
          rw [hm]
          rcases drain_eq (disk c) ((disk c).cache.getD j' (0, [])).1 with e' | ⟨dk, e'⟩ <;>
            rw [drainMove, e'] <;> exact hh
      | pop _ =>
        rw [moves_guard, popGuard_some] at hm
        obtain ⟨-, hm⟩ := hm
        rw [hm]
        exact phase_isSome_setPhase hh
      | fork _ => exact hm.elim
    · obtain ⟨⟨h0, hsp⟩, -⟩ := (ht _ _ _ _ hj).2 hr
      cases hsp with
      | op hsp' _ => exact Or.inl (servePrim_phase hsp' hm hh)
      | @idx r ui cf pa n w κ hκ =>
        have hm' : idxGuard h0 r ui cf (disk c) = some (disk c') := hm
        obtain ⟨-, hm'⟩ := idxGuard_some.1 hm'
        by_cases hh0 : h0 = h
        · subst hh0
          obtain ⟨m', hj', hcase⟩ := dev_succ hs hj
          rcases hcase with ⟨-, obs, σ', efs, hst, hg'⟩ | ⟨hd, -⟩
          · rcases hst with ⟨v, rfl, -⟩ | ⟨-, -, hσ, -, -⟩
            · right
              refine ⟨⟨e, tid, _, hj, hl, hr, SProg.idx hκ, ?_⟩, ?_⟩
              · rintro ⟨hf, -⟩
                rcases hf with h1 | ⟨_, _, h1⟩ | h1 <;> cases h1
              · rintro (⟨e', tid', m'', hx, -, -, -, hni⟩ | ⟨e', m'', hx, -, -⟩)
                · rw [hj'] at hx
                  obtain ⟨-, -, -, hm⟩ := Expr.dev.inj (Option.some.inj hx)
                  rw [← eq_of_heq hm, hκ v] at hni
                  exact hni trivial
                · rw [hj'] at hx
                  obtain ⟨-, -, htid, -⟩ := Expr.dev.inj (Option.some.inj hx)
                  exact hr htid
            · left
              have : disk c' = disk c := by
                show c'.2.m.devs.st .virtio = c.2.m.devs.st .virtio
                rw [hg', hσ]
              rw [this]
              exact hh
          · exact absurd hl hd
        · left
          rw [hm', phase_complete_ne (Ne.symm hh0)]
          exact hh
  · left
    obtain ⟨-, cfg, isr, hc'⟩ := mmio_cases hs hj hl hdec hw hR (inflight_ne_nil hh)
    rw [hc']
    exact hh

/-- **Where a holder after a step comes from.**  At a step of a thread that is not the power
thread, a holder of `h` after the step held `h` before it, or it is the root that just popped `h`
(which was not in flight, and is now), or it is the serving task the root just forked for `h`,
appended at the end (the step moves no disk state, and the root holds `h` no more). -/
theorem ownsAt_back (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power)
    (hn : nextOk c) (ht : tasksOk c) {h : BitVec 16} (ho : ownsAt i h c') :
    ownsAt i h c ∨
    (i = j ∧ (phase (disk c) h).isSome = false ∧ (phase (disk c') h).isSome = true ∧
      ∃ e κ, c.1[j]? = some (.dev e .virtio rootTask (.op (popOp h) κ))) ∨
    (i = c.1.length ∧ forkingAt j h c ∧ disk c' = disk c ∧ ¬ ownsAt j h c') := by
  have hlive : ∀ e, threadLive c'.2 e ↔ threadLive c.2 e := Era.threadLive_of_step hs hnp
  rcases ho with ⟨e, tid, m, hx, hl, hnr, hsp, hni⟩ | ⟨e, m, hx, hl, hrp⟩
  · rcases dev_step_at hs hx with ⟨-, hold⟩ | ⟨rfl, m0, hj, hcase⟩ |
      ⟨rfl, tid0, t, κ, hj, hlj, rfl, rfl⟩ | ⟨-, hpw, -⟩
    · exact Or.inl (Or.inl ⟨e, tid, m, hold, (hlive e).1 hl, hnr, hsp, hni⟩)
    · have hl0 := (hlive e).1 hl
      rcases hcase with ⟨-, obs, σ', efs, hst, -⟩ | ⟨hd, -, -⟩
      · cases m0 with
        | pure a =>
          obtain ⟨-, -, ⟨hroot, -, -⟩ | ⟨-, rfl, -⟩⟩ := hst
          · exact absurd hroot hnr
          · exact absurd trivial hni
        | op o κ =>
          rcases hst with ⟨v, rfl, -⟩ | ⟨-, rfl, -⟩
          · obtain ⟨⟨h0, hsp0⟩, -⟩ := (ht _ _ _ _ hj).2 hnr
            have hh : h = h0 := sprog_head hsp (hsp0.cont v) hni
            subst hh
            exact Or.inl (Or.inl ⟨e, tid, _, hj, hl0, hnr, hsp0, fun hin => hni (hin.2 v)⟩)
          · exact Or.inl (Or.inl ⟨e, tid, _, hj, hl0, hnr, hsp, hni⟩)
      · exact absurd hl0 hd
    · -- the task the root just forked
      by_cases hr0 : tid0 = rootTask
      · subst hr0
        obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
        cases hrp with
        | op hp _ => cases hp
        | @fork h' κ hκ =>
          have hh : h' = h := sprog_head (sprog_serve h') hsp hni
          subst hh
          obtain ⟨m', hj', hcase⟩ := dev_succ hs hj
          rcases hcase with ⟨-, obs, σ', efs, hst, hg'⟩ | ⟨hd, -⟩
          · rcases hst with ⟨v, rfl, hop⟩ | ⟨hb, -⟩
            · obtain ⟨-, -, hσ, -⟩ := hop
              refine Or.inr (Or.inr ⟨rfl, ⟨e, _, hj, hlj, RootProg.fork hκ⟩, ?_, ?_⟩)
              · show c'.2.m.devs.st .virtio = c.2.m.devs.st .virtio
                rw [hg', hσ]
              · rintro (⟨e', tid', m'', hx', -, hnr', -, -⟩ | ⟨e', m'', hx', -, hrp'⟩)
                · rw [hj'] at hx'
                  obtain ⟨-, -, htid, -⟩ := Expr.dev.inj (Option.some.inj hx')
                  exact hnr' htid.symm
                · rw [hj'] at hx'
                  obtain ⟨-, -, -, hm⟩ := Expr.dev.inj (Option.some.inj hx')
                  rw [← eq_of_heq hm] at hrp'
                  exact (hκ v).none_some hrp'
            · exact hb.elim
          · exact absurd hlj hd
      · obtain ⟨⟨h0, hsp0⟩, -⟩ := (ht _ _ _ _ hj).2 hr0
        cases hsp0 with
        | op hp _ => cases hp
    · exact absurd hpw (hnp _ · rfl)
  · rcases dev_step_at hs hx with ⟨-, hold⟩ | ⟨rfl, m0, hj, hcase⟩ |
      ⟨rfl, tid0, t, κ, hj, hlj, hid, -⟩ | ⟨-, hpw, -⟩
    · exact Or.inl (Or.inr ⟨e, m, hold, (hlive e).1 hl, hrp⟩)
    · have hl0 := (hlive e).1 hl
      rcases hcase with ⟨-, obs, σ', efs, hst, hg'⟩ | ⟨hd, -, -⟩
      · cases m0 with
        | pure a =>
          obtain ⟨-, -, ⟨-, rfl, -⟩ | ⟨hnr, -, -⟩⟩ := hst
          · exact absurd hrp (fun h2 => rootProg_body.none_some h2)
          · exact absurd rfl hnr
        | op o κ =>
          rcases hst with ⟨v, rfl, hop⟩ | ⟨-, rfl, -⟩
          · obtain ⟨⟨oh, hrp0⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
            cases hrp0 with
            | op _ hκ => exact absurd hrp (hκ v).none_some
            | @pop h' κ hκ =>
              have hh : h' = h := (hκ v).some_inj hrp
              subst hh
              obtain ⟨s', os, hgd, -, hσ, -⟩ := hop
              have hd := disk_of_setDev hg' hσ
              obtain ⟨hnone, rfl⟩ := popGuard_some.1 (moves_guard.1 ⟨os, hgd⟩)
              refine Or.inr (Or.inl ⟨rfl, hnone, ?_, e, κ, hj⟩)
              rw [hd]
              show (phase (setPhase (disk c) h' .popped) h').isSome = true
              rw [phase_setPhase_self]
              rfl
            | fork hκ => exact absurd hrp (hκ v).none_some
          · exact Or.inl (Or.inr ⟨e, _, hj, hl0, hrp⟩)
      · exact absurd hl0 hd
    · exact absurd hid.symm (fork_ne_root hn hj hlj)
    · exact absurd hpw (hnp _ · rfl)

/-- No thread holds a head right after a power step: a power-off kills every thread, a power-on
kills the old ones and forks roots at the end of their (empty) programs. -/
theorem not_ownsAt_power (hs : Step j c c') (hpw : c.1[j]? = some .power) (hg : genOk c)
    {h : BitVec 16} : ¬ ownsAt i h c' := by
  have key : ∀ {e tid} {m : DevProg .virtio}, c'.1[i]? = some (.dev e .virtio tid m) →
      threadLive c'.2 e → tid = rootTask ∧ m = .pure () := by
    intro e tid m hx hl
    rcases dev_step_at hs hx with ⟨-, hold⟩ | ⟨rfl, m0, hj, -⟩ | ⟨-, tid0, t, κ, hj, -⟩ |
      ⟨-, -, -, hr, hm, -⟩
    · rcases power_step hs hpw with ⟨-, hoff, -⟩ | ⟨hoff, hb, -⟩
      · rw [hl.1] at hoff
        cases hoff
      · have h1 := (hg i e (by simp [Era.genAt, hold, Era.Expr.gen?])).2 hoff
        have h2 := hl.2
        have h3 := hb.1
        omega
    · rw [hpw] at hj
      cases hj
    · rw [hpw] at hj
      cases hj
    · exact ⟨hr, hm⟩
  rintro (⟨e, tid, m, hx, hl, hnr, -, -⟩ | ⟨e, m, hx, hl, hrp⟩)
  · exact hnr (key hx hl).1
  · obtain ⟨κ, hm, -⟩ := hrp.some_eq
    rw [(key hx hl).2] at hm
    cases hm

/-- Every step keeps the ownership invariant, given the bookkeeping invariants and no busy reset
at the step. -/
theorem ownersOk_step (hs : Step j c c') (hg : genOk c) (hn : nextOk c) (ht : tasksOk c)
    (hp : progs c) (hR : noBusyReset c c') (h : ownersOk c) : ownersOk c' := by
  by_cases hpw : c.1[j]? = some .power
  · exact ⟨fun _ _ _ ho => absurd ho (not_ownsAt_power hs hpw hg),
      fun _ _ ho => absurd ho (not_ownsAt_power hs hpw hg)⟩
  have hnp : ∀ e, c.1[j]? = some e → e ≠ .power := fun e he hep => hpw (hep ▸ he)
  -- the root at a pop node is not at a fork node
  have popFork : ∀ {h e κ}, c.1[j]? = some (.dev e .virtio rootTask (.op (popOp h) κ)) →
      ¬ forkingAt j h c := by
    rintro h e κ hj ⟨e', m, hj', -, hrp⟩
    obtain ⟨κ', rfl, -⟩ := hrp.some_eq
    rw [hj] at hj'
    obtain ⟨-, -, -, hm⟩ := Expr.dev.inj (Option.some.inj hj')
    have := eq_of_heq hm
    cases this
  refine ⟨fun hh i i' ho ho' => ?_, fun hh i ho => ?_⟩
  · rcases ownsAt_back hs hnp hn ht ho with ho1 | ⟨rfl, hn1, -, e1, κ1, hj1⟩ |
      ⟨rfl, hf1, -, hno1⟩ <;>
    rcases ownsAt_back hs hnp hn ht ho' with ho2 | ⟨rfl, hn2, -, e2, κ2, hj2⟩ |
      ⟨rfl, hf2, -, hno2⟩
    · exact h.1 _ _ _ ho1 ho2
    · rw [h.2 _ _ ho1] at hn2
      cases hn2
    · obtain rfl := h.1 _ _ _ ho1 (Or.inr hf2)
      exact absurd ho hno2
    · rw [h.2 _ _ ho2] at hn1
      cases hn1
    · rfl
    · exact absurd hf2 (popFork hj1)
    · obtain rfl := h.1 _ _ _ ho2 (Or.inr hf1)
      exact absurd ho' hno1
    · exact absurd hf1 (popFork hj2)
    · rfl
  · rcases ownsAt_back hs hnp hn ht ho with ho1 | ⟨rfl, -, hs1, -⟩ | ⟨rfl, hf1, hd, -⟩
    · rcases phase_step hs hnp ht hp hR (h.2 _ _ ho1) with h1 | ⟨hsj, hnj⟩
      · exact h1
      · obtain rfl := h.1 _ _ _ ho1 (Or.inl hsj)
        exact absurd ho hnj
    · exact hs1
    · rw [hd]
      exact h.2 _ _ (Or.inr hf1)

/-- The ownership invariant holds of the boot configuration. -/
theorem ownersOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) : ownersOk c := by
  have hno : ∀ h i, ¬ ownsAt i h c := by
    rintro h i (⟨e, tid, m, hx, -⟩ | ⟨e, m, hx, -⟩) <;> rw [h0] at hx <;>
      rcases i with _ | i <;> simp at hx
  exact ⟨fun _ _ _ ho => absurd ho (hno _ _), fun _ _ ho => absurd ho (hno _ _)⟩

/-- The ownership invariant holds along every run from the boot configuration with no busy
reset. -/
theorem ownersOk_run (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ) :
    ∀ n, ownersOk (σ n) := by
  intro n
  induction n with
  | zero => exact ownersOk_boot h0
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact ownersOk_step hs (genOk_run hrun h0 n) (nextOk_run hrun h0 n) (tasksOk_run hrun h0 n)
      (progs_run hrun (progs_boot h0) n) (hR n) ih

/-- **No two live serving tasks for the same head.**  On a run from the boot configuration with no
busy reset, two live serving tasks of the same head are the same thread.  The root puts a head in
flight only when it is not (the pop guard), forks one service for it, and no serving task forks;
the head leaves the map only at its serving task's completion, the task's last step.  A busy reset
would break this: it empties the in-flight map while the serving tasks live on, and once the
driver has set the disk up again the root can pop the same head a second time. -/
theorem oneServer (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ) :
    ∀ n h i i', servingAt i h (σ n) → servingAt i' h (σ n) → i = i' :=
  fun n h i i' h1 h2 => (ownersOk_run hrun h0 hR n).1 h i i' (Or.inl h1) (Or.inl h2)

/-- **A live serving task's head is in flight**, on a run from the boot configuration with no busy
reset. -/
theorem inflight_of_serving (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power])
    (hR : NoBusyReset σ) :
    ∀ n h i, servingAt i h (σ n) → (phase (disk (σ n)) h).isSome = true :=
  fun n h i h1 => (ownersOk_run hrun h0 hR n).2 h i (Or.inl h1)

end Owners

/-! ### Who can be at a closing node

Every closing class of `Gates.lean` (the latch, the capture, the push, the phase writes of a head,
the used-index write) is a primitive of the service: the root never runs one, and an inert task
is never at one.  So a closer is a live serving task, of the head its node names. -/

section Closers

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The primitives of the root loop, the pop and the fork included. -/
def RootOp (o : DevOp VirtioState VTask) : Prop :=
  RootPrim o ∨ (∃ h, o = popOp h) ∨ (∃ t, o = .fork t)

/-- The primitives of `Gates.lean`'s closing classes, but the pop. -/
def Closer (o : DevOp VirtioState VTask) : Prop :=
  isLatch o ∨ isCapture o ∨ isPush o ∨ isUsedIdx o ∨ (∃ h, servesHead h o) ∨ (∃ h, pushesHead h o)

/-- The probe tactic: evaluate both sides of an equation between two guarded updates at the empty
probe or at a push probe, and read off a contradiction. -/
macro "probe_contra" hg:ident : tactic => `(tactic| first
  | (have hp := congrFun $hg probe0
     simp [modifyG, guardG, drainMove, drain, popGuard, captureGuard, pushGuard, captureMove,
       setPhase, alistSet, alistGet, phase, reqOf, probe0, Virtio.initial, stallG] at hp
     done))

/-- A primitive of the root loop is no closer. -/
theorem rootOp_not_closer {o : DevOp VirtioState VTask} (hr : RootOp o) : ¬ Closer o := by
  intro hc
  rcases hr with hr | ⟨h', rfl⟩ | ⟨t, rfl⟩
  · cases hr
    all_goals
      rcases hc with ⟨h, he⟩ | ⟨h, r, w, he⟩ | ⟨h, r, he⟩ | ⟨h, r, ui, cf, pa, n, w, he⟩ |
        ⟨h, ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, w, he⟩⟩ | ⟨h, r, he⟩
      all_goals
        first
        | (cases he; done)
        | (injection he with hg; probe_contra hg)
  all_goals
    rcases hc with ⟨h, he⟩ | ⟨h, r, w, he⟩ | ⟨h, r, he⟩ | ⟨h, r, ui, cf, pa, n, w, he⟩ |
      ⟨h, ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, w, he⟩⟩ | ⟨h, r, he⟩
    all_goals
      first
      | (cases he; done)
      | (injection he with hg; probe_contra hg)

/-- A read of the state, a DMA read or the stall is no closer. -/
theorem hfOp_not_closer {o : DevOp VirtioState VTask} (hf : HFOp o) : ¬ Closer o := by
  intro hc
  rcases hf with rfl | ⟨pa, n, rfl⟩ | rfl <;>
  rcases hc with ⟨h, he⟩ | ⟨h, r, w, he⟩ | ⟨h, r, he⟩ | ⟨h, r, ui, cf, pa, n, w, he⟩ |
    ⟨h, ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, he⟩ | ⟨r, w, he⟩⟩ | ⟨h, r, he⟩ <;>
  first
  | (cases he; done)
  | (injection he with hg; probe_contra hg)
  | (injection he with hg
     have hp := congrFun hg (probePush h)
     simp [guardG, stallG, pushGuard_probe] at hp
     done)

/-- A primitive of the service that is not a read of the state, a DMA read or the stall leaves its
task's program not inert. -/
theorem not_inert_of_op {o : DevOp VirtioState VTask} {κ : o.ret → VM Unit} (ho : ¬ HFOp o) :
    ¬ Inert (.op o κ) :=
  fun h => ho h.1

/-- **A closer is a live serving task.**  A live disk task at a closing node is a forked task, it
serves some head, and its node is a primitive of that head's service. -/
theorem closer_serving (ht : tasksOk c) {e : Nat} {tid : TaskId} {o : DevOp VirtioState VTask}
    {k : o.ret → VM Unit} (hj : c.1[j]? = some (.dev e .virtio tid (.op o k)))
    (hl : threadLive c.2 e) (hc : Closer o) :
    tid ≠ rootTask ∧ ∃ h0, servingAt j h0 c ∧ SNode h0 o := by
  by_cases hr : tid = rootTask
  · subst hr
    obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
    exfalso
    refine rootOp_not_closer ?_ hc
    cases hrp with
    | op hp _ => exact Or.inl hp
    | pop _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | fork _ => exact Or.inr (Or.inr ⟨_, rfl⟩)
  · obtain ⟨⟨h0, hsp⟩, -⟩ := (ht _ _ _ _ hj).2 hr
    have hno : ¬ HFOp o := fun hf => hfOp_not_closer hf hc
    refine ⟨hr, h0, ⟨e, tid, _, hj, hl, hr, hsp, not_inert_of_op hno⟩, ?_⟩
    exact hsp.nodes.1

/-- A live forked disk task at a primitive of the service of `h` that can move the disk serves
`h`. -/
theorem servingAt_of_node (ht : tasksOk c) {e : Nat} {tid : TaskId} {o : DevOp VirtioState VTask}
    {k : o.ret → VM Unit} {h : BitVec 16} (hj : c.1[j]? = some (.dev e .virtio tid (.op o k)))
    (hl : threadLive c.2 e) (hr : tid ≠ rootTask) (ho : SNode h o) (hno : ¬ HFOp o) :
    servingAt j h c := by
  obtain ⟨⟨h0, hsp⟩, -⟩ := (ht _ _ _ _ hj).2 hr
  obtain rfl := snode_head hsp.nodes.1 ho hno
  exact ⟨e, tid, _, hj, hl, hr, hsp, not_inert_of_op hno⟩

/-- The latch node is no read and no stall. -/
theorem latch_not_hf {h : BitVec 16} : ¬ HFOp (latchOp h) :=
  fun hf => hfOp_not_closer hf (Or.inl ⟨h, rfl⟩)

/-- The completion-and-push node is no read and no stall. -/
theorem push_not_hf {h : BitVec 16} {r : VioReq} : ¬ HFOp (pushOp h r) :=
  fun hf => hfOp_not_closer hf (Or.inr (Or.inr (Or.inl ⟨h, r, rfl⟩)))

/-- A DMA write is no read and no stall. -/
theorem dma_not_hf {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} : ¬ HFOp (.dmaWrite g pa n w) := by
  rintro (h | ⟨_, _, h⟩ | h) <;> cases h

/-- A task waiting at a node of the service of `h` other than a read or the stall is a forked
task: the root runs no such node. -/
theorem not_root_of_node (ht : tasksOk c) {e : Nat} {tid : TaskId} {o : DevOp VirtioState VTask}
    {k : o.ret → VM Unit} {h : BitVec 16} (hj : c.1[j]? = some (.dev e .virtio tid (.op o k)))
    (hc : Closer o) : tid ≠ rootTask := by
  intro hr
  subst hr
  obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
  refine rootOp_not_closer ?_ hc
  cases hrp with
  | op hp _ => exact Or.inl hp
  | pop _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | fork _ => exact Or.inr (Or.inr ⟨_, rfl⟩)

end Closers

/-! ## 5. The capture latch

"Past the latch" means the program positions of a write request's service after its latch guard
answered: the capture's DMA read of the payload, the capture, the status byte, the status phase
write, the completion-and-push guard, the snapshot read, the used element and the used index
(`PostLatch`; `sprogL_serve` checks that these are the nodes `serve h` reaches through its latch).
A task past the latch of `h` serves `h`, so it is unique (`latchHolder_unique`), and the latch is
held only by a head in flight (`latch_inflight`). -/

section Latch

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- **The nodes past the latch of head `h`**, for a write request `r`: the capture's read of the
payload, the capture, the status byte, the status phase write, the completion-and-push guard,
the snapshot read, the used element, and the used index last. -/
inductive PostLatch (h : BitVec 16) : VM Unit → Prop
  | read {r : VioReq} {κ : BitVec (8 * r.len.toNat) → VM Unit} : r.type.toNat = blkTOut →
      (∀ w, PostLatch h (κ w)) → PostLatch h (.op (.dmaRead r.buf r.len.toNat) κ)
  | capture {r : VioReq} {w : BitVec (8 * r.len.toNat)} {κ : Unit → VM Unit} :
      r.type.toNat = blkTOut → (∀ v, PostLatch h (κ v)) →
      PostLatch h (.op (.step (modifyG (captureMove h r w))) κ)
  | statusByte {r : VioReq} {κ : Unit → VM Unit} : r.type.toNat = blkTOut →
      (∀ v, PostLatch h (κ v)) → PostLatch h (.op (.dmaWrite (reqGuard h r) r.status 1 (statusOf r)) κ)
  | status {r : VioReq} {κ : Unit → VM Unit} : r.type.toNat = blkTOut → (∀ v, PostLatch h (κ v)) →
      PostLatch h (.op (.step (modifyG fun v => setPhase v h (.status r))) κ)
  | push {r : VioReq} {κ : Unit → VM Unit} : r.type.toNat = blkTOut → (∀ v, PostLatch h (κ v)) →
      PostLatch h (.op (pushOp h r) κ)
  | snap {κ : VirtioState → VM Unit} : (∀ v, PostLatch h (κ v)) → PostLatch h (.op .get κ)
  | elem {r : VioReq} {ui : BitVec 16} {cf : VirtioCfg} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
      {κ : Unit → VM Unit} : r.type.toNat = blkTOut → (∀ v, PostLatch h (κ v)) →
      PostLatch h (.op (.dmaWrite (elemGuard h r ui cf) pa n w) κ)
  | idx {r : VioReq} {ui : BitVec 16} {cf : VirtioCfg} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
      {κ : Unit → VM Unit} : (∀ v, κ v = .pure ()) → PostLatch h (.op (idxOp h r ui cf pa n w) κ)

/-- The primitives of the service of `h` other than the latch and the completion. -/
inductive ServePrimNL (h : BitVec 16) : DevOp VirtioState VTask → Prop
  | get : ServePrimNL h .get
  | dmaRead (pa : PAddr) (n : Nat) : ServePrimNL h (.dmaRead pa n)
  | stall : ServePrimNL h (.step stallG)
  | fetched (r : VioReq) : ServePrimNL h (.step (modifyG fun v => setPhase v h (.fetched r)))
  | served (r : VioReq) : ServePrimNL h (.step (modifyG fun v => setPhase v h (.served r)))
  | status (r : VioReq) : ServePrimNL h (.step (modifyG fun v => setPhase v h (.status r)))
  | push (r : VioReq) : ServePrimNL h (pushOp h r)
  | fill (r : VioReq) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
      ServePrimNL h (.dmaWrite (reqGuard h r) pa n w)
  | elem (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
      ServePrimNL h (.dmaWrite (elemGuard h r ui c) pa n w)

/-- The nodes of the service of `h` in which every latch node continues past the latch. -/
inductive SProgL (h : BitVec 16) : VM Unit → Prop
  | pure : SProgL h (.pure ())
  | op {o : DevOp VirtioState VTask} {κ : o.ret → VM Unit} :
      ServePrimNL h o → (∀ v, SProgL h (κ v)) → SProgL h (.op o κ)
  | idx {r : VioReq} {ui : BitVec 16} {c : VirtioCfg} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
      {κ : Unit → VM Unit} : (∀ v, κ v = .pure ()) → SProgL h (.op (idxOp h r ui c pa n w) κ)
  | latch {κ : Unit → VM Unit} : (∀ v, PostLatch h (κ v)) → SProgL h (.op (latchOp h) κ)

/-- DMA reads followed by nodes of `SProgL h` are nodes of `SProgL h`. -/
theorem SProgL.bind_reads {h : BitVec 16} {α : Type} {m : VM α} {f : α → VM Unit}
    (hm : PrimsIn IsRead m) (hf : ∀ x, SProgL h (f x)) : SProgL h (m >>= f) := by
  induction m with
  | pure a => exact hf a
  | op o κ ih =>
    obtain ⟨⟨pa, n, rfl⟩, hκ⟩ := hm
    exact SProgL.op (ServePrimNL.dmaRead pa n) fun v => ih v (hκ v)

/-- The step of the post-latch tactic. -/
macro "postlatch_step" : tactic => `(tactic| first
  | (intro _)
  | exact SProgL.pure
  | (apply SProgL.idx; intro _; rfl)
  | (apply PostLatch.idx; intro _; rfl)
  | (apply SProgL.latch)
  | (apply PostLatch.read; assumption)
  | (apply PostLatch.capture; assumption)
  | (apply PostLatch.statusByte; assumption)
  | (apply PostLatch.status; assumption)
  | (apply PostLatch.push; assumption)
  | (apply PostLatch.snap)
  | (apply PostLatch.elem; assumption)
  | exact ServePrimNL.get
  | exact ServePrimNL.dmaRead _ _
  | exact ServePrimNL.stall
  | exact ServePrimNL.fetched _
  | exact ServePrimNL.served _
  | exact ServePrimNL.status _
  | exact ServePrimNL.push _
  | exact ServePrimNL.fill _ _ _ _
  | exact ServePrimNL.elem _ _ _ _ _ _
  | (apply SProgL.op)
  | split
  | (dsimp only [DevM.bind])
  | (simp only [bind_pure_eq])
  | (dsimp only))

/-- **The service of `h` reaches only post-latch nodes through its latch.** -/
theorem sprogL_serve (h : BitVec 16) : SProgL h (serve h) := by
  unfold serve
  refine SProgL.op ServePrimNL.get fun v => ?_
  dsimp only [DevM.bind]
  refine SProgL.bind_reads (reads_fetch _ _) fun x => ?_
  repeat postlatch_step

/-- A node past the latch of `h` is a node of the service of `h`. -/
theorem PostLatch.sprog {h : BitVec 16} {m : VM Unit} (hm : PostLatch h m) : SProg h m := by
  induction hm with
  | read _ _ ih => exact SProg.op (ServePrim.dmaRead _ _) ih
  | capture _ _ ih => exact SProg.op (ServePrim.capture _ _) ih
  | statusByte _ _ ih => exact SProg.op (ServePrim.fill _ _ _ _) ih
  | status _ _ ih => exact SProg.op (ServePrim.status _) ih
  | push _ _ ih => exact SProg.op (ServePrim.push _) ih
  | snap _ ih => exact SProg.op ServePrim.get ih
  | elem _ _ ih => exact SProg.op (ServePrim.elem _ _ _ _ _ _) ih
  | idx hκ => exact SProg.idx hκ

/-- A node past the latch can still move the disk: it is not inert. -/
theorem PostLatch.not_inert {h : BitVec 16} {m : VM Unit} (hm : PostLatch h m) : ¬ Inert m := by
  induction hm with
  | read _ _ ih => exact fun hi => ih 0 (hi.2 0)
  | @capture r w κ _ _ _ =>
    exact not_inert_of_op fun hf => hfOp_not_closer hf (Or.inr (Or.inl ⟨h, r, w, rfl⟩))
  | statusByte _ _ _ => exact not_inert_of_op dma_not_hf
  | @status r κ _ _ _ =>
    exact not_inert_of_op fun hf => hfOp_not_closer hf
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))⟩)))))
  | push _ _ _ => exact not_inert_of_op push_not_hf
  | snap _ ih => exact fun hi => ih probe0 (hi.2 probe0)
  | elem _ _ _ => exact not_inert_of_op dma_not_hf
  | idx _ => exact not_inert_of_op dma_not_hf

/-- The thread at `i` is a live forked disk task past the latch of `h`. -/
def latchedAt (i : Nat) (h : BitVec 16) (c : Cfg) : Prop :=
  ∃ e tid m, c.1[i]? = some (Expr.dev e .virtio tid m) ∧ threadLive c.2 e ∧ tid ≠ rootTask ∧
    PostLatch h m

/-- A task past the latch of `h` serves `h`. -/
theorem servingAt_of_latched {h : BitVec 16} (hl : latchedAt i h c) : servingAt i h c :=
  let ⟨e, tid, m, hx, hlv, hr, hp⟩ := hl
  ⟨e, tid, m, hx, hlv, hr, hp.sprog, hp.not_inert⟩

/-- **The latch's holder is unique.**  On a run from the boot configuration with no busy reset, two
live tasks past the latch of the same head are the same thread, and that head is in flight. -/
theorem latchHolder_unique (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ) :
    ∀ n h i i', latchedAt i h (σ n) → latchedAt i' h (σ n) →
      i = i' ∧ (phase (disk (σ n)) h).isSome = true :=
  fun n h i i' h1 h2 =>
    ⟨oneServer hrun h0 hR n h i i' (servingAt_of_latched h1) (servingAt_of_latched h2),
      inflight_of_serving hrun h0 hR n h i (servingAt_of_latched h1)⟩

/-- The latch is held only by a head in flight. -/
def latchOk (c : Cfg) : Prop := ∀ h, (disk c).taken = some h → (phase (disk c) h).isSome = true

/-- Every step keeps the latch held only by a head in flight, given the other invariants. -/
theorem latchOk_step (hs : Step j c c') (ht : tasksOk c) (hp : progs c) (ho : ownersOk c)
    (h : latchOk c) : latchOk c' := by
  intro hh htk
  by_cases hpw : c.1[j]? = some .power
  · obtain ⟨ex, obs, e', efs, hex, hpr, -⟩ := hs
    rw [hpw] at hex
    obtain rfl := Option.some.inj hex
    rcases hpr with ⟨-, ⟨-, -, -, hg'⟩ | ⟨-, -, -, hb⟩⟩
    · -- a power-off leaves the machine as it was
      have hd : disk c' = disk c := by
        show c'.2.m.devs.st .virtio = c.2.m.devs.st .virtio
        rw [hg']
      rw [hd] at htk ⊢
      exact h hh htk
    · -- a power-on resets the disk: the latch is free
      have hd : disk c' = Virtio.reset (disk c) := by
        show c'.2.m.devs.st .virtio = _
        rw [hb.2.2.2]
        rfl
      rw [hd] at htk
      cases htk
  have hnp : ∀ e, c.1[j]? = some e → e ≠ .power := fun e he hep => hpw (hep ▸ he)
  rcases step_cases hs hnp hp with hd | ⟨e, tid, o, k, hj, hl, -, hm⟩ |
    ⟨e, cpu, req, w, tags, k, off, hj, hl, hdec, hw⟩
  · rw [hd] at htk ⊢
    exact h hh htk
  · by_cases hr : tid = rootTask
    · subst hr
      obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
      cases hrp with
      | op hpr _ =>
        cases hpr with
        | get | choose | dmaRead => exact hm.elim
        | drain j' =>
          rw [moves_modify] at hm
          rw [hm] at htk ⊢
          rcases drain_eq (disk c) ((disk c).cache.getD j' (0, [])).1 with e' | ⟨dk, e'⟩ <;>
            rw [drainMove, e'] at htk ⊢ <;> exact h hh htk
      | pop _ =>
        rw [moves_guard, popGuard_some] at hm
        obtain ⟨-, hm⟩ := hm
        rw [hm] at htk ⊢
        exact phase_isSome_setPhase (h hh htk)
      | fork _ => exact hm.elim
    · obtain ⟨⟨h0, hsp⟩, -⟩ := (ht _ _ _ _ hj).2 hr
      cases hsp with
      | op hsp' _ =>
        cases hsp' with
        | get | dmaRead => exact hm.elim
        | stall => exact absurd hm stall_never
        | fetched r | served r | status r =>
          rw [moves_modify] at hm
          rw [hm] at htk ⊢
          exact phase_isSome_setPhase (h hh htk)
        | latch =>
          rw [moves_guard, captureGuard_some] at hm
          obtain ⟨-, hm⟩ := hm
          rw [hm] at htk ⊢
          obtain rfl := Option.some.inj htk
          have hs0 : servingAt j h0 c :=
            ⟨e, tid, _, hj, hl, hr, SProg.op ServePrim.latch ‹_›, not_inert_of_op latch_not_hf⟩
          exact ho.2 _ _ (Or.inl hs0)
        | capture r w =>
          rw [moves_modify] at hm
          obtain ⟨cc, e'⟩ := captureMove_eq h0 r w (disk c)
          rw [hm, e'] at htk ⊢
          exact phase_isSome_setPhase (h hh htk)
        | push r =>
          rw [moves_guard, pushGuard_some] at hm
          obtain ⟨-, hm⟩ := hm
          rw [hm] at htk ⊢
          exact phase_isSome_setPhase (h hh htk)
        | fill r pa n w =>
          obtain ⟨-, hm⟩ := reqGuard_some.1 hm
          rw [hm] at htk ⊢
          exact h hh htk
        | elem r ui cf pa n w =>
          obtain ⟨-, hm⟩ := elemGuard_some.1 hm
          rw [hm] at htk ⊢
          exact h hh htk
      | @idx r ui cf pa n w κ hκ =>
        have hm' : idxGuard h0 r ui cf (disk c) = some (disk c') := hm
        obtain ⟨-, hm'⟩ := idxGuard_some.1 hm'
        rw [hm'] at htk ⊢
        by_cases ht0 : (disk c).taken = some h0
        · simp [complete, ht0] at htk
        · have htk' : (disk c).taken = some hh := by simpa [complete, ht0] using htk
          have hne : hh ≠ h0 := fun e' => ht0 (e' ▸ htk')
          rw [phase_complete_ne hne]
          exact h hh htk'
  · rcases writeN_cases hw with ⟨-, -, -, hd⟩ | ⟨cfg, isr, hd⟩
    · rw [hd] at htk
      cases htk
    · rw [hd] at htk ⊢
      exact h hh htk

/-- `latchOk` holds of the boot configuration. -/
theorem latchOk_boot {c : Cfg} (h0 : c.1 = [Expr.power]) (hd : (disk c).taken = none) :
    latchOk c := by
  intro h ht
  rw [hd] at ht
  cases ht

/-- **The latch is held only by a head in flight**, on a run from the boot configuration with the
latch free and no busy reset. -/
theorem latch_inflight (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power])
    (hd : (disk (σ 0)).taken = none) (hR : NoBusyReset σ) :
    ∀ n h, (disk (σ n)).taken = some h → (phase (disk (σ n)) h).isSome = true := by
  intro n
  induction n with
  | zero => exact latchOk_boot h0 hd
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact latchOk_step hs (tasksOk_run hrun h0 n) (progs_run hrun (progs_boot h0) n)
      (ownersOk_run hrun h0 hR n) ih

end Latch

/-! ## 6. The implications to the gate theorems

### At most one competitor, and its path is bounded -/

section Competitor

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- A head in flight is a key of the in-flight map. -/
theorem mem_keys_of_phase {v : VirtioState} {h : BitVec 16} (hv : (phase v h).isSome = true) :
    h ∈ v.inflight.map Prod.fst := by
  unfold phase alistGet at hv
  cases hf : v.inflight.find? (fun kv => decide (kv.1 = h)) with
  | none => rw [hf] at hv; cases hv
  | some p =>
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    exact List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hf, hp⟩

/-- Three distinct heads in flight make an in-flight map of at least three entries. -/
theorem three_le_length {v : VirtioState} {a b d : BitVec 16} (ha : (phase v a).isSome = true)
    (hb : (phase v b).isSome = true) (hd : (phase v d).isSome = true) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) : 3 ≤ v.inflight.length := by
  have ka := mem_keys_of_phase ha
  have kb := (List.mem_erase_of_ne (Ne.symm hab)).2 (mem_keys_of_phase hb)
  have kd := (List.mem_erase_of_ne (Ne.symm hbd)).2 ((List.mem_erase_of_ne (Ne.symm had)).2
    (mem_keys_of_phase hd))
  have l1 := List.length_erase_of_mem ka
  have l2 := List.length_erase_of_mem kb
  have l3 := List.length_pos_of_mem kd
  have : (v.inflight.map Prod.fst).length = v.inflight.length := List.length_map _
  omega

/-- **At most one competitor**, in one configuration: when every holder of a head is in flight and
at most two requests are, a serving task of `h` has at most one other serving task beside it, of
any head. -/
theorem competitor_unique_at (ho : ownersOk c) (hb : (disk c).inflight.length ≤ 2) {h h1 h2 : BitVec 16}
    {j' : Nat} (hi : servingAt i h c) (hj : servingAt j h1 c) (hj' : servingAt j' h2 c)
    (hji : j ≠ i) (hj'i : j' ≠ i) : j = j' := by
  have f0 := ho.2 _ _ (Or.inl hi)
  have f1 := ho.2 _ _ (Or.inl hj)
  have f2 := ho.2 _ _ (Or.inl hj')
  have n1 : h ≠ h1 := fun e => hji (ho.1 _ _ _ (Or.inl hj) (Or.inl (e ▸ hi)))
  have n2 : h ≠ h2 := fun e => hj'i (ho.1 _ _ _ (Or.inl hj') (Or.inl (e ▸ hi)))
  by_cases e12 : h1 = h2
  · subst e12
    exact ho.1 _ _ _ (Or.inl hj) (Or.inl hj')
  · have := three_le_length f0 f1 f2 n1 n2 e12
    omega

/-- **At most one competitor.**  On a run from the boot configuration with no busy reset and at
most two requests in flight (the kernel's bound), a serving task of `h` has at every position at
most one other live serving task, of any head: each serving task holds its own head, distinct
tasks hold distinct heads, and the held heads are in flight. -/
theorem competitor_unique (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ)
    (hB : BoundedInflight 2 σ) :
    ∀ n i h j h1 j' h2, servingAt i h (σ n) → servingAt j h1 (σ n) → servingAt j' h2 (σ n) →
      j ≠ i → j' ≠ i → j = j' :=
  fun n _ _ _ _ _ _ hi hj hj' hji hj'i =>
    competitor_unique_at (ownersOk_run hrun h0 hR n) (hB n) hi hj hj' hji hj'i

/-- **The competitor's path is bounded.**  A live serving task at a position of a run from the
boot configuration is a forked task at a program bounded by `16`: it is at the end of its program
once it has moved `16` times, and moves no more.  Its end is its completion when the used-index
write's guard answers there (see the module header for what that needs). -/
theorem serving_within (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) {n : Nat}
    {h : BitVec 16} (hs : servingAt j h (σ n)) :
    ∃ e tid, tid ≠ rootTask ∧ (∀ k, ownMoves j σ n k ≤ 16) ∧
      ∀ k, 16 ≤ ownMoves j σ n k → ∃ p ≤ k, atEnd j e .virtio tid (σ (n + p)) := by
  obtain ⟨e, tid, m, hx, -, hnr, -, -⟩ := hs
  obtain ⟨-, hb⟩ := (tasksOk_run hrun h0 n _ _ _ _ hx).2 hnr
  exact ⟨e, tid, hnr, forked_moves_le hrun hx hb hnr, fun k hk => pure_within hrun hx hb k hk⟩

end Competitor

/-! ### The gate theorems' side conditions -/

section Sides

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- The thread at `j` is a disk task at a node whose primitive is of class `K`. -/
def atNode (j : Nat) (K : DevOp VirtioState VTask → Prop) (c : Cfg) : Prop :=
  ∃ e tid o k, c.1[j]? = some (Expr.dev e .virtio tid (.op o k)) ∧ K o

/-- The pop node is no read and no stall. -/
theorem pop_not_hf {h : BitVec 16} : ¬ HFOp (popOp h) := by
  rintro (he | ⟨_, _, he⟩ | he)
  · cases he
  · cases he
  · injection he with hg
    probe_contra hg

/-- A live forked task at a pop node serves that head. -/
theorem servingAt_of_pop (ht : tasksOk c) {e : Nat} {tid : TaskId} {h : BitVec 16}
    {k : Unit → VM Unit} (hj : c.1[j]? = some (.dev e .virtio tid (.op (popOp h) k)))
    (hl : threadLive c.2 e) (hr : tid ≠ rootTask) : servingAt j h c := by
  obtain ⟨⟨h0, hsp⟩, -⟩ := (ht _ _ _ _ hj).2 hr
  have hn : SNode h0 (popOp h) := hsp.nodes.1
  have hh : h = h0 := by
    rcases hn with hn | ⟨_, _, _, _, _, _, he⟩
    · have hg : guardG (popGuard h) probe0 =
          some ({ setPhase probe0 h .popped with seen := probe0.seen + 1#16 }, []) := by
        simp [guardG, popGuard, phase, alistGet, probe0, Virtio.initial]
      rcases stepHead hn hg with h3 | ⟨h3, -⟩
      · simpa [setPhase, alistSet] using h3
      · simp [setPhase, probe0, Virtio.initial] at h3
    · cases he
  subst hh
  exact ⟨e, tid, _, hj, hl, hr, hsp, not_inert_of_op pop_not_hf⟩

/-- A root is at no DMA write. -/
theorem not_root_of_dma (ht : tasksOk c) {e : Nat} {tid : TaskId}
    {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    {k : Unit → VM Unit} (hj : c.1[j]? = some (.dev e .virtio tid (.op (.dmaWrite g pa n w) k))) :
    tid ≠ rootTask := by
  intro hr
  subst hr
  obtain ⟨⟨oh, hrp⟩, -⟩ := (ht _ _ _ _ hj).1 rfl
  cases hrp with
  | op hp _ => cases hp

/-- **The latch gate's side condition.**  While no serving task other than `i` is at a latch
node, no other live disk task takes a latch: `latch_stable`'s closer class is excluded. -/
theorem latch_closers (ht : tasksOk c)
    (hfree : ∀ j h', j ≠ i → servingAt j h' c → ¬ atNode j isLatch c) :
    ¬ Gate.stepBy i .virtio isLatch c c' := by
  rintro ⟨j, e, tid, o, k, hji, -, hj, hl, hK⟩
  obtain ⟨-, h0, hs, -⟩ := closer_serving ht hj hl (Or.inl hK)
  exact hfree j h0 hji hs ⟨e, tid, o, k, hj, hK⟩

/-- **The completion-and-push gate's side condition.**  While no serving task other than `i` is at
a capture or a push node, no other live disk task captures, pushes or completes the gate's head:
the completion of `h` is its serving task's, and that is `i`. -/
theorem push_closers (ht : tasksOk c) (ho : ownersOk c) {tid : TaskId} {h : BitVec 16}
    {r : VioReq} (hen : Gate.enabled i .virtio tid (pushOp h r) c)
    (hfree : ∀ j h', j ≠ i → servingAt j h' c → ¬ atNode j (fun o => isCapture o ∨ isPush o) c) :
    ¬ Gate.stepBy i .virtio (fun o => isCapture o ∨ isPush o ∨ completes h o) c c' := by
  rintro ⟨j, e, tid', o, k, hji, -, hj, hl, hK⟩
  have hc : Closer o := by
    rcases hK with hK | hK | ⟨r', ui, cf, pa, n, w, rfl⟩
    · exact Or.inr (Or.inl hK)
    · exact Or.inr (Or.inr (Or.inl hK))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, r', ui, cf, pa, n, w, rfl⟩)))
  obtain ⟨-, h0, hs, hn⟩ := closer_serving ht hj hl hc
  rcases hK with hK | hK | ⟨r', ui, cf, pa, n, w, rfl⟩
  · exact hfree j h0 hji hs ⟨e, tid', o, k, hj, Or.inl hK⟩
  · exact hfree j h0 hji hs ⟨e, tid', o, k, hj, Or.inr hK⟩
  · obtain rfl := snode_head hn (Or.inr ⟨r', ui, cf, pa, n, w, rfl⟩) dma_not_hf
    obtain ⟨⟨k', e', hi, hli⟩, -⟩ := hen
    have hr : tid ≠ rootTask := not_root_of_node ht hi (h := h0) (Or.inr (Or.inr (Or.inl ⟨h0, r, rfl⟩)))
    have hsi := servingAt_of_node ht hi hli hr (Or.inl (ServePrim.push r)) push_not_hf
    exact hji (ho.1 _ _ _ (Or.inl hs) (Or.inl hsi))

/-- **The pop guard has no task closer.**  When the root's pop guard for `h` is open (`h` is not in
flight), no other live disk task writes the phase of `h` or pops `h`: a task at a phase write of
`h` serves `h`, so `h` would be in flight, and a second pop would be a second live root. -/
theorem pop_closers (ht : tasksOk c) (ho : ownersOk c) (hr : rootsOk c) {tid : TaskId}
    {h : BitVec 16} (hen : Gate.enabled i .virtio tid (popOp h) c) :
    ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ popsHead h o) c c' := by
  rw [enabled_pop_iff] at hen
  obtain ⟨⟨k, e, hi, hli⟩, hnot⟩ := hen
  -- a serving task of `h` would put `h` in flight
  have noServe : ∀ {j'}, ¬ servingAt j' h c := fun hs => by
    rw [ho.2 _ _ (Or.inl hs)] at hnot
    cases hnot
  rintro ⟨j, e', tid', o, k', hji, -, hj, hl, hK⟩
  rcases hK with hK | rfl
  · obtain ⟨-, h0, hs, hn⟩ := closer_serving ht hj hl (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h, hK⟩)))))
    have hnh : SNode h o := by
      rcases hK with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, w, rfl⟩
      · exact Or.inl (ServePrim.fetched r)
      · exact Or.inl (ServePrim.served r)
      · exact Or.inl (ServePrim.status r)
      · exact Or.inl (ServePrim.capture r w)
    have hno : ¬ HFOp o := fun hf => hfOp_not_closer hf (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h, hK⟩)))))
    obtain rfl := snode_head hn hnh hno
    exact noServe hs
  · by_cases hr' : tid' = rootTask
    · subst hr'
      by_cases hri : tid = rootTask
      · subst hri
        exact hji (hr _ _ _ ⟨e', _, hj, hl⟩ ⟨e, _, hi, hli⟩)
      · exact noServe (servingAt_of_pop ht hi hli hri)
    · exact noServe (servingAt_of_pop ht hj hl hr')

/-- **The fill's and the status byte's guard has no task closer.**  A task at a DMA write of
head `h` guarded on its request serves `h`; another task's phase write, push or completion of
`h` would be a second serving task of `h`. -/
theorem req_closers (ht : tasksOk c) (ho : ownersOk c) {tid : TaskId} {h : BitVec 16} {r : VioReq}
    {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (hen : Gate.dmaAt i .virtio tid (reqGuard h r) pa n w c) :
    ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ pushesHead h o ∨ completes h o) c c' := by
  obtain ⟨⟨k, e, hi, hli⟩, -⟩ := hen
  have hsi := servingAt_of_node ht hi hli (not_root_of_dma ht hi)
    (Or.inl (ServePrim.fill r pa n w)) dma_not_hf
  rintro ⟨j, e', tid', o, k', hji, -, hj, hl, hK⟩
  have hnh : SNode h o ∧ Closer o := by
    rcases hK with (⟨r', rfl⟩ | ⟨r', rfl⟩ | ⟨r', rfl⟩ | ⟨r', w', rfl⟩) | ⟨r', rfl⟩ |
      ⟨r', ui, cf, pa', n', w', rfl⟩
    · exact ⟨Or.inl (ServePrim.fetched r'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h, Or.inl ⟨r', rfl⟩⟩))))⟩
    · exact ⟨Or.inl (ServePrim.served r'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h, Or.inr (Or.inl ⟨r', rfl⟩)⟩))))⟩
    · exact ⟨Or.inl (ServePrim.status r'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h, Or.inr (Or.inr (Or.inl ⟨r', rfl⟩))⟩))))⟩
    · exact ⟨Or.inl (ServePrim.capture r' w'), Or.inr (Or.inl ⟨h, r', w', rfl⟩)⟩
    · exact ⟨Or.inl (ServePrim.push r'), Or.inr (Or.inr (Or.inl ⟨h, r', rfl⟩))⟩
    · exact ⟨Or.inr ⟨r', ui, cf, pa', n', w', rfl⟩,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨h, r', ui, cf, pa', n', w', rfl⟩)))⟩
  obtain ⟨-, h0, hs, hn⟩ := closer_serving ht hj hl hnh.2
  obtain rfl := snode_head hn hnh.1 (fun hf => hfOp_not_closer hf hnh.2)
  exact hji (ho.1 _ _ _ (Or.inl hs) (Or.inl hsi))

/-- **The used element's and the used index's guard: the competitor's completion is the only task
closer.**  While no serving task other than `i` is at a used-index write, no other live disk task
writes the phase of `h`, pushes `h` or writes a used index. -/
theorem snap_closers (ht : tasksOk c) (ho : ownersOk c) {tid : TaskId} {h : BitVec 16}
    {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (hgo : SNode h (.dmaWrite g pa n w)) (hen : Gate.dmaAt i .virtio tid g pa n w c)
    (hfree : ∀ j h', j ≠ i → servingAt j h' c → ¬ atNode j isUsedIdx c) :
    ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o) c c' := by
  obtain ⟨⟨k, e, hi, hli⟩, -⟩ := hen
  have hsi := servingAt_of_node ht hi hli (not_root_of_dma ht hi) hgo dma_not_hf
  rintro ⟨j, e', tid', o, k', hji, -, hj, hl, hK⟩
  rcases hK with hK | hK | hK
  · have hc : Closer o := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hK⟩))))
    obtain ⟨-, h0, hs, hn⟩ := closer_serving ht hj hl hc
    have hnh : SNode h o := by
      rcases hK with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, w, rfl⟩
      · exact Or.inl (ServePrim.fetched r)
      · exact Or.inl (ServePrim.served r)
      · exact Or.inl (ServePrim.status r)
      · exact Or.inl (ServePrim.capture r w)
    obtain rfl := snode_head hn hnh (fun hf => hfOp_not_closer hf hc)
    exact hji (ho.1 _ _ _ (Or.inl hs) (Or.inl hsi))
  · have hc : Closer o := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hK⟩))))
    obtain ⟨-, h0, hs, hn⟩ := closer_serving ht hj hl hc
    obtain ⟨r, rfl⟩ := hK
    obtain rfl := snode_head hn (Or.inl (ServePrim.push r)) push_not_hf
    exact hji (ho.1 _ _ _ (Or.inl hs) (Or.inl hsi))
  · obtain ⟨-, h0, hs, -⟩ := closer_serving ht hj hl (Or.inr (Or.inr (Or.inr (Or.inl hK))))
    exact hfree j h0 hji hs ⟨e', tid', o, k', hj, hK⟩

/-! ### Along a run: the gate theorems' hypotheses -/

/-- `latch_persists`' and `latch_sf`'s closer hypothesis, on a run from the boot configuration
where no serving task other than `i` is ever at a latch node while the gate is open. -/
theorem latch_hK (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) {tid : TaskId} {h : BitVec 16}
    (hfree : ∀ n, Gate.enabled i .virtio tid (latchOp h) (σ n) →
      ∀ j h', j ≠ i → servingAt j h' (σ n) → ¬ atNode j isLatch (σ n)) :
    ∀ n, Gate.enabled i .virtio tid (latchOp h) (σ n) →
      ¬ Gate.stepBy i .virtio isLatch (σ n) (σ (n + 1)) :=
  fun n hen => latch_closers (tasksOk_run hrun h0 n) (hfree n hen)

/-- `push_persists`' and `push_sf`'s closer hypothesis, on a run from the boot configuration with
no busy reset where no serving task other than `i` is at a capture or a push node while the gate
is open. -/
theorem push_hK (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ)
    {tid : TaskId} {h : BitVec 16} {r : VioReq}
    (hfree : ∀ n, Gate.enabled i .virtio tid (pushOp h r) (σ n) →
      ∀ j h', j ≠ i → servingAt j h' (σ n) → ¬ atNode j (fun o => isCapture o ∨ isPush o) (σ n)) :
    ∀ n, Gate.enabled i .virtio tid (pushOp h r) (σ n) → ¬ Gate.stepBy i .virtio
      (fun o => isCapture o ∨ isPush o ∨ completes h o) (σ n) (σ (n + 1)) :=
  fun n hen => push_closers (tasksOk_run hrun h0 n) (ownersOk_run hrun h0 hR n) hen (hfree n hen)

/-- `pop_persists`' and `pop_sf`'s closer hypothesis holds outright on a run from the boot
configuration with no busy reset. -/
theorem pop_hK (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ)
    {tid : TaskId} {h : BitVec 16} :
    ∀ n, Gate.enabled i .virtio tid (popOp h) (σ n) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ popsHead h o) (σ n) (σ (n + 1)) :=
  fun n hen => pop_closers (tasksOk_run hrun h0 n) (ownersOk_run hrun h0 hR n)
    (fun d i i' => oneRoot hrun h0 n d i i') hen

/-- `req_persists`' and `req_sf_iff`'s closer hypothesis holds outright on a run from the boot
configuration with no busy reset. -/
theorem req_hK (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ)
    {tid : TaskId} {h : BitVec 16} {r : VioReq} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)} :
    ∀ m, Gate.dmaAt i .virtio tid (reqGuard h r) pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ completes h o) (σ m) (σ (m + 1)) :=
  fun m hen => req_closers (tasksOk_run hrun h0 m) (ownersOk_run hrun h0 hR m) hen

/-- `snap_persists`' and `snap_sf_iff`'s closer hypothesis, for the used element's or the used
index's write of head `h`, on a run from the boot configuration with no busy reset where no
serving task other than `i` is at a used-index write while the guard answers. -/
theorem snap_hK (hrun : PoolRun σ) (h0 : (σ 0).1 = [Expr.power]) (hR : NoBusyReset σ)
    {tid : TaskId} {h : BitVec 16} {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} (hgo : SNode h (.dmaWrite g pa n w))
    (hfree : ∀ m, Gate.dmaAt i .virtio tid g pa n w (σ m) →
      ∀ j h', j ≠ i → servingAt j h' (σ m) → ¬ atNode j isUsedIdx (σ m)) :
    ∀ m, Gate.dmaAt i .virtio tid g pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o) (σ m) (σ (m + 1)) :=
  fun m hen => snap_closers (tasksOk_run hrun h0 m) (ownersOk_run hrun h0 hR m) hgo hen
    (hfree m hen)

end Sides

end Disk
end Fairness

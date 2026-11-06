import MachCSL.Liveness.Fairness

/-! # The stable gates of the device programs

Milestone B2 of lane `xv6-liveness-now`: the plan's stable-gate lemma, for each gate of the three
device programs.  A device task waiting at a gate is the action `Dev` of `Fairness.lean` (3.5).
Its grant is certain at the task's own attempts, in the thread's view of the action (section 5 of
`FairnessTheory.lean`).  Its strong fairness follows from fair scheduling and persistence
(`Dev.sf_of_persists`).  The lemma says, for each gate, that once the gate is open no other
thread's step but the power thread's closes it before the task steps through, except for named
closing transitions.  Each gate's theorem takes a hypothesis excluding its closers while the gate
is open, and gives persistence through `Era.persists_of_liveStableUnder` (a generalisation of
`Era.persists_of_liveStable` to a side condition on the steps).

**Map of the file.**

1. `Gate`, any device.  What a step does to a device's state (`devSt_step`: unchanged, a move by
   one of the device's tasks at a guarded update or a DMA write, or a hart's MMIO read or write
   decoded to the device); the record of finished tasks only grows (`done_mono`).  The program
   invariant: a device's tasks run programs whose primitives are all in a set (`PrimsIn`,
   `Progs`, kept by every step, `progs_step`).  The gate of one node (`enabled`: a live task at a
   node with primitive `o`, and `o` not blocked), its strong fairness (`SF`, `sf_of_persists`).
   The primitives that never block (`neverBlocks`), whose gate is stable outright; the join, whose
   gate is stable outright because finished tasks stay finished (`stable_join`).  The node form
   of `Dma`'s enabling condition (`dmaAt`).
2. `Port`, the UART: the transmit and receive arms answer faithfully and never block.
3. `Disk`, the virtio disk.  Its primitives (`Prim`) and the proof that its programs reach only
   those (`prims_serve`, `prims_body`, so `progs` holds along every run that starts with it,
   `progs_run`); what a step does to the disk (`step_cases`); the skeleton of a gate's stability
   (`stable_of`); the gates, each with its closers; the hypotheses on the harts' MMIO writes.

**The gates and their closers.**  Each closer is a step by another live disk task at a node of the
named kind (`Gate.stepBy`), or a hart's MMIO write.

* The capture latch (`latch_stable`, open iff the latch is free): another task taking a capture
  latch.  No MMIO write closes it (a reset frees the latch), nor does a completion.
* The completion-and-push gate (`push_stable`): another task's capture (of any head; a flush waits
  for an empty cache, a write in write-through mode for its own sectors), push (of any head;
  `pushOk` becomes false) or completion of the same head; a busy reset; a store that turns the
  write-back mode off.  The latch conjunct is not closed by another head's completion.
* The root's pop guard (`pop_stable`, open iff the head is not in flight): another task's phase
  write for the head that never blocks (the moves to `.fetched`, `.served`, `.status`, the
  capture) and another pop of the head.  No MMIO write closes it.
* The fill's and the status byte's DMA guard (`req_stable`): another task's phase write for the
  head (those four, and the push) or completion of the head; a busy reset.
* The used element's and the used index's DMA guard (`snap_stable`): another task's phase write
  for the head (the same five) or used-index write of any head; a busy reset; a store that changes
  the configuration.
* The join (`Gate.stable_join`): no closer.

**The hypotheses.**  `NoBusyReset` (no 4-byte zero store to the status register while a request
is in flight) is used by the three gates a reset closes: the completion-and-push gate, the fill's
guard (where it is the only MMIO closer) and the used element's guard.  Two more are needed, each
by one gate: `NoWceOff` by the completion-and-push gate, `NoConfigWrite` by the used element's and
the used index's guard; both speak only of stores other than a reset, while a request is in
flight.  All three follow from `kernelStores`, the kernel's discipline after the disk's
initialisation (stores only to the queue-notify and the interrupt-acknowledge registers).  Every
disk gate also takes `progs` along the run: the step relation lets a thread run any program, and
a closer is named by the program node it steps at. -/

namespace Fairness

open MachCSL Sail Sail.ArchSem LeanRV64D
open Thread (Persists)
open Era (liveAt StableExceptPower StableExceptPowerUnder)

namespace Gate

/-- Every primitive reachable in the program `m`, along every answer, satisfies `P`. -/
def PrimsIn {S T α : Type} (P : DevOp S T → Prop) : DevM S T α → Prop
  | .pure _ => True
  | .op o k => P o ∧ ∀ v, PrimsIn P (k v)

variable {S T α β : Type} {P : DevOp S T → Prop}

/-- A sequence keeps its primitives in `P` when both parts do (the second for every answer). -/
theorem PrimsIn.bind {m : DevM S T α}
    {f : α → DevM S T β} (hm : PrimsIn P m) (hf : ∀ a, PrimsIn P (f a)) :
    PrimsIn P (m >>= f) := by
  induction m with
  | pure a => exact hf a
  | op o k ih => exact ⟨hm.1, fun v => ih v (hm.2 v)⟩

/-- A finished program has no primitive left. -/
theorem PrimsIn.pure (a : α) : PrimsIn P (Pure.pure a : DevM S T α) := trivial

/-- A single primitive in `P` is a program in `P`. -/
theorem PrimsIn.lift {o : DevOp S T} (h : P o) : PrimsIn P (DevM.lift o) := ⟨h, fun _ => trivial⟩

/-- The guard of a `DevM.modify f` node: always answers `f`, silently. -/
def modifyG (f : S → S) : S → Option (S × List DevObs) := fun s => some (f s, [])
/-- The guard of a `DevM.guard g` node: answers `g`'s answer, silently, or blocks. -/
def guardG (g : S → Option S) : S → Option (S × List DevObs) :=
  fun s => (g s).map fun s' => (s', [])

example (f : S → S) : (DevM.modify f : DevM S T Unit) = DevM.lift (.step (modifyG f)) := rfl
example (g : S → Option S) : (DevM.guard g : DevM S T Unit) = DevM.lift (.step (guardG g)) := rfl

/-! ### What a step does to a device's state -/

/-- Releasing a reservation leaves the devices alone. -/
theorem dropWindow_devs (σ : MState) (cpu : CPU) : (σ.dropWindow cpu).devs = σ.devs := by
  unfold MState.dropWindow
  split
  · split <;> rfl
  · rfl

/-- Releasing a reservation leaves the task bookkeeping alone. -/
theorem dropWindow_devrt (σ : MState) (cpu : CPU) : (σ.dropWindow cpu).devrt = σ.devrt := by
  unfold MState.dropWindow
  split
  · split <;> rfl
  · rfl

/-- An MMIO read is answered by the one device its address decodes to, which alone moves. -/
theorem devRead_some {ds ds' : DevStates} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (h : devRead ds pa n = some (w, ds')) :
    ∃ d off s', devDecode pa = some (d, off) ∧ (devSig d).read (ds.st d) off n = some (w, s') ∧
      ds' = ds.set d s' := by
  unfold devRead at h
  split at h
  · rename_i d off hdec
    simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨w', s', hr, rfl, rfl⟩ := h
    exact ⟨d, off, s', hdec, hr, rfl⟩
  · cases h

/-- An MMIO write is answered by the one device its address decodes to, which alone moves. -/
theorem devWrite_some {ds ds' : DevStates} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (h : devWrite ds pa n w = some ds') :
    ∃ d off s', devDecode pa = some (d, off) ∧ (devSig d).write (ds.st d) off n w = some s' ∧
      ds' = ds.set d s' := by
  unfold devWrite at h
  split at h
  · rename_i d off hdec
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s', hr, rfl⟩ := h
    exact ⟨d, off, s', hdec, hr, rfl⟩
  · cases h

/-- A hart's step leaves the devices alone, or is an MMIO read or an MMIO write. -/
theorem hartStep_devs {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') :
    σ'.devs = σ.devs ∨
    (∃ req k, m = .impure (.inl (.ok (.memRead req))) k ∧
      ∃ w, devRead σ.devs req.pa req.size = some (w, σ'.devs)) ∨
    (∃ req w tags k, m = .impure (.inl (.ok (.memWrite req w tags))) k ∧
      devWrite σ.devs req.pa req.size w = some σ'.devs) := by
  unfold hartStep at h
  split at h
  · obtain ⟨-, -, -, rfl⟩ := h
    exact Or.inl (dropWindow_devs _ _)
  · exact h.elim
  · rename_i o k
    rcases h with ⟨v, -, hev⟩ | ⟨hb, -⟩
    · cases o with
      | memRead req =>
        rcases hev with ⟨-, w, ds', hrd, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
          ⟨-, -, tvn, w, -, -, -, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩
        · exact Or.inr (Or.inl ⟨req, k, rfl, w, hrd⟩)
        all_goals exact Or.inl rfl
      | memWrite req w tags =>
        rcases hev with ⟨-, ds', hwr, -, rfl⟩ | ⟨-, -, -, rfl⟩
        · exact Or.inr (Or.inr ⟨req, w, tags, k, rfl, hwr⟩)
        · exact Or.inl rfl
      | _ =>
        first
        | (obtain rfl := hev; exact Or.inl rfl)
        | (obtain ⟨-, rfl⟩ := hev; exact Or.inl rfl)
    · cases o with
      | memRead req =>
        obtain ⟨-, -, rfl⟩ := hb
        exact Or.inl rfl
      | memWrite req w tags =>
        obtain ⟨-, rfl⟩ := hb
        split
        · exact Or.inl rfl
        · exact Or.inl (dropWindow_devs _ _)
      | _ => exact hb.elim
  · obtain ⟨-, -, rfl⟩ := h
    exact Or.inl rfl

/-- A hart's step leaves the task bookkeeping alone. -/
theorem hartStep_devrt {cpu : CPU} {m m' : SailM Unit} {σ σ' : MState}
    (h : hartStep cpu m σ m' σ') : σ'.devrt = σ.devrt := by
  unfold hartStep at h
  split at h
  · obtain ⟨-, -, -, rfl⟩ := h
    exact dropWindow_devrt _ _
  · exact h.elim
  · rename_i o k
    rcases h with ⟨v, -, hev⟩ | ⟨hb, -⟩
    · cases o with
      | memRead req =>
        rcases hev with ⟨-, w, ds', hrd, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
          ⟨-, -, tvn, w, -, -, -, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩
        all_goals rfl
      | memWrite req w tags =>
        rcases hev with ⟨-, ds', hwr, -, rfl⟩ | ⟨-, -, -, rfl⟩
        all_goals rfl
      | _ =>
        first
        | (obtain rfl := hev; rfl)
        | (obtain ⟨-, rfl⟩ := hev; rfl)
    · cases o with
      | memRead req =>
        obtain ⟨-, -, rfl⟩ := hb
        rfl
      | memWrite req w tags =>
        obtain ⟨-, rfl⟩ := hb
        split
        · rfl
        · exact dropWindow_devrt _ _
      | _ => exact hb.elim
  · obtain ⟨-, -, rfl⟩ := h
    rfl

/-- A device task's step leaves the devices alone, or moves its own device by a guarded update or
a DMA write whose guard answers. -/
theorem devStep_devs {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) :
    σ'.devs = σ.devs ∨
    (∃ g k, m = .op (.step g) k ∧ ∃ s' os, g (σ.devs.st d) = some (s', os) ∧
      σ'.devs = σ.devs.set d s') ∨
    (∃ g pa n w k, m = .op (.dmaWrite g pa n w) k ∧ ∃ s', g (σ.devs.st d) = some s' ∧
      σ'.devs = σ.devs.set d s') := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact Or.inl rfl
    · split <;> exact Or.inl rfl
  · rename_i o k
    rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · cases o with
      | step g =>
        obtain ⟨s', os, hg, -, rfl, -, -⟩ := hop
        exact Or.inr (Or.inl ⟨g, k, rfl, s', os, hg, rfl⟩)
      | get =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Or.inl rfl
      | choose =>
        obtain ⟨rfl, -, -⟩ := hop
        exact Or.inl rfl
      | dmaRead pa n =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Or.inl rfl
      | dmaWrite g pa n w =>
        obtain ⟨-, -, ⟨s', hg, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := hop
        · exact Or.inr (Or.inr ⟨g, pa, n, w, k, rfl, s', hg, rfl⟩)
        · exact Or.inl rfl
      | sample src =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Or.inl rfl
      | setPin cpu mmode b =>
        obtain ⟨-, -, rfl⟩ := hop
        cases mmode <;> exact Or.inl rfl
      | fork t =>
        obtain ⟨-, -, rfl, -⟩ := hop
        exact Or.inl rfl
      | join tid =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact Or.inl rfl
    · exact Or.inl rfl

/-- A device task's step only adds to the record of finished tasks. -/
theorem devStep_done {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) (d' : DevId) :
    (σ.devrt d').done ⊆ (σ'.devrt d').done := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩⟩ := h
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · simp only [updCpu']
        split
        · subst d'
          exact List.subset_cons_self _ _
        · exact List.Subset.refl _
  · rename_i o k
    rcases h with ⟨v, -, hop⟩ | ⟨-, -, rfl, -, -⟩
    · cases o with
      | step g =>
        obtain ⟨s', os, -, -, rfl, -, -⟩ := hop
        exact List.Subset.refl _
      | get =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact List.Subset.refl _
      | choose =>
        obtain ⟨rfl, -, -⟩ := hop
        exact List.Subset.refl _
      | dmaRead pa n =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact List.Subset.refl _
      | dmaWrite g pa n w =>
        obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := hop
        all_goals exact List.Subset.refl _
      | sample src =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact List.Subset.refl _
      | setPin cpu mmode b =>
        obtain ⟨-, -, rfl⟩ := hop
        cases mmode <;> exact List.Subset.refl _
      | fork t =>
        obtain ⟨-, -, rfl, -⟩ := hop
        simp only [updCpu']
        split
        · subst d'
          exact List.Subset.refl _
        · exact List.Subset.refl _
      | join tid =>
        obtain ⟨-, rfl, -, -⟩ := hop
        exact List.Subset.refl _
    · exact List.Subset.refl _

variable {i j : Nat} {c c' : Cfg}

/-- A step of a thread that is not the power thread only adds to every device's record of
finished tasks. -/
theorem done_mono (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) (d : DevId) :
    (c.2.m.devrt d).done ⊆ (c'.2.m.devrt d).done := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨-, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · show (g.m.devrt d).done ⊆ (σ'.devrt d).done
      rw [hartStep_devrt hst]
      exact List.Subset.refl _
    · exact List.Subset.refl _
  | dev gen d' tid m =>
    rcases hp with ⟨-, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact devStep_done hst d
    · exact List.Subset.refl _
  | power => exact absurd rfl (hnp _ he)

/-- **What a step does to a device's state.**  A step of a thread that is not the power thread
leaves the state of device `d` as it was, or it is one of four transitions: a live task of `d`
at a guarded update whose guard answers the new state; a live task of `d` at a DMA write whose
guard answers the new state; a live hart's MMIO read decoded to `d`, whose read function answers
the new state; a live hart's MMIO write decoded to `d`, whose write function answers the new
state. -/
theorem devSt_step (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) (d : DevId) :
    c'.2.m.devs.st d = c.2.m.devs.st d ∨
    (∃ e tid g k, c.1[j]? = some (.dev e d tid (.op (.step g) k)) ∧ threadLive c.2 e ∧
      ∃ os, g (c.2.m.devs.st d) = some (c'.2.m.devs.st d, os)) ∨
    (∃ e tid g pa n w k, c.1[j]? = some (.dev e d tid (.op (.dmaWrite g pa n w) k)) ∧
      threadLive c.2 e ∧ g (c.2.m.devs.st d) = some (c'.2.m.devs.st d)) ∨
    (∃ e cpu req k off, c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memRead req))) k)) ∧
      threadLive c.2 e ∧ devDecode req.pa = some (d, off) ∧
      ∃ w, (devSig d).read (c.2.m.devs.st d) off req.size = some (w, c'.2.m.devs.st d)) ∨
    (∃ e cpu req w tags k off,
      c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) ∧
      threadLive c.2 e ∧ devDecode req.pa = some (d, off) ∧
      (devSig d).write (c.2.m.devs.st d) off req.size w = some (c'.2.m.devs.st d)) := by
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  obtain ⟨e, obs, e', efs, he, hp, -⟩ := hs
  cases e with
  | hart gen cpu m =>
    rcases hp with ⟨-, ⟨hl, -, m', σ', -, hst, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · rcases hartStep_devs hst with hd | ⟨req, k, rfl, w, hrd⟩ | ⟨req, w, tags, k, rfl, hwr⟩
      · exact Or.inl (by simp only [hd])
      · obtain ⟨d', off, s', hdec, hr, hds⟩ := devRead_some hrd
        by_cases hdd : d' = d
        · subst hdd
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨gen, cpu, req, k, off, he, hl, hdec, w, ?_⟩)))
          simp only [hds, DevStates.set_same]
          exact hr
        · refine Or.inl ?_
          simp only [hds]
          exact DevStates.set_other _ _ _ _ (Ne.symm hdd)
      · obtain ⟨d', off, s', hdec, hr, hds⟩ := devWrite_some hwr
        by_cases hdd : d' = d
        · subst hdd
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨gen, cpu, req, w, tags, k, off, he, hl, hdec, ?_⟩)))
          simp only [hds, DevStates.set_same]
          exact hr
        · refine Or.inl ?_
          simp only [hds]
          exact DevStates.set_other _ _ _ _ (Ne.symm hdd)
    · exact Or.inl rfl
  | dev gen d' tid m =>
    rcases hp with ⟨hl, m', σ', -, hst, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · rcases devStep_devs hst with hd | ⟨gd, k, rfl, s', os, hg, hds⟩ |
        ⟨gd, pa, n, w, k, rfl, s', hg, hds⟩
      · exact Or.inl (by simp only [hd])
      · by_cases hdd : d' = d
        · subst hdd
          refine Or.inr (Or.inl ⟨gen, tid, gd, k, he, hl, os, ?_⟩)
          simp only [hds, DevStates.set_same]
          exact hg
        · refine Or.inl ?_
          simp only [hds]
          exact DevStates.set_other _ _ _ _ (Ne.symm hdd)
      · by_cases hdd : d' = d
        · subst hdd
          refine Or.inr (Or.inr (Or.inl ⟨gen, tid, gd, pa, n, w, k, he, hl, ?_⟩))
          simp only [hds, DevStates.set_same]
          exact hg
        · refine Or.inl ?_
          simp only [hds]
          exact DevStates.set_other _ _ _ _ (Ne.symm hdd)
    · exact Or.inl rfl
  | power => exact absurd rfl (hnp _ he)

/-! ### The programs the pool runs -/

/-- A thread of the pool after a step is the stepping thread's old self at another position, or
the stepping thread's successor, or one it forked. -/
theorem get?_of_step {x : Expr} (hs : Step j c c') {j' : Nat} (h : c'.1[j']? = some x) :
    (j' ≠ j ∧ c.1[j']? = some x) ∨
    ∃ ex obs e' efs, c.1[j]? = some ex ∧ primStep (ex, c.2) obs (e', c'.2, efs) ∧
      (x = e' ∨ x ∈ efs) := by
  obtain ⟨ex, obs, e', efs, he, hp, hc'⟩ := hs
  rw [hc'] at h
  by_cases hlt : j' < (c.1.set j e').length
  · rw [List.getElem?_append_left hlt, List.getElem?_set] at h
    split at h
    · rename_i hjj
      subst hjj
      have hi : j < c.1.length := (List.getElem?_eq_some_iff.1 he).1
      rw [ite_eq_left_iff.mpr (fun hn => absurd hi hn)] at h
      exact Or.inr ⟨ex, obs, e', efs, he, hp, Or.inl (Option.some.inj h).symm⟩
    · rename_i hjj
      exact Or.inl ⟨Ne.symm hjj, h⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at h
    exact Or.inr ⟨ex, obs, e', efs, he, hp, Or.inr (List.mem_of_getElem? h)⟩

/-- Every task of device `d` in the pool runs a program all of whose primitives satisfy `P`. -/
def Progs (d : DevId) (P : DevOp (DevSt d) (DevTask d) → Prop) (c : Cfg) : Prop :=
  ∀ (j e : Nat) (tid : TaskId) (m : DevProg d),
    c.1[j]? = some (Expr.dev e d tid m) → PrimsIn P m

/-- A device task's step keeps it inside a program whose primitives satisfy `P`, when the device's
root program does. -/
theorem devStep_prims {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} {P : DevOp (DevSt d) (DevTask d) → Prop}
    (hbody : PrimsIn P (devSig d).body) (h : devStep gen d tid m σ obs m' σ' efs)
    (hm : PrimsIn P m) : PrimsIn P m' := by
  unfold devStep at h
  split at h
  · obtain ⟨-, -, ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩⟩ := h
    · exact hbody
    · trivial
  · rcases h with ⟨v, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact hm.2 v
    · exact hm

/-- What a device task's step forks is a task of the same device running a named task program. -/
theorem devStep_efs {gen : Nat} {d : DevId} {tid : TaskId} {m m' : DevProg d} {σ σ' : MState}
    {obs : List Obs} {efs : List Expr} (h : devStep gen d tid m σ obs m' σ' efs) :
    ∀ x ∈ efs, ∃ n t, x = .dev gen d n ((devSig d).task t) := by
  unfold devStep at h
  split at h
  · obtain ⟨-, rfl, -⟩ := h
    intro x hx
    cases hx
  · rename_i o k
    rcases h with ⟨v, -, hop⟩ | ⟨-, -, -, -, rfl⟩
    · cases o with
      | fork t =>
        obtain ⟨-, -, -, rfl⟩ := hop
        intro x hx
        rw [List.mem_singleton] at hx
        exact ⟨_, t, hx⟩
      | step g =>
        obtain ⟨s', os, -, -, -, -, rfl⟩ := hop
        intro x hx; cases hx
      | dmaWrite g pa n w =>
        obtain ⟨-, rfl, -⟩ := hop
        intro x hx; cases hx
      | setPin cpu mmode b =>
        obtain ⟨-, rfl, -⟩ := hop
        intro x hx; cases hx
      | choose =>
        obtain ⟨-, -, rfl⟩ := hop
        intro x hx; cases hx
      | _ =>
        obtain ⟨-, -, -, rfl⟩ := hop
        intro x hx; cases hx
    · intro x hx; cases hx

/-- The invariant is kept by every step, when the device's root program and every task it forks
satisfy `P`. -/
theorem progs_step {d : DevId} {P : DevOp (DevSt d) (DevTask d) → Prop}
    (hbody : PrimsIn P (devSig d).body) (htask : ∀ t, PrimsIn P ((devSig d).task t))
    (hs : Step j c c') (h : Progs d P c) : Progs d P c' := by
  intro j' e tid m hj'
  rcases get?_of_step hs hj' with ⟨-, hj⟩ | ⟨ex, obs, e', efs, hex, hp, hx⟩
  · exact h _ _ _ _ hj
  · cases ex with
    | hart gen cpu m0 =>
      rcases hp with ⟨rfl, ⟨-, -, m', σ', rfl, -, -⟩ | ⟨-, -, rfl, -⟩⟩
      all_goals
        rcases hx with hx | hx
        · cases hx
        · cases hx
    | dev gen d' tid' m0 =>
      rcases hp with ⟨-, m', σ', rfl, hst, -⟩ | ⟨-, -, rfl, rfl, -⟩
      · rcases hx with hx | hx
        · simp only [Expr.dev.injEq] at hx
          obtain ⟨rfl, rfl, rfl, hm⟩ := hx
          obtain rfl := eq_of_heq hm
          exact devStep_prims hbody hst (h _ _ _ _ hex)
        · obtain ⟨n, t, hxe⟩ := devStep_efs hst _ hx
          simp only [Expr.dev.injEq] at hxe
          obtain ⟨rfl, rfl, rfl, hm⟩ := hxe
          obtain rfl := eq_of_heq hm
          exact htask t
      · rcases hx with hx | hx
        · exact h _ _ _ _ (hx ▸ hex)
        · cases hx
    | power =>
      rcases hp with ⟨rfl, ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩⟩
      · rcases hx with hx | hx
        · cases hx
        · cases hx
      · rcases hx with hx | hx
        · cases hx
        · simp only [powerFork, List.mem_append, List.mem_map] at hx
          rcases hx with ⟨cpu, -, hxe⟩ | ⟨d'', -, hxe⟩
          · cases hxe
          · simp only [DevLoop, Expr.dev.injEq] at hxe
            obtain ⟨rfl, rfl, rfl, hm⟩ := hxe
            obtain rfl := eq_of_heq hm
            trivial

/-- The invariant holds along a run that starts in it. -/
theorem progs_run {σ : Nat → Cfg} {d : DevId} {P : DevOp (DevSt d) (DevTask d) → Prop}
    (hbody : PrimsIn P (devSig d).body) (htask : ∀ t, PrimsIn P ((devSig d).task t))
    (hrun : PoolRun σ) (h0 : Progs d P (σ 0)) : ∀ n, Progs d P (σ n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨j, hs⟩ := hrun n
    exact progs_step hbody htask hs ih

/-! ### A task at a node, and its gate -/

/-- The thread at `i` is a live task `tid` of device `d` whose head primitive is `o`. -/
def taskAt (i : Nat) (d : DevId) (tid : TaskId) (o : DevOp (DevSt d) (DevTask d)) (c : Cfg) :
    Prop :=
  ∃ e k, c.1[i]? = some (.dev e d tid (.op o k)) ∧ threadLive c.2 e

/-- The enabling condition of a gate: the thread at `i` is a live task `tid` of device `d` at a
node whose primitive is `o`, and `o` is not blocked (the gate is open). -/
def enabled (i : Nat) (d : DevId) (tid : TaskId) (o : DevOp (DevSt d) (DevTask d)) (c : Cfg) :
    Prop :=
  taskAt i d tid o c ∧ ¬ devBlocked d o c.2.m

/-- Strong fairness of the gate's own action: the gate open infinitely often forces infinitely
many steps through it.  The grant is the device tasks' (`Dev.grant`). -/
abbrev SF (i : Nat) (d : DevId) (tid : TaskId) (o : DevOp (DevSt d) (DevTask d))
    (σ : Nat → Cfg) : Prop :=
  Action.SF (enabled i d tid o) (Dev.grant i d tid) σ

/-- Another live task of device `d`, at a position other than `i` and at a node whose primitive
satisfies `K`, takes the step from `c` to `c'`: the shape of a closing transition. -/
def stepBy (i : Nat) (d : DevId) (K : DevOp (DevSt d) (DevTask d) → Prop) (c c' : Cfg) : Prop :=
  ∃ j e tid o k, j ≠ i ∧ Step j c c' ∧ c.1[j]? = some (.dev e d tid (.op o k)) ∧
    threadLive c.2 e ∧ K o

variable {d : DevId} {tid : TaskId} {o : DevOp (DevSt d) (DevTask d)} {σ : Nat → Cfg}

/-- A task at a node is a live thread. -/
theorem taskAt_live (h : taskAt i d tid o c) : liveAt i c :=
  let ⟨e, _, he, hl⟩ := h; ⟨e, Or.inr ⟨d, tid, _, he⟩, hl⟩

/-- A task's place in its program, and its liveness, survive every other thread's step but the
power thread's. -/
theorem taskAt_stable : StableExceptPower i (taskAt i d tid o) := by
  intro j c c' hji hs hnp h
  obtain ⟨e, k, he, hl⟩ := h
  exact ⟨e, k, step_get?_ne hs hji he, (Era.threadLive_of_step hs hnp e).2 hl⟩

/-- An open gate is a live thread's. -/
theorem live (h : enabled i d tid o c) : liveAt i c := taskAt_live h.1

/-- An open gate at a primitive other than a DMA write is the device tasks' enabling condition. -/
theorem dev_enabled (hdma : ¬ Dev.isDma o) (h : enabled i d tid o c) : Dev.enabled i d tid c :=
  let ⟨⟨e, k, he, hl⟩, hnb⟩ := h; ⟨e, o, k, he, hl, hdma, hnb⟩

/-- Stepping through an open gate is certain: every attempt of the task at the open gate is
granted. -/
theorem certain (hdma : ¬ Dev.isDma o) :
    Thread.Certain i (enabled i d tid o) (Dev.grant i d tid) σ :=
  fun n ⟨hs, hA⟩ => Dev.certain n ⟨hs, dev_enabled hdma hA⟩

/-- Strong fairness of a gate follows from fair scheduling and its persistence. -/
theorem sf_of_persists (hdma : ¬ Dev.isDma o) (hsched : StepsInfOften i σ)
    (hper : Persists i (enabled i d tid o) σ) : SF i d tid o σ :=
  Thread.sf_of_certain hsched hper (certain hdma)

/-- Strong fairness of a gate that is stable under the steps meeting a side condition, on a run
whose every step meets it. -/
theorem sf_of_stableUnder {P : Cfg → Cfg → Prop} (hdma : ¬ Dev.isDma o) (hrun : PoolRun σ)
    (hsched : StepsInfOften i σ) (hstab : StableExceptPowerUnder i P (enabled i d tid o))
    (hP : ∀ n, P (σ n) (σ (n + 1))) : SF i d tid o σ :=
  sf_of_persists hdma hsched (Era.persists_of_liveStableUnder hrun (fun _ => live) hstab hP)

/-! ### A task at a DMA write -/

/-- The enabling condition of `Dma` at one node: the thread at `i` is a live task `tid` of device
`d` at a DMA write with guard `g` into RAM at `pa`, and the guard answers a faithful move. -/
def dmaAt (i : Nat) (d : DevId) (tid : TaskId) (g : DevSt d → Option (DevSt d)) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (c : Cfg) : Prop :=
  taskAt i d tid (.dmaWrite g pa n w) c ∧
    (∃ s', g (c.2.m.devs.st d) = some s' ∧ devObsOk d (c.2.m.devs.st d) s' []) ∧ ramBytes pa n

/-- A task at a DMA-write node is a live thread. -/
theorem dmaAt_live {g : DevSt d → Option (DevSt d)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (h : dmaAt i d tid g pa n w c) : liveAt i c :=
  taskAt_live h.1

/-- A task at one DMA-write node with its guard answering is the enabling condition of `Dma`. -/
theorem dma_enabled {g : DevSt d → Option (DevSt d)} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (h : dmaAt i d tid g pa n w c) : Dma.enabled i d tid c :=
  let ⟨⟨e, k, he, hl⟩, hg, hr⟩ := h; ⟨e, g, pa, n, w, k, he, hl, hg, hr⟩

/-! ### Primitives that never block -/

/-- Primitive `o` of device `d` is blocked in no machine state. -/
def neverBlocks (d : DevId) (o : DevOp (DevSt d) (DevTask d)) : Prop :=
  ∀ σ : MState, ¬ devBlocked d o σ

/-- Reading the local state never blocks. -/
theorem neverBlocks_get : neverBlocks d .get := fun _ h => h
/-- An environment choice never blocks. -/
theorem neverBlocks_choose : neverBlocks d .choose := fun _ h => h
/-- A DMA read never blocks. -/
theorem neverBlocks_dmaRead (pa : PAddr) (n : Nat) : neverBlocks d (.dmaRead pa n) := fun _ h => h
/-- Sampling an interrupt source never blocks. -/
theorem neverBlocks_sample (src : IrqSrc) : neverBlocks d (.sample src) := fun _ h => h
/-- Driving an interrupt pin never blocks. -/
theorem neverBlocks_setPin (cpu : CPU) (mmode b : Bool) : neverBlocks d (.setPin cpu mmode b) :=
  fun _ h => h
/-- Forking a task never blocks. -/
theorem neverBlocks_fork (t : DevTask d) : neverBlocks d (.fork t) := fun _ h => h

/-- A guarded update whose every answer is faithful to its events never blocks if its guard
always answers. -/
theorem neverBlocks_step {g : DevSt d → Option (DevSt d × List DevObs)}
    (hans : ∀ s, ∃ s' os, g s = some (s', os) ∧ devObsOk d s s' os) : neverBlocks d (.step g) := by
  intro σ hb
  obtain ⟨s', os, hg, hok⟩ := hans (σ.devs.st d)
  exact hb s' os hg hok

/-- A `DevM.modify` node of a silent device (the PLIC, the disk) never blocks. -/
theorem neverBlocks_modify (hsil : ∀ s s' : DevSt d, devObsOk d s s' []) (f : DevSt d → DevSt d) :
    neverBlocks d (.step (modifyG f)) :=
  neverBlocks_step fun s => ⟨f s, [], rfl, hsil s (f s)⟩

/-- A `DevM.modify` node of the PLIC never blocks. -/
theorem neverBlocks_modify_plic (f : PlicState → PlicState) :
    neverBlocks .plic (.step (modifyG f)) :=
  neverBlocks_modify (d := .plic) (fun _ _ => rfl) f

/-- A `DevM.modify` node of the disk never blocks. -/
theorem neverBlocks_modify_virtio (f : VirtioState → VirtioState) :
    neverBlocks .virtio (.step (modifyG f)) :=
  neverBlocks_modify (d := .virtio) (fun _ _ => rfl) f

/-- At a primitive that never blocks, the gate is the task being there. -/
theorem enabled_iff_of_neverBlocks (hnb : neverBlocks d o) :
    enabled i d tid o c ↔ taskAt i d tid o c :=
  ⟨fun h => h.1, fun h => ⟨h, hnb _⟩⟩

/-- At a primitive that never blocks, the gate survives every other thread's step but the power
thread's. -/
theorem stable_of_neverBlocks (hnb : neverBlocks d o) : StableExceptPower i (enabled i d tid o) :=
  fun hji hs hnp h => ⟨taskAt_stable hji hs hnp h.1, hnb _⟩

/-- At a primitive that never blocks, the gate persists on every run of the pool. -/
theorem persists_of_neverBlocks (hnb : neverBlocks d o) (hrun : PoolRun σ) :
    Persists i (enabled i d tid o) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) (stable_of_neverBlocks hnb)

/-- A task at a primitive that never blocks (and is not a DMA write) steps through it infinitely
often if it sits there infinitely often: no assumption beyond fair scheduling. -/
theorem sf_of_neverBlocks (hnb : neverBlocks d o) (hdma : ¬ Dev.isDma o) (hrun : PoolRun σ)
    (hsched : StepsInfOften i σ) : SF i d tid o σ :=
  sf_of_persists hdma hsched (persists_of_neverBlocks hnb hrun)

/-! ### The join -/

/-- A join gate is open exactly when the joined task has finished. -/
theorem enabled_join_iff {t : TaskId} :
    enabled i d tid (.join t) c ↔ taskAt i d tid (.join t) c ∧ t ∈ (c.2.m.devrt d).done := by
  unfold enabled devBlocked
  simp only [Classical.not_not]

/-- A join gate, once open, stays open under every other thread's step but the power thread's:
the record of finished tasks only grows. -/
theorem stable_join {t : TaskId} : StableExceptPower i (enabled i d tid (.join t)) := by
  intro j c c' hji hs hnp h
  rw [enabled_join_iff] at h ⊢
  exact ⟨taskAt_stable hji hs hnp h.1, done_mono hs hnp d h.2⟩

/-- A join gate persists on every run of the pool. -/
theorem persists_join {t : TaskId} (hrun : PoolRun σ) : Persists i (enabled i d tid (.join t)) σ :=
  Era.persists_of_liveStable hrun (fun _ => live) stable_join

/-- Strong fairness of a join gate follows from fair scheduling alone. -/
theorem sf_join {t : TaskId} (hrun : PoolRun σ) (hsched : StepsInfOften i σ) :
    SF i d tid (.join t) σ :=
  sf_of_persists (fun h => h) hsched (persists_join hrun)

end Gate

namespace Port
open Gate

/-- Every answer of a port's transmit arm is faithful to its events: the wire grows by exactly
the byte that left (nothing under loopback), and nothing comes in. -/
theorem txArm_faithful (i : UartId) {u u' : UartState} {os : List DevObs}
    (h : Uart.txArm i u = some (u', os)) : devObsOk (.uart i) u u' os := by
  unfold Uart.txArm at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [devObsOk, devObsOut, devObsIns]
  · rename_i b u'' hpop
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold Uart.txPop at hpop
    split at hpop
    · cases hpop
    · rename_i b' tx' htx
      simp only [Option.some.injEq, Prod.mk.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      by_cases hl : Uart.loopback u = true
      · simp [devObsOk, devObsOut, devObsIns, hl, Uart.recv]
      · simp [devObsOk, devObsOut, devObsIns, hl, DevObs.port]

/-- Every answer of a port's receive arm is faithful to its events: the cumulative input grows by
exactly the byte accepted (nothing when the FIFO is full), and the wire does not move. -/
theorem rxArm_faithful (i : UartId) (b : BitVec 8) {u u' : UartState} {os : List DevObs}
    (h : Uart.rxArm i b u = some (u', os)) : devObsOk (.uart i) u u' os := by
  unfold Uart.rxArm at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [devObsOk, devObsOut, devObsIns, DevObs.port, Uart.accept, Uart.recv]
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [devObsOk, devObsOut, devObsIns]

/-- A port's transmit arm never blocks: it always answers, faithfully. -/
theorem neverBlocks_txArm (i : UartId) : neverBlocks (.uart i) (.step (Uart.txArm i)) := by
  refine neverBlocks_step fun u => ?_
  cases h : Uart.txArm i u with
  | none =>
    unfold Uart.txArm at h
    split at h <;> cases h
  | some p => exact ⟨p.1, p.2, rfl, txArm_faithful i h⟩

/-- A port's receive arm never blocks: it always answers, faithfully. -/
theorem neverBlocks_rxArm (i : UartId) (b : BitVec 8) :
    neverBlocks (.uart i) (.step (Uart.rxArm i b)) := by
  refine neverBlocks_step fun u => ?_
  cases h : Uart.rxArm i b u with
  | none =>
    unfold Uart.rxArm at h
    split at h <;> cases h
  | some p => exact ⟨p.1, p.2, rfl, rxArm_faithful i b h⟩

end Port

namespace Disk
open Virtio Gate

/-! ### The disk's guards, named

Each guard below is the lambda of one node of `Virtio.serve` or `Virtio.body`, copied, and the
`example`s check by `rfl` that the node built from it is the node the program builds.  What ties
the names to the programs themselves is `prims_serve` and `prims_body`: every primitive the
programs can reach is one of `Prim`'s, which are stated with these names. -/

/-- The capture latch's guard in `Virtio.serve`: take the latch for head `h` if it is free. -/
def captureGuard (h : BitVec 16) : VirtioState → Option VirtioState :=
  fun v => if v.taken = none then some { v with taken := some h } else none

/-- The completion-and-push guard in `Virtio.serve`: once the request is in flight, its
completion gate holds and no other request is between its used element and its used index, move
it to `.pushed`. -/
def pushGuard (h : BitVec 16) (r : VioReq) : VirtioState → Option VirtioState :=
  fun v => if (phase v h).isSome && completeOk v r h && pushOk v then
    some (setPhase v h (.pushed r)) else none

/-- The pop guard in `Virtio.body`: refuse a head already in flight, else put it in flight and
advance the pop index. -/
def popGuard (h : BitVec 16) : VirtioState → Option VirtioState :=
  fun v => if (phase v h).isSome then none
    else some { setPhase v h .popped with seen := v.seen + 1#16 }

/-- The capture's move in `Virtio.capture`: lay the payload into the cache if the request is still
the one fetched, and move it to `.served`. -/
def captureMove (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat)) :
    VirtioState → VirtioState :=
  fun v => setPhase (if reqOf v h = some r then cacheReq v r (bytesOf w) else v) h (.served r)

/-- The drain's move in `Virtio.body`: write the `j`-th cached sector to the medium. -/
def drainMove (j : Nat) : VirtioState → VirtioState := fun v => drain v (v.cache.getD j (0, [])).1

/-- The guard of `Virtio.stall`: never answers. -/
def stallG : VirtioState → Option (VirtioState × List DevObs) :=
  fun s => if (fun (_ : VirtioState) => false) s then some (s, []) else none

/-- The guard of the fill's and the status byte's DMA writes: the request is still `r`. -/
def reqGuard (h : BitVec 16) (r : VioReq) : VirtioState → Option VirtioState :=
  fun v => if decide (reqOf v h = some r) then some v else none

/-- The guard of the used element's DMA write: the request is still `r`, and the used index and
the configuration are still the snapshot's. -/
def elemGuard (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    VirtioState → Option VirtioState :=
  fun s => if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
    some s else none

/-- The guard of the used index's DMA write: the used element's condition, and the answer is the
completion. -/
def idxGuard (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) :
    VirtioState → Option VirtioState :=
  fun s => if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
    some (complete s h) else none

example (h : BitVec 16) : (DevM.guard (captureGuard h) : VM Unit) =
    DevM.guard (fun v => if v.taken = none then some { v with taken := some h } else none) := rfl

example (h : BitVec 16) (r : VioReq) : (DevM.guard (pushGuard h r) : VM Unit) =
    DevM.guard (fun v =>
      if (phase v h).isSome && completeOk v r h && pushOk v then some (setPhase v h (.pushed r))
      else none) := rfl

example (h : BitVec 16) : (DevM.guard (popGuard h) : VM Unit) =
    DevM.guard (fun v =>
      if (phase v h).isSome then none
      else some { setPhase v h .popped with seen := v.seen + 1#16 }) := rfl

example (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat)) :
    (DevM.modify (captureMove h r w) : VM Unit) =
    DevM.modify (fun v =>
      setPhase (if reqOf v h = some r then cacheReq v r (bytesOf w) else v) h (.served r)) := rfl

example (j : Nat) : (DevM.modify (drainMove j) : VM Unit) =
    DevM.modify (fun v => drain v (v.cache.getD j (0, [])).1) := rfl

example : (DevM.lift (.step stallG) : VM Unit) = stall := rfl

example (h : BitVec 16) (r : VioReq) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    (DevM.lift (.dmaWrite (reqGuard h r) pa n w) : VM Unit) =
    DevM.dmaWriteIf (fun v => decide (reqOf v h = some r)) pa n w := rfl

example (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) : (DevM.lift (.dmaWrite (elemGuard h r ui c) pa n w) : VM Unit) =
    DevM.dmaWriteIf (fun s => decide (reqOf s h = some r) && decide (s.usedIdx = ui) &&
      decide (s.cfg = c)) pa n w := rfl

example (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) : (DevM.dmaWriteStep (idxGuard h r ui c) pa n w : VM Unit) =
    DevM.dmaWriteStep (fun s =>
      if decide (reqOf s h = some r) && decide (s.usedIdx = ui) && decide (s.cfg = c) then
        some (complete s h) else none) pa n w := rfl

/-- The primitives of the disk's programs (`Virtio.body`, `Virtio.serve` and what they call), one
constructor per kind of node. -/
inductive Prim : DevOp VirtioState VTask → Prop
  | get : Prim .get
  | choose : Prim .choose
  | dmaRead (pa : PAddr) (n : Nat) : Prim (.dmaRead pa n)
  | fork (t : VTask) : Prim (.fork t)
  | stall : Prim (.step stallG)
  | fetched (h : BitVec 16) (r : VioReq) : Prim (.step (modifyG fun v => setPhase v h (.fetched r)))
  | served (h : BitVec 16) (r : VioReq) : Prim (.step (modifyG fun v => setPhase v h (.served r)))
  | status (h : BitVec 16) (r : VioReq) : Prim (.step (modifyG fun v => setPhase v h (.status r)))
  | latch (h : BitVec 16) : Prim (.step (guardG (captureGuard h)))
  | capture (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat)) :
      Prim (.step (modifyG (captureMove h r w)))
  | push (h : BitVec 16) (r : VioReq) : Prim (.step (guardG (pushGuard h r)))
  | pop (h : BitVec 16) : Prim (.step (guardG (popGuard h)))
  | drain (j : Nat) : Prim (.step (modifyG (drainMove j)))
  | fill (h : BitVec 16) (r : VioReq) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
      Prim (.dmaWrite (reqGuard h r) pa n w)
  | elem (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat)
      (w : BitVec (8 * n)) : Prim (.dmaWrite (elemGuard h r ui c) pa n w)
  | idx (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (pa : PAddr) (n : Nat)
      (w : BitVec (8 * n)) : Prim (.dmaWrite (idxGuard h r ui c) pa n w)

/-- The stall is a disk program. -/
theorem prims_stall : PrimsIn Prim stall := PrimsIn.lift Prim.stall

/-- A 16-bit DMA read is a disk program. -/
theorem prims_dma16 (pa : PAddr) : PrimsIn Prim (dma16 pa) :=
  PrimsIn.bind (PrimsIn.lift (Prim.dmaRead _ _)) fun _ => PrimsIn.pure _

/-- A bounded choice is a disk program. -/
theorem prims_chooseLt (n : Nat) : PrimsIn Prim (DevM.chooseLt n : VM Nat) :=
  PrimsIn.bind (PrimsIn.lift Prim.choose) fun _ => PrimsIn.pure _

/-- The fetch of a chain is a disk program. -/
theorem prims_fetch (c : VirtioCfg) (h : BitVec 16) : PrimsIn Prim (fetch c h) := by
  unfold fetch
  repeat
    first
    | (intro _)
    | (apply PrimsIn.bind)
    | split
    | exact PrimsIn.pure _
    | exact PrimsIn.lift (Prim.dmaRead _ _)
    | (dsimp only)


/-- The step of the prims tactic. -/
macro "prims_step" : tactic => `(tactic| first
  | (intro _)
  | exact PrimsIn.pure _
  | exact prims_fetch _ _
  | exact prims_stall
  | exact prims_dma16 _
  | exact prims_chooseLt _
  | exact PrimsIn.lift Prim.get
  | exact PrimsIn.lift Prim.choose
  | exact PrimsIn.lift (Prim.dmaRead _ _)
  | exact PrimsIn.lift (Prim.fork _)
  | exact PrimsIn.lift (Prim.fetched _ _)
  | exact PrimsIn.lift (Prim.served _ _)
  | exact PrimsIn.lift (Prim.status _ _)
  | exact PrimsIn.lift (Prim.latch _)
  | exact PrimsIn.lift (Prim.capture _ _ _)
  | exact PrimsIn.lift (Prim.push _ _)
  | exact PrimsIn.lift (Prim.pop _)
  | exact PrimsIn.lift (Prim.drain _)
  | exact PrimsIn.lift (Prim.fill _ _ _ _ _)
  | exact PrimsIn.lift (Prim.elem _ _ _ _ _ _ _)
  | exact PrimsIn.lift (Prim.idx _ _ _ _ _ _ _)
  | (apply PrimsIn.bind)
  | split
  | (dsimp only))

/-- The fill of a read request is a disk program. -/
theorem prims_fill (h : BitVec 16) (r : VioReq) : PrimsIn Prim (fill h r) := by
  unfold fill
  repeat prims_step

/-- The capture of a write request is a disk program. -/
theorem prims_capture (h : BitVec 16) (r : VioReq) : PrimsIn Prim (capture h r) := by
  unfold capture
  repeat prims_step

/-- The service of a request is a disk program: every primitive it can reach is a `Prim`. -/
theorem prims_serve (h : BitVec 16) : PrimsIn Prim (serve h) := by
  unfold serve
  repeat (first | exact prims_fill _ _ | exact prims_capture _ _ | prims_step)

/-- The disk's root loop is a disk program: every primitive it can reach is a `Prim`. -/
theorem prims_body : PrimsIn Prim body := by
  unfold body
  repeat prims_step

/-- Every task the disk forks runs a disk program. -/
theorem prims_task (t : VTask) : PrimsIn Prim (task t) := by
  cases t with
  | serve h => exact prims_serve h

/-! ### The pool runs the disk's programs -/

/-- The disk's state in a configuration. -/
abbrev disk (c : Cfg) : VirtioState := c.2.m.devs.st .virtio

/-- Every disk task in the pool runs the disk's programs: each primitive it can reach is one of
the disk's (`Prim`). -/
def progs (c : Cfg) : Prop := Gate.Progs .virtio Prim c

variable {i j : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-- Every step keeps the disk's tasks inside its programs. -/
theorem progs_step (hs : Step j c c') (h : progs c) : progs c' :=
  Gate.progs_step (d := .virtio) prims_body prims_task hs h

/-- On a run that starts with the disk's tasks inside its programs, they stay there. -/
theorem progs_run (hrun : PoolRun σ) (h0 : progs (σ 0)) : ∀ n, progs (σ n) :=
  Gate.progs_run (d := .virtio) prims_body prims_task hrun h0

/-! ### Association lists -/

/-- Searching a filtered list finds what the search finds in the list, when every element the
search accepts passes the filter. -/
theorem find?_filter_of {α : Type} {p q : α → Bool} (hpq : ∀ x, p x = true → q x = true)
    (l : List α) : (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hp : p x = true
    · simp [hpq x hp, hp]
    · by_cases hq : q x = true
      · simp [hq, hp, ih]
      · simp [hq, ih, hp]

/-- A key just set is found with its new value. -/
theorem alistGet_set_self {V : Type} (l : List (BitVec 16 × V)) (k : BitVec 16) (v : V) :
    alistGet (alistSet l k v) k = some v := by
  simp [alistGet, alistSet]

/-- Setting one key leaves every other key's value. -/
theorem alistGet_set_ne {V : Type} (l : List (BitVec 16 × V)) {k k' : BitVec 16} (v : V)
    (h : k' ≠ k) : alistGet (alistSet l k v) k' = alistGet l k' := by
  have hk : decide (k = k') = false := by simpa using Ne.symm h
  simp only [alistGet, alistSet, List.find?_cons, hk]
  rw [find?_filter_of]
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  rw [hx]
  exact h

/-- Deleting one key leaves every other key's value. -/
theorem alistGet_del_ne {K V : Type} [DecidableEq K] (l : List (K × V)) {k k' : K}
    (h : k' ≠ k) : alistGet (alistDel l k) k' = alistGet l k' := by
  simp only [alistGet, alistDel]
  rw [find?_filter_of]
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  rw [hx]
  exact h

/-- A key just deleted is absent. -/
theorem alistGet_del_self {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) :
    alistGet (alistDel l k) k = none := by
  simp only [alistGet, alistDel, Option.map_eq_none_iff, List.find?_eq_none, List.mem_filter]
  intro x hx
  simpa using hx.2

/-- Deleting a key keeps a key that was absent absent. -/
theorem alistGet_del_isSome {K V : Type} [DecidableEq K] (l : List (K × V)) (k k' : K)
    (h : (alistGet (alistDel l k) k').isSome) : (alistGet l k').isSome := by
  by_cases hk : k' = k
  · subst hk
    rw [alistGet_del_self] at h
    cases h
  · rwa [alistGet_del_ne l hk] at h

/-! ### The fields each move touches -/

/-- A head's phase just set is found. -/
theorem phase_setPhase_self (v : VirtioState) (h : BitVec 16) (ph : VPhase) :
    phase (setPhase v h ph) h = some ph := alistGet_set_self _ _ _

/-- Setting one head's phase leaves every other head's phase. -/
theorem phase_setPhase_ne (v : VirtioState) {h h' : BitVec 16} (ph : VPhase) (hne : h' ≠ h) :
    phase (setPhase v h ph) h' = phase v h' := alistGet_set_ne _ _ hne

/-- Setting a phase other than `.pushed` keeps the used ring free. -/
theorem pushOk_setPhase {v : VirtioState} (hv : pushOk v = true) (h : BitVec 16) {ph : VPhase}
    (hph : ph.isPushed = false) : pushOk (setPhase v h ph) = true := by
  simp only [pushOk, setPhase, alistSet, List.all_cons, List.all_eq_true] at hv ⊢
  refine Bool.and_eq_true_iff.2 ⟨by simp [hph], ?_⟩
  simp only [List.all_eq_true, List.mem_filter]
  exact fun x hx => hv x hx.1

/-- Removing a request from the in-flight map keeps the used ring free. -/
theorem pushOk_del {v : VirtioState} (hv : pushOk v = true) (h : BitVec 16) :
    (v.inflight.filter fun kv => kv.1 ≠ h).all (fun hp => !hp.2.isPushed) = true := by
  simp only [pushOk, List.all_eq_true, List.mem_filter] at hv ⊢
  exact fun x hx => hv x hx.1

/-- A drain moves only the medium and removes one cache entry, or does nothing. -/
theorem drain_eq (v : VirtioState) (s : Nat) :
    drain v s = v ∨ ∃ dk, drain v s = { v with disk := dk, cache := alistDel v.cache s } := by
  unfold drain
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- The capture's move changes only the cache and the head's phase. -/
theorem captureMove_eq (h : BitVec 16) (r : VioReq) (w : BitVec (8 * r.len.toNat))
    (v : VirtioState) : ∃ cc, captureMove h r w v = setPhase { v with cache := cc } h (.served r) := by
  unfold captureMove
  split
  · exact ⟨_, rfl⟩
  · exact ⟨v.cache, rfl⟩

/-- A disk read never moves the disk. -/
theorem readN_state {v v' : VirtioState} {off n : Nat} {w : BitVec (8 * n)}
    (h : readN v off n = some (w, v')) : v' = v := by
  unfold readN at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    rfl
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · cases h

/-- A value whose recast to another width is zero is zero. -/
theorem castW_eq_zero {m n : Nat} (h : m = n) {w : BitVec m} (hw : castW h w = 0) : w = 0 := by
  subst h
  exact hw

/-- Every answer of a conditional is an answer of one of its branches, under its condition. -/
theorem ite_some {α : Type} {p : Prop} [Decidable p] {a b : Option α} {Q : α → Prop}
    (ha : p → ∀ x, a = some x → Q x) (hb : ¬ p → ∀ x, b = some x → Q x) :
    ∀ x, (if p then a else b) = some x → Q x := by
  intro x hx
  by_cases hp : p
  · simp only [hp, ↓reduceIte] at hx
    exact ha hp x hx
  · simp only [hp, ↓reduceIte] at hx
    exact hb hp x hx

/-- A 32-bit register write is a device reset (a zero to the status register), or it moves only
the configuration and the interrupt status. -/
theorem write_cases (v : VirtioState) (off : Nat) (w : BitVec 32) :
    ∀ v', write v off w = some v' →
      (off = offStatus ∧ w = 0#32 ∧ v' = reset v) ∨
      ∃ cfg isr, v' = { v with cfg := cfg, isr := isr } := by
  unfold write
  repeat (first
    | (refine ite_some (fun _ => ?_) (fun _ => ?_))
    | (intro x hx; cases hx; exact Or.inl ⟨‹_›, ‹_›, rfl⟩)
    | (intro x hx; cases hx; exact Or.inr ⟨_, _, rfl⟩)
    | (intro x hx; cases hx))

/-- A disk write is a device reset (a 4-byte zero to the status register), or it moves only the
configuration and the interrupt status. -/
theorem writeN_cases {v v' : VirtioState} {off n : Nat} {w : BitVec (8 * n)}
    (h : writeN v off n w = some v') :
    (off = offStatus ∧ n = 4 ∧ w = 0 ∧ v' = reset v) ∨
    ∃ cfg isr, v' = { v with cfg := cfg, isr := isr } := by
  unfold writeN at h
  split at h
  · rename_i hn
    subst hn
    rcases write_cases v off _ v' h with ⟨hoff, hz, rfl⟩ | hrest
    · exact Or.inl ⟨hoff, rfl, castW_eq_zero _ hz, rfl⟩
    · exact Or.inr hrest
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Or.inr ⟨_, _, rfl⟩
    · cases h

/-- The disk moves from `v` to `v'` at primitive `o`: a guarded update, or a DMA write, whose
guard answers `v'`. -/
def moves : DevOp VirtioState VTask → VirtioState → VirtioState → Prop
  | .step g, v, v' => ∃ os, g v = some (v', os)
  | .dmaWrite g _ _ _, v, v' => g v = some v'
  | _, _, _ => False

/-- The disk moves at a `modify` node by its function. -/
theorem moves_modify {f : VirtioState → VirtioState} {v v' : VirtioState} :
    moves (.step (modifyG f)) v v' ↔ v' = f v := by
  simp only [moves, modifyG, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, rfl, -⟩
    rfl
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

/-- The disk moves at a `guard` node by its guard's answer. -/
theorem moves_guard {g : VirtioState → Option VirtioState} {v v' : VirtioState} :
    moves (.step (guardG g)) v v' ↔ g v = some v' := by
  simp only [moves, guardG, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨_, _, h, rfl, -⟩
    exact h
  · intro h
    exact ⟨_, _, h, rfl, rfl⟩

/-- **What a step does to the disk.**  When every disk task runs the disk's programs, a step of a
thread that is not the power thread leaves the disk as it was, or it is a live disk task's move at
one of the disk's primitives, or it is a live hart's MMIO write to the disk's window.  (A hart's
MMIO read never moves the disk.) -/
theorem step_cases (hs : Step j c c') (hnp : ∀ e, c.1[j]? = some e → e ≠ .power) (hp : progs c) :
    disk c' = disk c ∨
    (∃ e tid o k, c.1[j]? = some (.dev e .virtio tid (.op o k)) ∧ threadLive c.2 e ∧ Prim o ∧
      moves o (disk c) (disk c')) ∨
    (∃ e cpu req w tags k off,
      c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) ∧
      threadLive c.2 e ∧ devDecode req.pa = some (.virtio, off) ∧
      writeN (disk c) off req.size w = some (disk c')) := by
  rcases Gate.devSt_step hs hnp .virtio with h | ⟨e, tid, g, k, he, hl, os, hg⟩ |
    ⟨e, tid, g, pa, n, w, k, he, hl, hg⟩ | ⟨e, cpu, req, k, off, he, hl, hdec, w, hr⟩ |
    ⟨e, cpu, req, w, tags, k, off, he, hl, hdec, hw⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨e, tid, .step g, k, he, hl, (hp _ _ _ _ he).1, os, hg⟩)
  · exact Or.inr (Or.inl ⟨e, tid, .dmaWrite g pa n w, k, he, hl, (hp _ _ _ _ he).1, hg⟩)
  · exact Or.inl (readN_state hr)
  · exact Or.inr (Or.inr ⟨e, cpu, req, w, tags, k, off, he, hl, hdec, hw⟩)

/-! ### The guards' answers -/

/-- The capture latch answers exactly when it is free, by taking it. -/
theorem captureGuard_some {h : BitVec 16} {v v' : VirtioState} :
    captureGuard h v = some v' ↔ v.taken = none ∧ v' = { v with taken := some h } := by
  unfold captureGuard
  split
  · simp only [Option.some.injEq, true_and, *]
    exact eq_comm
  · simp only [reduceCtorEq, false_iff, not_and]
    exact fun h' => absurd h' ‹¬ v.taken = none›

/-- The completion-and-push gate's condition: the request is in flight, its completion gate
(`completeOk`) holds, and no request is between its used element and its used index. -/
def pushOpen (h : BitVec 16) (r : VioReq) (v : VirtioState) : Prop :=
  (phase v h).isSome = true ∧ completeOk v r h = true ∧ pushOk v = true

/-- The completion-and-push guard answers exactly when its condition holds, by moving the request
to `.pushed`. -/
theorem pushGuard_some {h : BitVec 16} {r : VioReq} {v v' : VirtioState} :
    pushGuard h r v = some v' ↔ pushOpen h r v ∧ v' = setPhase v h (.pushed r) := by
  unfold pushGuard pushOpen
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [Option.some.injEq, hc, and_self, true_and]
    exact eq_comm
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h1 _ => absurd ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩ hc

/-- The pop guard answers exactly when the head is not in flight, by putting it in flight. -/
theorem popGuard_some {h : BitVec 16} {v v' : VirtioState} :
    popGuard h v = some v' ↔
      (phase v h).isSome = false ∧ v' = { setPhase v h .popped with seen := v.seen + 1#16 } := by
  unfold popGuard
  split
  · rename_i hc
    simp only [reduceCtorEq, false_iff, not_and, hc]
    exact fun h => absurd h (by simp)
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    simp only [Option.some.injEq, hc, true_and]
    exact eq_comm

/-- The fill's guard answers exactly when the request is still `r`, by moving nothing. -/
theorem reqGuard_some {h : BitVec 16} {r : VioReq} {v v' : VirtioState} :
    reqGuard h r v = some v' ↔ reqOf v h = some r ∧ v' = v := by
  unfold reqGuard
  split
  · rename_i hc
    simp only [decide_eq_true_eq] at hc
    simp only [Option.some.injEq, hc, true_and]
    exact eq_comm
  · rename_i hc
    simp only [decide_eq_true_eq] at hc
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h hc

/-- The condition of the used element's and the used index's guards: the request is still the
one fetched, and the used index and the configuration are those of the snapshot. -/
def snapOk (h : BitVec 16) (r : VioReq) (ui : BitVec 16) (c : VirtioCfg) (v : VirtioState) :
    Prop :=
  reqOf v h = some r ∧ v.usedIdx = ui ∧ v.cfg = c

/-- The used element's guard answers exactly at the snapshot, by moving nothing. -/
theorem elemGuard_some {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {v v' : VirtioState} : elemGuard h r ui c v = some v' ↔ snapOk h r ui c v ∧ v' = v := by
  unfold elemGuard snapOk
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq, hc, and_self, true_and]
    exact eq_comm
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h1 _ => absurd ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩ hc

/-- The used index's guard answers exactly at the snapshot, by the completion. -/
theorem idxGuard_some {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {v v' : VirtioState} : idxGuard h r ui c v = some v' ↔ snapOk h r ui c v ∧ v' = complete v h := by
  unfold idxGuard snapOk
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq, hc, and_self, true_and]
    exact eq_comm
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h1 _ => absurd ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩ hc

/-- The stall never moves the disk. -/
theorem stall_never {v v' : VirtioState} : ¬ moves (.step stallG) v v' := by
  rintro ⟨_, h⟩
  simp [stallG] at h

/-- At a guarded update of the disk (a silent device), the gate is open exactly when the guard
answers. -/
theorem notBlocked_guard {g : VirtioState → Option VirtioState} {m : MState} :
    ¬ devBlocked .virtio (.step (guardG g)) m ↔ (g (m.devs.st .virtio)).isSome = true := by
  show ¬ (∀ s' os, guardG g (m.devs.st .virtio) = some (s', os) → ¬ os = []) ↔ _
  constructor
  · intro hb
    cases hg : g (m.devs.st .virtio) with
    | none =>
      refine absurd (fun s' os hs => ?_) hb
      simp [guardG, hg] at hs
    | some s' => rfl
  · intro hs hb
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hs
    exact hb s' [] (by simp [guardG, hs']) rfl

/-! ### The skeleton of a disk gate's stability -/

/-- A disk gate whose condition `Q` on the disk is kept by every move at a primitive of the
disk's programs outside the closing class `K`, and by every hart's MMIO write to the disk that
meets the side condition `M`, is stable under every other thread's step but the power thread's
that keeps the disk's tasks inside its programs, meets `M` and is not a step by another live
disk task at a node in `K`. -/
theorem stable_of {o : DevOp VirtioState VTask} {tid : TaskId} {Q : VirtioState → Prop}
    {K : DevOp VirtioState VTask → Prop} {M : Cfg → Cfg → Prop}
    (htask : ∀ {o' v v'}, Prim o' → ¬ K o' → moves o' v v' → Q v → Q v')
    (hmmio : ∀ {j c c' e cpu req w tags k off}, Step j c c' →
      c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) →
      threadLive c.2 e → devDecode req.pa = some (.virtio, off) →
      writeN (disk c) off req.size w = some (disk c') → M c c' → Q (disk c) → Q (disk c')) :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧ M c c' ∧
        (taskAt i .virtio tid o c ∧ Q (disk c) → ¬ Gate.stepBy i .virtio K c c'))
      (fun c => taskAt i .virtio tid o c ∧ Q (disk c)) := by
  intro j c c' hji hs hnp ⟨hp, hM, hK⟩ ⟨ht, hq⟩
  refine ⟨taskAt_stable hji hs hnp ht, ?_⟩
  rcases step_cases hs hnp hp with h | ⟨e, tid', o', k, he, hl, hP, hm⟩ |
    ⟨e, cpu, req, w, tags, k, off, he, hl, hdec, hw⟩
  · rw [h]
    exact hq
  · exact htask hP (fun hKo => hK ⟨ht, hq⟩ ⟨j, e, tid', o', k, hji, hs, he, hl, hKo⟩) hm hq
  · exact hmmio hs he hl hdec hw hM hq

/-- The skeleton's persistence: on a run whose disk tasks stay inside the disk's programs, whose
every step meets `M`, and where no other live disk task steps at a node in `K` while the gate is
open, an open gate stays open until the task steps through it, or never opens again. -/
theorem persists_of {o : DevOp VirtioState VTask} {tid : TaskId} {Q : VirtioState → Prop}
    {K : DevOp VirtioState VTask → Prop} {M : Cfg → Cfg → Prop}
    (htask : ∀ {o' v v'}, Prim o' → ¬ K o' → moves o' v v' → Q v → Q v')
    (hmmio : ∀ {j c c' e cpu req w tags k off}, Step j c c' →
      c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) →
      threadLive c.2 e → devDecode req.pa = some (.virtio, off) →
      writeN (disk c) off req.size w = some (disk c') → M c c' → Q (disk c) → Q (disk c'))
    (hrun : PoolRun σ) (hprog : ∀ n, progs (σ n)) (hM : ∀ n, M (σ n) (σ (n + 1)))
    (hK : ∀ n, taskAt i .virtio tid o (σ n) ∧ Q (disk (σ n)) →
      ¬ Gate.stepBy i .virtio K (σ n) (σ (n + 1))) :
    Persists i (fun c => taskAt i .virtio tid o c ∧ Q (disk c)) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ h => taskAt_live h.1) (stable_of htask hmmio)
    fun n => ⟨hprog n, hM n, hK n⟩

/-! ### The nodes and the closing classes -/

/-- The capture-latch node of the serving task of head `h` (a write request's). -/
abbrev latchOp (h : BitVec 16) : DevOp VirtioState VTask := .step (guardG (captureGuard h))

/-- The completion-and-push node of the serving task of head `h` and request `r`. -/
abbrev pushOp (h : BitVec 16) (r : VioReq) : DevOp VirtioState VTask :=
  .step (guardG (pushGuard h r))

/-- The root's pop node for head `h`. -/
abbrev popOp (h : BitVec 16) : DevOp VirtioState VTask := .step (guardG (popGuard h))

/-- A capture-latch node, of any head. -/
def isLatch (o : DevOp VirtioState VTask) : Prop := ∃ h, o = latchOp h

/-- A capture node (a write request's payload laid into the cache), of any head. -/
def isCapture (o : DevOp VirtioState VTask) : Prop :=
  ∃ h r w, o = .step (modifyG (captureMove h r w))

/-- A completion-and-push node, of any head. -/
def isPush (o : DevOp VirtioState VTask) : Prop := ∃ h r, o = pushOp h r

/-- A used-index write (the completion), of any head. -/
def isUsedIdx (o : DevOp VirtioState VTask) : Prop :=
  ∃ h r ui c pa n w, o = .dmaWrite (idxGuard h r ui c) pa n w

/-- The used-index write (the completion) of head `h`. -/
def completes (h : BitVec 16) (o : DevOp VirtioState VTask) : Prop :=
  ∃ r ui c pa n w, o = .dmaWrite (idxGuard h r ui c) pa n w

/-- A serving task's phase write for head `h` that never blocks: the moves to `.fetched`,
`.served` and `.status`, and the capture. -/
def servesHead (h : BitVec 16) (o : DevOp VirtioState VTask) : Prop :=
  (∃ r, o = .step (modifyG fun v => setPhase v h (.fetched r))) ∨
  (∃ r, o = .step (modifyG fun v => setPhase v h (.served r))) ∨
  (∃ r, o = .step (modifyG fun v => setPhase v h (.status r))) ∨
  (∃ r w, o = .step (modifyG (captureMove h r w)))

/-- The completion-and-push node of head `h`. -/
def pushesHead (h : BitVec 16) (o : DevOp VirtioState VTask) : Prop := ∃ r, o = pushOp h r

/-- The pop node of head `h`. -/
def popsHead (h : BitVec 16) (o : DevOp VirtioState VTask) : Prop := o = popOp h

/-! ### The capture latch -/

/-- The capture latch stays free under every move of the disk's programs but another latch. -/
theorem latch_move {o : DevOp VirtioState VTask} {v v' : VirtioState} (hp : Prim o)
    (hK : ¬ isLatch o) (hm : moves o v v') (hv : v.taken = none) : v'.taken = none := by
  cases hp with
  | get | choose | dmaRead | fork => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched h r | served h r | status h r =>
    rw [moves_modify] at hm
    subst hm
    exact hv
  | latch h => exact absurd ⟨h, rfl⟩ hK
  | capture h r w =>
    rw [moves_modify] at hm
    subst hm
    obtain ⟨cc, e⟩ := captureMove_eq h r w v
    rw [e]
    exact hv
  | push h r =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact hv
  | pop h =>
    rw [moves_guard, popGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact hv
  | drain j =>
    rw [moves_modify] at hm
    subst hm
    rcases drain_eq v _ with e | ⟨dk, e⟩ <;> rw [drainMove, e] <;> exact hv
  | fill h r pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact hv
  | elem h r ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact hv
  | idx h r ui c pa n w =>
    obtain ⟨-, rfl⟩ := idxGuard_some.1 hm
    simp [complete, hv]

/-- A hart's MMIO write keeps the capture latch free: a reset frees it, every other write leaves
it alone. -/
theorem latch_writeN {v v' : VirtioState} {off n : Nat} {w : BitVec (8 * n)}
    (h : writeN v off n w = some v') (hv : v.taken = none) : v'.taken = none := by
  rcases writeN_cases h with ⟨-, -, -, rfl⟩ | ⟨cfg, isr, rfl⟩
  · rfl
  · exact hv

/-- The capture latch's guard answers exactly when the latch is free. -/
theorem captureGuard_isSome {h : BitVec 16} {v : VirtioState} :
    (captureGuard h v).isSome = true ↔ v.taken = none := by
  unfold captureGuard
  split <;> simp_all

variable {tid : TaskId}

/-- The capture-latch gate is open exactly when the latch is free. -/
theorem enabled_latch_iff {h : BitVec 16} :
    Gate.enabled i .virtio tid (latchOp h) c ↔
      taskAt i .virtio tid (latchOp h) c ∧ (disk c).taken = none := by
  unfold Gate.enabled
  rw [notBlocked_guard, captureGuard_isSome]

/-- **The capture latch is a stable gate except for the latch itself.**  Once the capture latch
of the serving task of head `h` is free, it stays free under every other thread's step but the
power thread's, when the disk's tasks run its programs, except for another live disk task taking
a capture latch (of any head).  No MMIO write closes it: a reset frees the latch, every other
write leaves it alone; nor does a completion, which frees only its own head's latch. -/
theorem latch_stable {h : BitVec 16} :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧
        (Gate.enabled i .virtio tid (latchOp h) c → ¬ Gate.stepBy i .virtio isLatch c c'))
      (Gate.enabled i .virtio tid (latchOp h)) := by
  intro j c c' hji hs hnp hP hA
  rw [enabled_latch_iff] at hA ⊢
  exact stable_of (M := fun _ _ => True) (K := isLatch) latch_move
    (fun _ _ _ _ hw _ hq => latch_writeN hw hq) hji hs hnp
    ⟨hP.1, trivial, fun ha => hP.2 (enabled_latch_iff.2 ha)⟩ hA

/-- The capture latch persists on a run whose disk tasks run its programs and where no other live
disk task takes a capture latch while this one is open. -/
theorem latch_persists {h : BitVec 16} (hrun : PoolRun σ) (hprog : ∀ n, progs (σ n))
    (hK : ∀ n, Gate.enabled i .virtio tid (latchOp h) (σ n) →
      ¬ Gate.stepBy i .virtio isLatch (σ n) (σ (n + 1))) :
    Persists i (Gate.enabled i .virtio tid (latchOp h)) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ => Gate.live) latch_stable fun n => ⟨hprog n, hK n⟩

/-- Strong fairness of the capture latch, under the same hypotheses and fair scheduling. -/
theorem latch_sf {h : BitVec 16} (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (hprog : ∀ n, progs (σ n))
    (hK : ∀ n, Gate.enabled i .virtio tid (latchOp h) (σ n) →
      ¬ Gate.stepBy i .virtio isLatch (σ n) (σ (n + 1))) :
    Gate.SF i .virtio tid (latchOp h) σ :=
  Gate.sf_of_persists (fun h => h) hsched (latch_persists hrun hprog hK)

/-! ### The hypotheses on the harts' MMIO writes -/

/-- The thread at `j` is a live hart whose head event is a busy reset of the disk: a 4-byte store
of zero to the status register while a request is in flight. -/
def busyReset (j : Nat) (c : Cfg) : Prop :=
  ∃ e cpu req w tags k,
    c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) ∧
    threadLive c.2 e ∧ devDecode req.pa = some (.virtio, offStatus) ∧ req.size = 4 ∧ w = 0 ∧
    (disk c).inflight ≠ []

/-- The step from `c` to `c'` is not a busy reset. -/
def noBusyReset (c c' : Cfg) : Prop := ∀ j, Step j c c' → ¬ busyReset j c

/-- No step of the run is a busy reset. -/
def NoBusyReset (σ : Nat → Cfg) : Prop := ∀ n, noBusyReset (σ n) (σ (n + 1))

/-- The thread at `j` is a live hart whose head event is a store to the disk's window other than a
reset, while a request is in flight. -/
def busyStore (j : Nat) (c : Cfg) : Prop :=
  ∃ e cpu req w tags k off,
    c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) ∧
    threadLive c.2 e ∧ devDecode req.pa = some (.virtio, off) ∧
    ¬ (off = offStatus ∧ req.size = 4 ∧ w = 0) ∧ (disk c).inflight ≠ []

/-- The step from `c` to `c'` does not turn the write-back cache mode off by a store to the disk
that is not a reset, while a request is in flight. -/
def noWceOff (c c' : Cfg) : Prop :=
  ∀ j, Step j c c' → busyStore j c → wce (disk c).cfg = true → wce (disk c').cfg = true

/-- No step of the run turns the write-back cache mode off while a request is in flight (other
than by a reset). -/
def NoWceOff (σ : Nat → Cfg) : Prop := ∀ n, noWceOff (σ n) (σ (n + 1))

/-- The step from `c` to `c'` does not change the disk's configuration by a store that is not a
reset, while a request is in flight. -/
def noConfigWrite (c c' : Cfg) : Prop :=
  ∀ j, Step j c c' → busyStore j c → (disk c').cfg = (disk c).cfg

/-- No step of the run changes the disk's configuration while a request is in flight (other than
by a reset). -/
def NoConfigWrite (σ : Nat → Cfg) : Prop := ∀ n, noConfigWrite (σ n) (σ (n + 1))

/-- A hart's MMIO write while a request is in flight, at a step that is no busy reset, is no
reset: it moves only the configuration and the interrupt status, and it is a `busyStore`. -/
theorem mmio_cases {j : Nat} {c c' : Cfg} {e : Nat} {cpu : CPU} {req : MemRequest}
    {w : BitVec (8 * req.size)} {tags : BitVec req.numTag} {k} {off : Nat} (hs : Step j c c')
    (he : c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)))
    (hl : threadLive c.2 e) (hdec : devDecode req.pa = some (.virtio, off))
    (hw : writeN (disk c) off req.size w = some (disk c')) (hR : noBusyReset c c')
    (hin : (disk c).inflight ≠ []) :
    busyStore j c ∧ ∃ cfg isr, disk c' = { disk c with cfg := cfg, isr := isr } := by
  by_cases hr : off = offStatus ∧ req.size = 4 ∧ w = 0
  · obtain ⟨rfl, hsz, hz⟩ := hr
    exact absurd ⟨e, cpu, req, w, tags, k, he, hl, hdec, hsz, hz, hin⟩ (hR j hs)
  · refine ⟨⟨e, cpu, req, w, tags, k, off, he, hl, hdec, hr, hin⟩, ?_⟩
    rcases writeN_cases hw with ⟨h1, h2, h3, -⟩ | h
    · exact absurd ⟨h1, h2, h3⟩ hr
    · exact h

/-- A step of a hart whose head event is a store leaves the disk as it was or is that store's
MMIO write to the disk. -/
theorem store_step {j : Nat} {c c' : Cfg} {e : Nat} {cpu : CPU} {req : MemRequest}
    {w : BitVec (8 * req.size)} {tags : BitVec req.numTag} {k} (hs : Step j c c')
    (he : c.1[j]? = some (.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k))) :
    disk c' = disk c ∨
    ∃ off, devDecode req.pa = some (.virtio, off) ∧ writeN (disk c) off req.size w = some (disk c') := by
  have hnp : ∀ x, c.1[j]? = some x → x ≠ .power := by
    intro x hx hxp
    rw [he, hxp] at hx
    cases hx
  rcases Gate.devSt_step hs hnp .virtio with h | ⟨_, _, _, _, he', -⟩ |
    ⟨_, _, _, _, _, _, _, he', -⟩ | ⟨_, _, _, _, _, he', -⟩ |
    ⟨e', cpu', req', w', tags', k', off, he', -, hdec, hw⟩
  · exact Or.inl h
  · rw [he] at he'
    cases he'
  · rw [he] at he'
    cases he'
  · rw [he] at he'
    cases he'
  · rw [he] at he'
    cases he'
    exact Or.inr ⟨off, hdec, hw⟩

/-- Every live hart whose head event is a store to the disk's window stores to the queue-notify
or the interrupt-acknowledge register: what the kernel does after the disk's initialisation. -/
def kernelStores (c : Cfg) : Prop :=
  ∀ (j e : Nat) (cpu : CPU) (req : MemRequest) (w : BitVec (8 * req.size))
    (tags : BitVec req.numTag) k (off : Nat),
    c.1[j]? = some (Expr.hart e cpu (.impure (.inl (.ok (.memWrite req w tags))) k)) →
    threadLive c.2 e → devDecode req.pa = some (.virtio, off) →
    off = offQueueNotify ∨ off = offInterruptAck

/-- A store to the queue-notify or the interrupt-acknowledge register leaves the configuration
as it was. -/
theorem writeN_cfg_notify_ack {v v' : VirtioState} {off n : Nat} {w : BitVec (8 * n)}
    (hoff : off = offQueueNotify ∨ off = offInterruptAck) (h : writeN v off n w = some v') :
    v'.cfg = v.cfg := by
  unfold writeN at h
  split at h
  · rcases hoff with rfl | rfl
    · have e : write v offQueueNotify (castW (by omega) w) = some v := rfl
      rw [e] at h
      cases h
      rfl
    · have e : write v offInterruptAck (castW (by omega) w) =
          some { v with isr := v.isr &&& ~~~(castW (by omega) w) } := rfl
      rw [e] at h
      cases h
      rfl
  · split at h
    · cases h
      rfl
    · cases h

/-- When the harts store to the disk only at the queue-notify and the interrupt-acknowledge
registers, no step changes the configuration. -/
theorem noConfigWrite_of_kernelStores {c c' : Cfg} (h : kernelStores c) : noConfigWrite c c' := by
  rintro j hs ⟨e, cpu, req, w, tags, k, off, he, hl, hdec, -, -⟩
  rcases store_step hs he with hd | ⟨off', hdec', hw⟩
  · rw [hd]
  · exact writeN_cfg_notify_ack (h j e cpu req w tags k off' he hl hdec') hw

/-- When the harts store to the disk only at the queue-notify and the interrupt-acknowledge
registers, no step turns the write-back mode off. -/
theorem noWceOff_of_kernelStores {c c' : Cfg} (h : kernelStores c) : noWceOff c c' := by
  intro j hs hst hw
  rw [noConfigWrite_of_kernelStores h j hs hst]
  exact hw

/-- When the harts store to the disk only at the queue-notify and the interrupt-acknowledge
registers, no step is a busy reset. -/
theorem noBusyReset_of_kernelStores {c c' : Cfg} (h : kernelStores c) : noBusyReset c c' := by
  rintro j _ ⟨e, cpu, req, w, tags, k, he, hl, hdec, -, -, -⟩
  rcases h j e cpu req w tags k _ he hl hdec with h1 | h1 <;> cases h1

/-- A head in flight makes the in-flight map nonempty. -/
theorem inflight_ne_nil {v : VirtioState} {h : BitVec 16} (hv : (phase v h).isSome = true) :
    v.inflight ≠ [] := by
  intro he
  simp [phase, he, alistGet] at hv

/-- A request past its fetch is in flight. -/
theorem phase_isSome_of_reqOf {v : VirtioState} {h : BitVec 16} {r : VioReq}
    (hv : reqOf v h = some r) : (phase v h).isSome = true := by
  unfold reqOf at hv
  cases hp : phase v h with
  | none => rw [hp] at hv; cases hv
  | some _ => rfl

/-- Setting any head's phase keeps a head in flight in flight. -/
theorem phase_isSome_setPhase {v : VirtioState} {h h' : BitVec 16} {ph : VPhase}
    (hv : (phase v h).isSome = true) : (phase (setPhase v h' ph) h).isSome = true := by
  by_cases hh : h = h'
  · subst hh
    rw [phase_setPhase_self]
    rfl
  · rw [phase_setPhase_ne _ _ hh]
    exact hv

/-- A completion leaves every other head's phase. -/
theorem phase_complete_ne {v : VirtioState} {h h' : BitVec 16} (hh : h ≠ h') :
    phase (complete v h') h = phase v h :=
  alistGet_del_ne _ hh

/-- A head's request record is read off its phase. -/
theorem reqOf_of_phase {v v' : VirtioState} {h : BitVec 16} (e : phase v' h = phase v h) :
    reqOf v' h = reqOf v h := by
  unfold reqOf
  rw [e]

/-! ### The root's pop guard -/

/-- The pop guard answers exactly when the head is not in flight. -/
theorem popGuard_isSome {h : BitVec 16} {v : VirtioState} :
    (popGuard h v).isSome = true ↔ (phase v h).isSome = false := by
  unfold popGuard
  split <;> simp_all

/-- The pop gate is open exactly when the head is not in flight. -/
theorem enabled_pop_iff {h : BitVec 16} :
    Gate.enabled i .virtio tid (popOp h) c ↔
      taskAt i .virtio tid (popOp h) c ∧ (phase (disk c) h).isSome = false := by
  unfold Gate.enabled
  rw [notBlocked_guard, popGuard_isSome]

/-- A head that is not in flight stays out of flight under every move of the disk's programs but a
serving task's phase write for that head and another pop of it. -/
theorem pop_move {h : BitVec 16} {o : DevOp VirtioState VTask} {v v' : VirtioState}
    (hp : Prim o) (hK : ¬ (servesHead h o ∨ popsHead h o)) (hm : moves o v v')
    (hv : (phase v h).isSome = false) : (phase v' h).isSome = false := by
  cases hp with
  | get | choose | dmaRead | fork => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched h' r =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inl ⟨r, rfl⟩)) hK
    · rw [phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | served h' r =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inl ⟨r, rfl⟩))) hK
    · rw [phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | status h' r =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inr (Or.inl ⟨r, rfl⟩)))) hK
    · rw [phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | latch h' =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact hv
  | capture h' r w =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inr (Or.inr ⟨r, w, rfl⟩)))) hK
    · obtain ⟨cc, e⟩ := captureMove_eq h' r w v
      rw [e, phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | push h' r =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨⟨hph, -⟩, rfl⟩ := hm
    by_cases hh : h' = h
    · subst hh
      rw [hph] at hv
      cases hv
    · rw [phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | pop h' =>
    rw [moves_guard, popGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inr rfl) hK
    · show (phase (setPhase v h' .popped) h).isSome = false
      rw [phase_setPhase_ne _ _ (Ne.symm hh)]
      exact hv
  | drain j =>
    rw [moves_modify] at hm
    subst hm
    rcases drain_eq v _ with e | ⟨dk, e⟩ <;> rw [drainMove, e] <;> exact hv
  | fill h' r pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact hv
  | elem h' r ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact hv
  | idx h' r ui c pa n w =>
    obtain ⟨-, rfl⟩ := idxGuard_some.1 hm
    by_cases hh : h' = h
    · subst hh
      show (alistGet (alistDel v.inflight h') h').isSome = false
      rw [alistGet_del_self]
      rfl
    · rw [phase_complete_ne (Ne.symm hh)]
      exact hv

/-- A hart's MMIO write keeps a head out of flight: a reset empties the in-flight map, every other
write leaves it alone. -/
theorem pop_writeN {h : BitVec 16} {v v' : VirtioState} {off n : Nat} {w : BitVec (8 * n)}
    (hw : writeN v off n w = some v') (hv : (phase v h).isSome = false) :
    (phase v' h).isSome = false := by
  rcases writeN_cases hw with ⟨-, -, -, rfl⟩ | ⟨cfg, isr, rfl⟩
  · rfl
  · exact hv

/-- **The root's pop guard is a stable gate except for the phase writes of its head.**  Once head
`h` is not in flight, it stays out of flight under every other thread's step but the power
thread's, when the disk's tasks run its programs, except for another live disk task writing the
phase of `h` without blocking (the moves to `.fetched`, `.served` and `.status`, and the
capture: a stale serving task of `h`, which a busy reset leaves behind) or popping `h` (a second
root).  No MMIO write closes it, nor does a completion (it removes its head), nor a push (it
needs its head in flight). -/
theorem pop_stable {h : BitVec 16} :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧ (Gate.enabled i .virtio tid (popOp h) c →
        ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ popsHead h o) c c'))
      (Gate.enabled i .virtio tid (popOp h)) := by
  intro j c c' hji hs hnp hP hA
  rw [enabled_pop_iff] at hA ⊢
  exact stable_of (M := fun _ _ => True) (K := fun o => servesHead h o ∨ popsHead h o) pop_move
    (fun _ _ _ _ hw _ hq => pop_writeN hw hq) hji hs hnp
    ⟨hP.1, trivial, fun ha => hP.2 (enabled_pop_iff.2 ha)⟩ hA

/-- The pop guard persists on a run whose disk tasks run its programs and where no other live disk
task writes the head's phase or pops it while the gate is open. -/
theorem pop_persists {h : BitVec 16} (hrun : PoolRun σ) (hprog : ∀ n, progs (σ n))
    (hK : ∀ n, Gate.enabled i .virtio tid (popOp h) (σ n) →
      ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ popsHead h o) (σ n) (σ (n + 1))) :
    Persists i (Gate.enabled i .virtio tid (popOp h)) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ => Gate.live) pop_stable fun n => ⟨hprog n, hK n⟩

/-- Strong fairness of the pop guard, under the same hypotheses and fair scheduling. -/
theorem pop_sf {h : BitVec 16} (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (hprog : ∀ n, progs (σ n))
    (hK : ∀ n, Gate.enabled i .virtio tid (popOp h) (σ n) →
      ¬ Gate.stepBy i .virtio (fun o => servesHead h o ∨ popsHead h o) (σ n) (σ (n + 1))) :
    Gate.SF i .virtio tid (popOp h) σ :=
  Gate.sf_of_persists (fun h => h) hsched (pop_persists hrun hprog hK)

/-! ### The completion-and-push gate -/

/-- The completion gate is monotone: it stays open when the latch, if held by the request, stays
held, the write-back mode, if on, stays on, the request's sectors leave the cache or stay, and an
empty cache stays empty. -/
theorem completeOk_mono {v v' : VirtioState} {r : VioReq} {h : BitVec 16}
    (ht : v.taken = some h → v'.taken = some h)
    (hw : wce v.cfg = true → wce v'.cfg = true)
    (hc : reqCached v' r = true → reqCached v r = true)
    (he : v.cache.isEmpty = true → v'.cache.isEmpty = true)
    (hv : completeOk v r h = true) : completeOk v' r h = true := by
  unfold completeOk at hv ⊢
  by_cases h1 : r.type.toNat = blkTOut
  · simp only [h1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hv ⊢
    refine ⟨ht hv.1, ?_⟩
    rcases hv.2 with hw' | hc'
    · exact Or.inl (hw hw')
    · refine Or.inr ?_
      cases hcc : reqCached v' r with
      | false => rfl
      | true => rw [hc hcc] at hc'; cases hc'
  · simp only [h1, ↓reduceIte] at hv ⊢
    by_cases h2 : r.type.toNat = blkTFlush
    · simp only [h2, ↓reduceIte] at hv ⊢
      exact he hv
    · simp only [h2, ↓reduceIte] at hv ⊢

/-- Removing a cache entry caches no sector of a request that was not cached. -/
theorem reqCached_del {v : VirtioState} {r : VioReq} {s : Nat} {dk : Nat → BitVec 8}
    (h : reqCached { v with disk := dk, cache := alistDel v.cache s } r = true) :
    reqCached v r = true := by
  simp only [reqCached, List.any_eq_true] at h ⊢
  obtain ⟨i, hi, hs⟩ := h
  exact ⟨i, hi, alistGet_del_isSome _ _ _ hs⟩

/-- Removing an entry from an empty cache leaves it empty. -/
theorem isEmpty_del {l : List (Nat × List (BitVec 8))} {s : Nat} (h : l.isEmpty = true) :
    (alistDel l s).isEmpty = true := by
  cases l with
  | nil => rfl
  | cons _ _ => cases h

/-- The completion-and-push gate stays open under every move of the disk's programs but a capture
(of any head), a push (of any head) and the completion of its own head. -/
theorem push_move {h : BitVec 16} {r : VioReq} {o : DevOp VirtioState VTask}
    {v v' : VirtioState} (hp : Prim o) (hK : ¬ (isCapture o ∨ isPush o ∨ completes h o))
    (hm : moves o v v') (hv : pushOpen h r v) : pushOpen h r v' := by
  obtain ⟨hph, hco, hpu⟩ := hv
  cases hp with
  | get | choose | dmaRead | fork => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched h' r' | served h' r' | status h' r' =>
    rw [moves_modify] at hm
    subst hm
    exact ⟨phase_isSome_setPhase hph, hco, pushOk_setPhase hpu _ rfl⟩
  | latch h' =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨ht, rfl⟩ := hm
    refine ⟨hph, completeOk_mono (v := v) (fun e => ?_) id id id hco, hpu⟩
    rw [ht] at e
    cases e
  | capture h' r' w => exact absurd (Or.inl ⟨h', r', w, rfl⟩) hK
  | push h' r' => exact absurd (Or.inr (Or.inl ⟨h', r', rfl⟩)) hK
  | pop h' =>
    rw [moves_guard, popGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact ⟨phase_isSome_setPhase (h' := h') (ph := .popped) hph, hco,
      pushOk_setPhase (ph := .popped) hpu h' rfl⟩
  | drain j =>
    rw [moves_modify] at hm
    subst hm
    rcases drain_eq v (v.cache.getD j (0, [])).1 with e | ⟨dk, e⟩ <;> rw [drainMove, e]
    · exact ⟨hph, hco, hpu⟩
    · exact ⟨hph, completeOk_mono (v := v) id id reqCached_del isEmpty_del hco, hpu⟩
  | fill h' r' pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact ⟨hph, hco, hpu⟩
  | elem h' r' ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact ⟨hph, hco, hpu⟩
  | idx h' r' ui c pa n w =>
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inr (Or.inr ⟨r', ui, c, pa, n, w, rfl⟩)) hK
    · obtain ⟨-, rfl⟩ := idxGuard_some.1 hm
      refine ⟨?_, completeOk_mono (v := v) (fun ht => ?_) id id id hco, pushOk_del hpu h'⟩
      · rw [phase_complete_ne (Ne.symm hh)]
        exact hph
      · have hne : ¬ v.taken = some h' := by
          rw [ht]
          exact fun e => hh (Option.some.inj e).symm
        simp only [complete, hne, ↓reduceIte]
        exact ht

/-- The completion-and-push guard answers exactly when its condition holds. -/
theorem pushGuard_isSome {h : BitVec 16} {r : VioReq} {v : VirtioState} :
    (pushGuard h r v).isSome = true ↔ pushOpen h r v := by
  cases hg : pushGuard h r v with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro ho
    have := pushGuard_some.2 ⟨ho, rfl⟩
    rw [hg] at this
    cases this
  | some v' => exact ⟨fun _ => (pushGuard_some.1 hg).1, fun _ => rfl⟩

/-- The completion-and-push gate is open exactly when its condition holds. -/
theorem enabled_push_iff {h : BitVec 16} {r : VioReq} :
    Gate.enabled i .virtio tid (pushOp h r) c ↔
      taskAt i .virtio tid (pushOp h r) c ∧ pushOpen h r (disk c) := by
  unfold Gate.enabled
  rw [notBlocked_guard, pushGuard_isSome]

/-- **The completion-and-push gate is a stable gate except for four closers.**  Once the gate of
the serving task of head `h` and request `r` is open, it stays open under every other thread's
step but the power thread's, when the disk's tasks run its programs, except for: another live
disk task's capture (a write's payload enters the cache: a flush then waits for the cache, and a
write in write-through mode for its own sectors), its push (`pushOk` becomes false), or its
completion of head `h` (a second serving task of `h`); and a hart's MMIO write while the request
is in flight that resets the disk (excluded by `noBusyReset`) or turns the write-back mode off
(excluded by `noWceOff`). -/
theorem push_stable {h : BitVec 16} {r : VioReq} :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧ (noBusyReset c c' ∧ noWceOff c c') ∧
        (Gate.enabled i .virtio tid (pushOp h r) c → ¬ Gate.stepBy i .virtio
          (fun o => isCapture o ∨ isPush o ∨ completes h o) c c'))
      (Gate.enabled i .virtio tid (pushOp h r)) := by
  intro j c c' hji hs hnp hP hA
  rw [enabled_push_iff] at hA ⊢
  refine stable_of (M := fun c c' => noBusyReset c c' ∧ noWceOff c c')
    (K := fun o => isCapture o ∨ isPush o ∨ completes h o) push_move ?_ hji hs hnp
    ⟨hP.1, hP.2.1, fun ha => hP.2.2 (enabled_push_iff.2 ha)⟩ hA
  intro j c c' e cpu req w tags k off hs he hl hdec hw ⟨hR, hW⟩ hq
  obtain ⟨hst, cfg, isr, hc'⟩ := mmio_cases hs he hl hdec hw hR (inflight_ne_nil hq.1)
  have hwce := hW _ hs hst
  rw [hc'] at hwce ⊢
  exact ⟨hq.1, completeOk_mono (v := disk c) id hwce id id hq.2.1, hq.2.2⟩

/-- The completion-and-push gate persists on a run whose disk tasks run its programs, with no busy
reset and no store that turns the write-back mode off, and where no other live disk task captures,
pushes or completes the gate's head while the gate is open. -/
theorem push_persists {h : BitVec 16} {r : VioReq} (hrun : PoolRun σ)
    (hprog : ∀ n, progs (σ n)) (hR : NoBusyReset σ) (hW : NoWceOff σ)
    (hK : ∀ n, Gate.enabled i .virtio tid (pushOp h r) (σ n) → ¬ Gate.stepBy i .virtio
      (fun o => isCapture o ∨ isPush o ∨ completes h o) (σ n) (σ (n + 1))) :
    Persists i (Gate.enabled i .virtio tid (pushOp h r)) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ => Gate.live) push_stable
    fun n => ⟨hprog n, ⟨hR n, hW n⟩, hK n⟩

/-- Strong fairness of the completion-and-push gate, under the same hypotheses and fair
scheduling. -/
theorem push_sf {h : BitVec 16} {r : VioReq} (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (hprog : ∀ n, progs (σ n)) (hR : NoBusyReset σ) (hW : NoWceOff σ)
    (hK : ∀ n, Gate.enabled i .virtio tid (pushOp h r) (σ n) → ¬ Gate.stepBy i .virtio
      (fun o => isCapture o ∨ isPush o ∨ completes h o) (σ n) (σ (n + 1))) :
    Gate.SF i .virtio tid (pushOp h r) σ :=
  Gate.sf_of_persists (fun h => h) hsched (push_persists hrun hprog hR hW hK)

/-! ### The DMA-write guards -/

/-- A request's record stays the one fetched under every move of the disk's programs but a
serving task's phase write for its head, a push of its head and the completion of its head. -/
theorem req_move {h : BitVec 16} {r : VioReq} {o : DevOp VirtioState VTask} {v v' : VirtioState}
    (hp : Prim o) (hK : ¬ (servesHead h o ∨ pushesHead h o ∨ completes h o)) (hm : moves o v v')
    (hv : reqOf v h = some r) : reqOf v' h = some r := by
  cases hp with
  | get | choose | dmaRead | fork => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched h' r' =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inl ⟨r', rfl⟩)) hK
    · rw [reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | served h' r' =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inl ⟨r', rfl⟩))) hK
    · rw [reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | status h' r' =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inr (Or.inl ⟨r', rfl⟩)))) hK
    · rw [reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | latch h' =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact hv
  | capture h' r' w =>
    rw [moves_modify] at hm
    subst hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inl (Or.inr (Or.inr (Or.inr ⟨r', w, rfl⟩)))) hK
    · obtain ⟨cc, e⟩ := captureMove_eq h' r' w v
      rw [e, reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | push h' r' =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inr (Or.inl ⟨r', rfl⟩)) hK
    · rw [reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | pop h' =>
    rw [moves_guard, popGuard_some] at hm
    obtain ⟨hn, rfl⟩ := hm
    by_cases hh : h' = h
    · subst hh
      rw [phase_isSome_of_reqOf hv] at hn
      cases hn
    · show reqOf (setPhase v h' .popped) h = some r
      rw [reqOf_of_phase (phase_setPhase_ne _ _ (Ne.symm hh))]
      exact hv
  | drain j =>
    rw [moves_modify] at hm
    subst hm
    rcases drain_eq v (v.cache.getD j (0, [])).1 with e | ⟨dk, e⟩ <;> rw [drainMove, e] <;>
      exact hv
  | fill h' r' pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact hv
  | elem h' r' ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact hv
  | idx h' r' ui c pa n w =>
    by_cases hh : h' = h
    · subst hh
      exact absurd (Or.inr (Or.inr ⟨r', ui, c, pa, n, w, rfl⟩)) hK
    · obtain ⟨-, rfl⟩ := idxGuard_some.1 hm
      rw [reqOf_of_phase (phase_complete_ne (Ne.symm hh))]
      exact hv

/-- The used index and the configuration stay under every move of the disk's programs but a
used-index write (of any head): no task writes the configuration. -/
theorem usedIdx_cfg_move {o : DevOp VirtioState VTask} {v v' : VirtioState} (hp : Prim o)
    (hK : ¬ isUsedIdx o) (hm : moves o v v') : v'.usedIdx = v.usedIdx ∧ v'.cfg = v.cfg := by
  cases hp with
  | get | choose | dmaRead | fork => exact hm.elim
  | stall => exact absurd hm stall_never
  | fetched h' r' | served h' r' | status h' r' =>
    rw [moves_modify] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  | latch h' =>
    rw [moves_guard, captureGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact ⟨rfl, rfl⟩
  | capture h' r' w =>
    rw [moves_modify] at hm
    subst hm
    obtain ⟨cc, e⟩ := captureMove_eq h' r' w v
    rw [e]
    exact ⟨rfl, rfl⟩
  | push h' r' =>
    rw [moves_guard, pushGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact ⟨rfl, rfl⟩
  | pop h' =>
    rw [moves_guard, popGuard_some] at hm
    obtain ⟨-, rfl⟩ := hm
    exact ⟨rfl, rfl⟩
  | drain j =>
    rw [moves_modify] at hm
    subst hm
    rcases drain_eq v (v.cache.getD j (0, [])).1 with e | ⟨dk, e⟩ <;> rw [drainMove, e] <;>
      exact ⟨rfl, rfl⟩
  | fill h' r' pa n w =>
    obtain ⟨-, rfl⟩ := reqGuard_some.1 hm
    exact ⟨rfl, rfl⟩
  | elem h' r' ui c pa n w =>
    obtain ⟨-, rfl⟩ := elemGuard_some.1 hm
    exact ⟨rfl, rfl⟩
  | idx h' r' ui c pa n w => exact absurd ⟨h', r', ui, c, pa, n, w, rfl⟩ hK

/-- The used element's and the used index's guard condition stays under every move of the disk's
programs but a serving task's phase write for its head, a push of its head and a used-index
write of any head. -/
theorem snap_move {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {o : DevOp VirtioState VTask} {v v' : VirtioState} (hp : Prim o)
    (hK : ¬ (servesHead h o ∨ pushesHead h o ∨ isUsedIdx o)) (hm : moves o v v')
    (hv : snapOk h r ui c v) : snapOk h r ui c v' := by
  have hK' : ¬ (servesHead h o ∨ pushesHead h o ∨ completes h o) := by
    rintro (h1 | h1 | ⟨r', ui', c', pa, n, w, rfl⟩)
    · exact hK (Or.inl h1)
    · exact hK (Or.inr (Or.inl h1))
    · exact hK (Or.inr (Or.inr ⟨h, r', ui', c', pa, n, w, rfl⟩))
  obtain ⟨hu, hc⟩ := usedIdx_cfg_move hp (fun h1 => hK (Or.inr (Or.inr h1))) hm
  exact ⟨req_move hp hK' hm hv.1, hu.trans hv.2.1, hc.trans hv.2.2⟩

/-- The fill's guard answers exactly when the request is still `r`. -/
theorem reqGuard_isSome {h : BitVec 16} {r : VioReq} {v : VirtioState} :
    (reqGuard h r v).isSome = true ↔ reqOf v h = some r := by
  unfold reqGuard
  split <;> simp_all

/-- The used element's guard answers exactly at the snapshot. -/
theorem elemGuard_isSome {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {v : VirtioState} : (elemGuard h r ui c v).isSome = true ↔ snapOk h r ui c v := by
  unfold elemGuard snapOk
  split <;> simp_all

/-- The used index's guard answers exactly at the snapshot. -/
theorem idxGuard_isSome {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {c : VirtioCfg}
    {v : VirtioState} : (idxGuard h r ui c v).isSome = true ↔ snapOk h r ui c v := by
  unfold idxGuard snapOk
  split <;> simp_all

/-- At a DMA write of the disk (a silent device), the enabling condition is the task there, its
guard answering, and the footprint in RAM. -/
theorem dmaAt_iff {g : VirtioState → Option VirtioState} {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} :
    Gate.dmaAt i .virtio tid g pa n w c ↔
      taskAt i .virtio tid (.dmaWrite g pa n w) c ∧ (g (disk c)).isSome = true ∧ ramBytes pa n := by
  unfold Gate.dmaAt
  constructor
  · rintro ⟨ht, ⟨s', hs', -⟩, hr⟩
    exact ⟨ht, by rw [hs']; rfl, hr⟩
  · rintro ⟨ht, hs, hr⟩
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨ht, ⟨s', hs', rfl⟩, hr⟩

/-- **The fill's and the status byte's guard is stable except for its head's writes.**  Once a
DMA write guarded on `reqOf v h = some r` (the fill of a read request, the status byte) answers,
its guard keeps answering under every other thread's step but the power thread's, when the
disk's tasks run its programs, except for another live disk task's phase write for head `h`
(the moves to `.fetched`, `.served`, `.status`, the capture, the push) or completion of `h` (a
second serving task of `h`), and a busy reset (excluded by `noBusyReset`).  The root's pop of `h`
does not close it: the pop guard refuses a head in flight. -/
theorem req_stable {h : BitVec 16} {r : VioReq} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)} :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧ noBusyReset c c' ∧
        (Gate.dmaAt i .virtio tid (reqGuard h r) pa n w c → ¬ Gate.stepBy i .virtio
          (fun o => servesHead h o ∨ pushesHead h o ∨ completes h o) c c'))
      (Gate.dmaAt i .virtio tid (reqGuard h r) pa n w) := by
  intro j c c' hji hs hnp hP hA
  rw [dmaAt_iff, reqGuard_isSome] at hA ⊢
  refine stable_of (M := noBusyReset) (Q := fun v => reqOf v h = some r ∧ ramBytes pa n)
    (K := fun o => servesHead h o ∨ pushesHead h o ∨ completes h o)
    (fun hp hK hm hq => ⟨req_move hp hK hm hq.1, hq.2⟩) ?_ hji hs hnp
    ⟨hP.1, hP.2.1, fun ha => hP.2.2 (by rw [dmaAt_iff, reqGuard_isSome]; exact ha)⟩ hA
  intro j c c' e cpu req w tags k off hs he hl hdec hw hR hq
  obtain ⟨-, cfg, isr, hc'⟩ :=
    mmio_cases hs he hl hdec hw hR (inflight_ne_nil (phase_isSome_of_reqOf hq.1))
  rw [hc']
  exact hq

/-- The fill's and the status byte's enabling condition persists on a run whose disk tasks run its
programs, with no busy reset, and where no other live disk task writes the head's phase or
completes it while the guard answers. -/
theorem req_persists {h : BitVec 16} {r : VioReq} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (hrun : PoolRun σ) (hprog : ∀ n, progs (σ n)) (hR : NoBusyReset σ)
    (hK : ∀ m, Gate.dmaAt i .virtio tid (reqGuard h r) pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ completes h o) (σ m) (σ (m + 1))) :
    Persists i (Gate.dmaAt i .virtio tid (reqGuard h r) pa n w) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ => Gate.dmaAt_live) req_stable
    fun m => ⟨hprog m, hR m, hK m⟩

/-- Under the same hypotheses and fair scheduling, the trusted form (the Progress Axiom for the
disk at this node) and the proof form of the DMA write coincide. -/
theorem req_sf_iff {h : BitVec 16} {r : VioReq} {pa : PAddr} {n : Nat} {w : BitVec (8 * n)}
    (hrun : PoolRun σ) (hsched : StepsInfOften i σ) (hprog : ∀ n, progs (σ n))
    (hR : NoBusyReset σ)
    (hK : ∀ m, Gate.dmaAt i .virtio tid (reqGuard h r) pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ completes h o) (σ m) (σ (m + 1))) :
    Action.SF (Gate.dmaAt i .virtio tid (reqGuard h r) pa n w) (Dma.grant i .virtio tid) σ ↔
      Thread.AttemptGrant i (Gate.dmaAt i .virtio tid (reqGuard h r) pa n w)
        (Dma.grant i .virtio tid) σ :=
  Thread.sf_iff_attemptGrant Dma.ownGrant hsched (req_persists hrun hprog hR hK)

/-- **The used element's and the used index's guard is stable except for five closers.**  Once a
DMA write guarded on the snapshot (`snapOk`: the request is still `r`, the used index is still
`ui`, the configuration is still `c`) answers, its guard keeps answering under every other
thread's step but the power thread's, when the disk's tasks run its programs, except for another
live disk task's phase write for head `h` (the moves to `.fetched`, `.served`, `.status`, the
capture, the push) or used-index write (of any head: it advances the used index), a busy reset
(excluded by `noBusyReset`) and a hart's MMIO write that changes the configuration while a
request is in flight (excluded by `noConfigWrite`). -/
theorem snap_stable {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {cf : VirtioCfg}
    {g : VirtioState → Option VirtioState}
    (hg : ∀ v, (g v).isSome = true ↔ snapOk h r ui cf v) {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} :
    StableExceptPowerUnder i
      (fun c c' => progs c ∧ (noBusyReset c c' ∧ noConfigWrite c c') ∧
        (Gate.dmaAt i .virtio tid g pa n w c → ¬ Gate.stepBy i .virtio
          (fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o) c c'))
      (Gate.dmaAt i .virtio tid g pa n w) := by
  intro j c c' hji hs hnp hP hA
  rw [dmaAt_iff, hg] at hA ⊢
  refine stable_of (M := fun c c' => noBusyReset c c' ∧ noConfigWrite c c')
    (Q := fun v => snapOk h r ui cf v ∧ ramBytes pa n)
    (K := fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o)
    (fun hp hK hm hq => ⟨snap_move hp hK hm hq.1, hq.2⟩) ?_ hji hs hnp
    ⟨hP.1, hP.2.1, fun ha => hP.2.2 (by rw [dmaAt_iff, hg]; exact ha)⟩ hA
  intro j c c' e cpu req w tags k off hs he hl hdec hw ⟨hR, hC⟩ hq
  obtain ⟨hst, cfg, isr, hc'⟩ :=
    mmio_cases hs he hl hdec hw hR (inflight_ne_nil (phase_isSome_of_reqOf hq.1.1))
  have hcfg := hC _ hs hst
  rw [hc'] at hcfg ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1, hcfg.trans hq.1.2.2⟩, hq.2⟩

/-- The used element's and the used index's enabling condition persists on a run whose disk tasks
run its programs, with no busy reset and no configuration write while a request is in flight,
and where no other live disk task writes the head's phase or a used index while the guard
answers. -/
theorem snap_persists {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {cf : VirtioCfg}
    {g : VirtioState → Option VirtioState}
    (hg : ∀ v, (g v).isSome = true ↔ snapOk h r ui cf v) {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} (hrun : PoolRun σ) (hprog : ∀ n, progs (σ n)) (hR : NoBusyReset σ)
    (hC : NoConfigWrite σ)
    (hK : ∀ m, Gate.dmaAt i .virtio tid g pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o) (σ m) (σ (m + 1))) :
    Persists i (Gate.dmaAt i .virtio tid g pa n w) σ :=
  Era.persists_of_liveStableUnder hrun (fun _ => Gate.dmaAt_live) (snap_stable hg)
    fun m => ⟨hprog m, ⟨hR m, hC m⟩, hK m⟩

/-- Under the same hypotheses and fair scheduling, the trusted form and the proof form of the used
element's or the used index's DMA write coincide. -/
theorem snap_sf_iff {h : BitVec 16} {r : VioReq} {ui : BitVec 16} {cf : VirtioCfg}
    {g : VirtioState → Option VirtioState}
    (hg : ∀ v, (g v).isSome = true ↔ snapOk h r ui cf v) {pa : PAddr} {n : Nat}
    {w : BitVec (8 * n)} (hrun : PoolRun σ) (hsched : StepsInfOften i σ)
    (hprog : ∀ n, progs (σ n)) (hR : NoBusyReset σ) (hC : NoConfigWrite σ)
    (hK : ∀ m, Gate.dmaAt i .virtio tid g pa n w (σ m) → ¬ Gate.stepBy i .virtio
      (fun o => servesHead h o ∨ pushesHead h o ∨ isUsedIdx o) (σ m) (σ (m + 1))) :
    Action.SF (Gate.dmaAt i .virtio tid g pa n w) (Dma.grant i .virtio tid) σ ↔
      Thread.AttemptGrant i (Gate.dmaAt i .virtio tid g pa n w) (Dma.grant i .virtio tid) σ :=
  Thread.sf_iff_attemptGrant Dma.ownGrant hsched (snap_persists hg hrun hprog hR hC hK)

end Disk
end Fairness

/-
Weak: **discharging `CapRelSite.pcLogAgree` -- the machine's pc log along a run** (W11-C2′ (a2)
[OWN.82]; mcslrec (2)), increment 1: how each MachCSL state change moves the issuing-pc log
`RelSiteProvExp.pcLogOf σ` (one entry per store position).  Lean-only, no Rocq twin.

* `CapPcLog.pcLogOfStore`: a hart's store appends the store's pc (its `PC` for a plain store,
  `-1` for an exclusive / AMO write) -- `RelSiteProvPc.recPc`'s value for the same record.
* `CapPcLog.pcLogOfDma`: a DMA write appends `-1` (the disk agent's pc in `recPc`); a zero-byte
  one is the identity.
* `CapPcLog.pcLogOfCongr`: a change that keeps the log and the pc record keeps the pc log.

**The result** `CapPcLog.machRunPc`: W4's `machRunOfPfRun` with `CapRelSite.pcLogAgree r g.m` at
the MachCSL state it builds.  Per recorded step (`CapPcLog.oneStepPc`, `CapPcLog.diskStepPc`) the
machine's pc log grows by exactly the step's `recPc`: `R-log` with `R-auth` (`CapPcLog.simLog`)
names the author of the one new machine entry; a hart's is the store of its single pool thread
(`bootHartN`, `hartThreadIs`), running the pf hart's own `memWrite` node, so plain/exclusive agree
(`CapPcLog.storeLbl`) and the pc is the pf hart's `PC` (`SimRel.pool`); a disk block's entries are
DMA writes, `-1` (`CapPcLog.mrunDiskPos`).  `CapPcLog.simRunPc` is the run induction.

Spec: FAITHFUL (proof organisation).  Names: `CapPcLog.*`.
-/
import Weak.CapRelSite

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

/-- The pc log of a state, by its two fields. -/
theorem CapPcLog.pcLogOfEq (σ : MState) :
    RelSiteProvExp.pcLogOf σ = (List.range σ.log.length).map (fun q => σ.pcAt (q + 1)) := rfl

/-- A change keeping the log and the pc record keeps the pc log. -/
theorem CapPcLog.pcLogOfCongr {σ σ' : MState} (hl : σ'.log = σ.log) (hp : σ'.pcAt = σ.pcAt) :
    RelSiteProvExp.pcLogOf σ' = RelSiteProvExp.pcLogOf σ := by
  simp only [RelSiteProvExp.pcLogOf, hl, hp]

/-- Appending one position whose pc is `v`, the old positions' pcs kept. -/
theorem CapPcLog.pcLogOfSnoc {σ σ' : MState} (g : Agent) (v : Int) (hl : σ'.log = σ.log ++ [g])
    (hp : ∀ t, σ'.pcAt t = if t = σ.log.length + 1 then v else σ.pcAt t) :
    RelSiteProvExp.pcLogOf σ' = RelSiteProvExp.pcLogOf σ ++ [v] := by
  simp only [RelSiteProvExp.pcLogOf, hl, List.length_append, List.length_singleton, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro q hq
    rw [hp]
    have := List.mem_range.1 hq
    rw [if_neg (by omega)]
  · rw [hp, if_pos rfl]

/-- **A hart's store appends its pc**: the hart's `PC` (plain) or `-1` (exclusive / AMO). -/
theorem CapPcLog.pcLogOfStore (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (excl : Bool) :
    RelSiteProvExp.pcLogOf (σ.store cpu pa n w excl) =
      RelSiteProvExp.pcLogOf σ ++ [if excl then -1 else (((σ.regs cpu) LeanRV64D.Register.PC).toNat : Int)] :=
  CapPcLog.pcLogOfSnoc (hartAgent cpu) _ rfl (fun t => rfl)

/-- **A DMA write appends `-1`** (a zero-byte one is the identity). -/
theorem CapPcLog.pcLogOfDma (σ : MState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    RelSiteProvExp.pcLogOf (σ.storeDma pa n w) =
      if n = 0 then RelSiteProvExp.pcLogOf σ else RelSiteProvExp.pcLogOf σ ++ [-1] := by
  by_cases hn : n = 0
  · rw [if_pos hn, MState.storeDma_zero σ pa n w hn]
  · rw [if_neg hn]
    exact CapPcLog.pcLogOfSnoc diskAgent (-1) (by simp only [MState.storeDma, if_neg hn])
      (fun t => by simp only [MState.storeDma, if_neg hn, MState.top])

/-- What a step does to the log and the pc record: nothing, or one store. -/
def CapPcLog.keepsPc (σ σ' : MState) : Prop := σ'.log = σ.log ∧ σ'.pcAt = σ.pcAt

/-- **A hart event keeps the pc log, or is a store** (`MachCSL.evStep`). -/
theorem CapPcLog.evStepPc (cpu : CPU) (o : Outcome Register RegisterType) (σ : MState) (v : o.ret)
    (σ' : MState) (h : evStep cpu o σ v σ') :
    CapPcLog.keepsPc σ σ' ∨ ∃ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (w : BitVec (8 * n)), o = .memWrite n va req ∧ σ' = σ.store cpu req.pa n w (akExcl req.access_kind) := by
  cases o with
  | memWrite n va req =>
    rcases h with ⟨-, w, ds', -, -, -, rfl⟩ | ⟨-, w, -, -, -, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨n, va, req, w, rfl, rfl⟩
  | memRead n va req =>
    left
    rcases h with ⟨-, w, ds', -, -, rfl⟩ | ⟨-, -, tvn, w, -, -, -, -, rfl⟩ |
      ⟨-, -, tvn, w, -, -, -, -, -, rfl⟩ | ⟨-, -, -, w, -, -, rfl⟩ <;> exact ⟨rfl, rfl⟩
  | readRam => exact absurd h id
  | writeRam => exact absurd h id
  | regRead r => obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | getCycleCount => obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | _ => subst h; exact Or.inl ⟨rfl, rfl⟩

/-- A blocked hart event keeps the pc log. -/
theorem CapPcLog.blockedPc (cpu : CPU) (o : Outcome Register RegisterType) (σ σ' : MState)
    (h : blockedStep cpu o σ σ') : CapPcLog.keepsPc σ σ' := by
  cases o with
  | memRead n va req => obtain ⟨-, -, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | memWrite n va req => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | _ => exact absurd h id

/-- **A hart step keeps the pc log, or is one of its events' stores** (`MachCSL.hartStep`). -/
theorem CapPcLog.hartStepPc (cpu : CPU) (m : SailM Unit) (σ : MState) (m' : SailM Unit) (σ' : MState)
    (h : hartStep cpu m σ m' σ') :
    CapPcLog.keepsPc σ σ' ∨ ∃ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (w : BitVec (8 * n)), σ' = σ.store cpu req.pa n w (akExcl req.access_kind) := by
  unfold hartStep at h
  match m, h with
  | .pure _, ⟨_, _, h⟩ => subst h; exact Or.inl ⟨rfl, rfl⟩
  | .impure (.ok o) k, Or.inl ⟨v, _, hv⟩ =>
    rcases CapPcLog.evStepPc cpu o σ v σ' hv with h | ⟨n, va, req, w, _, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, va, req, w, h⟩
  | .impure (.ok o) k, Or.inr ⟨hb, _⟩ => exact Or.inl (CapPcLog.blockedPc cpu o σ σ' hb)

/-- **A device primitive keeps the pc log, or is a DMA write** (`MachCSL.devOpStep`). -/
theorem CapPcLog.devOpStepPc (gen : Nat) (d : DevId) (o : DevOp (DevSt d) (DevTask d)) (σ : MState)
    (v : o.ret) (σ' : MState) (obs : List Obs) (efs : List Expr) (h : devOpStep gen d o σ v σ' obs efs) :
    CapPcLog.keepsPc σ σ' ∨ ∃ (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (s' : DevSt d),
      σ' = (σ.storeDma pa n w).setDev d s' := by
  cases o with
  | step g => obtain ⟨s', os, -, -, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | get => obtain ⟨-, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | choose => obtain ⟨rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | dmaRead pa n => obtain ⟨-, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | dmaWrite g pa n w =>
    obtain ⟨-, -, ⟨s', -, -, -, -, rfl⟩ | ⟨-, rfl⟩⟩ := h
    · exact Or.inr ⟨pa, n, w, s', rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  | sample src => obtain ⟨-, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | setPin cpu mmode b =>
    obtain ⟨-, -, rfl⟩ := h
    cases mmode <;> exact Or.inl ⟨rfl, rfl⟩
  | fork t => obtain ⟨-, -, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩
  | join tid => obtain ⟨-, rfl, -⟩ := h; exact Or.inl ⟨rfl, rfl⟩

/-- **A device step keeps the pc log, or is a DMA write** (`MachCSL.devStep`). -/
theorem CapPcLog.devStepPc (gen : Nat) (d : DevId) (tid : TaskId) (m : DevProg d) (σ : MState)
    (obs : List Obs) (m' : DevProg d) (σ' : MState) (efs : List Expr) (h : devStep gen d tid m σ obs m' σ' efs) :
    CapPcLog.keepsPc σ σ' ∨ ∃ (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (s' : DevSt d),
      σ' = (σ.storeDma pa n w).setDev d s' := by
  unfold devStep at h
  match m, h with
  | .pure _, ⟨_, _, Or.inl ⟨_, _, h⟩⟩ => subst h; exact Or.inl ⟨rfl, rfl⟩
  | .pure _, ⟨_, _, Or.inr ⟨_, _, h⟩⟩ =>
    subst h; split <;> exact Or.inl ⟨rfl, rfl⟩
  | .op o k, Or.inl ⟨v, _, hv⟩ => exact CapPcLog.devOpStepPc gen d o σ v σ' obs efs hv
  | .op o k, Or.inr ⟨_, _, h, _⟩ => subst h; exact Or.inl ⟨rfl, rfl⟩

/-- The pc log after a DMA write and a device move. -/
theorem CapPcLog.pcLogOfDmaDev (σ : MState) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (d : DevId)
    (s' : DevSt d) :
    RelSiteProvExp.pcLogOf ((σ.storeDma pa n w).setDev d s') =
      if n = 0 then RelSiteProvExp.pcLogOf σ else RelSiteProvExp.pcLogOf σ ++ [-1] :=
  CapPcLog.pcLogOfDma σ pa n w

/-- **What one pool step does to the pc record** (powered on): nothing, one hart store, or one DMA
write (with its device's move). -/
def CapPcLog.stepPc (σ σ' : MState) : Prop :=
  CapPcLog.keepsPc σ σ' ∨
  (∃ (cpu : CPU) (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (w : BitVec (8 * n)), σ' = σ.store cpu req.pa n w (akExcl req.access_kind)) ∨
  (∃ (d : DevId) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (s' : DevSt d), σ' = (σ.storeDma pa n w).setDev d s')

/-- **A thread-pool step with the power on** (`MachCSL.primStep`) is one of `stepPc`'s three
kinds: the hart and device arms by `hartStepPc`/`devStepPc`, the corpse arms and power-off keep the
machine state (power-on needs the power off). -/
theorem CapPcLog.primStepPc {e : Expr} {g : GState} {obs : List Obs} {e' : Expr} {g' : GState}
    {efs : List Expr} (h : primStep (e, g) obs (e', g', efs)) (hp : g.pow = true) : CapPcLog.stepPc g.m g'.m := by
  cases e with
  | hart gen cpu m =>
    obtain ⟨-, ⟨-, -, m', σ', -, hs, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := h
    · rcases CapPcLog.hartStepPc cpu m g.m m' σ' hs with hk | ⟨n, va, req, w, he⟩
      · exact Or.inl hk
      · exact Or.inr (Or.inl ⟨cpu, n, va, req, w, he⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  | dev gen d tid m =>
    rcases h with ⟨-, m', σ', -, hs, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · rcases CapPcLog.devStepPc gen d tid m g.m obs m' σ' efs hs with hk | ⟨pa, n, w, s', he⟩
      · exact Or.inl hk
      · exact Or.inr (Or.inr ⟨d, pa, n, w, s', he⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  | power =>
    obtain ⟨-, ⟨-, -, -, rfl⟩ | ⟨hp', -⟩⟩ := h
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hp] at hp'; cases hp'

/-- **A machine step with the power on** is one of `stepPc`'s three kinds. -/
theorem CapPcLog.stepPcOf {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) (hp : g.pow = true) : CapPcLog.stepPc g.m g'.m := by
  cases h with
  | atomic H t₁ t₂ => exact CapPcLog.primStepPc H hp

/-- A run of at most one machine step from a powered-on state: no step (the state kept), or one. -/
theorem CapPcLog.mrunLe1 {m : Nat} {t t' : List Expr} {g g' : GState} {κ : List Obs}
    (h : MachOfPf.MRun m (t, g) κ (t', g')) (hm : m ≤ 1) (hp : g.pow = true) :
    g' = g ∨ CapPcLog.stepPc g.m g'.m := by
  cases h with
  | refl => exact Or.inl rfl
  | cons hs hr =>
    cases hr with
    | refl => exact Or.inr (CapPcLog.stepPcOf hs hp)
    | cons _ _ => omega

/-- `R-log`: the pf log and the machine log have one entry per position. -/
theorem CapPcLog.logLen {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {t : List Expr} {g : GState}
    (hR : MachOfPf.SimRel c st t g) : c.pcLog.length = g.m.log.length := by
  have h := congrArg List.length hR.mem.1.1
  simpa using h

/-- The machine log's length after one `stepPc` step: kept, or one more. -/
theorem CapPcLog.stepPcLen {σ σ' : MState} (h : CapPcLog.stepPc σ σ') :
    (σ'.log = σ.log ∧ RelSiteProvExp.pcLogOf σ' = RelSiteProvExp.pcLogOf σ) ∨
    (σ'.log.length = σ.log.length + 1 ∧ ∃ v : Int, RelSiteProvExp.pcLogOf σ' = RelSiteProvExp.pcLogOf σ ++ [v]) := by
  rcases h with ⟨hl, hp⟩ | ⟨cpu, n, va, req, w, rfl⟩ | ⟨d, pa, n, w, s', rfl⟩
  · exact Or.inl ⟨hl, CapPcLog.pcLogOfCongr hl hp⟩
  · exact Or.inr ⟨by simp, _, CapPcLog.pcLogOfStore _ cpu _ n w _⟩
  · rw [CapPcLog.pcLogOfDmaDev]
    by_cases hn : n = 0
    · subst hn; exact Or.inl ⟨by simp, by simp⟩
    · exact Or.inr ⟨by simp [MState.storeDma, hn], -1, by rw [if_neg hn]⟩

/-- **A pf step that appends nothing, simulated by at most one machine step**, keeps the machine's
pc log (`R-log` at both ends). -/
theorem CapPcLog.noAppendKeeps {c c' : Wpcfg Pexv6 Efab} {st st' : List (Nat × Wlabel)} {t t' : List Expr}
    {g g' : GState} (hR : MachOfPf.SimRel c st t g) (hR' : MachOfPf.SimRel c' st' t' g')
    (hlen : c'.pcLog.length = c.pcLog.length) (hs : g' = g ∨ CapPcLog.stepPc g.m g'.m) :
    RelSiteProvExp.pcLogOf g'.m = RelSiteProvExp.pcLogOf g.m := by
  rcases hs with rfl | hs
  · rfl
  rcases CapPcLog.stepPcLen hs with ⟨-, h⟩ | ⟨hl, -⟩
  · exact h
  · have h1 := CapPcLog.logLen hR
    have h2 := CapPcLog.logLen hR'
    omega

/-- **A hart step that is a store names its event**: the residual program is the store's `memWrite`
node, and the exclusivity is that event's access kind. -/
theorem CapPcLog.hartStepStore (cpu : CPU) (m : SailM Unit) (σ : MState) (m' : SailM Unit) (σ' : MState)
    (h : hartStep cpu m σ m' σ') :
    CapPcLog.keepsPc σ σ' ∨ ∃ (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : (Outcome.memWrite n va req).ret → SailM Unit) (w : BitVec (8 * n)),
      m = .impure (.ok (.memWrite n va req)) k ∧ σ' = σ.store cpu req.pa n w (akExcl req.access_kind) := by
  unfold hartStep at h
  match m, h with
  | .pure _, ⟨_, _, h⟩ => subst h; exact Or.inl ⟨rfl, rfl⟩
  | .impure (.ok o) k, Or.inl ⟨v, _, hv⟩ =>
    rcases CapPcLog.evStepPc cpu o σ v σ' hv with h | ⟨n, va, req, w, ho, h⟩
    · exact Or.inl h
    · subst ho; exact Or.inr ⟨n, va, req, k, w, rfl, h⟩
  | .impure (.ok o) k, Or.inr ⟨hb, _⟩ => exact Or.inl (CapPcLog.blockedPc cpu o σ σ' hb)

/-- **A machine step with the power on, its store arm naming the stepping hart thread.** -/
theorem CapPcLog.stepStoreOf {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) (hp : g.pow = true) :
    CapPcLog.keepsPc g.m g'.m ∨
    (∃ (t₁ t₂ : List Expr) (gen : Nat) (cpu : CPU) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : (Outcome.memWrite n va req).ret → SailM Unit) (w : BitVec (8 * n)),
      t = t₁ ++ .hart gen cpu (.impure (.ok (.memWrite n va req)) k) :: t₂ ∧
      g'.m = g.m.store cpu req.pa n w (akExcl req.access_kind)) ∨
    (∃ (d : DevId) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (s' : DevSt d), g'.m = (g.m.storeDma pa n w).setDev d s') := by
  cases h with
  | @atomic e σ₀ obs₀ e' σ₁ eₜ H t₁ t₂ =>
    cases e with
    | hart gen cpu m =>
      obtain ⟨-, ⟨-, -, m', σ', -, hs, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := H
      · rcases CapPcLog.hartStepStore cpu m g.m m' σ' hs with hk | ⟨n, va, req, k, w, rfl, he⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inl ⟨t₁, t₂, gen, cpu, n, va, req, k, w, rfl, he⟩)
      · exact Or.inl ⟨rfl, rfl⟩
    | dev gen d tid m =>
      rcases H with ⟨-, m', σ', -, hs, rfl⟩ | ⟨-, -, -, -, rfl⟩
      · rcases CapPcLog.devStepPc gen d tid m g.m _ m' σ' _ hs with hk | ⟨pa, n, w, s', he⟩
        · exact Or.inl hk
        · exact Or.inr (Or.inr ⟨d, pa, n, w, s', he⟩)
      · exact Or.inl ⟨rfl, rfl⟩
    | power =>
      obtain ⟨-, ⟨-, -, -, rfl⟩ | ⟨hp', -⟩⟩ := H
      · exact Or.inl ⟨rfl, rfl⟩
      · rw [hp] at hp'; cases hp'

/-- Is `e` a hart thread of hart `cpu` (any generation)? -/
def CapPcLog.isHartOf (cpu : CPU) : Expr → Bool
  | .hart _ c _ => decide (c = cpu)
  | _ => false

/-- The number of hart threads of `cpu` in a pool. -/
def CapPcLog.hartN (cpu : CPU) (t : List Expr) : Nat := (t.filter (CapPcLog.isHartOf cpu)).length

theorem CapPcLog.hartNApp (cpu : CPU) (a b : List Expr) :
    CapPcLog.hartN cpu (a ++ b) = CapPcLog.hartN cpu a + CapPcLog.hartN cpu b := by
  simp [CapPcLog.hartN, List.filter_append]

theorem CapPcLog.hartNCons (cpu : CPU) (e : Expr) (a : List Expr) :
    CapPcLog.hartN cpu (e :: a) = (if CapPcLog.isHartOf cpu e then 1 else 0) + CapPcLog.hartN cpu a := by
  unfold CapPcLog.hartN
  cases h : CapPcLog.isHartOf cpu e <;> simp [List.filter_cons, h] <;> omega

/-- **A powered-on pool step keeps every hart's thread count**: a thread is replaced by one of the
same kind (a hart's by the same hart's), and only device threads are forked. -/
theorem CapPcLog.stepHartN {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) (hp : g.pow = true) (cpu : CPU) :
    CapPcLog.hartN cpu t' = CapPcLog.hartN cpu t := by
  cases h with
  | @atomic e σ₀ obs₀ e' σ₁ eₜ H t₁ t₂ =>
    have hsame : CapPcLog.isHartOf cpu e' = CapPcLog.isHartOf cpu e ∧ CapPcLog.hartN cpu eₜ = 0 := by
      cases e with
      | hart gen c m =>
        obtain ⟨rfl, ⟨-, -, m', σ', rfl, -, -⟩ | ⟨-, -, rfl, -⟩⟩ := H <;> exact ⟨rfl, rfl⟩
      | dev gen d tid m =>
        rcases H with ⟨-, m', σ', rfl, hs, -⟩ | ⟨-, -, rfl, rfl, -⟩
        · refine ⟨rfl, ?_⟩
          unfold devStep at hs
          split at hs
          · obtain ⟨-, rfl, -⟩ := hs; rfl
          · rcases hs with ⟨v, -, ho⟩ | ⟨-, -, -, -, rfl⟩
            · rename_i o k
              cases o with
              | step g => obtain ⟨-, -, -, -, -, -, rfl⟩ := ho; rfl
              | get => obtain ⟨-, -, -, rfl⟩ := ho; rfl
              | choose => obtain ⟨-, -, rfl⟩ := ho; rfl
              | dmaRead => obtain ⟨-, -, -, rfl⟩ := ho; rfl
              | dmaWrite => obtain ⟨-, rfl, -⟩ := ho; rfl
              | sample => obtain ⟨-, -, -, rfl⟩ := ho; rfl
              | setPin => obtain ⟨-, rfl, -⟩ := ho; rfl
              | fork tk => obtain ⟨-, -, -, rfl⟩ := ho; simp [CapPcLog.hartN, CapPcLog.isHartOf]
              | join => obtain ⟨-, -, -, rfl⟩ := ho; rfl
            · rfl
        · exact ⟨rfl, rfl⟩
      | power =>
        obtain ⟨rfl, ⟨-, -, rfl, -⟩ | ⟨hp', -⟩⟩ := H
        · exact ⟨rfl, rfl⟩
        · rw [hp] at hp'; cases hp'
    simp only [CapPcLog.hartNApp, CapPcLog.hartNCons, hsame.1, hsame.2]
    omega

/-- **A pool step's effect on the generation and the power**: the generation never drops; with the
power on, either nothing changes or the power goes off and the generation rises. -/
theorem CapPcLog.stepGen {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) :
    g.gen ≤ g'.gen ∧ (g.pow = true → (g'.gen = g.gen ∧ g'.pow = true) ∨ g'.gen = g.gen + 1) := by
  cases h with
  | @atomic e σ₀ obs₀ e' σ₁ eₜ H t₁ t₂ =>
    cases e with
    | hart gen c m =>
      obtain ⟨-, ⟨-, -, m', σ', -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := H <;>
        exact ⟨Nat.le_refl _, fun hp => Or.inl ⟨rfl, hp⟩⟩
    | dev gen d tid m =>
      rcases H with ⟨-, m', σ', -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;>
        exact ⟨Nat.le_refl _, fun hp => Or.inl ⟨rfl, hp⟩⟩
    | power =>
      obtain ⟨-, ⟨-, -, -, rfl⟩ | ⟨hp', -, -, hb⟩⟩ := H
      · exact ⟨Nat.le_succ _, fun _ => Or.inr rfl⟩
      · refine ⟨Nat.le_of_eq hb.1.symm, fun hp => ?_⟩
        rw [hp] at hp'; cases hp'

/-- The generation never drops along a run. -/
theorem CapPcLog.mrunGen {n : Nat} {ρ ρ' : List Expr × GState} {κ : List Obs}
    (h : MachOfPf.MRun n ρ κ ρ') : ρ.2.gen ≤ ρ'.2.gen := by
  induction h with
  | refl => exact Nat.le_refl _
  | @cons _ ρ₁ ρ₂ ρ₃ _ _ hs _ ih =>
    obtain ⟨t₁, g₁⟩ := ρ₁
    obtain ⟨t₂, g₂⟩ := ρ₂
    exact Nat.le_trans (CapPcLog.stepGen hs).1 ih

/-- **Along a run that keeps the power on and the generation, every hart keeps its thread count.** -/
theorem CapPcLog.mrunHartN {n : Nat} {ρ ρ' : List Expr × GState} {κ : List Obs}
    (h : MachOfPf.MRun n ρ κ ρ') (hp : ρ.2.pow = true) (hg : ρ'.2.gen = ρ.2.gen) (cpu : CPU) :
    CapPcLog.hartN cpu ρ'.1 = CapPcLog.hartN cpu ρ.1 := by
  induction h with
  | refl => rfl
  | @cons _ ρ₁ ρ₂ ρ₃ _ _ hs hr ih =>
    obtain ⟨t₁, g₁⟩ := ρ₁
    obtain ⟨t₂, g₂⟩ := ρ₂
    have hm := CapPcLog.mrunGen hr
    rcases (CapPcLog.stepGen hs).2 hp with ⟨hg2, hp2⟩ | hg2
    · rw [ih hp2 (by simp only at hg hg2 ⊢; omega)]
      exact CapPcLog.stepHartN hs hp cpu
    · simp only at hg hg2 hm; omega

/-- One hart thread of each hart in the boot fork. -/
theorem CapPcLog.hartNFork (gen : Nat) (cpu : CPU) : CapPcLog.hartN cpu (Expr.power :: powerFork gen) = 1 := by
  have h1 : CapPcLog.hartN cpu (cpus.map (Loop gen)) = 1 := by
    have : (List.filter (CapPcLog.isHartOf cpu) (cpus.map (Loop gen))) =
        (cpus.filter (fun c => decide (c = cpu))).map (Loop gen) := by
      rw [List.filter_map]; congr 1
    simp only [CapPcLog.hartN, this, List.length_map]
    clear this
    revert cpu; decide
  have h2 : CapPcLog.hartN cpu (DevId.all.map (DevLoop gen)) = 0 := by
    simp [CapPcLog.hartN, List.filter_map, Function.comp_def, DevLoop, CapPcLog.isHartOf]
  rw [CapPcLog.hartNCons, powerFork, CapPcLog.hartNApp, h1, h2]
  rfl

/-- A pool step, inverted. -/
theorem CapPcLog.stepInv {ρ ρ' : List Expr × GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step ρ obs ρ') :
    ∃ (e : Expr) (σ : GState) (e' : Expr) (σ' : GState) (eₜ t₁ t₂ : List Expr),
      ρ = (t₁ ++ e :: t₂, σ) ∧ ρ' = (t₁ ++ e' :: t₂ ++ eₜ, σ') ∧ primStep (e, σ) obs (e', σ', eₜ) := by
  cases h with
  | @atomic e σ _ e' σ' eₜ H t₁ t₂ => exact ⟨e, σ, e', σ', eₜ, t₁, t₂, rfl, rfl, H⟩

/-- **One thread per hart along a run from power-on** that ends powered on in generation 0. -/
theorem CapPcLog.bootHartN {n : Nat} {g0 g : GState} {κ : List Obs} {t : List Expr}
    (h : MachOfPf.MRun n ([Expr.power], g0) κ (t, g)) (hp0 : g0.pow = false) (hg0 : g0.gen = 0)
    (hp : g.pow = true) (hg : g.gen = 0) (cpu : CPU) : CapPcLog.hartN cpu t = 1 := by
  cases h with
  | refl => rw [hp0] at hp; cases hp
  | @cons _ _ ρ₂ _ _ _ hs hr =>
    obtain ⟨e, σ, e', σ', eₜ, t₁, t₂, h1, h2, H⟩ := CapPcLog.stepInv hs
    obtain ⟨hl, rfl⟩ := Prod.mk.inj h1
    obtain ⟨rfl, rfl, rfl⟩ : t₁ = [] ∧ e = Expr.power ∧ t₂ = [] := by
      cases t₁ with
      | nil => simp only [List.nil_append, List.cons.injEq] at hl; exact ⟨rfl, hl.1.symm, hl.2.symm⟩
      | cons x t₁ => simp at hl
    obtain ⟨rfl, ⟨hp', -⟩ | ⟨-, -, rfl, hb⟩⟩ := H
    · rw [hp0] at hp'; cases hp'
    · subst h2
      have hN := CapPcLog.mrunHartN hr hb.2.1 (by simp only; rw [hg, hb.1, hg0]) cpu
      simp only at hN
      rw [hN]
      simpa using CapPcLog.hartNFork g0.gen cpu

/-- Two hart threads of `cpu` in a pool holding exactly one are the same thread. -/
theorem CapPcLog.hartNUnique {cpu : CPU} {t : List Expr} (h1 : CapPcLog.hartN cpu t = 1) {x y : Expr}
    (hx : x ∈ t) (hxh : CapPcLog.isHartOf cpu x = true) (hy : y ∈ t) (hyh : CapPcLog.isHartOf cpu y = true) :
    x = y := by
  unfold CapPcLog.hartN at h1
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.1 h1
  have hx' : x ∈ t.filter (CapPcLog.isHartOf cpu) := List.mem_filter.2 ⟨hx, hxh⟩
  have hy' : y ∈ t.filter (CapPcLog.isHartOf cpu) := List.mem_filter.2 ⟨hy, hyh⟩
  rw [hz, List.mem_singleton] at hx' hy'
  rw [hx', hy']

/-- **The storing thread is hart `cpu`'s pool thread**: in a pool `poolOf H F vs` holding one thread per
hart, a hart thread of `cpu` is `hartsOf H`'s, generation 0 running `H cpu`. -/
theorem CapPcLog.hartThreadIs {H : CPU → SailM Unit} {F : Efab} {vs t₁ t₂ : List Expr} {gen : Nat} {cpu : CPU}
    {m : SailM Unit} (hpool : t₁ ++ Expr.hart gen cpu m :: t₂ = MachOfPf.poolOf H F vs)
    (h1 : CapPcLog.hartN cpu (MachOfPf.poolOf H F vs) = 1) : gen = 0 ∧ m = H cpu := by
  have hx : Expr.hart gen cpu m ∈ MachOfPf.poolOf H F vs := by rw [← hpool]; simp
  have hy : Expr.hart 0 cpu (H cpu) ∈ MachOfPf.poolOf H F vs := by
    unfold MachOfPf.poolOf MachOfPf.hartsOf
    refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨cpu, ?_, rfl⟩))
    simp [cpus]
  have he := CapPcLog.hartNUnique h1 hx (by simp [CapPcLog.isHartOf]) hy (by simp [CapPcLog.isHartOf])
  cases he
  exact ⟨rfl, rfl⟩

/-! ## The appended pc of a recorded step (increment 12) -/

/-- `stAuthors` of a one-step extension. -/
theorem CapPcLog.stAuthorsSnoc (st : List (Nat × Wlabel)) (i : Nat) (l : Wlabel) :
    TsoShadow.stAuthors (st ++ [(i, l)]) =
      TsoShadow.stAuthors st ++ (if TsoShadow.lbWrites l then [i] else []) := by
  unfold TsoShadow.stAuthors
  rw [List.filterMap_append]
  cases h : TsoShadow.lbWrites l <;> simp [h]

theorem CapPcLog.mapSomeInj : ∀ {a b : List Nat}, a.map some = b.map some → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, CapPcLog.mapSomeInj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **`R-log` with `R-auth`**: at a related pair the machine log IS the step list's author list. -/
theorem CapPcLog.simLog {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {t : List Expr} {g : GState}
    (hR : MachOfPf.SimRel c st t g) : g.m.log = TsoShadow.stAuthors st :=
  CapPcLog.mapSomeInj (hR.mem.1.1.symm.trans hR.auth)

theorem CapPcLog.lbAppendsEq (l : Wlabel) : RelSiteProvPc.lbAppends l = TsoShadow.lbWrites l := by
  cases l <;> rfl

/-- A non-appending recorded step has no pc. -/
theorem CapPcLog.recPcNone {x : MachOfPf.PfRec} (h : TsoShadow.lbWrites x.lb = false) :
    RelSiteProvPc.recPc x = none := by
  simp [RelSiteProvPc.recPc, CapPcLog.lbAppendsEq, h]

/-- A run of at most one machine step: none, or one `Step`. -/
theorem CapPcLog.mrunLe1Step {m : Nat} {t t' : List Expr} {g g' : GState} {κ : List Obs}
    (h : MachOfPf.MRun m (t, g) κ (t', g')) (hm : m ≤ 1) :
    (t' = t ∧ g' = g) ∨ ∃ obs, Iris.ProgramLogic.Language.Step (t, g) obs (t', g') := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | cons hs hr =>
    cases hr with
    | refl => exact Or.inr ⟨_, hs⟩
    | cons _ _ => omega

/-- **One powered-on machine step, by its log effect**: the log and pc log kept; one store of a
named hart thread (its pc appended); or one disk entry (`-1` appended). -/
theorem CapPcLog.stepLogPc {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) (hp : g.pow = true) :
    (g'.m.log = g.m.log ∧ RelSiteProvExp.pcLogOf g'.m = RelSiteProvExp.pcLogOf g.m) ∨
    (∃ (t₁ t₂ : List Expr) (gen : Nat) (cpu : CPU) (n va : Nat)
      (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : (Outcome.memWrite n va req).ret → SailM Unit),
      t = t₁ ++ .hart gen cpu (.impure (.ok (.memWrite n va req)) k) :: t₂ ∧
      g'.m.log = g.m.log ++ [hartAgent cpu] ∧
      RelSiteProvExp.pcLogOf g'.m = RelSiteProvExp.pcLogOf g.m ++
        [if akExcl req.access_kind then -1 else (((g.m.regs cpu) LeanRV64D.Register.PC).toNat : Int)]) ∨
    (g'.m.log = g.m.log ++ [diskAgent] ∧
      RelSiteProvExp.pcLogOf g'.m = RelSiteProvExp.pcLogOf g.m ++ [-1]) := by
  rcases CapPcLog.stepStoreOf h hp with ⟨hl, hpc⟩ | ⟨t₁, t₂, gen, cpu, n, va, req, k, w, ht, he⟩ |
    ⟨d, pa, n, w, s', he⟩
  · exact Or.inl ⟨hl, CapPcLog.pcLogOfCongr hl hpc⟩
  · refine Or.inr (Or.inl ⟨t₁, t₂, gen, cpu, n, va, req, k, ht, by rw [he], ?_⟩)
    rw [he, CapPcLog.pcLogOfStore]
  · rw [he, CapPcLog.pcLogOfDmaDev]
    by_cases hn : n = 0
    · exact Or.inl ⟨by simp [hn], by rw [if_pos hn]⟩
    · exact Or.inr (Or.inr ⟨by simp [hn], by rw [if_neg hn]⟩)

/-- **A hart's appending pf step at a `memWrite` node is a plain store exactly when the access is
not exclusive** (`pnodeStep`'s `memWrite` arm; the wire step and the disk kinds append nothing / do
not apply to a hart). -/
theorem CapPcLog.storeLbl {k : MachOfPf.SKind} {cpu : CPU} {n va : Nat}
    {req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak}
    {kk : (Outcome.memWrite n va req).ret → SailM Unit} {rs : RegFile}
    {fn : Option (Bool × Bool × Bool × Bool)} {ib : Ibch} {d : Efab} {l : Wlabel} {p' : Pexv6}
    {d' : Efab}
    (hks : MachOfPf.kindStep k (.PHart cpu (.impure (.ok (.memWrite n va req)) kk) rs fn ib) d l p' d')
    (hw : TsoShadow.lbWrites l = true) : RelSiteProvPc.lbStore l = !akExcl req.access_kind := by
  cases k with
  | node =>
    cases p' with
    | PDisk _ => exact hks.elim
    | PHart cpu' m' rs' fn' ib' =>
      obtain ⟨-, ors, oib, obar, -, -, hn, -⟩ := hks
      unfold pstepNode at hn
      cases fn with
      | some f =>
        obtain ⟨pr, pw, sr, sw⟩ := f
        obtain ⟨rfl, -⟩ := hn
        simp [TsoShadow.lbWrites] at hw
      | none =>
        simp only [pnodeStep] at hn
        split at hn
        · split at hn
          · obtain ⟨-, rfl, -⟩ := hn
            simp [TsoShadow.lbWrites] at hw
          · exact hn.elim
        · split at hn
          · rcases hn with ⟨-, ⟨hlat, rfl, -⟩ | ⟨hlat, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩⟩
            · have h2 : akExcl req.access_kind = false := hlat
              simp [RelSiteProvPc.lbStore, h2]
            · have h2 : akExcl req.access_kind = true := hlat
              simp [RelSiteProvPc.lbStore, h2]
            · simp [TsoShadow.lbWrites] at hw
          · exact hn.elim
  | wire =>
    cases p' with
    | PDisk _ => exact hks.elim
    | PHart _ _ _ _ _ =>
      obtain ⟨-, ors, oib, obar, -, -, ⟨mm, b, k, -, rfl, -⟩⟩ := hks
      simp [TsoShadow.lbWrites] at hw
  | uart u => cases p' <;> exact hks.elim
  | gate => cases p' <;> exact hks.elim
  | disk => cases p' <;> exact hks.elim

/-- **One recorded pf step simulated by at most one machine step appends exactly its `recPc`** to
the machine's pc log: nothing for a non-appending step; for an appending one the machine step is the
store of the agent's own hart thread (`R-log` names the author, `hartThreadIs` the program `H cpu`)
whose exclusivity is the label's (`storeLbl`) and whose pc is the pf hart's (`SimRel.pool`), or a
disk entry (`-1`). -/
theorem CapPcLog.oneStepPc {g0 : GState} {c c' : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    {t t' : List Expr} {g g' : GState} {n : Nat} {κ : List Obs} {i : Nat} {l : Wlabel}
    {k : MachOfPf.SKind} {m : Nat} {obs : List Obs}
    (hp0 : g0.pow = false) (hg0 : g0.gen = 0)
    (hR : MachOfPf.SimRel c st t g) (hreach : MachOfPf.MRun n ([Expr.power], g0) κ (t, g))
    (hR' : MachOfPf.SimRel c' (st ++ [(i, l)]) t' g') (hk : MachOfPf.kindOk c i l c' k)
    (hm : MachOfPf.MRun m (t, g) obs (t', g')) (hle : m ≤ 1) :
    RelSiteProvExp.pcLogOf g'.m =
      RelSiteProvExp.pcLogOf g.m ++ (RelSiteProvPc.recPc ⟨c, i, l, k⟩).toList := by
  have hL' := CapPcLog.simLog hR'
  rw [CapPcLog.stAuthorsSnoc, ← CapPcLog.simLog hR] at hL'
  cases hw : TsoShadow.lbWrites l with
  | false =>
    rw [hw, if_neg Bool.false_ne_true, List.append_nil] at hL'
    rw [CapPcLog.recPcNone (x := ⟨c, i, l, k⟩) hw, Option.toList_none, List.append_nil]
    rcases CapPcLog.mrunLe1 hm hle hR.pow with rfl | hs
    · rfl
    · rcases CapPcLog.stepPcLen hs with ⟨-, h⟩ | ⟨hl, -⟩
      · exact h
      · rw [hL'] at hl; omega
  | true =>
    rw [hw, if_pos rfl] at hL'
    have hlen : ∀ {a : List Agent}, g.m.log = g.m.log ++ a → a = [] := fun h => by
      simpa using congrArg List.length h
    rcases CapPcLog.mrunLe1Step hm hle with ⟨rfl, rfl⟩ | ⟨obs', hs⟩
    · exact absurd (hlen hL') (by simp)
    rcases CapPcLog.stepLogPc hs hR.pow with ⟨hl, -⟩ | ⟨t₁, t₂, gen, cpu, n', va, req, kk, ht, hl, hp⟩ |
      ⟨hl, hp⟩
    · rw [hl] at hL'; exact absurd (hlen hL') (by simp)
    · rw [hl] at hL'
      have hi : hartAgent cpu = i := by simpa using List.append_cancel_left hL'
      subst hi
      obtain ⟨H, vs, dp, dws, dpr, hpool, -, hharts, -, -⟩ := hR.pool
      have hN := CapPcLog.bootHartN hreach hp0 hg0 hR.pow hR.gen cpu
      rw [hpool] at hN ht
      obtain ⟨-, hH⟩ := CapPcLog.hartThreadIs ht.symm hN
      obtain ⟨fn, ib, ws, pr, hlk0, -⟩ := hharts cpu
      obtain ⟨ag, p', ws', hlk, hks, -, -⟩ := hk
      have hlk' : c.pcAgs[cpu.val]? = some ag := hlk
      rw [hlk0, Option.some.injEq] at hlk'
      subst hlk'
      have hks' : MachOfPf.kindStep k (.PHart cpu (.impure (.ok (.memWrite n' va req)) kk) (g.m.regs cpu) fn ib)
          c.pcDev l p' c'.pcDev := by
        rw [hH]; exact hks
      have hst := CapPcLog.storeLbl hks' hw
      rw [hp]
      congr 1
      have hlb : RelSiteProvPc.lbAppends l = true := by rw [CapPcLog.lbAppendsEq, hw]
      simp only [RelSiteProvPc.recPc, hlb, hst, if_true, hartAgent, hlk0, Option.elim,
        RelSiteProvPc.pcOfSt]
      cases akExcl req.access_kind <;> rfl
    · rw [hl] at hL'
      have hi : diskAgent = i := by simpa using List.append_cancel_left hL'
      subst hi
      obtain ⟨H, vs, dp, dws, dpr, -, -, -, hdisk, -⟩ := hR.pool
      rw [hp]
      congr 1
      have hlb : RelSiteProvPc.lbAppends l = true := by rw [CapPcLog.lbAppendsEq, hw]
      simp only [RelSiteProvPc.recPc, hlb, if_true, diskAgent, hdisk, Option.elim,
        RelSiteProvPc.pcOfSt, ite_self]
      rfl

/-! ## The disk kind: a block of machine steps -/

/-- **The new log positions of a run and their pcs**: the log grows by `L`, the pc log by `ps`
(one per position), and every disk position carries `-1`. -/
def CapPcLog.diskPos (σ σ' : MState) : Prop :=
  ∃ (L : List Agent) (ps : List Int), σ'.log = σ.log ++ L ∧
    RelSiteProvExp.pcLogOf σ' = RelSiteProvExp.pcLogOf σ ++ ps ∧ ps.length = L.length ∧
    ∀ j : Nat, L[j]? = some diskAgent → ps[j]? = some (-1)

theorem CapPcLog.diskPosRefl (σ : MState) : CapPcLog.diskPos σ σ :=
  ⟨[], [], by simp, by simp, rfl, by simp⟩

theorem CapPcLog.diskPosTrans {σ1 σ2 σ3 : MState} (h1 : CapPcLog.diskPos σ1 σ2)
    (h2 : CapPcLog.diskPos σ2 σ3) : CapPcLog.diskPos σ1 σ3 := by
  obtain ⟨L1, p1, hl1, hp1, hn1, hd1⟩ := h1
  obtain ⟨L2, p2, hl2, hp2, hn2, hd2⟩ := h2
  refine ⟨L1 ++ L2, p1 ++ p2, by rw [hl2, hl1, List.append_assoc],
    by rw [hp2, hp1, List.append_assoc], by simp [hn1, hn2], ?_⟩
  intro j hj
  rcases Nat.lt_or_ge j L1.length with h | h
  · rw [List.getElem?_append_left h] at hj
    rw [List.getElem?_append_left (by omega)]
    exact hd1 j hj
  · rw [List.getElem?_append_right h] at hj
    rw [List.getElem?_append_right (by omega), hn1]
    exact hd2 _ hj

/-- One powered-on step: a hart store's position is not the disk's. -/
theorem CapPcLog.stepDiskPos {t t' : List Expr} {g g' : GState} {obs : List Obs}
    (h : Iris.ProgramLogic.Language.Step (t, g) obs (t', g')) (hp : g.pow = true) :
    CapPcLog.diskPos g.m g'.m := by
  rcases CapPcLog.stepLogPc h hp with ⟨hl, hpc⟩ | ⟨_, _, _, cpu, _, _, _, _, _, hl, hpc⟩ | ⟨hl, hpc⟩
  · exact ⟨[], [], by simp [hl], by simp [hpc], rfl, by simp⟩
  · refine ⟨[hartAgent cpu], _, hl, hpc, rfl, ?_⟩
    intro j hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact absurd hj (Nat.ne_of_lt cpu.isLt)
    | succ j => simp at hj
  · refine ⟨[diskAgent], [-1], hl, hpc, rfl, fun j hj => ?_⟩
    cases j with
    | zero => rfl
    | succ j => simp at hj

/-- **Along a powered-on run ending in the same generation**, `diskPos`. -/
theorem CapPcLog.mrunDiskPos {n : Nat} {ρ ρ' : List Expr × GState} {κ : List Obs}
    (h : MachOfPf.MRun n ρ κ ρ') (hp : ρ.2.pow = true) (hg : ρ'.2.gen = ρ.2.gen) :
    CapPcLog.diskPos ρ.2.m ρ'.2.m := by
  induction h with
  | refl => exact CapPcLog.diskPosRefl _
  | @cons _ ρ₁ ρ₂ ρ₃ _ _ hs hr ih =>
    obtain ⟨t₁, g₁⟩ := ρ₁
    obtain ⟨t₂, g₂⟩ := ρ₂
    have hm := CapPcLog.mrunGen hr
    rcases (CapPcLog.stepGen hs).2 hp with ⟨hg2, hp2⟩ | hg2
    · exact CapPcLog.diskPosTrans (CapPcLog.stepDiskPos hs hp)
        (ih hp2 (by simp only at hg hg2 ⊢; omega))
    · simp only at hg hg2 hm; omega

/-- **A recorded disk-agent step** (any number of machine steps) appends exactly its `recPc`
(`-1` if it appends). -/
theorem CapPcLog.diskStepPc {c c' : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {t t' : List Expr}
    {g g' : GState} {i : Nat} {l : Wlabel} {k : MachOfPf.SKind} {m : Nat} {obs : List Obs}
    {ag : Wpagent Pexv6} {dp : Option (DM Dres)}
    (hR : MachOfPf.SimRel c st t g) (hR' : MachOfPf.SimRel c' (st ++ [(i, l)]) t' g')
    (hlk : c.pcAgs[i]? = some ag) (hd : ag.paSt = .PDisk dp) (hm : MachOfPf.MRun m (t, g) obs (t', g')) :
    RelSiteProvExp.pcLogOf g'.m =
      RelSiteProvExp.pcLogOf g.m ++ (RelSiteProvPc.recPc ⟨c, i, l, k⟩).toList := by
  have hi := MachOfPf.diskAgentIdx hR hlk hd
  obtain ⟨L, ps, hl, hp, hn, hdk⟩ := CapPcLog.mrunDiskPos hm hR.pow (by simp only; rw [hR.gen, hR'.gen])
  have hL' := CapPcLog.simLog hR'
  rw [CapPcLog.stAuthorsSnoc, ← CapPcLog.simLog hR, hl] at hL'
  have hLA := List.append_cancel_left hL'
  rw [hp]
  congr 1
  cases hw : TsoShadow.lbWrites l with
  | false =>
    rw [hw] at hLA
    rw [CapPcLog.recPcNone (x := ⟨c, i, l, k⟩) hw, Option.toList_none]
    rw [hLA] at hn
    exact List.eq_nil_of_length_eq_zero hn
  | true =>
    rw [hw, if_pos rfl] at hLA
    rw [hLA] at hn hdk
    obtain ⟨p, rfl⟩ : ∃ p, ps = [p] := by
      match ps, hn with
      | [p], _ => exact ⟨p, rfl⟩
    have h0 := hdk 0 (by rw [hi]; rfl)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    have hlb : RelSiteProvPc.lbAppends l = true := by rw [CapPcLog.lbAppendsEq, hw]
    simp only [RelSiteProvPc.recPc, hlb, if_true, hlk, Option.elim, hd, RelSiteProvPc.pcOfSt, ite_self]
    rfl

/-! ## The run induction: `pcLogAgree` -/

/-- **`simRun` with the pc log**: from a related, boot-reachable MachCSL configuration, the rest of the
run ends related, and its pc log grows by exactly the record's issuing-pc log. -/
theorem CapPcLog.simRunPc {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab}
    (hH : MachOfPf.HypsC fok fcutT g0 c0) (hp0 : g0.pow = false) (hg0 : g0.gen = 0) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List MachOfPf.PfRec} {cN : Wpcfg Pexv6 Efab},
      MachOfPf.contRC fok fcutT c st r cN →
      ∀ {t : List Expr} {g : GState} {n : Nat} {κ : List Obs},
        MachOfPf.SimRel c st t g → MachOfPf.MRun n ([Expr.power], g0) κ (t, g) →
        pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c →
        pairAdjacent (st ++ MachOfPf.recLabels r) →
        ∃ (m : Nat) (t' : List Expr) (g' : GState),
          MachOfPf.MRun m ([Expr.power], g0) (κ ++ MachOfPf.pfObsOf r) (t', g') ∧
          MachOfPf.SimRel cN (st ++ MachOfPf.recLabels r) t' g' ∧
          RelSiteProvExp.pcLogOf g'.m = RelSiteProvExp.pcLogOf g.m ++ RelSiteProvPc.recPcLog r := by
  intro c st r cN h
  induction h with
  | nil c st =>
    intro t g n κ hR hreach _ _
    exact ⟨n, t, g, by simpa [MachOfPf.pfObsOf] using hreach, by simpa [MachOfPf.recLabels] using hR,
      by simp [RelSiteProvPc.recPcLog]⟩
  | cons c c' st i l k r cN hs hf hfT hcf hk hr ih =>
    intro t g n κ hR hreach hrun hadj
    have hadj' : pairAdjacent (st ++ (i, l) :: MachOfPf.recLabels r) := by
      simpa [MachOfPf.recLabels] using hadj
    obtain ⟨m1, t1, g1, hle, hm1, hR1⟩ := MachOfPf.simStep hH hR hreach hrun hs hf hfT hcf hk hadj'
      (fun aq base tvs asrc hl => by subst hl; exact MachOfPf.exclAhead fok hs hr hadj')
    have hpc1 : RelSiteProvExp.pcLogOf g1.m =
        RelSiteProvExp.pcLogOf g.m ++ (RelSiteProvPc.recPc ⟨c, i, l, k⟩).toList := by
      by_cases hkd : k = .disk
      · subst hkd
        obtain ⟨ag, p', ws', hlk, hks, -, -⟩ := hk
        obtain ⟨st0, ws0, pr0⟩ := ag
        cases st0 with
        | PHart _ _ _ _ _ => cases p' <;> exact hks.elim
        | PDisk dp0 => exact CapPcLog.diskStepPc (ag := ⟨.PDisk dp0, ws0, pr0⟩) hR hR1 hlk rfl hm1
      · exact CapPcLog.oneStepPc hp0 hg0 hR hreach hR1 hk hm1 (hle hkd)
    obtain ⟨m2, t2, g2, hm2, hR2, hpc2⟩ :=
      ih hR1 (MachOfPf.mrunTrans hreach hm1) (pfRunST.snoc c c' st i l hrun hs hf hfT)
        (by simpa using hadj')
    refine ⟨m2, t2, g2, ?_, by simpa [MachOfPf.recLabels] using hR2, ?_⟩
    · rw [MachOfPf.pfObsOfCons, ← List.append_assoc]
      exact hm2
    · rw [hpc2, hpc1, RelSiteProvPc.recPcLogCons]
      cases RelSiteProvPc.recPc ⟨c, i, l, k⟩ <;> simp

/-- **W4's theorem with (a2)** (`MachOfPf.machRunOfPfRun` plus `CapRelSite.pcLogAgree`): the MachCSL
run W4 builds from power-on ends at a state whose per-store pc record IS the run record's
issuing-pc log. -/
theorem CapPcLog.machRunPc (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (σ0 : WGState) (ds : DevStates) (g0 : GState)
    (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hgd : g0.m.devs = ds)
    (hH : MachOfPf.HypsC fok fcutT g0 (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)))
    (st : List (Nat × Wlabel)) (cN : Wpcfg Pexv6 Efab)
    (hrun : pfRunSTC pstepEv pclsEv fok TsoShadow.cohSrc fcutT
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cN)
    (hadj : pairAdjacent st) :
    ∃ r : List MachOfPf.PfRec,
      MachOfPf.contRC fok fcutT (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cN ∧
      MachOfPf.recLabels r = st ∧
      ∃ (n : Nat) (t : List Expr) (g : GState),
        MachOfPf.MRun n ([Expr.power], g0) (Obs.powerOn :: MachOfPf.pfObsOf r) (t, g) ∧
        MachOfPf.SimRel cN st t g ∧ CapRelSite.pcLogAgree r g.m := by
  obtain ⟨r, hr, hl⟩ := MachOfPf.contROfRun fok hrun
  have hboot := MachOfPf.powerOnRun g0 σ0 ds hb hg0 hp0 hgd
  have hR0 := MachOfPf.simRelBoot σ0 ds hb hds
  obtain ⟨m, t, g, hm, hR, hpc⟩ :=
    CapPcLog.simRunPc hH hp0 hg0 hr hR0 hboot pfRunST.nil (by simpa [hl] using hadj)
  refine ⟨r, hr, hl, m, t, g, by simpa using hm, by simpa [hl] using hR, ?_⟩
  unfold CapRelSite.pcLogAgree
  rw [hpc]
  simp [RelSiteProvExp.pcLogOf, MachOfPf.bootG1]

/-! ## The release-site fact at `readAt`'s configuration -/

/-- **`readAt` at the primed twin of a realized configuration** (W11-C's realized read, with its
release-site clause): from a W4 record `r` ending at `cf` (any record end — e.g. the realized
configuration of a candidate load, `CapF8.loadReadAtParts`), `rmem`, the export, (a2)
(`CapPcLog.machRunPc`) and (a3) (`relArmedOf`), the read's message clauses at `cf` give a primed
twin `cf′` (`WbPrimed.cfgRel`: same image, fabric, agents, tids, bytes; classes re-tagged) and the
same message `m′` (up to class) at which `readAt` holds in full.

The release-site clause CANNOT be moved to `cf` itself: `relSiteWCrel` reads the CLASS of each
release-site message, and on W4's registered machine an `LExStore` (the walker's A/D write-back of
the release `sw`'s own translation, issued after `fence rw,w`) clears the release-pending flag, so the
registered class of that `sw` is `.WCplain` [OWN.97]; `cfgRel` relates the logs only up to a re-tag,
so nothing carries the primed `.WCrel` back.  The conclusion therefore stays on the primed twin,
where every other conjunct of `readAt` holds verbatim (`WbPrimed.readAtPrimed`). -/
theorem CapPcLog.readAtPrimedOf {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st0 : List (Nat × Wlabel)} {r : List MachOfPf.PfRec} {cf : Wpcfg Pexv6 Efab}
    (h : MachOfPf.contRC fok fcutT c st0 r cf) (h0 : c.pcLog = [])
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (hR : PfStepTsoMem.rmem cf st σ) (hD : Xv6.AccessDiscipline.xv6AccessDisc σ)
    (ha2 : CapRelSite.pcLogAgree r σ) (ha3 : WbPrimed.relArmed r)
    (hp : cf.pcLog[p]? = some m) (hv : (msgByte m (paZ pa)).isSome) (hram : inRam pa 1)
    (hcoh : (σ.hr j).coh pa = p + 1) :
    ∃ cf', WbPrimed.cfgRel cf cf' ∧ ∃ m', cf'.pcLog[p]? = some m' ∧ m'.wmPa = m.wmPa ∧
      m'.wmData = m.wmData ∧ m'.wmTid = m.wmTid ∧ readAt cf'.pcLog cf' st σ j pa p m' := by
  obtain ⟨cf', hrel, hsite⟩ := CapRelSite.relSiteWCrelOf h h0 σ hD ha2 ha3
  exact ⟨cf', hrel, WbPrimed.readAtPrimed cf'.pcLog cf cf' st σ j pa p m hR hrel hD hsite
    (List.prefix_refl _) hp hv hram hcoh⟩

end Weak

/-
Weak: **discharging `CapRelSite.pcLogAgree` -- the machine's pc log along a run** (W11-C2′ (a2)
[OWN.82]; mcslrec (2)), increment 1: how each MachCSL state change moves the issuing-pc log
`RelSiteProvExp.pcLogOf σ` (one entry per store position).  Lean-only, no Rocq twin.

* `CapPcLog.pcLogOfStore`: a hart's store appends the store's pc (its `PC` for a plain store,
  `-1` for an exclusive / AMO write) -- `RelSiteProvPc.recPc`'s value for the same record.
* `CapPcLog.pcLogOfDma`: a DMA write appends `-1` (the disk agent's pc in `recPc`); a zero-byte
  one is the identity.
* `CapPcLog.pcLogOfCongr`: a change that keeps the log and the pc record keeps the pc log.

Next (resume): along `simRunAt`/`simStep` (`Weak/MachOfPf.lean`), a non-appending pf step's
MachCSL run keeps `log`/`pcAt`, an appending one performs exactly one store (or DMA write) whose pc
is the record's `recPc` (`SimRel.pool`: the hart's register file IS the MachCSL hart's), so
`recPcLog r = pcLogOf g.m` at the run's end -- `CapRelSite.pcLogAgree`.

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

end Weak

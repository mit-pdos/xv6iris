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

end Weak

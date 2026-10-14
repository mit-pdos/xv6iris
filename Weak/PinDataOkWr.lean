/-
Weak: **`dataOkR` (3e) — the memory WRITES under `dkB`**: `checked_mem_write` of a data store or a
PTE write-back at an aligned RAM address answers `Ok true`; `mem_write_ea` never `Err`
(`Mem.lean:503-600`; a write node is answered `.Ok (some true)`, `WeakEvInst.pnodeStep`);
`PROGRESS-dataOk.md`.  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkRd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

set_option maxHeartbeats 40000000 in
/-- `within_mmio_writable` answers `false` at a RAM address. -/
theorem PinDataOk.xfWithinMmioWritableRam (pa : physaddr) (w : Nat)
    (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    xf (fun r => r = false) (within_mmio_writable pa w) := by
  xf_walk_v
  all_goals first
    | rfl
    | (exfalso; have := SailCycleOrderFp.clintNotRam _ _ ‹_›; simp only [bits_of_physaddr] at h; omega)
    | (simp only [Rboot] at *; contradiction)
    | trace_state

/-- **The RAM write leaf** answers `true`. -/
theorem dkWriteRam (wk : write_kind) (pa : BitVec 64) (n : Nat) (v : BitVec (8 * n)) (m : Unit) :
    dkB c (fun b => b = true) (write_ram wk (.Physaddr pa) n v m) := by
  cases wk <;>
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit, pure_bind, bind_assoc] <;>
  first
    | rfl
    | trivial
    | (simp only [internal_error]; trivial)
    | trace_state

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`checked_mem_write` of a data store / PTE write-back answers `Ok true`** at an aligned RAM
address. -/
theorem dkCheckedMemWriteOk (pa : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (con : Bool)
    (hacc : (acc = .Store .Data ∧ con = false) ∨ acc = .Store .PageTableEntry)
    (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 8) (hal : pa.toNat % w = 0) (priv : Privilege) :
    dkB c (fun r => r = .Ok true)
      (checked_mem_write (.Physaddr pa) w data acc .PBMT_PMA priv () false false con) := by
  have hal' : is_aligned_paddr (.Physaddr pa) w = true := by
    simp only [is_aligned_paddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  have hk : pmaKind acc con := by
    rcases hacc with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hrwx : pmpCheckRWX 0x0f#8 acc = pure true := by rcases hacc with ⟨rfl, -⟩ | rfl <;> rfl
  have hpo : pmpOk pa w := by
    simp only [inRam, ramBase, ramEnd] at hram; unfold pmpOk; omega
  have htm : Int.tmod (BitVec.toNatInt pa) w = 0 := by
    simp only [BitVec.toNatInt]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  rcases hacc with ⟨rfl, rfl⟩ | rfl
  all_goals (try cases con)
  all_goals
    simp only [checked_mem_write, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
      bind_assoc, pure_bind, ExceptT.run_pure, check_pma_with_pmp_priority, write_kind_of_flags]
    refine dkBind _ _ _ _ (dkPmaCheckRam pa w _ _ hk hram hw (by omega) hal') (fun r hr => ?_)
    cases r with
    | Err e => exact absurd rfl (hr e)
    | Ok info =>
      simp only [ExceptT.run_pure, pure_bind]
      rw [bind_assoc]
      refine dkXfBind _ _ _ _ (PinFetchPaFp.xfSplitAligned pa w _ _ htm) (fun p hp => ?_)
      subst hp
      simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
        Bool.false_eq_true, ↓reduceIte]
      rw [show Int.toNat 1 = 0 + 1 from rfl]
      simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine dkXfT _ _ (PinDataOk.xfAssertTrue _) (fun _ => ?_)
      have e0 : BitVec.addInt (bits_of_physaddr (physaddr.Physaddr pa)) (↑(Int.toNat 0) * (w : Int)) = pa :=
        SailCycleOrderFp.addInt0 _ _
      have ew : Int.toNat (w : Int) = w := Int.toNat_natCast w
      simp only [e0, ew]
      refine dkBind _ _ _ _ (dkPmpCheck pa w _ priv hpo hrwx) (fun o ho => ?_)
      subst ho
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine dkXfBind _ _ _ _ (PinDataOk.xfWithinMmioWritableRam (.Physaddr pa) w hram.1) (fun b hb => ?_)
      subst hb
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine dkBind _ _ _ _ (dkWriteRam _ _ _ _ _) (fun v hv => ?_)
      subst hv
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind, Bool.and_true]
      rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **`mem_write_ea`** of a data store / PTE write-back never answers `Err` at an aligned RAM
address. -/
theorem dkMemWriteEaOk (pa : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload) (con : Bool)
    (hacc : (acc = .Store .Data ∧ con = false) ∨ acc = .Store .PageTableEntry)
    (hram : inRam pa w) (hw : 0 < w) (hw' : w ≤ 8) (hal : pa.toNat % w = 0) :
    dkB c (fun r => ∀ e, r ≠ .Err e) (mem_write_ea (.Physaddr pa) w acc .PBMT_PMA false false con) := by
  have hal' : is_aligned_paddr (.Physaddr pa) w = true := by
    simp only [is_aligned_paddr, BitVec.toNatInt, beq_iff_eq]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  have hk : pmaKind acc con := by
    rcases hacc with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hrwx : pmpCheckRWX 0x0f#8 acc = pure true := by rcases hacc with ⟨rfl, -⟩ | rfl <;> rfl
  have hpo : pmpOk pa w := by
    simp only [inRam, ramBase, ramEnd] at hram; unfold pmpOk; omega
  have htm : Int.tmod (BitVec.toNatInt pa) w = 0 := by
    simp only [BitVec.toNatInt]
    rw [Int.ofNat_eq_natCast, ← Int.ofNat_tmod, hal]; rfl
  rcases hacc with ⟨rfl, rfl⟩ | rfl
  all_goals (try cases con)
  all_goals
    simp only [mem_write_ea, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
      bind_assoc, pure_bind, ExceptT.run_pure, check_pma_with_pmp_priority, write_kind_of_flags]
    refine dkReadReg _ _ (fun _ _ => ?_)
    refine dkReadReg _ _ (fun _ _ => ?_)
    refine dkXfT _ _ (xfEffectivePrivilege _ _ _) (fun priv => ?_)
    refine dkBind _ _ _ _ (dkPmaCheckRam pa w _ _ hk hram hw (by omega) hal') (fun r hr => ?_)
    cases r with
    | Err e => exact absurd rfl (hr e)
    | Ok info =>
      simp only [ExceptT.run_pure, pure_bind]
      rw [bind_assoc]
      refine dkXfBind _ _ _ _ (PinFetchPaFp.xfSplitAligned pa w _ _ htm) (fun p hp => ?_)
      subst hp
      simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
        Bool.false_eq_true, ↓reduceIte]
      rw [show Int.toNat 1 = 0 + 1 from rfl]
      simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine dkXfT _ _ (PinDataOk.xfAssertTrue _) (fun _ => ?_)
      have e0 : BitVec.addInt (bits_of_physaddr (physaddr.Physaddr pa)) (↑(Int.toNat 0) * (w : Int)) = pa :=
        SailCycleOrderFp.addInt0 _ _
      have ew : Int.toNat (w : Int) = w := Int.toNat_natCast w
      simp only [e0, ew]
      refine dkBind _ _ _ _ (dkPmpCheck pa w _ priv hpo hrwx) (fun o ho => ?_)
      subst ho
      have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
      simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind, ExceptT.run_bind, run_liftM, bind_assoc]
      intro e h; cases h

/-- **The Svadu write-back** (`write_pte_conditional`) at a walk slot answers `Ok true`. -/
theorem dkWritePteCond (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (pte : BitVec (8 * 8)) :
    dkB c (fun r => r = .Ok true) (write_pte_conditional (.Physaddr pa) 8 pte) := by
  simp only [write_pte_conditional, mem_write_value_priv, mem_write_value_priv_meta]
  exact dkBind _ _ _ _ (dkCheckedMemWriteOk pa 8 pte _ true (Or.inr rfl) hram (by decide) (by decide)
    hal .Supervisor) (fun r h => h)

/-- **A data store's value write** (`mem_write_value`) answers `Ok true`. -/
theorem dkMemWriteValue (pa : BitVec 64) (w : Nat) (v : BitVec (8 * w)) (hram : inRam pa w)
    (hw : 0 < w) (hw' : w ≤ 8) (hal : pa.toNat % w = 0) :
    dkB c (fun r => r = .Ok true) (mem_write_value (.Physaddr pa) w v (.Store .Data) .PBMT_PMA false false false) := by
  simp only [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta, bind_assoc]
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkReadReg _ _ (fun _ _ => ?_)
  refine dkXfT _ _ (xfEffectivePrivilege _ _ _) (fun priv => ?_)
  exact dkBind _ _ _ _ (dkCheckedMemWriteOk pa w v _ false (Or.inl ⟨rfl, rfl⟩) hram hw hw' hal priv)
    (fun r h => h)

end PinDataOk
end Weak

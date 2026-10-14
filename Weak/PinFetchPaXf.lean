/-
Weak: **W9a (B) B5 r2 part (B) — the `satp`/`tlb`-free footprints of the fetch translation's
register-only and memory leaves** (`@[xf_reg]`, walked by `PinFetchPaFp.xf_walk`; plan rev 52 §D
Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).  Lean-only.

The same statements as W-SCO's `fp` leaves (`Weak/SailCycleOrderAllMem.lean`,
`Weak/SailCycleOrderFetch.lean`), re-walked for `xfB` (whose writes never touch `satp`/`tlb`), plus
`xfSplitAligned` (an aligned access is one access of the whole width,
`SplitAccessUtils.lean:256`).  Every helper is `Weak.PinFetchPaFp.*`.
-/
import Weak.PinFetchPaFp
import Weak.SailCycleOrderFetch

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinFetchPaFp
open SailCycleOrderK

@[xf_reg] theorem xfReadKindOfFlags (aq rl res : Bool) :
    xf (fun rk => rk ≠ .Read_ifetch) (read_kind_of_flags aq rl res) := by
  unfold read_kind_of_flags; split <;> first | trivial | (intro h; cases h)


set_option maxHeartbeats 4000000 in
@[xf_reg] theorem xfReadRam (rk : read_kind) (h : rk ≠ .Read_ifetch) (pa : physaddr) (w : Nat) (m : Bool) :
    xfT (read_ram rk pa w m) := by
  xf_walk


set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfRX (app_0 : regno) :
    xfT (rX app_0) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfWX (typ_0 : regno) (in_v : (BitVec 64)) :
    xfT (wX typ_0 in_v) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfRXBits (app_0 : regidx) :
    xfT (rX_bits app_0) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfWXBits (typ_0 : regidx) (data : (BitVec 64)) :
    xfT (wX_bits typ_0 data) := by
  xf_walk


set_option maxHeartbeats 8000000 in
@[xf_reg] theorem xfCurrentlyEnabled (e : extension) : xfT (currentlyEnabled e) := by
  cases e <;> xf_walk


set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfAccessFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    xfT (accessFaultFromAccessType access) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfAlignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    xfT (alignmentFaultFromAccessType access) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfTranslationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) :
    xfT (translationException access err) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfIsShadowStackAccess (access : (MemoryAccessType mem_payload)) :
    xfT (is_shadow_stack_access access) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfCheckPTEPermission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (a5_0 : (BitVec 10)) (a6_0 : Unit) :
    xfT (check_PTE_permission access priv mxr do_sum pte_flags a5_0 a6_0) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfPmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) :
    xfT (pmpCheckRWX ent access) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfIsMagApplicableAccess (access : (MemoryAccessType mem_payload)) (width : Nat) :
    xfT (is_mag_applicable_access access width) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfPmaMisalignedException (pma : PMA) (access : (MemoryAccessType mem_payload)) :
    xfT (pma_misaligned_exception pma access) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfMagPmaCheck (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) :
    xfT (mag_pma_check pma access paddr width) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfPmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) :
    xfT (pmpCheck addr width access priv) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfPmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) :
    xfT (pmaCheck paddr width access pbmt res_or_con) := by
  xf_walk

set_option maxHeartbeats 40000000 in
@[xf_reg] theorem xfEffectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) :
    xfT (effectivePrivilege access m priv) := by
  xf_walk

set_option maxHeartbeats 40000000 in
/-- `within_mmio_readable` answers `false` at a RAM address. -/
theorem xfWithinMmioRam (pa : physaddr) (w : Nat) (h : 0x80000000 ≤ (bits_of_physaddr pa).toNat) :
    xf (fun r => r = false) (within_mmio_readable pa w) := by
  xf_walk_v
  all_goals first
    | rfl
    | (exfalso; have := SailCycleOrderFp.clintNotRam _ _ ‹_›; simp only [bits_of_physaddr] at h; omega)
    | (simp only [Rboot] at *; contradiction)

set_option maxHeartbeats 40000000 in
/-- An aligned access is one access of the whole width. -/
theorem xfSplitAligned (pa : BitVec 64) (w : Nat) (e : Nat) (sp : Splittability)
    (h : Int.tmod (BitVec.toNatInt pa) w = 0) :
    xf (fun p => p = (1, (w : Int))) (split_misaligned (.Physaddr pa) w e sp) := by
  unfold split_misaligned
  simp only [h, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]
  rfl

end PinFetchPaFp
end Weak

/-
Weak: **W11-C2′ (a3) relArmed — `zfB` footprints of the memory pieces** (the `zfB` twins of
`Weak/PinCycRunMem.lean`, walked by `zf_walk`): no protected register write and no plain RAM
store in the read kind, `read_ram`, the extension cluster, the access checks, PMP/PMA, the page
walk `pt_walk` (its A/D write-back is `write_pte_conditional`, exclusive) and `translateAddr`.
Lean-only.  Every helper is `Weak.PinRelArmFp.*`.
-/
import Weak.PinRelArmFp
import Weak.PinDataflowMem
import Weak.SailCycleOrderAllMem

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinRelArmFp
open SailCycleOrderK

@[zf_reg] theorem zfReadKindOfFlags (aq rl res : Bool) :
    zf (fun rk => rk ≠ .Read_ifetch) (read_kind_of_flags aq rl res) := by
  unfold read_kind_of_flags; split <;> first | trivial | (intro h; cases h)


set_option maxHeartbeats 4000000 in
@[zf_reg] theorem zfReadRam (rk : read_kind) (h : rk ≠ .Read_ifetch) (pa : physaddr) (w : Nat) (m : Bool) :
    zfT (read_ram rk pa w m) := by
  zf_walk


set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfRX (app_0 : regno) :
    zfT (rX app_0) := by
  zf_walk


set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfRXBits (app_0 : regidx) :
    zfT (rX_bits app_0) := by
  zf_walk



set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfCurrentlyEnabled (e : extension) : zfT (currentlyEnabled e) := by
  cases e <;> zf_walk


set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfAccessFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    zfT (accessFaultFromAccessType access) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfAlignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    zfT (alignmentFaultFromAccessType access) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfTranslationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) :
    zfT (translationException access err) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfIsShadowStackAccess (access : (MemoryAccessType mem_payload)) :
    zfT (is_shadow_stack_access access) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfCheckPTEPermission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (a5_0 : (BitVec 10)) (a6_0 : Unit) :
    zfT (check_PTE_permission access priv mxr do_sum pte_flags a5_0 a6_0) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfPmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) :
    zfT (pmpCheckRWX ent access) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfIsMagApplicableAccess (access : (MemoryAccessType mem_payload)) (width : Nat) :
    zfT (is_mag_applicable_access access width) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfPmaMisalignedException (pma : PMA) (access : (MemoryAccessType mem_payload)) :
    zfT (pma_misaligned_exception pma access) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfMagPmaCheck (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) :
    zfT (mag_pma_check pma access paddr width) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfPmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) :
    zfT (pmpCheck addr width access priv) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfPmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) :
    zfT (pmaCheck paddr width access pbmt res_or_con) := by
  zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfEffectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) :
    zfT (effectivePrivilege access m priv) := by
  zf_walk


set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfCheckedMemRead (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ())
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    zfT (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  zf_walk
  all_goals simp_all


/-- A conditional write kind (the store-conditional family). -/
def wkCon (wk : write_kind) : Prop :=
  wk = .Write_RISCV_conditional ∨ wk = .Write_RISCV_conditional_release ∨
    wk = .Write_RISCV_conditional_strong_release

@[zf_reg] theorem zfWriteKindCon (aq rl : Bool) :
    zf wkCon (write_kind_of_flags aq rl true) := by
  unfold write_kind_of_flags
  split <;> first
    | (exact Or.inl rfl) | (exact Or.inr (Or.inl rfl)) | (exact Or.inr (Or.inr rfl)) | trivial
    | (rename_i h; simp at h)

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfWriteRamCon (wk : write_kind) (h : wkCon wk) (pa : physaddr) (w : Nat)
    (data : BitVec (8 * w)) (m : Unit) : zfT (write_ram wk pa w data m) := by
  rcases h with rfl | rfl | rfl <;> (unfold write_ram; zf_walk)

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfCheckedMemWriteCon (pa : physaddr) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege) (m : Unit)
    (aq rl : Bool) : zfT (checked_mem_write pa w data acc pbmt priv m aq rl true) := by
  unfold checked_mem_write
  zf_walk

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfWritePteConditional (pa : physaddr) (n : Nat) (pte : BitVec (n * 8)) :
    zfT (write_pte_conditional pa n pte) := by
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  zf_walk

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfPtWalk (sv : Nat) (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) :
    ∀ (level : Nat) (base : BitVec (if (sv = 32 : Bool) then 22 else 44)) (g : Bool) (ext : Unit),
      zfT (pt_walk sv vpn acc priv mxr sum base level g ext) := by
  intro level
  induction level using Nat.strongRecOn with
  | ind level ih =>
    intro base g ext
    rw [pt_walk]
    zf_walk
    all_goals (apply SailCycleOrderFp.ptMeasure; assumption)

set_option maxHeartbeats 8000000 in
@[zf_reg] theorem zfTranslateAddr (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    zfT (translateAddr va acc) := by
  zf_walk


end PinRelArmFp
end Weak

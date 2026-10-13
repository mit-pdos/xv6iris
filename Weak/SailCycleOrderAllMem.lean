/-
Weak: **W-SCO (A) — footprints of the memory pieces** (plan rev 36 §C W-SCO (A) (1)(a)): the read
kind, `read_ram` off `Read_ifetch`, `checked_mem_read` / `mem_read` off `InstructionFetch`, the
extension and stateen cluster (`currentlyEnabled` and its mutual block, unfolded at closed
arguments), the page-table walk `pt_walk` (induction on the level), `translateAddr` (every access
type: its page-table reads are `Read_ttw`).  Lean-only.
-/
import Weak.SailCycleOrderFp

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp
set_option profiler true
set_option profiler.threshold 2000

@[fp_reg] theorem fpReadKindOfFlags (aq rl res : Bool) :
    fp (fun rk => rk ≠ .Read_ifetch) (read_kind_of_flags aq rl res) := by
  unfold read_kind_of_flags; split <;> first | trivial | (intro h; cases h)


set_option maxHeartbeats 4000000 in
@[fp_reg] theorem fpReadRam (rk : read_kind) (h : rk ≠ .Read_ifetch) (pa : physaddr) (w : Nat) (m : Bool) :
    fpT (read_ram rk pa w m) := by
  fp_walk


set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpRX (app_0 : regno) :
    fpT (rX app_0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpWX (typ_0 : regno) (in_v : (BitVec 64)) :
    fpT (wX typ_0 in_v) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpRXBits (app_0 : regidx) :
    fpT (rX_bits app_0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpWXBits (typ_0 : regidx) (data : (BitVec 64)) :
    fpT (wX_bits typ_0 data) := by
  fp_walk


set_option maxHeartbeats 8000000 in
@[fp_reg] theorem fpCurrentlyEnabled (e : extension) : fpT (currentlyEnabled e) := by
  cases e <;> fp_walk


set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpAccessFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    fpT (accessFaultFromAccessType access) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpAlignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    fpT (alignmentFaultFromAccessType access) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpTranslationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) :
    fpT (translationException access err) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpIsShadowStackAccess (access : (MemoryAccessType mem_payload)) :
    fpT (is_shadow_stack_access access) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpCheckPTEPermission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (a5_0 : (BitVec 10)) (a6_0 : Unit) :
    fpT (check_PTE_permission access priv mxr do_sum pte_flags a5_0 a6_0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpPmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) :
    fpT (pmpCheckRWX ent access) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpIsMagApplicableAccess (access : (MemoryAccessType mem_payload)) (width : Nat) :
    fpT (is_mag_applicable_access access width) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpPmaMisalignedException (pma : PMA) (access : (MemoryAccessType mem_payload)) :
    fpT (pma_misaligned_exception pma access) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpMagPmaCheck (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) :
    fpT (mag_pma_check pma access paddr width) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpPmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) :
    fpT (pmpCheck addr width access priv) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpPmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) :
    fpT (pmaCheck paddr width access pbmt res_or_con) := by
  fp_walk

set_option maxHeartbeats 40000000 in
@[fp_reg] theorem fpEffectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) :
    fpT (effectivePrivilege access m priv) := by
  fp_walk


set_option maxHeartbeats 8000000 in
@[fp_reg] theorem fpCheckedMemRead (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ())
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    fpT (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  fp_walk
  all_goals simp_all


theorem ptMeasure (level : Nat) (b c : Bool)
    (h : Bool.and b (Bool.and c (decide (level > 0))) = true) :
    ((level : Int) - 1).toNat < level := by
  have : level > 0 := by cases b <;> cases c <;> simp_all [Bool.and]
  omega

set_option maxHeartbeats 8000000 in
@[fp_reg] theorem fpPtWalk (sv : Nat) (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) :
    ∀ (level : Nat) (base : BitVec (if (sv = 32 : Bool) then 22 else 44)) (g : Bool) (ext : Unit),
      fpT (pt_walk sv vpn acc priv mxr sum base level g ext) := by
  intro level
  induction level using Nat.strongRecOn with
  | ind level ih =>
    intro base g ext
    rw [pt_walk]
    fp_walk
    all_goals (apply SailCycleOrderFp.ptMeasure; assumption)

set_option maxHeartbeats 8000000 in
@[fp_reg] theorem fpTranslateAddr (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    fpT (translateAddr va acc) := by
  fp_walk

end SailCycleOrderFp
end Weak

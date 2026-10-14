/-
Weak: **W9a (B) B5 cycRun — `pfB` footprints of the memory pieces** (the `pfB` twins of B1's
`Weak/PinDataflowMem.lean`, walked by `pf_walk`): the read kind, `read_ram` off `Read_ifetch`,
`rX`/`rX_bits`, the extension cluster, the access checks, PMP/PMA, the page-table walk `pt_walk`
(induction on the level) and `translateAddr`: none of them writes a protected register
(`pfProt`).  Lean-only.
-/
import Weak.PinCycRunFp
import Weak.PinDataflowMem
import Weak.SailCycleOrderAllMem

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinCycRunFp
open SailCycleOrderK

@[pf_reg] theorem pfReadKindOfFlags (aq rl res : Bool) :
    pf (fun rk => rk ≠ .Read_ifetch) (read_kind_of_flags aq rl res) := by
  unfold read_kind_of_flags; split <;> first | trivial | (intro h; cases h)


set_option maxHeartbeats 4000000 in
@[pf_reg] theorem pfReadRam (rk : read_kind) (h : rk ≠ .Read_ifetch) (pa : physaddr) (w : Nat) (m : Bool) :
    pfT (read_ram rk pa w m) := by
  pf_walk


set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfRX (app_0 : regno) :
    pfT (rX app_0) := by
  pf_walk


set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfRXBits (app_0 : regidx) :
    pfT (rX_bits app_0) := by
  pf_walk



set_option maxHeartbeats 8000000 in
@[pf_reg] theorem pfCurrentlyEnabled (e : extension) : pfT (currentlyEnabled e) := by
  cases e <;> pf_walk


set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfAccessFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    pfT (accessFaultFromAccessType access) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfAlignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    pfT (alignmentFaultFromAccessType access) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfTranslationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) :
    pfT (translationException access err) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfIsShadowStackAccess (access : (MemoryAccessType mem_payload)) :
    pfT (is_shadow_stack_access access) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfCheckPTEPermission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (a5_0 : (BitVec 10)) (a6_0 : Unit) :
    pfT (check_PTE_permission access priv mxr do_sum pte_flags a5_0 a6_0) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfPmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) :
    pfT (pmpCheckRWX ent access) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfIsMagApplicableAccess (access : (MemoryAccessType mem_payload)) (width : Nat) :
    pfT (is_mag_applicable_access access width) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfPmaMisalignedException (pma : PMA) (access : (MemoryAccessType mem_payload)) :
    pfT (pma_misaligned_exception pma access) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfMagPmaCheck (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) :
    pfT (mag_pma_check pma access paddr width) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfPmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) :
    pfT (pmpCheck addr width access priv) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfPmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) :
    pfT (pmaCheck paddr width access pbmt res_or_con) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfEffectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) :
    pfT (effectivePrivilege access m priv) := by
  pf_walk


set_option maxHeartbeats 8000000 in
@[pf_reg] theorem pfCheckedMemRead (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ())
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    pfT (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  pf_walk
  all_goals simp_all


set_option maxHeartbeats 8000000 in
@[pf_reg] theorem pfPtWalk (sv : Nat) (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) :
    ∀ (level : Nat) (base : BitVec (if (sv = 32 : Bool) then 22 else 44)) (g : Bool) (ext : Unit),
      pfT (pt_walk sv vpn acc priv mxr sum base level g ext) := by
  intro level
  induction level using Nat.strongRecOn with
  | ind level ih =>
    intro base g ext
    rw [pt_walk]
    pf_walk
    all_goals (apply SailCycleOrderFp.ptMeasure; assumption)

set_option maxHeartbeats 8000000 in
@[pf_reg] theorem pfTranslateAddr (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    pfT (translateAddr va acc) := by
  pf_walk

/-! ## Value posts: a failing access answers a TRAP (`jump_to` writes `nextPC`, protected: it has
no `pfB` twin) -/

/-- A trap result. -/
def isTrapR (r : ExecutionResult) : Bool :=
  match r with
  | .Trap _ => true
  | _ => false

/-- A data access's result: a value, or a trap. -/
@[reducible] def resTrap {α : Type} (res : Result α ExecutionResult) : Prop :=
  match res with
  | .Err e => isTrapR e = true
  | .Ok _ => True

set_option maxHeartbeats 4000000 in
@[pf_reg] theorem pfMemoryException (va : virtaddr) (e : ExceptionType) :
    pf (fun r => isTrapR r = true) (memory_exception va e) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfTranslateAndReadValue (va : virtaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ()) (aq rl res : Bool) :
    pf resTrap (translate_and_read_value va w acc aq rl res) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfVmemReadAddr (va : virtaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ()) (aq rl res : Bool) :
    pf resTrap (vmem_read_addr va w acc aq rl res) := by
  pf_walk_v


end PinCycRunFp
end Weak

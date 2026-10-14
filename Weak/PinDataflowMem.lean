/-
Weak: **W9a (B) B1 — `nwB` footprints of the memory pieces** (the `nwB` twins of W-SCO's
`Weak/SailCycleOrderAllMem.lean`, walked by `nw_walk`): the read kind, `read_ram` off `Read_ifetch`,
`rX`/`rX_bits` (a GPR READ is neutral; `wX` is not, so it has no twin), the extension and stateen
cluster, the access checks, PMP/PMA, the page-table walk `pt_walk` (induction on the level) and
`translateAddr`: none of them writes a register with a dependency number.  Lean-only.
-/
import Weak.PinDataflowDf
import Weak.SailCycleOrderAllMem

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace PinDataflow
open SailCycleOrderK

@[nw_reg] theorem nwReadKindOfFlags (aq rl res : Bool) :
    nw (fun rk => rk ≠ .Read_ifetch) (read_kind_of_flags aq rl res) := by
  unfold read_kind_of_flags; split <;> first | trivial | (intro h; cases h)


set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwReadRam (rk : read_kind) (h : rk ≠ .Read_ifetch) (pa : physaddr) (w : Nat) (m : Bool) :
    nwT (read_ram rk pa w m) := by
  nw_walk


set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwRX (app_0 : regno) :
    nwT (rX app_0) := by
  nw_walk


set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwRXBits (app_0 : regidx) :
    nwT (rX_bits app_0) := by
  nw_walk



set_option maxHeartbeats 8000000 in
@[nw_reg] theorem nwCurrentlyEnabled (e : extension) : nwT (currentlyEnabled e) := by
  cases e <;> nw_walk


set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwAccessFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    nwT (accessFaultFromAccessType access) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwAlignmentFaultFromAccessType (access : (MemoryAccessType mem_payload)) :
    nwT (alignmentFaultFromAccessType access) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwTranslationException (access : (MemoryAccessType mem_payload)) (err : PTW_Error) :
    nwT (translationException access err) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwIsShadowStackAccess (access : (MemoryAccessType mem_payload)) :
    nwT (is_shadow_stack_access access) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwCheckPTEPermission (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte_flags : (BitVec 8)) (a5_0 : (BitVec 10)) (a6_0 : Unit) :
    nwT (check_PTE_permission access priv mxr do_sum pte_flags a5_0 a6_0) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwPmpCheckRWX (ent : (BitVec 8)) (access : (MemoryAccessType mem_payload)) :
    nwT (pmpCheckRWX ent access) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwIsMagApplicableAccess (access : (MemoryAccessType mem_payload)) (width : Nat) :
    nwT (is_mag_applicable_access access width) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwPmaMisalignedException (pma : PMA) (access : (MemoryAccessType mem_payload)) :
    nwT (pma_misaligned_exception pma access) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwMagPmaCheck (pma : PMA) (access : (MemoryAccessType mem_payload)) (paddr : physaddr) (width : Nat) :
    nwT (mag_pma_check pma access paddr width) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwPmpCheck (addr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (priv : Privilege) :
    nwT (pmpCheck addr width access priv) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwPmaCheck (paddr : physaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (pbmt : page_based_mem_type) (res_or_con : Bool) :
    nwT (pmaCheck paddr width access pbmt res_or_con) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwEffectivePrivilege (access : (MemoryAccessType mem_payload)) (m : (BitVec 64)) (priv : Privilege) :
    nwT (effectivePrivilege access m priv) := by
  nw_walk


set_option maxHeartbeats 8000000 in
@[nw_reg] theorem nwCheckedMemRead (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ())
    (pbmt : page_based_mem_type) (priv : Privilege) (pa : physaddr) (w : Nat) (aq rl res m : Bool) :
    nwT (checked_mem_read acc pbmt priv pa w aq rl res m) := by
  nw_walk
  all_goals simp_all


set_option maxHeartbeats 8000000 in
@[nw_reg] theorem nwPtWalk (sv : Nat) (vpn : BitVec (sv - 12)) (acc : MemoryAccessType mem_payload)
    (priv : Privilege) (mxr sum : Bool) :
    ∀ (level : Nat) (base : BitVec (if (sv = 32 : Bool) then 22 else 44)) (g : Bool) (ext : Unit),
      nwT (pt_walk sv vpn acc priv mxr sum base level g ext) := by
  intro level
  induction level using Nat.strongRecOn with
  | ind level ih =>
    intro base g ext
    rw [pt_walk]
    nw_walk
    all_goals (apply SailCycleOrderFp.ptMeasure; assumption)

set_option maxHeartbeats 8000000 in
@[nw_reg] theorem nwTranslateAddr (va : virtaddr) (acc : MemoryAccessType mem_payload) :
    nwT (translateAddr va acc) := by
  nw_walk

/-! ## Value posts: a failing access never answers a retirement or a redirect -/

/-- A FAILURE result: neither a retirement nor an `ExecuteAs` redirect. -/
def failRes (r : ExecutionResult) : Bool :=
  match r with
  | .Retire_Success _ => false
  | .ExecuteAs _ => false
  | _ => true

/-- A `Result` whose error payload is a failure (reducible: the walker reads it at a leaf). -/
@[reducible] def resFail {α : Type} (res : Result α ExecutionResult) : Prop :=
  match res with
  | .Err e => failRes e = true
  | .Ok _ => True

set_option maxHeartbeats 4000000 in
@[nw_reg] theorem nwMemoryException (va : virtaddr) (e : ExceptionType) :
    nw (fun r => failRes r = true) (memory_exception va e) := by
  nw_walk

/-- A retirement or a failure (never a redirect). -/
@[reducible] def retOrFail (r : ExecutionResult) : Prop := failRes r = true ∨ r = RETIRE_SUCCESS

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwJumpTo (t : BitVec 64) : nw retOrFail (jump_to t) := by
  nw_walk_v

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwTranslateAndReadValue (va : virtaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ()) (aq rl res : Bool) :
    nw resFail (translate_and_read_value va w acc aq rl res) := by
  nw_walk_v

set_option maxHeartbeats 40000000 in
@[nw_reg] theorem nwVmemReadAddr (va : virtaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ()) (aq rl res : Bool) :
    nw resFail (vmem_read_addr va w acc aq rl res) := by
  nw_walk_v


end PinDataflow
end Weak

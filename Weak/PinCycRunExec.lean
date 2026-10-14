/-
Weak: **W9a (B) B5 cycRun — the execute stage, part 1: the register-only and memory classes**
([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

The PLAIN class (`plainC`): every base ALU, multiply/divide, load and store AST and every
compressed AST that redirects (`ExecuteAs`, `InstsEnd.lean:18452-18600`) to one.  Its execute
stage, through the one redirect (`uxaExecAs`), writes no protected register (`pfB`) and answers
`RETIRE_SUCCESS`, or a TRAP at a load/store (`memory_exception` → `trap`, `InstsBegin.lean:213`)
— walked by `pf_walk_v` over the `pfB` registry (`Weak/PinCycRunMem.lean`).

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunTab

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pf pfT pfProt pfRegOk pfW isTrapR resTrap)

/-! ## 1. The memory paths with a trap post -/

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfVmemReadT (rs : regidx) (off : BitVec 64) (w : Nat)
    (acc : MemoryAccessType mem_payload) (h : acc ≠ .InstructionFetch ()) (aq rl res : Bool) :
    pf resTrap (vmem_read rs off w acc aq rl res) := by
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfMemWriteEa (pa : physaddr) (w : Nat) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (aq rl res : Bool) :
    pfT (mem_write_ea pa w acc pbmt aq rl res) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfMemWriteValue (pa : physaddr) (w : Nat) (v : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (aq rl res : Bool) :
    pfT (mem_write_value pa w v acc pbmt aq rl res) := by
  pf_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfTranslateAndWriteValueT (va : virtaddr) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (aq rl res : Bool) :
    pf resTrap (translate_and_write_value va w data acc aq rl res) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfVmemWriteAddrT (va : virtaddr) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (aq rl res : Bool) :
    pf resTrap (vmem_write_addr va w data acc aq rl res) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfVmemWriteT (rs : regidx) (off : BitVec 64) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (aq rl res : Bool) :
    pf resTrap (vmem_write rs off w data acc aq rl res) := by
  unfold vmem_write get_transformed_data_addr ext_data_get_addr
  pf_walk_v

/-! ## 2. The plain class -/

/-- The PLAIN class: base ALU / multiply / divide / load / store ASTs and the compressed ASTs that
redirect to one. -/
def plainC (c : instruction) : Bool :=
  match c with
  | .UTYPE _ | .ITYPE _ | .SHIFTIOP _ | .RTYPE _ | .LOAD _ | .STORE _ | .ADDIW _ | .RTYPEW _
  | .SHIFTIWOP _ | .MUL _ | .DIV _ | .REM _ | .MULW _ | .DIVW _ | .REMW _
  | .C_NOP _ | .C_ADDI4SPN _ | .C_LW _ | .C_LD _ | .C_SW _ | .C_SD _ | .C_ADDI _ | .C_ADDIW _
  | .C_LI _ | .C_ADDI16SP _ | .C_LUI _ | .C_SRLI _ | .C_SRAI _ | .C_ANDI _ | .C_SUB _ | .C_XOR _
  | .C_OR _ | .C_AND _ | .C_SUBW _ | .C_ADDW _ | .C_SLLI _ | .C_LWSP _ | .C_LDSP _ | .C_SWSP _
  | .C_SDSP _ | .C_MV _ | .C_ADD _ => true
  | _ => false

/-- A retirement, or a trap at a load/store. -/
@[reducible] def plainPost (c : instruction) (r : ExecutionResult) : Prop :=
  r = RETIRE_SUCCESS ∨ (memC c = true ∧ isTrapR r = true)

/-! ## 2. The base clauses -/

/-- A retirement or a trap. -/
@[reducible] def retTrap (r : ExecutionResult) : Prop := r = RETIRE_SUCCESS ∨ isTrapR r = true

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecItype (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_ITYPE imm rs1 rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecShiftiop (sh : BitVec 6) (rs1 rd : regidx) (op : sop) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_SHIFTIOP sh rs1 rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecRtype (rs2 rs1 rd : regidx) (op : rop) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_RTYPE rs2 rs1 rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecAddiw (imm : BitVec 12) (rs1 rd : regidx) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_ADDIW imm rs1 rd) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecRtypew (rs2 rs1 rd : regidx) (op : ropw) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_RTYPEW rs2 rs1 rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecShiftiwop (sh : BitVec 5) (rs1 rd : regidx) (op : sopw) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_SHIFTIWOP sh rs1 rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecUtype (imm : BitVec 20) (rd : regidx) (op : uop) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_UTYPE imm rd op) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecMul (rs2 rs1 rd : regidx) (mo : mul_op) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_MUL rs2 rs1 rd mo) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecDiv (rs2 rs1 rd : regidx) (u : Bool) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_DIV rs2 rs1 rd u) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecRem (rs2 rs1 rd : regidx) (u : Bool) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_REM rs2 rs1 rd u) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecMulw (rs2 rs1 rd : regidx) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_MULW rs2 rs1 rd) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecDivw (rs2 rs1 rd : regidx) (u : Bool) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_DIVW rs2 rs1 rd u) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecRemw (rs2 rs1 rd : regidx) (u : Bool) :
    pf (fun r => r = RETIRE_SUCCESS) (execute_REMW rs2 rs1 rd u) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecLoad (imm : BitVec 12) (rs1 rd : regidx) (u : Bool) (w : Nat) :
    pf retTrap (execute_LOAD imm rs1 rd u w) := by
  pf_walk_v

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExecStore (imm : BitVec 12) (rs2 rs1 : regidx) (w : Nat) :
    pf retTrap (execute_STORE imm rs2 rs1 w) := by
  pf_walk_v

/-! ## 3. Through the one redirect -/

/-- An `ExecuteAs` redirect. -/
def isExecAsR (r : ExecutionResult) : Bool :=
  match r with
  | .ExecuteAs _ => true
  | _ => false

/-- `uxaExecAs` of an instruction whose `execute` does not redirect. -/
theorem pfUxaOf (c : instruction) (P : ExecutionResult → Prop)
    (h : pf (fun r => P r ∧ isExecAsR r = false) (execute c)) : pf P (uxaExecAs c) := by
  unfold uxaExecAs
  refine PinCycRunFp.pfBBindQ false _ _ _ _ h (fun r hr => ?_)
  cases r
  case ExecuteAs i => exact absurd hr.2 (by simp [isExecAsR])
  all_goals exact hr.1

theorem PinCycRun.plainOfRet (c : instruction) (r : ExecutionResult) (h : r = RETIRE_SUCCESS) :
    plainPost c r ∧ isExecAsR r = false := by
  subst h; exact ⟨Or.inl rfl, rfl⟩

theorem PinCycRun.plainOfRetTrap (c : instruction) (hm : memC c = true) (r : ExecutionResult)
    (h : retTrap r) : plainPost c r ∧ isExecAsR r = false := by
  rcases h with rfl | h
  · exact ⟨Or.inl rfl, rfl⟩
  · refine ⟨Or.inr ⟨hm, h⟩, ?_⟩
    cases r <;> simp_all [isTrapR, isExecAsR]

/-- A base instruction that retires. -/
theorem pfUxaBaseRet (c : instruction) (h : pf (fun r => r = RETIRE_SUCCESS) (execute c)) :
    pf (plainPost c) (uxaExecAs c) :=
  pfUxaOf c _ (PinCycRunFp.pfBMono false false (Or.inl rfl) _ _ (PinCycRun.plainOfRet c) _ h)

/-- A base load/store. -/
theorem pfUxaBaseMem (c : instruction) (hm : memC c = true) (h : pf retTrap (execute c)) :
    pf (plainPost c) (uxaExecAs c) :=
  pfUxaOf c _ (PinCycRunFp.pfBMono false false (Or.inl rfl) _ _ (PinCycRun.plainOfRetTrap c hm) _ h)

/-- A compressed instruction redirecting to a base one that retires. -/
theorem pfUxaRedirRet (c b : instruction) (he : execute c = pure (.ExecuteAs b))
    (h : pf (fun r => r = RETIRE_SUCCESS) (execute b)) : pf (plainPost c) (uxaExecAs c) := by
  unfold uxaExecAs
  rw [he]
  exact PinCycRunFp.pfBMono false false (Or.inl rfl) _ _ (fun r hr => Or.inl hr) _ h

/-- A compressed load/store. -/
theorem pfUxaRedirMem (c b : instruction) (he : execute c = pure (.ExecuteAs b))
    (hm : memC c = true) (h : pf retTrap (execute b)) : pf (plainPost c) (uxaExecAs c) := by
  unfold uxaExecAs
  rw [he]
  refine PinCycRunFp.pfBMono false false (Or.inl rfl) _ _ (fun r hr => ?_) _ h
  rcases hr with hr | hr
  · exact Or.inl hr
  · exact Or.inr ⟨hm, hr⟩

set_option maxHeartbeats 4000000 in
/-- **THE PLAIN CLASS'S EXECUTE STAGE** (header). -/
theorem pfUxaPlain (c : instruction) (hc : plainC c = true) :
    pf (plainPost c) (uxaExecAs c) := by
  cases c with
  | UTYPE x => exact pfUxaBaseRet _ (pfExecUtype ..)
  | ITYPE x => exact pfUxaBaseRet _ (pfExecItype ..)
  | SHIFTIOP x => exact pfUxaBaseRet _ (pfExecShiftiop ..)
  | RTYPE x => exact pfUxaBaseRet _ (pfExecRtype ..)
  | ADDIW x => exact pfUxaBaseRet _ (pfExecAddiw ..)
  | RTYPEW x => exact pfUxaBaseRet _ (pfExecRtypew ..)
  | SHIFTIWOP x => exact pfUxaBaseRet _ (pfExecShiftiwop ..)
  | MUL x => exact pfUxaBaseRet _ (pfExecMul ..)
  | DIV x => exact pfUxaBaseRet _ (pfExecDiv ..)
  | REM x => exact pfUxaBaseRet _ (pfExecRem ..)
  | MULW x => exact pfUxaBaseRet _ (pfExecMulw ..)
  | DIVW x => exact pfUxaBaseRet _ (pfExecDivw ..)
  | REMW x => exact pfUxaBaseRet _ (pfExecRemw ..)
  | LOAD x => exact pfUxaBaseMem _ rfl (pfExecLoad ..)
  | STORE x => exact pfUxaBaseMem _ rfl (pfExecStore ..)
  | C_ADDI4SPN x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecItype ..)
  | C_LW x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecLoad ..)
  | C_LD x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecLoad ..)
  | C_SW x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecStore ..)
  | C_SD x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecStore ..)
  | C_ADDI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecItype ..)
  | C_ADDIW x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecAddiw ..)
  | C_LI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecItype ..)
  | C_ADDI16SP x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecItype ..)
  | C_LUI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecUtype ..)
  | C_SRLI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecShiftiop ..)
  | C_SRAI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecShiftiop ..)
  | C_ANDI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecItype ..)
  | C_SUB x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_XOR x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_OR x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_AND x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_SUBW x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtypew ..)
  | C_ADDW x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtypew ..)
  | C_SLLI x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecShiftiop ..)
  | C_LWSP x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecLoad ..)
  | C_LDSP x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecLoad ..)
  | C_SWSP x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecStore ..)
  | C_SDSP x => exact pfUxaRedirMem _ _ rfl rfl (by simp only [execute]; exact pfExecStore ..)
  | C_MV x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_ADD x => exact pfUxaRedirRet _ _ rfl (by simp only [execute]; exact pfExecRtype ..)
  | C_NOP x => exact (Or.inl rfl : plainPost (.C_NOP x) RETIRE_SUCCESS)
  | _ => exact absurd hc (by simp [plainC])

end PinCycRun
end Weak

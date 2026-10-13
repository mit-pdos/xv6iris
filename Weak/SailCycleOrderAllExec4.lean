/-
Weak: **W-SCO (A) — the per-clause footprints, part 4** (plan rev 36 §C W-SCO (A) (1)(b)): one
lemma per `execute_*` clause of `model/Lean_RV64D/LeanRV64D/InstsEnd.lean` (symbolic in its
operands), each by the walker over the registered helpers.  `execute_FENCEI` (the one
`Barrier_RISCV_i`) is handled by hand in `Weak/SailCycleOrderCycle.lean`.  Lean-only.
-/
import Weak.SailCycleOrderAllCsr

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZicboz (rs1 : regidx) :
    fpT (execute_ZICBOZ rs1) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbsRtype (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbs) :
    fpT (execute_ZBS_RTYPE rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbbExtop (rs1 : regidx) (rd : regidx) (op : extop_zbb) :
    fpT (execute_ZBB_EXTOP rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecWfi (a0 : Unit) :
    fpT (execute_WFI a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSsrdp (rd : regidx) :
    fpT (execute_SSRDP rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSret (a0 : Unit) :
    fpT (execute_SRET a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecShiftiop (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) :
    fpT (execute_SHIFTIOP shamt rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRtypew (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) :
    fpT (execute_RTYPEW rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRev8 (rs1 : regidx) (rd : regidx) :
    fpT (execute_REV8 rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecOrcb (rs1 : regidx) (rd : regidx) :
    fpT (execute_ORCB rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecMret (a0 : Unit) :
    fpT (execute_MRET a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecJalr (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    fpT (execute_JALR imm rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecFenceTso (a0 : Unit) :
    fpT (execute_FENCE_TSO a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecDivw (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) :
    fpT (execute_DIVW rs2 rs1 rd is_unsigned) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCZextB (rsdc : cregidx) :
    fpT (execute_C_ZEXT_B rsdc) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSubw (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_SUBW rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSrli (shamt : (BitVec 6)) (rsd : cregidx) :
    fpT (pure (execute_C_SRLI shamt rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSextH (rsdc : cregidx) :
    fpT (pure (execute_C_SEXT_H rsdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSb (uimm : (BitVec 2)) (rsc1 : cregidx) (rsc2 : cregidx) :
    fpT (pure (execute_C_SB uimm rsc1 rsc2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCNop (g__189 : (BitVec 6)) :
    fpT (pure (execute_C_NOP g__189) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLw (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) :
    fpT (pure (execute_C_LW uimm rsc rdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLh (uimm : (BitVec 2)) (rdc : cregidx) (rsc1 : cregidx) :
    fpT (pure (execute_C_LH uimm rdc rsc1) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCJr (rs1 : regidx) :
    fpT (pure (execute_C_JR rs1) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCIllegal (a0 : (BitVec 16)) :
    fpT (pure (execute_C_ILLEGAL a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAndi (imm : (BitVec 6)) (rsd : cregidx) :
    fpT (pure (execute_C_ANDI imm rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAddi4spn (rdc : cregidx) (nzimm : (BitVec 8)) :
    fpT (pure (execute_C_ADDI4SPN rdc nzimm) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCtzw (rs1 : regidx) (rd : regidx) :
    fpT (execute_CTZW rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCpopw (rs1 : regidx) (rd : regidx) :
    fpT (execute_CPOPW rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecClmulr (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    fpT (execute_CLMULR rs2 rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecAmo (op : amoop) (aq : Bool) (rl : Bool) (rs2 : regidx) (rs1 : regidx) (width : Nat) (rd : regidx) :
    fpT (execute_AMO op aq rl rs2 rs1 width rd) := by
  fp_walk

end SailCycleOrderFp
end Weak

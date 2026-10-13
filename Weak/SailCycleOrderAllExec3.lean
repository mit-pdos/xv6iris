/-
Weak: **W-SCO (A) — the per-clause footprints, part 3** (plan rev 36 §C W-SCO (A) (1)(b)): one
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
@[fp_reg] theorem fpExecZicondRtype (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : zicondop) :
    fpT (execute_ZICOND_RTYPE rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecZcmop (a0 : (BitVec 3)) :
    fpT (pure (execute_ZCMOP a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbbRtype (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbb) :
    fpT (execute_ZBB_RTYPE rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecWrs (merge_var : wrsop) :
    fpT (pure (execute_WRS merge_var) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecStore (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) :
    fpT (execute_STORE imm rs2 rs1 width) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSsamoswap (aq : Bool) (rl : Bool) (rs2 : regidx) (rs1 : regidx) (width : Nat) (rd : regidx) :
    fpT (execute_SSAMOSWAP aq rl rs2 rs1 width rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecShiftiwop (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) :
    fpT (execute_SHIFTIWOP shamt rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSfenceInvalIr (a0 : Unit) :
    fpT (execute_SFENCE_INVAL_IR a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRori (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) :
    fpT (execute_RORI shamt rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecPause (a0 : Unit) :
    fpT (pure (execute_PAUSE a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecMul (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) :
    fpT (execute_MUL rs2 rs1 rd mul_op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecLoad (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) :
    fpT (execute_LOAD imm rs1 rd is_unsigned width) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecIllegal (a0 : (BitVec 32)) :
    fpT (pure (execute_ILLEGAL a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecEbreak (a0 : Unit) :
    fpT (execute_EBREAK a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCZextH (rsdc : cregidx) :
    fpT (pure (execute_C_ZEXT_H rsdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSw (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) :
    fpT (pure (execute_C_SW uimm rsc1 rsc2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSspopchk (a0 : Unit) :
    fpT (pure (execute_C_SSPOPCHK a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSh (uimm : (BitVec 2)) (rsc1 : cregidx) (rsc2 : cregidx) :
    fpT (pure (execute_C_SH uimm rsc1 rsc2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSd (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) :
    fpT (pure (execute_C_SD uimm rsc1 rsc2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCNot (rsdc : cregidx) :
    fpT (execute_C_NOT rsdc) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLwsp (uimm : (BitVec 6)) (rd : regidx) :
    fpT (pure (execute_C_LWSP uimm rd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLhu (uimm : (BitVec 2)) (rdc : cregidx) (rsc1 : cregidx) :
    fpT (pure (execute_C_LHU uimm rdc rsc1) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLbu (uimm : (BitVec 2)) (rdc : cregidx) (rsc1 : cregidx) :
    fpT (pure (execute_C_LBU uimm rdc rsc1) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCJ (imm : (BitVec 11)) :
    fpT (pure (execute_C_J imm) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCBeqz (imm : (BitVec 8)) (rs : cregidx) :
    fpT (pure (execute_C_BEQZ imm rs) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAddiw (imm : (BitVec 6)) (rsd : regidx) :
    fpT (pure (execute_C_ADDIW imm rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAdd (rsd : regidx) (rs2 : regidx) :
    fpT (pure (execute_C_ADD rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCsrimm (csr : (BitVec 12)) (imm : (BitVec 5)) (rd : regidx) (op : csrop) :
    fpT (execute_CSRImm csr imm rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecClz (rs1 : regidx) (rd : regidx) :
    fpT (execute_CLZ rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecBtype (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) :
    fpT (execute_BTYPE imm rs2 rs1 op) := by
  fp_walk

end SailCycleOrderFp
end Weak

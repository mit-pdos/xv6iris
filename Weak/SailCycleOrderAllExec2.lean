/-
Weak: **W-SCO (A) — the per-clause footprints, part 2** (plan rev 36 §C W-SCO (A) (1)(b)): one
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
@[fp_reg] theorem fpExecZimopMopR (a0 : (BitVec 5)) (a1 : regidx) (rd : regidx) :
    fpT (execute_ZIMOP_MOP_R a0 a1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZicbom (arg0 : cbop_zicbom) (arg1 : regidx) :
    fpT (execute_ZICBOM arg0 arg1) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbbRtypew (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : bropw_zbb) :
    fpT (execute_ZBB_RTYPEW rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbaRtype (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : (BitVec 2)) :
    fpT (execute_ZBA_RTYPE rs2 rs1 rd shamt) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecStorecon (aq : Bool) (rl : Bool) (rs2 : regidx) (rs1 : regidx) (width : Nat) (rd : regidx) :
    fpT (execute_STORECON aq rl rs2 rs1 width rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSspopchk (rs1 : regidx) :
    fpT (execute_SSPOPCHK rs1) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecSinvalVma (rs1 : regidx) (rs2 : regidx) :
    fpT (pure (execute_SINVAL_VMA rs1 rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSfenceVma (rs1 : regidx) (rs2 : regidx) :
    fpT (execute_SFENCE_VMA rs1 rs2) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRoriw (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) :
    fpT (execute_RORIW shamt rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRem (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) :
    fpT (execute_REM rs2 rs1 rd is_unsigned) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecMulw (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    fpT (execute_MULW rs2 rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecLoadres (aq : Bool) (rl : Bool) (rs1 : regidx) (width : Nat) (rd : regidx) :
    fpT (execute_LOADRES aq rl rs1 width rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecItype (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) :
    fpT (execute_ITYPE imm rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecEcall (a0 : Unit) :
    fpT (execute_ECALL a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCZextW (rsdc : cregidx) :
    fpT (pure (execute_C_ZEXT_W rsdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSwsp (uimm : (BitVec 6)) (rs2 : regidx) :
    fpT (pure (execute_C_SWSP uimm rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSspush (a0 : Unit) :
    fpT (pure (execute_C_SSPUSH a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSlli (shamt : (BitVec 6)) (rsd : regidx) :
    fpT (pure (execute_C_SLLI shamt rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSdsp (uimm : (BitVec 6)) (rs2 : regidx) :
    fpT (pure (execute_C_SDSP uimm rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCNtl (g__188 : ntl_type) :
    fpT (pure (execute_C_NTL g__188) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCMul (rsdc : cregidx) (rsc2 : cregidx) :
    fpT (pure (execute_C_MUL rsdc rsc2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLi (imm : (BitVec 6)) (rd : regidx) :
    fpT (pure (execute_C_LI imm rd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLd (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) :
    fpT (pure (execute_C_LD uimm rsc rdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCJal (imm : (BitVec 11)) :
    fpT (pure (execute_C_JAL imm) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCBnez (imm : (BitVec 8)) (rs : cregidx) :
    fpT (pure (execute_C_BNEZ imm rs) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAddw (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_ADDW rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAddi (imm : (BitVec 6)) (rsd : regidx) :
    fpT (pure (execute_C_ADDI imm rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCsrreg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) :
    fpT (execute_CSRReg csr rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecClzw (rs1 : regidx) (rd : regidx) :
    fpT (execute_CLZW rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecClmul (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    fpT (execute_CLMUL rs2 rs1 rd) := by
  fp_walk

end SailCycleOrderFp
end Weak

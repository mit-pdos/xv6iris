/-
Weak: **W-SCO (A) — the per-clause footprints, part 1** (plan rev 36 §C W-SCO (A) (1)(b)): one
lemma per `execute_*` clause of `model/Lean_RV64D/LeanRV64D/InstsEnd.lean` (symbolic in its
operands), each by the walker over the registered helpers.  `execute_FENCEI` (the one
`Barrier_RISCV_i`) is handled in `Weak/SailCycleOrderExecG.lean` (`gExecute`).  Lean-only.
-/
import Weak.SailCycleOrderAllCsr

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZimopMopRr (a0 : (BitVec 3)) (a1 : regidx) (a2 : regidx) (rd : regidx) :
    fpT (execute_ZIMOP_MOP_RR a0 a1 a2 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZicbop (cbop : cbop_zicbop) (rs1 : regidx) (offset : (BitVec 12)) :
    fpT (execute_ZICBOP cbop rs1 offset) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbsIop (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : biop_zbs) :
    fpT (execute_ZBS_IOP shamt rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecZbaRtypeuw (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : (BitVec 2)) :
    fpT (execute_ZBA_RTYPEUW rs2 rs1 rd shamt) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecUtype (imm : (BitVec 20)) (rd : regidx) (op : uop) :
    fpT (execute_UTYPE imm rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSspush (rs2 : regidx) :
    fpT (execute_SSPUSH rs2) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSlliuw (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) :
    fpT (execute_SLLIUW shamt rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecSfenceWInval (a0 : Unit) :
    fpT (execute_SFENCE_W_INVAL a0) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRtype (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) :
    fpT (execute_RTYPE rs2 rs1 rd op) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecRemw (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) :
    fpT (execute_REMW rs2 rs1 rd is_unsigned) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecNtl (g__187 : ntl_type) :
    fpT (pure (execute_NTL g__187) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecLpad (lpl : (BitVec 20)) :
    fpT (execute_LPAD lpl) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecJal (imm : (BitVec 21)) (rd : regidx) :
    fpT (execute_JAL imm rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecFence (a0 : (BitVec 4)) (pred : (BitVec 4)) (succ : (BitVec 4)) (a3 : regidx) (a4 : regidx) :
    fpT (execute_FENCE a0 pred succ a3 a4) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecDiv (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) :
    fpT (execute_DIV rs2 rs1 rd is_unsigned) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCXor (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_XOR rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSub (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_SUB rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSrai (shamt : (BitVec 6)) (rsd : cregidx) :
    fpT (pure (execute_C_SRAI shamt rsd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCSextB (rsdc : cregidx) :
    fpT (pure (execute_C_SEXT_B rsdc) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCOr (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_OR rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCMv (rd : regidx) (rs2 : regidx) :
    fpT (pure (execute_C_MV rd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLui (imm : (BitVec 6)) (rd : regidx) :
    fpT (pure (execute_C_LUI imm rd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCLdsp (uimm : (BitVec 6)) (rd : regidx) :
    fpT (pure (execute_C_LDSP uimm rd) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCJalr (rs1 : regidx) :
    fpT (pure (execute_C_JALR rs1) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCEbreak (a0 : Unit) :
    fpT (pure (execute_C_EBREAK a0) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAnd (rsd : cregidx) (rs2 : cregidx) :
    fpT (pure (execute_C_AND rsd rs2) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
theorem fpExecCAddi16sp (imm : (BitVec 6)) :
    fpT (pure (execute_C_ADDI16SP imm) : SailM ExecutionResult) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCtz (rs1 : regidx) (rd : regidx) :
    fpT (execute_CTZ rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecCpop (rs1 : regidx) (rd : regidx) :
    fpT (execute_CPOP rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecClmulh (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    fpT (execute_CLMULH rs2 rs1 rd) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpExecAddiw (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    fpT (execute_ADDIW imm rs1 rd) := by
  fp_walk

end SailCycleOrderFp
end Weak

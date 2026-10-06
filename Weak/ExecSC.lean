/-
Weak: the exec-level GPR and register-only ALU facts, and the compressed
redirects (the first of the `Weak/ExecSC*.lean` files: Rocq's SC `exec_*` library
the weak tier uses, ported onto `Weak.exec`).

Rocq: `iris/WpGpr.v`, `iris/WpMmodeLeafBase.v` (the GPR/ALU/compressed part),
`iris/WpMmodeShiftiop.v`, `iris/RiscvExtras.v` (`auipc_off`) @ xxvzwolszwmp.

**Conventions (all `Weak/ExecSC*.lean` files; the deviations every statement shares).**
Statements are about `Weak.exec` over the LEAN model (sail-riscv `070832a1`,
`-D SYMBOLIC`: announce events silent), not Rocq's `exec` over the Coq model.
* GPRs: Rocq `if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64
  (gpr_of_Z (uint i))) s.(sregs)` ↦ `s.gpr i`; Rocq `if uint rd =? 0 then s else
  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦
  `s.setGpr rd v` (`Weak/ExecSC.lean`).  Where Rocq has a `uint rd ≠ 0` premise and a
  plain `set_reg`, the premise is kept and the result is `setGpr` (equal under it).
* Spelling: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
  `(x == 1#1) = b`; `vec_access_dec v i` ↦ `v[i]!`; `vec_update_dec v i x` ↦
  `vectorUpdate v i x`; `uint x` ↦ `x.toNat`; `Z` widths/indices ↦ `Nat`;
  `mword n` ↦ `BitVec n`; `tt` ↦ `()`; `zeros' n` ↦ `zeros (n := n)`.
* Memory: `dev_addr pa = false` ↦ `devAddr pa = false`; Rocq's byte window
  `∀ j < n, s.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt s pa n w`;
  `MState s.(sregs) (write_bytes s.(mem) pa n v) s.(mdev)` ↦
  `s.setMem (bmWrite s.mem pa n v)`.  An ifetch is a RAM read in `exec`
  (`Weak/Exec.lean`), so the fetch facts read the byte map (`AK_ifetch` plays no role).
* `hartSupports` is pure in Lean: Rocq `exec (hartSupports X) s = Some (true, s)` ↦
  `hartSupports .X = true`; Rocq's fuelled `_rec_currentlyEnabled` facts are stated on
  `currentlyEnabled`.  Rocq loops (`foreach_ZM_up'`, `untilMT`) ↦ lean-sail's `IntRange`
  `forIn` and `untilFuelM`.
* Rocq section hypotheses become theorem premises; section `Let`s become `def`s or are
  inlined; premise bundles that several statements share are `structure`s
  (`FetchM4`, `FetchM2`, `FetchS`, `MemM8`, `AmoS4`), each field a Rocq hypothesis.

Also here: the tactic `exec_run` (`exec_steps` plus the closed-guard reductions,
`assert`, the `execR` kit) and `execIte`.

**Deviations from Rocq.**  The conventions above.  The compressed lemmas are `rfl`
(the Lean model's `execute (.C_* …)` is `pure (.ExecuteAs …)`, as in Rocq).

**Name map (Rocq → Lean).**  WpGpr: `exec_rX_bits_gpr` ↦ `execRXBitsGpr`,
`exec_wX_bits_gpr` ↦ `execWXBitsGpr`, `exec_ext_data_get_addr_gpr` ↦
`execExtDataGetAddrGpr`, `gpr_rd_val` ↦ `gprRdVal`, `exec_execute_RTYPE_ADD_gpr` ↦
`execExecuteRTYPEADDGpr`.  WpMmodeLeafBase: `gpr_addi_val` ↦ `gprAddiVal`,
`exec_execute_ITYPE_ADDI_gpr` ↦ `execExecuteITYPEADDIGpr`, `gpr_addiw_val` ↦
`gprAddiwVal`, `exec_execute_ADDIW_gpr` ↦ `execExecuteADDIWGpr`, `gpr_or_val` ↦
`gprOrVal`, `exec_execute_RTYPE_OR_gpr` ↦ `execExecuteRTYPEORGpr`, `gpr_sub_val` ↦
`gprSubVal`, `exec_execute_RTYPE_SUB_gpr` ↦ `execExecuteRTYPESUBGpr`, `gpr_ori_val` ↦
`gprOriVal`, `gpr_andi_val` ↦ `gprAndiVal`, `gpr_sltiu_val` ↦ `gprSltiuVal`,
`exec_execute_ITYPE_ORI_gpr` ↦ `execExecuteITYPEORIGpr`, `exec_execute_ITYPE_ANDI_gpr`
↦ `execExecuteITYPEANDIGpr`, `exec_execute_ITYPE_SLTIU_gpr` ↦
`execExecuteITYPESLTIUGpr`, `exec_execute_UTYPE_AUIPC_gpr` ↦
`execExecuteUTYPEAUIPCGpr`, `caddi16sp_imm` ↦ `caddi16spImm`, `caddi4spn_imm` ↦
`caddi4spnImm`, `exec_execute_C_X` ↦ `execExecuteCX` for X ∈ {SDSP, LDSP, ADDI, MV,
ADDI4SPN, LI, LUI, JR, BNEZ, BEQZ, ADDIW, ADDI16SP, ADD, SLLI, SRLI, OR, AND, LW, J}.
RiscvExtras: `auipc_off` ↦ `auipcOff`.  WpMmodeShiftiop: `gpr_src` ↦ `gprSrc`,
`gpr_slli_val` ↦ `gprSlliVal`, `gpr_srli_val` ↦ `gprSrliVal`,
`exec_execute_SHIFTIOP_SLLI_gpr` ↦ `execExecuteSHIFTIOPSLLIGpr`,
`exec_execute_SHIFTIOP_SRLI_gpr` ↦ `execExecuteSHIFTIOPSRLIGpr`.  Lean-only:
`ExecSt.gpr`, `ExecSt.setGpr`, `execIte`, `exec_run`.

**Dropped** (no weak use): the remaining lemmas of these Rocq files (their other
ALU/compressed forms, the Iris rules).
-/
import Weak.ExecLib
import MachCSL.UExecAluGpr

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `exec_steps` plus the closed-guard reductions (`if True`, `decide` on closed
`Bool` guards, `assert`), for the model's straight-line leaves. -/
syntax "exec_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_run) => `(tactic| simp (config := { decide := true }) only [execBind, readReg,
      writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, exec, execReturnm, ↓reduceIte, ite_true,
      ite_false, Bool.false_eq_true, assert, PreSail.assert, execRBind, execRLiftR, execRReturnR, execRThrow, decide_false, decide_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and])
  | `(tactic| exec_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only [execBind, readReg,
      writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, exec, execReturnm, ↓reduceIte, ite_true,
      ite_false, Bool.false_eq_true, assert, PreSail.assert, execRBind, execRLiftR, execRReturnR, execRThrow, decide_false, decide_true, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, $ls,*])

/-- `exec` of an `if` is the `if` of the `exec`s. -/
theorem execIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X) (s : ExecSt) :
    exec (if c then a else b) s = if c then exec a s else exec b s := by
  split <;> rfl

/-! ## 1. GPRs at a symbolic index (Rocq `WpGpr.v`) -/

/-- GPR `i` of the state (`x0` reads zero; Rocq
`if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64 (gpr_of_Z (uint i)))`). -/
def ExecSt.gpr (s : ExecSt) (i : BitVec 5) : BitVec 64 := uxaXget s.regs i

/-- Write GPR `i` (`x0` discards; Rocq
`if uint i =? 0 then s else set_reg s (R_bitvector_64 (gpr_of_Z (uint i))) v`). -/
def ExecSt.setGpr (s : ExecSt) (i : BitVec 5) (v : BitVec 64) : ExecSt :=
  match i.toNat with
  | 0 => s
  | 1 => s.setReg .x1 v
  | 2 => s.setReg .x2 v
  | 3 => s.setReg .x3 v
  | 4 => s.setReg .x4 v
  | 5 => s.setReg .x5 v
  | 6 => s.setReg .x6 v
  | 7 => s.setReg .x7 v
  | 8 => s.setReg .x8 v
  | 9 => s.setReg .x9 v
  | 10 => s.setReg .x10 v
  | 11 => s.setReg .x11 v
  | 12 => s.setReg .x12 v
  | 13 => s.setReg .x13 v
  | 14 => s.setReg .x14 v
  | 15 => s.setReg .x15 v
  | 16 => s.setReg .x16 v
  | 17 => s.setReg .x17 v
  | 18 => s.setReg .x18 v
  | 19 => s.setReg .x19 v
  | 20 => s.setReg .x20 v
  | 21 => s.setReg .x21 v
  | 22 => s.setReg .x22 v
  | 23 => s.setReg .x23 v
  | 24 => s.setReg .x24 v
  | 25 => s.setReg .x25 v
  | 26 => s.setReg .x26 v
  | 27 => s.setReg .x27 v
  | 28 => s.setReg .x28 v
  | 29 => s.setReg .x29 v
  | 30 => s.setReg .x30 v
  | _ => s.setReg .x31 v

/-- Rocq `exec_rX_bits_gpr`. -/
theorem execRXBitsGpr (i : BitVec 5) (s : ExecSt) :
    exec (rX_bits (.Regidx i)) s = some (s.gpr i, s) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Rocq `exec_wX_bits_gpr`. -/
theorem execWXBitsGpr (i : BitVec 5) (v : BitVec 64) (s : ExecSt) :
    exec (wX_bits (.Regidx i) v) s = some ((), s.setGpr i v) := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- Rocq `exec_ext_data_get_addr_gpr`. -/
theorem execExtDataGetAddrGpr (rs1 : BitVec 5) (offset : BitVec 64) (acc : MemoryAccessType mem_payload)
    (w : Nat) (s : ExecSt) :
    exec (ext_data_get_addr (.Regidx rs1) offset acc w) s =
      some (.Ext_DataAddr_OK (.Virtaddr (s.gpr rs1 + offset)), s) := by
  unfold ext_data_get_addr
  simp only [execBind, execRXBitsGpr, execReturnm]

/-- Rocq `gpr_rd_val`. -/
def gprRdVal (rs2 rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := s.gpr rs1 + s.gpr rs2

/-- Rocq `exec_execute_RTYPE_ADD_gpr`. -/
theorem execExecuteRTYPEADDGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) :
    exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprRdVal rs2 rs1 s)) := by
  unfold execute_RTYPE gprRdVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-! ## 2. Register-only ALU forms (Rocq `WpMmodeLeafBase.v`, `WpMmodeShiftiop.v`) -/

/-- Rocq `gpr_addi_val`. -/
def gprAddiVal (rs1 : BitVec 5) (imm : BitVec 12) (s : ExecSt) : BitVec 64 :=
  s.gpr rs1 + sign_extend (m := 64) imm

/-- Rocq `exec_execute_ITYPE_ADDI_gpr`. -/
theorem execExecuteITYPEADDIGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    exec (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprAddiVal rs1 imm s)) := by
  show exec (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ADDI) s = _
  unfold execute_ITYPE gprAddiVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `gpr_addiw_val`. -/
def gprAddiwVal (rs1 : BitVec 5) (imm : BitVec 12) (s : ExecSt) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (s.gpr rs1 + sign_extend (m := 64) imm) 31 0)

/-- Rocq `exec_execute_ADDIW_gpr`. -/
theorem execExecuteADDIWGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    exec (execute (.ADDIW (imm, .Regidx rs1, .Regidx rd))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprAddiwVal rs1 imm s)) := by
  show exec (execute_ADDIW imm (.Regidx rs1) (.Regidx rd)) s = _
  unfold execute_ADDIW gprAddiwVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `gpr_or_val`. -/
def gprOrVal (rs2 rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := s.gpr rs1 ||| s.gpr rs2

/-- Rocq `exec_execute_RTYPE_OR_gpr` (the `uint rd ≠ 0` premise is kept; `setGpr`
discards an `x0` write anyway). -/
theorem execExecuteRTYPEORGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) (_hrd : rd.toNat ≠ 0) :
    exec (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprOrVal rs2 rs1 s)) := by
  show exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .OR) s = _
  unfold execute_RTYPE gprOrVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `gpr_sub_val`. -/
def gprSubVal (rs2 rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := s.gpr rs1 - s.gpr rs2

/-- Rocq `exec_execute_RTYPE_SUB_gpr`. -/
theorem execExecuteRTYPESUBGpr (rs2 rs1 rd : BitVec 5) (s : ExecSt) :
    exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .SUB) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSubVal rs2 rs1 s)) := by
  unfold execute_RTYPE gprSubVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `gpr_ori_val`. -/
def gprOriVal (rs1 : BitVec 5) (imm : BitVec 12) (s : ExecSt) : BitVec 64 :=
  s.gpr rs1 ||| sign_extend (m := 64) imm

/-- Rocq `gpr_andi_val`. -/
def gprAndiVal (rs1 : BitVec 5) (imm : BitVec 12) (s : ExecSt) : BitVec 64 :=
  s.gpr rs1 &&& sign_extend (m := 64) imm

/-- Rocq `gpr_sltiu_val`. -/
def gprSltiuVal (rs1 : BitVec 5) (imm : BitVec 12) (s : ExecSt) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u (s.gpr rs1) (sign_extend (m := 64) imm)))

/-- Rocq `exec_execute_ITYPE_ORI_gpr`. -/
theorem execExecuteITYPEORIGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    exec (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprOriVal rs1 imm s)) := by
  show exec (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ORI) s = _
  unfold execute_ITYPE gprOriVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `exec_execute_ITYPE_ANDI_gpr`. -/
theorem execExecuteITYPEANDIGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    exec (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprAndiVal rs1 imm s)) := by
  show exec (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ANDI) s = _
  unfold execute_ITYPE gprAndiVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `exec_execute_ITYPE_SLTIU_gpr`. -/
theorem execExecuteITYPESLTIUGpr (rs1 rd : BitVec 5) (imm : BitVec 12) (s : ExecSt) :
    exec (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSltiuVal rs1 imm s)) := by
  show exec (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .SLTIU) s = _
  unfold execute_ITYPE gprSltiuVal
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `auipc_off` (RiscvExtras). -/
def auipcOff (imm : BitVec 20) : BitVec 64 := sign_extend (m := 64) (imm +++ 0x000#12)

/-- Rocq `exec_execute_UTYPE_AUIPC_gpr`. -/
theorem execExecuteUTYPEAUIPCGpr (rd : BitVec 5) (imm : BitVec 20) (s : ExecSt) :
    exec (execute (.UTYPE (imm, .Regidx rd, .AUIPC))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (s.regs .PC + auipcOff imm)) := by
  show exec (execute_UTYPE imm (.Regidx rd) .AUIPC) s = _
  unfold execute_UTYPE auipcOff get_arch_pc
  exec_steps [execWXBitsGpr]

/-- Rocq `gpr_src` (WpMmodeShiftiop). -/
def gprSrc (rs1 : BitVec 5) (s : ExecSt) : BitVec 64 := s.gpr rs1

/-- Rocq `gpr_slli_val`. -/
def gprSlliVal (rs1 : BitVec 5) (shamt : BitVec 6) (s : ExecSt) : BitVec 64 :=
  shift_bits_left (gprSrc rs1 s) (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0)

/-- Rocq `gpr_srli_val`. -/
def gprSrliVal (rs1 : BitVec 5) (shamt : BitVec 6) (s : ExecSt) : BitVec 64 :=
  shift_bits_right (gprSrc rs1 s) (Sail.BitVec.extractLsb shamt (Functions.log2_xlen -i 1) 0)

/-- Rocq `exec_execute_SHIFTIOP_SLLI_gpr`. -/
theorem execExecuteSHIFTIOPSLLIGpr (rs1 rd : BitVec 5) (shamt : BitVec 6) (s : ExecSt) :
    exec (execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSlliVal rs1 shamt s)) := by
  show exec (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) .SLLI) s = _
  unfold execute_SHIFTIOP gprSlliVal gprSrc
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-- Rocq `exec_execute_SHIFTIOP_SRLI_gpr`. -/
theorem execExecuteSHIFTIOPSRLIGpr (rs1 rd : BitVec 5) (shamt : BitVec 6) (s : ExecSt) :
    exec (execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SRLI))) s =
      some (RETIRE_SUCCESS, s.setGpr rd (gprSrliVal rs1 shamt s)) := by
  show exec (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) .SRLI) s = _
  unfold execute_SHIFTIOP gprSrliVal gprSrc
  simp only [execBind, execRXBitsGpr, execWXBitsGpr, execReturnm]

/-! ## 3. The compressed redirects (Rocq `WpMmodeLeafBase.v`) -/

/-- Rocq `caddi16sp_imm`. -/
def caddi16spImm (imm : BitVec 6) : BitVec 12 := sign_extend (m := 12) (imm +++ 0x0#4)
/-- Rocq `caddi4spn_imm`. -/
def caddi4spnImm (nzimm : BitVec 8) : BitVec 12 := 0b00#2 +++ (nzimm +++ 0b00#2)

/-- Rocq `exec_execute_C_SDSP`. -/
theorem execExecuteCSDSP (uimm : BitVec 6) (rs2 : regidx) (s : ExecSt) :
    exec (execute (.C_SDSP (uimm, rs2))) s =
      some (.ExecuteAs (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), rs2, sp, 8)), s) := rfl
/-- Rocq `exec_execute_C_LDSP`. -/
theorem execExecuteCLDSP (uimm : BitVec 6) (rd : regidx) (s : ExecSt) :
    exec (execute (.C_LDSP (uimm, rd))) s =
      some (.ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, rd, false, 8)), s) := rfl
/-- Rocq `exec_execute_C_ADDI`. -/
theorem execExecuteCADDI (imm : BitVec 6) (rsd : regidx) (s : ExecSt) :
    exec (execute (.C_ADDI (imm, rsd))) s =
      some (.ExecuteAs (.ITYPE (sign_extend (m := 12) imm, rsd, rsd, .ADDI)), s) := rfl
/-- Rocq `exec_execute_C_MV`. -/
theorem execExecuteCMV (rd rs2 : regidx) (s : ExecSt) :
    exec (execute (.C_MV (rd, rs2))) s = some (.ExecuteAs (.RTYPE (rs2, zreg, rd, .ADD)), s) := rfl
/-- Rocq `exec_execute_C_ADDI4SPN`. -/
theorem execExecuteCADDI4SPN (rdc : cregidx) (nzimm : BitVec 8) (s : ExecSt) :
    exec (execute (.C_ADDI4SPN (rdc, nzimm))) s =
      some (.ExecuteAs (.ITYPE (caddi4spnImm nzimm, sp, creg2reg_idx rdc, .ADDI)), s) := rfl
/-- Rocq `exec_execute_C_LI`. -/
theorem execExecuteCLI (imm : BitVec 6) (rd : regidx) (s : ExecSt) :
    exec (execute (.C_LI (imm, rd))) s =
      some (.ExecuteAs (.ITYPE (sign_extend (m := 12) imm, zreg, rd, .ADDI)), s) := rfl
/-- Rocq `exec_execute_C_LUI`. -/
theorem execExecuteCLUI (imm : BitVec 6) (rd : regidx) (s : ExecSt) :
    exec (execute (.C_LUI (imm, rd))) s =
      some (.ExecuteAs (.UTYPE (sign_extend (m := 20) imm, rd, .LUI)), s) := rfl
/-- Rocq `exec_execute_C_JR`. -/
theorem execExecuteCJR (rs1 : regidx) (s : ExecSt) :
    exec (execute (.C_JR rs1)) s = some (.ExecuteAs (.JALR (zeros (n := 12), rs1, zreg)), s) := rfl
/-- Rocq `exec_execute_C_BNEZ`. -/
theorem execExecuteCBNEZ (imm : BitVec 8) (rs : cregidx) (s : ExecSt) :
    exec (execute (.C_BNEZ (imm, rs))) s =
      some (.ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BNE)), s) :=
  rfl
/-- Rocq `exec_execute_C_BEQZ`. -/
theorem execExecuteCBEQZ (imm : BitVec 8) (rs : cregidx) (s : ExecSt) :
    exec (execute (.C_BEQZ (imm, rs))) s =
      some (.ExecuteAs (.BTYPE (sign_extend (m := 13) (imm +++ 0#1), zreg, creg2reg_idx rs, .BEQ)), s) :=
  rfl
/-- Rocq `exec_execute_C_ADDIW`. -/
theorem execExecuteCADDIW (imm : BitVec 6) (rsd : regidx) (s : ExecSt) :
    exec (execute (.C_ADDIW (imm, rsd))) s =
      some (.ExecuteAs (.ADDIW (sign_extend (m := 12) imm, rsd, rsd)), s) := rfl
/-- Rocq `exec_execute_C_ADDI16SP`. -/
theorem execExecuteCADDI16SP (imm : BitVec 6) (s : ExecSt) :
    exec (execute (.C_ADDI16SP imm)) s =
      some (.ExecuteAs (.ITYPE (caddi16spImm imm, sp, sp, .ADDI)), s) := rfl
/-- Rocq `exec_execute_C_ADD`. -/
theorem execExecuteCADD (rsd rs2 : regidx) (s : ExecSt) :
    exec (execute (.C_ADD (rsd, rs2))) s = some (.ExecuteAs (.RTYPE (rs2, rsd, rsd, .ADD)), s) := rfl
/-- Rocq `exec_execute_C_SLLI`. -/
theorem execExecuteCSLLI (shamt : BitVec 6) (rsd : regidx) (s : ExecSt) :
    exec (execute (.C_SLLI (shamt, rsd))) s =
      some (.ExecuteAs (.SHIFTIOP (shamt, rsd, rsd, .SLLI)), s) := rfl
/-- Rocq `exec_execute_C_SRLI`. -/
theorem execExecuteCSRLI (shamt : BitVec 6) (crsd : cregidx) (s : ExecSt) :
    exec (execute (.C_SRLI (shamt, crsd))) s =
      some (.ExecuteAs (.SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, .SRLI)), s) := rfl
/-- Rocq `exec_execute_C_OR`. -/
theorem execExecuteCOR (rsd rs2 : cregidx) (s : ExecSt) :
    exec (execute (.C_OR (rsd, rs2))) s =
      some (.ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .OR)), s) := rfl
/-- Rocq `exec_execute_C_AND`. -/
theorem execExecuteCAND (rsd rs2 : cregidx) (s : ExecSt) :
    exec (execute (.C_AND (rsd, rs2))) s =
      some (.ExecuteAs (.RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, .AND)), s) := rfl
/-- Rocq `exec_execute_C_LW`. -/
theorem execExecuteCLW (uimm : BitVec 5) (rsc1 rdc : cregidx) (s : ExecSt) :
    exec (execute (.C_LW (uimm, rsc1, rdc))) s =
      some (.ExecuteAs (.LOAD (zero_extend (m := 12) (uimm +++ 0b00#2), creg2reg_idx rsc1,
        creg2reg_idx rdc, false, 4)), s) := rfl
/-- Rocq `exec_execute_C_J`. -/
theorem execExecuteCJ (imm : BitVec 11) (s : ExecSt) :
    exec (execute (.C_J imm)) s =
      some (.ExecuteAs (.JAL (sign_extend (m := 21) (imm +++ 0#1), zreg)), s) := rfl

end Weak

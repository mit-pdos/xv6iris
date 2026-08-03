(* CodeStrlen.v -- the instruction-DECODE layer for xv6's strlen().

     strlen @ 0x80000e52 .. 0x80000e7d   (offsets 0x00 .. 0x2a, 44 bytes)

   One [kernel_text -* instr pc <is_rvc> <AST>] fact ([sli_<off>]) per
   instruction, plus the decode facts they consume.  Shared words come from
   KernelRvcDecode as [cdec_<word>]; strlen's own are [sldc_]/[sldb_].

     +0x00..+0x06        the 2-slot frame (a plain [c.addi sp,-16] push and a
                         [c.addi sp,16] pop -- the frame is symmetric here,
                         unlike fetchaddr's)
     +0x08 lbu a5,0(a0)
     +0x0c beqz a5 -> +0x28      s[0] == 0: return 0
     +0x0e addi a5,a0,1
     +0x12 mv a3,a5              <-- loop head, a3 = s + 1 + t
     +0x14 addi a5,a5,1
     +0x16 lbu a4,-1(a5)         reads the byte at a3 (gcc bumps FIRST)
     +0x1a bnez a4 -> +0x12
     +0x1c subw a0,a3,a0         a0 is UNTOUCHED until here, so it still holds s
     +0x20..+0x26        the epilogue, shared with the +0x28 empty-string arm  *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for this function's own words.                 *)
(* ===================================================================== *)

(* c.beqz a5,+0x28     # empty string -> return 0 *)
Lemma sldc_cf91 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf91 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 14, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a3,a5          # <-- loop head; a3 records the cursor *)
Lemma sldc_86be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.addi a5,a5,1 *)
Lemma sldc_0785 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0785 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.bnez a4,-0x08     # -> +0x12 *)
Lemma sldc_ff65 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xff65 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 252, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.j -0x0a           # -> +0x20, the epilogue *)
Lemma sldc_bfdd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfdd : mword 16)) s
  = Some (C_J (mword_of_int 2043), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* lbu a5,0(a0)        # s[0] *)
Lemma sldb_00054783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00054783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a0,1        # a5 := s + 1 *)
Lemma sldb_00150793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00150793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* lbu a4,-1(a5)       # the byte AT a3 *)
Lemma sldb_fff7c703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfff7c703 : mword 32)) s
  = Some (LOAD (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* subw a0,a3,a0       # return a3 - s *)
Lemma sldb_40a6853b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40a6853b : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 13), Regidx (mword_of_int 10), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InstrsSL.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma sli_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).  (* c.addi sp,sp,-16    # 2-slot frame: ra/s0 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma sli_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.strlen + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma sli_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.strlen + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma sli_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,16 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma sli_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x08) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), true, 1)).  (* lbu a5,0(a0)        # s[0] *)
  Proof. mk_base (KernelSyms.strlen + 0x08)%Z (mword_of_int 0x00054783 : mword 32)
    (mword_of_int (KernelSyms.strlen + 0x08) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), true, 1)) sldb_00054783. Qed.

  Lemma sli_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x0c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).  (* c.beqz a5,+0x28     # empty string -> return 0 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x0c)%Z (mword_of_int 0xcf91 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x0c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 14 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) sldc_cf91 exec_execute_C_BEQZ. Qed.

  Lemma sli_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x0e) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).  (* addi a5,a0,1        # a5 := s + 1 *)
  Proof. mk_base (KernelSyms.strlen + 0x0e)%Z (mword_of_int 0x00150793 : mword 32)
    (mword_of_int (KernelSyms.strlen + 0x0e) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)) sldb_00150793. Qed.

  Lemma sli_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 13), ADD)).  (* c.mv a3,a5          # <-- loop head; a3 records the cursor *)
  Proof. mk_rvc (KernelSyms.strlen + 0x12)%Z (mword_of_int 0x86be : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 13), ADD)) sldc_86be exec_execute_C_MV. Qed.

  Lemma sli_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).  (* c.addi a5,a5,1 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x14)%Z (mword_of_int 0x0785 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) sldc_0785 exec_execute_C_ADDI. Qed.

  Lemma sli_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x16) : mword 64) false (LOAD (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), true, 1)).  (* lbu a4,-1(a5)       # the byte AT a3 *)
  Proof. mk_base (KernelSyms.strlen + 0x16)%Z (mword_of_int 0xfff7c703 : mword 32)
    (mword_of_int (KernelSyms.strlen + 0x16) : mword 64) (LOAD (mword_of_int 4095 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), true, 1)) sldb_fff7c703. Qed.

  Lemma sli_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x1a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)).  (* c.bnez a4,-0x08     # -> +0x12 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x1a)%Z (mword_of_int 0xff65 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)) sldc_ff65 exec_execute_C_BNEZ. Qed.

  Lemma sli_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x1c) : mword 64) false (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 13), Regidx (mword_of_int 10), SUBW)).  (* subw a0,a3,a0       # return a3 - s *)
  Proof. mk_base (KernelSyms.strlen + 0x1c)%Z (mword_of_int 0x40a6853b : mword 32)
    (mword_of_int (KernelSyms.strlen + 0x1c) : mword 64) (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 13), Regidx (mword_of_int 10), SUBW)) sldb_40a6853b. Qed.

  Lemma sli_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.strlen + 0x20)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma sli_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.strlen + 0x22)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma sli_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).  (* c.addi sp,sp,16 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x24)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma sli_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x26) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (KernelSyms.strlen + 0x26)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x26) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma sli_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x28) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,0 *)
  Proof. mk_rvc (KernelSyms.strlen + 0x28)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma sli_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.strlen + 0x2a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0")), zreg)).  (* c.j -0x0a           # -> +0x20, the epilogue *)
  Proof. mk_rvc (KernelSyms.strlen + 0x2a)%Z (mword_of_int 0xbfdd : mword 16)
    (mword_of_int (KernelSyms.strlen + 0x2a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2043 : mword 11) ('b"0")), zreg)) sldc_bfdd exec_execute_C_J. Qed.

End InstrsSL.


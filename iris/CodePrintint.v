(* CodePrintint.v -- the instruction-DECODE layer for xv6's printint().
   For every instruction of

     printint @ 0x80000466 .. 0x800004fa   (offsets 0x00 .. 0x94)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pii_<off>]) plus
   the per-instruction decode facts they consume ([pidc_<word>] compressed /
   [pidb_<word>] base).

   printint uses the 64-byte / 8-slot frame, so its four [c.sdsp]s, four
   [c.ldsp]s, the two [c.addi16sp]s and the [c.addi4spn] are shared
   KernelRvcDecode templates; everything else -- the digit loop's remu/divu,
   the [digits] table relocation, the byte load/store, the print loop's cursor
   arithmetic and the six branches -- is printint's own and is proved here. *)
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to printint.                            *)
(* ===================================================================== *)

(* 0xc219  c.beqz a2,+6   -- if (sign && ..) *)
Lemma pidc_c219 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc219 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 3, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4301  c.li t1,0 *)
Lemma pidc_4301 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4301 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4305  c.li t1,1 *)
Lemma pidc_4305 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4305 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4701  c.li a4,0 *)
Lemma pidc_4701 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4701 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_86ca] -- shared, see KernelRvcDecode.v *)

(* 0x88ba  c.mv a7,a4 *)
Lemma pidc_88ba s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x88ba : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 17), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8732  c.mv a4,a2 *)
Lemma pidc_8732 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8732 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x87aa  c.mv a5,a0 *)
Lemma pidc_87aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97c2  c.add a5,a5,a6 *)
Lemma pidc_97c2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97c2 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 16)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x993a  c.add s2,s2,a4 *)
Lemma pidc_993a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x993a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0685  c.addi a3,a3,1 *)
Lemma pidc_0685 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0685 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x197d  c.addi s2,s2,-1 *)
Lemma pidc_197d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x197d : mword 16)) s
  = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x14fd  c.addi s1,s1,-1 *)
Lemma pidc_14fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x14fd : mword 16)) s
  = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x377d  c.addiw a4,a4,-1 *)
Lemma pidc_377d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x377d : mword 16)) s
  = Some (C_ADDIW (mword_of_int 63, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1702  c.slli a4,a4,32 *)
Lemma pidc_1702 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1702 : mword 16)) s
  = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9301  c.srli a4,a4,32 *)
Lemma pidc_9301 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9301 : mword 16)) s
  = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbfbd  c.j -130  (the negate arm's jump back to [x = -xx]) *)
Lemma pidc_bfbd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfbd : mword 16)) s
  = Some (C_J (mword_of_int 1983 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to printint.  Negative immediates    *)
(* appear as the decoder's POSITIVE RESIDUE (-56 -> 4040, ...).           *)
(* ===================================================================== *)

(* bltz a0,+0x82 *)
Lemma pidb_08054163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08054163 : mword 32)) s
  = Some (BTYPE (mword_of_int 130 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* addi s2,s0,-56  -- s2 := buf *)
Lemma pidb_fc840913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc840913 : mword 32)) s
  = Some (ITYPE (mword_of_int 4040 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a6,0x7 -- a6 := &digits (high part) *)
Lemma pidb_00007817 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00007817 : mword 32)) s
  = Some (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 16), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a6,a6,656 -- a6 := &digits *)
Lemma pidb_29080813 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x29080813 : mword 32)) s
  = Some (ITYPE (mword_of_int 656 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addiw a2,a4,1 -- i+1 *)
Lemma pidb_0017061b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017061b : mword 32)) s
  = Some (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 12)), s).
Proof. decode_bridge_ms. Qed.

(* addiw a4,a7,2 *)
Lemma pidb_0028871b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0028871b : mword 32)) s
  = Some (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 14)), s).
Proof. decode_bridge_ms. Qed.

(* remu a5,a0,a1 -- x % base *)
Lemma pidb_02b577b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02b577b3 : mword 32)) s
  = Some (REM (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 15), true), s).
Proof. decode_bridge_ms. Qed.

(* divu a0,a0,a1 -- x /= base *)
Lemma pidb_02b55533 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02b55533 : mword 32)) s
  = Some (DIV (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 10), true), s).
Proof. decode_bridge_ms. Qed.

(* lbu a5,0(a5) -- digits[x % base] *)
Lemma pidb_0007c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007c783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* lbu a0,0(s1) -- buf[i] *)
Lemma pidb_0004c503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004c503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* sb a5,0(a3) -- buf[i++] = digit *)
Lemma pidb_00f68023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f68023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), 1), s).
Proof. decode_bridge_ms. Qed.

(* sb a5,-24(a2) -- buf[i++] = '-' *)
Lemma pidb_fef60423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfef60423 : mword 32)) s
  = Some (STORE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), 1), s).
Proof. decode_bridge_ms. Qed.

(* bgeu a5,a1,-30 -- the do-while back edge *)
Lemma pidb_feb7f1e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfeb7f1e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* beqz t1,+24 -- if (sign) *)
Lemma pidb_00030c63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00030c63 : mword 32)) s
  = Some (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 6), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a2,-32 *)
Lemma pidb_fe060793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe060793 : mword 32)) s
  = Some (ITYPE (mword_of_int 4064 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* add a2,a5,s0 *)
Lemma pidb_00878633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00878633 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 8), Regidx (mword_of_int 15), Regidx (mword_of_int 12), ADD), s).
Proof. decode_bridge_ms. Qed.

(* li a5,45 -- '-' *)
Lemma pidb_02d00793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02d00793 : mword 32)) s
  = Some (ITYPE (mword_of_int 45 : mword 12, zreg, Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* blez a4,+40 -- while (--i >= 0) guard *)
Lemma pidb_02e05463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02e05463 : mword 32)) s
  = Some (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* add s1,s2,a4 *)
Lemma pidb_00e904b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e904b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 9), ADD), s).
Proof. decode_bridge_ms. Qed.

(* sub s2,s2,a4 -- the print loop's end sentinel *)
Lemma pidb_40e90933 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40e90933 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 18), SUB), s).
Proof. decode_bridge_ms. Qed.

(* neg a0,a0 = sub a0,x0,a0 *)
Lemma pidb_40a00533 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40a00533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUB), s).
Proof. decode_bridge_ms. Qed.

(* bne s1,s2,-40 -- the print loop's back edge *)
Lemma pidb_ff249be3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff249be3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,consputc *)
Lemma pidb_d9fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd9fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096542 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section CodePrintint.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PI := KernelSyms.printint.

  (* ---- prologue (0x00..0x08) ---- *)

  Lemma pii_00 : kernel_text -∗ instr (mword_of_int PI : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc PI (mword_of_int 0x7139 : mword 16)
    (mword_of_int PI : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  Lemma pii_02 : kernel_text -∗ instr (mword_of_int (PI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PI + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (PI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  Lemma pii_04 : kernel_text -∗ instr (mword_of_int (PI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PI + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (PI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  Lemma pii_06 : kernel_text -∗ instr (mword_of_int (PI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PI + 0x06)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (PI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  Lemma pii_08 : kernel_text -∗ instr (mword_of_int (PI + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PI + 0x08)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (PI + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  (* ---- sign handling (0x0a..0x12, and the negate arm at 0x8e) ---- *)

  Lemma pii_0a : kernel_text -∗ instr (mword_of_int (PI + 0x0a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc (PI + 0x0a)%Z (mword_of_int 0xc219 : mword 16)
    (mword_of_int (PI + 0x0a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) pidc_c219 exec_execute_C_BEQZ. Qed.

  Lemma pii_0c : kernel_text -∗ instr (mword_of_int (PI + 0x0c) : mword 64) false (BTYPE (mword_of_int 130 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (PI + 0x0c)%Z (mword_of_int 0x08054163 : mword 32)
    (mword_of_int (PI + 0x0c) : mword 64) (BTYPE (mword_of_int 130 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) pidb_08054163. Qed.

  Lemma pii_10 : kernel_text -∗ instr (mword_of_int (PI + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 6), ADDI)).
  Proof. mk_rvc (PI + 0x10)%Z (mword_of_int 0x4301 : mword 16)
    (mword_of_int (PI + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 6), ADDI)) pidc_4301 exec_execute_C_LI. Qed.

  Lemma pii_12 : kernel_text -∗ instr (mword_of_int (PI + 0x12) : mword 64) false (ITYPE (mword_of_int 4040 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (PI + 0x12)%Z (mword_of_int 0xfc840913 : mword 32)
    (mword_of_int (PI + 0x12) : mword 64) (ITYPE (mword_of_int 4040 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 18), ADDI)) pidb_fc840913. Qed.

  Lemma pii_16 : kernel_text -∗ instr (mword_of_int (PI + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (PI + 0x16)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (PI + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) cdec_86ca exec_execute_C_MV. Qed.

  Lemma pii_18 : kernel_text -∗ instr (mword_of_int (PI + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (PI + 0x18)%Z (mword_of_int 0x4701 : mword 16)
    (mword_of_int (PI + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) pidc_4701 exec_execute_C_LI. Qed.

  Lemma pii_1a : kernel_text -∗ instr (mword_of_int (PI + 0x1a) : mword 64) false (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 16), AUIPC)).
  Proof. mk_base (PI + 0x1a)%Z (mword_of_int 0x00007817 : mword 32)
    (mword_of_int (PI + 0x1a) : mword 64) (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 16), AUIPC)) pidb_00007817. Qed.

  Lemma pii_1e : kernel_text -∗ instr (mword_of_int (PI + 0x1e) : mword 64) false (ITYPE (mword_of_int 656 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI)).
  Proof. mk_base (PI + 0x1e)%Z (mword_of_int 0x29080813 : mword 32)
    (mword_of_int (PI + 0x1e) : mword 64) (ITYPE (mword_of_int 656 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 16), ADDI)) pidb_29080813. Qed.

  (* ---- the digit loop (0x22..0x40) ---- *)

  Lemma pii_22 : kernel_text -∗ instr (mword_of_int (PI + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 17), ADD)).
  Proof. mk_rvc (PI + 0x22)%Z (mword_of_int 0x88ba : mword 16)
    (mword_of_int (PI + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 17), ADD)) pidc_88ba exec_execute_C_MV. Qed.

  Lemma pii_24 : kernel_text -∗ instr (mword_of_int (PI + 0x24) : mword 64) false (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 12))).
  Proof. mk_base (PI + 0x24)%Z (mword_of_int 0x0017061b : mword 32)
    (mword_of_int (PI + 0x24) : mword 64) (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 12))) pidb_0017061b. Qed.

  Lemma pii_28 : kernel_text -∗ instr (mword_of_int (PI + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (PI + 0x28)%Z (mword_of_int 0x8732 : mword 16)
    (mword_of_int (PI + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 14), ADD)) pidc_8732 exec_execute_C_MV. Qed.

  Lemma pii_2a : kernel_text -∗ instr (mword_of_int (PI + 0x2a) : mword 64) false (REM (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 15), true)).
  Proof. mk_base (PI + 0x2a)%Z (mword_of_int 0x02b577b3 : mword 32)
    (mword_of_int (PI + 0x2a) : mword 64) (REM (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 15), true)) pidb_02b577b3. Qed.

  Lemma pii_2e : kernel_text -∗ instr (mword_of_int (PI + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 16), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PI + 0x2e)%Z (mword_of_int 0x97c2 : mword 16)
    (mword_of_int (PI + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 16), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) pidc_97c2 exec_execute_C_ADD. Qed.

  Lemma pii_30 : kernel_text -∗ instr (mword_of_int (PI + 0x30) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (PI + 0x30)%Z (mword_of_int 0x0007c783 : mword 32)
    (mword_of_int (PI + 0x30) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)) pidb_0007c783. Qed.

  Lemma pii_34 : kernel_text -∗ instr (mword_of_int (PI + 0x34) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), 1)).
  Proof. mk_base (PI + 0x34)%Z (mword_of_int 0x00f68023 : mword 32)
    (mword_of_int (PI + 0x34) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), 1)) pidb_00f68023. Qed.

  Lemma pii_38 : kernel_text -∗ instr (mword_of_int (PI + 0x38) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PI + 0x38)%Z (mword_of_int 0x87aa : mword 16)
    (mword_of_int (PI + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) pidc_87aa exec_execute_C_MV. Qed.

  Lemma pii_3a : kernel_text -∗ instr (mword_of_int (PI + 0x3a) : mword 64) false (DIV (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 10), true)).
  Proof. mk_base (PI + 0x3a)%Z (mword_of_int 0x02b55533 : mword 32)
    (mword_of_int (PI + 0x3a) : mword 64) (DIV (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 10), true)) pidb_02b55533. Qed.

  Lemma pii_3e : kernel_text -∗ instr (mword_of_int (PI + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (PI + 0x3e)%Z (mword_of_int 0x0685 : mword 16)
    (mword_of_int (PI + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) pidc_0685 exec_execute_C_ADDI. Qed.

  Lemma pii_40 : kernel_text -∗ instr (mword_of_int (PI + 0x40) : mword 64) false (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU)).
  Proof. mk_base (PI + 0x40)%Z (mword_of_int 0xfeb7f1e3 : mword 32)
    (mword_of_int (PI + 0x40) : mword 64) (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU)) pidb_feb7f1e3. Qed.

  (* ---- the sign digit (0x44..0x58) ---- *)

  Lemma pii_44 : kernel_text -∗ instr (mword_of_int (PI + 0x44) : mword 64) false (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 6), BEQ)).
  Proof. mk_base (PI + 0x44)%Z (mword_of_int 0x00030c63 : mword 32)
    (mword_of_int (PI + 0x44) : mword 64) (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 6), BEQ)) pidb_00030c63. Qed.

  Lemma pii_48 : kernel_text -∗ instr (mword_of_int (PI + 0x48) : mword 64) false (ITYPE (mword_of_int 4064 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PI + 0x48)%Z (mword_of_int 0xfe060793 : mword 32)
    (mword_of_int (PI + 0x48) : mword 64) (ITYPE (mword_of_int 4064 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI)) pidb_fe060793. Qed.

  Lemma pii_4c : kernel_text -∗ instr (mword_of_int (PI + 0x4c) : mword 64) false (RTYPE (Regidx (mword_of_int 8), Regidx (mword_of_int 15), Regidx (mword_of_int 12), ADD)).
  Proof. mk_base (PI + 0x4c)%Z (mword_of_int 0x00878633 : mword 32)
    (mword_of_int (PI + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 8), Regidx (mword_of_int 15), Regidx (mword_of_int 12), ADD)) pidb_00878633. Qed.

  Lemma pii_50 : kernel_text -∗ instr (mword_of_int (PI + 0x50) : mword 64) false (ITYPE (mword_of_int 45 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PI + 0x50)%Z (mword_of_int 0x02d00793 : mword 32)
    (mword_of_int (PI + 0x50) : mword 64) (ITYPE (mword_of_int 45 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)) pidb_02d00793. Qed.

  Lemma pii_54 : kernel_text -∗ instr (mword_of_int (PI + 0x54) : mword 64) false (STORE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), 1)).
  Proof. mk_base (PI + 0x54)%Z (mword_of_int 0xfef60423 : mword 32)
    (mword_of_int (PI + 0x54) : mword 64) (STORE (mword_of_int 4072 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12), 1)) pidb_fef60423. Qed.

  Lemma pii_58 : kernel_text -∗ instr (mword_of_int (PI + 0x58) : mword 64) false (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 14))).
  Proof. mk_base (PI + 0x58)%Z (mword_of_int 0x0028871b : mword 32)
    (mword_of_int (PI + 0x58) : mword 64) (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 14))) pidb_0028871b. Qed.

  (* ---- the print loop's setup and body (0x5c..0x82) ---- *)

  Lemma pii_5c : kernel_text -∗ instr (mword_of_int (PI + 0x5c) : mword 64) false (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PI + 0x5c)%Z (mword_of_int 0x02e05463 : mword 32)
    (mword_of_int (PI + 0x5c) : mword 64) (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 0), BGE)) pidb_02e05463. Qed.

  Lemma pii_60 : kernel_text -∗ instr (mword_of_int (PI + 0x60) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PI + 0x60)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (PI + 0x60) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  Lemma pii_62 : kernel_text -∗ instr (mword_of_int (PI + 0x62) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))).
  Proof. mk_rvc (PI + 0x62)%Z (mword_of_int 0x377d : mword 16)
    (mword_of_int (PI + 0x62) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))) pidc_377d exec_execute_C_ADDIW. Qed.

  Lemma pii_64 : kernel_text -∗ instr (mword_of_int (PI + 0x64) : mword 64) false (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 9), ADD)).
  Proof. mk_base (PI + 0x64)%Z (mword_of_int 0x00e904b3 : mword 32)
    (mword_of_int (PI + 0x64) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 9), ADD)) pidb_00e904b3. Qed.

  Lemma pii_68 : kernel_text -∗ instr (mword_of_int (PI + 0x68) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (PI + 0x68)%Z (mword_of_int 0x197d : mword 16)
    (mword_of_int (PI + 0x68) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) pidc_197d exec_execute_C_ADDI. Qed.

  Lemma pii_6a : kernel_text -∗ instr (mword_of_int (PI + 0x6a) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PI + 0x6a)%Z (mword_of_int 0x993a : mword 16)
    (mword_of_int (PI + 0x6a) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) pidc_993a exec_execute_C_ADD. Qed.

  Lemma pii_6c : kernel_text -∗ instr (mword_of_int (PI + 0x6c) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_rvc (PI + 0x6c)%Z (mword_of_int 0x1702 : mword 16)
    (mword_of_int (PI + 0x6c) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) pidc_1702 exec_execute_C_SLLI. Qed.

  Lemma pii_6e : kernel_text -∗ instr (mword_of_int (PI + 0x6e) : mword 64) true (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 6)), SRLI)).
  Proof. mk_rvc (PI + 0x6e)%Z (mword_of_int 0x9301 : mword 16)
    (mword_of_int (PI + 0x6e) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 6)), SRLI)) pidc_9301 exec_execute_C_SRLI. Qed.

  Lemma pii_70 : kernel_text -∗ instr (mword_of_int (PI + 0x70) : mword 64) false (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 18), SUB)).
  Proof. mk_base (PI + 0x70)%Z (mword_of_int 0x40e90933 : mword 32)
    (mword_of_int (PI + 0x70) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 18), Regidx (mword_of_int 18), SUB)) pidb_40e90933. Qed.

  Lemma pii_74 : kernel_text -∗ instr (mword_of_int (PI + 0x74) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PI + 0x74)%Z (mword_of_int 0x0004c503 : mword 32)
    (mword_of_int (PI + 0x74) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1)) pidb_0004c503. Qed.

  Lemma pii_78 : kernel_text -∗ instr (mword_of_int (PI + 0x78) : mword 64) false (JAL (mword_of_int 2096542 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PI + 0x78)%Z (mword_of_int 0xd9fff0ef : mword 32)
    (mword_of_int (PI + 0x78) : mword 64) (JAL (mword_of_int 2096542 : mword 21, Regidx (mword_of_int 1))) pidb_d9fff0ef. Qed.

  Lemma pii_7c : kernel_text -∗ instr (mword_of_int (PI + 0x7c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (PI + 0x7c)%Z (mword_of_int 0x14fd : mword 16)
    (mword_of_int (PI + 0x7c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) pidc_14fd exec_execute_C_ADDI. Qed.

  Lemma pii_7e : kernel_text -∗ instr (mword_of_int (PI + 0x7e) : mword 64) false (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (PI + 0x7e)%Z (mword_of_int 0xff249be3 : mword 32)
    (mword_of_int (PI + 0x7e) : mword 64) (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE)) pidb_ff249be3. Qed.

  Lemma pii_82 : kernel_text -∗ instr (mword_of_int (PI + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PI + 0x82)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (PI + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  (* ---- epilogue (0x84..0x8c) ---- *)

  Lemma pii_84 : kernel_text -∗ instr (mword_of_int (PI + 0x84) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PI + 0x84)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (PI + 0x84) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  Lemma pii_86 : kernel_text -∗ instr (mword_of_int (PI + 0x86) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PI + 0x86)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (PI + 0x86) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  Lemma pii_88 : kernel_text -∗ instr (mword_of_int (PI + 0x88) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PI + 0x88)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (PI + 0x88) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  Lemma pii_8a : kernel_text -∗ instr (mword_of_int (PI + 0x8a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PI + 0x8a)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (PI + 0x8a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  Lemma pii_8c : kernel_text -∗ instr (mword_of_int (PI + 0x8c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PI + 0x8c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PI + 0x8c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- the negate arm (0x8e..0x94) ---- *)

  Lemma pii_8e : kernel_text -∗ instr (mword_of_int (PI + 0x8e) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUB)).
  Proof. mk_base (PI + 0x8e)%Z (mword_of_int 0x40a00533 : mword 32)
    (mword_of_int (PI + 0x8e) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUB)) pidb_40a00533. Qed.

  Lemma pii_92 : kernel_text -∗ instr (mword_of_int (PI + 0x92) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 6), ADDI)).
  Proof. mk_rvc (PI + 0x92)%Z (mword_of_int 0x4305 : mword 16)
    (mword_of_int (PI + 0x92) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 6), ADDI)) pidc_4305 exec_execute_C_LI. Qed.

  Lemma pii_94 : kernel_text -∗ instr (mword_of_int (PI + 0x94) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1983 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PI + 0x94)%Z (mword_of_int 0xbfbd : mword 16)
    (mword_of_int (PI + 0x94) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1983 : mword 11) ('b"0")), zreg)) pidc_bfbd exec_execute_C_J. Qed.

End CodePrintint.

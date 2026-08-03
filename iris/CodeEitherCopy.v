(* CodeEitherCopy.v -- the instruction-DECODE layer for xv6's
   either_copyout() AND either_copyin().  For EVERY instruction of

     either_copyout @ 0x80002260 .. 0x800022a9   (offsets 0x00 .. 0x48)
     either_copyin  @ 0x800022aa .. 0x800022f3   (offsets 0x00 .. 0x48)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([eco_<off>] /
   [eci_<off>]).

   ONE FILE FOR THE TWO FUNCTIONS, which is not the usual per-function
   convention but is what these two are: gcc emitted the SAME 31-instruction
   block twice, differing only in which of a0/a1 is the flag (+0x10/+0x12)
   and in the three [jal] targets.  Every other word is shared, so a second
   file would have been a verbatim copy of this one's word layer.

     0x00 7179       c.addi16sp sp,-48
     0x02 f406       c.sdsp     ra,40(sp)
     0x04 f022       c.sdsp     s0,32(sp)
     0x06 ec26       c.sdsp     s1,24(sp)
     0x08 e84a       c.sdsp     s2,16(sp)
     0x0a e44e       c.sdsp     s3,8(sp)
     0x0c e052       c.sdsp     s4,0(sp)
     0x0e 1800       c.addi4spn s0,sp,48          # s0 = entry sp
     0x10 84aa/8a2a  c.mv       s1,a0 / s4,a0     # <- THE ONLY BODY DIFFERENCE
     0x12 8a2e/84ae  c.mv       s4,a1 / s1,a1     #    (out: s1=flag s4=dst;
     0x14 89b2       c.mv       s3,a2             #     in:  s4=dst  s1=flag)
     0x16 8936       c.mv       s2,a3
     0x18 <jal>      jal        ra,myproc
     0x1c cc99       c.beqz     s1,+0x1e          # !user -> the memmove arm
     0x1e 86ca       c.mv       a3,s2             # len
     0x20 864e       c.mv       a2,s3             # src / srcva
     0x22 85d2       c.mv       a1,s4             # dst / dstva
     0x24 6928       c.ld       a0,80(a0)         # a0 := p->pagetable
     0x26 <jal>      jal        ra,copyout/copyin # ITS return value is ours
     0x2a 70a2       c.ldsp     ra,40(sp)         # <- BOTH arms join here
     0x2c 7402       c.ldsp     s0,32(sp)
     0x2e 64e2       c.ldsp     s1,24(sp)
     0x30 6942       c.ldsp     s2,16(sp)
     0x32 69a2       c.ldsp     s3,8(sp)
     0x34 6a02       c.ldsp     s4,0(sp)
     0x36 6145       c.addi16sp sp,48
     0x38 8082       c.ret
     0x3a 0009061b   sext.w     a2,s2             # (uint)len
     0x3e 85ce       c.mv       a1,s3             # src
     0x40 8552       c.mv       a0,s4             # dst
     0x42 <jal>      jal        ra,memmove
     0x46 8526       c.mv       a0,s1             # return the FLAG, which the
     0x48 b7cd       c.j        -0x1e             # c.beqz proved is 0

   The frame is SYMMETRIC here (both ends are c.addi16sp), unlike
   fetchaddr's; and the 48-byte six-slot push/pop set is the one vmfault,
   pipealloc, binit and freerange already use, so all fifteen of its words
   come from [KernelRvcDecode].

   THREE WORDS ARE NEW TO THE TREE -- [89b2], [8936] and [cc99]; everything
   else comes from [KernelRvcDecode], including the six ([86ca] [864e]
   [85d2] [85ce] [6928] [b7cd]) that this function's sweep moved there out of
   the two or three private copies each had. *)
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
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed words.                                                      *)
(* ===================================================================== *)

(* +0x14  c.mv s3,a2   -- NEW *)
Lemma ecdc_89b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89b2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x16  c.mv s2,a3   -- NEW *)
Lemma ecdc_8936 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8936 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1c  c.beqz s1,+0x1e   -- NEW *)
Lemma ecdc_cc99 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcc99 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 15, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_86ca] [cdec_864e] [cdec_85d2] [cdec_85ce] [cdec_6928] [cdec_b7cd]
   -- shared, see KernelRvcDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)


(* either_copyout +0x18  jal ra,myproc   (0x80002278 -> 0x80001904 is -2420) *)
Lemma ecdb_e8cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe8cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094732 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* either_copyout +0x26  jal ra,copyout  (0x80002286 -> 0x80001624 is -3170) *)
Lemma ecdb_b9eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb9eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093982 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* either_copyout +0x42  jal ra,memmove  (0x800022a2 -> 0x80000d28 is -5498) *)
Lemma ecdb_a87fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa87fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2091654 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* either_copyin +0x18  jal ra,myproc    (0x800022c2 -> 0x80001904 is -2494) *)
Lemma ecdb_e42ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe42ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094658 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


(* either_copyin +0x42  jal ra,memmove   (0x800022ec -> 0x80000d28 is -5572) *)
Lemma ecdb_a3dfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa3dfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2091580 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section EitherCopyInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation ECO := KernelSyms.either_copyout.
  Notation ECI := KernelSyms.either_copyin.

  (* ------------------------- either_copyout ------------------------- *)

  Lemma eco_00 : kernel_text -∗ instr (mword_of_int (ECO + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ECO + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (ECO + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma eco_02 : kernel_text -∗ instr (mword_of_int (ECO + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (ECO + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (ECO + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma eco_04 : kernel_text -∗ instr (mword_of_int (ECO + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (ECO + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (ECO + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma eco_06 : kernel_text -∗ instr (mword_of_int (ECO + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (ECO + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (ECO + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma eco_08 : kernel_text -∗ instr (mword_of_int (ECO + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (ECO + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (ECO + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma eco_0a : kernel_text -∗ instr (mword_of_int (ECO + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (ECO + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (ECO + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma eco_0c : kernel_text -∗ instr (mword_of_int (ECO + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (ECO + 0x0c)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (ECO + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  Lemma eco_0e : kernel_text -∗ instr (mword_of_int (ECO + 0x0e) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (ECO + 0x0e)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (ECO + 0x0e) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma eco_10 : kernel_text -∗ instr (mword_of_int (ECO + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (ECO + 0x10)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (ECO + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma eco_12 : kernel_text -∗ instr (mword_of_int (ECO + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (ECO + 0x12)%Z (mword_of_int 0x8a2e : mword 16)
    (mword_of_int (ECO + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2e exec_execute_C_MV. Qed.

  Lemma eco_14 : kernel_text -∗ instr (mword_of_int (ECO + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (ECO + 0x14)%Z (mword_of_int 0x89b2 : mword 16)
    (mword_of_int (ECO + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 19), ADD)) ecdc_89b2 exec_execute_C_MV. Qed.

  Lemma eco_16 : kernel_text -∗ instr (mword_of_int (ECO + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (ECO + 0x16)%Z (mword_of_int 0x8936 : mword 16)
    (mword_of_int (ECO + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)) ecdc_8936 exec_execute_C_MV. Qed.

  Lemma eco_18 : kernel_text -∗ instr (mword_of_int (ECO + 0x18) : mword 64) false (JAL (mword_of_int 2094732 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECO + 0x18)%Z (mword_of_int 0xe8cff0ef : mword 32)
    (mword_of_int (ECO + 0x18) : mword 64) (JAL (mword_of_int 2094732 : mword 21, Regidx (mword_of_int 1))) ecdb_e8cff0ef. Qed.

  Lemma eco_1c : kernel_text -∗ instr (mword_of_int (ECO + 0x1c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)).
  Proof. mk_rvc (ECO + 0x1c)%Z (mword_of_int 0xcc99 : mword 16)
    (mword_of_int (ECO + 0x1c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)) ecdc_cc99 exec_execute_C_BEQZ. Qed.

  Lemma eco_1e : kernel_text -∗ instr (mword_of_int (ECO + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (ECO + 0x1e)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (ECO + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) cdec_86ca exec_execute_C_MV. Qed.

  Lemma eco_20 : kernel_text -∗ instr (mword_of_int (ECO + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (ECO + 0x20)%Z (mword_of_int 0x864e : mword 16)
    (mword_of_int (ECO + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)) cdec_864e exec_execute_C_MV. Qed.

  Lemma eco_22 : kernel_text -∗ instr (mword_of_int (ECO + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (ECO + 0x22)%Z (mword_of_int 0x85d2 : mword 16)
    (mword_of_int (ECO + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)) cdec_85d2 exec_execute_C_MV. Qed.

  Lemma eco_24 : kernel_text -∗ instr (mword_of_int (ECO + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (ECO + 0x24)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (ECO + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma eco_26 : kernel_text -∗ instr (mword_of_int (ECO + 0x26) : mword 64) false (JAL (mword_of_int 2093982 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECO + 0x26)%Z (mword_of_int 0xb9eff0ef : mword 32)
    (mword_of_int (ECO + 0x26) : mword 64) (JAL (mword_of_int 2093982 : mword 21, Regidx (mword_of_int 1))) ecdb_b9eff0ef. Qed.

  Lemma eco_2a : kernel_text -∗ instr (mword_of_int (ECO + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (ECO + 0x2a)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (ECO + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma eco_2c : kernel_text -∗ instr (mword_of_int (ECO + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (ECO + 0x2c)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (ECO + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma eco_2e : kernel_text -∗ instr (mword_of_int (ECO + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (ECO + 0x2e)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (ECO + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma eco_30 : kernel_text -∗ instr (mword_of_int (ECO + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (ECO + 0x30)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (ECO + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma eco_32 : kernel_text -∗ instr (mword_of_int (ECO + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (ECO + 0x32)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (ECO + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma eco_34 : kernel_text -∗ instr (mword_of_int (ECO + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (ECO + 0x34)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (ECO + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma eco_36 : kernel_text -∗ instr (mword_of_int (ECO + 0x36) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ECO + 0x36)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (ECO + 0x36) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma eco_38 : kernel_text -∗ instr (mword_of_int (ECO + 0x38) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (ECO + 0x38)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (ECO + 0x38) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma eco_3a : kernel_text -∗ instr (mword_of_int (ECO + 0x3a) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))).
  Proof. mk_base (ECO + 0x3a)%Z (mword_of_int 0x0009061b : mword 32)
    (mword_of_int (ECO + 0x3a) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))) bdec_0009061b. Qed.

  Lemma eco_3e : kernel_text -∗ instr (mword_of_int (ECO + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (ECO + 0x3e)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (ECO + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ce exec_execute_C_MV. Qed.

  Lemma eco_40 : kernel_text -∗ instr (mword_of_int (ECO + 0x40) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ECO + 0x40)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (ECO + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  Lemma eco_42 : kernel_text -∗ instr (mword_of_int (ECO + 0x42) : mword 64) false (JAL (mword_of_int 2091654 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECO + 0x42)%Z (mword_of_int 0xa87fe0ef : mword 32)
    (mword_of_int (ECO + 0x42) : mword 64) (JAL (mword_of_int 2091654 : mword 21, Regidx (mword_of_int 1))) ecdb_a87fe0ef. Qed.

  Lemma eco_46 : kernel_text -∗ instr (mword_of_int (ECO + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ECO + 0x46)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (ECO + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma eco_48 : kernel_text -∗ instr (mword_of_int (ECO + 0x48) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (ECO + 0x48)%Z (mword_of_int 0xb7cd : mword 16)
    (mword_of_int (ECO + 0x48) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)) cdec_b7cd exec_execute_C_J. Qed.

  (* ------------------------- either_copyin -------------------------- *)

  Lemma eci_00 : kernel_text -∗ instr (mword_of_int (ECI + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ECI + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (ECI + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma eci_02 : kernel_text -∗ instr (mword_of_int (ECI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (ECI + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (ECI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma eci_04 : kernel_text -∗ instr (mword_of_int (ECI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (ECI + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (ECI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma eci_06 : kernel_text -∗ instr (mword_of_int (ECI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (ECI + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (ECI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma eci_08 : kernel_text -∗ instr (mword_of_int (ECI + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (ECI + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (ECI + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma eci_0a : kernel_text -∗ instr (mword_of_int (ECI + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (ECI + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (ECI + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma eci_0c : kernel_text -∗ instr (mword_of_int (ECI + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (ECI + 0x0c)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (ECI + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  Lemma eci_0e : kernel_text -∗ instr (mword_of_int (ECI + 0x0e) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (ECI + 0x0e)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (ECI + 0x0e) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma eci_10 : kernel_text -∗ instr (mword_of_int (ECI + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (ECI + 0x10)%Z (mword_of_int 0x8a2a : mword 16)
    (mword_of_int (ECI + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.

  Lemma eci_12 : kernel_text -∗ instr (mword_of_int (ECI + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (ECI + 0x12)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (ECI + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma eci_14 : kernel_text -∗ instr (mword_of_int (ECI + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (ECI + 0x14)%Z (mword_of_int 0x89b2 : mword 16)
    (mword_of_int (ECI + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 19), ADD)) ecdc_89b2 exec_execute_C_MV. Qed.

  Lemma eci_16 : kernel_text -∗ instr (mword_of_int (ECI + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (ECI + 0x16)%Z (mword_of_int 0x8936 : mword 16)
    (mword_of_int (ECI + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)) ecdc_8936 exec_execute_C_MV. Qed.

  Lemma eci_18 : kernel_text -∗ instr (mword_of_int (ECI + 0x18) : mword 64) false (JAL (mword_of_int 2094658 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECI + 0x18)%Z (mword_of_int 0xe42ff0ef : mword 32)
    (mword_of_int (ECI + 0x18) : mword 64) (JAL (mword_of_int 2094658 : mword 21, Regidx (mword_of_int 1))) ecdb_e42ff0ef. Qed.

  Lemma eci_1c : kernel_text -∗ instr (mword_of_int (ECI + 0x1c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)).
  Proof. mk_rvc (ECI + 0x1c)%Z (mword_of_int 0xcc99 : mword 16)
    (mword_of_int (ECI + 0x1c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)) ecdc_cc99 exec_execute_C_BEQZ. Qed.

  Lemma eci_1e : kernel_text -∗ instr (mword_of_int (ECI + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (ECI + 0x1e)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (ECI + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) cdec_86ca exec_execute_C_MV. Qed.

  Lemma eci_20 : kernel_text -∗ instr (mword_of_int (ECI + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (ECI + 0x20)%Z (mword_of_int 0x864e : mword 16)
    (mword_of_int (ECI + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)) cdec_864e exec_execute_C_MV. Qed.

  Lemma eci_22 : kernel_text -∗ instr (mword_of_int (ECI + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (ECI + 0x22)%Z (mword_of_int 0x85d2 : mword 16)
    (mword_of_int (ECI + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)) cdec_85d2 exec_execute_C_MV. Qed.

  Lemma eci_24 : kernel_text -∗ instr (mword_of_int (ECI + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (ECI + 0x24)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (ECI + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma eci_26 : kernel_text -∗ instr (mword_of_int (ECI + 0x26) : mword 64) false (JAL (mword_of_int 2094098 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECI + 0x26)%Z (mword_of_int 0xc12ff0ef : mword 32)
    (mword_of_int (ECI + 0x26) : mword 64) (JAL (mword_of_int 2094098 : mword 21, Regidx (mword_of_int 1))) bdec_c12ff0ef. Qed.

  Lemma eci_2a : kernel_text -∗ instr (mword_of_int (ECI + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (ECI + 0x2a)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (ECI + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma eci_2c : kernel_text -∗ instr (mword_of_int (ECI + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (ECI + 0x2c)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (ECI + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma eci_2e : kernel_text -∗ instr (mword_of_int (ECI + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (ECI + 0x2e)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (ECI + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma eci_30 : kernel_text -∗ instr (mword_of_int (ECI + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (ECI + 0x30)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (ECI + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma eci_32 : kernel_text -∗ instr (mword_of_int (ECI + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (ECI + 0x32)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (ECI + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma eci_34 : kernel_text -∗ instr (mword_of_int (ECI + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (ECI + 0x34)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (ECI + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma eci_36 : kernel_text -∗ instr (mword_of_int (ECI + 0x36) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (ECI + 0x36)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (ECI + 0x36) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma eci_38 : kernel_text -∗ instr (mword_of_int (ECI + 0x38) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (ECI + 0x38)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (ECI + 0x38) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma eci_3a : kernel_text -∗ instr (mword_of_int (ECI + 0x3a) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))).
  Proof. mk_base (ECI + 0x3a)%Z (mword_of_int 0x0009061b : mword 32)
    (mword_of_int (ECI + 0x3a) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))) bdec_0009061b. Qed.

  Lemma eci_3e : kernel_text -∗ instr (mword_of_int (ECI + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (ECI + 0x3e)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (ECI + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ce exec_execute_C_MV. Qed.

  Lemma eci_40 : kernel_text -∗ instr (mword_of_int (ECI + 0x40) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ECI + 0x40)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (ECI + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  Lemma eci_42 : kernel_text -∗ instr (mword_of_int (ECI + 0x42) : mword 64) false (JAL (mword_of_int 2091580 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (ECI + 0x42)%Z (mword_of_int 0xa3dfe0ef : mword 32)
    (mword_of_int (ECI + 0x42) : mword 64) (JAL (mword_of_int 2091580 : mword 21, Regidx (mword_of_int 1))) ecdb_a3dfe0ef. Qed.

  Lemma eci_46 : kernel_text -∗ instr (mword_of_int (ECI + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (ECI + 0x46)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (ECI + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma eci_48 : kernel_text -∗ instr (mword_of_int (ECI + 0x48) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (ECI + 0x48)%Z (mword_of_int 0xb7cd : mword 16)
    (mword_of_int (ECI + 0x48) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)) cdec_b7cd exec_execute_C_J. Qed.

End EitherCopyInstrs.

(* CodeBwrite.v -- the instruction-DECODE layer for xv6's bwrite().
   For EVERY instruction of

     bwrite @ 0x80002c0c .. 0x80002c32   (offsets 0x00 .. 0x24)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([bwi_<off>]).

   bwrite uses the SAME 32-byte frame as filedup, so every prologue/epilogue
   word is already shared in KernelRvcDecode's bit-keyed base; only four words
   are proved here (the [c.addi a0,a0,16] that forms &b->lock, the [c.beqz a0]
   that guards the panic arm, and the two [jal]s).

   The panic tail at +0x26..+0x2e is deliberately ABSENT: [bio_locked] carries
   the sleeplock token and the holder's pid cell, so holdingsleep provably
   returns 1 and the [c.beqz] falls through; a never-executed instruction needs
   no [instr] fact.

     0x00 1101       c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84aa       c.mv  s1,a0          # s1 := b
     0x0c 0541       c.addi a0,a0,16      # a0 := &b->lock
     0x0e 330010ef   jal   ra,holdingsleep
     0x12 c911       c.beqz a0,+0x14      # -> the panic tail; DEAD
     0x14 4585       c.li  a1,1           # write = 1
     0x16 8526       c.mv  a0,s1          # a0 := b
     0x18 32d020ef   jal   ra,virtio_disk_rw
     0x1c 60e2       c.ldsp ra,24(sp)
     0x1e 6442       c.ldsp s0,16(sp)
     0x20 64a2       c.ldsp s1,8(sp)
     0x22 6105       c.addi16sp sp,32
     0x24 8082       c.ret                                                    *)
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
(* Compressed decode facts private to bwrite.                             *)
(* ===================================================================== *)

(* +0x0c  0x0541  c.addi a0,a0,16  -- &b->lock *)
Lemma bwc_0541 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0541 : mword 16)) s
  = Some (C_ADDI (mword_of_int 16, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x12  0xc911  c.beqz a0,+0x14 -- the panic guard *)
Lemma bwc_c911 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc911 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 10, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x0e  jal ra,holdingsleep  (0x80003f4a - 0x80002c1a = 0x1330) *)
Lemma bwdb_330010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x330010ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1330 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x18  jal ra,virtio_disk_rw  (0x80005750 - 0x80002c24 = 0x2b2c) *)
Lemma bwdb_32d020ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x32d020ef : mword 32)) s
  = Some (JAL (mword_of_int 0x2b2c : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BwriteInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma bwi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma bwi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma bwi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma bwi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma bwi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma bwi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma bwi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x0c)%Z (mword_of_int 0x0541 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bwc_0541 exec_execute_C_ADDI. Qed.

  Lemma bwi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x0e) : mword 64) false (JAL (mword_of_int 0x1330 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.bwrite + 0x0e)%Z (mword_of_int 0x330010ef : mword 32)
    (mword_of_int (KernelSyms.bwrite + 0x0e) : mword 64) (JAL (mword_of_int 0x1330 : mword 21, Regidx (mword_of_int 1))) bwdb_330010ef. Qed.

  Lemma bwi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x12) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x12)%Z (mword_of_int 0xc911 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) bwc_c911 exec_execute_C_BEQZ. Qed.

  Lemma bwi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x14)%Z (mword_of_int 0x4585 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4585 exec_execute_C_LI. Qed.

  Lemma bwi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x16)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma bwi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x18) : mword 64) false (JAL (mword_of_int 0x2b2c : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.bwrite + 0x18)%Z (mword_of_int 0x32d020ef : mword 32)
    (mword_of_int (KernelSyms.bwrite + 0x18) : mword 64) (JAL (mword_of_int 0x2b2c : mword 21, Regidx (mword_of_int 1))) bwdb_32d020ef. Qed.

  Lemma bwi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x1c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma bwi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x1e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma bwi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x20)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma bwi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x22) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x22)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x22) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma bwi_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.bwrite + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.bwrite + 0x24)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.bwrite + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End BwriteInstrs.

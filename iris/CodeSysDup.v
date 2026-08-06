(* CodeSysDup.v -- the instruction-DECODE layer for xv6's sys_dup().
   For EVERY instruction of

     sys_dup @ 0x80004bd6 .. 0x80004c20   (offsets 0x00 .. 0x4a)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([sdi_<off>]).

   The 48-byte ra/s0/s1/s2 frame is argfd's own, word for word, so all twelve
   of its push/pop words come from KernelRvcDecode's shared base, as do
   [c.li a0,0] / [c.li a1,0] / [c.li a5,-1] / [c.mv a0,s1] / [c.mv s2,a0] /
   [c.mv a0,a5] / [c.j] / [c.ret].  What is sys_dup's own is the three calls,
   the two [bltz a0] tests, the two accesses to the [struct file *f] local, and
   [c.mv a5,s2].

     0x00 7179       c.addi16sp sp,sp,-48
     0x02 f406       c.sdsp     ra,40(sp)
     0x04 f022       c.sdsp     s0,32(sp)
     0x06 1800       c.addi4spn s0,sp,48
     0x08 fd840613   addi       a2,s0,-40        # &f  (the third argument)
     0x0c 4581       c.li       a1,0             # pfd = 0 -- sys_dup wants no fd
     0x0e 4501       c.li       a0,0             # n   = 0
     0x10 e1fff0ef   jal        ra,argfd
     0x14 57fd       c.li       a5,-1            # the return value, pre-loaded
     0x16 02054363   bltz       a0,+0x26         # -> +0x3c  (argfd failed)
     0x1a ec26       c.sdsp     s1,24(sp)    <-- s1/s2 are saved ONLY here, so
     0x1c e84a       c.sdsp     s2,16(sp)        #  the early exit never pops them
     0x1e fd843483   ld         s1,-40(s0)       # s1 := f
     0x22 8526       c.mv       a0,s1
     0x24 e65ff0ef   jal        ra,fdalloc
     0x28 892a       c.mv       s2,a0            # s2 := fd
     0x2a 57fd       c.li       a5,-1
     0x2c 00054d63   bltz       a0,+0x1a         # -> +0x46 (no free descriptor)
     0x30 8526       c.mv       a0,s1
     0x32 c0eff0ef   jal        ra,filedup       # only NOW does the count rise
     0x36 87ca       c.mv       a5,s2
     0x38 64e2       c.ldsp     s1,24(sp)
     0x3a 6942       c.ldsp     s2,16(sp)
     0x3c 853e       c.mv       a0,a5        <-- ALL THREE arms join here
     0x3e 70a2       c.ldsp     ra,40(sp)
     0x40 7402       c.ldsp     s0,32(sp)
     0x42 6145       c.addi16sp sp,sp,48
     0x44 8082       c.ret
     0x46 64e2       c.ldsp     s1,24(sp)    <-- the fdalloc-failure tail:
     0x48 6942       c.ldsp     s2,16(sp)        #  pop s1/s2, then join
     0x4a bfcd       c.j        -0x0e            # -> +0x3c

   THREE ARMS, ONE EPILOGUE, and the asymmetry that matters for the proof: the
   two callee-saved pushes at +0x1a/+0x1c sit AFTER the first call, so on the
   argfd-failure path slots 3 and 4 of the frame are never written and never
   read.  [callee_saved] still holds on all three paths, but for two different
   reasons. *)
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
Import Defs.
Local Open Scope Z_scope.

Notation SD := KernelSyms.sys_dup.

(* ===================================================================== *)
(* Compressed (2-byte) decode facts sys_dup does not share.               *)
(* ===================================================================== *)

(* +0x36  c.mv a5,s2 *)
Lemma sddc_87ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87ca : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x08  addi a2,s0,-40   (-40 is 0xfd8 in the 12-bit field) *)
Lemma sddb_fd840613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd840613 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                 Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x10  jal ra,argfd     (0x80004be6 -> 0x80004a04 is -482) *)
Lemma sddb_e1fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe1fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096670 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  bltz a0,+0x26 -- argfd returned -1 *)
Lemma sddb_02054363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02054363 : mword 32)) s
  = Some (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0),
                 Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  ld s1,-40(s0) -- reload the file pointer argfd stored *)
Lemma sddb_fd843483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd843483 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                Regidx (mword_of_int 9), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* +0x24  jal ra,fdalloc   (0x80004bfa -> 0x80004a5e is -412) *)
Lemma sddb_e65ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe65ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096740 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x2c  bltz a0,+0x1a -- fdalloc returned -1 *)
Lemma sddb_00054d63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00054d63 : mword 32)) s
  = Some (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0),
                 Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* +0x32  jal ra,filedup   (0x80004c08 -> 0x80004016 is -3058) *)
Lemma sddb_c0eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc0eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094094 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(* The [instr] facts, one per program counter.                            *)
(* ===================================================================== *)
Section SysDupInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma sdi_00 : kernel_text -∗ instr (mword_of_int (SD + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SD + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (SD + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma sdi_02 : kernel_text -∗ instr (mword_of_int (SD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SD + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (SD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma sdi_04 : kernel_text -∗ instr (mword_of_int (SD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SD + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (SD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma sdi_06 : kernel_text -∗ instr (mword_of_int (SD + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SD + 0x06)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (SD + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma sdi_08 : kernel_text -∗ instr (mword_of_int (SD + 0x08) : mword 64) false (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (SD + 0x08)%Z (mword_of_int 0xfd840613 : mword 32)
    (mword_of_int (SD + 0x08) : mword 64) (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)) sddb_fd840613. Qed.

  Lemma sdi_0c : kernel_text -∗ instr (mword_of_int (SD + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (SD + 0x0c)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (SD + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma sdi_0e : kernel_text -∗ instr (mword_of_int (SD + 0x0e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SD + 0x0e)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SD + 0x0e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma sdi_10 : kernel_text -∗ instr (mword_of_int (SD + 0x10) : mword 64) false (JAL (mword_of_int 2096670 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x10)%Z (mword_of_int 0xe1fff0ef : mword 32)
    (mword_of_int (SD + 0x10) : mword 64) (JAL (mword_of_int 2096670 : mword 21, Regidx (mword_of_int 1))) sddb_e1fff0ef. Qed.

  Lemma sdi_14 : kernel_text -∗ instr (mword_of_int (SD + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SD + 0x14)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SD + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma sdi_16 : kernel_text -∗ instr (mword_of_int (SD + 0x16) : mword 64) false (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SD + 0x16)%Z (mword_of_int 0x02054363 : mword 32)
    (mword_of_int (SD + 0x16) : mword 64) (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) sddb_02054363. Qed.

  Lemma sdi_1a : kernel_text -∗ instr (mword_of_int (SD + 0x1a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SD + 0x1a)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (SD + 0x1a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma sdi_1c : kernel_text -∗ instr (mword_of_int (SD + 0x1c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (SD + 0x1c)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (SD + 0x1c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma sdi_1e : kernel_text -∗ instr (mword_of_int (SD + 0x1e) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_base (SD + 0x1e)%Z (mword_of_int 0xfd843483 : mword 32)
    (mword_of_int (SD + 0x1e) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 9), false, 8)) sddb_fd843483. Qed.

  Lemma sdi_22 : kernel_text -∗ instr (mword_of_int (SD + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SD + 0x22)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SD + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma sdi_24 : kernel_text -∗ instr (mword_of_int (SD + 0x24) : mword 64) false (JAL (mword_of_int 2096740 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x24)%Z (mword_of_int 0xe65ff0ef : mword 32)
    (mword_of_int (SD + 0x24) : mword 64) (JAL (mword_of_int 2096740 : mword 21, Regidx (mword_of_int 1))) sddb_e65ff0ef. Qed.

  Lemma sdi_28 : kernel_text -∗ instr (mword_of_int (SD + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (SD + 0x28)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (SD + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma sdi_2a : kernel_text -∗ instr (mword_of_int (SD + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SD + 0x2a)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SD + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma sdi_2c : kernel_text -∗ instr (mword_of_int (SD + 0x2c) : mword 64) false (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SD + 0x2c)%Z (mword_of_int 0x00054d63 : mword 32)
    (mword_of_int (SD + 0x2c) : mword 64) (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) sddb_00054d63. Qed.

  Lemma sdi_30 : kernel_text -∗ instr (mword_of_int (SD + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SD + 0x30)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SD + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma sdi_32 : kernel_text -∗ instr (mword_of_int (SD + 0x32) : mword 64) false (JAL (mword_of_int 2094094 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SD + 0x32)%Z (mword_of_int 0xc0eff0ef : mword 32)
    (mword_of_int (SD + 0x32) : mword 64) (JAL (mword_of_int 2094094 : mword 21, Regidx (mword_of_int 1))) sddb_c0eff0ef. Qed.

  Lemma sdi_36 : kernel_text -∗ instr (mword_of_int (SD + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SD + 0x36)%Z (mword_of_int 0x87ca : mword 16)
    (mword_of_int (SD + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 15), ADD)) sddc_87ca exec_execute_C_MV. Qed.

  Lemma sdi_38 : kernel_text -∗ instr (mword_of_int (SD + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SD + 0x38)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (SD + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma sdi_3a : kernel_text -∗ instr (mword_of_int (SD + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SD + 0x3a)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (SD + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma sdi_3c : kernel_text -∗ instr (mword_of_int (SD + 0x3c) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SD + 0x3c)%Z (mword_of_int 0x853e : mword 16)
    (mword_of_int (SD + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)) cdec_853e exec_execute_C_MV. Qed.

  Lemma sdi_3e : kernel_text -∗ instr (mword_of_int (SD + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SD + 0x3e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (SD + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma sdi_40 : kernel_text -∗ instr (mword_of_int (SD + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SD + 0x40)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (SD + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma sdi_42 : kernel_text -∗ instr (mword_of_int (SD + 0x42) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SD + 0x42)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (SD + 0x42) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma sdi_44 : kernel_text -∗ instr (mword_of_int (SD + 0x44) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SD + 0x44)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SD + 0x44) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma sdi_46 : kernel_text -∗ instr (mword_of_int (SD + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SD + 0x46)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (SD + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma sdi_48 : kernel_text -∗ instr (mword_of_int (SD + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SD + 0x48)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (SD + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma sdi_4a : kernel_text -∗ instr (mword_of_int (SD + 0x4a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SD + 0x4a)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (SD + 0x4a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

End SysDupInstrs.

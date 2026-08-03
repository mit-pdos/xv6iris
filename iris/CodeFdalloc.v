(* CodeFdalloc.v -- the instruction-DECODE layer for xv6's fdalloc().
   For EVERY instruction of

     fdalloc @ 0x80004a5e .. 0x80004a9c   (offsets 0x00 .. 0x3e)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fdi_<off>]).

   The 32-byte ra/s0/s1 frame is argint's / sys_uptime's, so its nine words
   come from KernelRvcDecode's shared base, as do [c.mv s1,a0], [c.mv a2,a0],
   [c.li a0,0], [c.li a0,-1] and [c.ret]; [addi a5,a5,208] -- the same
   [p->ofile] displacement sys_close and argfd use -- is KernelBaseDecode's
   [bdec_0d078793].  What is fdalloc's own is the SCAN: the four words of the
   loop body plus the two that set it up, and the three of the install arm.

     0x00 1101       c.addi     sp,sp,-32
     0x02 ec06       c.sdsp     ra,24(sp)
     0x04 e822       c.sdsp     s0,16(sp)
     0x06 e426       c.sdsp     s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84aa       c.mv       s1,a0            # s1 := f (callee-saved)
     0x0c e9bfc0ef   jal        ra,myproc
     0x10 862a       c.mv       a2,a0            # a2 := p  (never touched again
     0x12 0d050793   addi       a5,a0,208        #  until the install arm)
     0x16 4501       c.li       a0,0             # fd := 0
     0x18 46c1       c.li       a3,16            # NOFILE
     0x1a 6398       c.ld       a4,0(a5)     <-- LOOP HEAD
     0x1c cb19       c.beqz     a4,+0x16         # -> +0x32
     0x1e 2505       c.addiw    a0,a0,1
     0x20 07a1       c.addi     a5,a5,8
     0x22 fed51ce3   bne        a0,a3,-0x0a      # -> +0x1a
     0x26 557d       c.li       a0,-1        <-- table full
     0x28 60e2       c.ldsp     ra,24(sp)    <-- BOTH arms join here
     0x2a 6442       c.ldsp     s0,16(sp)
     0x2c 64a2       c.ldsp     s1,8(sp)
     0x2e 6105       c.addi16sp sp,32
     0x30 8082       c.ret
     0x32 00351793   slli       a5,a0,0x3    <-- install arm
     0x36 0d078793   addi       a5,a5,208
     0x3a 963e       c.add      a2,a2,a5
     0x3c e204       c.sd       s1,0(a2)
     0x3e b7ed       c.j        -0x16            # -> +0x28

   As in argint / fetchaddr the frame is ASYMMETRIC: the push is a plain
   [c.addi sp,-32] but the pop is [c.addi16sp sp,32], so the two ends take
   different WP leaves. *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed words fdalloc does not share with any other function.       *)
(* ===================================================================== *)

(* +0x18  c.li a3,16 *)
Lemma fddc_46c1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x46c1 : mword 16)) s
  = Some (C_LI (mword_of_int 16, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* +0x1c  c.beqz a4,+0x16 *)
Lemma fddc_cb19 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb19 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 11, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1e  c.addiw a0,a0,1 *)
Lemma fddc_2505 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2505 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.



(* +0x3c  c.sd s1,0(a2) *)
Lemma fddc_e204 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe204 : mword 16)) s
  = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 4), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* ---- the two compressed load/store ASTs, in the shape a WP leaf takes ---- *)

Lemma fdexec_ld0_a5_a4 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma fdexec_sd0_a2_s1 s :
  exec (execute (C_SD (mword_of_int 0, Cregidx (mword_of_int 4), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 12), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x0c  jal ra,myproc  (0x80004a6a -> 0x80001904 is -12646; the 21-bit
   field is 2^21 - 12646 = 2084506) *)
Lemma fddb_e9bfc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe9bfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084506 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  addi a5,a0,208  -- &p->ofile[0] *)
Lemma fddb_0d050793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0d050793 : mword 32)) s
  = Some (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x22  bne a0,a3,-0x0a  (the 13-bit field is 2^13 - 8 = 8184) *)
Lemma fddb_fed51ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfed51ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 10), BNE), s).
Proof. decode_bridge_ms. Qed.

(* +0x32  slli a5,a0,0x3 *)
Lemma fddb_00351793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00351793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FdallocInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FD := KernelSyms.fdalloc.

  Lemma fdi_00 : kernel_text -∗ instr (mword_of_int (FD + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FD + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (FD + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma fdi_02 : kernel_text -∗ instr (mword_of_int (FD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FD + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (FD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma fdi_04 : kernel_text -∗ instr (mword_of_int (FD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FD + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (FD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma fdi_06 : kernel_text -∗ instr (mword_of_int (FD + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FD + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (FD + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma fdi_08 : kernel_text -∗ instr (mword_of_int (FD + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FD + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (FD + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma fdi_0a : kernel_text -∗ instr (mword_of_int (FD + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FD + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (FD + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma fdi_0c : kernel_text -∗ instr (mword_of_int (FD + 0x0c) : mword 64) false (JAL (mword_of_int 2084506 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FD + 0x0c)%Z (mword_of_int 0xe9bfc0ef : mword 32)
    (mword_of_int (FD + 0x0c) : mword 64) (JAL (mword_of_int 2084506 : mword 21, Regidx (mword_of_int 1))) fddb_e9bfc0ef. Qed.

  Lemma fdi_10 : kernel_text -∗ instr (mword_of_int (FD + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (FD + 0x10)%Z (mword_of_int 0x862a : mword 16)
    (mword_of_int (FD + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 12), ADD)) cdec_862a exec_execute_C_MV. Qed.

  Lemma fdi_12 : kernel_text -∗ instr (mword_of_int (FD + 0x12) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (FD + 0x12)%Z (mword_of_int 0x0d050793 : mword 32)
    (mword_of_int (FD + 0x12) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)) fddb_0d050793. Qed.

  Lemma fdi_16 : kernel_text -∗ instr (mword_of_int (FD + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (FD + 0x16)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (FD + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma fdi_18 : kernel_text -∗ instr (mword_of_int (FD + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (FD + 0x18)%Z (mword_of_int 0x46c1 : mword 16)
    (mword_of_int (FD + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) fddc_46c1 exec_execute_C_LI. Qed.

  Lemma fdi_1a : kernel_text -∗ instr (mword_of_int (FD + 0x1a) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (FD + 0x1a)%Z (mword_of_int 0x6398 : mword 16)
    (mword_of_int (FD + 0x1a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) cdec_6398 fdexec_ld0_a5_a4. Qed.

  Lemma fdi_1c : kernel_text -∗ instr (mword_of_int (FD + 0x1c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).
  Proof. mk_rvc (FD + 0x1c)%Z (mword_of_int 0xcb19 : mword 16)
    (mword_of_int (FD + 0x1c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 11 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) fddc_cb19 exec_execute_C_BEQZ. Qed.

  Lemma fdi_1e : kernel_text -∗ instr (mword_of_int (FD + 0x1e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))).
  Proof. mk_rvc (FD + 0x1e)%Z (mword_of_int 0x2505 : mword 16)
    (mword_of_int (FD + 0x1e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))) fddc_2505 exec_execute_C_ADDIW. Qed.

  Lemma fdi_20 : kernel_text -∗ instr (mword_of_int (FD + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (FD + 0x20)%Z (mword_of_int 0x07a1 : mword 16)
    (mword_of_int (FD + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cdec_07a1 exec_execute_C_ADDI. Qed.

  Lemma fdi_22 : kernel_text -∗ instr (mword_of_int (FD + 0x22) : mword 64) false (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 10), BNE)).
  Proof. mk_base (FD + 0x22)%Z (mword_of_int 0xfed51ce3 : mword 32)
    (mword_of_int (FD + 0x22) : mword 64) (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 10), BNE)) fddb_fed51ce3. Qed.

  Lemma fdi_26 : kernel_text -∗ instr (mword_of_int (FD + 0x26) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (FD + 0x26)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (FD + 0x26) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma fdi_28 : kernel_text -∗ instr (mword_of_int (FD + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FD + 0x28)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (FD + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma fdi_2a : kernel_text -∗ instr (mword_of_int (FD + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FD + 0x2a)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (FD + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma fdi_2c : kernel_text -∗ instr (mword_of_int (FD + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FD + 0x2c)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (FD + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma fdi_2e : kernel_text -∗ instr (mword_of_int (FD + 0x2e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FD + 0x2e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (FD + 0x2e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma fdi_30 : kernel_text -∗ instr (mword_of_int (FD + 0x30) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FD + 0x30)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FD + 0x30) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma fdi_32 : kernel_text -∗ instr (mword_of_int (FD + 0x32) : mword 64) false (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (FD + 0x32)%Z (mword_of_int 0x00351793 : mword 32)
    (mword_of_int (FD + 0x32) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI)) fddb_00351793. Qed.

  Lemma fdi_36 : kernel_text -∗ instr (mword_of_int (FD + 0x36) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (FD + 0x36)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (FD + 0x36) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  Lemma fdi_3a : kernel_text -∗ instr (mword_of_int (FD + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (FD + 0x3a)%Z (mword_of_int 0x963e : mword 16)
    (mword_of_int (FD + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)) cdec_963e exec_execute_C_ADD. Qed.

  Lemma fdi_3c : kernel_text -∗ instr (mword_of_int (FD + 0x3c) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 12), 8)).
  Proof. mk_rvc (FD + 0x3c)%Z (mword_of_int 0xe204 : mword 16)
    (mword_of_int (FD + 0x3c) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 12), 8)) fddc_e204 fdexec_sd0_a2_s1. Qed.

  Lemma fdi_3e : kernel_text -∗ instr (mword_of_int (FD + 0x3e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FD + 0x3e)%Z (mword_of_int 0xb7ed : mword 16)
    (mword_of_int (FD + 0x3e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2037 : mword 11) ('b"0")), zreg)) cdec_b7ed exec_execute_C_J. Qed.

End FdallocInstrs.

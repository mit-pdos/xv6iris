(* WpFreeDescDecode.v -- the instruction-DECODE layer for xv6's free_desc().
   For every instruction of

     free_desc @ 0x80005512 .. 0x8000556e   (offsets 0x00 .. 0x5c)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fdi_<off>]).

   free_desc's 16-byte frame prologue/epilogue (c.addi sp,-16 / c.sdsp ra,8 /
   c.sdsp s0,0 / c.addi4spn s0,sp,16 ... c.ldsp ra,8 / c.ldsp s0,0 /
   c.addi sp,16 / c.ret) is byte-identical to clockintr's and mycpu's, so
   those decodes reuse the shared bit-keyed [cdec_<word>] templates of
   KernelRvcDecode.v; so does the [c.add a5,a5,a0] pointer arithmetic
   ([cdec_97aa]).  Everything else is free_desc's own.

     0x00 1141        c.addi sp,-16
     0x02 e406        c.sdsp ra,8(sp)
     0x04 e022        c.sdsp s0,0(sp)
     0x06 0800        c.addi4spn s0,sp,16
     0x08 479d        c.li  a5,7                # NUM - 1
     0x0a 04a7ca63    blt   a5,a0,+0x54         # i > 7 -> panic("free_desc 1")
     0x0e 0001e797    auipc a5,0x1e
     0x12 ef878793    addi  a5,a5,-264          # a5 = &disk
     0x16 97aa        c.add a5,a5,a0
     0x18 0187c783    lbu   a5,24(a5)           # disk.free[i]
     0x1c e7b9        c.bnez a5,+0x4e           # set -> panic("free_desc 2")
     0x1e 00451693    slli  a3,a0,0x4           # a3 = 16*i
     0x22 0001e797    auipc a5,0x1e
     0x26 ee478793    addi  a5,a5,-284          # a5 = &disk
     0x2a 6398        c.ld  a4,0(a5)            # a4 = disk.desc  (the page)
     0x2c 9736        c.add a4,a4,a3            # a4 = &disk.desc[i]
     0x2e 00073023    sd    zero,0(a4)          # .addr  = 0
     0x32 6398        c.ld  a4,0(a5)
     0x34 9736        c.add a4,a4,a3
     0x36 00072423    sw    zero,8(a4)          # .len   = 0
     0x3a 00071623    sh    zero,12(a4)         # .flags = 0
     0x3e 00071723    sh    zero,14(a4)         # .next  = 0
     0x42 97aa        c.add a5,a5,a0
     0x44 4705        c.li  a4,1
     0x46 00e78c23    sb    a4,24(a5)           # disk.free[i] = 1
     0x4a 0001e517    auipc a0,0x1e
     0x4e ed450513    addi  a0,a0,-300          # a0 = &disk.free[0]
     0x52 9effc0ef    jal   ra,wakeup
     0x56 60a2        c.ldsp ra,8(sp)
     0x58 6402        c.ldsp s0,0(sp)
     0x5a 0141        c.addi sp,16
     0x5c 8082        c.ret

   The two panic tails at +0x5e..+0x66 and +0x6a..+0x72 are DEAD: the spec's
   [i < 8] refutes the [blt] and the caller's [disk.free[i] = 0] cell refutes
   the [c.bnez], so no [instr] fact is needed for them.                      *)
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

Notation FD := KernelSyms.free_desc.

(* ===================================================================== *)
(* Compressed words free_desc does not share with any other function.      *)
(* ===================================================================== *)

(* +0x08  c.li a5,7 *)
Lemma fdc_479d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x479d : mword 16)) s
  = Some (C_LI (mword_of_int 7, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1c  c.bnez a5,+0x4e  (0x4e = 78 = 2 * 39) *)
Lemma fdc_e7b9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe7b9 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 39, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x2a / +0x32  c.ld a4,0(a5) *)
Lemma fdc_6398 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6398 : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma fdc_exec_6398 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x2c / +0x34  c.add a4,a4,a3 *)
Lemma fdc_9736 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9736 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x44  c.li a4,1 *)
Lemma fdc_4705 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4705 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x0a  blt a5,a0,+0x54 -- the [i >= NUM] test *)
Lemma fdb_04a7ca63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04a7ca63 : mword 32)) s
  = Some (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 10), Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

(* +0x0e / +0x22  auipc a5,0x1e *)
Lemma fdb_0001e797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e797 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  addi a5,a5,-264 *)
Lemma fdb_ef878793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xef878793 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xef8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x18  lbu a5,24(a5) -- disk.free[i] *)
Lemma fdb_0187c783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0187c783 : mword 32)) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  slli a3,a0,0x4 *)
Lemma fdb_00451693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00451693 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* +0x26  addi a5,a5,-284 *)
Lemma fdb_ee478793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xee478793 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xee4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x2e  sd zero,0(a4) *)
Lemma fdb_00073023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00073023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8), s).
Proof. decode_bridge_ms. Qed.

(* +0x36  sw zero,8(a4) *)
Lemma fdb_00072423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00072423 : mword 32)) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x3a  sh zero,12(a4) *)
Lemma fdb_00071623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00071623 : mword 32)) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x3e  sh zero,14(a4) *)
Lemma fdb_00071723 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00071723 : mword 32)) s
  = Some (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2), s).
Proof. decode_bridge_ms. Qed.

(* +0x46  sb a4,24(a5) -- disk.free[i] = 1 *)
Lemma fdb_00e78c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e78c23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* +0x4e  addi a0,a0,-300 -- a0 = &disk.free[0] *)
Lemma fdb_ed450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xed450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xed4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x52  jal ra,wakeup  (0x80005564 -> 0x80001f52 is -13842; 2^21 - 13842) *)
Lemma fdb_9effc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9effc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083310 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FreeDescInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- prologue: 16-byte frame, saves ra/s0 (shared cdec_* decodes) ---- *)
  Lemma fdi_00 : kernel_text -∗ instr (mword_of_int (FD + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FD + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (FD + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma fdi_02 : kernel_text -∗ instr (mword_of_int (FD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FD + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (FD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma fdi_04 : kernel_text -∗ instr (mword_of_int (FD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FD + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (FD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma fdi_06 : kernel_text -∗ instr (mword_of_int (FD + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FD + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (FD + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- the [i >= NUM] test ---- *)
  Lemma fdi_08 : kernel_text -∗ instr (mword_of_int (FD + 0x08) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (FD + 0x08)%Z (mword_of_int 0x479d : mword 16)
    (mword_of_int (FD + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) fdc_479d exec_execute_C_LI. Qed.

  Lemma fdi_0a : kernel_text -∗ instr (mword_of_int (FD + 0x0a) : mword 64) false (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 10), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (FD + 0x0a)%Z (mword_of_int 0x04a7ca63 : mword 32)
    (mword_of_int (FD + 0x0a) : mword 64) (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 10), Regidx (mword_of_int 15), BLT)) fdb_04a7ca63. Qed.

  (* ---- a5 := &disk ; read disk.free[i] ---- *)
  Lemma fdi_0e : kernel_text -∗ instr (mword_of_int (FD + 0x0e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (FD + 0x0e)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (FD + 0x0e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) fdb_0001e797. Qed.

  Lemma fdi_12 : kernel_text -∗ instr (mword_of_int (FD + 0x12) : mword 64) false (ITYPE (mword_of_int 0xef8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (FD + 0x12)%Z (mword_of_int 0xef878793 : mword 32)
    (mword_of_int (FD + 0x12) : mword 64) (ITYPE (mword_of_int 0xef8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) fdb_ef878793. Qed.

  Lemma fdi_16 : kernel_text -∗ instr (mword_of_int (FD + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (FD + 0x16)%Z (mword_of_int 0x97aa : mword 16)
    (mword_of_int (FD + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97aa exec_execute_C_ADD. Qed.

  Lemma fdi_18 : kernel_text -∗ instr (mword_of_int (FD + 0x18) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (FD + 0x18)%Z (mword_of_int 0x0187c783 : mword 32)
    (mword_of_int (FD + 0x18) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)) fdb_0187c783. Qed.

  Lemma fdi_1c : kernel_text -∗ instr (mword_of_int (FD + 0x1c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 39 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (FD + 0x1c)%Z (mword_of_int 0xe7b9 : mword 16)
    (mword_of_int (FD + 0x1c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 39 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) fdc_e7b9 exec_execute_C_BNEZ. Qed.

  (* ---- clear descriptor entry i ---- *)
  Lemma fdi_1e : kernel_text -∗ instr (mword_of_int (FD + 0x1e) : mword 64) false (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI)).
  Proof. mk_base (FD + 0x1e)%Z (mword_of_int 0x00451693 : mword 32)
    (mword_of_int (FD + 0x1e) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 13), SLLI)) fdb_00451693. Qed.

  Lemma fdi_22 : kernel_text -∗ instr (mword_of_int (FD + 0x22) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (FD + 0x22)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (FD + 0x22) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) fdb_0001e797. Qed.

  Lemma fdi_26 : kernel_text -∗ instr (mword_of_int (FD + 0x26) : mword 64) false (ITYPE (mword_of_int 0xee4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (FD + 0x26)%Z (mword_of_int 0xee478793 : mword 32)
    (mword_of_int (FD + 0x26) : mword 64) (ITYPE (mword_of_int 0xee4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) fdb_ee478793. Qed.

  Lemma fdi_2a : kernel_text -∗ instr (mword_of_int (FD + 0x2a) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (FD + 0x2a)%Z (mword_of_int 0x6398 : mword 16)
    (mword_of_int (FD + 0x2a) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) fdc_6398 fdc_exec_6398. Qed.

  Lemma fdi_2c : kernel_text -∗ instr (mword_of_int (FD + 0x2c) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (FD + 0x2c)%Z (mword_of_int 0x9736 : mword 16)
    (mword_of_int (FD + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) fdc_9736 exec_execute_C_ADD. Qed.

  Lemma fdi_2e : kernel_text -∗ instr (mword_of_int (FD + 0x2e) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8)).
  Proof. mk_base (FD + 0x2e)%Z (mword_of_int 0x00073023 : mword 32)
    (mword_of_int (FD + 0x2e) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8)) fdb_00073023. Qed.

  Lemma fdi_32 : kernel_text -∗ instr (mword_of_int (FD + 0x32) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (FD + 0x32)%Z (mword_of_int 0x6398 : mword 16)
    (mword_of_int (FD + 0x32) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) fdc_6398 fdc_exec_6398. Qed.

  Lemma fdi_34 : kernel_text -∗ instr (mword_of_int (FD + 0x34) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (FD + 0x34)%Z (mword_of_int 0x9736 : mword 16)
    (mword_of_int (FD + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) fdc_9736 exec_execute_C_ADD. Qed.

  Lemma fdi_36 : kernel_text -∗ instr (mword_of_int (FD + 0x36) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (FD + 0x36)%Z (mword_of_int 0x00072423 : mword 32)
    (mword_of_int (FD + 0x36) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 4)) fdb_00072423. Qed.

  Lemma fdi_3a : kernel_text -∗ instr (mword_of_int (FD + 0x3a) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (FD + 0x3a)%Z (mword_of_int 0x00071623 : mword 32)
    (mword_of_int (FD + 0x3a) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)) fdb_00071623. Qed.

  Lemma fdi_3e : kernel_text -∗ instr (mword_of_int (FD + 0x3e) : mword 64) false (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)).
  Proof. mk_base (FD + 0x3e)%Z (mword_of_int 0x00071723 : mword 32)
    (mword_of_int (FD + 0x3e) : mword 64) (STORE (mword_of_int 14 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 2)) fdb_00071723. Qed.

  (* ---- disk.free[i] = 1 ; wakeup(&disk.free[0]) ---- *)
  Lemma fdi_42 : kernel_text -∗ instr (mword_of_int (FD + 0x42) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (FD + 0x42)%Z (mword_of_int 0x97aa : mword 16)
    (mword_of_int (FD + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97aa exec_execute_C_ADD. Qed.

  Lemma fdi_44 : kernel_text -∗ instr (mword_of_int (FD + 0x44) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (FD + 0x44)%Z (mword_of_int 0x4705 : mword 16)
    (mword_of_int (FD + 0x44) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) fdc_4705 exec_execute_C_LI. Qed.

  Lemma fdi_46 : kernel_text -∗ instr (mword_of_int (FD + 0x46) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (FD + 0x46)%Z (mword_of_int 0x00e78c23 : mword 32)
    (mword_of_int (FD + 0x46) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)) fdb_00e78c23. Qed.

  Lemma fdi_4a : kernel_text -∗ instr (mword_of_int (FD + 0x4a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FD + 0x4a)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FD + 0x4a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fdi_4e : kernel_text -∗ instr (mword_of_int (FD + 0x4e) : mword 64) false (ITYPE (mword_of_int 0xed4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FD + 0x4e)%Z (mword_of_int 0xed450513 : mword 32)
    (mword_of_int (FD + 0x4e) : mword 64) (ITYPE (mword_of_int 0xed4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fdb_ed450513. Qed.

  Lemma fdi_52 : kernel_text -∗ instr (mword_of_int (FD + 0x52) : mword 64) false (JAL (mword_of_int 2083310 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FD + 0x52)%Z (mword_of_int 0x9effc0ef : mword 32)
    (mword_of_int (FD + 0x52) : mword 64) (JAL (mword_of_int 2083310 : mword 21, Regidx (mword_of_int 1))) fdb_9effc0ef. Qed.

  (* ---- epilogue ---- *)
  Lemma fdi_56 : kernel_text -∗ instr (mword_of_int (FD + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FD + 0x56)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (FD + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma fdi_58 : kernel_text -∗ instr (mword_of_int (FD + 0x58) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FD + 0x58)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (FD + 0x58) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma fdi_5a : kernel_text -∗ instr (mword_of_int (FD + 0x5a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FD + 0x5a)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (FD + 0x5a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma fdi_5c : kernel_text -∗ instr (mword_of_int (FD + 0x5c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FD + 0x5c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FD + 0x5c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End FreeDescInstrs.

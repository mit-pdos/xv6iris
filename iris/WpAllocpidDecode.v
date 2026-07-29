(* WpAllocpidDecode.v -- the instruction-DECODE layer for xv6's allocpid().
   For every instruction of

     allocpid @ 0x800019d0 .. 0x80001a0c   (offsets 0x00 .. 0x3c)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([apdi_<off>]).

     0x00 1101       c.addi     sp,sp,-32
     0x02 ec06       c.sdsp     ra,24(sp)
     0x04 e822       c.sdsp     s0,16(sp)
     0x06 e426       c.sdsp     s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 00011517   auipc      a0,0x11          # a0 := &pid_lock
     0x0e 96e50513   addi       a0,a0,-1682
     0x12 a26ff0ef   jal        ra,acquire
     0x16 00009797   auipc      a5,0x9           # a5 := &nextpid
     0x1a 80e78793   addi       a5,a5,-2034
     0x1e 4384       c.lw       s1,0(a5)         # pid = nextpid
     0x20 0014871b   addiw      a4,s1,1
     0x24 c398       c.sw       a4,0(a5)         # nextpid = pid + 1
     0x26 00011517   auipc      a0,0x11          # a0 := &pid_lock (again)
     0x2a 95250513   addi       a0,a0,-1710
     0x2e a92ff0ef   jal        ra,release
     0x32 8526       c.mv       a0,s1
     0x34 60e2       c.ldsp     ra,24(sp)
     0x36 6442       c.ldsp     s0,16(sp)
     0x38 64a2       c.ldsp     s1,8(sp)
     0x3a 6105       c.addi16sp sp,32
     0x3c 8082       c.ret

   The 32-byte three-register frame and [c.mv a0,s1] come from
   KernelRvcDecode's shared base; [auipc a0,0x11] is the same relocation
   procinit, kalloc, proc_mapstacks and wakeup all use to reach the proc
   area, so it is KernelBaseDecode's [bdec_00011517]. *)
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
(* allocpid's own compressed words.                                       *)
(* ===================================================================== *)

(* +0x1e  c.lw s1,0(a5)  -- nextpid *)
Lemma apidc_4384 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4384 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x24  c.sw a4,0(a5) *)
Lemma apidc_c398 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc398 : mword 16)) s
  = Some (C_SW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* their leaf-form expansions *)
Lemma apidexec_lw0_a5_s1 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apidexec_sw0_a5_a4 s :
  exec (execute (C_SW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x0a / +0x26  auipc a0,0x11 *)
Lemma apidb_00011517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011517 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x0e  addi a0,a0,-1682  (2^12 - 1682 = 2414) *)
Lemma apidb_96e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x96e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  jal ra,acquire  (0x800019e2 -> 0x80000c08 is -3546) *)
Lemma apidb_a26ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa26ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093606 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  auipc a5,0x9 *)
Lemma apidb_00009797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00009797 : mword 32)) s
  = Some (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  addi a5,a5,-2034  (2^12 - 2034 = 2062) *)
Lemma apidb_80e78793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x80e78793 : mword 32)) s
  = Some (ITYPE (mword_of_int 2062 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x20  addiw a4,s1,1 *)
Lemma apidb_0014871b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0014871b : mword 32)) s
  = Some (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14)), s).
Proof. decode_bridge_ms. Qed.

(* +0x2a  addi a0,a0,-1710  (2^12 - 1710 = 2386) *)
Lemma apidb_95250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x95250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2386 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x2e  jal ra,release  (0x800019fe -> 0x80000c90 is -3438) *)
Lemma apidb_a92ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa92ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093714 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section AllocpidInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation API := KernelSyms.allocpid.

  Lemma apdi_00 : kernel_text -∗ instr (mword_of_int (API + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (API + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (API + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma apdi_02 : kernel_text -∗ instr (mword_of_int (API + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (API + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (API + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma apdi_04 : kernel_text -∗ instr (mword_of_int (API + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (API + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (API + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma apdi_06 : kernel_text -∗ instr (mword_of_int (API + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (API + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (API + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma apdi_08 : kernel_text -∗ instr (mword_of_int (API + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (API + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (API + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma apdi_0a : kernel_text -∗ instr (mword_of_int (API + 0x0a) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (API + 0x0a)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (API + 0x0a) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) apidb_00011517. Qed.

  Lemma apdi_0e : kernel_text -∗ instr (mword_of_int (API + 0x0e) : mword 64) false (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (API + 0x0e)%Z (mword_of_int 0x96e50513 : mword 32)
    (mword_of_int (API + 0x0e) : mword 64) (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) apidb_96e50513. Qed.

  Lemma apdi_12 : kernel_text -∗ instr (mword_of_int (API + 0x12) : mword 64) false (JAL (mword_of_int 2093606 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (API + 0x12)%Z (mword_of_int 0xa26ff0ef : mword 32)
    (mword_of_int (API + 0x12) : mword 64) (JAL (mword_of_int 2093606 : mword 21, Regidx (mword_of_int 1))) apidb_a26ff0ef. Qed.

  Lemma apdi_16 : kernel_text -∗ instr (mword_of_int (API + 0x16) : mword 64) false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (API + 0x16)%Z (mword_of_int 0x00009797 : mword 32)
    (mword_of_int (API + 0x16) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)) apidb_00009797. Qed.

  Lemma apdi_1a : kernel_text -∗ instr (mword_of_int (API + 0x1a) : mword 64) false (ITYPE (mword_of_int 2062 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (API + 0x1a)%Z (mword_of_int 0x80e78793 : mword 32)
    (mword_of_int (API + 0x1a) : mword 64) (ITYPE (mword_of_int 2062 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) apidb_80e78793. Qed.

  Lemma apdi_1e : kernel_text -∗ instr (mword_of_int (API + 0x1e) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)).
  Proof. mk_rvc (API + 0x1e)%Z (mword_of_int 0x4384 : mword 16)
    (mword_of_int (API + 0x1e) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)) apidc_4384 apidexec_lw0_a5_s1. Qed.

  Lemma apdi_20 : kernel_text -∗ instr (mword_of_int (API + 0x20) : mword 64) false (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14))).
  Proof. mk_base (API + 0x20)%Z (mword_of_int 0x0014871b : mword 32)
    (mword_of_int (API + 0x20) : mword 64) (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14))) apidb_0014871b. Qed.

  Lemma apdi_24 : kernel_text -∗ instr (mword_of_int (API + 0x24) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (API + 0x24)%Z (mword_of_int 0xc398 : mword 16)
    (mword_of_int (API + 0x24) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) apidc_c398 apidexec_sw0_a5_a4. Qed.

  Lemma apdi_26 : kernel_text -∗ instr (mword_of_int (API + 0x26) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (API + 0x26)%Z (mword_of_int 0x00011517 : mword 32)
    (mword_of_int (API + 0x26) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 10), AUIPC)) apidb_00011517. Qed.

  Lemma apdi_2a : kernel_text -∗ instr (mword_of_int (API + 0x2a) : mword 64) false (ITYPE (mword_of_int 2386 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (API + 0x2a)%Z (mword_of_int 0x95250513 : mword 32)
    (mword_of_int (API + 0x2a) : mword 64) (ITYPE (mword_of_int 2386 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) apidb_95250513. Qed.

  Lemma apdi_2e : kernel_text -∗ instr (mword_of_int (API + 0x2e) : mword 64) false (JAL (mword_of_int 2093714 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (API + 0x2e)%Z (mword_of_int 0xa92ff0ef : mword 32)
    (mword_of_int (API + 0x2e) : mword 64) (JAL (mword_of_int 2093714 : mword 21, Regidx (mword_of_int 1))) apidb_a92ff0ef. Qed.

  Lemma apdi_32 : kernel_text -∗ instr (mword_of_int (API + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (API + 0x32)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (API + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma apdi_34 : kernel_text -∗ instr (mword_of_int (API + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (API + 0x34)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (API + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma apdi_36 : kernel_text -∗ instr (mword_of_int (API + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (API + 0x36)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (API + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma apdi_38 : kernel_text -∗ instr (mword_of_int (API + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (API + 0x38)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (API + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma apdi_3a : kernel_text -∗ instr (mword_of_int (API + 0x3a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (API + 0x3a)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (API + 0x3a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma apdi_3c : kernel_text -∗ instr (mword_of_int (API + 0x3c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (API + 0x3c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (API + 0x3c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End AllocpidInstrs.

(* CodeKkill.v -- the machine code of kkill(): the decode templates for the
   words this function alone uses, and the [instr] constructors for its
   instruction addresses.  Consumed by ProofKkill.v.

     +0x00  7179      c.addi16sp sp,sp,-48
     +0x02  f406      c.sdsp     ra,40(sp)
     +0x04  f022      c.sdsp     s0,32(sp)
     +0x06  ec26      c.sdsp     s1,24(sp)
     +0x08  e84a      c.sdsp     s2,16(sp)
     +0x0a  e44e      c.sdsp     s3,8(sp)
     +0x0c  1800      c.addi4spn s0,sp,48
     +0x0e  892a      c.mv       s2,a0            s2 := pid
     +0x10  00010497  auipc      s1,0x10
     +0x14  6b048493  addi       s1,s1,1712       s1 := &proc[0]
     +0x18  00016997  auipc      s3,0x16
     +0x1c  0a898993  addi       s3,s3,168        s3 := &proc[NPROC]
     +0x20  8526      c.mv       a0,s1            <-- LOOP HEAD
     +0x22  b2ffe0ef  jal        ra,acquire
     +0x26  589c      c.lw       a5,48(s1)        a5 := p->pid
     +0x28  01278b63  beq        a5,s2,+0x3e
     +0x2c  8526      c.mv       a0,s1
     +0x2e  babfe0ef  jal        ra,release
     +0x32  16848493  addi       s1,s1,360        p++
     +0x36  ff3495e3  bne        s1,s3,+0x20
     +0x3a  557d      c.li       a0,-1
     +0x3c  a819      c.j        +0x52
     +0x3e  4785      c.li       a5,1             <-- MATCH ARM
     +0x40  d49c      c.sw       a5,40(s1)        p->killed = 1
     +0x42  4c98      c.lw       a4,24(s1)        a4 := p->state
     +0x44  4789      c.li       a5,2
     +0x46  00f70d63  beq        a4,a5,+0x60
     +0x4a  8526      c.mv       a0,s1            <-- SHARED release-and-0
     +0x4c  b8dfe0ef  jal        ra,release
     +0x50  4501      c.li       a0,0
     +0x52  70a2      c.ldsp     ra,40(sp)        <-- EPILOGUE
     +0x54  7402      c.ldsp     s0,32(sp)
     +0x56  64e2      c.ldsp     s1,24(sp)
     +0x58  6942      c.ldsp     s2,16(sp)
     +0x5a  69a2      c.ldsp     s3,8(sp)
     +0x5c  6145      c.addi16sp sp,sp,48
     +0x5e  8082      c.ret
     +0x60  478d      c.li       a5,3             <-- WAKE ARM
     +0x62  cc9c      c.sw       a5,24(s1)        p->state = RUNNABLE
     +0x64  b7dd      c.j        +0x4a

   Slot 0 of the 48-byte frame is padding: five registers are saved, six
   slots are carved. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import KernelRvcDecode KernelBaseDecode WpRvcBridge WpDecodeBridge.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Local Notation KK := KernelSyms.kkill.

Notation kk_ra := (mword_of_int 1 : mword 5).

(* ---- the compressed decodes kkill alone uses ---- *)

(* 0x589c  c.lw a5,48(s1)  -- p->pid.  [C_LW]'s first field is the word
   index, so 48 = 4 * 12. *)
Lemma cdec_589c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x589c : mword 16)) s
  = Some (C_LW (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cexec_589c s :
  exec (execute (C_LW (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 48, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* 0x4c98  c.lw a4,24(s1)  -- p->state, into a4 rather than [cdec_4c9c]'s a5 *)
Lemma cdec_4c98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4c98 : mword 16)) s
  = Some (C_LW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cexec_4c98 s :
  exec (execute (C_LW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* 0x4789  c.li a5,2  -- the SLEEPING literal *)
Lemma cdec_4789 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4789 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x478d  c.li a5,3  -- the RUNNABLE literal *)
Lemma cdec_478d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x478d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa819  c.j +22  -- the "not found" tail's jump to the epilogue *)
Lemma cdec_a819 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa819 : mword 16)) s
  = Some (C_J (mword_of_int 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

Section CodeKkill.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation KKI o t d := (kernel_text -∗ instr (mword_of_int (KK + o) : mword 64) t d).

  (* ---- the base decodes kkill alone uses ---- *)
  (* +0x10  auipc s1,0x10 *)
  Lemma kkdec_auipc_s1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00010497 : mword 32)) s
    = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x14  addi s1,s1,1712 *)
  Lemma kkdec_addi_s1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x6b048493 : mword 32)) s
    = Some (ITYPE (mword_of_int 1712 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x18  auipc s3,0x16 *)
  Lemma kkdec_auipc_s3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00016997 : mword 32)) s
    = Some (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 19), AUIPC), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x1c  addi s3,s3,168 *)
  Lemma kkdec_addi_s3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0a898993 : mword 32)) s
    = Some (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x22  jal ra,acquire   (0x800020da -> 0x80000c08 = -5330) *)
  Lemma kkdec_jal_acq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xb2ffe0ef : mword 32)) s
    = Some (JAL (mword_of_int 2091822 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x28  beq a5,s2,+0x3e *)
  Lemma kkdec_beq_pid s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x01278b63 : mword 32)) s
    = Some (BTYPE (mword_of_int 22 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BEQ), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x2e  jal ra,release   (0x800020e6 -> 0x80000c90 = -5206) *)
  Lemma kkdec_jal_rel1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xbabfe0ef : mword 32)) s
    = Some (JAL (mword_of_int 2091946 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x36  bne s1,s3,+0x20 *)
  Lemma kkdec_bne_end s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xff3495e3 : mword 32)) s
    = Some (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x46  beq a4,a5,+0x60 *)
  Lemma kkdec_beq_sleep s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00f70d63 : mword 32)) s
    = Some (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x4c  jal ra,release   (0x80002104 -> 0x80000c90 = -5236) *)
  Lemma kkdec_jal_rel2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xb8dfe0ef : mword 32)) s
    = Some (JAL (mword_of_int 2091916 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.

  (* ---- the [instr] facts, one per address ---- *)
  Lemma kki_00 : KKI 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KK + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (KK + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.
  Lemma kki_02 : KKI 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KK + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (KK + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.
  Lemma kki_04 : KKI 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KK + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (KK + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.
  Lemma kki_06 : KKI 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KK + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (KK + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.
  Lemma kki_08 : KKI 0x08 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KK + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (KK + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.
  Lemma kki_0a : KKI 0x0a true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KK + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (KK + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.
  Lemma kki_0c : KKI 0x0c true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KK + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (KK + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.
  Lemma kki_0e : KKI 0x0e true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KK + 0x0e)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (KK + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.
  Lemma kki_10 : KKI 0x10 false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KK + 0x10)%Z (mword_of_int 0x00010497 : mword 32)
    (mword_of_int (KK + 0x10) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 9), AUIPC)) kkdec_auipc_s1. Qed.
  Lemma kki_14 : KKI 0x14 false (ITYPE (mword_of_int 1712 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KK + 0x14)%Z (mword_of_int 0x6b048493 : mword 32)
    (mword_of_int (KK + 0x14) : mword 64) (ITYPE (mword_of_int 1712 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) kkdec_addi_s1. Qed.
  Lemma kki_18 : KKI 0x18 false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 19), AUIPC)).
  Proof. mk_base (KK + 0x18)%Z (mword_of_int 0x00016997 : mword 32)
    (mword_of_int (KK + 0x18) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 19), AUIPC)) kkdec_auipc_s3. Qed.
  Lemma kki_1c : KKI 0x1c false (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (KK + 0x1c)%Z (mword_of_int 0x0a898993 : mword 32)
    (mword_of_int (KK + 0x1c) : mword 64) (ITYPE (mword_of_int 168 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), ADDI)) kkdec_addi_s3. Qed.
  Lemma kki_20 : KKI 0x20 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KK + 0x20)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KK + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kki_22 : KKI 0x22 false (JAL (mword_of_int 2091822 : mword 21, Regidx kk_ra)).
  Proof. mk_base (KK + 0x22)%Z (mword_of_int 0xb2ffe0ef : mword 32)
    (mword_of_int (KK + 0x22) : mword 64) (JAL (mword_of_int 2091822 : mword 21, Regidx kk_ra)) kkdec_jal_acq. Qed.
  Lemma kki_26 : KKI 0x26 true (LOAD (mword_of_int 48, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KK + 0x26)%Z (mword_of_int 0x589c : mword 16)
    (mword_of_int (KK + 0x26) : mword 64) (LOAD (mword_of_int 48, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_589c cexec_589c. Qed.
  Lemma kki_28 : KKI 0x28 false (BTYPE (mword_of_int 22 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BEQ)).
  Proof. mk_base (KK + 0x28)%Z (mword_of_int 0x01278b63 : mword 32)
    (mword_of_int (KK + 0x28) : mword 64) (BTYPE (mword_of_int 22 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BEQ)) kkdec_beq_pid. Qed.
  Lemma kki_2c : KKI 0x2c true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KK + 0x2c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KK + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kki_2e : KKI 0x2e false (JAL (mword_of_int 2091946 : mword 21, Regidx kk_ra)).
  Proof. mk_base (KK + 0x2e)%Z (mword_of_int 0xbabfe0ef : mword 32)
    (mword_of_int (KK + 0x2e) : mword 64) (JAL (mword_of_int 2091946 : mword 21, Regidx kk_ra)) kkdec_jal_rel1. Qed.
  Lemma kki_32 : KKI 0x32 false (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KK + 0x32)%Z (mword_of_int 0x16848493 : mword 32)
    (mword_of_int (KK + 0x32) : mword 64) (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bdec_16848493. Qed.
  Lemma kki_36 : KKI 0x36 false (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (KK + 0x36)%Z (mword_of_int 0xff3495e3 : mword 32)
    (mword_of_int (KK + 0x36) : mword 64) (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 9), BNE)) kkdec_bne_end. Qed.
  Lemma kki_3a : KKI 0x3a true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KK + 0x3a)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KK + 0x3a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.
  Lemma kki_3c : KKI 0x3c true (JAL (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KK + 0x3c)%Z (mword_of_int 0xa819 : mword 16)
    (mword_of_int (KK + 0x3c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 11 : mword 11) ('b"0")), zreg)) cdec_a819 exec_execute_C_J. Qed.
  Lemma kki_3e : KKI 0x3e true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KK + 0x3e)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (KK + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.
  Lemma kki_40 : KKI 0x40 true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (KK + 0x40)%Z (mword_of_int 0xd49c : mword 16)
    (mword_of_int (KK + 0x40) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_d49c cexec_d49c. Qed.
  Lemma kki_42 : KKI 0x42 true (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (KK + 0x42)%Z (mword_of_int 0x4c98 : mword 16)
    (mword_of_int (KK + 0x42) : mword 64) (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) cdec_4c98 cexec_4c98. Qed.
  Lemma kki_44 : KKI 0x44 true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KK + 0x44)%Z (mword_of_int 0x4789 : mword 16)
    (mword_of_int (KK + 0x44) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4789 exec_execute_C_LI. Qed.
  Lemma kki_46 : KKI 0x46 false (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (KK + 0x46)%Z (mword_of_int 0x00f70d63 : mword 32)
    (mword_of_int (KK + 0x46) : mword 64) (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) kkdec_beq_sleep. Qed.
  Lemma kki_4a : KKI 0x4a true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KK + 0x4a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KK + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kki_4c : KKI 0x4c false (JAL (mword_of_int 2091916 : mword 21, Regidx kk_ra)).
  Proof. mk_base (KK + 0x4c)%Z (mword_of_int 0xb8dfe0ef : mword 32)
    (mword_of_int (KK + 0x4c) : mword 64) (JAL (mword_of_int 2091916 : mword 21, Regidx kk_ra)) kkdec_jal_rel2. Qed.
  Lemma kki_50 : KKI 0x50 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KK + 0x50)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KK + 0x50) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.
  Lemma kki_52 : KKI 0x52 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KK + 0x52)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (KK + 0x52) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.
  Lemma kki_54 : KKI 0x54 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KK + 0x54)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (KK + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.
  Lemma kki_56 : KKI 0x56 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KK + 0x56)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (KK + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.
  Lemma kki_58 : KKI 0x58 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KK + 0x58)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (KK + 0x58) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.
  Lemma kki_5a : KKI 0x5a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KK + 0x5a)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (KK + 0x5a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.
  Lemma kki_5c : KKI 0x5c true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KK + 0x5c)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (KK + 0x5c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.
  Lemma kki_5e : KKI 0x5e true (JALR (zeros' 12, Regidx kk_ra, zreg)).
  Proof. mk_rvc (KK + 0x5e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KK + 0x5e) : mword 64) (JALR (zeros' 12, Regidx kk_ra, zreg)) cdec_8082 exec_execute_C_JR. Qed.
  Lemma kki_60 : KKI 0x60 true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KK + 0x60)%Z (mword_of_int 0x478d : mword 16)
    (mword_of_int (KK + 0x60) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_478d exec_execute_C_LI. Qed.
  Lemma kki_62 : KKI 0x62 true (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (KK + 0x62)%Z (mword_of_int 0xcc9c : mword 16)
    (mword_of_int (KK + 0x62) : mword 64) (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_cc9c cexec_cc9c. Qed.
  Lemma kki_64 : KKI 0x64 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KK + 0x64)%Z (mword_of_int 0xb7dd : mword 16)
    (mword_of_int (KK + 0x64) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)) cdec_b7dd exec_execute_C_J. Qed.

End CodeKkill.

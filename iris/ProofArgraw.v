(* ProofArgraw.v -- whole-function WP for argraw(), the first proof in the
   tree over a COMPUTED INDIRECT JUMP.

     static uint64 argraw(int n) {
       struct proc *p = myproc();
       switch (n) { case 0: return p->trapframe->a0; ... case 5: ...a5; }
       panic("argraw");
     }

   Thirty instructions @ 0x8000271a.  gcc compiles the switch to a jump
   table in .rodata at 0x80007758: six self-relative 4-byte offsets, indexed
   by n, added back to the table base and entered with [c.jr a5].  Three
   things make that cheaper than it looks:

   * [wp_cret_s_sconf] is already general over its register -- it is not a
     "return" rule, it is the [jr rs] rule -- so [c.jr a5] needs no new leaf.
   * [KernelDataInv.kernel_data_window]'s output is literally
     [word4_pointsto]'s definition at [DfracDiscarded], so reading a table
     entry costs one alignment fact; the [kernel_data] lookups discharge by
     [vm_compute] despite the 18k-entry map.
   * the spec's [i < NARG] precondition refutes the [bltu a5,s1,panic] arm
     via [wp_bltu_fall_s_sconf], so argraw carries NO [panic_wp] hypothesis.

   Shape: everything through the [bltu] is uniform in [i]; then a six-way
   [destruct] makes the table address, the loaded entry and the jump target
   concrete.  All six arms re-join at +0x2c, so the epilogue is proved ONCE
   as [ar_tail] over an arbitrary arrival map (the [wp_ci_tail] pattern from
   ProofClockintr, design/kernel-proofs.md). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText KernelDataInv.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge WpAuipc.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs WpLock.
Require Import HartTp WpNext.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv ProcInv.
Require Import SpecMyproc.
Require Import RiscvModelBytes InstrBytes.
Require Import ProcPtOwn.
Require Import SpecArgraw.
From Kernel Require KernelInstrs KernelData.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

(* the jump table: base, and the six self-relative entries (little-endian
   words extracted from KernelData.kernel_data). *)
Definition ar_tbl : Z := 0x80007758.
Definition ar_entry (i : nat) : mword 32 :=
  mword_of_int (match i with
                | 0%nat => 0xffffafea | 1%nat => 0xffffaff8 | 2%nat => 0xffffaffe
                | 3%nat => 0xffffb004 | 4%nat => 0xffffb00a | _ => 0xffffb010 end).

(* the case-body and argument-load PCs as FUNCTIONS of the switch index --
   what lets the arm be proved ONCE over a symbolic [k]. *)
Definition ar_case_off (k : nat) : Z :=
  match k with 0%nat => 0x28 | 1%nat => 0x36 | 2%nat => 0x3c
             | 3%nat => 0x42 | 4%nat => 0x48 | _ => 0x4e end.
Definition ar_ld_off (k : nat) : Z :=
  match k with 0%nat => 0x2a | 1%nat => 0x38 | 2%nat => 0x3e
             | 3%nat => 0x44 | 4%nat => 0x4a | _ => 0x50 end.
(* the [c.j] immediate of case k >= 1 (case 0 falls through to +0x2c) *)
Definition ar_cj_imm (k : nat) : Z :=
  match k with 1%nat => 2041 | 2%nat => 2038 | 3%nat => 2035
             | 4%nat => 2032 | _ => 2029 end.

(* ======================= fresh decode templates ======================= *)


(* +0x10  c.li a5,5 *)
Lemma ardec_li_a5_5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4795 : mword 16)) s = Some (C_LI (mword_of_int 5, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x16  c.slli s1,s1,2  -- s1 := 4n *)
Lemma ardec_slli_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x048a : mword 16)) s = Some (C_SLLI (mword_of_int 2, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x20  c.add s1,s1,a4  -- s1 := &tbl[n] *)
Lemma ardec_add_s1_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94ba : mword 16)) s = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.



(* +0x26  c.jr a5         -- THE indirect jump *)
Lemma ardec_jr_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8782 : mword 16)) s = Some (C_JR (Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* every arm: c.ld a5,88(a0)  -- p->trapframe *)
Lemma ardec_ld_tf s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6d3c : mword 16)) s = Some (C_LD (mword_of_int 11, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 0: c.ld a0,112(a5)  -- tf->a0 *)
Lemma ardec_ld_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ba8 : mword 16)) s = Some (C_LD (mword_of_int 14, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 1: c.ld a0,120(a5)  -- tf->a1 *)
Lemma ardec_ld_a1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7fa8 : mword 16)) s = Some (C_LD (mword_of_int 15, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 2: c.ld a0,128(a5)  -- tf->a2 *)
Lemma ardec_ld_a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x63c8 : mword 16)) s = Some (C_LD (mword_of_int 16, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 3: c.ld a0,136(a5)  -- tf->a3 *)
Lemma ardec_ld_a3 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x67c8 : mword 16)) s = Some (C_LD (mword_of_int 17, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 4: c.ld a0,144(a5)  -- tf->a4 *)
Lemma ardec_ld_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6bc8 : mword 16)) s = Some (C_LD (mword_of_int 18, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* case 5: c.ld a0,152(a5)  -- tf->a5 *)
Lemma ardec_ld_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6fc8 : mword 16)) s = Some (C_LD (mword_of_int 19, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* case 2 tail: c.j +0x2c *)
Lemma ardec_cj2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7f5 : mword 16)) s = Some (C_J (mword_of_int 2038 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* case 4 tail: c.j +0x2c *)


(* +0x0c  jal ra,myproc  (0x80002726 -> 0x80001904 = -3618) *)
Lemma ardec_jal_myproc s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9deff0ef : mword 32)) s = Some (JAL (mword_of_int 2093534 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x12  bltu a5,s1,+0x54 -- the panic arm, refuted by i < NARG *)
Lemma ardec_bltu s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0497e163 : mword 32)) s = Some (BTYPE (mword_of_int 66 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* +0x18  auipc a4,0x5 *)
Lemma ardec_auipc_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00005717 : mword 32)) s = Some (UTYPE (mword_of_int 0x5 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x1c  addi a4,a4,38 -- a4 := 0x80007758, the table base *)
Lemma ardec_addi_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02670713 : mword 32)) s = Some (ITYPE (mword_of_int 38 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.


Notation ar_ra := (mword_of_int 1 : mword 5).
Notation ar_s0 := (mword_of_int 8 : mword 5).
Notation ar_s1 := (mword_of_int 9 : mword 5).
Notation ar_a0 := (mword_of_int 10 : mword 5).
Notation ar_a4 := (mword_of_int 14 : mword 5).
Notation ar_a5 := (mword_of_int 15 : mword 5).

Lemma ar_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx ar_s1.
Proof. vm_compute. reflexivity. Qed.
Lemma ar_cr2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx ar_a0.
Proof. vm_compute. reflexivity. Qed.
Lemma ar_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx ar_a5.
Proof. vm_compute. reflexivity. Qed.

(* argraw's balanced 32-byte frame (identical to argint's / sys_uptime's). *)
Lemma ar_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (Hu : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !Hu. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
             = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
             = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Module ArgrawProof (Myproc : MYPROC) : ARGRAW.

Section ProofArgraw.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ}.
  Context `{CID : CpuId}.

  Notation ARI o t d := (kernel_text -∗ instr (mword_of_int (AR + o) : mword 64) t d).

  Lemma ari_00 : ARI 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (AR + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (AR + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma ari_02 : ARI 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (AR + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (AR + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma ari_04 : ARI 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (AR + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (AR + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma ari_06 : ARI 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (AR + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (AR + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma ari_08 : ARI 0x08 true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (AR + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (AR + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma ari_0a : ARI 0x0a true (RTYPE (Regidx ar_a0, zreg, Regidx ar_s1, ADD)).
  Proof. mk_rvc (AR + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (AR + 0x0a) : mword 64) (RTYPE (Regidx ar_a0, zreg, Regidx ar_s1, ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma ari_0c : ARI 0x0c false (JAL (mword_of_int 2093534 : mword 21, Regidx ar_ra)).
  Proof. mk_base (AR + 0x0c)%Z (mword_of_int 0x9deff0ef : mword 32)
    (mword_of_int (AR + 0x0c) : mword 64) (JAL (mword_of_int 2093534 : mword 21, Regidx ar_ra)) ardec_jal_myproc. Qed.

  Lemma ari_10 : ARI 0x10 true (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), zreg, Regidx ar_a5, ADDI)).
  Proof. mk_rvc (AR + 0x10)%Z (mword_of_int 0x4795 : mword 16)
    (mword_of_int (AR + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 5 : mword 6), zreg, Regidx ar_a5, ADDI)) ardec_li_a5_5 exec_execute_C_LI. Qed.

  Lemma ari_12 : ARI 0x12 false (BTYPE (mword_of_int 66 : mword 13, Regidx ar_s1, Regidx ar_a5, BLTU)).
  Proof. mk_base (AR + 0x12)%Z (mword_of_int 0x0497e163 : mword 32)
    (mword_of_int (AR + 0x12) : mword 64) (BTYPE (mword_of_int 66 : mword 13, Regidx ar_s1, Regidx ar_a5, BLTU)) ardec_bltu. Qed.

  Lemma ari_16 : ARI 0x16 true (SHIFTIOP (mword_of_int 2 : mword 6, Regidx ar_s1, Regidx ar_s1, SLLI)).
  Proof. mk_rvc (AR + 0x16)%Z (mword_of_int 0x048a : mword 16)
    (mword_of_int (AR + 0x16) : mword 64) (SHIFTIOP (mword_of_int 2 : mword 6, Regidx ar_s1, Regidx ar_s1, SLLI)) ardec_slli_s1 exec_execute_C_SLLI. Qed.

  Lemma ari_18 : ARI 0x18 false (UTYPE (mword_of_int 0x5 : mword 20, Regidx ar_a4, AUIPC)).
  Proof. mk_base (AR + 0x18)%Z (mword_of_int 0x00005717 : mword 32)
    (mword_of_int (AR + 0x18) : mword 64) (UTYPE (mword_of_int 0x5 : mword 20, Regidx ar_a4, AUIPC)) ardec_auipc_a4. Qed.

  Lemma ari_1c : ARI 0x1c false (ITYPE (mword_of_int 38 : mword 12, Regidx ar_a4, Regidx ar_a4, ADDI)).
  Proof. mk_base (AR + 0x1c)%Z (mword_of_int 0x02670713 : mword 32)
    (mword_of_int (AR + 0x1c) : mword 64) (ITYPE (mword_of_int 38 : mword 12, Regidx ar_a4, Regidx ar_a4, ADDI)) ardec_addi_a4. Qed.

  Lemma ari_20 : ARI 0x20 true (RTYPE (Regidx ar_a4, Regidx ar_s1, Regidx ar_s1, ADD)).
  Proof. mk_rvc (AR + 0x20)%Z (mword_of_int 0x94ba : mword 16)
    (mword_of_int (AR + 0x20) : mword 64) (RTYPE (Regidx ar_a4, Regidx ar_s1, Regidx ar_s1, ADD)) ardec_add_s1_a4 exec_execute_C_ADD. Qed.

  Lemma ari_22 : ARI 0x22 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (AR + 0x22)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (AR + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) cdec_409c exec_execute_C_LW. Qed.

  Lemma ari_24 : ARI 0x24 true (RTYPE (Regidx ar_a4, Regidx ar_a5, Regidx ar_a5, ADD)).
  Proof. mk_rvc (AR + 0x24)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (AR + 0x24) : mword 64) (RTYPE (Regidx ar_a4, Regidx ar_a5, Regidx ar_a5, ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma ari_26 : ARI 0x26 true (JALR (zeros' 12, Regidx ar_a5, zreg)).
  Proof. mk_rvc (AR + 0x26)%Z (mword_of_int 0x8782 : mword 16)
    (mword_of_int (AR + 0x26) : mword 64) (JALR (zeros' 12, Regidx ar_a5, zreg)) ardec_jr_a5 exec_execute_C_JR. Qed.

  Lemma ari_28 : ARI 0x28 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x28)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_36 : ARI 0x36 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x36)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_3c : ARI 0x3c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x3c)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_42 : ARI 0x42 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x42)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_48 : ARI 0x48 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x48)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_4e : ARI 0x4e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (AR + 0x4e)%Z (mword_of_int 0x6d3c : mword 16)
    (mword_of_int (AR + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.

  Lemma ari_2a : ARI 0x2a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x2a)%Z (mword_of_int 0x7ba8 : mword 16)
    (mword_of_int (AR + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a0 exec_execute_C_LD. Qed.

  Lemma ari_38 : ARI 0x38 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x38)%Z (mword_of_int 0x7fa8 : mword 16)
    (mword_of_int (AR + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a1 exec_execute_C_LD. Qed.

  Lemma ari_3e : ARI 0x3e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x3e)%Z (mword_of_int 0x63c8 : mword 16)
    (mword_of_int (AR + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a2 exec_execute_C_LD. Qed.

  Lemma ari_44 : ARI 0x44 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 17 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x44)%Z (mword_of_int 0x67c8 : mword 16)
    (mword_of_int (AR + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 17 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a3 exec_execute_C_LD. Qed.

  Lemma ari_4a : ARI 0x4a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 18 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x4a)%Z (mword_of_int 0x6bc8 : mword 16)
    (mword_of_int (AR + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 18 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a4 exec_execute_C_LD. Qed.

  Lemma ari_50 : ARI 0x50 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 19 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (AR + 0x50)%Z (mword_of_int 0x6fc8 : mword 16)
    (mword_of_int (AR + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 19 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a5 exec_execute_C_LD. Qed.

  Lemma ari_3a : ARI 0x3a true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (AR + 0x3a)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (AR + 0x3a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

  Lemma ari_40 : ARI 0x40 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (AR + 0x40)%Z (mword_of_int 0xb7f5 : mword 16)
    (mword_of_int (AR + 0x40) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")), zreg)) ardec_cj2 exec_execute_C_J. Qed.

  Lemma ari_46 : ARI 0x46 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (AR + 0x46)%Z (mword_of_int 0xb7dd : mword 16)
    (mword_of_int (AR + 0x46) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)) cdec_b7dd exec_execute_C_J. Qed.

  Lemma ari_4c : ARI 0x4c true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (AR + 0x4c)%Z (mword_of_int 0xb7c5 : mword 16)
    (mword_of_int (AR + 0x4c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)) cdec_b7c5 exec_execute_C_J. Qed.

  Lemma ari_52 : ARI 0x52 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (AR + 0x52)%Z (mword_of_int 0xbfe9 : mword 16)
    (mword_of_int (AR + 0x52) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)) cdec_bfe9 exec_execute_C_J. Qed.

  Lemma ari_2c : ARI 0x2c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (AR + 0x2c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (AR + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma ari_2e : ARI 0x2e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (AR + 0x2e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (AR + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma ari_30 : ARI 0x30 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (AR + 0x30)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (AR + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma ari_32 : ARI 0x32 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (AR + 0x32)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (AR + 0x32) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma ari_34 : ARI 0x34 true (JALR (zeros' 12, Regidx ar_ra, zreg)).
  Proof. mk_rvc (AR + 0x34)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (AR + 0x34) : mword 64) (JALR (zeros' 12, Regidx ar_ra, zreg)) cdec_8082 exec_execute_C_JR. Qed.



  (* the switch index is in range, so [bltu a5,s1] (5 <u n) does not fire *)
  Lemma ar_bltu_false (i : nat) : (i < NARG)%nat ->
    zopz0zI_u (mword_of_int 5 : mword 64) (mword_of_int (Z.of_nat i) : mword 64) = false.
  Proof. intro Hi. unfold NARG in Hi. destruct i as [|[|[|[|[|[|i']]]]]]; try lia; vm_compute; reflexivity. Qed.

  (* The jump table's .rodata bytes, as ONE PURE lemma over a SYMBOLIC index,
     outside any Iris goal.  [ar_table_word] then passes it to
     [kernel_data_window] BY NAME.  This is the optimization.md rule about
     inline [ltac:(…)] term-args: the six inline byte-premise tactics this
     replaces were re-elaborated by the proofmode without the [Qed] vm-seal,
     at ~12 s per call site -- 73.6 s of the file's 93.8 s in ONE sentence.
     The 24 [kernel_data] lookups themselves are NOT the cost (~0.15 s total:
     the VM compiles the 18k-entry [list_to_map] once per process and the
     remaining lookups are ~2 ms each). *)
  Lemma ar_tbl_bytes (i : nat) : (i < NARG)%nat ->
    forall j, (j < 4)%nat ->
      KernelData.kernel_data !! (ar_tbl + 4 * Z.of_nat i + Z.of_nat j)%Z
        = Some (nth_byte (ar_entry i) j).
  Proof.
    unfold NARG. intros Hi j Hj.
    destruct i as [|[|[|[|[|[|i']]]]]]; try lia;
      (destruct j as [|[|[|[|j']]]]; try lia;
       vm_compute; f_equal; apply bv_eq; reflexivity).
  Qed.

  (* the [i]th jump-table entry, straight out of the .rodata image.  No
     [destruct i] on the Iris goal: ONE [iApply] over the symbolic index,
     every premise a named hypothesis. *)
  Lemma ar_table_word (i : nat) : (i < NARG)%nat ->
    kernel_data -∗ (mword_of_int (ar_tbl + 4 * Z.of_nat i) : mword 64) ↦₄□ ar_entry i.
  Proof.
    intro Hi.
    assert (Hle : text_end <= ar_tbl + 4 * Z.of_nat i) by (unfold text_end, ar_tbl; lia).
    pose proof (ar_tbl_bytes i Hi) as Hb.
    unfold NARG in Hi. iIntros "#Hd". rewrite /word4_pointsto. iSplit.
    { iPureIntro. destruct i as [|[|[|[|[|[|i']]]]]]; try lia; vm_compute; reflexivity. }
    iApply (kernel_data_window (ar_tbl + 4 * Z.of_nat i) (ar_entry i) 4%nat _ eq_refl
              Hle Hb with "Hd").
  Qed.

  (* ================================================================== *)
  (* The shared epilogue at +0x2c.                                       *)
  (* All six switch arms re-join here, so it is proved ONCE over an       *)
  (* ARBITRARY arrival map [M] and hands the caller exactly the register  *)
  (* facts the postcondition needs (the [wp_ci_tail] pattern).            *)
  (* ================================================================== *)
  Lemma ar_stk (sp0 : mword 64) (j u : nat) :
    (j + u = 4)%nat -> (u < 4)%nat ->
    pa_stk sp0 j = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000"))).
  Proof.
    intros Hju Hu.
    destruct u as [|[|[|[|]]]]; try lia; destruct j as [|[|[|[|[|]]]]]; try lia;
      unfold pa_stk, add_vec_int; rewrite add_vec_off2;
      f_equal; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ar_tail `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (sp0 ra0 s00 s10 gapv : mword 64) (k : nat) (b : bool) (p : mword 64) :
    M !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    sie_cap_gpr M k b p -∗
    kernel_text -∗ pc_is (mword_of_int (AR + 0x2c) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) gapv -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mf : regfile,
        ⌜ Mf !!! Regidx csp_rs1 = sp0 /\
          Mf !!! Regidx ar_s0 = s00 /\
          Mf !!! Regidx ar_s1 = s10 /\
          Mf !!! Regidx ar_a0 = M !!! Regidx ar_a0 /\
          (forall r : mword 5, is_cs_idx r = true ->
             r <> csp_rs1 -> r <> ar_s0 -> r <> ar_s1 ->
             Mf !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr Mf (k + 4)%nat b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intro HMsp.
    iIntros "Hcg #Htext Hpc Hr24 Hr16 Hr8 Hgap Hcont".
    assert (Hb1 : pa_stk sp0 1 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))
      by (apply (ar_stk sp0 1 3); lia).
    assert (Hb2 : pa_stk sp0 2 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))
      by (apply (ar_stk sp0 2 2); lia).
    assert (Hb3 : pa_stk sp0 3 = add_vec (pa_stk sp0 4) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))
      by (apply (ar_stk sp0 3 1); lia).
    (* +0x2c: c.ldsp ra,24(sp) *)
    iPoseProof (ari_2c with "Htext") as "Hi2c".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (AR + 0x2c)) (mword_of_int 3 : mword 6) ar_ra
              M k ra0 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hr24] [-]").
    { iEval (rewrite HMsp -Hb1). iExact "Hr24". }
    iIntros (CID1 Hs1) "Hcg Hpc Hr24".
    set (T1 := <[Regidx ar_ra := regval_into_reg ra0]> M).
    change (<[Regidx ar_ra := regval_into_reg ra0]> M) with T1.
    assert (Hp2e : add_vec_int (mword_of_int (AR + 0x2c) : mword 64) 2 = mword_of_int (AR + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T1 upd_ne; [exact HMsp | vm_compute; discriminate]).
    (* +0x2e: c.ldsp s0,16(sp) *)
    iPoseProof (ari_2e with "Htext") as "Hi2e".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (AR + 0x2e)) (mword_of_int 2 : mword 6) ar_s0
              T1 k s00 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [Hr16] [-]").
    { iEval (rewrite HT1sp -Hb2). iExact "Hr16". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr16".
    set (T2 := <[Regidx ar_s0 := regval_into_reg s00]> T1).
    change (<[Regidx ar_s0 := regval_into_reg s00]> T1) with T2.
    assert (Hp30 : add_vec_int (mword_of_int (AR + 0x2e) : mword 64) 2 = mword_of_int (AR + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    (* +0x30: c.ldsp s1,8(sp) *)
    iPoseProof (ari_30 with "Htext") as "Hi30".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (AR + 0x30)) (mword_of_int 1 : mword 6) ar_s1
              T2 k s10 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi30 [Hr8] [-]").
    { iEval (rewrite HT2sp -Hb3). iExact "Hr8". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr8".
    set (T3 := <[Regidx ar_s1 := regval_into_reg s10]> T2).
    change (<[Regidx ar_s1 := regval_into_reg s10]> T2) with T3.
    assert (Hp32 : add_vec_int (mword_of_int (AR + 0x30) : mword 64) 2 = mword_of_int (AR + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 4)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    (* +0x32: c.addi16sp sp,32 -- the frame pop *)
    assert (Hup : add_vec (pa_stk sp0 4) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
      assert (HAB : add_vec (mword_of_int (-8 * 4)%Z : mword 64)
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = mword_of_int 0)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite HAB. apply kv_addv_zero. }
    assert (Hwv : add_vec (T3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
      by (rewrite HT3sp; exact Hup).
    assert (Hpop : T3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
      by (rewrite Hwv HT3sp; reflexivity).
    iPoseProof (ari_32 with "Htext") as "Hi32".
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24". { iExists _. iEval (rewrite Hb1 -HMsp). iExact "Hr24". }
      iSplitL "Hr16". { iExists _. iEval (rewrite Hb2 -HT1sp). iExact "Hr16". }
      iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3 -HT2sp). iExact "Hr8". }
      iSplitL "Hgap". { iExists _. iExact "Hgap". }
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (AR + 0x32)) (mword_of_int 2 : mword 6) T3 k 4 b Hpop
              with "Hcg Hpc Hi32 Hframe4 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (T4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (T3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> T3) with T4.
    assert (Hp34 : add_vec_int (mword_of_int (AR + 0x32) : mword 64) 2 = mword_of_int (AR + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* +0x34: c.ret *)
    assert (HT4ra : T4 !!! Regidx ar_ra = ra0).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1. apply upd_eq. }
    assert (Hrt34 : forall CID' : CpuId, ret_pc (rget (CID := CID') T4 ar_ra) = ret_pc ra0)
      by (intros CID'; rgne; rewrite HT4ra; reflexivity).
    iPoseProof (ari_34 with "Htext") as "Hi34".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x34)) ar_ra T4 (k + 4)%nat b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rewrite Hrt34) in "Hpc".
    iSpecialize ("Hcont" $! CID5 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T4 with "[%] Hcg Hpc").
    split; [rewrite /T4 upd_eq; exact Hwv|].
    split. { rewrite /T4 upd_ne; [| vm_compute; discriminate].
             rewrite /T3 upd_ne; [| vm_compute; discriminate]. rewrite /T2. apply upd_eq. }
    split. { rewrite /T4 upd_ne; [| vm_compute; discriminate]. rewrite /T3. apply upd_eq. }
    split. { rewrite /T4 upd_ne; [| vm_compute; discriminate].
             rewrite /T3 upd_ne; [| vm_compute; discriminate].
             rewrite /T2 upd_ne; [| vm_compute; discriminate].
             rewrite /T1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    intros r Hr Ncsp N8 N9.
    assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite /T4 upd_ne; [| congruence].
    rewrite /T3 upd_ne; [| congruence].
    rewrite /T2 upd_ne; [| congruence].
    rewrite /T1 upd_ne; [reflexivity | congruence].
  Qed.


  (* [c.mv rd,rs] is modelled as [add zero, rs]. *)
  Lemma ar_addv_zero_l (X : mword 64) : add_vec (zero_reg : mword 64) X = X.
  Proof.
    assert (Hu : forall x y : mword 64,
              bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
    { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
        SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned. reflexivity. }
    apply bv_eq. rewrite Hu.
    assert (HZ : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
    rewrite HZ Z.add_0_l. apply bv_wrap_bv_unsigned.
  Qed.


  (* ================================================================== *)
  (* Per-case dispatch: the ONLY six-way [destruct]s, each on a TINY     *)
  (* goal.  Splitting inside the capstone instead cost 81 s and ~74 GB   *)
  (* -- Coq retains all six arms' Iris proof terms until [Qed], and each *)
  (* branch re-typechecks the dependently-typed Sail bitvector context.  *)
  (* ================================================================== *)
  Lemma ar_i_tf (k : nat) : (k < NARG)%nat ->
    kernel_text -∗ instr (mword_of_int (AR + ar_case_off k) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")),
             creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia; cbn [ar_case_off];
      [ exact ari_28 | exact ari_36 | exact ari_3c | exact ari_42 | exact ari_48 | exact ari_4e ].
  Qed.

  Lemma ar_i_ld (k : nat) : (k < NARG)%nat ->
    kernel_text -∗ instr (mword_of_int (AR + ar_ld_off k) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat k) : mword 5) ('b"000")),
             creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      cbn [ar_ld_off Z.of_nat]; cbn [Z.add];
      [ exact ari_2a | exact ari_38 | exact ari_3e | exact ari_44 | exact ari_4a | exact ari_50 ].
  Qed.

  (* the table entry really does land on the case body *)
  Lemma ar_jump_tgt (k : nat) : (k < NARG)%nat ->
    ret_pc (add_vec (sign_extend' 64 (ar_entry k)) (mword_of_int ar_tbl))
    = (mword_of_int (AR + ar_case_off k) : mword 64).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* the [c.ld a0,<112+8k>(a5)] displacement lands on trapframe word 14+k *)
  Lemma ar_arg_addr (tfp : mword 44) (k : nat) : (k < NARG)%nat ->
    add_vec (page_base tfp)
      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat k) : mword 5) ('b"000"))))
    = a_tf_word tfp (tf_arg_idx k).
  Proof.
    intro Hk. unfold NARG in Hk. rewrite /a_tf_word /tf_arg_idx /pa_add /add_vec_int.
    destruct k as [|[|[|[|[|[|k']]]]]]; try lia; f_equal; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ar_lw_off :
    sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")))
    = (mword_of_int 0 : mword 64).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma ar_tf_off (X : mword 64) :
    add_vec X (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
    = p_trapframe X.
  Proof. rewrite /p_trapframe. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

  (* the six arms re-join at +0x2c: case 0 falls through, 1..5 take a [c.j].
     The six-way dispatch is done on the INSTR fact and on a pure equation --
     never on the WP goal.  A [destruct k] there re-typechecks the
     dependently-typed Sail context per branch and ran the machine out of
     memory; the WP-level split below is binary. *)
  Lemma ar_i_cj (k : nat) : (1 <= k < NARG)%nat ->
    kernel_text -∗ instr (mword_of_int (AR + ar_ld_off k + 2) : mword 64) true
      (JAL (sign_extend' 21 (concat_vec (mword_of_int (ar_cj_imm k) : mword 11) ('b"0")), zreg)).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      cbn [ar_ld_off ar_cj_imm];
      [ exact ari_3a | exact ari_40 | exact ari_46 | exact ari_4c | exact ari_52 ].
  Qed.

  Lemma ar_cj_tgt (k : nat) : (1 <= k < NARG)%nat ->
    add_vec (mword_of_int (AR + ar_ld_off k + 2) : mword 64)
      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int (ar_cj_imm k) : mword 11) ('b"0"))))
    = mword_of_int (AR + 0x2c).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      cbn [ar_ld_off ar_cj_imm]; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma ar_fall0 : (mword_of_int (AR + ar_ld_off 0 + 2) : mword 64) = mword_of_int (AR + 0x2c).
  Proof. cbn [ar_ld_off]. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma ar_join `{CID0 : CpuId} (Φ : mval -> iProp Σ) (M : regfile) (k : nat) (av' : nat) (b : bool) (p : mword 64) :
    (k < NARG)%nat ->
    kernel_text -∗ sie_cap_gpr M av' b p -∗
    pc_is (mword_of_int (AR + ar_ld_off k + 2) : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr M av' b p -∗ pc_is (mword_of_int (AR + 0x2c) : mword 64) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intro Hk. iIntros "#Htext Hcg Hpc Hcont".
    destruct (decide (k = 0%nat)) as [->|Hne].
    { iEval (rewrite ar_fall0) in "Hpc".
      iSpecialize ("Hcont" $! CID0 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" with "Hcg Hpc"). }
    assert (Hk1 : (1 <= k < NARG)%nat) by lia.
    iPoseProof (ar_i_cj k Hk1 with "Htext") as "Hicj".
    iApply (wp_cj_s_sconf Φ (mword_of_int (AR + ar_ld_off k + 2))
              (sign_extend' 21 (concat_vec (mword_of_int (ar_cj_imm k) : mword 11) ('b"0")))
              M av' b ltac:(rewrite (ar_cj_tgt k Hk1); vm_compute; reflexivity)
              with "Hcg Hpc Hicj [-]").
    iIntros (CID1 Hs1). iNext. iIntros "Hcg Hpc".
    iEval (rewrite (ar_cj_tgt k Hk1)) in "Hpc".
    iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" with "Hcg Hpc").
  Qed.


  (* ================================================================== *)
  (* THE arm: +0x22 (table read) through the two loads and the join,     *)
  (* proved ONCE over a symbolic switch index [k].                       *)
  (* ================================================================== *)
  Lemma ar_ld_after_case (k : nat) : (k < NARG)%nat ->
    add_vec_int (mword_of_int (AR + ar_case_off k) : mword 64) 2
    = mword_of_int (AR + ar_ld_off k).
  Proof.
    intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      cbn [ar_case_off ar_ld_off]; apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* The arm's STATEMENT, once.  Each of the six concrete arms below proves
     this at its own index and is closed with its own [Qed], so Coq releases
     that arm's proof term instead of retaining all six (which peaked at
     74 GB).  Keeping the index CONCRETE also keeps the addresses closed
     terms, so the WP leaves' unification can just compute them -- a symbolic
     [k] there made unification itself blow up (14 GB and climbing). *)
  Definition ar_arm_body `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (k : nat) (av' : nat)
      (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) : Prop :=
    (k < NARG)%nat ->
    ws !! tf_arg_idx k = Some v ->
    M !!! Regidx ar_s1 = mword_of_int (ar_tbl + 4 * Z.of_nat k) ->
    M !!! Regidx ar_a4 = mword_of_int ar_tbl ->
    M !!! Regidx ar_a0 = p ->
    M !!! Regidx csp_rs1 = pa_stk sp0 4 ->
    kernel_text -∗ kernel_data -∗
    sie_cap_gpr M av' b p -∗
    pc_is (mword_of_int (AR + 0x22) : mword 64) -∗
    p_trapframe p ↦₈{dqt} page_base tfp -∗
    tf_page tfp ws -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) vgap -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ Mf : regfile,
        ⌜ Mf !!! Regidx csp_rs1 = sp0 /\
          Mf !!! Regidx ar_s0 = s00 /\
          Mf !!! Regidx ar_s1 = s10 /\
          Mf !!! Regidx ar_a0 = v /\
          (forall r : mword 5, is_cs_idx r = true ->
             r <> csp_rs1 -> r <> ar_s0 -> r <> ar_s1 ->
             Mf !!! Regidx r = M !!! Regidx r) ⌝ -∗
        sie_cap_gpr Mf (av' + 4)%nat b p -∗
        pc_is (ret_pc ra0) -∗
        p_trapframe p ↦₈{dqt} page_base tfp -∗
        tf_page tfp ws -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.

  Local Lemma ar_arm0 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 0%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 0%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 0%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 0%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 0%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 0%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 0%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 0%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 0%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 0%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 0%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 0%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 0%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<0%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 0%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 0%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 0%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 0%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 0%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 0%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 0%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 0%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 0%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 0%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  Local Lemma ar_arm1 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 1%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 1%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 1%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 1%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 1%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 1%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 1%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 1%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 1%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 1%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 1%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 1%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 1%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<1%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 1%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 1%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 1%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 1%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 1%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 1%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 1%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 1%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 1%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 1%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  Local Lemma ar_arm2 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 2%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 2%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 2%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 2%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 2%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 2%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 2%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 2%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 2%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 2%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 2%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 2%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 2%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<2%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 2%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 2%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 2%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 2%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 2%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 2%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 2%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 2%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 2%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 2%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  Local Lemma ar_arm3 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 3%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 3%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 3%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 3%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 3%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 3%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 3%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 3%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 3%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 3%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 3%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 3%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 3%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<3%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 3%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 3%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 3%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 3%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 3%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 3%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 3%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 3%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 3%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 3%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  Local Lemma ar_arm4 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 4%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 4%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 4%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 4%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 4%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 4%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 4%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 4%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 4%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 4%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 4%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 4%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 4%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<4%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 4%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 4%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 4%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 4%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 4%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 4%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 4%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 4%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 4%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 4%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  Local Lemma ar_arm5 `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (av' : nat) (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M 5%nat av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    cbv beta delta [ar_arm_body].
    intros Hk Hws HMs1 HMa4 HMa0 HMsp.
    iIntros "#Htext #Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap Hcont".
    iPoseProof (ar_table_word 5%nat Hk with "Hdata") as "#Hent".
    (* +0x22: c.lw a5,0(s1) -- read the jump-table entry *)
    iPoseProof (ari_22 with "Htext") as "Hi22".
    iEval (rewrite ar_cr1; rewrite ar_cr7) in "Hi22".
    assert (Hta : add_vec (M !!! Regidx ar_s1)
                    (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))))
                  = mword_of_int (ar_tbl + 4 * Z.of_nat 5%nat))
      by (rewrite HMs1 ar_lw_off; apply kv_addv_zero).
    iApply (wp_clw_s_sconf Φ (mword_of_int (AR + 0x22)) ar_a5 ar_s1
              (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00"))) M av' (ar_entry 5%nat) b
              (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [] [-]").
    { iEval (rewrite Hta). iExact "Hent". }
    iIntros (CID1 Hs1) "Hcg Hpc _".
    set (B5 := <[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 5%nat))]> M).
    change (<[Regidx ar_a5 := regval_into_reg (sign_extend' 64 (ar_entry 5%nat))]> M) with B5.
    assert (Hp24 : add_vec_int (mword_of_int (AR + 0x22) : mword 64) 2 = mword_of_int (AR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24: c.add a5,a5,a4 -- a5 := the case target *)
    iPoseProof (ari_24 with "Htext") as "Hi24".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x24)) ar_a5 ar_a4 B5 av' b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (B6 := <[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5).
    change (<[Regidx ar_a5 := regval_into_reg (add_vec (B5 !!! Regidx ar_a5) (B5 !!! Regidx ar_a4))]> B5) with B6.
    assert (Hp26 : add_vec_int (mword_of_int (AR + 0x24) : mword 64) 2 = mword_of_int (AR + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26: c.jr a5 -- THE computed indirect jump *)
    assert (HB5a5 : B5 !!! Regidx ar_a5 = sign_extend' 64 (ar_entry 5%nat))
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a4 : B5 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B5 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HB6a5 : ret_pc (B6 !!! Regidx ar_a5) = mword_of_int (AR + ar_case_off 5%nat)).
    { rewrite /B6 upd_eq HB5a5 HB5a4. exact (ar_jump_tgt 5%nat Hk). }
    assert (Hrt26 : forall CID' : CpuId, ret_pc (rget (CID := CID') B6 ar_a5) = mword_of_int (AR + ar_case_off 5%nat))
      by (intros CID'; rgne; exact HB6a5).
    iPoseProof (ari_26 with "Htext") as "Hi26".
    iApply (wp_cret_s_sconf Φ (mword_of_int (AR + 0x26)) ar_a5 B6 av' b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi26 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc". iEval (rewrite Hrt26) in "Hpc".
    (* the case body: c.ld a5,88(a0) -- p->trapframe *)
    iPoseProof (ar_i_tf 5%nat Hk with "Htext") as "Hitf".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hitf".
    assert (HB6a0 : B6 !!! Regidx ar_a0 = p).
    { rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    assert (Htfa : add_vec (B6 !!! Regidx ar_a0)
                     (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))))
                   = p_trapframe p)
      by (rewrite HB6a0; apply ar_tf_off).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_case_off 5%nat)) ar_a5 ar_a0
              (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000"))) B6 av' (page_base tfp) b
              (dqm := dqt) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hitf [Htfp] [-]").
    { iEval (rewrite Htfa). iExact "Htfp". }
    iIntros (CID4 Hs4) "Hcg Hpc Htfp". iEval (rewrite Htfa) in "Htfp".
    set (C0 := <[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6).
    change (<[Regidx ar_a5 := regval_into_reg (page_base tfp)]> B6) with C0.
    iEval (rewrite (ar_ld_after_case 5%nat Hk)) in "Hpc".
    (* c.ld a0,<112+8k>(a5) -- tf->a<5%nat>.  The word lives at the PHYSICAL
       tier inside [tf_page]; the load is a VA-tier one through the kernel
       identity map, so it crosses with [tf_word_to_mem] and back. *)
    iDestruct (tf_page_word tfp ws (tf_arg_idx 5%nat) v Hws with "Htf") as "[Hw Hwback]".
    iPoseProof (ar_i_ld 5%nat Hk with "Htext") as "Hild".
    iEval (rewrite ar_cr2; rewrite ar_cr7) in "Hild".
    assert (Harga : add_vec (C0 !!! Regidx ar_a5)
                      (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 5%nat) : mword 5) ('b"000"))))
                    = a_tf_word tfp (tf_arg_idx 5%nat))
      by (rewrite /C0 upd_eq; exact (ar_arg_addr tfp 5%nat Hk)).
    iApply (wp_cld_s_sconf Φ (mword_of_int (AR + ar_ld_off 5%nat)) ar_a0 ar_a5
              (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat 5%nat) : mword 5) ('b"000"))) C0 av' v b
              (dqm := DfracOwn 1) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hild [Hw] [-]").
    { iEval (rewrite Harga). iExact "Hw". }
    iIntros (CID5 Hs5) "Hcg Hpc Hw". iEval (rewrite Harga) in "Hw".
    iDestruct ("Hwback" with "Hw") as "Htf".
    set (C1 := <[Regidx ar_a0 := regval_into_reg v]> C0).
    change (<[Regidx ar_a0 := regval_into_reg v]> C0) with C1.
    assert (Hpj : add_vec_int (mword_of_int (AR + ar_ld_off 5%nat) : mword 64) 2
                  = mword_of_int (AR + ar_ld_off 5%nat + 2)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpj) in "Hpc".
    (* re-join at +0x2c, then the shared epilogue *)
    iApply (ar_join Φ C1 5%nat av' b p Hk with "Htext Hcg Hpc [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite /C1 upd_ne; [| vm_compute; discriminate].
      rewrite /C0 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite /B5 upd_ne; [| vm_compute; discriminate]. exact HMsp. }
    iApply (ar_tail Φ C1 sp0 ra0 s00 s10 vgap av' b p HC1sp
              with "Hcg Htext Hpc Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID7 Hs7 Mf) "%HMf Hcg Hpc".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hpc Htfp Htf").
    split; [exact Hfsp|]. split; [exact Hfs0|]. split; [exact Hfs1|].
    split. { rewrite Hfa0 /C1 upd_eq. reflexivity. }
    intros r Hr Ncsp N8 N9.
    assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
    rewrite Hfthr; [| exact Hr | exact Ncsp | exact N8 | exact N9].
    rewrite /C1 upd_ne; [| congruence].
    rewrite /C0 upd_ne; [| congruence].
    rewrite /B6 upd_ne; [| congruence].
    rewrite /B5 upd_ne; [reflexivity | congruence].
  Qed.

  (* Dispatch.  The [destruct] happens BEFORE any hypothesis is introduced,
     so the goal is a closed implication and there is no Iris context to
     duplicate per branch -- which is what made the in-proof six-way split
     cost 81 s and re-typecheck the dependent Sail context six times. *)
  Lemma ar_arm `{CID0 : CpuId} (Φ : mval -> iProp Σ)
      (M : regfile) (k : nat) (av' : nat)
      (sp0 ra0 s00 s10 vgap p : mword 64) (tfp : mword 44)
      (ws : list (mword 64)) (v : mword 64) (dqt : dfrac) (b : bool) :
    ar_arm_body Φ M k av' sp0 ra0 s00 s10 vgap p tfp ws v dqt b.
  Proof.
    destruct k as [|[|[|[|[|[|k']]]]]];
      [ apply ar_arm0 | apply ar_arm1 | apply ar_arm2
      | apply ar_arm3 | apply ar_arm4 | apply ar_arm5 | ].
    cbv beta delta [ar_arm_body]. intro Hk. unfold NARG in Hk. lia.
  Qed.


  Lemma wp_argraw_sconf (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (dqt : dfrac) (b : bool)
    : wp_argraw_sconf_body Φ m av n eb p C i tfp ws v dqt b.
  Proof.
    cbv beta delta [wp_argraw_sconf_body].
    intros pcE ret_tgt Hi Ha0 Hargs Hn Hav.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext #Hdata Hpc Htfp Htf Hcont".
    (* ===================== PROLOGUE (32-byte frame) ===================== *)
    iPoseProof (ari_00 with "Htext") as "Hi00".
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspA0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal; apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m av 4 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (AR + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24". iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".  iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (ar_stk sp0 1 3); lia. }
    assert (Hb2 : pa_stk sp0 2 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (ar_stk sp0 2 2); lia. }
    assert (Hb3 : pa_stk sp0 3 = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite -Hspd4. apply (ar_stk sp0 3 1); lia. }
    iPoseProof (ari_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AR + 0x02)) (mword_of_int 3 : mword 6) ar_ra
              A0 (av - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HcspA0 -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (AR + 0x02) : mword 64) 2 = mword_of_int (AR + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (ari_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AR + 0x04)) (mword_of_int 2 : mword 6) ar_s0
              A0 (av - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HcspA0 -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (AR + 0x04) : mword 64) 2 = mword_of_int (AR + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (ari_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AR + 0x06)) (mword_of_int 1 : mword 6) ar_s1
              A0 (av - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HcspA0 -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hp08 : add_vec_int (mword_of_int (AR + 0x06) : mword 64) 2 = mword_of_int (AR + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HraA0 : A0 !!! Regidx ar_ra = m !!! Regidx ar_ra)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0A0 : A0 !!! Regidx ar_s0 = m !!! Regidx ar_s0)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1A0 : A0 !!! Regidx ar_s1 = m !!! Regidx ar_s1)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite (rget_ne (CID := CID1) A0 ar_ra ltac:(vm_compute; discriminate)) HcspA0 HraA0 -Hb1) in "Hr24".
    iEval (rewrite (rget_ne (CID := CID2) A0 ar_s0 ltac:(vm_compute; discriminate)) HcspA0 Hs0A0 -Hb2) in "Hr16".
    iEval (rewrite (rget_ne (CID := CID3) A0 ar_s1 ltac:(vm_compute; discriminate)) HcspA0 Hs1A0 -Hb3) in "Hr8".
    (* +0x08: c.addi4spn s0,sp,32 *)
    iPoseProof (ari_08 with "Htext") as "Hi08".
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (AR + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) ar_s0
              A0 (av - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx ar_s0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx ar_s0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hp0a : add_vec_int (mword_of_int (AR + 0x08) : mword 64) 2 = mword_of_int (AR + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a: c.mv s1,a0 -- s1 := n *)
    iPoseProof (ari_0a with "Htext") as "Hi0a".
    iApply (wp_cmv_s_sconf Φ (mword_of_int (AR + 0x0a)) ar_s1 ar_a0 A1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A2 := <[Regidx ar_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx ar_a0))]> A1).
    change (<[Regidx ar_s1 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx ar_a0))]> A1) with A2.
    assert (Hp0c : add_vec_int (mword_of_int (AR + 0x0a) : mword 64) 2 = mword_of_int (AR + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    assert (HA2s1 : A2 !!! Regidx ar_s1 = mword_of_int (Z.of_nat i)).
    { rewrite /A2 upd_eq ar_addv_zero_l.
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. exact Ha0. }
    (* +0x0c: jal ra,myproc *)
    iPoseProof (ari_0c with "Htext") as "Hi0c".
    iApply (wp_jal_s_sconf Φ (mword_of_int (AR + 0x0c)) ar_ra (mword_of_int 2093534 : mword 21)
              A2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A3 := <[Regidx ar_ra := regval_into_reg (add_vec_int (mword_of_int (AR + 0x0c) : mword 64) 4)]> A2).
    change (<[Regidx ar_ra := regval_into_reg (add_vec_int (mword_of_int (AR + 0x0c) : mword 64) 4)]> A2) with A3.
    assert (Hjmp : add_vec (mword_of_int (AR + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 2093534 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmp) in "Hpc".
    assert (HA3ra : A3 !!! Regidx ar_ra = add_vec_int (mword_of_int (AR + 0x0c) : mword 64) 4)
      by (rewrite /A3 upd_eq; reflexivity).
    iDestruct (cpu_own_transport CID CID7 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Myproc.wp_myproc_sconf Φ A3 (av - 4)%nat n eb p C b
              Hn ltac:(lia) with "Hcg Hcpu Htext Hpc [-]").
    iIntros (CID8 Hs8 ms MF) "%Hms Hcg Hcpu Hpc %HcsMF".
    destruct HcsMF as [HcsMF HMFa0].
    assert (Hp10 : ret_pc (A3 !!! Regidx ar_ra) = mword_of_int (AR + 0x10))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    assert (HMFsp : MF !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup HcsMF csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspA0. }
    assert (HMFs1 : MF !!! Regidx ar_s1 = mword_of_int (Z.of_nat i)).
    { rewrite (callee_saved_lookup HcsMF ar_s1 ltac:(vm_compute; reflexivity)).
      rewrite /A3 upd_ne; [| vm_compute; discriminate]. exact HA2s1. }
    (* +0x10: c.li a5,5 *)
    iPoseProof (ari_10 with "Htext") as "Hi10".
    iApply (wp_cli_s_sconf Φ (mword_of_int (AR + 0x10)) ar_a5 (mword_of_int 5 : mword 6)
              (mword_of_int 5 : mword 64) MF (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (B0 := <[Regidx ar_a5 := regval_into_reg (mword_of_int 5 : mword 64)]> MF).
    change (<[Regidx ar_a5 := regval_into_reg (mword_of_int 5 : mword 64)]> MF) with B0.
    assert (Hp12 : add_vec_int (mword_of_int (AR + 0x10) : mword 64) 2 = mword_of_int (AR + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    assert (HB0a5 : B0 !!! Regidx ar_a5 = mword_of_int 5) by (rewrite /B0 upd_eq; reflexivity).
    assert (HB0s1 : B0 !!! Regidx ar_s1 = mword_of_int (Z.of_nat i))
      by (rewrite /B0 upd_ne; [exact HMFs1 | vm_compute; discriminate]).
    (* +0x12: bltu a5,s1 -- NOT taken, by the [i < NARG] precondition *)
    iPoseProof (ari_12 with "Htext") as "Hi12".
    iApply (wp_bltu_fall_s_sconf Φ (mword_of_int (AR + 0x12)) (mword_of_int 66 : mword 13) ar_s1 ar_a5
              B0 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite (rget_ne B0 ar_a5 ltac:(vm_compute; discriminate))
                            (rget_ne B0 ar_s1 ltac:(vm_compute; discriminate))
                            HB0a5 HB0s1; exact (ar_bltu_false i Hi))
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    assert (Hp16 : add_vec_int (mword_of_int (AR + 0x12) : mword 64) 4 = mword_of_int (AR + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16: c.slli s1,s1,2 -- s1 := 4n *)
    iPoseProof (ari_16 with "Htext") as "Hi16".
    iApply (wp_cslli_s_sconf Φ (mword_of_int (AR + 0x16)) (Regidx ar_s1) ar_s1 (mword_of_int 2 : mword 6)
              B0 (av - 4)%nat b eq_refl
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (B1 := <[Regidx ar_s1 := regval_into_reg
        (shift_bits_left (B0 !!! Regidx ar_s1) (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0))]> B0).
    change (<[Regidx ar_s1 := regval_into_reg
        (shift_bits_left (B0 !!! Regidx ar_s1) (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0))]> B0) with B1.
    assert (Hp18 : add_vec_int (mword_of_int (AR + 0x16) : mword 64) 2 = mword_of_int (AR + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18/+0x1c: a4 := the jump-table base *)
    iPoseProof (ari_18 with "Htext") as "Hi18".
    iApply (wp_auipc_s_sconf Φ (mword_of_int (AR + 0x18)) ar_a4 (mword_of_int 0x5 : mword 20)
              B1 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (B2 := <[Regidx ar_a4 := regval_into_reg
        (add_vec (mword_of_int (AR + 0x18) : mword 64) (auipc_off (mword_of_int 0x5 : mword 20)))]> B1).
    change (<[Regidx ar_a4 := regval_into_reg
        (add_vec (mword_of_int (AR + 0x18) : mword 64) (auipc_off (mword_of_int 0x5 : mword 20)))]> B1) with B2.
    assert (Hp1c : add_vec_int (mword_of_int (AR + 0x18) : mword 64) 4 = mword_of_int (AR + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    iPoseProof (ari_1c with "Htext") as "Hi1c".
    iApply (wp_addi4_s_sconf Φ (mword_of_int (AR + 0x1c)) ar_a4 ar_a4 (mword_of_int 38 : mword 12)
              B2 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (B3 := <[Regidx ar_a4 := regval_into_reg
        (add_vec (B2 !!! Regidx ar_a4) (sign_extend' 64 (mword_of_int 38 : mword 12)))]> B2).
    change (<[Regidx ar_a4 := regval_into_reg
        (add_vec (B2 !!! Regidx ar_a4) (sign_extend' 64 (mword_of_int 38 : mword 12)))]> B2) with B3.
    assert (Hp20 : add_vec_int (mword_of_int (AR + 0x1c) : mword 64) 4 = mword_of_int (AR + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HB3a4 : B3 !!! Regidx ar_a4 = mword_of_int ar_tbl).
    { rewrite /B3 upd_eq /B2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* +0x20: c.add s1,s1,a4 -- s1 := &tbl[n] *)
    iPoseProof (ari_20 with "Htext") as "Hi20".
    iApply (wp_cadd_s_sconf Φ (mword_of_int (AR + 0x20)) ar_s1 ar_a4 B3 (av - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (B4 := <[Regidx ar_s1 := regval_into_reg (add_vec (B3 !!! Regidx ar_s1) (B3 !!! Regidx ar_a4))]> B3).
    change (<[Regidx ar_s1 := regval_into_reg (add_vec (B3 !!! Regidx ar_s1) (B3 !!! Regidx ar_a4))]> B3) with B4.
    assert (Hp22 : add_vec_int (mword_of_int (AR + 0x20) : mword 64) 2 = mword_of_int (AR + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    assert (HB3s1 : B3 !!! Regidx ar_s1
                    = shift_bits_left (mword_of_int (Z.of_nat i) : mword 64)
                        (subrange_vec_dec (mword_of_int 2 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_eq HB0s1. reflexivity. }
    assert (HB4s1 : B4 !!! Regidx ar_s1 = mword_of_int (ar_tbl + 4 * Z.of_nat i)).
    { rewrite /B4 upd_eq HB3s1 HB3a4.
      unfold NARG in Hi. destruct i as [|[|[|[|[|[|i']]]]]]; try lia;
        apply bv_eq; vm_compute; reflexivity. }
    (* generic facts about the B-chain, for the six arms' [callee_saved]. *)
    assert (HBthr : forall r : mword 5, is_cs_idx r = true ->
                      r <> csp_rs1 -> r <> ar_s0 -> r <> ar_s1 ->
                      B4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /B4 upd_ne; [| congruence].
      rewrite /B3 upd_ne; [| congruence].
      rewrite /B2 upd_ne; [| congruence].
      rewrite /B1 upd_ne; [| congruence].
      rewrite /B0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsMF r Hr).
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 4).
    { rewrite Hspd4 /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact HMFsp. }
    assert (HB4a0 : B4 !!! Regidx ar_a0 = p).
    { rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      rewrite /B2 upd_ne; [| vm_compute; discriminate].
      rewrite /B1 upd_ne; [| vm_compute; discriminate].
      rewrite /B0 upd_ne; [| vm_compute; discriminate]. exact HMFa0. }
    assert (HB4a4 : B4 !!! Regidx ar_a4 = mword_of_int ar_tbl)
      by (rewrite /B4 upd_ne; [exact HB3a4 | vm_compute; discriminate]).
    (* ================= the arm, applied ONCE at a symbolic index ======= *)
    iApply (ar_arm Φ B4 i (av - 4)%nat sp0 (m !!! Regidx ar_ra) (m !!! Regidx ar_s0)
                   (m !!! Regidx ar_s1) vgap p tfp ws v dqt b
              Hi Hargs HB4s1 HB4a4 HB4a0 HB4sp
              with "Htext Hdata Hcg Hpc Htfp Htf Hr24 Hr16 Hr8 Hgap [-]").
    iIntros (CID15 Hs15 Mf) "%HMf Hcg Hpc Htfp Htf".
    destruct HMf as (Hfsp & Hfs0 & Hfs1 & Hfa0 & Hfthr).
    assert (Hnk : ((av - 4) + 4)%nat = av) by lia.
    iEval (rewrite Hnk) in "Hcg".
    iDestruct (cpu_own_transport CID8 CID15 n eb p C b ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iSpecialize ("Hcont" $! CID15 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Mf with "[%] Hcg Hcpu Hpc Htfp Htf").
    split; [| exact Hfa0].
    unfold callee_saved.
    split; [exact Hfsp|].
    split; [exact Hfs0|]. split; [exact Hfs1|].
    repeat (split; [rewrite Hfthr; [apply HBthr | ..]; vm_compute; first [reflexivity | discriminate]|]).
    rewrite Hfthr; [apply HBthr | ..]; vm_compute; first [reflexivity | discriminate].
  Qed.

End ProofArgraw.

End ArgrawProof.

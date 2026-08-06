(* CodeArgrawAux.v -- the machine code of argraw(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofArgraw.v. *)

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
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
Require Import ProcGeom.
Require Import InstrBytes.
From Kernel Require KernelInstrs KernelData.
From Kernel Require KernelSyms.
Require Import CodeArgraw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation ar_ra := (mword_of_int 1 : mword 5).
Notation ar_s1 := (mword_of_int 9 : mword 5).
Notation ar_a0 := (mword_of_int 10 : mword 5).
Notation ar_a4 := (mword_of_int 14 : mword 5).
Notation ar_a5 := (mword_of_int 15 : mword 5).

Section CodeArgrawAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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
Notation ARI o t d := (kernel_text -∗ instr (mword_of_int (KernelSyms.argraw + o) : mword 64) t d).
(* every arm: c.ld a5,88(a0)  -- p->trapframe *)
Lemma ardec_ld_tf s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6d3c : mword 16)) s = Some (C_LD (mword_of_int 11, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_28 : ARI 0x28 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x28)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
Lemma ari_36 : ARI 0x36 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x36)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
Lemma ari_3c : ARI 0x3c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x3c)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
Lemma ari_42 : ARI 0x42 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x42)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
Lemma ari_48 : ARI 0x48 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x48)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
Lemma ari_4e : ARI 0x4e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x4e)%Z (mword_of_int 0x6d3c : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) ardec_ld_tf exec_execute_C_LD. Qed.
(* case 0: c.ld a0,112(a5)  -- tf->a0 *)
Lemma ardec_ld_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ba8 : mword 16)) s = Some (C_LD (mword_of_int 14, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_2a : ARI 0x2a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x2a)%Z (mword_of_int 0x7ba8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a0 exec_execute_C_LD. Qed.
(* case 1: c.ld a0,120(a5)  -- tf->a1 *)
Lemma ardec_ld_a1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7fa8 : mword 16)) s = Some (C_LD (mword_of_int 15, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_38 : ARI 0x38 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x38)%Z (mword_of_int 0x7fa8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a1 exec_execute_C_LD. Qed.
(* case 2: c.ld a0,128(a5)  -- tf->a2 *)
Lemma ardec_ld_a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x63c8 : mword 16)) s = Some (C_LD (mword_of_int 16, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_3e : ARI 0x3e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x3e)%Z (mword_of_int 0x63c8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a2 exec_execute_C_LD. Qed.
(* case 3: c.ld a0,136(a5)  -- tf->a3 *)
Lemma ardec_ld_a3 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x67c8 : mword 16)) s = Some (C_LD (mword_of_int 17, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_44 : ARI 0x44 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 17 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x44)%Z (mword_of_int 0x67c8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 17 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a3 exec_execute_C_LD. Qed.
(* case 4: c.ld a0,144(a5)  -- tf->a4 *)
Lemma ardec_ld_a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6bc8 : mword 16)) s = Some (C_LD (mword_of_int 18, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_4a : ARI 0x4a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 18 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x4a)%Z (mword_of_int 0x6bc8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 18 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a4 exec_execute_C_LD. Qed.
(* case 5: c.ld a0,152(a5)  -- tf->a5 *)
Lemma ardec_ld_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6fc8 : mword 16)) s = Some (C_LD (mword_of_int 19, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_50 : ARI 0x50 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 19 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof. mk_rvc (KernelSyms.argraw + 0x50)%Z (mword_of_int 0x6fc8 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 19 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) ardec_ld_a5 exec_execute_C_LD. Qed.
Lemma ari_3a : ARI 0x3a true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
Proof. mk_rvc (KernelSyms.argraw + 0x3a)%Z (mword_of_int 0xbfcd : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x3a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.
(* case 2 tail: c.j +0x2c *)
Lemma ardec_cj2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7f5 : mword 16)) s = Some (C_J (mword_of_int 2038 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma ari_40 : ARI 0x40 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")), zreg)).
Proof. mk_rvc (KernelSyms.argraw + 0x40)%Z (mword_of_int 0xb7f5 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x40) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2038 : mword 11) ('b"0")), zreg)) ardec_cj2 exec_execute_C_J. Qed.
Lemma ari_46 : ARI 0x46 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)).
Proof. mk_rvc (KernelSyms.argraw + 0x46)%Z (mword_of_int 0xb7dd : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x46) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)) cdec_b7dd exec_execute_C_J. Qed.
Lemma ari_4c : ARI 0x4c true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)).
Proof. mk_rvc (KernelSyms.argraw + 0x4c)%Z (mword_of_int 0xb7c5 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x4c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)) cdec_b7c5 exec_execute_C_J. Qed.
Lemma ari_52 : ARI 0x52 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)).
Proof. mk_rvc (KernelSyms.argraw + 0x52)%Z (mword_of_int 0xbfe9 : mword 16)
  (mword_of_int (KernelSyms.argraw + 0x52) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)) cdec_bfe9 exec_execute_C_J. Qed.

(* +0x10  c.li a5,5 *)

(* +0x16  c.slli s1,s1,2  -- s1 := 4n *)

(* +0x20  c.add s1,s1,a4  -- s1 := &tbl[n] *)

(* +0x26  c.jr a5         -- THE indirect jump *)

(* +0x0c  jal ra,myproc  (0x80002726 -> 0x80001904 = -3618) *)

(* +0x12  bltu a5,s1,+0x54 -- the panic arm, refuted by i < NARG *)

(* +0x18  auipc a4,0x5 *)

(* +0x1c  addi a4,a4,38 -- a4 := 0x80007758, the table base *)

(* ================================================================== *)
(* Per-case dispatch: the ONLY six-way [destruct]s, each on a TINY     *)
(* goal.  Splitting inside the capstone instead cost 81 s and ~74 GB   *)
(* -- Coq retains all six arms' Iris proof terms until [Qed], and each *)
(* branch re-typechecks the dependently-typed Sail bitvector context.  *)
(* ================================================================== *)
Lemma ar_i_tf (k : nat) : (k < NARG)%nat ->
  kernel_text -∗ instr (mword_of_int (KernelSyms.argraw + ar_case_off k) : mword 64) true
    (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 5) ('b"000")),
           creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
Proof.
  intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia; cbn [ar_case_off];
    [ exact ari_28 | exact ari_36 | exact ari_3c | exact ari_42 | exact ari_48 | exact ari_4e ].
Qed.
Lemma ar_i_ld (k : nat) : (k < NARG)%nat ->
  kernel_text -∗ instr (mword_of_int (KernelSyms.argraw + ar_ld_off k) : mword 64) true
    (LOAD (zero_extend' 12 (concat_vec (mword_of_int (14 + Z.of_nat k) : mword 5) ('b"000")),
           creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
Proof.
  intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
    cbn [ar_ld_off Z.of_nat]; cbn [Z.add];
    [ exact ari_2a | exact ari_38 | exact ari_3e | exact ari_44 | exact ari_4a | exact ari_50 ].
Qed.
Lemma ar_i_cj (k : nat) : (1 <= k < NARG)%nat ->
  kernel_text -∗ instr (mword_of_int (KernelSyms.argraw + ar_ld_off k + 2) : mword 64) true
    (JAL (sign_extend' 21 (concat_vec (mword_of_int (ar_cj_imm k) : mword 11) ('b"0")), zreg)).
Proof.
  intro Hk. unfold NARG in Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
    cbn [ar_ld_off ar_cj_imm];
    [ exact ari_3a | exact ari_40 | exact ari_46 | exact ari_4c | exact ari_52 ].
Qed.

End CodeArgrawAux.

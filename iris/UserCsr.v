(* UserCsr.v -- CSR access at User privilege: the totality facts for the
   CSRReg / CSRImm families.

   VALUES NEVER MATTER (safety only): a permitted CSR access at U is a
   RETIRING READ of an existential value (the counter shadows, when the
   counter-enable bits allow them); everything else is Illegal.  The
   target statements and the proof driver are recorded in
   iris/CLAUDE.md (§CSR-AT-U PLAN): destruct each dispatch guard
   [eq_vec csr ADDR] with eqn:, SUBSTITUTE csr := ADDR in the true
   branch (everything downstream reduces concretely), chain the false
   branches linearly; the priv-bits compare is destructed first and
   kills every non-U-addressed csr in one split.

   §1 holds the extension-gate PROBE reductions the U-addressed clauses
   need: the xv6 config pins make each gate a closed boolean.           *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr WpLeafCommon.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 Extension-gate probes at the xv6 config.                            *)
(* ===================================================================== *)

(* Zfinx is not hart-supported: the gate is a closed false. *)
Lemma exec_currentlyEnabled_Zfinx (s : mstate) :
  exec (currentlyEnabled Ext_Zfinx) s = Some (false, s).
Proof. reflexivity. Qed.

Lemma exec_hartSupports_F (s : mstate) :
  exec (hartSupports Ext_F) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_F) 0) with true by reflexivity.
  cbn match.
  first [ apply exec_returnM
        | rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s));
          apply exec_returnM
        | reflexivity ].
Qed.

(* F is hart-supported and misa.F is set, but the FS = Off pin turns the
   gate false BEFORE the Zicsr recursion (and_boolM short-circuits), so
   the fflags/frm/fcsr clauses are ILLEGAL at U. *)
Lemma exec_currentlyEnabled_F_off (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  exec (currentlyEnabled Ext_F) s = Some (false, s).
Proof.
  intros Hms Hfs.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_F) 0) with true.
  cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_F s)).
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_F (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb;
    [ | reflexivity ].
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
      rewrite Hms. apply exec_returnM. }
  assert (Hneq : neq_vec (_get_Mstatus_FS ms_v) ('b"00") = false).
  { unfold neq_vec. rewrite Hfs. reflexivity. }
  rewrite Hneq.
  reflexivity.
Qed.

(* the hart-supported flags the U-addressed gates consult *)
Lemma exec_hartSupports_Zicntr (s : mstate) :
  exec (hartSupports Ext_Zicntr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zicntr) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicfiss (s : mstate) :
  exec (hartSupports Ext_Zicfiss) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zimop (s : mstate) :
  exec (hartSupports Ext_Zimop) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zimop) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zaamo (s : mstate) :
  exec (hartSupports Ext_Zaamo) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zaamo) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma exec_hartSupports_A (s : mstate) :
  exec (hartSupports Ext_A) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_A) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

(* limit-instantiated recursive probes (the Zicfiss clause runs its
   sub-probes at measure-1 = 1, and Zaamo's Ext_A at 0) *)
Lemma exec_rec_cE_Zicsr_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  exec (_rec_currentlyEnabled Ext_Zicsr 1 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_rec_cE_Zimop_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  exec (_rec_currentlyEnabled Ext_Zimop 1 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_hartSupports_Zimop.
Qed.

Lemma exec_rec_cE_A_0 (s : mstate) (acc : Acc (Zwf 0) 0) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (_rec_currentlyEnabled Ext_A 0 acc) s = Some (true, s).
Proof.
  intro Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_A s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). cbn beta.
  rewrite Hmisa.
  replace (eq_vec (_get_Misa_A MISA_C) ('b"1")) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zaamo_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (_rec_currentlyEnabled Ext_Zaamo 1 acc) s = Some (true, s).
Proof.
  intro Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  unfold or_boolM.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_hartSupports_Zaamo s)). cbn beta. cbn match.
  apply exec_rec_cE_A_0. exact Hmisa.
Qed.

(* the two gates the U-addressed CSR clauses actually consult *)
Lemma exec_currentlyEnabled_Zicntr (s : mstate) :
  exec (currentlyEnabled Ext_Zicntr) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicntr s)).
  apply exec_rec_cE_Zicsr.
Qed.

Lemma exec_currentlyEnabled_Zicfiss (s : mstate) :
  register_lookup misa s.(sregs) = MISA_C ->
  exec (currentlyEnabled Ext_Zicfiss) s = Some (true, s).
Proof.
  intro Hmisa.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfiss s)).
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_rec_cE_Zicsr_1 s _)).
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_rec_cE_Zimop_1 s _)).
  apply exec_rec_cE_Zaamo_1. exact Hmisa.
Qed.

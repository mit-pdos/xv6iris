(* UserCsr.v -- CSR access at User privilege: the totality facts for the
   CSRReg / CSRImm families.

   VALUES NEVER MATTER (safety only): a permitted CSR access at U is a
   RETIRING READ of an existential value (the counter shadows, when the
   counter-enable bits allow them); everything else is Illegal.  The
   proof driver: destruct each dispatch guard
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
Require Import RiscvExtras WpGpr WpGprCsrrCommon UserBits UserExecFacts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE [goodmb] TWINS (the <exec, goodmb> pair convention).               *)
(*                                                                        *)
(* Every [exec_X] below has a [goodmb_X] immediately after it, with the    *)
(* SAME binders and hypotheses plus one [Dr r = true] per register the     *)
(* stretch READS and one [Dw r = true] per register it WRITES, over        *)
(* abstract [Dr]/[Dw].  All at [mm := ∅]: the CSR families touch no        *)
(* memory, and [HartMemRun.goodmb_map_mono] lifts an ∅-certificate to any  *)
(* map.  Where the exec fact is EXISTENTIAL in the result the twin is      *)
(* unconditional -- a certificate does not depend on the outcome -- which  *)
(* is why the accessibility traversal's twin has no                        *)
(* [u_csr_readable] obligation and is strictly shorter than its exec twin. *)
(*                                                                        *)
(* THE 200-CLAUSE TRAVERSAL COSTS ALMOST NOTHING TO MIRROR: the dispatch   *)
(* guards are PURE (address-bit comparisons, no reads), so                 *)
(* [gm_csr_step] is [csr_step] with the [exists _, exec _ = Some _ /\ _]   *)
(* pattern replaced by [goodmb _ _ _ _ _ = true] and the per-clause result *)
(* obligations DELETED.  The dead branches die on exactly the same three   *)
(* facts ([pmp_subrange_dead], [hpm_subrange_dead], the priv gate).        *)
(* ===================================================================== *)
Require Import HartMemRun.

(* ===================================================================== *)
(* §1 Extension-gate probes at the xv6 config.                            *)
(* ===================================================================== *)

(* the hartSupports probes read NOTHING, so their certificate is the same
   walk with [goodmb] in place of [exec]. *)
Ltac gm_hs X :=
  unfold hartSupports; destruct (Defs.Zwf_guarded _);
  cbn [_rec_hartSupports]; unfold Defs.assert_exp';
  replace (Z.geb (hartSupports_measure X) 0) with true by reflexivity;
  cbn match;
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply exec_returnM ];
  cbn beta; apply goodmb_returnm.
(* Zfinx is not hart-supported: the gate is a closed false. *)
Lemma exec_currentlyEnabled_Zfinx (s : mstate) :
  exec (currentlyEnabled Ext_Zfinx) s = Some (false, s).
Proof. reflexivity. Qed.

Lemma goodmb_currentlyEnabled_Zfinx (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (currentlyEnabled Ext_Zfinx) s mm = true.
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

Lemma goodmb_hartSupports_F (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_F) s mm = true.
Proof. gm_hs Ext_F. Qed.

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

Lemma goodmb_currentlyEnabled_F_off (Dr Dw : register -> bool) (s : mstate)
    (ms_v : mword 64) :
  Dr misa = true -> Dr mstatus = true ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  goodmb Dr Dw (currentlyEnabled Ext_F) s ∅ = true.
Proof.
  intros HDmi HDms Hms Hfs.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_F) 0) with true.
  cbn match. gm_pure. cbn beta. cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_F | apply (exec_hartSupports_F s) ].
  cbn match.
  erewrite goodmb_and_boolM_empty.
  2:{ gm_rr misa HDmi. apply goodmb_returnm. }
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_F (register_lookup misa s.(sregs))) ('b"1"));
    [ | reflexivity ].
  erewrite goodmb_and_boolM_empty.
  2:{ gm_rr mstatus HDms. cbn beta. apply goodmb_returnm. }
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
      rewrite Hms. apply exec_returnM. }
  assert (Hneq : neq_vec (_get_Mstatus_FS ms_v) ('b"00") = false)
    by (unfold neq_vec; rewrite Hfs; reflexivity).
  rewrite Hneq. reflexivity.
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

Lemma goodmb_hartSupports_Zicntr (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zicntr) s mm = true.
Proof. gm_hs Ext_Zicntr. Qed.

Lemma exec_hartSupports_Zicfiss (s : mstate) :
  exec (hartSupports Ext_Zicfiss) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_Zicfiss (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zicfiss) s mm = true.
Proof. gm_hs Ext_Zicfiss. Qed.

Lemma exec_hartSupports_Zimop (s : mstate) :
  exec (hartSupports Ext_Zimop) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zimop) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_Zimop (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zimop) s mm = true.
Proof. gm_hs Ext_Zimop. Qed.

Lemma exec_hartSupports_Zaamo (s : mstate) :
  exec (hartSupports Ext_Zaamo) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zaamo) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_Zaamo (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zaamo) s mm = true.
Proof. gm_hs Ext_Zaamo. Qed.

Lemma exec_hartSupports_A (s : mstate) :
  exec (hartSupports Ext_A) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_A) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_A (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_A) s mm = true.
Proof. gm_hs Ext_A. Qed.

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

Lemma goodmb_rec_cE_Zicsr_1 (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 1) mm :
  goodmb Dr Dw (_rec_currentlyEnabled Ext_Zicsr 1 acc) s mm = true.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. apply goodmb_hartSupports_Zicsr.
Qed.

Lemma exec_rec_cE_Zimop_1 (s : mstate) (acc : Acc (Zwf 0) 1) :
  exec (_rec_currentlyEnabled Ext_Zimop 1 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_hartSupports_Zimop.
Qed.

Lemma goodmb_rec_cE_Zimop_1 (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 1) mm :
  goodmb Dr Dw (_rec_currentlyEnabled Ext_Zimop 1 acc) s mm = true.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. apply goodmb_hartSupports_Zimop.
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

Lemma goodmb_rec_cE_A_0 (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 0) :
  Dr misa = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  goodmb Dr Dw (_rec_currentlyEnabled Ext_A 0 acc) s ∅ = true.
Proof.
  intros HDmi Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_A | apply (exec_hartSupports_A s) ].
  cbn match. gm_rr misa HDmi. cbn beta. apply goodmb_returnm.
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

Lemma goodmb_rec_cE_Zaamo_1 (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 1) :
  Dr misa = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  goodmb Dr Dw (_rec_currentlyEnabled Ext_Zaamo 1 acc) s ∅ = true.
Proof.
  intros HDmi Hmisa.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 1 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta.
  erewrite goodmb_or_boolM_empty;
    [ | apply goodmb_hartSupports_Zaamo | apply (exec_hartSupports_Zaamo s) ].
  cbn match. apply goodmb_rec_cE_A_0; assumption.
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

Lemma goodmb_currentlyEnabled_Zicntr (Dr Dw : register -> bool) (s : mstate) :
  goodmb Dr Dw (currentlyEnabled Ext_Zicntr) s ∅ = true.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicntr) 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_Zicntr | apply (exec_hartSupports_Zicntr s) ].
  cbn match. apply goodmb_rec_cE_Zicsr.
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

Lemma goodmb_currentlyEnabled_Zicfiss (Dr Dw : register -> bool) (s : mstate) :
  Dr misa = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  goodmb Dr Dw (currentlyEnabled Ext_Zicfiss) s ∅ = true.
Proof.
  intros HDmi Hmisa.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zicfiss) 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_Zicfiss | apply (exec_hartSupports_Zicfiss s) ].
  cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_rec_cE_Zicsr_1 | apply (exec_rec_cE_Zicsr_1 s _) ].
  cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_rec_cE_Zimop_1 | apply (exec_rec_cE_Zimop_1 s _) ].
  cbn match.
  apply goodmb_rec_cE_Zaamo_1; assumption.
Qed.

(* Zve32x: NOT hart-supported.  It comes from V's [support_level], which
   model-xv6iris/sail-config-rv64d.json sets to "Disabled" (the kernel is
   rv64gc -- see that file's header), so the vector gates are off at the
   HART-support level and never reach the mstatus.VS check below. *)
Lemma exec_hartSupports_Zve32x (s : mstate) :
  exec (hartSupports Ext_Zve32x) s = Some (false, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zve32x) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  match goal with
  | |- exec (returnM ?v) _ = _ =>
      replace v with false by (vm_compute; reflexivity)
  end.
  apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_Zve32x (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zve32x) s mm = true.
Proof. gm_hs Ext_Zve32x. Qed.

Lemma exec_rec_cE_Zvl32b_0 (s : mstate) (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zvl32b 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta.
  match goal with
  | |- exec ?m _ = _ =>
      first [ apply exec_returnM
            | match m with
              | returnM ?v =>
                  replace v with true by (vm_compute; reflexivity)
              end; apply exec_returnM ]
  end.
Qed.

Lemma goodmb_rec_cE_Zvl32b_0 (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 0) mm :
  goodmb Dr Dw (_rec_currentlyEnabled Ext_Zvl32b 0 acc) s mm = true.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb 0 0) with true. cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. apply goodmb_returnm.
Qed.

Lemma exec_currentlyEnabled_Zve32x_off (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  exec (currentlyEnabled Ext_Zve32x) s = Some (false, s).
Proof.
  (* THE mstatus.VS PREMISES ARE NO LONGER NEEDED, and the statement keeps them
     anyway so no caller churns (the wrapper recipe): with V disabled in the
     model's config, [hartSupports Ext_Zve32x] is already false and
     [and_boolM] short-circuits before the VS read. *)
  intros _ _.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zve32x) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zve32x s)).
  reflexivity.
Qed.

Lemma goodmb_currentlyEnabled_Zve32x_off (Dr Dw : register -> bool) (s : mstate)
    (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  goodmb Dr Dw (currentlyEnabled Ext_Zve32x) s ∅ = true.
Proof.
  intros _ _.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zve32x) 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_Zve32x | apply (exec_hartSupports_Zve32x s) ].
  reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The check-chain component reductions.                               *)
(* ===================================================================== *)

(* the privilege gate at User: pure in the ADDRESS bits -- 'b00 ≥u
   csrPriv csr, i.e. true iff bits 9:8 are 00 *)
Lemma exec_check_CSR_priv_U (csr : mword 12) (s : mstate) :
  exec (check_CSR_priv csr User) s
    = Some (zopz0zKzJ_u ('b"00") (csrPriv csr), s).
Proof.
  unfold check_CSR_priv, privLevel_to_CSR_privbits. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"00" : mword 2) s)). cbn beta.
  apply exec_returnM.
Qed.

Lemma goodmb_check_CSR_priv_U (Dr Dw : register -> bool) (csr : mword 12)
    (s : mstate) :
  goodmb Dr Dw (check_CSR_priv csr User) s ∅ = true.
Proof.
  unfold check_CSR_priv, privLevel_to_CSR_privbits. cbn match.
  erewrite goodmb_bind_empty;
    [ | apply goodmb_returnm | apply (exec_returnM ('b"00" : mword 2) s) ].
  cbn beta. apply goodmb_returnm.
Qed.

(* feature_enabled_for_priv at U, totality: SOME result comes out
   whatever the enable bits are (all booleans destructed up front). *)
Lemma exec_feature_U_total (m sb h : mword 1) (s : mstate) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists r, exec (feature_enabled_for_priv User m sb h) s = Some (r, s).
Proof.
  intro HES.
  unfold feature_enabled_for_priv. cbn match.
  unfold and_boolM, or_boolM.
  destruct (eq_vec m ('b"1")) eqn:E1.
  - (* m-bit set: the S/senv disjunct decides *)
    destruct (eq_vec sb ('b"1")) eqn:E2.
    + eexists.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
          cbn beta. cbn match.
          erewrite exec_bind_Some.
          2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta.
              apply exec_returnM. }
          cbn beta. cbn [not negb]. cbn match.
          apply exec_returnM. }
      cbn beta. cbv zeta.
      apply exec_returnM.
    + eexists.
      erewrite exec_bind_Some.
      2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
          cbn beta. cbn match.
          erewrite exec_bind_Some.
          2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta.
              apply exec_returnM. }
          cbn beta. cbn [not negb]. cbn match.
          apply exec_returnM. }
      cbn beta. cbv zeta.
      apply exec_returnM.
  - (* m-bit clear: short-circuit false *)
    eexists.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind_Some; [ | apply exec_returnM ].
        cbn beta. cbn match.
        apply exec_returnM. }
    cbn beta. cbv zeta.
    apply exec_returnM.
Qed.

Lemma goodmb_feature_U (Dr Dw : register -> bool) (m sb h : mword 1) (s : mstate) :
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (feature_enabled_for_priv User m sb h) s ∅ = true.
Proof.
  intros HgES HES.
  unfold feature_enabled_for_priv. cbn match.
  unfold and_boolM, or_boolM.
  destruct (eq_vec m ('b"1")).
  - erewrite goodmb_bind_empty.
    2:{ erewrite goodmb_bind_empty;
          [ | apply goodmb_returnm | apply (exec_returnM true s) ].
        cbn beta. cbn match.
        erewrite goodmb_bind_empty.
        2:{ erewrite goodmb_bind_empty; [ | exact HgES | exact HES ].
            cbn beta. apply goodmb_returnm. }
        2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta. apply exec_returnM. }
        cbn beta. cbn [not negb]. cbn match. apply goodmb_returnm. }
    2:{ erewrite exec_bind_Some; [ | apply (exec_returnM true s) ].
        cbn beta. cbn match.
        erewrite exec_bind_Some.
        2:{ rewrite (exec_bind_Some _ _ _ _ _ HES). cbn beta. apply exec_returnM. }
        cbn beta. cbn [not negb]. cbn match. apply exec_returnM. }
    cbn beta. cbv zeta. apply goodmb_returnm.
  - erewrite goodmb_bind_empty.
    2:{ erewrite goodmb_bind_empty;
          [ | apply goodmb_returnm | apply (exec_returnM false s) ].
        cbn beta. cbn match. apply goodmb_returnm. }
    2:{ erewrite exec_bind_Some; [ | apply (exec_returnM false s) ].
        cbn beta. cbn match. apply exec_returnM. }
    cbn beta. cbv zeta. apply goodmb_returnm.
Qed.

(* counter enables at U: SOME boolean comes out (values never matter) *)
Lemma exec_counter_enabled_U_total (i : Z) (s : mstate) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists en : bool, exec (counter_enabled i User) s = Some (en, s).
Proof.
  intro HES.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)). cbn beta.
  unfold feature_enabled_for_priv_bool.
  destruct (exec_feature_U_total
              (access_vec_dec (register_lookup mcounteren s.(sregs)) i)
              (access_vec_dec (register_lookup scounteren s.(sregs)) i)
              ('b"0") s HES) as [r Hr].
  eexists.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  apply exec_returnM.
Qed.

Lemma goodmb_counter_enabled_U (Dr Dw : register -> bool) (i : Z) (s : mstate) :
  Dr mcounteren = true -> Dr scounteren = true ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (counter_enabled i User) s ∅ = true.
Proof.
  intros HDmc HDsc HgES HES.
  unfold counter_enabled.
  gm_rr mcounteren HDmc. cbn beta.
  gm_rr scounteren HDsc. cbn beta.
  unfold feature_enabled_for_priv_bool.
  destruct (exec_feature_U_total
              (access_vec_dec (register_lookup mcounteren s.(sregs)) i)
              (access_vec_dec (register_lookup scounteren s.(sregs)) i)
              ('b"0") s HES) as [r Hr].
  erewrite goodmb_bind_empty; [ | apply goodmb_feature_U; assumption | exact Hr ].
  cbn beta. apply goodmb_returnm.
Qed.

(* ssp (0x011) is inaccessible: Zicfiss is enabled, but MENVCFG_S has SSE
   clear, so the User arm's menvcfg conjunct is false (and_boolM
   short-circuits before senvcfg is consulted). *)
Lemma exec_is_ssp_accessible_U_off (s : mstate) :
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (is_ssp_accessible User) s = Some (false, s).
Proof.
  intros Hmisa Hmenv.
  unfold is_ssp_accessible.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicfiss s Hmisa)).
  cbn match.
  erewrite exec_and_boolM_Some.
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
      rewrite Hmenv. apply exec_returnM. }
  match goal with
  | |- context [ if ?g then _ else _ ] =>
      replace g with false by (vm_compute; reflexivity)
  end.
  reflexivity.
Qed.

Lemma goodmb_is_ssp_accessible_U_off (Dr Dw : register -> bool) (s : mstate) :
  Dr misa = true -> Dr menvcfg = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (is_ssp_accessible User) s ∅ = true.
Proof.
  intros HDmi HDme Hmisa Hmenv.
  unfold is_ssp_accessible.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_currentlyEnabled_Zicfiss; assumption
      | apply (exec_currentlyEnabled_Zicfiss s Hmisa) ].
  cbn match.
  erewrite goodmb_and_boolM_empty.
  2:{ gm_rr menvcfg HDme. cbn beta. apply goodmb_returnm. }
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
      rewrite Hmenv. apply exec_returnM. }
  match goal with
  | |- context [ if ?g then _ else _ ] =>
      replace g with false by (vm_compute; reflexivity)
  end.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The traversal groundwork: address-bit arithmetic.                   *)
(* ===================================================================== *)

(* the two CSR-address subranges, as unsigned arithmetic *)
Lemma sub114_unsigned (x : mword 12) :
  bv_unsigned (subrange_vec_dec x 11 4) = (bv_unsigned x / 16) mod 256.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (11 - 4 + 1))) with 256.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 4)) with 4.
  change (2 ^ 4) with 16.
  reflexivity.
Qed.

Lemma csrPriv_unsigned (x : mword 12) :
  bv_unsigned (csrPriv x) = (bv_unsigned x / 256) mod 4.
Proof.
  unfold csrPriv, subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (9 - 8 + 1))) with 4.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 8.
  change (2 ^ 8) with 256.
  reflexivity.
Qed.

(* a PMP-file subrange guard contradicts the U priv gate: the address's
   bits 9:8 sit inside the matched high byte (0x3A-0x3E all have bits
   5:4 = 11, i.e. h / 16 = 3). *)
Lemma pmp_subrange_dead (csr : mword 12) (h : mword 8) :
  eq_vec (subrange_vec_dec csr 11 4) h = true ->
  bv_unsigned h / 16 = 3 ->
  zopz0zKzJ_u ('b"00") (csrPriv csr) = true -> False.
Proof.
  intros E Hh EP.
  apply eq_vec_true_iff in E.
  apply (f_equal bv_unsigned) in E.
  rewrite sub114_unsigned in E.
  unfold zopz0zKzJ_u in EP. apply Z.geb_le in EP.
  rewrite !(uint_unsigned_n _) in EP.
  rewrite csrPriv_unsigned in EP.
  change (bv_unsigned ('b"00" : mword 2)) with 0 in EP.
  set (c := bv_unsigned csr) in *.
  pose proof (Z.mod_pos_bound (c / 256) 4 ltac:(lia)) as Hb.
  assert (Hz : (c / 256) mod 4 = 0) by lia.
  assert (Hdd : c / 256 = (c / 16) / 16).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 16) in *.
  assert (Hh16 : q / 16 = 16 * (q / 256) + 3).
  { assert (Hq2 : q = 16 * (q / 256) * 16 + bv_unsigned h).
    { pose proof (Z_div_mod_eq_full q 256) as Hd.
      rewrite E in Hd.
      replace (16 * (q / 256) * 16) with (256 * (q / 256)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia.
    rewrite Hh. reflexivity. }
  rewrite Hdd, Hh16 in Hz.
  replace (16 * (q / 256) + 3) with (3 + (q / 256) * 4 * 4) in Hz by lia.
  rewrite Z_mod_plus_full in Hz.
  vm_compute in Hz. discriminate Hz.
Qed.

(* ===================================================================== *)
(* §3b The accessibility traversal at User.                               *)
(* ===================================================================== *)

(* the complete U-accessible read set under the xv6 pins: the three
   Zicntr counter shadows plus the Zihpm hpmcounter(h) shadow ranges *)
Definition u_hpm_range (csr : mword 12) (k : mword 7) : Prop :=
  eq_vec (subrange_vec_dec csr 11 5) k = true /\
  Z.geb (uint (subrange_vec_dec csr 4 0)) 3 = true.

Definition u_csr_readable (csr : mword 12) : Prop :=
  csr = Ox"C00" \/ csr = Ox"C01" \/ csr = Ox"C02" \/
  u_hpm_range csr ('b"1100000").

Lemma exec_hartSupports_Zihpm (s : mstate) :
  exec (hartSupports Ext_Zihpm) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  change (Z.geb (hartSupports_measure Ext_Zihpm) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. apply exec_returnM.
Qed.

Lemma goodmb_hartSupports_Zihpm (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zihpm) s mm = true.
Proof. gm_hs Ext_Zihpm. Qed.

Lemma exec_currentlyEnabled_Zihpm (s : mstate) :
  exec (currentlyEnabled Ext_Zihpm) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zihpm) 0) with true. cbn match.
  erewrite exec_bind_Some. 2:{ apply exec_returnM. }
  cbn beta. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zihpm s)).
  apply exec_rec_cE_Zicsr.
Qed.

Lemma goodmb_currentlyEnabled_Zihpm (Dr Dw : register -> bool) (s : mstate) :
  goodmb Dr Dw (currentlyEnabled Ext_Zihpm) s ∅ = true.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Zihpm) 0) with true. cbn match.
  erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
  cbn beta. cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_Zihpm | apply (exec_hartSupports_Zihpm s) ].
  cbn match. apply goodmb_rec_cE_Zicsr.
Qed.

Lemma sub115_unsigned (x : mword 12) :
  bv_unsigned (subrange_vec_dec x 11 5) = (bv_unsigned x / 32) mod 128.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (11 - 5 + 1))) with 128.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 5)) with 5.
  change (2 ^ 5) with 32.
  reflexivity.
Qed.

(* an hpm-family 11:5 subrange guard whose high byte is M/S-addressed
   contradicts the U priv gate (bits 9:8 of csr = bits 4:3 of the key) *)
Lemma hpm_subrange_dead (csr : mword 12) (k : mword 7) :
  eq_vec (subrange_vec_dec csr 11 5) k = true ->
  (bv_unsigned k / 8) mod 4 <> 0 ->
  zopz0zKzJ_u ('b"00") (csrPriv csr) = true -> False.
Proof.
  intros E Hk EP.
  apply eq_vec_true_iff in E.
  apply (f_equal bv_unsigned) in E.
  rewrite sub115_unsigned in E.
  unfold zopz0zKzJ_u in EP. apply Z.geb_le in EP.
  rewrite !(uint_unsigned_n _) in EP.
  rewrite csrPriv_unsigned in EP.
  change (bv_unsigned ('b"00" : mword 2)) with 0 in EP.
  set (c := bv_unsigned csr) in *.
  pose proof (Z.mod_pos_bound (c / 256) 4 ltac:(lia)) as Hb.
  assert (Hz : (c / 256) mod 4 = 0) by lia.
  assert (Hdd : c / 256 = (c / 32) / 8).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 32) in *.
  assert (Hh8 : q / 8 = 16 * (q / 128) + bv_unsigned k / 8).
  { assert (Hq2 : q = 16 * (q / 128) * 8 + bv_unsigned k).
    { pose proof (Z_div_mod_eq_full q 128) as Hd.
      rewrite E in Hd.
      replace (16 * (q / 128) * 8) with (128 * (q / 128)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdd, Hh8 in Hz.
  replace (16 * (q / 128) + bv_unsigned k / 8)
    with (bv_unsigned k / 8 + (q / 128) * 4 * 4) in Hz by ring.
  rewrite Z_mod_plus_full in Hz.
  exact (Hk Hz).
Qed.

Lemma exec_or_ff (l r : M bool) (s : mstate) :
  exec l s = Some (false, s) ->
  exec r s = Some (false, s) ->
  exec (or_boolM l r) s = Some (false, s).
Proof.
  intros Hl Hr. unfold or_boolM.
  rewrite (exec_bind_Some _ _ _ _ _ Hl). cbn match. exact Hr.
Qed.

Lemma goodmb_or_ff (Dr Dw : register -> bool) (l r : M bool) (s : mstate) :
  goodmb Dr Dw l s ∅ = true ->
  exec l s = Some (false, s) ->
  goodmb Dr Dw r s ∅ = true ->
  goodmb Dr Dw (or_boolM l r) s ∅ = true.
Proof.
  intros Hgl Hl Hgr.
  erewrite goodmb_or_boolM_empty; [ | exact Hgl | exact Hl ]. exact Hgr.
Qed.

(* per-clause closers for the U-addressed survivors of the priv gate *)
Ltac csr_close HES EP Hms Hfs Hvs Hmisa Hmenv :=
  lazymatch goal with
  | |- exists _, exec (or_boolM _ _) _ = Some _ /\ _ =>
      (* fflags / frm / fcsr: F ∨ Zfinx, both off *)
      eexists; split;
      [ apply exec_or_ff;
        [ exact (exec_currentlyEnabled_F_off _ _ Hms Hfs)
        | apply exec_currentlyEnabled_Zfinx ]
      | let Hb := fresh in intro Hb; discriminate Hb ]
  | |- exists _, exec (currentlyEnabled Ext_Zve32x) _ = Some _ /\ _ =>
      eexists; split;
      [ exact (exec_currentlyEnabled_Zve32x_off _ _ Hms Hvs)
      | let Hb := fresh in intro Hb; discriminate Hb ]
  | |- exists _, exec (is_ssp_accessible _) _ = Some _ /\ _ =>
      eexists; split;
      [ exact (exec_is_ssp_accessible_U_off _ Hmisa Hmenv)
      | let Hb := fresh in intro Hb; discriminate Hb ]
  | |- exists _, exec (and_boolM _ (and_boolM (returnM _) _)) _ = Some _ /\ _ =>
      (* the RV32 counter highs: Zicntr ∧ (xlen = 32) ∧ … *)
      eexists; split;
      [ rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr _));
        unfold and_boolM at 1;
        erewrite exec_bind_Some; [ | apply exec_returnM ];
        cbn beta;
        match goal with
        | |- exec (if ?g then _ else _) _ = _ =>
            replace g with false by (vm_compute; reflexivity)
        end;
        cbn match; apply exec_returnM
      | let Hb := fresh in intro Hb; discriminate Hb ]
  | |- exists _, exec (and_boolM _ (counter_enabled ?i _)) _ = Some _ /\ _ =>
      (* cycle / time / instret: the enable bit decides; both outcomes fit *)
      let en := fresh "en" in let Hen := fresh "Hen" in
      destruct (exec_counter_enabled_U_total i _ HES) as [en Hen];
      eexists; split;
      [ rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr _));
        exact Hen
      | let Hb := fresh in intro Hb; unfold u_csr_readable;
        first [ left; reflexivity
              | right; left; reflexivity
              | right; right; left; reflexivity ] ]
  end.

(* the Zihpm hpm-range closers: the shadow range retires on the enable,
   the RV32-high range dies on xlen = 32 *)
Ltac csr_close_hpm HES E1 E2 :=
  cbv zeta;
  lazymatch goal with
  | |- exists _, exec (and_boolM _ (and_boolM (returnM _) _)) _ = Some _ /\ _ =>
      eexists; split;
      [ rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zihpm _));
        unfold and_boolM at 1;
        erewrite exec_bind_Some; [ | apply exec_returnM ];
        cbn beta;
        match goal with
        | |- exec (if ?g then _ else _) _ = _ =>
            replace g with false by (vm_compute; reflexivity)
        end;
        cbn match; apply exec_returnM
      | let Hb := fresh in intro Hb; discriminate Hb ]
  | |- exists _, exec (and_boolM _ (counter_enabled ?i _)) _ = Some _ /\ _ =>
      let en := fresh "en" in let Hen := fresh "Hen" in
      destruct (exec_counter_enabled_U_total i _ HES) as [en Hen];
      eexists; split;
      [ rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zihpm _));
        exact Hen
      | let Hb := fresh in intro Hb;
        unfold u_csr_readable, u_hpm_range;
        right; right; right;
        split; [ exact E1 | exact E2 ] ]
  end.

(* one dispatch guard: PMP subranges die on the priv gate; concrete
   addresses either contradict the priv gate (M/S-addressed) or are
   closed by the clause closer (U-addressed); the andb-guarded hpm
   ranges either die the same way or close via the hpm closers *)
Ltac csr_step HES EP Hms Hfs Hvs Hmisa Hmenv :=
  lazymatch goal with
  | |- exists _, exec (if andb ?g1 ?g2 then _ else _) _ = Some _ /\ _ =>
      let E := fresh "E" in
      destruct (andb g1 g2) eqn:E;
      [ apply andb_prop in E;
        let E1 := fresh "E1" in let E2 := fresh "E2" in
        destruct E as [E1 E2];
        first
          [ exfalso;
            exact (hpm_subrange_dead _ _ E1
                     ltac:(vm_compute; congruence) EP)
          | csr_close_hpm HES E1 E2 ]
      | clear E ]
  | |- exists _, exec (if eq_vec (subrange_vec_dec ?c 11 4) ?h then _ else _) _ = Some _ /\ _ =>
      let E := fresh "E" in
      destruct (eq_vec (subrange_vec_dec c 11 4) h) eqn:E;
      [ exfalso;
        exact (pmp_subrange_dead c h E ltac:(vm_compute; reflexivity) EP)
      | clear E ]
  | |- exists _, exec (if eq_vec ?c ?a then _ else _) _ = Some _ /\ _ =>
      let E := fresh "E" in
      destruct (eq_vec c a) eqn:E;
      [ apply eq_vec_true_iff in E; subst c;
        first
          [ exfalso; vm_compute in EP; discriminate EP
          | csr_close HES EP Hms Hfs Hvs Hmisa Hmenv ]
      | clear E ]
  end.

Ltac gm_csr_close :=
  lazymatch goal with
  | |- goodmb _ _ (or_boolM _ _) _ _ = true =>
      apply goodmb_or_ff;
      [ eapply goodmb_currentlyEnabled_F_off; eassumption
      | eapply exec_currentlyEnabled_F_off; eassumption
      | apply goodmb_currentlyEnabled_Zfinx ]
  | |- goodmb _ _ (currentlyEnabled Ext_Zve32x) _ _ = true =>
      eapply goodmb_currentlyEnabled_Zve32x_off; eassumption
  | |- goodmb _ _ (is_ssp_accessible _) _ _ = true =>
      apply goodmb_is_ssp_accessible_U_off; assumption
  | |- goodmb _ _ (and_boolM _ (and_boolM (returnM _) _)) _ _ = true =>
      erewrite goodmb_and_boolM_empty;
        [ | apply goodmb_currentlyEnabled_Zicntr
          | apply exec_currentlyEnabled_Zicntr ];
      cbn match;
      unfold and_boolM at 1;
      erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ];
      cbn beta;
      match goal with
      | |- goodmb _ _ (if ?g then _ else _) _ _ = _ =>
          replace g with false by (vm_compute; reflexivity)
      end;
      cbn match; apply goodmb_returnm
  | |- goodmb _ _ (and_boolM _ (counter_enabled ?i _)) _ _ = true =>
      erewrite goodmb_and_boolM_empty;
        [ | apply goodmb_currentlyEnabled_Zicntr
          | apply exec_currentlyEnabled_Zicntr ];
      cbn match; apply goodmb_counter_enabled_U; assumption
  end.

Ltac gm_csr_close_hpm :=
  cbv zeta;
  lazymatch goal with
  | |- goodmb _ _ (and_boolM _ (and_boolM (returnM _) _)) _ _ = true =>
      erewrite goodmb_and_boolM_empty;
        [ | apply goodmb_currentlyEnabled_Zihpm
          | apply exec_currentlyEnabled_Zihpm ];
      cbn match;
      unfold and_boolM at 1;
      erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ];
      cbn beta;
      match goal with
      | |- goodmb _ _ (if ?g then _ else _) _ _ = _ =>
          replace g with false by (vm_compute; reflexivity)
      end;
      cbn match; apply goodmb_returnm
  | |- goodmb _ _ (and_boolM _ (counter_enabled ?i _)) _ _ = true =>
      erewrite goodmb_and_boolM_empty;
        [ | apply goodmb_currentlyEnabled_Zihpm
          | apply exec_currentlyEnabled_Zihpm ];
      cbn match; apply goodmb_counter_enabled_U; assumption
  end.

Ltac gm_csr_step EP :=
  lazymatch goal with
  | |- goodmb _ _ (if andb ?g1 ?g2 then _ else _) _ _ = true =>
      let E := fresh "E" in
      destruct (andb g1 g2) eqn:E;
      [ apply andb_prop in E;
        let E1 := fresh "E1" in let E2 := fresh "E2" in
        destruct E as [E1 E2];
        first
          [ exfalso;
            exact (hpm_subrange_dead _ _ E1 ltac:(vm_compute; congruence) EP)
          | gm_csr_close_hpm ]
      | clear E ]
  | |- goodmb _ _ (if eq_vec (subrange_vec_dec ?c 11 4) ?h then _ else _) _ _ = true =>
      let E := fresh "E" in
      destruct (eq_vec (subrange_vec_dec c 11 4) h) eqn:E;
      [ exfalso;
        exact (pmp_subrange_dead c h E ltac:(vm_compute; reflexivity) EP)
      | clear E ]
  | |- goodmb _ _ (if eq_vec ?c ?a then _ else _) _ _ = true =>
      let E := fresh "E" in
      destruct (eq_vec c a) eqn:E;
      [ apply eq_vec_true_iff in E; subst c;
        first
          [ exfalso; vm_compute in EP; discriminate EP
          | gm_csr_close ]
      | clear E ]
  end.
Lemma exec_is_CSR_accessible_U (csr : mword 12) (acc : CSRAccessType)
    (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  zopz0zKzJ_u ('b"00") (csrPriv csr) = true ->
  exists b, exec (is_CSR_accessible csr User acc) s = Some (b, s)
            /\ (b = true -> u_csr_readable csr).
Proof.
  intros Hms Hfs Hvs Hmisa Hmenv HES EP.
  unfold is_CSR_accessible.
  repeat csr_step HES EP Hms Hfs Hvs Hmisa Hmenv.
  (* the fall-through default *)
  eexists; split; [ apply exec_returnM | ].
  intro Hb; discriminate Hb.
Qed.

Lemma goodmb_is_CSR_accessible_U (Dr Dw : register -> bool) (csr : mword 12)
    (acc : CSRAccessType) (s : mstate) (ms_v : mword 64) :
  Dr misa = true -> Dr mstatus = true -> Dr menvcfg = true ->
  Dr mcounteren = true -> Dr scounteren = true ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  zopz0zKzJ_u ('b"00") (csrPriv csr) = true ->
  goodmb Dr Dw (is_CSR_accessible csr User acc) s ∅ = true.
Proof.
  intros HDmi HDms HDme HDmc HDsc Hms Hfs Hvs Hmisa Hmenv HgES HES EP.
  unfold is_CSR_accessible.
  repeat gm_csr_step EP.
  apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §3c The assembled check at User.                                       *)
(* ===================================================================== *)

Lemma exec_check_CSR_U (csr : mword 12) (acc : CSRAccessType)
    (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists ok, exec (check_CSR csr User acc) s = Some (ok, s)
    /\ (ok = true -> u_csr_readable csr /\ check_CSR_access csr acc = true).
Proof.
  intros Hms Hfs Hvs Hmisa Hmenv HES.
  unfold check_CSR.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_U csr s)).
  destruct (zopz0zKzJ_u ('b"00") (csrPriv csr)) eqn:EP.
  - (* priv gate passed *)
    rewrite (exec_and_boolM_Some _ _ _ _ _
               (exec_returnM (check_CSR_access csr acc) s)).
    destruct (check_CSR_access csr acc) eqn:EA.
    + (* access shape OK: the accessibility traversal decides *)
      destruct (exec_is_CSR_accessible_U csr acc s ms_v
                  Hms Hfs Hvs Hmisa Hmenv HES EP) as (b & Hb & Himp).
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hb).
      destruct b.
      * (* accessible: csr is a readable counter -- stateen is concrete *)
        pose proof (Himp eq_refl) as Hr.
        destruct Hr as [-> | [-> | [-> | Hhpm]]].
        { eexists. split.
          { unfold stateen_allows_CSR_access. cbn match.
            repeat match goal with
            | |- exec (if ?g then _ else _) _ = _ =>
                replace g with false by (vm_compute; reflexivity)
            end.
            apply exec_returnM. }
          intro; split; [ left; reflexivity | reflexivity ]. }
        { eexists. split.
          { unfold stateen_allows_CSR_access. cbn match.
            repeat match goal with
            | |- exec (if ?g then _ else _) _ = _ =>
                replace g with false by (vm_compute; reflexivity)
            end.
            apply exec_returnM. }
          intro; split; [ right; left; reflexivity | reflexivity ]. }
        { eexists. split.
          { unfold stateen_allows_CSR_access. cbn match.
            repeat match goal with
            | |- exec (if ?g then _ else _) _ = _ =>
                replace g with false by (vm_compute; reflexivity)
            end.
            apply exec_returnM. }
          intro; split; [ right; right; left; reflexivity | reflexivity ]. }
        { (* the hpm range: stateen's guards are all concrete-address
             mismatches EXCEPT none match the 0xCxx range -- every guard
             is eq_vec csr ADDR with ADDR outside the range; kill each by
             the range facts *)
          destruct Hhpm as [E1 E2].
          eexists. split.
          { unfold stateen_allows_CSR_access. cbn match.
            repeat match goal with
            | |- exec (if eq_vec ?c ?a then _ else _) _ = _ =>
                let EX := fresh "EX" in
                destruct (eq_vec c a) eqn:EX;
                [ exfalso;
                  apply eq_vec_true_iff in EX; subst c;
                  vm_compute in E1; discriminate E1
                | clear EX ]
            end.
            apply exec_returnM. }
          intro; split;
            [ right; right; right; split; assumption | reflexivity ]. }
      * (* inaccessible *)
        eexists. split; [ apply exec_returnM | ].
        intro Hb'; discriminate Hb'.
    + (* wrong access shape (write to a read-only address) *)
      eexists. split; [ apply exec_returnM | ].
      intro Hb'; discriminate Hb'.
  - (* priv gate failed *)
    eexists. split; [ apply exec_returnM | ].
    intro Hb'; discriminate Hb'.
Qed.

Lemma goodmb_check_CSR_U (Dr Dw : register -> bool) (csr : mword 12)
    (acc : CSRAccessType) (s : mstate) (ms_v : mword 64) :
  Dr misa = true -> Dr mstatus = true -> Dr menvcfg = true ->
  Dr mcounteren = true -> Dr scounteren = true ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (check_CSR csr User acc) s ∅ = true.
Proof.
  intros HDmi HDms HDme HDmc HDsc Hms Hfs Hvs Hmisa Hmenv HgES HES.
  unfold check_CSR.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_check_CSR_priv_U | apply (exec_check_CSR_priv_U csr s) ].
  destruct (zopz0zKzJ_u ('b"00") (csrPriv csr)) eqn:EP; [ | reflexivity ].
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_returnm
      | apply (exec_returnM (check_CSR_access csr acc) s) ].
  destruct (check_CSR_access csr acc) eqn:EA; [ | reflexivity ].
  destruct (exec_is_CSR_accessible_U csr acc s ms_v Hms Hfs Hvs Hmisa Hmenv HES EP)
    as (b & Hb & Himp).
  erewrite goodmb_and_boolM_empty;
    [ | eapply goodmb_is_CSR_accessible_U; eassumption | exact Hb ].
  destruct b; [ | reflexivity ].
  pose proof (Himp eq_refl) as Hr.
  destruct Hr as [-> | [-> | [-> | Hhpm]]].
  1-3: (unfold stateen_allows_CSR_access; cbn match;
        repeat match goal with
        | |- goodmb _ _ (if ?g then _ else _) _ _ = _ =>
            replace g with false by (vm_compute; reflexivity)
        end;
        apply goodmb_returnm).
  destruct Hhpm as [E1 E2].
  unfold stateen_allows_CSR_access. cbn match.
  repeat match goal with
  | |- goodmb _ _ (if eq_vec ?c ?a then _ else _) _ _ = _ =>
      let EX := fresh "EX" in
      destruct (eq_vec c a) eqn:EX;
      [ exfalso; apply eq_vec_true_iff in EX; subst c;
        vm_compute in E1; discriminate E1
      | clear EX ]
  end.
  apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §3d check_CSR_result and the survivor reads.                           *)
(* ===================================================================== *)

Lemma exec_check_CSR_result_U (csr : mword 12) (acc : CSRAccessType)
    (s : mstate) (ms_v : mword 64) :
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists res, exec (check_CSR_result csr User acc) s = Some (res, s)
    /\ (res = CSR_Check_OK tt \/ res = CSR_Illegal tt)
    /\ (res = CSR_Check_OK tt ->
        u_csr_readable csr /\ check_CSR_access csr acc = true).
Proof.
  intros Hms Hfs Hvs Hmisa Hmenv HES.
  unfold check_CSR_result.
  destruct (exec_check_CSR_U csr acc s ms_v Hms Hfs Hvs Hmisa Hmenv HES)
    as (ok & Hok & Himp).
  rewrite (exec_bind_Some _ _ _ _ _ Hok).
  destruct ok.
  - (* passed: CSR_Check_OK *)
    cbn match.
    eexists. split; [ apply exec_returnM | ].
    split; [ left; reflexivity | ].
    intro; exact (Himp eq_refl).
  - (* failed: User is not a virtual privilege, so plain Illegal *)
    cbn match.
    eexists. split.
    { erewrite exec_bind_Some.
      2:{ unfold and_boolM.
          erewrite exec_bind_Some; [ | apply exec_returnM ].
          cbn beta. cbn match.
          apply (exec_returnM false s). }
      cbn beta. cbv zeta.
      apply exec_returnM. }
    split; [ right; reflexivity | ].
    intro Hr; discriminate Hr.
Qed.

Lemma goodmb_check_CSR_result_U (Dr Dw : register -> bool) (csr : mword 12)
    (acc : CSRAccessType) (s : mstate) (ms_v : mword 64) :
  Dr misa = true -> Dr mstatus = true -> Dr menvcfg = true ->
  Dr mcounteren = true -> Dr scounteren = true ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (check_CSR_result csr User acc) s ∅ = true.
Proof.
  intros HDmi HDms HDme HDmc HDsc Hms Hfs Hvs Hmisa Hmenv HgES HES.
  unfold check_CSR_result.
  destruct (exec_check_CSR_U csr acc s ms_v Hms Hfs Hvs Hmisa Hmenv HES)
    as (ok & Hok & Himp).
  erewrite goodmb_bind_empty;
    [ | eapply goodmb_check_CSR_U; eassumption | exact Hok ].
  destruct ok.
  - cbn match. apply goodmb_returnm.
  - cbn match.
    erewrite goodmb_bind_empty.
    2:{ unfold and_boolM.
        erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
        cbn beta. cbn match. apply goodmb_returnm. }
    2:{ unfold and_boolM.
        erewrite exec_bind_Some; [ | apply exec_returnM ].
        cbn beta. cbn match. apply (exec_returnM false s). }
    cbn beta. cbv zeta. apply goodmb_returnm.
Qed.

(* the two missing Zicntr counter reads (time exists in WpGprCsrrB) *)
Lemma exec_read_CSR_cycle_u (s : mstate) :
  exec (read_CSR (Ox"C00")) s
    = Some (subrange_vec_dec (register_lookup mcycle s.(sregs)) (Z.sub xlen 1) 0, s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcycle s)).
  apply exec_returnM.
Qed.

Lemma goodmb_read_CSR_cycle_u (Dr Dw : register -> bool) (s : mstate) :
  Dr mcycle = true -> goodmb Dr Dw (read_CSR (Ox"C00")) s ∅ = true.
Proof. intros H. drive_csr_term. gm_rr mcycle H. apply goodmb_returnm. Qed.

Lemma exec_read_CSR_time_u (s : mstate) :
  exec (read_CSR (Ox"C01")) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0, s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mtime s)).
  apply exec_returnM.
Qed.

Lemma goodmb_read_CSR_time_u (Dr Dw : register -> bool) (s : mstate) :
  Dr mtime = true -> goodmb Dr Dw (read_CSR (Ox"C01")) s ∅ = true.
Proof. intros H. drive_csr_term. gm_rr mtime H. apply goodmb_returnm. Qed.

Lemma exec_read_CSR_instret_u (s : mstate) :
  exec (read_CSR (Ox"C02")) s
    = Some (subrange_vec_dec (register_lookup minstret s.(sregs)) (Z.sub xlen 1) 0, s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg minstret s)).
  apply exec_returnM.
Qed.

Lemma goodmb_read_CSR_instret_u (Dr Dw : register -> bool) (s : mstate) :
  Dr minstret = true -> goodmb Dr Dw (read_CSR (Ox"C02")) s ∅ = true.
Proof. intros H. drive_csr_term. gm_rr minstret H. apply goodmb_returnm. Qed.

(* a readable csr sits at a read-only address (bits 11:10 = 11), so the
   only access shape check_CSR_access admits is CSRRead *)
Lemma csrAccess_unsigned (x : mword 12) :
  bv_unsigned (csrAccess x) = (bv_unsigned x / 1024) mod 4.
Proof.
  unfold csrAccess, subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (11 - 10 + 1))) with 4.
  rewrite Z.shiftr_div_pow2 by (vm_compute; congruence).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 10)) with 10.
  change (2 ^ 10) with 1024.
  reflexivity.
Qed.

Lemma u_readable_read_only (csr : mword 12) :
  u_csr_readable csr -> csrAccess csr = ('b"11" : mword 2).
Proof.
  intros [-> | [-> | [-> | [E1 E2]]]];
    try (vm_compute; reflexivity).
  (* hpm range: bits 11:10 come from the key's top bits *)
  apply eq_vec_true_iff in E1.
  apply (f_equal bv_unsigned) in E1.
  rewrite sub115_unsigned in E1.
  apply bv_eq.
  rewrite csrAccess_unsigned.
  change (bv_unsigned ('b"11" : mword 2)) with 3.
  set (c := bv_unsigned csr) in *.
  assert (Hdd : c / 1024 = (c / 32) / 32).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 32) in *.
  assert (Hh32 : q / 32 = 4 * (q / 128) + bv_unsigned ('b"1100000" : mword 7) / 32).
  { assert (Hq2 : q = 4 * (q / 128) * 32 + bv_unsigned ('b"1100000" : mword 7)).
    { pose proof (Z_div_mod_eq_full q 128) as Hd.
      rewrite E1 in Hd.
      replace (4 * (q / 128) * 32) with (128 * (q / 128)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdd, Hh32.
  change (bv_unsigned ('b"1100000" : mword 7) / 32) with 3.
  replace (4 * (q / 128) + 3) with (3 + (q / 128) * 4) by ring.
  rewrite Z_mod_plus_full.
  vm_compute; reflexivity.
Qed.

Lemma u_readable_acc_read (csr : mword 12) (acc : CSRAccessType) :
  u_csr_readable csr ->
  check_CSR_access csr acc = true ->
  acc = CSRRead.
Proof.
  intros Hr EA.
  unfold check_CSR_access in EA.
  rewrite (u_readable_read_only csr Hr) in EA.
  destruct acc; [ reflexivity | | ];
    vm_compute in EA; discriminate EA.
Qed.

(* ===================================================================== *)
(* §3e read_CSR over the hpm shadow range.                                *)
(* ===================================================================== *)

(* priv bits from a matched subrange, extracted for reuse *)
Lemma sub115_priv (csr : mword 12) (k : mword 7) :
  eq_vec (subrange_vec_dec csr 11 5) k = true ->
  (bv_unsigned csr / 256) mod 4 = (bv_unsigned k / 8) mod 4.
Proof.
  intros E.
  apply eq_vec_true_iff in E.
  apply (f_equal bv_unsigned) in E.
  rewrite sub115_unsigned in E.
  set (c := bv_unsigned csr) in *.
  assert (Hdd : c / 256 = (c / 32) / 8).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 32) in *.
  assert (Hh8 : q / 8 = 16 * (q / 128) + bv_unsigned k / 8).
  { assert (Hq2 : q = 16 * (q / 128) * 8 + bv_unsigned k).
    { pose proof (Z_div_mod_eq_full q 128) as Hd.
      rewrite E in Hd.
      replace (16 * (q / 128) * 8) with (128 * (q / 128)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdd, Hh8.
  replace (16 * (q / 128) + bv_unsigned k / 8)
    with (bv_unsigned k / 8 + (q / 128) * 4 * 4) by ring.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

Lemma sub114_priv (csr : mword 12) (h : mword 8) :
  eq_vec (subrange_vec_dec csr 11 4) h = true ->
  (bv_unsigned csr / 256) mod 4 = (bv_unsigned h / 16) mod 4.
Proof.
  intros E.
  apply eq_vec_true_iff in E.
  apply (f_equal bv_unsigned) in E.
  rewrite sub114_unsigned in E.
  set (c := bv_unsigned csr) in *.
  assert (Hdd : c / 256 = (c / 16) / 16).
  { rewrite Z.div_div by lia. reflexivity. }
  set (q := c / 16) in *.
  assert (Hh16 : q / 16 = 16 * (q / 256) + bv_unsigned h / 16).
  { assert (Hq2 : q = 16 * (q / 256) * 16 + bv_unsigned h).
    { pose proof (Z_div_mod_eq_full q 256) as Hd.
      rewrite E in Hd.
      replace (16 * (q / 256) * 16) with (256 * (q / 256)) by ring.
      exact Hd. }
    rewrite Hq2 at 1.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdd, Hh16.
  replace (16 * (q / 256) + bv_unsigned h / 16)
    with (bv_unsigned h / 16 + (q / 256) * 4 * 4) by ring.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(* a PMP-file 11:4 guard cannot coexist with the hpm 11:5 range *)
Lemma pmp_vs_hpm_dead (csr : mword 12) (h : mword 8) :
  eq_vec (subrange_vec_dec csr 11 4) h = true ->
  bv_unsigned h / 16 = 3 ->
  eq_vec (subrange_vec_dec csr 11 5) ('b"1100000") = true -> False.
Proof.
  intros E4 Hh E5.
  pose proof (sub114_priv csr h E4) as H4.
  pose proof (sub115_priv csr ('b"1100000") E5) as H5.
  rewrite Hh in H4.
  change (bv_unsigned ('b"1100000" : mword 7) / 8) with 12 in H5.
  rewrite H4 in H5.
  vm_compute in H5. discriminate H5.
Qed.

(* one read_CSR guard, killed from the hpm range membership *)
Ltac csr_read_step E1 :=
  lazymatch goal with
  | |- exists _, exec (if andb false ?g2 then _ else _) _ = Some _ =>
      (* a prior [change] already exposed the closed-false conjunct *)
      rewrite (andb_false_l g2); cbn match
  | |- exists _, exec (if andb (Z.eqb xlen 32) ?g2 then _ else _) _ = Some _ =>
      (* an RV32-only clause: the first conjunct is closed false *)
      change (Z.eqb xlen 32) with false;
      rewrite (andb_false_l g2);
      cbn match
  | |- exists _, exec (if andb (eq_vec (subrange_vec_dec ?c 11 4) ?h) ?g2 then _ else _) _ = Some _ =>
      let E := fresh "E" in
      destruct (andb (eq_vec (subrange_vec_dec c 11 4) h) g2) eqn:E;
      [ apply andb_prop in E;
        let Ea := fresh "Ea" in let Eb := fresh "Eb" in
        destruct E as [Ea Eb];
        exfalso;
        exact (pmp_vs_hpm_dead c h Ea ltac:(vm_compute; reflexivity) E1)
      | clear E ]
  | |- exists _, exec (if andb (eq_vec (subrange_vec_dec ?c 11 5) ?k) ?g2 then _ else _) _ = Some _ =>
      let E := fresh "E" in
      destruct (andb (eq_vec (subrange_vec_dec c 11 5) k) g2) eqn:E;
      [ apply andb_prop in E;
        let Ea := fresh "Ea" in let Eb := fresh "Eb" in
        destruct E as [Ea Eb];
        exfalso;
        apply eq_vec_true_iff in Ea;
        let E1' := fresh "E1x" in
        pose proof E1 as E1';
        apply eq_vec_true_iff in E1';
        rewrite E1' in Ea; vm_compute in Ea; discriminate Ea
      | clear E ]
  | |- exists _, exec (if eq_vec (subrange_vec_dec ?c 11 4) ?h then _ else _) _ = Some _ =>
      let E := fresh "E" in
      destruct (eq_vec (subrange_vec_dec c 11 4) h) eqn:E;
      [ exfalso;
        exact (pmp_vs_hpm_dead c h E ltac:(vm_compute; reflexivity) E1)
      | clear E ]
  | |- exists _, exec (if eq_vec ?c ?a then _ else _) _ = Some _ =>
      let E := fresh "E" in
      destruct (eq_vec c a) eqn:E;
      [ exfalso; apply eq_vec_true_iff in E; subst c;
        vm_compute in E1; discriminate E1
      | clear E ]
  end.

Ltac gm_csr_read_step E1 :=
  lazymatch goal with
  | |- goodmb _ _ (if andb false ?g2 then _ else _) _ _ = true =>
      rewrite (andb_false_l g2); cbn match
  | |- goodmb _ _ (if andb (Z.eqb xlen 32) ?g2 then _ else _) _ _ = true =>
      change (Z.eqb xlen 32) with false;
      rewrite (andb_false_l g2); cbn match
  | |- goodmb _ _ (if andb (eq_vec (subrange_vec_dec ?c 11 4) ?h) ?g2 then _ else _)
              _ _ = true =>
      let E := fresh "E" in
      destruct (andb (eq_vec (subrange_vec_dec c 11 4) h) g2) eqn:E;
      [ apply andb_prop in E;
        let Ea := fresh "Ea" in let Eb := fresh "Eb" in
        destruct E as [Ea Eb];
        exfalso;
        exact (pmp_vs_hpm_dead c h Ea ltac:(vm_compute; reflexivity) E1)
      | clear E ]
  | |- goodmb _ _ (if andb (eq_vec (subrange_vec_dec ?c 11 5) ?k) ?g2 then _ else _)
              _ _ = true =>
      let E := fresh "E" in
      destruct (andb (eq_vec (subrange_vec_dec c 11 5) k) g2) eqn:E;
      [ apply andb_prop in E;
        let Ea := fresh "Ea" in let Eb := fresh "Eb" in
        destruct E as [Ea Eb];
        exfalso;
        apply eq_vec_true_iff in Ea;
        let E1' := fresh "E1x" in
        pose proof E1 as E1';
        apply eq_vec_true_iff in E1';
        rewrite E1' in Ea; vm_compute in Ea; discriminate Ea
      | clear E ]
  | |- goodmb _ _ (if eq_vec (subrange_vec_dec ?c 11 4) ?h then _ else _) _ _ = true =>
      let E := fresh "E" in
      destruct (eq_vec (subrange_vec_dec c 11 4) h) eqn:E;
      [ exfalso;
        exact (pmp_vs_hpm_dead c h E ltac:(vm_compute; reflexivity) E1)
      | clear E ]
  | |- goodmb _ _ (if eq_vec ?c ?a then _ else _) _ _ = true =>
      let E := fresh "E" in
      destruct (eq_vec c a) eqn:E;
      [ exfalso; apply eq_vec_true_iff in E; subst c;
        vm_compute in E1; discriminate E1
      | clear E ]
  end.
Lemma exec_read_CSR_hpm (csr : mword 12) (s : mstate) :
  u_hpm_range csr ('b"1100000") ->
  exists v, exec (read_CSR csr) s = Some (v, s).
Proof.
  intros [E1 E2].
  unfold read_CSR.
  repeat csr_read_step E1.
  (* the live hpm clause *)
  cbv zeta.
  match goal with
  | |- exists _, exec (if ?g then _ else _) _ = Some _ =>
      replace g with true
        by (symmetry; apply andb_true_iff; split; [ exact E1 | exact E2 ])
  end.
  eexists.
  erewrite exec_bind_Some.
  2:{ unfold hpmidx_from_bits, Defs.assert_exp'. cbv zeta.
      lazymatch goal with
      | |- exec (Defs.bind (match ?g with true => _ | false => _ end) _) _ = _ =>
          lazymatch type of E2 with
          | ?g2 = true => change g2 with g in E2
          end;
          let E3 := fresh "E3" in
          destruct g eqn:E3; [ | discriminate E2 ]
      end.
      cbn match.
      erewrite exec_bind_Some; [ | apply exec_returnM ].
      cbn beta. apply exec_returnM. }
  cbn beta.
  unfold read_mhpmcounter.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mhpmcounter s)). cbn beta.
  apply exec_returnM.
Qed.

Lemma goodmb_read_CSR_hpm (Dr Dw : register -> bool) (csr : mword 12) (s : mstate) :
  Dr mhpmcounter = true ->
  u_hpm_range csr ('b"1100000") ->
  goodmb Dr Dw (read_CSR csr) s ∅ = true.
Proof.
  intros HDh [E1 E2].
  unfold read_CSR.
  repeat gm_csr_read_step E1.
  cbv zeta.
  match goal with
  | |- goodmb _ _ (if ?g then _ else _) _ _ = true =>
      replace g with true
        by (symmetry; apply andb_true_iff; split; [ exact E1 | exact E2 ])
  end.
  erewrite goodmb_bind_empty.
  2:{ unfold hpmidx_from_bits, Defs.assert_exp'. cbv zeta.
      lazymatch goal with
      | |- goodmb _ _ (Defs.bind (match ?g with true => _ | false => _ end) _) _ _ = _ =>
          lazymatch type of E2 with
          | ?g2 = true => change g2 with g in E2
          end;
          let E3 := fresh "E3" in
          destruct g eqn:E3; [ | discriminate E2 ]
      end.
      cbn match.
      erewrite goodmb_bind_empty; [ | apply goodmb_returnm | apply exec_returnM ].
      cbn beta. apply goodmb_returnm. }
  2:{ unfold hpmidx_from_bits, Defs.assert_exp'. cbv zeta.
      lazymatch goal with
      | |- exec (Defs.bind (match ?g with true => _ | false => _ end) _) _ = _ =>
          lazymatch type of E2 with
          | ?g2 = true => change g2 with g in E2
          end;
          let E3 := fresh "E3" in
          destruct g eqn:E3; [ | discriminate E2 ]
      end.
      cbn match.
      erewrite exec_bind_Some; [ | apply exec_returnM ].
      cbn beta. apply exec_returnM. }
  cbn beta.
  unfold read_mhpmcounter.
  gm_rr mhpmcounter HDh. cbn beta. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §3f Concretizing the hpm range: 29 addresses.                          *)
(* ===================================================================== *)

Lemma sub40_unsigned (x : mword 12) :
  bv_unsigned (subrange_vec_dec x 4 0) = bv_unsigned x mod 32.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (4 - 0 + 1))) with 32.
  reflexivity.
Qed.

Lemma u_hpm_unsigned (csr : mword 12) :
  u_hpm_range csr ('b"1100000") ->
  3072 + 3 <= bv_unsigned csr <= 3072 + 31.
Proof.
  intros [E1 E2].
  apply eq_vec_true_iff in E1.
  apply (f_equal bv_unsigned) in E1.
  rewrite sub115_unsigned in E1.
  change (bv_unsigned ('b"1100000" : mword 7)) with 96 in E1.
  rewrite (uint_unsigned_n _) in E2.
  rewrite sub40_unsigned in E2.
  apply Z.geb_le in E2.
  pose proof (bv_unsigned_in_range _ csr) as Hr.
  unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 4096 in Hr.
  set (c := bv_unsigned csr) in *.
  assert (H32 : (0 < 32)%Z) by (vm_compute; constructor).
  assert (Hd32 : c / 32 < 128).
  { apply Z.div_lt_upper_bound; [ exact H32 | ].
    change (32 * 128) with 4096. lia. }
  assert (Hd0 : 0 <= c / 32) by (apply Z.div_pos; lia).
  rewrite Z.mod_small in E1 by (split; [ exact Hd0 | exact Hd32 ]).
  pose proof (Z_div_mod_eq_full c 32) as Hdm.
  pose proof (Z.mod_pos_bound c 32 H32) as Hmb.
  lia.
Qed.

(* the 29 concrete hpm shadow addresses, as unsigned values *)
Lemma u_hpm_cases (csr : mword 12) :
  u_hpm_range csr ('b"1100000") ->
  bv_unsigned csr = 3075 \/
  bv_unsigned csr = 3076 \/
  bv_unsigned csr = 3077 \/
  bv_unsigned csr = 3078 \/
  bv_unsigned csr = 3079 \/
  bv_unsigned csr = 3080 \/
  bv_unsigned csr = 3081 \/
  bv_unsigned csr = 3082 \/
  bv_unsigned csr = 3083 \/
  bv_unsigned csr = 3084 \/
  bv_unsigned csr = 3085 \/
  bv_unsigned csr = 3086 \/
  bv_unsigned csr = 3087 \/
  bv_unsigned csr = 3088 \/
  bv_unsigned csr = 3089 \/
  bv_unsigned csr = 3090 \/
  bv_unsigned csr = 3091 \/
  bv_unsigned csr = 3092 \/
  bv_unsigned csr = 3093 \/
  bv_unsigned csr = 3094 \/
  bv_unsigned csr = 3095 \/
  bv_unsigned csr = 3096 \/
  bv_unsigned csr = 3097 \/
  bv_unsigned csr = 3098 \/
  bv_unsigned csr = 3099 \/
  bv_unsigned csr = 3100 \/
  bv_unsigned csr = 3101 \/
  bv_unsigned csr = 3102 \/
  bv_unsigned csr = 3103.
Proof.
  intro H.
  pose proof (u_hpm_unsigned csr H) as Hb.
  lia.
Qed.

(* ===================================================================== *)
(* §3g The assembled doCSR at User: Illegal, or a retiring read.          *)
(* ===================================================================== *)

(* the sip/mip special-case guards never match a readable csr *)
Ltac docsr_specials :=
  cbv zeta;
  repeat match goal with
  | |- exec (if ?g then _ else _) _ = _ =>
      replace g with false by (vm_compute; reflexivity)
  end;
  cbn match.

(* the common tail: callback + wX rd + RETIRE, from a callback fact *)
Ltac docsr_retire_tail rd HCB :=
  erewrite exec_bind0_Some;
  [ apply exec_returnm
  | erewrite exec_bind0_Some; [ | exact HCB ];
    apply (exec_wX_bits_gpr rd _ _) ].

Ltac gm_docsr_specials :=
  cbv zeta;
  repeat match goal with
  | |- goodmb _ _ (if ?g then _ else _) _ _ = _ =>
      replace g with false by (vm_compute; reflexivity)
  end;
  cbn match.

Ltac gm_docsr_retire_tail rd HgCB HCB Hd :=
  erewrite goodmb_bind0_empty;
    [ apply goodmb_returnm
    | erewrite goodmb_bind0_empty; [ | exact HgCB | exact HCB ];
      apply goodmb_wX_bits_gpr, Hd
    | erewrite exec_bind0_Some; [ | exact HCB ];
      apply (exec_wX_bits_gpr rd _ _) ].
Lemma exec_doCSR_U (csr : mword 12) (rs1v : mword 64) (rd : mword 5)
    (op : csrop) (acc : CSRAccessType)
    (s : mstate) (ms_v : mword 64) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists res s',
    exec (doCSR csr rs1v (Regidx rd) op acc) s = Some (res, s')
    /\ ((res = Illegal_Instruction tt /\ s' = s)
        \/ (res = RETIRE_SUCCESS /\ exists v, s' = gpr_write_state rd v s)).
Proof.
  intros Hpriv Hms Hfs Hvs Hmisa Hmenv HES.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  destruct (exec_check_CSR_result_U csr acc s ms_v Hms Hfs Hvs Hmisa Hmenv HES)
    as (res0 & Hres & Hcls & Himp).
  rewrite (exec_bind_Some _ _ _ _ _ Hres). cbn beta.
  destruct Hcls as [-> | ->].
  - (* CSR_Check_OK: a readable counter, access is a read *)
    cbn match.
    destruct (Himp eq_refl) as [Hread EA].
    pose proof (u_readable_acc_read csr acc Hread EA) as ->.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv.
    replace (not (ext_check_CSR csr User CSRRead)) with false
      by (vm_compute; reflexivity).
    cbn match.
    replace (generic_neq CSRRead CSRWrite) with true by (vm_compute; reflexivity).
    cbn match.
    destruct Hread as [-> | [-> | [-> | Hrange]]].
    + (* cycle *)
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_cycle_u s)). cbn beta.
      erewrite exec_bind_Some.
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C00")
                            (subrange_vec_dec (register_lookup mcycle s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      do 2 eexists. split.
      { docsr_retire_tail rd HCB. }
      right. split; [ reflexivity | eexists; reflexivity ].
    + (* time *)
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_time_u s)). cbn beta.
      erewrite exec_bind_Some.
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C01")
                            (subrange_vec_dec (register_lookup mtime s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      do 2 eexists. split.
      { docsr_retire_tail rd HCB. }
      right. split; [ reflexivity | eexists; reflexivity ].
    + (* instret *)
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_instret_u s)). cbn beta.
      erewrite exec_bind_Some.
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C02")
                            (subrange_vec_dec (register_lookup minstret s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      do 2 eexists. split.
      { docsr_retire_tail rd HCB. }
      right. split; [ reflexivity | eexists; reflexivity ].
    + (* the hpm shadow range: read range-generically; the special-case
         guards die on the range key; the name-map callback needs the
         29-way concretization *)
      destruct (exec_read_CSR_hpm csr s Hrange) as (v & Hv).
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn beta.
      destruct Hrange as [E1 E2].
      erewrite exec_bind_Some.
      2:{ cbv zeta.
          repeat match goal with
          | |- exec (if eq_vec ?c ?a then _ else _) _ = _ =>
              let EX := fresh "EX" in
              destruct (eq_vec c a) eqn:EX;
              [ exfalso; apply eq_vec_true_iff in EX; subst c;
                vm_compute in E1; discriminate E1
              | clear EX ]
          end.
          apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback csr v) s = Some (tt, s)).
      { pose proof (u_hpm_cases csr (conj E1 E2)) as Hc.
        repeat (destruct Hc as [Hc | Hc]);
          (assert (Hcsr : csr = Z_to_bv _ (bv_unsigned csr))
             by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry;
                 apply bv_wrap_small;
                 pose proof (bv_unsigned_in_range _ csr);
                 unfold bv_modulus in *; lia);
           rewrite Hc in Hcsr; rewrite Hcsr;
           reflexivity). }
      do 2 eexists. split.
      { docsr_retire_tail rd HCB. }
      right. split; [ reflexivity | eexists; reflexivity ].
  - (* CSR_Illegal *)
    cbn match.
    do 2 eexists. split; [ apply exec_returnm | ].
    left. split; reflexivity.
Qed.

Lemma goodmb_doCSR_U (Dr Dw : register -> bool) (csr : mword 12)
    (rs1v : mword 64) (rd : mword 5) (op : csrop) (acc : CSRAccessType)
    (s : mstate) (ms_v : mword 64) :
  Dr cur_privilege = true -> Dr misa = true -> Dr mstatus = true ->
  Dr menvcfg = true -> Dr mcounteren = true -> Dr scounteren = true ->
  Dr mcycle = true -> Dr mtime = true -> Dr minstret = true ->
  Dr mhpmcounter = true ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (doCSR csr rs1v (Regidx rd) op acc) s ∅ = true.
Proof.
  intros HDcp HDmi HDms HDme HDmc HDsc HDcy HDti HDin HDh Hd
         Hpriv Hms Hfs Hvs Hmisa Hmenv HgES HES.
  unfold doCSR.
  gm_rr cur_privilege HDcp. cbn beta. rewrite Hpriv.
  destruct (exec_check_CSR_result_U csr acc s ms_v Hms Hfs Hvs Hmisa Hmenv HES)
    as (res0 & Hres & Hcls & Himp).
  erewrite goodmb_bind_empty;
    [ | eapply goodmb_check_CSR_result_U; eassumption | exact Hres ].
  cbn beta.
  destruct Hcls as [-> | ->].
  - cbn match.
    destruct (Himp eq_refl) as [Hread EA].
    pose proof (u_readable_acc_read csr acc Hread EA) as ->.
    gm_rr cur_privilege HDcp. cbn beta. rewrite Hpriv.
    replace (not (ext_check_CSR csr User CSRRead)) with false
      by (vm_compute; reflexivity).
    cbn match.
    replace (generic_neq CSRRead CSRWrite) with true by (vm_compute; reflexivity).
    cbn match.
    destruct Hread as [-> | [-> | [-> | Hrange]]].
    + erewrite goodmb_bind_empty;
        [ | apply goodmb_read_CSR_cycle_u, HDcy | apply (exec_read_CSR_cycle_u s) ].
      cbn beta.
      erewrite goodmb_bind_empty.
      2:{ gm_docsr_specials. apply goodmb_returnm. }
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C00")
                            (subrange_vec_dec (register_lookup mcycle s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      assert (HgCB : goodmb Dr Dw (csr_id_read_callback (Ox"C00")
                            (subrange_vec_dec (register_lookup mcycle s.(sregs))
                               (Z.sub xlen 1) 0)) s ∅ = true) by reflexivity.
      gm_docsr_retire_tail rd HgCB HCB Hd.
    + erewrite goodmb_bind_empty;
        [ | apply goodmb_read_CSR_time_u, HDti | apply (exec_read_CSR_time_u s) ].
      cbn beta.
      erewrite goodmb_bind_empty.
      2:{ gm_docsr_specials. apply goodmb_returnm. }
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C01")
                            (subrange_vec_dec (register_lookup mtime s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      assert (HgCB : goodmb Dr Dw (csr_id_read_callback (Ox"C01")
                            (subrange_vec_dec (register_lookup mtime s.(sregs))
                               (Z.sub xlen 1) 0)) s ∅ = true) by reflexivity.
      gm_docsr_retire_tail rd HgCB HCB Hd.
    + erewrite goodmb_bind_empty;
        [ | apply goodmb_read_CSR_instret_u, HDin
          | apply (exec_read_CSR_instret_u s) ].
      cbn beta.
      erewrite goodmb_bind_empty.
      2:{ gm_docsr_specials. apply goodmb_returnm. }
      2:{ docsr_specials. apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback (Ox"C02")
                            (subrange_vec_dec (register_lookup minstret s.(sregs))
                               (Z.sub xlen 1) 0)) s
                    = Some (tt, s)) by reflexivity.
      assert (HgCB : goodmb Dr Dw (csr_id_read_callback (Ox"C02")
                            (subrange_vec_dec (register_lookup minstret s.(sregs))
                               (Z.sub xlen 1) 0)) s ∅ = true) by reflexivity.
      gm_docsr_retire_tail rd HgCB HCB Hd.
    + destruct (exec_read_CSR_hpm csr s Hrange) as (v & Hv).
      erewrite goodmb_bind_empty;
        [ | apply goodmb_read_CSR_hpm; assumption | exact Hv ].
      cbn beta.
      destruct Hrange as [E1 E2].
      erewrite goodmb_bind_empty.
      2:{ cbv zeta.
          repeat match goal with
          | |- goodmb _ _ (if eq_vec ?c ?a then _ else _) _ _ = _ =>
              let EX := fresh "EX" in
              destruct (eq_vec c a) eqn:EX;
              [ exfalso; apply eq_vec_true_iff in EX; subst c;
                vm_compute in E1; discriminate E1
              | clear EX ]
          end.
          apply goodmb_returnm. }
      2:{ cbv zeta.
          repeat match goal with
          | |- exec (if eq_vec ?c ?a then _ else _) _ = _ =>
              let EX := fresh "EX" in
              destruct (eq_vec c a) eqn:EX;
              [ exfalso; apply eq_vec_true_iff in EX; subst c;
                vm_compute in E1; discriminate E1
              | clear EX ]
          end.
          apply exec_returnM. }
      cbn beta.
      replace (generic_eq CSRRead CSRRead) with true by (vm_compute; reflexivity).
      cbn match.
      assert (HCB : exec (csr_id_read_callback csr v) s = Some (tt, s)).
      { pose proof (u_hpm_cases csr (conj E1 E2)) as Hc.
        repeat (destruct Hc as [Hc | Hc]);
          (assert (Hcsr : csr = Z_to_bv _ (bv_unsigned csr))
             by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry;
                 apply bv_wrap_small;
                 pose proof (bv_unsigned_in_range _ csr);
                 unfold bv_modulus in *; lia);
           rewrite Hc in Hcsr; rewrite Hcsr;
           reflexivity). }
      assert (HgCB : goodmb Dr Dw (csr_id_read_callback csr v) s ∅ = true).
      { pose proof (u_hpm_cases csr (conj E1 E2)) as Hc.
        repeat (destruct Hc as [Hc | Hc]);
          (assert (Hcsr : csr = Z_to_bv _ (bv_unsigned csr))
             by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry;
                 apply bv_wrap_small;
                 pose proof (bv_unsigned_in_range _ csr);
                 unfold bv_modulus in *; lia);
           rewrite Hc in Hcsr; rewrite Hcsr;
           reflexivity). }
      gm_docsr_retire_tail rd HgCB HCB Hd.
  - cbn match. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §4 The execute-level CSR totality at User.                             *)
(* ===================================================================== *)

Lemma exec_execute_CSRReg_total_U (csr : mword 12) (i1 rd : mword 5)
    (op : csrop) (s : mstate) (ms_v : mword 64) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists res s',
    exec (execute (CSRReg (csr, Regidx i1, Regidx rd, op))) s = Some (res, s')
    /\ ((res = Illegal_Instruction tt /\ s' = s)
        \/ (res = RETIRE_SUCCESS /\ exists v, s' = gpr_write_state rd v s)).
Proof.
  intros Hpriv Hms Hfs Hvs Hmisa Hmenv HES.
  change (execute (CSRReg (csr, Regidx i1, Regidx rd, op)))
    with (execute_CSRReg csr (Regidx i1) (Regidx rd) op).
  unfold execute_CSRReg. cbv zeta.
  destruct (exec_doCSR_U csr
              (if Z.eqb (uint i1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint i1))) s.(sregs))
              rd op
              (csr_access_type op (generic_eq (Regidx rd) zreg)
                 (generic_eq (Regidx i1) zreg))
              s ms_v Hpriv Hms Hfs Hvs Hmisa Hmenv HES)
    as (res & s' & Hdo & Hcls).
  exists res, s'. split; [ | exact Hcls ].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr i1 s)). cbn beta.
  exact Hdo.
Qed.

Lemma goodmb_execute_CSRReg_total_U (Dr Dw : register -> bool) (csr : mword 12)
    (i1 rd : mword 5) (op : csrop) (s : mstate) (ms_v : mword 64) :
  Dr cur_privilege = true -> Dr misa = true -> Dr mstatus = true ->
  Dr menvcfg = true -> Dr mcounteren = true -> Dr scounteren = true ->
  Dr mcycle = true -> Dr mtime = true -> Dr minstret = true ->
  Dr mhpmcounter = true ->
  (uint i1 <> 0 -> Dr (R_bitvector_64 (gpr_of_Z (uint i1))) = true) ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (execute (CSRReg (csr, Regidx i1, Regidx rd, op))) s ∅ = true.
Proof.
  intros HDcp HDmi HDms HDme HDmc HDsc HDcy HDti HDin HDh H1 Hd
         Hpriv Hms Hfs Hvs Hmisa Hmenv HgES HES.
  change (execute (CSRReg (csr, Regidx i1, Regidx rd, op)))
    with (execute_CSRReg csr (Regidx i1) (Regidx rd) op).
  unfold execute_CSRReg. cbv zeta.
  gm_rd i1 H1. cbn beta.
  eapply goodmb_doCSR_U; eassumption.
Qed.

Lemma exec_execute_CSRImm_total_U (csr : mword 12) (imm : mword 5) (rd : mword 5)
    (op : csrop) (s : mstate) (ms_v : mword 64) :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists res s',
    exec (execute (CSRImm (csr, imm, Regidx rd, op))) s = Some (res, s')
    /\ ((res = Illegal_Instruction tt /\ s' = s)
        \/ (res = RETIRE_SUCCESS /\ exists v, s' = gpr_write_state rd v s)).
Proof.
  intros Hpriv Hms Hfs Hvs Hmisa Hmenv HES.
  change (execute (CSRImm (csr, imm, Regidx rd, op)))
    with (execute_CSRImm csr imm (Regidx rd) op).
  unfold execute_CSRImm. cbv zeta.
  destruct (exec_doCSR_U csr (zero_extend' 64 imm) rd op
              (csr_access_type op (generic_eq (Regidx rd) zreg)
                 (eq_vec imm (zeros' 5)))
              s ms_v Hpriv Hms Hfs Hvs Hmisa Hmenv HES)
    as (res & s' & Hdo & Hcls).
  exists res, s'. split; [ exact Hdo | exact Hcls ].
Qed.

Lemma goodmb_execute_CSRImm_total_U (Dr Dw : register -> bool) (csr : mword 12)
    (imm rd : mword 5) (op : csrop) (s : mstate) (ms_v : mword 64) :
  Dr cur_privilege = true -> Dr misa = true -> Dr mstatus = true ->
  Dr menvcfg = true -> Dr mcounteren = true -> Dr scounteren = true ->
  Dr mcycle = true -> Dr mtime = true -> Dr minstret = true ->
  Dr mhpmcounter = true ->
  (uint rd <> 0 -> Dw (R_bitvector_64 (gpr_of_Z (uint rd))) = true) ->
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup mstatus s.(sregs) = ms_v ->
  eq_vec (_get_Mstatus_FS ms_v) ('b"00") = true ->
  eq_vec (_get_Mstatus_VS ms_v) ('b"00") = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  goodmb Dr Dw (execute (CSRImm (csr, imm, Regidx rd, op))) s ∅ = true.
Proof.
  intros HDcp HDmi HDms HDme HDmc HDsc HDcy HDti HDin HDh Hd
         Hpriv Hms Hfs Hvs Hmisa Hmenv HgES HES.
  change (execute (CSRImm (csr, imm, Regidx rd, op)))
    with (execute_CSRImm csr imm (Regidx rd) op).
  unfold execute_CSRImm. cbv zeta.
  eapply goodmb_doCSR_U; eassumption.
Qed.

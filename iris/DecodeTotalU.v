(* DecodeTotalU.v -- decoder totality at the U-mode reference state, WITHOUT
   the clause-by-clause symbolic peel.

   The whole problem reduces to ONE boolean fact:

       goodb D_u (ext_decode w) dstateU = true        (goodb_encdec_u)

   because [goodb] = true already implies exec-success with the state
   unchanged ([exec_goodb_congr] at s2 := s1), and the same witness
   transports the (unique) result to every agreeing state.  [goodb] never
   inspects VALUES except to follow register reads, so the proof needs no
   exec threading, no eexists, and -- critically -- no per-guard duplication
   of the clause spine: the bind rule [goodb_bind_forall] proves each
   continuation ONCE for all results, so total work is linear in the size
   of the decoder (the abandoned peel was per-clause x per-guard).          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpDecodeBridge UmodeEcall.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 goodb structural rules.                                             *)
(* ===================================================================== *)

(* The linchpin: the continuation is proven for ALL results, so a bind
   never case-splits on what its head computes.                          *)
Lemma goodb_bind_forall (D : register -> bool) {X Y} (m : M X) (f : X -> M Y) (s : mstate) :
  goodb D m s = true ->
  (forall x, goodb D (f x) s = true) ->
  goodb D (Defs.bind m f) s = true.
Proof.
  intros Hm Hf; revert Hm.
  induction m as [y|T oc k IH]; intros Hm.
  - rewrite bind_Ret. apply Hf.
  - rewrite bind_Next.
    destruct oc; cbn [goodb] in Hm |- *; try discriminate Hm;
      try (apply IH; exact Hm).
    apply andb_prop in Hm as [HD Hk]. rewrite HD. cbn. apply IH; exact Hk.
Qed.

(* goodb alone implies exec success with the state unchanged.            *)
Lemma goodb_exec_total (D : register -> bool) {X} (m : M X) (s : mstate) :
  goodb D m s = true -> exists x, exec m s = Some (x, s).
Proof.
  intros Hg.
  destruct (exec_goodb_congr D m s s (fun r _ => eq_refl) Hg) as (x & Hx & _).
  eauto.
Qed.

Lemma goodb_and_boolM (D : register -> bool) (l r : M bool) (s : mstate) :
  goodb D l s = true -> goodb D r s = true ->
  goodb D (and_boolM l r) s = true.
Proof.
  intros Hl Hr. unfold and_boolM. apply goodb_bind_forall; [exact Hl|].
  intros [|]; [exact Hr|reflexivity].
Qed.

Lemma goodb_or_boolM (D : register -> bool) (l r : M bool) (s : mstate) :
  goodb D l s = true -> goodb D r s = true ->
  goodb D (or_boolM l r) s = true.
Proof.
  intros Hl Hr. unfold or_boolM. apply goodb_bind_forall; [exact Hl|].
  intros [|]; [reflexivity|exact Hr].
Qed.

(* ===================================================================== *)
(* §2 mapper goodb lemmas (read-free, so D and s stay generic): each      *)
(*    [encdec_*_backwards] mapper is goodb-good whenever its [_matches]   *)
(*    guard holds -- same guard-destruct script as DecodeTotal's          *)
(*    [mapper_total], closing by conversion instead of [exec] rewrites.   *)
(* ===================================================================== *)

Ltac mapper_goodb :=
  let H := fresh "H" in
  intro H;
  repeat match type of H with context[if ?g then _ else _] =>
    let E := fresh "E" in destruct g eqn:E end;
  try discriminate H;
  reflexivity.

Lemma goodb_reg_backwards (D : register -> bool) (x : mword 5) (s : mstate) :
  encdec_reg_backwards_matches x = true ->
  goodb D (encdec_reg_backwards x) s = true.
Proof. unfold encdec_reg_backwards_matches, encdec_reg_backwards. mapper_goodb. Qed.

Lemma goodb_cbop_zicbop_backwards (D : register -> bool) (x : mword 5) (s : mstate) :
  encdec_cbop_zicbop_backwards_matches x = true ->
  goodb D (encdec_cbop_zicbop_backwards x) s = true.
Proof. unfold encdec_cbop_zicbop_backwards_matches, encdec_cbop_zicbop_backwards. mapper_goodb. Qed.

Lemma goodb_cbop_backwards (D : register -> bool) (x : mword 12) (s : mstate) :
  encdec_cbop_backwards_matches x = true ->
  goodb D (encdec_cbop_backwards x) s = true.
Proof. unfold encdec_cbop_backwards_matches, encdec_cbop_backwards. mapper_goodb. Qed.

Lemma goodb_ntl_backwards (D : register -> bool) (x : mword 5) (s : mstate) :
  encdec_ntl_backwards_matches x = true ->
  goodb D (encdec_ntl_backwards x) s = true.
Proof. unfold encdec_ntl_backwards_matches, encdec_ntl_backwards. mapper_goodb. Qed.

Lemma goodb_uop_backwards (D : register -> bool) (x : mword 7) (s : mstate) :
  encdec_uop_backwards_matches x = true ->
  goodb D (encdec_uop_backwards x) s = true.
Proof. unfold encdec_uop_backwards_matches, encdec_uop_backwards. mapper_goodb. Qed.

Lemma goodb_bop_backwards (D : register -> bool) (x : mword 3) (s : mstate) :
  encdec_bop_backwards_matches x = true ->
  goodb D (encdec_bop_backwards x) s = true.
Proof. unfold encdec_bop_backwards_matches, encdec_bop_backwards. mapper_goodb. Qed.

Lemma goodb_iop_backwards (D : register -> bool) (x : mword 3) (s : mstate) :
  encdec_iop_backwards_matches x = true ->
  goodb D (encdec_iop_backwards x) s = true.
Proof. unfold encdec_iop_backwards_matches, encdec_iop_backwards. mapper_goodb. Qed.

Lemma goodb_mul_op_backwards (D : register -> bool) (x : mword 3) (s : mstate) :
  encdec_mul_op_backwards_matches x = true ->
  goodb D (encdec_mul_op_backwards x) s = true.
Proof. unfold encdec_mul_op_backwards_matches, encdec_mul_op_backwards. mapper_goodb. Qed.

Lemma goodb_csrop_backwards (D : register -> bool) (x : mword 2) (s : mstate) :
  encdec_csrop_backwards_matches x = true ->
  goodb D (encdec_csrop_backwards x) s = true.
Proof. unfold encdec_csrop_backwards_matches, encdec_csrop_backwards. mapper_goodb. Qed.

Lemma goodb_amoop_backwards (D : register -> bool) (x : mword 5) (s : mstate) :
  encdec_amoop_backwards_matches x = true ->
  goodb D (encdec_amoop_backwards x) s = true.
Proof. unfold encdec_amoop_backwards_matches, encdec_amoop_backwards. mapper_goodb. Qed.

Lemma goodb_wrsop_backwards (D : register -> bool) (x : mword 12) (s : mstate) :
  encdec_wrsop_backwards_matches x = true ->
  goodb D (encdec_wrsop_backwards x) s = true.
Proof. unfold encdec_wrsop_backwards_matches, encdec_wrsop_backwards. mapper_goodb. Qed.

Lemma goodb_zicondop_backwards (D : register -> bool) (x : mword 3) (s : mstate) :
  encdec_zicondop_backwards_matches x = true ->
  goodb D (encdec_zicondop_backwards x) s = true.
Proof. unfold encdec_zicondop_backwards_matches, encdec_zicondop_backwards. mapper_goodb. Qed.

Lemma goodb_width_enc_wide_backwards (D : register -> bool) (x : mword 3) (s : mstate) :
  width_enc_wide_backwards_matches x = true ->
  goodb D (width_enc_wide_backwards x) s = true.
Proof. unfold width_enc_wide_backwards_matches, width_enc_wide_backwards. mapper_goodb. Qed.

(* ===================================================================== *)
(* §3 The traversal driver.  Arm order matters: leaves first, then the    *)
(*    closed config probes (vm_compute at the concrete dstateU), the      *)
(*    boolM combinators, the guarded mappers, if/let/match, and the       *)
(*    forall-bind LAST.                                                   *)
(* ===================================================================== *)

Ltac bool_solve :=
  repeat match goal with
         | H : (let x := _ in _) = true |- _ => cbv zeta in H
         | H : andb _ _ = true |- _ => apply andb_prop in H; destruct H
         end;
  assumption.

(* Register reads must stay VALUE-PINNED (goodb's fixpoint follows the
   actual lookup): generalizing a read's result like an ordinary bind
   would force goodb-goodness of continuations the concrete state never
   reaches (e.g. zicfiss_xSSE at VirtualSupervisor = internal_error).
   The rule is pure conversion: bind grafts, RegRead steps to the lookup. *)
Lemma goodb_bind_read_reg (D : register -> bool) {X} (r : register)
      (f : type_of_register r -> M X) (s : mstate) :
  D r = true ->
  goodb D (f (register_lookup r s.(sregs))) s = true ->
  goodb D (Defs.bind (Defs.read_reg r) f) s = true.
Proof.
  intros HD Hf.
  change (goodb D (Defs.bind (Defs.read_reg r) f) s)
    with (andb (D r) (goodb D (f (register_lookup r s.(sregs))) s)).
  rewrite HD, Hf. reflexivity.
Qed.

Ltac dt_leaf :=
  lazymatch goal with
  | |- goodb _ (returnM _) _ = true => reflexivity
  | |- goodb _ (Defs.returnm _) _ = true => reflexivity
  | |- goodb _ (Interface.Ret _) _ = true => reflexivity
  end.

Ltac dt_probe :=
  lazymatch goal with
  | |- goodb _ (currentlyEnabled _) _ = true => vm_compute; reflexivity
  | |- goodb _ (virtual_memory_supported _) _ = true => vm_compute; reflexivity
  | |- goodb _ (Defs.read_reg _) _ = true => vm_compute; reflexivity
  | |- goodb _ (zicfiss_xSSE _) _ = true => vm_compute; reflexivity
  end.

Ltac dt_boolM :=
  lazymatch goal with
  | |- goodb _ (and_boolM _ _) _ = true => apply goodb_and_boolM
  | |- goodb _ (or_boolM _ _) _ = true => apply goodb_or_boolM
  end.

Ltac dt_mapper :=
  lazymatch goal with
  | |- goodb _ (encdec_reg_backwards _) _ = true => apply goodb_reg_backwards; bool_solve
  | |- goodb _ (encdec_cbop_zicbop_backwards _) _ = true => apply goodb_cbop_zicbop_backwards; bool_solve
  | |- goodb _ (encdec_cbop_backwards _) _ = true => apply goodb_cbop_backwards; bool_solve
  | |- goodb _ (encdec_ntl_backwards _) _ = true => apply goodb_ntl_backwards; bool_solve
  | |- goodb _ (encdec_uop_backwards _) _ = true => apply goodb_uop_backwards; bool_solve
  | |- goodb _ (encdec_bop_backwards _) _ = true => apply goodb_bop_backwards; bool_solve
  | |- goodb _ (encdec_iop_backwards _) _ = true => apply goodb_iop_backwards; bool_solve
  | |- goodb _ (encdec_mul_op_backwards _) _ = true => apply goodb_mul_op_backwards; bool_solve
  | |- goodb _ (encdec_csrop_backwards _) _ = true => apply goodb_csrop_backwards; bool_solve
  | |- goodb _ (encdec_amoop_backwards _) _ = true => apply goodb_amoop_backwards; bool_solve
  | |- goodb _ (encdec_wrsop_backwards _) _ = true => apply goodb_wrsop_backwards; bool_solve
  | |- goodb _ (encdec_zicondop_backwards _) _ = true => apply goodb_zicondop_backwards; bool_solve
  | |- goodb _ (width_enc_wide_backwards _) _ = true => apply goodb_width_enc_wide_backwards; bool_solve
  end.

Ltac dt_if :=
  lazymatch goal with
  | |- goodb _ (if ?g then _ else _) _ = true =>
      tryif constr_eq g true then cbv iota
      else tryif constr_eq g false then cbv iota
      else (let E := fresh "E" in destruct g eqn:E)
  end.

Ltac dt_let :=
  lazymatch goal with
  | |- goodb _ (let x := _ in _) _ = true => cbv zeta
  end.

Ltac dt_match :=
  lazymatch goal with
  | |- goodb _ (match ?x with _ => _ end) _ = true =>
      tryif is_var x then destruct x
      else first [ progress (cbv beta iota) | let E := fresh "E" in destruct x eqn:E ]
  end.

Ltac dt_readreg :=
  lazymatch goal with
  | |- goodb _ (Defs.bind (Defs.read_reg _) _) _ = true =>
      apply goodb_bind_read_reg; [ vm_compute; reflexivity | cbv beta ]
  end.

Ltac dt_bind :=
  lazymatch goal with
  | |- goodb _ (Defs.bind _ _) _ = true =>
      apply goodb_bind_forall; [ | let x := fresh "x" in intros x ]
  end.

Ltac dt_core :=
  first [ dt_leaf | dt_probe | dt_boolM | dt_mapper | dt_if | dt_let | dt_match
        | dt_readreg | dt_bind ].

(* ===================================================================== *)
(* §4 amo_encoding_valid: its AMOCAS_Fatal arm sits behind a match on the *)
(*    concrete constant [amocas_odd_register_reserved_behavior] (=        *)
(*    AMOCAS_Illegal), so unfolding kills the [reserved_behavior] branch  *)
(*    before the traversal ever sees it.                                  *)
(* ===================================================================== *)

Lemma goodb_amo_valid (width : Z) (op : amoop) (rs2 rd : regidx) :
  goodb D_u (amo_encoding_valid width op rs2 rd) dstateU = true.
Proof.
  destruct rs2 as [rs2], rd as [rd].
  unfold amo_encoding_valid, amocas_odd_register_reserved_behavior.
  repeat dt_core.
Qed.

Ltac dt_step :=
  first
  [ lazymatch goal with
    | |- goodb _ (amo_encoding_valid _ _ _ _) _ = true => apply goodb_amo_valid
    end
  | dt_core ].

(* ===================================================================== *)
(* §5 The single boolean fact, and decoder totality.                      *)
(* ===================================================================== *)

Lemma goodb_encdec_u (w : mword 32) :
  goodb D_u (ext_decode w) dstateU = true.
Proof.
  unfold ext_decode, encdec_backwards. cbv beta zeta.
  repeat dt_step.
Qed.

(* Every 32-bit word decodes -- to a SINGLE instruction shared by every
   state that agrees with the U-mode reference on the decode read set.    *)
Theorem decode_total_u (w : mword 32) :
  exists i, forall s, agree_on D_u s dstateU ->
    exec (ext_decode w) s = Some (i, s).
Proof.
  destruct (goodb_exec_total D_u (ext_decode w) dstateU (goodb_encdec_u w)) as [i Hi].
  exists i. intros s Hag.
  destruct (exec_goodb_congr D_u (ext_decode w) dstateU s
              (fun r HD => eq_sym (Hag r HD)) (goodb_encdec_u w)) as (x & Hx & Hs).
  assert (i = x) as -> by congruence.
  exact Hs.
Qed.

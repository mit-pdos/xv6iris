(* DecodeTotal.v -- toward decode totality: every 32-bit word decodes.

   §1 sub-mapper totality: each [encdec_*_backwards] mapper used under a
      [_matches] guard in the decoder succeeds whenever its guard holds.
      One generic script: destruct the guard chain of [_matches], kill the
      contradictory all-false case, and run the corresponding branch of
      [backwards] to its returnM.

   The main peel (forall w s, cfg facts -> exists i, exec (ext_decode w) s
   = Some (i, s) /\ decodable_u i) builds on these plus the per-extension
   currentlyEnabled reduce lemmas (§2, to come).                          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Local Open Scope Z_scope.
Import Defs.

(* the generic mapper-totality script *)
Ltac mapper_total :=
  let H := fresh "H" in
  intro H;
  repeat match type of H with context[if ?g then _ else _] =>
    let E := fresh "E" in destruct g eqn:E end;
  try discriminate H; eexists;
  repeat (rewrite ?exec_bind; cbn match beta);
  try (unfold Defs.assert_exp'; cbn match); apply exec_returnm.

Lemma total_reg_backwards (x : mword 5) s :
  encdec_reg_backwards_matches x = true ->
  exists v, exec (encdec_reg_backwards x) s = Some (v, s).
Proof. unfold encdec_reg_backwards_matches, encdec_reg_backwards. mapper_total. Qed.

Lemma total_cbop_zicbop_backwards (x : mword 5) s :
  encdec_cbop_zicbop_backwards_matches x = true ->
  exists v, exec (encdec_cbop_zicbop_backwards x) s = Some (v, s).
Proof. unfold encdec_cbop_zicbop_backwards_matches, encdec_cbop_zicbop_backwards. mapper_total. Qed.

Lemma total_cbop_backwards (x : mword 12) s :
  encdec_cbop_backwards_matches x = true ->
  exists v, exec (encdec_cbop_backwards x) s = Some (v, s).
Proof. unfold encdec_cbop_backwards_matches, encdec_cbop_backwards. mapper_total. Qed.

Lemma total_ntl_backwards (x : mword 5) s :
  encdec_ntl_backwards_matches x = true ->
  exists v, exec (encdec_ntl_backwards x) s = Some (v, s).
Proof. unfold encdec_ntl_backwards_matches, encdec_ntl_backwards. mapper_total. Qed.

Lemma total_uop_backwards (x : mword 7) s :
  encdec_uop_backwards_matches x = true ->
  exists v, exec (encdec_uop_backwards x) s = Some (v, s).
Proof. unfold encdec_uop_backwards_matches, encdec_uop_backwards. mapper_total. Qed.

Lemma total_bop_backwards (x : mword 3) s :
  encdec_bop_backwards_matches x = true ->
  exists v, exec (encdec_bop_backwards x) s = Some (v, s).
Proof. unfold encdec_bop_backwards_matches, encdec_bop_backwards. mapper_total. Qed.

Lemma total_iop_backwards (x : mword 3) s :
  encdec_iop_backwards_matches x = true ->
  exists v, exec (encdec_iop_backwards x) s = Some (v, s).
Proof. unfold encdec_iop_backwards_matches, encdec_iop_backwards. mapper_total. Qed.

Lemma total_mul_op_backwards (x : mword 3) s :
  encdec_mul_op_backwards_matches x = true ->
  exists v, exec (encdec_mul_op_backwards x) s = Some (v, s).
Proof. unfold encdec_mul_op_backwards_matches, encdec_mul_op_backwards. mapper_total. Qed.

Lemma total_csrop_backwards (x : mword 2) s :
  encdec_csrop_backwards_matches x = true ->
  exists v, exec (encdec_csrop_backwards x) s = Some (v, s).
Proof. unfold encdec_csrop_backwards_matches, encdec_csrop_backwards. mapper_total. Qed.

Lemma total_amoop_backwards (x : mword 5) s :
  encdec_amoop_backwards_matches x = true ->
  exists v, exec (encdec_amoop_backwards x) s = Some (v, s).
Proof. unfold encdec_amoop_backwards_matches, encdec_amoop_backwards. mapper_total. Qed.

Lemma total_wrsop_backwards (x : mword 12) s :
  encdec_wrsop_backwards_matches x = true ->
  exists v, exec (encdec_wrsop_backwards x) s = Some (v, s).
Proof. unfold encdec_wrsop_backwards_matches, encdec_wrsop_backwards. mapper_total. Qed.

Lemma total_zicondop_backwards (x : mword 3) s :
  encdec_zicondop_backwards_matches x = true ->
  exists v, exec (encdec_zicondop_backwards x) s = Some (v, s).
Proof. unfold encdec_zicondop_backwards_matches, encdec_zicondop_backwards. mapper_total. Qed.

(* encdec_creg_backwards is PURE (returns cregidx) -- no totality lemma needed *)

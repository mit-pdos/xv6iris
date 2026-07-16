(* WpUserClassifyTotal.v -- the total-classification capstone: prove
   [∀ frame, ustep_case ∨ ustep_mem_case ∨ ustep_fault_case] with no
   TLB-hit premise, then feed it to [user_step_holds_full] for an
   unconditional [wp_user_exec].  Built incrementally against local
   well-formedness hypotheses; the [uctx] contract fields are baked in
   at the end. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep.
Require Import WpGpr.
Require Import WpDecodeBridge.
Require Import UptInv WpUserBase.
Require Import WpUserSteps.
Require Import WpUserClassify.
Require Import WpUserFull.
Require Import DecodeSetU.
Local Open Scope Z_scope.
Import Defs.

(* ------------------------------------------------------------------ *)
(* Fetch-word existence: if all 4 bytes of an instruction slot are
   present in a byte map, they assemble into a concrete word whose
   [nth_byte]s are exactly those bytes.  This is the pure engine that
   turns a "page is resident in [code]" well-formedness fact into the
   [∃ w, ...] fetch premise of [ufetch_hit].                          *)
(* ------------------------------------------------------------------ *)

(* [nth_byte] of a little-endian assembled word recovers each byte.  This is
   the instance-free core (it never touches a gmap, only [bv 8] values), so it
   sidesteps the [Arch.pa] Countable-instance mismatch between [read_bytes]
   (stdpp [bv_countable]) and the [uctx] [code]/[data] maps. *)
Lemma nth_byte_assemble (bs : list (bv 8)) (j : nat) :
  (j < length bs)%nat ->
  nth_byte (Z_to_bv (8 * N.of_nat (length bs)) (assemble_bytes bs)) j = bs !!! j.
Proof.
  intros Hjlt.
  apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi].
  rewrite (Z.mod_small (assemble_bytes bs));
    [| split; [lia | rewrite N2Z.inj_mul; lia ] ].
  pose proof (assemble_bytes_byte bs j Hjlt) as Hbyte.
  rewrite Nat2Z.inj_mul in Hbyte. change (Z.of_nat 8) with 8 in Hbyte.
  replace (Z.of_N (8 * N.of_nat j)) with (8 * Z.of_nat j) by (rewrite N2Z.inj_mul; lia).
  rewrite Hbyte. reflexivity.
Qed.

(* Four bytes assemble into a concrete 32-bit word whose [nth_byte]s are
   exactly those bytes -- the pure fetch-word constructor. *)
Lemma word_of_bytes4 (b0 b1 b2 b3 : bv 8) :
  exists w : mword 32,
    nth_byte w 0%nat = b0 /\ nth_byte w 1%nat = b1 /\
    nth_byte w 2%nat = b2 /\ nth_byte w 3%nat = b3.
Proof.
  exists (Z_to_bv 32 (assemble_bytes [b0;b1;b2;b3])).
  pose proof (fun j Hj => nth_byte_assemble [b0;b1;b2;b3] j Hj) as H.
  simpl length in H. change (8 * N.of_nat 4)%N with 32%N in H.
  split; [|split; [|split]].
  - exact (H 0%nat ltac:(lia)).
  - exact (H 1%nat ltac:(lia)).
  - exact (H 2%nat ltac:(lia)).
  - exact (H 3%nat ltac:(lia)).
Qed.

(* Two bytes assemble into a 16-bit halfword (compressed fetch). *)
Lemma hword_of_bytes2 (b0 b1 : bv 8) :
  exists h : mword 16,
    nth_byte h 0%nat = b0 /\ nth_byte h 1%nat = b1.
Proof.
  exists (Z_to_bv 16 (assemble_bytes [b0;b1])).
  pose proof (fun j Hj => nth_byte_assemble [b0;b1] j Hj) as H.
  simpl length in H. change (8 * N.of_nat 2)%N with 16%N in H.
  split.
  - exact (H 0%nat ltac:(lia)).
  - exact (H 1%nat ltac:(lia)).
Qed.

(* Package: given the four instruction bytes present in a byte map [mm]
   (any instance), there is a word [w] with [mm !! pa_add pa j = Some
   (nth_byte w j)] for j < 4 -- the exact shape of the [ufetch_hit] fetch
   conjunct.  Works for [code] regardless of its Countable instance. *)
Lemma bytes_to_word4 {K} `{Countable K} (mm : gmap K (bv 8))
    (nb : nat -> K) :
  (forall j, (j < 4)%nat -> exists b, mm !! nb j = Some b) ->
  exists w : mword 32,
    forall j, (j < 4)%nat -> mm !! nb j = Some (nth_byte w j).
Proof.
  intros Hex.
  destruct (Hex 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hex 1%nat ltac:(lia)) as [b1 Hb1].
  destruct (Hex 2%nat ltac:(lia)) as [b2 Hb2].
  destruct (Hex 3%nat ltac:(lia)) as [b3 Hb3].
  destruct (word_of_bytes4 b0 b1 b2 b3) as (w & E0 & E1 & E2 & E3).
  exists w. intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
    first [ rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3 ]; assumption.
Qed.

Lemma bytes_to_hword2 {K} `{Countable K} (mm : gmap K (bv 8))
    (nb : nat -> K) :
  (forall j, (j < 2)%nat -> exists b, mm !! nb j = Some b) ->
  exists h : mword 16,
    forall j, (j < 2)%nat -> mm !! nb j = Some (nth_byte h j).
Proof.
  intros Hex.
  destruct (Hex 0%nat ltac:(lia)) as [b0 Hb0].
  destruct (Hex 1%nat ltac:(lia)) as [b1 Hb1].
  destruct (hword_of_bytes2 b0 b1) as (h & E0 & E1).
  exists h. intros j Hj.
  destruct j as [|[|j']]; try lia;
    first [ rewrite E0 | rewrite E1 ]; assumption.
Qed.

(* ====================================================================== *)
(* UImgWordDefs.v -- EIGHT IMAGE BYTES PIN THE WORD THEY ENCODE.           *)
(*                                                                        *)
(* The two byte-window lemmas relating a user image map's own              *)
(* [Some (nth_byte w k)] spelling to the contract's                        *)
(* [bv_to_little_endian], and the determinacy that follows.  Pure facts    *)
(* about a [gmap Z (bv 8)] -- no slot, no WP, nothing about /init or /sh.  *)
(*                                                                        *)
(* They were proved in [UInitSh.v] because that is where they were first   *)
(* needed; [UShEcho.v] wants exactly these two and nothing else of         *)
(* /init's shell-entry proof, which is a 10 s node on the build's          *)
(* critical path.  See claude-notes/design/code-organization.md -- a lemma *)
(* belongs at the altitude of what it says.                               *)
(*                                                                        *)
(* [UInitSh.v] RE-EXPORTS this file, so its own uses and every existing    *)
(* importer are unchanged.                                                *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
                                   (* the ssreflect [rewrite A B] the
                                      moved proofs are written in *)
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.    (* [nth_byte], [bv_le_nth_byte] *)
Require Import SpecCopyin.         (* [uimg_word_at] *)
Require Import UmodeArith.         (* [moi_small], [Z64] *)

Local Open Scope Z_scope.

(* an eight-byte window of the image, in the two spellings: the map's own
   [Some (nth_byte w k)] and the contract's [bv_to_little_endian] *)
Lemma img_word_of_bytes (M : gmap Z (bv 8)) (a z : Z) :
  (forall k : nat, (k < 8)%nat ->
     M !! (a + Z.of_nat k) = Some (nth_byte (mword_of_int z : mword 64) k)) ->
  forall k : nat, (k < 8)%nat ->
    M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 z !! k.
Proof.
  intros H k Hk. rewrite (H k Hk). exact (eq_sym (bv_le_nth_byte z k Hk)).
Qed.

(* the two spellings of a word's bytes agree, so eight image bytes pin the
   word they encode *)
Lemma uimg_word_det (M : gmap Z (bv 8)) (a : Z) (w : mword 64) (z : Z) :
  0 <= z < 2 ^ 64 ->
  uimg_word_at M a w ->
  (forall k : nat, (k < 8)%nat ->
     M !! (a + Z.of_nat k) = bv_to_little_endian 8 8 z !! k) ->
  w = (mword_of_int z : mword 64).
Proof.
  intros Hz Hw Hz8.
  assert (Hlen : forall y : Z, length (bv_to_little_endian 8 8 y) = 8%nat)
    by (intro y; rewrite (length_bv_to_little_endian 8 8 y ltac:(lia));
        reflexivity).
  assert (Hl : bv_to_little_endian 8 8 (bv_unsigned w)
               = bv_to_little_endian 8 8 z).
  { apply list_eq. intro k.
    destruct (decide (k < 8)%nat) as [Hk | Hk].
    - rewrite <- (Hw k Hk). exact (Hz8 k Hk).
    - assert (Hnw : bv_to_little_endian 8 8 (bv_unsigned w) !! k = None)
        by (apply lookup_ge_None_2; rewrite Hlen; lia).
      assert (Hnz : bv_to_little_endian 8 8 z !! k = None)
        by (apply lookup_ge_None_2; rewrite Hlen; lia).
      rewrite Hnw Hnz. reflexivity. }
  assert (Hmod : bv_unsigned w `mod` 2 ^ 64 = z `mod` 2 ^ 64).
  { pose proof (little_endian_to_bv_to_little_endian 8 8 (bv_unsigned w)
                  ltac:(lia)) as H1.
    pose proof (little_endian_to_bv_to_little_endian 8 8 z ltac:(lia)) as H2.
    change (8 * Z.of_N 8) with 64 in H1.
    change (8 * Z.of_N 8) with 64 in H2.
    rewrite <- H1. rewrite <- H2. rewrite Hl. reflexivity. }
  pose proof (bv_unsigned_in_range _ w) as Hr.
  unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
  rewrite (Z.mod_small _ _ Hr) in Hmod.
  rewrite (Z.mod_small _ _ Hz) in Hmod.
  apply bv_eq. rewrite Hmod.
  exact (eq_sym (moi_small z ltac:(unfold Z64; lia))).
Qed.

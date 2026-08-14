(* BitmapEnc.v -- the BITS inside a disk block.

   A disk block is 1024 raw bytes ([list (bv 8)]); the BLOCK BITMAP reads
   those same bytes as 8192 one-bit allocation flags, bit [bi] living in
   byte [bi / 8] at mask [1 << (bi mod 8)] -- exactly the address and mask
   balloc/bfree compute ([bp->data[bi/8]] and [1 << (bi % 8)]).

   This is the third vocabulary of its kind after [BlockWords.v]'s words
   and [DinodeEnc.v]'s records, and it follows the same discipline: the
   block's content is always in the IMAGE of an encoding function over a
   PURE index set, so an update is a set operation ([u ∪ {[bi]}] /
   [u ∖ {[bi]}]) and the byte level is only ever read back.

     [bm_byte u j]     -- byte [j] of the bitmap whose SET BITS are [u]
                          (bit [k] of it is set iff [8*j + k ∈ u])
     [bm_bytes n u]    -- the first [n] such bytes, i.e. the block image

   POLARITY: [u] is the set of SET bits, and in xv6 a set bit means the
   block is IN USE.  The free pool ([BitmapInv.v]) is therefore indexed by
   the COMPLEMENT of [u] below sb.size, which is the direction the
   allocator's handshake runs in.

   The three laws the WP proof needs at the arithmetic seam are stated on
   [Z] rather than on [bv 8] ([bm_byte_land_pow2] / [bm_byte_lor_pow2] /
   [bm_byte_ldiff_pow2]): the code's [and]/[or]/[not] run at 64 bits over
   a zero-extended [lbu] and a [sllw]-formed mask, and [bv_and_unsigned] &
   co. land exactly on [Z.land]/[Z.lor]/[Z.lnot].

   The block-image update law is [bm_bytes_upd] (and its two corollaries
   [bm_bytes_set] / [bm_bytes_clear]): storing one byte into the image of
   [u] yields the image of the updated set, which is what relates
   log_write of the whole bitmap block to a one-element set operation.

   This file is iris-FREE (no proofmode, no ssreflect) and Sail-free, so it
   stays usable from the vanilla-[rewrite ... by ...] files per
   durable-notes' ssreflect rule -- and, by not naming [SailStdpp.Values],
   it cannot leak the [Countable] instances that break unrelated proofs.
   The block SIZE is deliberately a parameter [n]: BSIZE lives in
   FsCrash.v, which is not iris-free.                                     *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
(* The tree-wide [set_solver] override.  EXPORT, not Import, and that is not
   cosmetic: this import is deliberately "dead" -- everything here compiles
   without it, just far slower -- so the nightly dead-import sweep
   (.github/workflows/dead-imports.yml) would delete it.  The sweep skips
   [Require Export] lines.  See FastSetSolver.v. *)
Require Export FastSetSolver.

Local Open Scope Z_scope.

(* a decidable-proposition congruence, used at every byte comparison *)
Lemma bool_decide_iff_eq (P Q : Prop) `{Decision P, Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof. intros Hiff. repeat case_bool_decide; solve [reflexivity | exfalso; tauto]. Qed.

(* ---------------------------------------------------------------------- *)
(* A byte, from eight bools, least significant first.                      *)
(* ---------------------------------------------------------------------- *)

Fixpoint bits_to_Z (l : list bool) : Z :=
  match l with
  | [] => 0
  | true :: t => 2 * bits_to_Z t + 1
  | false :: t => 2 * bits_to_Z t
  end.

Lemma bits_to_Z_nonneg (l : list bool) : 0 <= bits_to_Z l.
Proof. induction l as [|[|] l IH]; simpl; lia. Qed.

Lemma bits_to_Z_lt (l : list bool) : bits_to_Z l < 2 ^ Z.of_nat (length l).
Proof.
  induction l as [|[|] l IH]; simpl length.
  - simpl bits_to_Z. simpl Z.of_nat. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    simpl bits_to_Z. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    simpl bits_to_Z. lia.
Qed.

Lemma bits_to_Z_testbit (l : list bool) (k : Z) :
  0 <= k -> Z.testbit (bits_to_Z l) k = default false (l !! Z.to_nat k).
Proof.
  revert k. induction l as [|b l IH]; intros k Hk.
  - simpl bits_to_Z. rewrite Z.testbit_0_l.
    destruct (Z.to_nat k); reflexivity.
  - destruct (Z.eq_dec k 0) as [->|Hne].
    + destruct b; simpl bits_to_Z.
      * rewrite Z.testbit_odd_0. reflexivity.
      * rewrite Z.testbit_even_0. reflexivity.
    + destruct (Z.to_nat k) as [|nk] eqn:Hnk; [lia|].
      cbn [lookup list_lookup].
      assert (Hk1 : k = Z.succ (Z.of_nat nk)) by lia.
      assert (Hnk2 : Z.to_nat (Z.of_nat nk) = nk) by lia.
      rewrite Hk1.
      destruct b; simpl bits_to_Z.
      * rewrite Z.testbit_odd_succ by lia. rewrite IH by lia.
        rewrite Hnk2. reflexivity.
      * rewrite Z.testbit_even_succ by lia. rewrite IH by lia.
        rewrite Hnk2. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* One byte of a bitmap whose set bits are [u].                            *)
(* ---------------------------------------------------------------------- *)

Definition byte_bits (u : gset Z) (j : Z) : list bool :=
  (fun k : nat => bool_decide (8 * j + Z.of_nat k ∈ u)) <$> seq 0 8.

Lemma byte_bits_length (u : gset Z) (j : Z) : length (byte_bits u j) = 8%nat.
Proof. unfold byte_bits. rewrite length_fmap, length_seq. reflexivity. Qed.

Lemma byte_bits_lookup (u : gset Z) (j : Z) (k : nat) :
  (k < 8)%nat ->
  byte_bits u j !! k = Some (bool_decide (8 * j + Z.of_nat k ∈ u)).
Proof.
  intros Hk. unfold byte_bits. rewrite list_lookup_fmap.
  rewrite lookup_seq_lt by exact Hk. reflexivity.
Qed.

Definition bm_byte (u : gset Z) (j : Z) : bv 8 :=
  Z_to_bv 8 (bits_to_Z (byte_bits u j)).

Lemma bm_byte_unsigned (u : gset Z) (j : Z) :
  bv_unsigned (bm_byte u j) = bits_to_Z (byte_bits u j).
Proof.
  unfold bm_byte. apply Z_to_bv_small.
  pose proof (bits_to_Z_nonneg (byte_bits u j)) as Hlo.
  pose proof (bits_to_Z_lt (byte_bits u j)) as Hhi.
  rewrite byte_bits_length in Hhi.
  change (2 ^ Z.of_nat 8) with 256 in Hhi.
  change (2 ^ Z.of_N 8) with 256. split; assumption.
Qed.

Lemma bm_byte_bound (u : gset Z) (j : Z) : 0 <= bv_unsigned (bm_byte u j) < 256.
Proof.
  pose proof (bv_unsigned_in_range _ (bm_byte u j)) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

(* THE characterisation: bit [k] of byte [j] is set iff block [8*j+k] is. *)
Lemma bm_byte_testbit (u : gset Z) (j k : Z) :
  0 <= k < 8 ->
  Z.testbit (bv_unsigned (bm_byte u j)) k = bool_decide (8 * j + k ∈ u).
Proof.
  intros Hk. rewrite bm_byte_unsigned.
  rewrite bits_to_Z_testbit by lia.
  rewrite byte_bits_lookup by lia.
  cbn [default from_option]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bm_byte_testbit_high (u : gset Z) (j n : Z) :
  8 <= n -> Z.testbit (bv_unsigned (bm_byte u j)) n = false.
Proof.
  intros Hn. rewrite bm_byte_unsigned.
  rewrite bits_to_Z_testbit by lia.
  rewrite (lookup_ge_None_2 (byte_bits u j) (Z.to_nat n))
    by (rewrite byte_bits_length; lia).
  reflexivity.
Qed.

Lemma bm_byte_ext (u u' : gset Z) (j : Z) :
  (forall k : Z, 0 <= k < 8 -> (8 * j + k ∈ u <-> 8 * j + k ∈ u')) ->
  bm_byte u j = bm_byte u' j.
Proof.
  intros H. apply bv_eq. rewrite !bm_byte_unsigned. f_equal.
  apply list_eq. intros i.
  destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
  - rewrite !byte_bits_lookup by exact Hi. f_equal.
    apply bool_decide_iff_eq. apply H. lia.
  - rewrite !(lookup_ge_None_2 _ i) by (rewrite byte_bits_length; lia).
    reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The three arithmetic laws, on Z (where the mword layer lands).          *)
(* ---------------------------------------------------------------------- *)

(* TEST: [bp->data[j] & (1 << k)] is zero exactly when the block is free. *)
Lemma bm_byte_land_pow2 (u : gset Z) (j k : Z) :
  0 <= k < 8 ->
  Z.land (bv_unsigned (bm_byte u j)) (2 ^ k)
  = (if bool_decide (8 * j + k ∈ u) then 2 ^ k else 0).
Proof.
  intros Hk. apply Z.bits_inj_iff'. intros n Hn.
  rewrite Z.land_spec, (Z.pow2_bits_eqb k n) by lia.
  destruct (Z.eq_dec k n) as [->|Hne].
  - rewrite Z.eqb_refl, andb_true_r.
    rewrite bm_byte_testbit by lia.
    destruct (bool_decide (8 * j + n ∈ u)); cbn.
    + rewrite (Z.pow2_bits_eqb n n) by lia. rewrite Z.eqb_refl. reflexivity.
    + rewrite Z.testbit_0_l. reflexivity.
  - assert (Hkn : (k =? n) = false) by (apply Z.eqb_neq; exact Hne).
    rewrite Hkn, andb_false_r.
    destruct (bool_decide (8 * j + k ∈ u)).
    + rewrite (Z.pow2_bits_eqb k n) by lia. rewrite Hkn. reflexivity.
    + rewrite Z.testbit_0_l. reflexivity.
Qed.

(* SET: [bp->data[j] |= (1 << k)] adds the block to the used set. *)
Lemma bm_byte_lor_pow2 (u : gset Z) (j k : Z) :
  0 <= k < 8 ->
  Z.lor (bv_unsigned (bm_byte u j)) (2 ^ k)
  = bv_unsigned (bm_byte (u ∪ {[ 8 * j + k ]}) j).
Proof.
  intros Hk. apply Z.bits_inj_iff'. intros n Hn.
  rewrite Z.lor_spec, (Z.pow2_bits_eqb k n) by lia.
  destruct (Z.lt_ge_cases n 8) as [Hn8|Hn8].
  - rewrite !bm_byte_testbit by lia.
    destruct (Z.eq_dec k n) as [->|Hne].
    + rewrite Z.eqb_refl, orb_true_r.
      symmetry. apply bool_decide_eq_true. set_solver.
    + assert (Hkn : (k =? n) = false) by (apply Z.eqb_neq; exact Hne).
      rewrite Hkn, orb_false_r.
      apply bool_decide_iff_eq. split; [set_solver|].
      intros Hin. apply elem_of_union in Hin as [Hin|Hs]; [exact Hin|].
      apply elem_of_singleton in Hs. exfalso. lia.
  - rewrite !bm_byte_testbit_high by lia.
    assert (Hkn : (k =? n) = false) by (apply Z.eqb_neq; lia).
    rewrite Hkn. reflexivity.
Qed.

(* CLEAR: [bp->data[j] &= ~(1 << k)] removes the block from the used set. *)
Lemma bm_byte_ldiff_pow2 (u : gset Z) (j k : Z) :
  0 <= k < 8 ->
  Z.land (bv_unsigned (bm_byte u j)) (Z.lnot (2 ^ k))
  = bv_unsigned (bm_byte (u ∖ {[ 8 * j + k ]}) j).
Proof.
  intros Hk. apply Z.bits_inj_iff'. intros n Hn.
  rewrite Z.land_spec, Z.lnot_spec by lia.
  rewrite (Z.pow2_bits_eqb k n) by lia.
  destruct (Z.lt_ge_cases n 8) as [Hn8|Hn8].
  - rewrite !bm_byte_testbit by lia.
    destruct (Z.eq_dec k n) as [->|Hne].
    + rewrite Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
      symmetry. apply bool_decide_eq_false. set_solver.
    + assert (Hkn : (k =? n) = false) by (apply Z.eqb_neq; exact Hne).
      rewrite Hkn. cbn [negb]. rewrite andb_true_r.
      apply bool_decide_iff_eq. split; [|set_solver].
      intros Hin. apply elem_of_difference. split; [exact Hin|].
      intros Hs. apply elem_of_singleton in Hs. exfalso. lia.
  - rewrite !bm_byte_testbit_high by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The block image.                                                        *)
(* ---------------------------------------------------------------------- *)

Definition bm_bytes (n : nat) (u : gset Z) : list (bv 8) :=
  (fun j : nat => bm_byte u (Z.of_nat j)) <$> seq 0 n.

Lemma bm_bytes_length (n : nat) (u : gset Z) : length (bm_bytes n u) = n.
Proof. unfold bm_bytes. rewrite length_fmap, length_seq. reflexivity. Qed.

Lemma bm_bytes_lookup (n : nat) (u : gset Z) (j : nat) :
  (j < n)%nat -> bm_bytes n u !! j = Some (bm_byte u (Z.of_nat j)).
Proof.
  intros Hj. unfold bm_bytes. rewrite list_lookup_fmap.
  rewrite lookup_seq_lt by exact Hj. reflexivity.
Qed.

Lemma bm_bytes_lookup_None (n : nat) (u : gset Z) (j : nat) :
  (n <= j)%nat -> bm_bytes n u !! j = None.
Proof. intros Hj. apply lookup_ge_None_2. rewrite bm_bytes_length. lia. Qed.

(* the byte index of a bit, and the two facts every consumer restates *)
Lemma bit_split (bi : Z) : 8 * (bi `div` 8) + bi `mod` 8 = bi.
Proof. pose proof (Z.div_mod bi 8 ltac:(lia)). lia. Qed.

Lemma bit_off_range (bi : Z) : 0 <= bi -> 0 <= bi `mod` 8 < 8.
Proof. intros _. apply Z.mod_pos_bound. lia. Qed.

Lemma bit_byte_of (i k : Z) : 0 <= k < 8 -> (8 * i + k) `div` 8 = i.
Proof.
  intros Hk. rewrite (Z.mul_comm 8 i). rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia. lia.
Qed.

(* ---- installing one byte -------------------------------------------- *)

(* THE law: storing byte [j] of the image of [u'] over the image of [u]
   yields the image of [u'], provided [u] and [u'] agree away from byte
   [j].  Everything the allocator does to the block is an instance. *)
Lemma bm_bytes_upd (n : nat) (u u' : gset Z) (j : Z) :
  0 <= j -> (Z.to_nat j < n)%nat ->
  (forall x : Z, 0 <= x -> x `div` 8 <> j -> (x ∈ u <-> x ∈ u')) ->
  <[Z.to_nat j := bm_byte u' j]> (bm_bytes n u) = bm_bytes n u'.
Proof.
  intros Hj Hjn Hag. apply list_eq. intros i.
  destruct (Nat.eq_dec i (Z.to_nat j)) as [->|Hne].
  - rewrite list_lookup_insert by (rewrite bm_bytes_length; exact Hjn).
    rewrite bm_bytes_lookup by exact Hjn.
    rewrite Z2Nat.id by exact Hj. reflexivity.
  - rewrite list_lookup_insert_ne by congruence.
    destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
    + rewrite !bm_bytes_lookup by exact Hi. f_equal.
      apply bm_byte_ext. intros k Hk.
      apply Hag; [lia|]. rewrite bit_byte_of by exact Hk. lia.
    + rewrite !bm_bytes_lookup_None by exact Hi. reflexivity.
Qed.

Lemma bm_bytes_set (n : nat) (u : gset Z) (bi : Z) :
  0 <= bi -> (Z.to_nat (bi `div` 8) < n)%nat ->
  <[Z.to_nat (bi `div` 8) := bm_byte (u ∪ {[bi]}) (bi `div` 8)]> (bm_bytes n u)
  = bm_bytes n (u ∪ {[bi]}).
Proof.
  intros Hbi Hn. apply bm_bytes_upd; [apply Z.div_pos; lia|exact Hn|].
  intros x Hx Hxd. split; [set_solver|]. intros Hin.
  apply elem_of_union in Hin as [Hin|Hin]; [exact Hin|].
  apply elem_of_singleton in Hin. congruence.
Qed.

Lemma bm_bytes_clear (n : nat) (u : gset Z) (bi : Z) :
  0 <= bi -> (Z.to_nat (bi `div` 8) < n)%nat ->
  <[Z.to_nat (bi `div` 8) := bm_byte (u ∖ {[bi]}) (bi `div` 8)]> (bm_bytes n u)
  = bm_bytes n (u ∖ {[bi]}).
Proof.
  intros Hbi Hn. apply bm_bytes_upd; [apply Z.div_pos; lia|exact Hn|].
  intros x Hx Hxd. split; [|set_solver]. intros Hin.
  apply elem_of_difference. split; [exact Hin|].
  intros Hs. apply elem_of_singleton in Hs. congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(* The same three laws, spelled AT A BIT INDEX -- the form the code uses:   *)
(* balloc and bfree compute the byte as [bi / 8] and the mask as            *)
(* [1 << (bi % 8)], never as a separate (j, k) pair.                        *)
(* ---------------------------------------------------------------------- *)

Lemma bm_bit_test (u : gset Z) (bi : Z) :
  0 <= bi ->
  Z.land (bv_unsigned (bm_byte u (bi `div` 8))) (2 ^ (bi `mod` 8))
  = (if bool_decide (bi ∈ u) then 2 ^ (bi `mod` 8) else 0).
Proof.
  intros Hbi. rewrite bm_byte_land_pow2 by (apply bit_off_range; exact Hbi).
  rewrite bit_split. reflexivity.
Qed.

Lemma bm_bit_set (u : gset Z) (bi : Z) :
  0 <= bi ->
  Z.lor (bv_unsigned (bm_byte u (bi `div` 8))) (2 ^ (bi `mod` 8))
  = bv_unsigned (bm_byte (u ∪ {[bi]}) (bi `div` 8)).
Proof.
  intros Hbi. rewrite bm_byte_lor_pow2 by (apply bit_off_range; exact Hbi).
  rewrite bit_split. reflexivity.
Qed.

Lemma bm_bit_clear (u : gset Z) (bi : Z) :
  0 <= bi ->
  Z.land (bv_unsigned (bm_byte u (bi `div` 8))) (Z.lnot (2 ^ (bi `mod` 8)))
  = bv_unsigned (bm_byte (u ∖ {[bi]}) (bi `div` 8)).
Proof.
  intros Hbi. rewrite bm_byte_ldiff_pow2 by (apply bit_off_range; exact Hbi).
  rewrite bit_split. reflexivity.
Qed.

(* the byte index is in range whenever the bit is *)
Lemma bit_byte_lt (n : nat) (bi : Z) :
  0 <= bi < 8 * Z.of_nat n -> (Z.to_nat (bi `div` 8) < n)%nat.
Proof.
  intros Hbi. assert (bi `div` 8 < Z.of_nat n) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= bi `div` 8) by (apply Z.div_pos; lia). lia.
Qed.

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Import VcGen.
Require Import WpIntenaBits.
Require Import WpGprCsrwCommon.
(* helper bridges for ProofPushOff -- pure bit-vector facts *)
Require Import CpuOwn.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

Lemma bvw32_small (z : Z) : (0 <= z < 2^32)%Z -> bv_wrap 32 z = z.
Proof. intro. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. lia. Qed.

Lemma bvw64_small (z : Z) : (0 <= z < 2^64)%Z -> bv_wrap 64 z = z.
Proof. intro. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z. lia. Qed.

Lemma moi32_unsigned (z : Z) : bv_unsigned (mword_of_int z : mword 32) = bv_wrap 32 z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N. reflexivity.
Qed.

Lemma moi32_small (z : Z) : (0 <= z < 2^32)%Z -> bv_unsigned (mword_of_int z : mword 32) = z.
Proof. intro. rewrite moi32_unsigned. apply bvw32_small. lia. Qed.

Lemma sext64_moi32_unsigned (z : Z) : (0 <= z < 2^31)%Z ->
  bv_unsigned (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = z.
Proof.
  intro Hz.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite (bvw32_small z) by (change (2^32) with (2*2^31); lia).
  rewrite bv_swrap_small by (assert (Hhm : bv_half_modulus 32 = 2^31) by reflexivity; rewrite Hhm; lia).
  apply bvw64_small. lia.
Qed.

Lemma sint64_moi32 (z : Z) : (0 <= z < 2^31)%Z ->
  sint (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite sext64_moi32_unsigned by lia.
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

Lemma push_storeval_succ (n : nat) : (Z.of_nat n + 1 < 2^31)%Z ->
  (autocast (T := mword)
    (subrange_vec_dec
       (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val n))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
       (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val (S n).
Proof.
  intro Hb.
  change (autocast (T := mword)
    (subrange_vec_dec
       (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val n))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
       (Z.sub (Z.mul 4 8) 1) 0) : mword 32)
    with (trunc32 (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val n))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))).
  rewrite <- trunc32_subrange.
  rewrite trunc32_sext.
  rewrite trunc32_add.
  rewrite trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK.
  apply bv_eq.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  unfold noff_val.
  rewrite (moi32_small (Z.of_nat n)) by (change (2^32) with (2*2^31); lia).
  rewrite (moi32_small 1) by lia.
  rewrite moi32_unsigned.
  rewrite Nat2Z.inj_succ.
  rewrite !bvw32_small by (change (2^32) with (2*2^31); lia).
  lia.
Qed.

Lemma noff_val_zero (n : nat) : (Z.of_nat n < 2^31)%Z ->
  eq_vec (sign_extend' 64 (noff_val n)) (zero_reg : mword 64) = (n =? 0)%nat.
Proof.
  intro Hb.
  destruct n as [|n'].
  - vm_compute. reflexivity.
  - cbn [Nat.eqb].
    apply eq_vec_false_iff. intro Heq.
    apply (f_equal bv_unsigned) in Heq.
    unfold noff_val in Heq.
    rewrite sext64_moi32_unsigned in Heq by lia.
    change (bv_unsigned (zero_reg : mword 64)) with 0%Z in Heq. lia.
Qed.

Lemma pop_nv1_pred (n : nat) : (Z.of_nat (S n) < 2^31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 (noff_val (S n)))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
   = sign_extend' 64 (noff_val n).
Proof.
  intro Hb.
  rewrite <- trunc32_subrange.
  f_equal.
  apply bv_eq.
  rewrite trunc32_unsigned.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (HK : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)) : mword 64) = (2^64 - 1)%Z)
    by (vm_compute; reflexivity).
  rewrite HK.
  unfold noff_val.
  rewrite sext64_moi32_unsigned by lia.
  rewrite moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  rewrite bv_wrap_bv_wrap by lia.
  rewrite Nat2Z.inj_succ.
  unfold bv_wrap, bv_modulus.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
  replace (Z.succ (Z.of_nat n) + (2 ^ 64 - 1))%Z with (Z.of_nat n + 2 ^ 64)%Z by lia.
  change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma pop_storeval_pred (n : nat) : (Z.of_nat (S n) < 2^31)%Z ->
  (autocast (T := mword)
    (subrange_vec_dec
       (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val (S n)))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
       (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = noff_val n.
Proof.
  intro Hb.
  change (autocast (T := mword)
    (subrange_vec_dec
       (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val (S n)))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
       (Z.sub (Z.mul 4 8) 1) 0) : mword 32)
    with (trunc32 (sign_extend' 64 (subrange_vec_dec
          (add_vec (sign_extend' 64 (noff_val (S n)))
                   (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))).
  rewrite (pop_nv1_pred n Hb).
  rewrite trunc32_sext. reflexivity.
Qed.

Lemma pop_noff_pos (n : nat) : (Z.of_nat (S n) < 2^31)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (sign_extend' 64 (noff_val (S n))) = false.
Proof.
  intro Hb.
  unfold zopz0zKzJ_s.
  rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  unfold noff_val.
  rewrite sint64_moi32 by lia. lia.
Qed.

Lemma pop_nv1_zero_iff (n : nat) : (Z.of_nat (S n) < 2^31)%Z ->
  (neq_vec (sign_extend' 64 (subrange_vec_dec
     (add_vec (sign_extend' 64 (noff_val (S n)))
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
     (zero_reg : mword 64) = false <-> n = 0%nat).
Proof.
  intro Hb.
  rewrite (pop_nv1_pred n Hb).
  unfold neq_vec. rewrite negb_false_iff. rewrite eq_vec_true_iff.
  split.
  - intro Heq. apply (f_equal bv_unsigned) in Heq.
    unfold noff_val in Heq. rewrite sext64_moi32_unsigned in Heq by lia.
    change (bv_unsigned (zero_reg : mword 64)) with 0%Z in Heq. lia.
  - intros ->. apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma sie_bit1 (m : mword 64) :
  _get_Mstatus_SIE m = 'b"1" -> Z.testbit (bv_unsigned m) 1 = true.
Proof.
  intro HS.
  apply (f_equal bv_unsigned) in HS.
  unfold _get_Mstatus_SIE, subrange_vec_dec in HS.
  rewrite autocast_refl in HS.
  unfold to_word_idx, to_word, get_word in HS.
  rewrite MachineWord.MachineWord.cast_idx_refl in HS.
  unfold MachineWord.MachineWord.slice in HS.
  rewrite bv_extract_unsigned in HS.
  change (bv_unsigned ('b"1" : mword 1)) with 1%Z in HS.
  apply (f_equal (fun z => Z.testbit z 0)) in HS.
  change (Z.testbit 1 0) with true in HS.
  rewrite <- HS.
  unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N (MachineWord.MachineWord.Z_idx (1 - 1 + 1)))); [| vm_compute; reflexivity].
  rewrite Z.shiftr_spec; [| lia]. reflexivity.
Qed.

Require WpGprCsrwC.

Lemma sstatus_read_lower (ms : mword 64) : sstatus_read ms = lower_mstatus ms.
Proof. unfold sstatus_read. apply WpGprCsrwC.subrange_full. Qed.

Lemma land1_testbit0 (y : Z) : Z.land y 1 = Z.b2z (Z.testbit y 0).
Proof.
  replace 1%Z with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia. change (2^1)%Z with 2%Z.
  rewrite Z.bit0_odd. rewrite Zmod_odd.
  destruct (Z.odd y); reflexivity.
Qed.

Lemma po_intena_unsigned (ms : mword 64) :
  bv_unsigned (po_intena_val ms) = Z.b2z (Z.testbit (bv_unsigned (sstatus_read ms)) 1).
Proof.
  unfold po_intena_val.
  change (autocast (T := mword)
     (subrange_vec_dec
        (and_vec (shift_bits_right (sstatus_read ms)
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32)
    with (trunc32 (and_vec (shift_bits_right (sstatus_read ms)
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))).
  rewrite trunc32_unsigned.
  unfold and_vec, shift_bits_right, shiftr, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.and, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_and_unsigned. rewrite bv_shiftr_unsigned.
  match goal with |- context [Z.shiftr _ (bv_unsigned ?am)] =>
    replace (bv_unsigned am) with 1%Z by (vm_compute; reflexivity) end.
  match goal with |- context [Z.land _ (bv_unsigned ?mm)] =>
    replace (bv_unsigned mm) with 1%Z by (vm_compute; reflexivity) end.
  rewrite land1_testbit0.
  rewrite Z.shiftr_spec by lia. change (0 + 1)%Z with 1%Z.
  apply bvw32_small.
  destruct (Z.testbit (bv_unsigned (sstatus_read ms)) 1); simpl; lia.
Qed.

Lemma po_intena_val_bridge (ms : mword 64) (eb : bool) :
  _get_Mstatus_SIE ms = sie_bit eb -> po_intena_val ms = intena_val eb.
Proof.
  intro Hsie. apply bv_eq.
  rewrite po_intena_unsigned. rewrite sstatus_read_lower.
  assert (Hb1 : Z.testbit (bv_unsigned (lower_mstatus ms)) 1 = eb).
  { destruct eb.
    - apply sie_bit1. rewrite WpGprCsrwC.mSIE_lower. rewrite Hsie. reflexivity.
    - apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. rewrite Hsie. reflexivity. }
  rewrite Hb1.
  destruct eb; unfold intena_val; simpl Z.b2z.
  - rewrite (moi32_small 1) by lia. reflexivity.
  - rewrite (moi32_small 0) by lia. reflexivity.
Qed.

Lemma intena_val_zero (eb : bool) :
  eq_vec (sign_extend' 64 (intena_val eb)) (zero_reg : mword 64) = negb eb.
Proof. destruct eb; vm_compute; reflexivity. Qed.

(* WpIntenaBits.v: the pure intena-bit fact -- the value push_off stores
   (and pop_off reads back) as intena IS the SIE bit of the saved
   sstatus view.  Iris-free (vanilla rewrite scope): the testbit chase
   below relies on it. *)
Require Import SailStdpp.Operators_mwords SailStdpp.MachineWord SailStdpp.Values SailStdpp.TypeCasts.
From stdpp Require Import bitvector.definitions.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvExtras WpGprCsrwCommon WpGprCsrwC.
From Stdlib Require Import ZArith Lia.

(* the value the srli/andi chain computes from the saved sstatus view
   (spelled operationally, as the instructions compute it) *)
Definition po_intena_val (ms : mword 64) : mword 32 :=
  (autocast (T := mword)
     (subrange_vec_dec
        (and_vec (shift_bits_right (sstatus_read ms)
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32).

(* the value pop_off reads back as intena IS the SIE bit of the saved
   sstatus view -- the pure fact that converts push_off's ⌜SIE ms⌝-keyed
   payload into pop_off's intenav-keyed input disjunct. *)
Lemma po_intena_val_sie (ms : mword 64) :
  sign_extend' 64 (po_intena_val ms) = zero_extend' 64 (_get_Mstatus_SIE ms).
Proof.
  set (X := sstatus_read ms).
  assert (Hb2z : forall b : bool, (0 <= Z.b2z b < 2)%Z)
    by (intro b; destruct b; compute; split; congruence).
  assert (Hlt32 : (2 < 4294967296)%Z) by (vm_compute; reflexivity).
  assert (Hlt31 : (2 < 2147483648)%Z) by (vm_compute; reflexivity).
  assert (Hlt64 : (2 < 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (Hneg31 : (-2147483648 <= 0)%Z) by (compute; congruence).
  (* the 32-bit truncated value is bit 1 of the S-view, as a Z bit *)
  assert (Hinner : bv_unsigned (po_intena_val ms)
                   = Z.b2z (Z.testbit (bv_unsigned X) 1)).
  { unfold po_intena_val, trunc32.
    unfold subrange_vec_dec.
    rewrite !autocast_refl.
    unfold to_word_idx, to_word, get_word.
    rewrite !MachineWord.MachineWord.cast_idx_refl.
    unfold MachineWord.MachineWord.slice.
    rewrite bv_extract_unsigned.
    unfold and_vec, word_binop, with_word', SailStdpp.Values.with_word, to_word, get_word.
    unfold MachineWord.MachineWord.and.
    rewrite bv_and_unsigned.
    unfold riscv_extras.shift_bits_right, shiftr, with_word', SailStdpp.Values.with_word, to_word, get_word.
    unfold MachineWord.MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    match goal with
    | |- context [ Z.land ?a ?b ] =>
        assert (Hmask : b = 1%Z) by (vm_compute; reflexivity); rewrite Hmask
    end.
    match goal with
    | |- context [ Z.shiftr ?x ?sh ] =>
        assert (Hsh : sh = 1%Z) by (vm_compute; reflexivity); rewrite Hsh
    end.
    rewrite Z.shiftr_0_r.
    assert (Hl1 : forall y : Z, Z.land y 1 = Z.b2z (Z.testbit y 0)).
    { intro y.
      change (Z.land y 1) with (Z.land y (Z.ones 1)).
      rewrite Z.land_ones; [| compute; congruence].
      change (2 ^ 1)%Z with 2%Z. rewrite Zmod_odd. rewrite Z.bit0_odd.
      destruct (Z.odd y); reflexivity. }
    rewrite Hl1.
    rewrite Z.shiftr_spec; [| compute; congruence].
    change (0 + 1)%Z with 1%Z.
    match goal with
    | |- bv_wrap ?n ?z = _ =>
        assert (Hm32 : bv_modulus n = 4294967296%Z) by (vm_compute; reflexivity)
    end.
    rewrite bv_wrap_small;
      [ reflexivity
      | rewrite Hm32; destruct (Hb2z (Z.testbit (bv_unsigned X) 1)) as [Hb1 Hb2];
        split; [ exact Hb1 | eapply Z.lt_trans; [ exact Hb2 | exact Hlt32 ] ] ]. }
  apply bv_eq.
  (* outer: sext of a {0,1}-valued 32-bit word = the value *)
  unfold sign_extend', sign_extend, exts_vec.
  unfold zero_extend', zero_extend, extz_vec.
  unfold MachineWord.MachineWord.sign_extend, MachineWord.MachineWord.zero_extend.
  unfold to_word, get_word.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_zero_extend_unsigned; [| compute; congruence].
  unfold bv_signed. rewrite Hinner.
  match goal with
  | |- context [ bv_swrap ?n ?z ] =>
      assert (Hh32 : bv_half_modulus n = 2147483648%Z) by (vm_compute; reflexivity)
  end.
  rewrite bv_swrap_small;
    [| rewrite Hh32; destruct (Hb2z (Z.testbit (bv_unsigned X) 1)) as [Hb1 Hb2];
       split; [ eapply Z.le_trans; [ exact Hneg31 | exact Hb1 ]
              | eapply Z.lt_trans; [ exact Hb2 | exact Hlt31 ] ] ].
  match goal with
  | |- context [ bv_wrap ?n ?z ] =>
      assert (Hm64 : bv_modulus n = 18446744073709551616%Z) by (vm_compute; reflexivity)
  end.
  rewrite bv_wrap_small;
    [| rewrite Hm64; destruct (Hb2z (Z.testbit (bv_unsigned X) 1)) as [Hb1 Hb2];
       split; [ exact Hb1 | eapply Z.lt_trans; [ exact Hb2 | exact Hlt64 ] ] ].
  (* the SIE getter is bit 1 of the S-view *)
  rewrite <- (sSIE_lower ms).
  unfold _get_Sstatus_SIE.
  unfold subrange_vec_dec.
  rewrite !autocast_refl.
  unfold to_word_idx, to_word, get_word.
  rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  match goal with
  | |- context [ bv_wrap ?n ?z ] =>
      assert (Hm1 : bv_modulus n = 2%Z) by (vm_compute; reflexivity)
  end.
  unfold bv_wrap. rewrite Hm1. rewrite Zmod_odd.
  assert (HX : bv_unsigned X = bv_unsigned (lower_mstatus ms)).
  { unfold X, sstatus_read.
    unfold subrange_vec_dec.
    rewrite !autocast_refl.
    unfold to_word_idx, to_word, get_word.
    rewrite !MachineWord.MachineWord.cast_idx_refl.
    unfold MachineWord.MachineWord.slice.
    rewrite bv_extract_unsigned.
    rewrite Z.shiftr_0_r.
    apply bv_wrap_small. apply bv_unsigned_in_range. }
  rewrite HX.
  rewrite <- Z.bit0_odd.
  rewrite Z.shiftr_spec; [| compute; congruence].
  change (0 + Z.of_N (MachineWord.Z_idx 1))%Z with 1%Z.
  destruct (Z.testbit (bv_unsigned (lower_mstatus ms)) 1); reflexivity.
Qed.

(* AlignBits.v -- the alignment<->low-bits bridge lemmas, kept in a file with
   the MINIMAL import set (mirroring RiscvExtras) so the delicate bitvector
   unfold/rewrite chain reduces predictably.  Inside the big WpUser* import
   context the same script mis-reduces (extra instances/notations perturb how
   [eq_vec]/[slice]/[bv_extract] unfold), so this stays isolated and is
   [Require]d where needed. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* The CONVERSE of [align4_low_bits] (RiscvExtras.v): pc's low two bits both
   zero implies 4-byte alignment.  (bit0=0 => 2|pc, bit1=0 => 2|(pc/2), so
   4|pc.)  Used by the top-level [user_classify] to feed the 4-aligned branch's
   [is_aligned_vaddr .. 4 = true] premise from the pc case-split. *)
Lemma align4_of_low_bits (pc : mword 64) :
  neq_vec (access_vec_dec pc 0) ('b"0") = false ->
  neq_vec (access_vec_dec pc 1) ('b"0") = false ->
  is_aligned_vaddr (Virtaddr pc) 4 = true.
Proof.
  intros H0 H1.
  unfold neq_vec in H0, H1. rewrite negb_false_iff in H0, H1.
  unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word in H0, H1.
  rewrite MachineWord.MachineWord.eqb_true_iff in H0, H1.
  apply bv_eq in H0, H1.
  unfold MachineWord.slice in H0, H1.
  rewrite bv_extract_unsigned in H0, H1.
  replace (bv_unsigned ('b"0")) with 0%Z in H0 by (vm_compute; reflexivity).
  replace (bv_unsigned ('b"0")) with 0%Z in H1 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus in H0, H1.
  change (Z.of_N (MachineWord.Z_idx 0)) with 0%Z in H0.
  change (Z.of_N (MachineWord.Z_idx 1)) with 1%Z in H1.
  rewrite Z.shiftr_0_r in H0.
  rewrite Z.shiftr_div_pow2 in H1; [ | lia ].
  change (2 ^ Z.of_N 1)%Z with 2%Z in H0, H1.
  change (2 ^ 1)%Z with 2%Z in H1.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ pc) as Hr.
  rewrite Z.rem_mod_nonneg by lia.
  apply Z.mod_divide in H0; [| lia]. destruct H0 as [q0 Hq0].
  rewrite Hq0 in H1. rewrite Z.div_mul in H1; [| lia].
  apply Z.mod_divide in H1; [| lia]. destruct H1 as [q1 Hq1].
  rewrite Hq0, Hq1, <- Z.mul_assoc. change (2 * 2)%Z with 4%Z.
  apply Z.mod_mul. lia.
Qed.

(* A 2-aligned pc's bit 0 is already 0, so writing 0 there is the identity.
   ([sret_tgt] = [update_vec_dec _ 0 'b"0"], WpSmodeSret.v: every
   instruction-aligned pc is its own legal sret target -- lets the SIE=1
   engines derive their sret-target premise from [instr_bytes]' alignment
   fact instead of demanding it at every call site.) *)
Lemma update_bit0_zero_of_aligned2 (pc : mword 64) :
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  update_vec_dec pc 0 ('b"0") = pc.
Proof.
  intros H2.
  assert (Heven : Z.rem (bv_unsigned pc) 2 = 0).
  { unfold is_aligned_vaddr in H2. apply Z.eqb_eq in H2.
    rewrite uint_unsigned in H2. exact H2. }
  pose proof (bv_unsigned_in_range _ pc) as [Hlo Hhi].
  apply bv_eq.
  unfold update_vec_dec, update_mword_dec, MachineWord.update_slice.
  rewrite bv_concat_unsigned'.
  rewrite bv_concat_unsigned'.
  unfold MachineWord.slice.
  rewrite !bv_extract_unsigned.
  change (Z.of_N 0) with 0%Z.
  rewrite Z.shiftr_0_r.
  match goal with |- context [bv_wrap (MachineWord.Z_idx 0) ?z] =>
    replace (bv_wrap (MachineWord.Z_idx 0) z) with 0%Z
      by (unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N (MachineWord.Z_idx 0))%Z with 1%Z;
          rewrite Z.mod_1_r; reflexivity) end.
  match goal with |- context [Z.lor ?hi (bv_wrap ?w ?z)] =>
    replace (bv_wrap w z) with 0%Z by (vm_compute; reflexivity) end.
  rewrite Z.lor_0_r.
  change (Z.of_N (MachineWord.Z_idx 0 + MachineWord.Z_idx 1)) with 1%Z.
  change (MachineWord.Z_idx 64 - MachineWord.Z_idx 1 - MachineWord.Z_idx 0)%N with 63%N.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  assert (Hm64 : bv_modulus (MachineWord.Z_idx 64) = (2 ^ 64)%Z)
    by (vm_compute; reflexivity).
  assert (Hpow : (2 ^ 64)%Z = (2 * 2 ^ 63)%Z) by (vm_compute; reflexivity).
  rewrite Hm64 in Hhi.
  assert (Hdiv : (0 <= bv_unsigned pc / 2 < 2 ^ 63)%Z).
  { split; [ apply Z.div_pos; lia | ].
    apply Z.div_lt_upper_bound; [ lia | ]. lia. }
  rewrite (bv_wrap_small 63)
    by (replace (bv_modulus 63) with (2 ^ 63)%Z by (vm_compute; reflexivity); lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  pose proof (Z.div_mod (bv_unsigned pc) 2 ltac:(lia)) as Hdm.
  rewrite Z.rem_mod_nonneg in Heven by lia.
  rewrite bv_wrap_small; [ lia | rewrite Hm64; lia ].
Qed.

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

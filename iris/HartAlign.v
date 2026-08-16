(* HartAlign.v -- the two bit-level address facts the 2-mod-4 fetch needs.

   Their proofs reach into the machine-word representation, which needs
   [SailStdpp.Base]; that module's [read_kind] SHADOWS the model's, so
   importing it into [HartMFetch] breaks every [Read_plain] there.  Hence a
   file of its own: the import stays contained and the consumers see only
   the two statements. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvExtras.
Local Open Scope Z_scope.

Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Lemma access1_unsigned_gen (n : Z) (w : SailStdpp.Values.mword n) :
  bv_unsigned (access_vec_dec w 1) = (bv_unsigned w / 2) mod 2.
Proof.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice. cbv [get_word].
  rewrite bv_extract_unsigned.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  reflexivity.
Qed.

(* PC bit 1 SET means the address is not 4-aligned -- which is what makes
   the model's 4-alignment [and_boolM] short-circuit to false before
   [Ext_Ziccif] on the 2-mod-4 fetch path. *)
Lemma mf_align4_false (pc : SailStdpp.Values.mword 64) :
  neq_vec (access_vec_dec pc 1) zerobit = true ->
  is_aligned_vaddr (Virtaddr pc) 4 = false.
Proof.
  intros Hb1.
  assert (Hne : bv_unsigned (access_vec_dec pc 1) <> 0).
  { intro Hz.
    assert (Heq : access_vec_dec pc 1 = zerobit)
      by (apply bv_eq; rewrite Hz; vm_compute; reflexivity).
    rewrite Heq in Hb1. vm_compute in Hb1. discriminate Hb1. }
  rewrite access1_unsigned_gen in Hne.
  unfold is_aligned_vaddr. apply Z.eqb_neq. rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ pc) as Hr. destruct Hr as [Hr0 _].
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned pc / 2) 2 ltac:(lia)) as Hh.
  pose proof (Z.div_mod (bv_unsigned pc / 2) 2 ltac:(lia)) as Hd4.
  pose proof (Z.div_mod (bv_unsigned pc) 2 ltac:(lia)) as Hd2.
  pose proof (Z.mod_pos_bound (bv_unsigned pc) 2 ltac:(lia)) as Hb2.
  pose proof (Z.div_mod (bv_unsigned pc) 4 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned pc) 4 ltac:(lia)) as Hbm.
  assert (Hdd : bv_unsigned pc / 4 = (bv_unsigned pc / 2) / 2)
    by (rewrite Zdiv_Zdiv by lia; reflexivity).
  lia.
Qed.

(* UserBits.v -- page-window bitvector arithmetic for the user-mode memory
   layer, kept in a MINIMAL-import file (the AlignBits convention: inside
   the heavy WP import contexts the delicate bv unfold chains mis-reduce).

   The payoff lemma is [pa_window]: adding a small offset to a translated
   physical address [zext64 (concat ppn (va's page offset))] stays on the
   page and equals the translation of [va + j] -- the bridge from
   [upt_data_cov] (which covers every translated address) to the per-byte
   facts memory reads and writes need.                                    *)
From Stdlib Require Import ZArith Bool Lia Znumtheory.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvExtras KptPt.
Local Open Scope Z_scope.

(* [uint] is [bv_unsigned] at every width (RiscvExtras' [uint_unsigned]
   is 64-bit-specific) *)
Lemma uint_unsigned_n (n : Z) (a : mword n) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

(* the low 12 bits of a 64-bit word, as unsigned arithmetic *)
Lemma uint_subrange11 (x : mword 64) :
  uint (subrange_vec_dec x 11 0) = (uint x) mod 4096.
Proof.
  rewrite !(uint_unsigned_n _).
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx (11 - 0 + 1))) with 4096.
  reflexivity.
Qed.

(* a (possibly wrapping) 64-bit add acts modularly on the page offset *)
Lemma uint_add_vec_int_mod4096 (va : mword 64) (j : Z) :
  0 <= j < 4096 ->
  (uint (add_vec_int va j)) mod 4096 = (uint va + j) mod 4096.
Proof.
  intro Hj.
  rewrite !uint_unsigned.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 64) = j).
  { unfold mword_of_int, Values.to_word, get_word.
    cbn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. cbn. lia. }
  rewrite Hjv.
  unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
  rewrite <- Znumtheory.Zmod_div_mod; [ reflexivity | lia | lia | ].
  exists 4503599627370496. reflexivity.
Qed.

(* a non-wrapping 64-bit add, as unsigned arithmetic *)
Lemma uint_add_vec_int_small (a : mword 64) (j : Z) :
  0 <= j ->
  bv_unsigned a + j < 18446744073709551616 ->
  bv_unsigned (add_vec_int a j) = bv_unsigned a + j.
Proof.
  intros Hj Hfit.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 64) = j).
  { unfold mword_of_int, Values.to_word, get_word.
    cbn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. cbn.
    pose proof (bv_unsigned_in_range _ a). lia. }
  rewrite Hjv.
  apply bv_wrap_small.
  unfold bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hr.
  lia.
Qed.

(* bv_unsigned forms of the two offset lemmas (robust rewrite targets) *)
Lemma bv_subrange11 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 11 0) = (bv_unsigned x) mod 4096.
Proof.
  pose proof (uint_subrange11 x) as H.
  rewrite !(uint_unsigned_n _) in H. exact H.
Qed.

Lemma bv_add_mod4096 (va : mword 64) (j : Z) :
  0 <= j < 4096 ->
  (bv_unsigned (add_vec_int va j)) mod 4096 = (bv_unsigned va + j) mod 4096.
Proof.
  intro Hj.
  pose proof (uint_add_vec_int_mod4096 va j Hj) as H.
  rewrite !(uint_unsigned_n _) in H. exact H.
Qed.

(* a 4-aligned va's page offset leaves room for the 4-byte window *)
Lemma off4_bound (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  uint (subrange_vec_dec va 11 0) + 4 <= 4096.
Proof.
  intro Hal.
  unfold is_aligned_vaddr in Hal. apply Z.eqb_eq in Hal.
  rewrite uint_subrange11.
  rewrite !(uint_unsigned_n _) in Hal |- *.
  pose proof (bv_unsigned_in_range _ va) as Hr.
  rewrite Z.rem_mod_nonneg in Hal by lia.
  assert (Hoff4 : (bv_unsigned va mod 4096) mod 4 = 0).
  { rewrite <- Znumtheory.Zmod_div_mod; [ exact Hal | lia | lia | ].
    exists 1024. reflexivity. }
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hb.
  apply Z.mod_divide in Hoff4; [ | lia ]. destruct Hoff4 as [q Hq].
  lia.
Qed.

(* THE page-window lemma: within the page, translated addresses add *)
Lemma pa_window (p : mword 44) (va : mword 64) (j : nat) :
  uint (subrange_vec_dec va 11 0) + Z.of_nat j < 4096 ->
  pa_add (zero_extend' 64 (concat_vec p (subrange_vec_dec va 11 0))) j
  = zero_extend' 64 (concat_vec p (subrange_vec_dec (add_vec_int va (Z.of_nat j)) 11 0)).
Proof.
  intro Hfit.
  pose proof (bv_unsigned_in_range _ p) as Hp. unfold bv_modulus in Hp.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 17592186044416 in Hp.
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hoffb.
  rewrite (uint_unsigned_n _) in Hfit.
  rewrite bv_subrange11 in Hfit.
  apply bv_eq.
  assert (Hlhs : bv_unsigned (pa_add (zero_extend' 64 (concat_vec p (subrange_vec_dec va 11 0))) j)
                 = bv_unsigned p * 4096 + (bv_unsigned va) mod 4096 + Z.of_nat j).
  { unfold pa_add.
    match goal with |- bv_unsigned (add_vec_int ?A _) = _ =>
      assert (HA : bv_unsigned A = bv_unsigned p * 4096 + (bv_unsigned va) mod 4096) end.
    { rewrite zext64_concat44_12_unsigned.
      rewrite bv_subrange11. reflexivity. }
    pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hb'.
    rewrite uint_add_vec_int_small; [ | lia | rewrite HA; lia ].
    rewrite HA. lia. }
  assert (Hrhs : bv_unsigned (zero_extend' 64 (concat_vec p
                    (subrange_vec_dec (add_vec_int va (Z.of_nat j)) 11 0)))
                 = bv_unsigned p * 4096 + ((bv_unsigned va) mod 4096 + Z.of_nat j)).
  { etransitivity; [ exact (zext64_concat44_12_unsigned p _) | ].
    f_equal.
    etransitivity; [ exact (bv_subrange11 (add_vec_int va (Z.of_nat j))) | ].
    etransitivity; [ exact (bv_add_mod4096 va (Z.of_nat j) ltac:(lia)) | ].
    pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hb2.
    rewrite <- Z.add_mod_idemp_l; [ | lia ].
    rewrite Z.mod_small; [ reflexivity | lia ]. }
  etransitivity; [ exact Hlhs | ].
  symmetry.
  etransitivity; [ exact Hrhs | ].
  lia.
Qed.

(* ===================================================================== *)
(* little-endian words built from bytes reproduce those bytes (the        *)
(* width-4/2 clones of KallocInv's width-8 [nth_byte_assemble8]) -- how a *)
(* fetched word is conjured from the EXISTENTIAL page contents            *)
(* ===================================================================== *)
Lemma nth_byte_assemble4 (bs : list (bv 8)) (j : nat) :
  length bs = 4%nat -> (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (assemble_bytes bs) : mword 32) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 32 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

Lemma nth_byte_assemble2 (bs : list (bv 8)) (j : nat) :
  length bs = 2%nat -> (j < 2)%nat ->
  nth_byte (Z_to_bv 16 (assemble_bytes bs) : mword 16) j = bs !!! j.
Proof.
  intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
  rewrite Z_to_bv_unsigned.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
  assert (Hws : bv_wrap 16 (assemble_bytes bs) = assemble_bytes bs).
  { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite Hws.
  assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
    by (apply assemble_bytes_byte; lia).
  rewrite <- Hab.
  f_equal. f_equal. lia.
Qed.

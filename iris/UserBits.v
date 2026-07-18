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

(* a 4-aligned va translates to a 4-aligned pa (the page offset carries
   the low bits) *)
Lemma pa4_aligned (p : mword 44) (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  is_aligned_paddr (Physaddr (zero_extend' 64
    (concat_vec p (subrange_vec_dec va 11 0)))) 4 = true.
Proof.
  intro Hal.
  unfold is_aligned_vaddr in Hal. apply Z.eqb_eq in Hal.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite !(uint_unsigned_n _) in Hal |- *.
  pose proof (bv_unsigned_in_range _ va) as Hr.
  rewrite Z.rem_mod_nonneg in Hal by lia.
  rewrite zext64_concat44_12_unsigned.
  rewrite bv_subrange11.
  pose proof (bv_unsigned_in_range _ p) as Hp.
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)) as Hb.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite <- Z.add_mod_idemp_l by lia.
  replace ((bv_unsigned p * 4096) mod 4) with 0.
  2:{ symmetry. apply Z.mod_divide; [ lia | ].
      exists (bv_unsigned p * 1024). lia. }
  rewrite Z.add_0_l.
  rewrite <- Znumtheory.Zmod_div_mod; [ | lia | lia | exists 1024; reflexivity ].
  exact Hal.
Qed.

(* ===================================================================== *)
(* Decode-wf bit facts: the JAL / BTYPE decoders build their immediates   *)
(* as [concat_vec imm ('b"0")], so bit 0 is the literal low bit.  These   *)
(* discharge the strengthened [decodable_u] leaf checks (DecodeSetU.v).   *)
(* ===================================================================== *)

Lemma bit0_concat0_20 (x : mword 20) :
  eq_vec (access_vec_dec (concat_vec x ('b"0" : mword 1)) 0) ('b"0") = true.
Proof.
  apply eq_vec_true_iff.
  apply bv_eq.
  unfold access_vec_dec, access_mword_dec, concat_vec.
  cbv [to_word get_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (20 + 1)) (20 + 1)) as [e2 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e2)).
  unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice, MachineWord.MachineWord.concat, Values.to_word.
  rewrite bv_extract_unsigned.
  erewrite bv_concat_unsigned by (cbn; lia).
  cbn.
  rewrite Z.shiftr_0_r.
  rewrite Z.lor_0_r.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_wrap, bv_modulus.
  change (2 ^ 1) with 2.
  change (2 ^ Z.of_N 1) with 2.
  rewrite Z_mod_mult.
  vm_compute; reflexivity.
Qed.

Lemma bit0_concat0_12 (x : mword 12) :
  eq_vec (access_vec_dec (concat_vec x ('b"0" : mword 1)) 0) ('b"0") = true.
Proof.
  apply eq_vec_true_iff.
  apply bv_eq.
  unfold access_vec_dec, access_mword_dec, concat_vec.
  cbv [to_word get_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (12 + 1)) (12 + 1)) as [e2 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e2)).
  unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice, MachineWord.MachineWord.concat, Values.to_word.
  rewrite bv_extract_unsigned.
  erewrite bv_concat_unsigned by (cbn; lia).
  cbn.
  rewrite Z.shiftr_0_r.
  rewrite Z.lor_0_r.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_wrap, bv_modulus.
  change (2 ^ 1) with 2.
  change (2 ^ Z.of_N 1) with 2.
  rewrite Z_mod_mult.
  vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* Decode-wf TRANSPORT: turn the recorded JAL/BTYPE immediate-evenness    *)
(* and the fetch alignment into [jump_to]'s target-bit-0 premise.         *)
(*   wf_imm_even_{21,13}   : the decodable_u payload fact, as mod-2       *)
(*   aligned_even          : a fetched pc is even (align check at 2 or 4) *)
(*   add_sext_even_64_{21,13} : even pc + sign-extended even imm has      *)
(*                              bit 0 clear -- exactly jump_to's assert.  *)
(* ===================================================================== *)
(* mod-2 helpers *)
Lemma mod2_wrap (n : N) (z : Z) :
  (1 <= Z.of_N n)%Z ->
  bv_wrap n z mod 2 = z mod 2.
Proof.
  intro Hn. unfold bv_wrap, bv_modulus.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | | ].
  - apply Z.pow_pos_nonneg; lia.
  - exists (2 ^ (Z.of_N n - 1)).
    rewrite Z.mul_comm.
    rewrite <- Z.pow_succ_r by lia. f_equal. lia.
Qed.

Lemma mod2_swrap (n : N) (z : Z) :
  (2 <= Z.of_N n)%Z ->
  bv_swrap n z mod 2 = z mod 2.
Proof.
  intro Hn. unfold bv_swrap.
  set (E := bv_half_modulus n) in *.
  assert (Hpow : 2 ^ Z.of_N n = 2 ^ (Z.of_N n - 1) * 2).
  { rewrite Z.mul_comm. rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (HE : E mod 2 = 0).
  { unfold E, bv_half_modulus, bv_modulus.
    rewrite Hpow. rewrite Z_div_mult by lia.
    apply Z.mod_divide; [lia|].
    exists (2 ^ (Z.of_N n - 1 - 1)).
    rewrite Z.mul_comm.
    rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  rewrite Zminus_mod.
  rewrite mod2_wrap by lia.
  rewrite HE. rewrite Z.sub_0_r.
  rewrite Zmod_mod.
  rewrite Zplus_mod, HE, Z.add_0_r.
  rewrite !Zmod_mod.
  reflexivity.
Qed.

(* bit 0 of a 64-bit word, as unsigned arithmetic *)
Lemma access0_unsigned_64 (w : mword 64) :
  bv_unsigned (access_vec_dec w 0) = bv_unsigned w mod 2.
Proof.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice.
  cbv [get_word].
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  reflexivity.
Qed.

Lemma access0_unsigned_21 (w : mword 21) :
  bv_unsigned (access_vec_dec w 0) = bv_unsigned w mod 2.
Proof.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice.
  cbv [get_word].
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  reflexivity.
Qed.

Lemma access0_unsigned_13 (w : mword 13) :
  bv_unsigned (access_vec_dec w 0) = bv_unsigned w mod 2.
Proof.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice.
  cbv [get_word].
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  reflexivity.
Qed.

(* the JAL/BTYPE decode-wf fact, read back as evenness *)
Lemma wf_imm_even_21 (imm : mword 21) :
  eq_vec (access_vec_dec imm 0) ('b"0") = true ->
  bv_unsigned imm mod 2 = 0.
Proof.
  intro H. apply eq_vec_true_iff in H.
  apply (f_equal bv_unsigned) in H.
  rewrite access0_unsigned_21 in H. rewrite H.
  vm_compute; reflexivity.
Qed.

Lemma wf_imm_even_13 (imm : mword 13) :
  eq_vec (access_vec_dec imm 0) ('b"0") = true ->
  bv_unsigned imm mod 2 = 0.
Proof.
  intro H. apply eq_vec_true_iff in H.
  apply (f_equal bv_unsigned) in H.
  rewrite access0_unsigned_13 in H. rewrite H.
  vm_compute; reflexivity.
Qed.

(* an even 64-bit sum: pc + sign_extend' imm, both even *)
Lemma add_sext_even_64_21 (pc : mword 64) (imm : mword 21) :
  bv_unsigned pc mod 2 = 0 ->
  bv_unsigned imm mod 2 = 0 ->
  eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true.
Proof.
  intros Hpc Himm.
  apply eq_vec_true_iff. apply bv_eq.
  rewrite access0_unsigned_64.
  unfold add_vec, word_binop, with_word', to_word, get_word.
  unfold SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  rewrite mod2_wrap by (cbn; lia).
  unfold sign_extend', Operators_mwords.sign_extend, exts_vec, to_word, get_word.
  unfold MachineWord.MachineWord.sign_extend, Values.to_word.
  rewrite bv_sign_extend_unsigned.
  rewrite Zplus_mod.
  rewrite mod2_wrap by (cbn; lia).
  unfold bv_signed.
  rewrite mod2_swrap by (cbn; lia).
  rewrite Hpc, Himm.
  vm_compute; reflexivity.
Qed.

Lemma add_sext_even_64_13 (pc : mword 64) (imm : mword 13) :
  bv_unsigned pc mod 2 = 0 ->
  bv_unsigned imm mod 2 = 0 ->
  eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true.
Proof.
  intros Hpc Himm.
  apply eq_vec_true_iff. apply bv_eq.
  rewrite access0_unsigned_64.
  unfold add_vec, word_binop, with_word', to_word, get_word.
  unfold SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  rewrite mod2_wrap by (cbn; lia).
  unfold sign_extend', Operators_mwords.sign_extend, exts_vec, to_word, get_word.
  unfold MachineWord.MachineWord.sign_extend, Values.to_word.
  rewrite bv_sign_extend_unsigned.
  rewrite Zplus_mod.
  rewrite mod2_wrap by (cbn; lia).
  unfold bv_signed.
  rewrite mod2_swrap by (cbn; lia).
  rewrite Hpc, Himm.
  vm_compute; reflexivity.
Qed.

(* a fetched pc is even: the fetch alignment check passed at width 2 or 4 *)
Lemma aligned_even (va : mword 64) (w : Z) :
  (2 | w) -> 0 < w ->
  is_aligned_vaddr (Virtaddr va) w = true ->
  bv_unsigned va mod 2 = 0.
Proof.
  intros Hdvd Hw Hal.
  unfold is_aligned_vaddr in Hal. apply Z.eqb_eq in Hal.
  rewrite (uint_unsigned_n _) in Hal.
  rewrite Z.rem_mod_nonneg in Hal; [ | apply bv_unsigned_in_range | lia ].
  rewrite (Znumtheory.Zmod_div_mod 2 w) by (assumption || lia).
  rewrite Hal. reflexivity.
Qed.

(* JALR's cleared target: bit 0 of [update_vec_dec t 0 'b"0"] is 0 --
   [update_slice] at bit 0 is a nested [bv_concat] whose low limb is the
   written literal, so parity is the low limb's.                          *)
Lemma even_lor (a b : Z) : a mod 2 = 0 -> b mod 2 = 0 -> Z.lor a b mod 2 = 0.
Proof.
  intros Ha Hb.
  rewrite Zmod_odd in *.
  destruct (Z.odd (Z.lor a b)) eqn:E; [ | reflexivity ].
  rewrite <- Z.bit0_odd in E. rewrite Z.lor_spec in E.
  rewrite !Z.bit0_odd in E.
  destruct (Z.odd a); destruct (Z.odd b); simpl in E; congruence.
Qed.

Lemma even_shiftl1 (a : Z) : Z.shiftl a 1 mod 2 = 0.
Proof.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2. apply Z_mod_mult.
Qed.

Lemma bit0_update0_64 (t : mword 64) :
  eq_vec (access_vec_dec (update_vec_dec t 0 ('b"0")) 0) ('b"0") = true.
Proof.
  apply eq_vec_true_iff. apply bv_eq.
  rewrite access0_unsigned_64.
  unfold update_vec_dec, update_mword_dec.
  unfold MachineWord.MachineWord.update_slice.
  erewrite bv_concat_unsigned by (cbn; lia).
  match goal with
  | |- Z.lor (Z.shiftl _ ?w) _ mod 2 = _ =>
      replace w with 1 by (vm_compute; reflexivity)
  end.
  match goal with
  | |- Z.lor ?a ?b mod 2 = ?rhs =>
      replace rhs with 0 by (vm_compute; reflexivity)
  end.
  apply even_lor; [ apply even_shiftl1 | ].
  erewrite bv_concat_unsigned by (cbn; lia).
  apply even_lor.
  - rewrite Z.shiftl_mul_pow2 by lia.
    match goal with
    | |- (?a * ?b) mod 2 = 0 =>
        replace a with 0 by (vm_compute; reflexivity)
    end.
    reflexivity.
  - cbn.
    match goal with
    | |- bv_unsigned ?x mod 2 = 0 =>
        pose proof (bv_unsigned_in_range _ x) as Hr;
        unfold bv_modulus in Hr; cbn in Hr;
        change (2 ^ 0) with 1 in Hr;
        replace (bv_unsigned x) with 0 by lia;
        reflexivity
    end.
Qed.

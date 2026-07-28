(* PrintintArith.v -- the pure arithmetic printint's two loops run on.

   Kept OUT of the WP file, and deliberately with ByteCursor's minimal import
   set (no iris, no [bitvector.tactics]): the zify hook those bring makes [lia]
   answer "Cannot find witness" on goals that merely mention a [bv_unsigned],
   which is most of what is below.  That is the same reason ByteCursor.v
   restates its two [add_vec] identities locally, and why durable-notes.md says
   to factor arithmetic into [mword]-free helpers.

   Four groups:
   - [tbt64] / [tbt_moi]: the value DIVU/REMU write.  The model computes the
     quotient/remainder over Z and truncates ([to_bits_truncate]), so a call
     site that knows its operands turns that back into a literal [mword_of_int].
   - [sextw_moi] / [addiw_lit]: the 32-bit add-immediate + sign-extend
     round-trip ([addiw], [c.addiw]) is the identity on a small nonnegative
     index -- printint's [i] counter.
   - [digit_step]: the do-while's progress and, with it, the BUFFER BOUND.  One
     base-[b] digit falls off [x] per iteration once [b >= 10], so a bound of
     [10^f] on the value bounds the remaining iterations by [f]; that is what
     keeps the loop's writes inside [buf].
   - [pa_add_neq_base]: the print loop's descending cursor meets its [base-1]
     sentinel exactly when it has walked off the front.  No no-wrap assumption,
     as in [ByteCursor.pa_add_cmp_bound]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import ByteCursor.
Require Import StackOwn.
Local Open Scope Z_scope.

(* [autocast] is the identity -- restated locally, as with the two above *)
Lemma pi_autocast_id (m : Z) (x : mword m) : autocast x = x.
Proof. apply autocast_refl. Qed.

(* restated locally (as ByteCursor does) so this file needs no heavy import *)
Lemma pi_uint_unsigned (a : mword 64) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Lemma moi64_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 64) = z `mod` 18446744073709551616.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma sint_moi_small (z : Z) : (0 <= z < 2^63)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  assert (Hu : bv_unsigned (mword_of_int z : mword 64) = z).
  { rewrite moi64_unsigned. apply Z.mod_small.
    change 18446744073709551616 with (2^64) in *. lia. }
  rewrite Hu. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

(* [lia] cannot evaluate [2^n]; give it the literals first. *)
Ltac zlit :=
  try change (2^31) with 2147483648 in *;
  try change (2^32) with 4294967296 in *;
  try change (2^63) with 9223372036854775808 in *;
  try change (2^64) with 18446744073709551616 in *;
  lia.



Lemma sub64_63 (x : mword (0+64-1+1)) :
  bv_unsigned (subrange_vec_dec x (0+64-1) 0) = bv_unsigned x `mod` 2^64.
Proof.
  unfold subrange_vec_dec. rewrite pi_autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (0+64-1-0+1)) with 64%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). reflexivity.
Qed.

Lemma gsi64 (N : Z) : bv_unsigned (get_slice_int 64 N 0 : mword 64) = N `mod` 2^64.
Proof.
  rewrite get_slice_int_eta. unfold get_slice_int'.
  replace (64 >=? 0) with true by reflexivity. cbn [sumbool_of_bool].
  rewrite pi_autocast_id. rewrite sub64_63.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx (0+64-1+1)) = 2^64) as -> by (vm_compute; reflexivity).
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma tbt64 (N : Z) : uint (to_bits_truncate 64 N : mword 64) = N `mod` 2^64.
Proof. rewrite pi_uint_unsigned. unfold to_bits_truncate. apply gsi64. Qed.

(* ---- small-value mword arithmetic ---- *)

Lemma moi_add (a b : Z) :
  add_vec (mword_of_int a : mword 64) (mword_of_int b) = mword_of_int (a + b).
Proof.
  apply bv_eq.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. rewrite !moi64_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma sub64_31 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 31 0 : mword 32) = bv_unsigned x `mod` 2^32.
Proof.
  unfold subrange_vec_dec. rewrite pi_autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (31-0+1)) with 32%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). reflexivity.
Qed.

Lemma sext32_64_small (k : Z) : 0 <= k < 2^31 ->
  sign_extend' 64 (mword_of_int k : mword 32) = (mword_of_int k : mword 64).
Proof.
  intro Hk. apply bv_eq.
  unfold sign_extend', Operators_mwords.sign_extend, Operators_mwords.exts_vec,
    SailStdpp.Values.to_word, to_word, get_word, MachineWord.MachineWord.sign_extend.
  rewrite bv_sign_extend_unsigned.
  assert (Hu : bv_unsigned (mword_of_int k : mword 32) = k).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus (MachineWord.MachineWord.Z_idx 32)) with (2^32). zlit. }
  assert (Hs : bv_signed (mword_of_int k : mword 32) = k).
  { unfold bv_signed, bv_swrap. rewrite Hu.
    change (bv_half_modulus (MachineWord.MachineWord.Z_idx 32)) with (2^31).
    unfold bv_wrap. change (bv_modulus (MachineWord.MachineWord.Z_idx 32)) with (2^32).
    rewrite (Z.mod_small (k + 2^31) (2^32) ltac:(zlit)). zlit. }
  rewrite Hs. rewrite moi64_unsigned.
  unfold bv_wrap. change (bv_modulus _) with 18446744073709551616. reflexivity.
Qed.

Lemma sextw_moi (k : Z) : 0 <= k < 2^31 ->
  sign_extend' 64 (subrange_vec_dec (mword_of_int k : mword 64) 31 0) = mword_of_int k.
Proof.
  intro Hk.
  assert (Hsub : subrange_vec_dec (mword_of_int k : mword 64) 31 0 = (mword_of_int k : mword 32)).
  { apply bv_eq. rewrite sub64_31, moi64_unsigned.
    unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus (MachineWord.MachineWord.Z_idx 32)) with 4294967296.
    change 18446744073709551616 with (2^64). change (2^32) with 4294967296.
    rewrite (Z.mod_small k (2^64) ltac:(zlit)). reflexivity. }
  rewrite Hsub. apply sext32_64_small. exact Hk.
Qed.

(* ---- the value the leaves write, as a literal ---- *)
Lemma tbt_moi (N : Z) : to_bits_truncate 64 N = (mword_of_int N : mword 64).
Proof.
  apply bv_eq. rewrite <- (pi_uint_unsigned (to_bits_truncate 64 N)), <- (pi_uint_unsigned (mword_of_int N)).
  rewrite tbt64, pi_uint_unsigned, moi64_unsigned.
  change 18446744073709551616 with (2^64). reflexivity.
Qed.

(* addiw rd,rs,c on a small value: the 32-bit add + sign-extend round-trips *)
Lemma addiw_lit (k c : Z) (e : mword 64) :
  e = mword_of_int c -> 0 <= k + c < 2^31 ->
  sign_extend' 64 (subrange_vec_dec (add_vec (mword_of_int k : mword 64) e) 31 0)
  = mword_of_int (k + c).
Proof. intros -> H. rewrite moi_add. apply sextw_moi. exact H. Qed.

(* the do-while's progress: one base-[b] digit falls off [x] each iteration, so
   a bound of [10^f] on the value bounds the remaining digits by [f]. *)
Lemma digit_step (x b : Z) (f : nat) :
  0 <= x -> 10 <= b -> b <= x -> x < 10^(Z.of_nat f) ->
  (1 <= f)%nat /\ Z.quot x b < 10^(Z.of_nat (f-1)).
Proof.
  intros Hx Hb Hbx Hf.
  assert (Hf1 : (1 <= f)%nat).
  { destruct f as [|f']; [ | lia ].
    change (Z.of_nat 0) with 0 in Hf. rewrite Z.pow_0_r in Hf. lia. }
  split; [exact Hf1 | ].
  assert (Hfe : Z.of_nat f = Z.of_nat (f - 1) + 1) by lia.
  rewrite Hfe in Hf. rewrite Z.pow_add_r in Hf; [ | lia | lia ].
  rewrite Z.pow_1_r in Hf.
  assert (Hpos : 0 < 10^(Z.of_nat (f-1))) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.quot_div_nonneg; [ | lia | lia ].
  apply Z.div_lt_upper_bound; [ lia | ].
  apply (Z.lt_le_trans _ (10^(Z.of_nat (f-1)) * 10)); [ exact Hf | ].
  rewrite Z.mul_comm. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

(* the print loop's end-pointer compare: the descending cursor equals the
   sentinel [base-1] exactly when it has walked off the front. *)
Lemma pa_add_neq_base (p : mword 64) (j : nat) :
  Z.of_nat j < 2^64 ->
  neq_vec (add_vec (pa_add p j) (mword_of_int (-1) : mword 64))
          (add_vec p (mword_of_int (-1))) = negb (Nat.eqb j 0).
Proof.
  intro Hj.
  assert (Hmod64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E64 in Hj.
  assert (HxL : bv_unsigned (add_vec (pa_add p j) (mword_of_int (-1) : mword 64) : mword 64)
              = bv_wrap 64 (bv_unsigned p + Z.of_nat j + (-1))).
  { unfold pa_add, add_vec_int.
    rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap_add_idemp_l.
    (* the remaining inner wrap sits in the MIDDLE of the sum; rotate it to the
       right so [bv_wrap_add_idemp_r] can absorb it *)
    replace (bv_unsigned p + bv_wrap 64 (Z.of_nat j) + -1)
      with (bv_unsigned p + -1 + bv_wrap 64 (Z.of_nat j)) by ring.
    rewrite bv_wrap_add_idemp_r. f_equal. ring. }
  assert (HeL : bv_unsigned (add_vec p (mword_of_int (-1) : mword 64) : mword 64)
              = bv_wrap 64 (bv_unsigned p + (-1))).
  { rewrite bc_add_vec_unsigned, bc_moi_unsigned. rewrite bv_wrap_add_idemp_r. reflexivity. }
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec j 0) as [He | Hne].
  - apply eq_vec_true_iff. apply bv_eq. rewrite HxL, HeL, He.
    change (Z.of_nat 0) with 0. f_equal. ring.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite HxL, HeL in Hc. unfold bv_wrap in Hc.
    assert (Hd : (((bv_unsigned p + Z.of_nat j + (-1)) - (bv_unsigned p + (-1)))
                    mod bv_modulus 64 = 0)%Z).
    { rewrite Zminus_mod. rewrite Hc. rewrite Z.sub_diag. apply Zmod_0_l. }
    replace ((bv_unsigned p + Z.of_nat j + (-1)) - (bv_unsigned p + (-1)))%Z
      with (Z.of_nat j)%Z in Hd by ring.
    rewrite Z.mod_small in Hd;
      [ apply Hne; change 0%Z with (Z.of_nat 0) in Hd; exact (Nat2Z.inj _ _ Hd)
      | rewrite Hmod64; split; [ apply Nat2Z.is_nonneg | exact Hj ] ].
Qed.

Lemma uint_moi_small (k : Z) : 0 <= k < 2^64 -> uint (mword_of_int k : mword 64) = k.
Proof.
  intro Hk. rewrite pi_uint_unsigned, moi64_unsigned. apply Z.mod_small.
  change 18446744073709551616 with (2^64). exact Hk.
Qed.

Lemma moi_uint (r : mword 64) : mword_of_int (uint r) = r.
Proof.
  apply bv_eq. rewrite moi64_unsigned, pi_uint_unsigned. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 r) as Hr.
  assert (Hm : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Hm in Hr. exact Hr.
Qed.

(* the [digits] table access: [add] of an offset VALUE to a base address is the
   base address at that byte index, which is how the caller's per-byte
   [kernel_data] window is indexed. *)
Lemma add_vec_pa_add (D r : mword 64) :
  add_vec r D = pa_add D (Z.to_nat (uint r)).
Proof.
  unfold pa_add, add_vec_int.
  rewrite add_vec_comm. f_equal.
  rewrite Z2Nat.id; [ symmetry; apply moi_uint | ].
  rewrite pi_uint_unsigned. apply (bv_unsigned_in_range 64 r).
Qed.

(* [zero_reg] is a left identity for [add_vec] -- the value every [c.mv] writes.
   (The right-identity twin is [RiscvExtras.kv_addv_zero].) *)
Lemma pi_addv_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite bv_add_unsigned.
  change (bv_unsigned zero_reg) with 0.
  rewrite Z.add_0_l. apply bv_wrap_bv_unsigned.
Qed.

Lemma pi_uint_nonneg (x : mword 64) : 0 <= uint x.
Proof. rewrite pi_uint_unsigned. apply (bv_unsigned_in_range 64 x). Qed.

Lemma pi_uint_lt64 (x : mword 64) : uint x < 2^64.
Proof.
  rewrite pi_uint_unsigned.
  pose proof (bv_unsigned_in_range 64 x) as Hr.
  assert (Hm : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Hm in Hr. change (2^64) with 18446744073709551616. exact (proj2 Hr).
Qed.

Lemma quot_nonneg (a b : Z) : 0 <= a -> 1 <= b -> 0 <= Z.quot a b.
Proof. intros Ha Hb. rewrite Z.quot_div_nonneg; [ | lia | lia ]. apply Z.div_pos; lia. Qed.

Lemma quot_le_self (a b : Z) : 0 <= a -> 1 <= b -> Z.quot a b <= a.
Proof.
  intros Ha Hb. rewrite Z.quot_div_nonneg; [ | lia | lia ].
  apply Z.div_le_upper_bound; [ lia | nia ].
Qed.

(* an inner [bv_wrap] in the MIDDLE of a sum is invisible to
   [bv_wrap_add_idemp_l/r]; rotate it to the head first. *)
Lemma wrap_add3 (a b c : Z) : bv_wrap 64 (bv_wrap 64 a + b + c) = bv_wrap 64 (a + b + c).
Proof.
  replace (bv_wrap 64 a + b + c) with (bv_wrap 64 a + (b + c)) by ring.
  rewrite bv_wrap_add_idemp_l. f_equal. ring.
Qed.

Lemma wrap_add3' (a b c : Z) : bv_wrap 64 (a + bv_wrap 64 b + c) = bv_wrap 64 (a + b + c).
Proof.
  replace (a + bv_wrap 64 b + c) with (bv_wrap 64 b + (a + c)) by ring.
  rewrite bv_wrap_add_idemp_l. f_equal. ring.
Qed.

(* the '-' byte's address: gcc computes [buf + i] as [(i - 32) + s0 - 24] with
   [s0 = sp0] and [buf = sp0 - 56]. *)
Lemma sign_slot_addr (sp0 : mword 64) (n : nat) :
  add_vec (add_vec (add_vec (mword_of_int (Z.of_nat n) : mword 64) (mword_of_int (-32))) sp0)
          (mword_of_int (-24))
  = pa_add (pa_stk sp0 7) n.
Proof.
  apply bv_eq. unfold pa_add, pa_stk, add_vec_int.
  rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite !bv_wrap_add_idemp_l, !bv_wrap_add_idemp_r.
  rewrite wrap_add3, wrap_add3'.
  f_equal. ring.
Qed.

(* [x + k - k = x] : the print loop's sentinel comes back after the
   [add a4 / sub a4] pair gcc emits. *)
Lemma add_sub_cancel (S : mword 64) (k : Z) :
  sub_vec (add_vec S (mword_of_int k)) (mword_of_int k) = S.
Proof.
  apply bv_eq.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned. rewrite bc_add_vec_unsigned, bc_moi_unsigned.
  rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned S + bv_wrap 64 k - bv_wrap 64 k) with (bv_unsigned S) by ring.
  apply bv_wrap_bv_unsigned.
Qed.

(* every 64-bit value has at most twenty decimal digits *)
Lemma uint_lt_1020 (x : mword 64) : uint x < 10 ^ (Z.of_nat 20).
Proof.
  apply (Z.lt_trans _ (2^64)); [ apply pi_uint_lt64 | vm_compute; reflexivity ].
Qed.

(* two immediate offsets from the same base collapse into one -- the shape a
   va_list bump ([ap] read, +8, written back) needs. *)
Lemma addv_moi_moi (x : mword 64) (a b : Z) :
  add_vec (add_vec x (mword_of_int a)) (mword_of_int b) = add_vec x (mword_of_int (a + b)).
Proof.
  apply bv_eq. rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite bv_wrap_add_idemp_l, !bv_wrap_add_idemp_r.
  (* the surviving inner wrap sits in the middle of the sum: rotate it out *)
  rewrite wrap_add3'. f_equal. ring.
Qed.

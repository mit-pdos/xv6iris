(* KstackArith.v -- the pure arithmetic behind KSTACK(i), separated from the
   two proofs that need it.

   gcc compiles [p - proc] (an array of 360-byte elements) into an arithmetic
   shift by 3 followed by a multiply by the modular inverse of 45:

     45 * 0x4fa4fa4fa4fa4fa5 = 1 + 14 * 2^64,

   so [(360*i >>s 3) * magic] IS [i] mod 2^64, and the rest of the sequence
   ([slli 13], [addw 0x2000], [sub] from TRAMPOLINE) is
   [0x3FFFFFF000 - (i+1)*8192] -- i.e. KvmMap.kstack_va i.

   proc_mapstacks maps those pages and procinit stores the addresses into
   [p->kstack], so BOTH need this; it used to live inside
   ProofProcMapstacks.v, and a Proof file must not be imported
   (code-organization.md).  Its own file rather than RiscvExtras.v because the
   chain is stated over Sail operators ([shift_bits_left],
   [mult_to_bits_half], [get_slice_int]) that the root-level mword-facts file
   deliberately does not pull in. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions bitvector.tactics.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvExtras.
Require Import ExecCommon VcGen.
Local Open Scope Z_scope.

(* ================================================================= *)
(* Pure arithmetic: the KSTACK address bridge.                        *)
(* ================================================================= *)


(* magic reciprocal fact *)
Lemma magic_recip : (45 * 0x4fa4fa4fa4fa4fa5 = 1 + 14 * 18446744073709551616)%Z.
Proof. vm_compute. reflexivity. Qed.

(* sint of a small nonnegative mword_of_int *)
Lemma sint_moi_small (z : Z) : (0 <= z < 2^63)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  assert (Hu : bv_unsigned (mword_of_int z : mword 64) = z).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    lia. }
  rewrite Hu. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 2^63) by reflexivity. rewrite Hhm. lia.
Qed.

Lemma moi64_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 64) = z `mod` 18446744073709551616.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma sub128_63 (x : mword (2*64)) :
  bv_unsigned (subrange_vec_dec x (64-1) 0) = bv_unsigned x `mod` 2^64.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (64 - 1 - 0 + 1)) with 64%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). reflexivity.
Qed.

Lemma sub128_127 (x : mword (0+2*64-1+1)) :
  bv_unsigned (subrange_vec_dec x (0+2*64-1) 0) = bv_unsigned x `mod` 2^128.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (0+2*64 - 1 - 0 + 1)) with 128%N.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 128) with (2^128). reflexivity.
Qed.

Lemma gsi128 (N : Z) : bv_unsigned (get_slice_int (2*64) N 0) = N `mod` 2^128.
Proof.
  rewrite get_slice_int_eta. unfold get_slice_int'.
  replace (2 * 64 >=? 0) with true by reflexivity. cbn [sumbool_of_bool].
  rewrite autocast_id. rewrite sub128_127.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx (0+2*64-1+1)) = 2^128) as -> by (vm_compute; reflexivity).
  rewrite Zmod_mod. reflexivity.
Qed.

(* the MUL result value characterization *)
Lemma mult_low_unsigned (a b : mword 64) :
  bv_unsigned (mult_to_bits_half 64 Signed Signed a b Low)
  = (sint a * sint b) `mod` 2 ^ 64.
Proof.
  unfold mult_to_bits_half. cbn beta iota.
  unfold to_bits_truncate.
  rewrite autocast_id.
  rewrite sub128_63.
  rewrite gsi128.
  change (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
  rewrite (Z.mod_mod_divide (sint a * sint b) (2^64*2^64) (2^64)); [reflexivity | exists (2^64); ring].
Qed.

(* the KSTACK mul step: (45*i) * magic ≡ i (mod 2^64) for i < 64 *)
Lemma kstack_mul_step (i : nat) : (i < 64)%nat ->
  mult_to_bits_half 64 Signed Signed
    (mword_of_int (45 * Z.of_nat i)) (mword_of_int 0x4fa4fa4fa4fa4fa5) Low
  = mword_of_int (Z.of_nat i).
Proof.
  intro Hi. apply bv_eq. rewrite mult_low_unsigned.
  rewrite (sint_moi_small (45 * Z.of_nat i) ltac:(split; [lia | change (2^63) with 9223372036854775808; lia])).
  rewrite (sint_moi_small 0x4fa4fa4fa4fa4fa5 ltac:(split; [lia | vm_compute; reflexivity])).
  rewrite moi64_unsigned. change 18446744073709551616 with (2^64).
  (* 45*i*magic = i + (i*14)*2^64 ≡ i mod 2^64 *)
  assert (Hprod : (45 * Z.of_nat i * 5738987045154082725
                   = Z.of_nat i + (Z.of_nat i * 14) * 2 ^ 64)%Z)
    by (change (2 ^ 64)%Z with 18446744073709551616%Z; ring).
  rewrite Hprod. rewrite Z_mod_plus_full. reflexivity.
Qed.


Lemma moi64_uns (z : Z) : (0 <= z < 18446744073709551616)%Z -> bv_unsigned (mword_of_int z : mword 64) = z.
Proof.
  intro. unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity). lia.
Qed.

Lemma bvsigned_moi_small (z : Z) : (0 <= z < 2^63)%Z -> bv_signed (mword_of_int z : mword 64) = z.
Proof. intro Hz. change (bv_signed ?x) with (sint x). apply sint_moi_small; exact Hz. Qed.

Lemma srai3 (z : Z) : (0 <= z < 9223372036854775808)%Z ->
  shift_bits_right_arith (mword_of_int z : mword 64) (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0)
  = mword_of_int (z / 8).
Proof.
  intro Hz. apply bv_eq.
  unfold shift_bits_right_arith, arith_shiftr, with_word, get_word, MachineWord.MachineWord.arith_shift_right.
  rewrite bv_ashiftr_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx (int_of_mword false (subrange_vec_dec (mword_of_int 3 : mword 6) 5 0))))) with 3
    by (vm_compute; reflexivity).
  rewrite (bvsigned_moi_small z ltac:(change (2^63)%Z with 9223372036854775808%Z; lia)).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2^3) with 8.
  assert (Hdlt : 0 <= z / 8 < 18446744073709551616).
  { split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with z; [apply Z.div_le_upper_bound; lia | lia]. }
  rewrite (moi64_uns (z/8) ltac:(exact Hdlt)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact Hdlt.
Qed.

Lemma slli13 (z : Z) : (0 <= z)%Z -> (z * 8192 < 18446744073709551616)%Z ->
  shift_bits_left (mword_of_int z : mword 64) (subrange_vec_dec (mword_of_int 13 : mword 6) 5 0)
  = mword_of_int (z * 8192).
Proof.
  intros Hz0 Hz. apply bv_eq.
  unfold shift_bits_left, shiftl, with_word, get_word, MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx (int_of_mword false (subrange_vec_dec (mword_of_int 13 : mword 6) 5 0))))) with 13
    by (vm_compute; reflexivity).
  assert (Hzlt : z < 18446744073709551616) by nia.
  rewrite (moi64_uns z ltac:(lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2^13) with 8192.
  rewrite (moi64_uns (z*8192) ltac:(lia)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  split; [apply Z.mul_nonneg_nonneg; lia | exact Hz].
Qed.

Require Import RiscvExtras.

(* sub_vec of two mword_of_int, no wrap *)
Lemma subvec_moi (x y : Z) : (0 <= y)%Z -> (y <= x)%Z -> (x < 18446744073709551616)%Z ->
  sub_vec (mword_of_int x : mword 64) (mword_of_int y : mword 64) = mword_of_int (x - y).
Proof.
  intros Hy Hyx Hx. apply bv_eq.
  assert (Hxy : (0 <= x - y < 18446744073709551616)%Z) by lia.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned.
  rewrite (moi64_uns x ltac:(lia)). rewrite (moi64_uns y ltac:(lia)).
  rewrite (moi64_uns (x - y) ltac:(exact Hxy)).
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact Hxy.
Qed.

(* addw step: (8192*i) +w 8192 = 8192*(i+1), no truncation *)
Lemma addw_step (i : nat) : (i < 64)%nat ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int (8192 * Z.of_nat i) : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int 8192 : mword 64) 31 0 : mword 32))
  = mword_of_int (8192 * (Z.of_nat i + 1)).
Proof.
  intro Hi.
  assert (Hvb : (0 <= 8192 * (Z.of_nat i + 1) <= 524288)%Z).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    apply (Z.le_trans _ (8192 * 64)); [apply Z.mul_le_mono_nonneg_l; lia | apply Z.leb_le; vm_compute; reflexivity]. }
  apply bv_eq.
  rewrite <- !trunc32_subrange.
  rewrite !trunc32_mword_of_int.
  set (v := (8192 * (Z.of_nat i + 1))%Z) in *.
  rewrite (moi64_uns v ltac:(lia)).
  set (w := add_vec (mword_of_int (8192 * Z.of_nat i) : mword 32) (mword_of_int 8192 : mword 32)).
  assert (Hw : bv_unsigned w = v).
  { unfold w, v, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    assert (Ha : bv_unsigned (mword_of_int (8192 * Z.of_nat i) : mword 32) = 8192 * Z.of_nat i).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
    assert (Hb : bv_unsigned (mword_of_int 8192 : mword 32) = 8192).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
      change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
    rewrite Ha. rewrite Hb.
    replace (8192 * Z.of_nat i + 8192)%Z with (8192 * (Z.of_nat i + 1))%Z by lia.
    apply bv_wrap_small. unfold bv_modulus.
    change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z with 4294967296%Z. lia. }
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite Hw.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [| rewrite Hhm; lia].
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. lia.
Qed.

(* UmodeArith.v -- the [mword_of_int] CALCULUS of the verified user-execution
   tier (claude-notes/projects/user-echo.md).

   A verified program's proof carries every live register as a concrete
   [mword 64].  The leaves (WpUmodeLeaf.v, WpUmodeBranch.v) hand back the
   MODEL's spelling of each result -- [add_vec], [sign_extend'] of a
   subrange, [shift_bits_left], [sub_vec] of two low halves -- and a proof
   that has to relate three consecutive such results to a pointer's ARITHMETIC
   drowns in bitvector plumbing.

   So every value in this tier is normalized to ONE shape, [mword_of_int z]
   with [z : Z], and this file is the rewrite kit that keeps it there:

     [moi_add]    the workhorse -- and it is UNCONDITIONAL, because
                  [mword_of_int] already wraps.  Side conditions appear only
                  where a lemma has to read a value BACK ([uint_moi]) or where
                  the model truncates ([moi_sext32], the shifts).
     [moi_*]      one lemma per instruction family echo executes.

   A CLOSED immediate never needs a lemma here: [sign_extend' 64
   (mword_of_int 2300 : mword 12) = mword_of_int (-1796)] is a [vm_compute]
   at the call site.  What needs a lemma is a SYMBOLIC value, and that is
   what everything below is about. *)
From Stdlib Require Import ZArith Bool Lia Znumtheory.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvExtras.
Require Import UserBits.
Local Open Scope Z_scope.
Import Defs.

Definition Z64 : Z := 18446744073709551616.   (* 2 ^ 64 *)
Definition Z63 : Z := 9223372036854775808.    (* 2 ^ 63 *)
Definition Z32 : Z := 4294967296.             (* 2 ^ 32 *)
Definition Z31 : Z := 2147483648.             (* 2 ^ 31 *)

Lemma Zmod64 : bv_modulus 64 = Z64.
Proof. vm_compute; reflexivity. Qed.
Lemma Zmod32 : bv_modulus 32 = Z32.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* §1 Reading a normalized value.                                          *)
(* ===================================================================== *)

Lemma moi_unsigned (z : Z) :
  bv_unsigned (mword_of_int z : mword 64) = z mod Z64.
Proof. rewrite moi64_unsigned. unfold bv_wrap. rewrite Zmod64. reflexivity. Qed.

Lemma moi_small (z : Z) :
  0 <= z < Z64 -> bv_unsigned (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite moi_unsigned. apply Z.mod_small. exact H. Qed.

Lemma uint_moi (z : Z) :
  0 <= z < Z64 -> uint (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite uint_unsigned. exact (moi_small z H). Qed.

Lemma moi_mod (x y : Z) :
  x mod Z64 = y mod Z64 -> (mword_of_int x : mword 64) = mword_of_int y.
Proof. intro H. apply bv_eq. rewrite !moi_unsigned. exact H. Qed.

Lemma moi_of_unsigned (a : mword 64) : (mword_of_int (bv_unsigned a) : mword 64) = a.
Proof.
  apply bv_eq. rewrite moi_unsigned.
  pose proof (bv_unsigned_in_range _ a) as Hr. rewrite Zmod64 in Hr.
  apply Z.mod_small. exact Hr.
Qed.

Lemma moi_of_uint (a : mword 64) : (mword_of_int (uint a) : mword 64) = a.
Proof. rewrite uint_unsigned. apply moi_of_unsigned. Qed.

(* the signed reading, on the range every user pointer and count lives in *)
Lemma sint_moi (z : Z) :
  0 <= z < Z63 -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro H.
  change (sint (mword_of_int z : mword 64)) with (bv_signed (mword_of_int z : mword 64)).
  unfold bv_signed, bv_swrap, bv_wrap.
  rewrite moi_unsigned.
  rewrite (Z.mod_small z Z64 ltac:(unfold Z64, Z63 in *; lia)).
  assert (Eh : bv_half_modulus 64 = Z63) by (vm_compute; reflexivity).
  rewrite Zmod64 Eh.
  rewrite (Z.mod_small (z + Z63) Z64 ltac:(unfold Z64, Z63 in *; lia)). lia.
Qed.

(* ===================================================================== *)
(* §2 THE workhorse: addition, unconditional.                              *)
(* ===================================================================== *)

Lemma moi_add (x y : Z) :
  add_vec (mword_of_int x : mword 64) (mword_of_int y) = mword_of_int (x + y).
Proof.
  apply bv_eq.
  rewrite add_vec64_unsigned !moi_unsigned.
  unfold bv_wrap. rewrite Zmod64.
  rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma moi_sub (x y : Z) :
  sub_vec (mword_of_int x : mword 64) (mword_of_int y) = mword_of_int (x - y).
Proof.
  apply bv_eq.
  rewrite sub_vec64_unsigned !moi_unsigned.
  unfold bv_wrap. rewrite Zmod64.
  rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 Comparisons -- the branch leaf's [uv_btaken] arguments.              *)
(* ===================================================================== *)

Lemma moi_eq_vec (x y : Z) :
  0 <= x < Z64 -> 0 <= y < Z64 ->
  eq_vec (mword_of_int x : mword 64) (mword_of_int y) = Z.eqb x y.
Proof.
  intros Hx Hy.
  destruct (Z.eqb_spec x y) as [-> | Hne].
  - apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff. intro Heq.
    apply Hne. rewrite <- (moi_small x Hx), <- (moi_small y Hy), Heq. reflexivity.
Qed.

Lemma moi_neq_vec (x y : Z) :
  0 <= x < Z64 -> 0 <= y < Z64 ->
  neq_vec (mword_of_int x : mword 64) (mword_of_int y) = negb (Z.eqb x y).
Proof. intros Hx Hy. unfold neq_vec. rewrite (moi_eq_vec x y Hx Hy). reflexivity. Qed.

Lemma moi_ge_s (x y : Z) :
  0 <= x < Z63 -> 0 <= y < Z63 ->
  zopz0zKzJ_s (mword_of_int x : mword 64) (mword_of_int y) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_s.
  rewrite (sint_moi x Hx) (sint_moi y Hy). reflexivity.
Qed.

Lemma moi_lt_s (x y : Z) :
  0 <= x < Z63 -> 0 <= y < Z63 ->
  zopz0zI_s (mword_of_int x : mword 64) (mword_of_int y) = Z.ltb x y.
Proof.
  intros Hx Hy. unfold zopz0zI_s.
  rewrite (sint_moi x Hx) (sint_moi y Hy). reflexivity.
Qed.

(* ===================================================================== *)
(* §4 The 32-bit truncating operations: addiw / subw.                      *)
(*                                                                         *)
(* Both are "compute in 32 bits, sign-extend to 64".  On a value whose      *)
(* 32-bit result is a small NON-NEGATIVE number -- which is every count     *)
(* echo computes -- the sign extension is the identity and the whole        *)
(* instruction is exact.                                                   *)
(* ===================================================================== *)

Lemma low32_moi (z : Z) :
  bv_unsigned (subrange_vec_dec (mword_of_int z : mword 64) 31 0 : mword 32)
  = z mod Z32.
Proof.
  rewrite (subrange_dec_unsigned_lo0 (mword_of_int z : mword 64) 31 Z32
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite moi_unsigned.
  rewrite <- (Znumtheory.Zmod_div_mod Z32 Z64 z
                ltac:(unfold Z32; lia) ltac:(unfold Z64; lia)
                ltac:(exists Z32; unfold Z32, Z64; reflexivity)).
  reflexivity.
Qed.

Lemma sext32_small (w : mword 32) :
  bv_unsigned w < Z31 ->
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_unsigned w).
Proof.
  intro Hlt.
  apply bv_eq.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold bv_signed, bv_swrap, bv_wrap.
  assert (Eh32 : bv_half_modulus 32 = Z31) by (vm_compute; reflexivity).
  rewrite Zmod32 Eh32 Zmod64 moi_unsigned.
  pose proof (proj1 (bv_unsigned_in_range _ w)) as Hlo.
  rewrite (Z.mod_small (bv_unsigned w + Z31) Z32 ltac:(unfold Z31, Z32 in *; lia)).
  replace (bv_unsigned w + Z31 - Z31) with (bv_unsigned w) by lia.
  reflexivity.
Qed.

(* addiw / c.addiw at a result that fits: rd := x + d exactly *)
Lemma moi_addw (x d : Z) :
  0 <= x + d < Z31 ->
  (sign_extend' 64
     (subrange_vec_dec (add_vec (mword_of_int x : mword 64) (mword_of_int d)) 31 0
      : mword 32) : mword 64)
  = mword_of_int (x + d).
Proof.
  intro H.
  rewrite moi_add.
  assert (Hlow : bv_unsigned
                   (subrange_vec_dec (mword_of_int (x + d) : mword 64) 31 0 : mword 32)
                 = x + d).
  { rewrite low32_moi. apply Z.mod_small. unfold Z31, Z32 in *; lia. }
  rewrite (sext32_small (subrange_vec_dec (mword_of_int (x + d) : mword 64) 31 0)
             ltac:(rewrite Hlow; unfold Z31 in *; lia)).
  rewrite Hlow. reflexivity.
Qed.

(* subw at a result that fits: rd := x - y exactly, whatever the HIGH halves
   of x and y are (a 32-bit subtraction only sees the low halves) *)
Lemma moi_subw (x y : Z) :
  0 <= x - y < Z31 ->
  (sign_extend' 64
     (sub_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
              (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
   : mword 64)
  = mword_of_int (x - y).
Proof.
  intro H.
  assert (Hlow : bv_unsigned
                   (sub_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
                            (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
                 = (x - y) mod Z32).
  { rewrite sub_vec32_unsigned !low32_moi.
    unfold bv_wrap. rewrite Zmod32.
    rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r. reflexivity. }
  assert (Hlow' : bv_unsigned
                    (sub_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
                             (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
                  = x - y).
  { rewrite Hlow. apply Z.mod_small. unfold Z31, Z32 in *; lia. }
  rewrite (sext32_small
             (sub_vec (subrange_vec_dec (mword_of_int x : mword 64) 31 0 : mword 32)
                      (subrange_vec_dec (mword_of_int y : mword 64) 31 0 : mword 32))
             ltac:(rewrite Hlow'; unfold Z31 in *; lia)).
  rewrite Hlow'. reflexivity.
Qed.

(* ===================================================================== *)
(* §5 The shift pair.                                                      *)
(*                                                                         *)
(* gcc's zero-extend-and-scale idiom is [slli rd,rs,32; srli rd,rd,32-k],   *)
(* i.e. "clear the high half, then multiply by 2^k".  echo uses k = 3       *)
(* (scaling an argv index to a byte offset).  The two halves are stated     *)
(* separately because the leaf hands back one at a time.                    *)
(* ===================================================================== *)

Lemma shift_amount_bv (sh : Z) :
  0 <= sh < 64 ->
  bv_unsigned (subrange_vec_dec (mword_of_int sh : mword 6)
                 (Z.sub log2_xlen 1) 0 : mword 6) = sh.
Proof.
  intro H.
  change (Z.sub log2_xlen 1) with 5.
  rewrite (subrange_dec_unsigned_lo0 (mword_of_int sh : mword 6) 5 64
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  unfold mword_of_int, Values.to_word, get_word. cbn.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  assert (E6 : bv_modulus 6 = 64) by (vm_compute; reflexivity).
  rewrite E6. rewrite (Z.mod_small sh 64 H). apply Z.mod_small. exact H.
Qed.

(* the shift count, as the model's own [N_to_word] spells it *)
Lemma nw_unsigned (sh : Z) :
  0 <= sh < 64 ->
  bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 64)
                 (MachineWord.MachineWord.Z_idx sh)) = sh.
Proof.
  intro H.
  unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
  rewrite Z_to_bv_unsigned. rewrite Z2N.id; [ | lia ].
  unfold bv_wrap. rewrite Zmod64. apply Z.mod_small. unfold Z64; lia.
Qed.

(* ... as the model's [shift_bits_*] actually spells it *)
Lemma shift_amount (sh : Z) :
  0 <= sh < 64 ->
  int_of_mword false (subrange_vec_dec (mword_of_int sh : mword 6)
                        (Z.sub log2_xlen 1) 0) = sh.
Proof.
  intro H.
  change (int_of_mword false
            (subrange_vec_dec (mword_of_int sh : mword 6) (Z.sub log2_xlen 1) 0))
    with (uint (subrange_vec_dec (mword_of_int sh : mword 6) (Z.sub log2_xlen 1) 0)).
  rewrite uint_unsigned_n. exact (shift_amount_bv sh H).
Qed.

Lemma moi_shl (z sh : Z) :
  0 <= sh < 64 ->
  shift_bits_left (mword_of_int z : mword 64)
    (subrange_vec_dec (mword_of_int sh : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (z * 2 ^ sh).
Proof.
  intro Hsh.
  unfold shift_bits_left.
  rewrite (shift_amount sh Hsh).
  apply bv_eq.
  unfold shiftl, SailStdpp.Values.with_word,
    SailStdpp.Values.get_word, MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  rewrite (nw_unsigned sh Hsh).
  rewrite !moi_unsigned. unfold bv_wrap. rewrite Zmod64.
  rewrite Z.shiftl_mul_pow2; [ | lia ].
  rewrite Z.mul_mod_idemp_l; [ reflexivity | unfold Z64; lia ].
Qed.

Lemma moi_shr (z sh : Z) :
  0 <= sh < 64 -> 0 <= z < Z64 ->
  shift_bits_right (mword_of_int z : mword 64)
    (subrange_vec_dec (mword_of_int sh : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (z / 2 ^ sh).
Proof.
  intros Hsh Hz.
  unfold shift_bits_right.
  rewrite (shift_amount sh Hsh).
  apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word,
    SailStdpp.Values.get_word, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  rewrite (nw_unsigned sh Hsh).
  rewrite !moi_unsigned.
  rewrite (Z.mod_small z Z64 Hz).
  rewrite Z.shiftr_div_pow2; [ | lia ].
  symmetry. apply Z.mod_small.
  pose proof (Z.pow_pos_nonneg 2 sh ltac:(lia) ltac:(lia)).
  split; [ apply Z.div_pos; lia | ].
  apply (Z.le_lt_trans _ z); [ apply Z.div_le_upper_bound; nia | lia ].
Qed.

(* THE composite: the whole [slli 32 ; srli (32-k)] idiom at once.  [z] need
   only fit in 32 bits -- that is exactly what the pair is FOR. *)
Lemma moi_zext_scale (z k : Z) :
  0 <= z < Z32 -> 0 <= k <= 32 ->
  (mword_of_int (z * Z32 / 2 ^ (32 - k)) : mword 64) = mword_of_int (z * 2 ^ k).
Proof.
  intros Hz Hk.
  f_equal.
  assert (Hp : 0 < 2 ^ (32 - k)) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ k * 2 ^ (32 - k) = Z32).
  { rewrite <- Z.pow_add_r; [ | lia | lia ].
    replace (k + (32 - k)) with 32 by lia. vm_compute. reflexivity. }
  rewrite <- E. rewrite Z.mul_assoc. apply Z.div_mul. lia.
Qed.

(* THE instance echo needs, in one rewrite: [slli rd,rs,32 ; srli rd,rd,29] on
   a value that fits in 32 bits is "scale an argv index to a byte offset". *)
Lemma moi_shl32_shr29 (z : Z) :
  0 <= z < Z32 ->
  shift_bits_right
    (shift_bits_left (mword_of_int z : mword 64)
       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 29 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (z * 8).
Proof.
  intro Hz.
  rewrite (moi_shl z 32 ltac:(lia)).
  rewrite (moi_shr (z * 2 ^ 32) 29 ltac:(lia)
             ltac:(change (2 ^ 32) with Z32; unfold Z32, Z64 in *; lia)).
  f_equal.
  replace (2 ^ 32) with (8 * 2 ^ 29) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc. apply Z.div_mul. vm_compute; discriminate.
Qed.

(* ===================================================================== *)
(* §6 x0.                                                                  *)
(*                                                                         *)
(* Every leaf whose expansion reads x0 -- c.li (ADDI from x0), c.mv (ADD    *)
(* from x0) -- hands back its result as [add_vec zero_reg v].  Normalizing  *)
(* that away is the first rewrite of every such call site.                 *)
(* ===================================================================== *)

Lemma zero_reg_moi : (zero_reg : mword 64) = mword_of_int 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma moi_add_zero_l (x : Z) :
  add_vec (zero_reg : mword 64) (mword_of_int x) = mword_of_int x.
Proof. rewrite zero_reg_moi moi_add. f_equal; lia. Qed.

Lemma moi_eq_zero (x : Z) :
  0 <= x < Z64 -> eq_vec (mword_of_int x : mword 64) zero_reg = Z.eqb x 0.
Proof.
  intro H. rewrite zero_reg_moi.
  apply (moi_eq_vec x 0 H). unfold Z64; lia.
Qed.

Lemma moi_neq_zero (x : Z) :
  0 <= x < Z64 -> neq_vec (mword_of_int x : mword 64) zero_reg = negb (Z.eqb x 0).
Proof. intro H. unfold neq_vec. rewrite (moi_eq_zero x H). reflexivity. Qed.

(* an unsigned byte load leaves its byte ZERO-extended; normalize it like
   everything else.  (A byte read out of a [gmap Z (bv 8)] image must be
   given the binder type [mword 8] -- see durable-notes.md's mword-width
   traps.) *)
Lemma zext8_unsigned (b : mword 8) :
  bv_unsigned (zero_extend' 64 b : mword 64) = bv_unsigned b.
Proof.
  unfold zero_extend'.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

Lemma zext8_moi (b : mword 8) :
  (zero_extend' 64 b : mword 64) = mword_of_int (bv_unsigned b).
Proof.
  transitivity (mword_of_int (bv_unsigned (zero_extend' 64 b : mword 64)) : mword 64).
  - symmetry. apply moi_of_unsigned.
  - rewrite zext8_unsigned. reflexivity.
Qed.

(* [moi_add] at a register that is not YET normalized -- the shape every
   "pointer + closed displacement" step lands in *)
Lemma moi_add_l (a : mword 64) (d : Z) :
  add_vec a (mword_of_int d) = mword_of_int (uint a + d).
Proof.
  transitivity (add_vec (mword_of_int (uint a) : mword 64) (mword_of_int d)).
  - rewrite moi_of_uint. reflexivity.
  - apply moi_add.
Qed.

(* ... and its reading direction: a word whose [uint] is known IS that
   literal's [mword_of_int] *)
Lemma moi_of_uint_eq (a : mword 64) (z : Z) : uint a = z -> a = mword_of_int z.
Proof. intro H. rewrite <- H. symmetry. apply moi_of_uint. Qed.

(* the UNSIGNED twins of [moi_ge_s] / [moi_lt_s].  Every pointer comparison
   is unsigned (`bltu' / `bgeu'), so these are what a scan over a data
   structure actually needs -- the signed pair only fits counts. *)
Lemma moi_lt_u (x y : Z) :
  0 <= x < Z64 -> 0 <= y < Z64 ->
  zopz0zI_u (mword_of_int x : mword 64) (mword_of_int y) = Z.ltb x y.
Proof.
  intros Hx Hy. unfold zopz0zI_u.
  rewrite (uint_moi x Hx) (uint_moi y Hy). reflexivity.
Qed.

Lemma moi_ge_u (x y : Z) :
  0 <= x < Z64 -> 0 <= y < Z64 ->
  zopz0zKzJ_u (mword_of_int x : mword 64) (mword_of_int y) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_u.
  rewrite (uint_moi x Hx) (uint_moi y Hy). reflexivity.
Qed.

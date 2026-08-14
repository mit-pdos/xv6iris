(* BvShift.v -- TWO FACTS ABOUT WHAT A SHIFT PAIR AND A SIGNED READING DO
   TO THE LOW BITS OF A WORD.  Pure stdpp bitvector arithmetic: this file
   requires no Sail, no Iris and nothing else in the tree, and it is where
   a whole-function walk should reach for either fact.

   WHY THEY ARE WORTH A FILE.  RV64 has no sub-word zero-extension
   instruction, so gcc spells one as a SHIFT PAIR -- [slli rd,rd,64-w] then
   [srli rd,rd,64-w] keeps the low [w] bits and clears the rest -- and it
   emits that idiom wherever a C [short] or [int] is widened.  create's
   found arm is the first whole-function proof in this tree to walk one
   ([lhu; addiw -2; slli 48; srli 48; bltu], the [ip->type in {2,3}] range
   test at +0x52..+0x5e), and there was no lemma for it anywhere.  The
   second fact is its companion: the [addiw] in the middle leaves a
   SIGN-extended 32-bit intermediate, and the shift pair then reads it
   unsigned, so the proof needs "a signed reading and an unsigned reading
   agree on the low bits" as well.

   Both are stated generally rather than at create's widths.  [swrap_low]'s
   [(m | h)] premise is what makes it width-generic: [h] is the half
   modulus, [2 * h] the modulus, and any [m] dividing [h] is a window the
   sign correction cannot disturb.

   ==== AN ORPHAN THIS FILE DOES NOT ADOPT, RECORDED ON PURPOSE ==========

   [BootReset.v] section 3a proves three generic bitvector lemmas of the
   same kind -- [bv_extract_concat_mid], [bv_extract_extract_0] and
   [bv_extract_full] -- which stdpp does not provide and which have nothing
   to do with the boot path they were proven for.  They belong HERE.  They
   are not moved now because [BootReset.v] is a landed 60 s / 0.77 GB proof
   and reopening it buys no gate; move them at the next touch of that file,
   and delete this paragraph when you do. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.

Local Open Scope Z_scope.

(* THE SHIFT PAIR.  [slli k] then [srli k] on an [m]-bit register, where
   [m = k + n], keeps exactly the low [n] bits -- and the [bv_wrap] is the
   register's own width, i.e. the truncation the [slli] itself performs.
   Stated over [Z] shift amounts rather than [N] ones because that is how
   the shift leaves ([WpSconfAlu.wp_cslli_s_sconf] / [wp_csrli_s_sconf])
   deliver them, so no [Z.of_N] has to be pushed through at the call. *)
Lemma bv_wrap_shift_pair (m : N) (n k x : Z) :
  0 <= k -> 0 <= n -> Z.of_N m = k + n ->
  Z.shiftr (bv_wrap m (Z.shiftl x k)) k = x `mod` 2 ^ n.
Proof.
  intros Hk Hn Hm.
  rewrite Z.shiftl_mul_pow2 by exact Hk.
  rewrite Z.shiftr_div_pow2 by exact Hk.
  unfold bv_wrap, bv_modulus. rewrite Hm, Z.pow_add_r by lia.
  rewrite (Z.mul_comm x (2 ^ k)).
  rewrite Z.mul_mod_distr_l by (apply Z.pow_nonzero; lia).
  rewrite (Z.mul_comm (2 ^ k) (x `mod` 2 ^ n)).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

(* THE SIGNED READING.  [bv_signed] is [bv_swrap], i.e. "add the half
   modulus, wrap, subtract it again", and every step of that is a multiple
   of any [m] that divides the half modulus.  So a signed reading and an
   unsigned one agree modulo [m] -- which is what lets a proof walk an
   [addiw] (32-bit, sign-extended) and then read only the low sixteen bits
   without ever case-splitting on the sign. *)
Lemma swrap_low (h m u : Z) : m <> 0 -> (m | h) ->
  ((u + h) `mod` (2 * h) - h) `mod` m = u `mod` m.
Proof.
  intros Hm [q Hq].
  replace ((u + h) `mod` (2 * h) - h)
     with ((u + h) `mod` (2 * h) + (- q) * m) by lia.
  rewrite Z.mod_add by exact Hm.
  rewrite Z.mod_mod_divide by (exists (2 * q); lia).
  replace (u + h) with (u + q * m) by lia.
  rewrite Z.mod_add by exact Hm. reflexivity.
Qed.

(* the instance a 32-bit intermediate read at sixteen bits wants, spelled
   in the shape [unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus,
   bv_modulus] leaves behind -- note the [/ 2], which is
   [bv_half_modulus] and does NOT reduce to a literal on its own. *)
Lemma swrap_low_32_16 (u : Z) :
  ((u + 4294967296 / 2) `mod` 4294967296 - 4294967296 / 2) `mod` 65536
  = u `mod` 65536.
Proof. apply (swrap_low 2147483648 65536 u); [lia | exists 32768; reflexivity]. Qed.

(* ==== THE PREMISE-FREE COROLLARIES A PROOFMODE FILE CAN ACTUALLY USE ====
   Every consumer of this file loads the iris proofmode, where ssreflect's
   [rewrite] rejects BOTH the comma form and [rewrite lem by tac].  So the
   side conditions are discharged HERE, in a file with no ssreflect, and
   the consumer does bare rewrites.  That is the whole reason these exist
   as separate lemmas rather than as [by] clauses at the call sites. *)

Lemma bv_wrap_shift_pair_16 (x : Z) :
  Z.shiftr (bv_wrap 64 (Z.shiftl x 48)) 48 = x `mod` 65536.
Proof. rewrite (bv_wrap_shift_pair 64 16 48 x) by lia. reflexivity. Qed.

Lemma mod_2_64_16 (a : Z) :
  (a `mod` 18446744073709551616) `mod` 65536 = a `mod` 65536.
Proof. rewrite Z.mod_mod_divide by (exists 281474976710656; reflexivity). reflexivity. Qed.

Lemma mod_2_64_32 (a : Z) :
  (a `mod` 18446744073709551616) `mod` 4294967296 = a `mod` 4294967296.
Proof. rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity). reflexivity. Qed.

Lemma mod_2_32_16 (a : Z) :
  (a `mod` 4294967296) `mod` 65536 = a `mod` 65536.
Proof. rewrite Z.mod_mod_divide by (exists 65536; reflexivity). reflexivity. Qed.

(* the [-2] the addiw adds arrives as the 64-bit constant [2^64 - 2]; at
   32 bits that is just [-2] again *)
Lemma sub2_wrap64_32 (T : Z) :
  (T + 18446744073709551614) `mod` 4294967296 = (T - 2) `mod` 4294967296.
Proof.
  replace (T + 18446744073709551614)
     with ((T - 2) + 4294967296 * 4294967296) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* W32Arith.v -- the 32-bit ALU laws a whole-function proof needs when the C
   it is about counts in [int].

   [addw] / [subw] / [sext.w] all compute in 32 bits and sign-extend to 64, so
   a proof about a loop counter has to show, over and over, that the round
   trip is the identity on the values the loop actually holds -- small
   non-negative literals.  The same four laws were being restated per
   function ([ProofFilewriteParts]'s [fw_subw_moi] / [fw_addw_moi] /
   [fw_sextw_moi] / [fw_bge_moi], [ProofFilereadParts]'s [fr_sext_moi32]),
   which is one restatement per counting loop in the tree; this is their
   home.

   Everything here is PURE and Iris-free, and it requires only the decode /
   bitvector layer, so it costs nothing on the critical path: a proof file
   that needs it gains a leaf dependency, not a sibling whole-function one.
   That is also why the file has since taken in the small BYTE and MASK facts
   at the bottom, which are not 32-bit ALU laws at all: they are the other
   thing two whole-function proofs kept restating, and this is the only leaf
   both of them already depend on.

   STATED OVER PLAIN [Z], never over [mword], in the hypotheses.  [lia]
   answers "Cannot find witness" when an [mword] is merely in context, and
   every call site here is inside a whole-function proof whose context is
   full of them. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
(* for the ssreflect [rewrite]/[by] the bitvector proofs below are written in *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvExtras.
Require Import VcGen.
Import Defs.
Local Open Scope Z_scope.

(* ---- the two 32-bit binops, on literals ---- *)

Lemma w32_addv (x y : Z) :
  add_vec (mword_of_int x : mword 32) (mword_of_int y : mword 32)
  = (mword_of_int (x + y) : mword 32).
Proof.
  apply bv_eq.
  rewrite (add_vec_unsigned (mword_of_int x : mword 32) (mword_of_int y : mword 32)).
  rewrite !moi32_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  unfold bv_wrap. by rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r.
Qed.

Lemma w32_subv (x y : Z) :
  sub_vec (mword_of_int x : mword 32) (mword_of_int y : mword 32)
  = (mword_of_int (x - y) : mword 32).
Proof.
  apply bv_eq. rewrite sub_vec32_unsigned !moi32_unsigned.
  unfold bv_wrap. by rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r.
Qed.

(* ---- widening a small non-negative 32-bit literal ---- *)

Lemma w32_sext_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = (mword_of_int z : mword 64).
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bvw64_small.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  change (2 ^ 31)%Z with 2147483648%Z in Hz. lia.
Qed.

(* ---- the three instructions ---- *)

(* [subw rd,ra,rc] : a loop's [n - i].  THE DIFFERENCE is the only thing
   that has to be in [int] range -- the operands wrap away, so a counter
   pair like consoleread's [target - n] is covered even where [n] itself is
   negative (a non-positive request never enters the loop and the answer is
   still 0). *)
Lemma w32_subw_moi (a c : Z) :
  (0 <= a - c < 2 ^ 31)%Z ->
  sign_extend' 64 (sub_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32))
  = (mword_of_int (a - c) : mword 64).
Proof.
  intro Hac.
  rewrite <- !trunc32_subrange. rewrite !trunc32_mword_of_int.
  rewrite w32_subv. apply w32_sext_moi. exact Hac.
Qed.

(* [addw rd,rc,ra] : a loop's [i + nn].  The argument order is the one the
   [RTYPEW (rs2, rs1, rd, ADDW)] leaf produces, i.e. [rs1] first. *)
Lemma w32_addw_moi (a c : Z) :
  (0 <= a)%Z -> (0 <= c)%Z -> (a + c < 2 ^ 31)%Z ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32))
  = (mword_of_int (c + a) : mword 64).
Proof.
  intros Ha Hc Hac.
  rewrite <- !trunc32_subrange. rewrite !trunc32_mword_of_int.
  rewrite w32_addv. apply w32_sext_moi. lia.
Qed.

(* [sext.w rd,rs] = [addiw rd,rs,0], with the immediate in the FOUR-BYTE
   encoding's spelling ([mword_of_int 0 : mword 12]).  The compressed
   [c.addiw]'s zero is [sign_extend' 12 (mword_of_int 0 : mword 6)] and does
   not match this statement -- see [w32_sextw6_moi] below. *)
Lemma w32_sextw_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64)
              (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0 : mword 32)
  = (mword_of_int z : mword 64).
Proof.
  intro Hz.
  assert (H0 : add_vec (mword_of_int z : mword 64)
                 (sign_extend' 64 (mword_of_int 0 : mword 12))
               = (mword_of_int z : mword 64))
    by (apply bv_add_0_r; vm_compute; reflexivity).
  rewrite H0. rewrite <- trunc32_subrange, trunc32_mword_of_int.
  apply w32_sext_moi. exact Hz.
Qed.

Lemma w32_sextw6_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0 : mword 32)
  = (mword_of_int z : mword 64).
Proof.
  intro Hz.
  assert (H0 : add_vec (mword_of_int z : mword 64)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
               = (mword_of_int z : mword 64))
    by (apply bv_add_0_r; vm_compute; reflexivity).
  rewrite H0. rewrite <- trunc32_subrange, trunc32_mword_of_int.
  apply w32_sext_moi. exact Hz.
Qed.

(* ---- the signed compares the [bge] family reduces to ---- *)

Lemma w32_sint_moi (a : Z) : (- 2 ^ 63 <= a < 2 ^ 63)%Z ->
  sint (mword_of_int a : mword 64) = a.
Proof.
  intro Ha.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 63)
    by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

Lemma w32_bge_moi (a c : Z) :
  (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= c < 2 ^ 63)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int c : mword 64) = Z.geb a c.
Proof.
  intros Ha Hc. unfold zopz0zKzJ_s.
  rewrite (w32_sint_moi a Ha) (w32_sint_moi c Hc).
  reflexivity.
Qed.

Lemma w32_bge0_moi (c : Z) : (- 2 ^ 63 <= c < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int c : mword 64) = Z.geb 0 c.
Proof.
  intro Hc.
  assert (Hz : (zero_reg : mword 64) = (mword_of_int 0 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz. apply w32_bge_moi; [lia | exact Hc].
Qed.

(* The UNSIGNED compare, for a [bgeu] whose two operands are non-negative
   [int]s -- which is how gcc spells "did we copy anything yet?" when both
   sides are known non-negative and it can save the sign analysis
   (consoleread's [if (n < target)] at +0xe2). *)
Lemma w32_bgeu_moi (a c : Z) :
  (0 <= a < 2 ^ 64)%Z -> (0 <= c < 2 ^ 64)%Z ->
  zopz0zKzJ_u (mword_of_int a : mword 64) (mword_of_int c : mword 64) = Z.geb a c.
Proof.
  intros Ha Hc. unfold zopz0zKzJ_u.
  rewrite !uint_unsigned !moi64_unsigned !bvw64_small;
    [reflexivity | exact Hc | exact Ha].
Qed.

(* [c.addiw rd,rd,k] on a small non-negative counter: the COMPRESSED
   immediate is a 6-bit field sign-extended twice, so the law is stated over
   the 64-bit value [k] that field denotes rather than over the field --
   which keeps one lemma for every [c.addiw] rather than one per constant.
   [w32_addw_moi]'s twin for the immediate form. *)
Lemma w32_caddiw_moi (z k : Z) (i6 : mword 6) :
  (sign_extend' 64 (sign_extend' 12 i6) : mword 64) = (mword_of_int k : mword 64) ->
  (0 <= z + k < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64) (sign_extend' 64 (sign_extend' 12 i6))) 31 0 : mword 32)
  = (mword_of_int (z + k) : mword 64).
Proof.
  intros Hk Hzk. rewrite Hk.
  rewrite <- trunc32_subrange. rewrite trunc32_add !trunc32_mword_of_int w32_addv.
  apply w32_sext_moi. exact Hzk.
Qed.

(* ---- a uint ARGUMENT AT THE FULL 32-BIT RANGE ----------------------

   Everything above is about a counter the code itself produced, and so is
   below 2^31.  An ARGUMENT is not: RV64 passes a 32-bit argument
   SIGN-EXTENDED, [uint] included, so a caller's [uint] at or above 2^31
   arrives in its register as a NEGATIVE 64-bit word.  A contract that pins
   that register to [mword_of_int x] therefore confines its parameter to
   [0, 2^31) and cannot be widened -- no compiled caller ever puts the
   zero-extended word there.  [SpecReadi]'s [off] and [n] are the worked
   instance (design/fs-inode.md, "readi takes off and n at the FULL 32-bit
   range").

   [w32_uarg x] is what such a word is worth as an UNSIGNED 64-bit number --
   the number a [bltu]/[bgeu] actually compares -- and the three orderings
   below it are what a proof about those compares needs: a sign-extended
   negative word is ABOVE every small bound, and a value that is at most a
   small bound is not sign-extended at all.  Together they are why the
   64-bit compares gcc emits DECIDE the 32-bit unsigned compares the C is
   written in. *)

Definition w32_uarg (x : Z) : Z :=
  if decide (x < 2 ^ 31) then x else x + (2 ^ 64 - 2 ^ 32).

Lemma w32_arg_unsigned (x : Z) : (0 <= x < 2 ^ 32)%Z ->
  bv_unsigned (sign_extend' 64 (mword_of_int x : mword 32) : mword 64)
  = w32_uarg x.
Proof.
  intro Hx. unfold w32_uarg. case_decide as Hs.
  - rewrite (w32_sext_moi x ltac:(lia)) moi64_unsigned.
    apply bvw64_small. change (2 ^ 64)%Z with 18446744073709551616%Z.
    change (2 ^ 31)%Z with 2147483648%Z in Hs. lia.
  - change (2 ^ 31)%Z with 2147483648%Z in Hs.
    change (2 ^ 32)%Z with 4294967296%Z in Hx.
    rewrite sext32_64_moi moi64_mod.
    assert (Hsg : bv_signed (mword_of_int x : mword 32) = x - 4294967296).
    { unfold bv_signed, bv_swrap. rewrite moi32_unsigned.
      rewrite (bvw32_small x ltac:(lia)).
      change (bv_half_modulus (MachineWord.MachineWord.Z_idx 32)) with 2147483648.
      unfold bv_wrap.
      change (bv_modulus (MachineWord.MachineWord.Z_idx 32)) with 4294967296.
      replace (x + 2147483648)
        with (x + 2147483648 - 4294967296 + 1 * 4294967296) by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (x + 2147483648 - 4294967296) 4294967296 ltac:(lia)).
      lia. }
    rewrite Hsg.
    replace ((x - 4294967296) mod 18446744073709551616)
      with ((x - 4294967296 + 1 * 18446744073709551616)
              mod 18446744073709551616)
      by (rewrite Z_mod_plus_full; reflexivity).
    rewrite (Z.mod_small (x - 4294967296 + 1 * 18446744073709551616)
               18446744073709551616 ltac:(lia)).
    change (2 ^ 64)%Z with 18446744073709551616%Z.
    change (2 ^ 32)%Z with 4294967296%Z. lia.
Qed.

(* never below the value itself... *)
Lemma w32_uarg_lb (x : Z) : (x <= w32_uarg x)%Z.
Proof. unfold w32_uarg. case_decide; lia. Qed.

(* ...ABOVE any small bound it exceeds -- a size test that FIRES... *)
Lemma w32_uarg_gt (x y : Z) :
  (y < 2 ^ 31)%Z -> (y < x)%Z -> (y < w32_uarg x)%Z.
Proof. intros Hy Hlt. unfold w32_uarg. case_decide; lia. Qed.

(* ...and the value itself when it is within one -- a size test that does
   NOT fire, which is what leaves the rest of a proof in the literals. *)
Lemma w32_uarg_le (x y : Z) :
  (y < 2 ^ 31)%Z -> (x <= y)%Z -> (w32_uarg x <= y)%Z.
Proof. intros Hy Hle. unfold w32_uarg. case_decide; lia. Qed.

(* [addw rd,rs1,rs2] with rs1 an ABI-passed uint at the full range and rs2 a
   64-bit literal: [addw] truncates both operands before adding, so the sign
   extension is invisible to it and the sum comes back in the same ABI form.
   NO PREMISE -- both sides wrap mod 2^32, which is the honest statement of
   what the instruction does.  A caller's bound on the sum is what makes the
   RESULT DENOTE that sum ([w32_arg_unsigned] on [a + c], which is where
   [SpecReadi]'s joint [off + n < 2^32] is really used) rather than its
   wrap. *)
Lemma w32_addw_arg (a c : Z) :
  sign_extend' 64
    (add_vec (subrange_vec_dec
                (sign_extend' 64 (mword_of_int a : mword 32) : mword 64) 31 0
              : mword 32)
             (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32))
  = (sign_extend' 64 (mword_of_int (a + c) : mword 32) : mword 64).
Proof.
  rewrite <- !trunc32_subrange.
  rewrite trunc32_sext64 trunc32_mword_of_int w32_addv. reflexivity.
Qed.

(* [add_vec zero_reg x = x] -- what every [c.mv] produces. *)
Lemma w32_zero_add (x : mword 64) : add_vec zero_reg x = x.
Proof.
  apply bv_eq. rewrite add_vec64_unsigned.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz. rewrite Z.add_0_l.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* ===================================================================== *)
(*  Bytes and power-of-two masks.                                         *)
(* ===================================================================== *)

(* a 64-bit word is the literal of its own unsigned reading *)
Lemma w32_moi_unsigned (x : mword 64) : (mword_of_int (bv_unsigned x) : mword 64) = x.
Proof.
  apply bv_eq. rewrite moi64_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [andi rd,rs,2^k-1] -- a ring index.  Stated over the MASK's value rather
   than over a literal, so the console's [% 128] and the pipe's [% 512] are
   the same lemma.  The [bv_unsigned] premise is what a call site closes with
   [vm_compute]; it cannot be inferred, because the immediate is a [mword 12]
   that has to be sign-extended first. *)
Lemma w32_and_mask_bound (x : mword 64) (msk : mword 12) (k : Z) :
  (0 <= k)%Z ->
  bv_unsigned (sign_extend' 64 msk : mword 64) = Z.ones k ->
  (0 <= bv_unsigned (and_vec x (sign_extend' 64 msk)) < 2 ^ k)%Z.
Proof.
  intros Hk Hm. rewrite and_vec64_unsigned Hm Z.land_ones; [| exact Hk].
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* the two literal comparisons a [beq] against a small constant makes, as
   decidable equalities on [Z] -- so the arm is a [destruct] on [Z.eqb]. *)
Lemma w32_eq_moi (a b : Z) :
  (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  eq_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.eqb a b.
Proof.
  intros Ha Hb. destruct (Z.eqb a b) eqn:Hab.
  - apply Z.eqb_eq in Hab. subst. apply eq_vec_true_iff. reflexivity.
  - apply Z.eqb_neq in Hab. apply eq_vec_false_iff. intro Hc.
    apply (f_equal bv_unsigned) in Hc. rewrite !moi64_unsigned in Hc.
    rewrite (bvw64_small a Ha) (bvw64_small b Hb) in Hc. contradiction.
Qed.

Lemma w32_neq_moi (a b : Z) :
  (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  neq_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64) = negb (Z.eqb a b).
Proof. intros Ha Hb. unfold neq_vec. rewrite (w32_eq_moi a b Ha Hb). reflexivity. Qed.

(* [lbu] delivers a zero-extended byte, and [sext.w] then reads it as the
   literal it is; both facts are about the same small non-negative value, and
   the zero-extension is the identity on the unsigned reading, so what is left
   is only the wrap-away. *)
Lemma w32_byte_range (db : mword 8) : (0 <= bv_unsigned db < 256)%Z.
Proof. exact (bv_unsigned_in_range 8 db). Qed.

Lemma w32_zext8_moi (db : mword 8) :
  (zero_extend' 64 db : mword 64) = (mword_of_int (bv_unsigned db) : mword 64).
Proof.
  apply bv_eq. rewrite moi64_unsigned.
  rewrite (bvw64_small (bv_unsigned db) ltac:(pose proof (w32_byte_range db); lia)).
  reflexivity.
Qed.

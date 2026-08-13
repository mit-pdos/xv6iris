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

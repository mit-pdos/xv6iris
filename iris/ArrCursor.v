(* ArrCursor.v -- the strided array cursor that an initializer loop walks, and
   the two pure facts such a loop needs about it.

   Every "initialize each element of a global array" loop in the kernel --
   binit over bcache.buf[], iinit over itable.inode[] -- keeps a pointer
   register stepping by the element stride and stops when it reaches a
   precomputed end pointer one past the last element.  [acur base stride i] is
   that pointer at element [i]; [acur_step] is the loop's [addi cur,cur,stride]
   and [acur_neq] turns its [bne cur,end] test into the index comparison
   [i =? n], which is what the fuel induction runs on.

   Stated over an arbitrary base/stride (no no-wrap assumption beyond the one
   the compare genuinely needs) rather than per array, so a new array-walking
   loop reuses it instead of re-deriving the bitvector arithmetic. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvExtras.
Local Open Scope Z_scope.

(* the cursor at element [i] of an array of [stride]-byte elements based at
   [base]; [acur base stride n] is the loop's end pointer for [n] elements. *)
Definition acur (base stride : Z) (i : nat) : mword 64 :=
  mword_of_int (base + stride * Z.of_nat i).

(* the loop's pointer bump.  [o] is the increment as the instruction spells it
   (a sign-extended 12-bit immediate at the use site), passed as a premise so
   the caller discharges the widening by [vm_compute] on its own literal. *)
Lemma acur_step (base stride : Z) (i : nat) (o : mword 64) :
  o = (mword_of_int stride : mword 64) ->
  add_vec (acur base stride i) o = acur base stride (S i).
Proof.
  intros ->. unfold acur.
  change (add_vec (mword_of_int (base + stride * Z.of_nat i) : mword 64) (mword_of_int stride))
    with (add_vec_int (mword_of_int (base + stride * Z.of_nat i) : mword 64) stride).
  rewrite avi_mword. f_equal. rewrite Nat2Z.inj_succ. ring.
Qed.

(* [mword_of_int] is [Z_to_bv], so its value is the wrapped literal.  (The same
   identity is proved inside [WpMemsetS]'s Iris section as [moi_unsigned]; this
   file is deliberately Iris-free, so it carries its own copy rather than
   pulling a whole WP file in for one bitvector fact.) *)
Lemma acur_moi_unsigned (k : Z) : bv_unsigned (mword_of_int k : mword 64) = bv_wrap 64 k.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* the cursor's numeric value: in range for every index the loop visits,
   so the address arithmetic never wraps. *)
Lemma acur_unsigned (base stride : Z) (i n : nat) :
  0 <= base -> 0 < stride ->
  base + stride * Z.of_nat n < 2 ^ 64 -> (i <= n)%nat ->
  bv_unsigned (acur base stride i) = base + stride * Z.of_nat i.
Proof.
  intros Hb Hs Hend Hin.
  assert (Hmod64 : bv_modulus 64 = 2 ^ 64) by (unfold bv_modulus; f_equal).
  assert (Hile : (stride * Z.of_nat i <= stride * Z.of_nat n)%Z)
    by (apply Z.mul_le_mono_nonneg_l; [lia | apply inj_le; exact Hin]).
  unfold acur. rewrite acur_moi_unsigned. apply bv_wrap_small.
  rewrite Hmod64. split; [| lia].
  apply Z.add_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; lia].
Qed.

(* the loop's exit test.  Both cursors are in range (the array does not wrap),
   so the address compare is exactly the index compare. *)
Lemma acur_neq (base stride : Z) (i n : nat) :
  0 <= base -> 0 < stride ->
  base + stride * Z.of_nat n < 2 ^ 64 ->
  (i <= n)%nat ->
  neq_vec (acur base stride i) (acur base stride n) = negb (Nat.eqb i n).
Proof.
  intros Hb Hs Hend Hin.
  pose proof (acur_unsigned base stride i n Hb Hs Hend Hin) as Hui.
  pose proof (acur_unsigned base stride n n Hb Hs Hend (Nat.le_refl n)) as Hun.
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec i n) as [-> | Hne].
  - apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite Hui, Hun in Hc.
    assert (Hi : Z.of_nat i = Z.of_nat n) by nia.
    apply Nat2Z.inj in Hi. contradiction.
Qed.

(* the cursor is injective on the indices a loop visits: distinct elements of
   the array are distinct addresses.  ([acur_neq] gives this for the end
   pointer; this is the general form, used to keep the per-element resources
   apart.) *)
Lemma acur_inj (base stride : Z) (i j n : nat) :
  0 <= base -> 0 < stride ->
  base + stride * Z.of_nat n < 2 ^ 64 ->
  (i <= n)%nat -> (j <= n)%nat ->
  acur base stride i = acur base stride j -> i = j.
Proof.
  intros Hb Hs Hend Hin Hjn Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (acur_unsigned base stride i n Hb Hs Hend Hin) in Heq.
  rewrite (acur_unsigned base stride j n Hb Hs Hend Hjn) in Heq.
  apply Nat2Z.inj. nia.
Qed.

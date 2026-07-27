(* ByteCursor.v -- the BYTE cursor a memory fill/copy loop walks, and the pure
   facts such a loop needs about it.

   Every byte-at-a-time loop in the kernel -- memset's fill, memmove's copy --
   keeps one or two pointer registers stepping by a single byte and stops when a
   cursor reaches a precomputed end pointer [base + len].  The cursor at byte
   [j] is just [pa_add base j], the same indexing the caller's buffer resource
   ([∗ list] j ∈ seq 0 len, pa_add base j ↦ₘ _) uses, so nothing has to be
   translated at the loop boundary.  What a loop then needs is: the pointer bump
   ([pa_add_step], and [pa_add_back1] for the [-1(reg)] displacement gcc emits
   when it bumps before accessing), the end-pointer compare read back as an
   index compare ([pa_add_cmp_bound]), and the [(unsigned int)] count truncation
   the C source performs on the count argument ([slli32_srli32]).

   Stated over a SYMBOLIC base with no no-wrap assumption -- a buffer that wraps
   the address space is fine, since the cursor wraps exactly as [pa_add] does --
   so a new byte-walking loop reuses these instead of re-deriving the bitvector
   arithmetic.  This is the byte-granularity, symbolic-base counterpart of
   [ArrCursor.v] (strided elements at a CONCRETE base). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang RiscvExtras.
Local Open Scope Z_scope.

(* the two bitvector identities everything below runs on, restated here (as
   [ArrCursor] does) so this file sits in the definitional layer and needs no
   function's WP file. *)
Lemma bc_add_vec_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma bc_moi_unsigned (k : Z) : bv_unsigned (mword_of_int k : mword 64) = bv_wrap 64 k.
Proof.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [add_vec] is commutative -- the end pointer is [base + len] or [len + base]
   depending on which operand register the [add] put in rs1. *)
Lemma add_vec_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof. apply bv_eq. rewrite !bc_add_vec_unsigned. f_equal. ring. Qed.

(* the cursor bump.  [o] is the increment as the INSTRUCTION spells it (a
   sign-extended immediate at the use site), passed as a premise so the caller
   discharges the widening by [vm_compute] on its own closed literal. *)
Lemma pa_add_step (p : mword 64) (j : nat) (o : mword 64) :
  o = (mword_of_int 1 : mword 64) ->
  add_vec (pa_add p j) o = pa_add p (S j).
Proof.
  intros ->. unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(* ...and its dual: gcc bumps the pointer FIRST and then accesses [-1(reg)], so
   the access address is the cursor one below the bumped one. *)
Lemma pa_add_back1 (p : mword 64) (j : nat) (o : mword 64) :
  o = (mword_of_int (-1) : mword 64) ->
  add_vec (pa_add p (S j)) o = pa_add p j.
Proof.
  intros ->. unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(* the end-pointer compare is spelled with whichever operand the [bne] happens
   to put in rs1, so the index reading below is needed in both orders. *)
Lemma neq_vec_comm {m : Z} (x y : mword m) : neq_vec x y = neq_vec y x.
Proof.
  unfold neq_vec. f_equal.
  destruct (eq_vec x y) eqn:E.
  - apply eq_vec_true_iff in E. symmetry. apply eq_vec_true_iff. congruence.
  - apply eq_vec_false_iff in E. symmetry. apply eq_vec_false_iff. congruence.
Qed.

(* the loop's end-pointer compare [p+(j+1) =? p+len] reflects the offset compare
   [(j+1) =? len].  The two addresses differ by [len - (j+1)], a nonzero residue
   mod 2^64 for every 0 < j+1 < len < 2^64, so NO no-wrap assumption on
   [p .. p+len) is needed: if the buffer wraps the address space the cursor wraps
   with it, exactly as the caller's [pa_add]-indexed buffer does. *)
Lemma pa_add_cmp_bound (p : mword 64) (len j : nat) :
  Z.of_nat len < 2 ^ 64 -> (j < len)%nat ->
  neq_vec (pa_add p (S j)) (add_vec (mword_of_int (Z.of_nat len) : mword 64) p)
    = negb (Nat.eqb (S j) len).
Proof.
  intros Hlen Hj.
  assert (Hmod64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E64 in Hlen.
  (* both addresses, as the wrapped sum of the base and the offset *)
  (* NB the [: mword 64] ascription: [pa_add] lands in [Arch.pa], whose width is
     an unreduced [Z_idx (if xlen =? 32 then .. else ..)] match, and a
     [bv_unsigned] elaborated at THAT width does not rewrite in a goal stated at
     width 64. *)
  assert (HxL : bv_unsigned (pa_add p (S j) : mword 64) = bv_wrap 64 (bv_unsigned p + Z.of_nat (S j))).
  { unfold pa_add, add_vec_int. rewrite bc_add_vec_unsigned, bc_moi_unsigned.
    rewrite bv_wrap_add_idemp_r. reflexivity. }
  assert (HeL : bv_unsigned (add_vec (mword_of_int (Z.of_nat len) : mword 64) p)
              = bv_wrap 64 (bv_unsigned p + Z.of_nat len)).
  { rewrite bc_add_vec_unsigned, bc_moi_unsigned.
    rewrite bv_wrap_add_idemp_l. f_equal. lia. }
  unfold neq_vec. f_equal.
  destruct (Nat.eqb_spec (S j) len) as [He | Hne].
  - apply eq_vec_true_iff. apply bv_eq. rewrite HxL, HeL, He. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite HxL, HeL in Hc. unfold bv_wrap in Hc.
    (* equal residues => the modulus divides [len - (j+1)], which is too small *)
    assert (Hd : (((bv_unsigned p + Z.of_nat len) - (bv_unsigned p + Z.of_nat (S j)))
                    mod bv_modulus 64 = 0)%Z).
    { rewrite Zminus_mod. rewrite Hc. rewrite Z.sub_diag. apply Zmod_0_l. }
    replace ((bv_unsigned p + Z.of_nat len) - (bv_unsigned p + Z.of_nat (S j)))%Z
      with (Z.of_nat len - Z.of_nat (S j))%Z in Hd by lia.
    rewrite Z.mod_small in Hd; [ lia | rewrite Hmod64; lia ].
Qed.

(* the C source computes the byte count as [(unsigned int)n], i.e. [n << 32 >> 32]
   in a 64-bit register; for a count that already fits in 32 bits this round-trip
   is the identity. *)
Lemma slli32_srli32 (x : mword 64) :
  bv_unsigned x < 2 ^ 32 ->
  shift_bits_right
    (shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0) = x.
Proof.
  intro Hx.
  assert (Hl : shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : shift_bits_right (shiftl x 32) (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr (shiftl x 32) 32).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl, Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left, MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned, bv_shiftl_unsigned.
  assert (H32 : bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 32)) = 32).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H32.
  pose proof (bv_unsigned_in_range 64 x) as [Hx0 _].
  assert (E32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  assert (Hmul_nonneg : 0 <= bv_unsigned x * 2 ^ 32)
    by (apply Z.mul_nonneg_nonneg; [ exact Hx0 | rewrite E32; lia ]).
  assert (Hmul_lt : bv_unsigned x * 2 ^ 32 < 2 ^ 64)
    by (rewrite E32 in Hx |- *; rewrite E64; nia).
  rewrite Z.shiftl_mul_pow2; [| lia].
  assert (Hmod : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 64)
    by (unfold bv_modulus; f_equal).
  rewrite bv_wrap_small; [| rewrite Hmod; split; [ exact Hmul_nonneg | exact Hmul_lt ] ].
  rewrite Z.shiftr_div_pow2; [| lia].
  rewrite Z.div_mul; [ reflexivity | rewrite E32; lia ].
Qed.

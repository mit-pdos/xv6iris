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
   [ArrCursor.v] (strided elements at a CONCRETE base).

   The second half of the file is the LOOP-COUNTER arithmetic the same loops
   need: a byte count lives in a register as [mword_of_int (Z.of_nat k)], and
   every branch/bump the compiler emits on it -- the zero test, the unsigned
   compare, the [sub], the pointer bump -- has to be read back as the
   corresponding fact about [k].  copyin and copyout each proved that block
   for themselves before it was collected here; do not re-derive it. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvExtras.
Local Open Scope Z_scope.

(* the three bitvector identities everything below runs on, restated off
   [RiscvExtras] (as [ArrCursor] does) so callers need only this file. *)
Lemma bc_add_vec_unsigned (x y : mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof. exact (add_vec64_unsigned x y). Qed.

(* ...and its [sub_vec] counterpart, which the tree had under no name at all
   before this (it was inlined in [WpHolding] and [KstackArith] and proved
   twice more inside the two copy proofs). *)
Lemma bc_sub_vec_unsigned (x y : mword 64) :
  bv_unsigned (sub_vec x y) = bv_wrap 64 (bv_unsigned x - bv_unsigned y).
Proof. exact (sub_vec64_unsigned x y). Qed.

Lemma bc_moi_unsigned (k : Z) : bv_unsigned (mword_of_int k : mword 64) = bv_wrap 64 k.
Proof. exact (moi64_unsigned k). Qed.

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

(* the same bump by an arbitrary count held in a register -- a CHUNK-at-a-time
   loop (copyin's [add s5,s5,s1], copyout's [add s6,s6,s2]) moves the cursor by
   the chunk length, not by 1. *)
Lemma pa_add_bump (p : mword 64) (d n : nat) :
  add_vec (pa_add p d) (mword_of_int (Z.of_nat n)) = pa_add p (d + n).
Proof.
  unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite !bv_wrap_add_idemp_r, !bv_wrap_add_idemp_l. f_equal.
  rewrite Nat2Z.inj_add. ring.
Qed.

(* ...with the operands the other way round, which is how the encoder spells it
   when the count register is rs1 (copyin's [add a1,a1,a0] at +0x38). *)
Lemma pa_add_comm (p : mword 64) (k : nat) :
  add_vec (mword_of_int (Z.of_nat k) : mword 64) p = pa_add p k.
Proof. unfold pa_add, add_vec_int. apply add_vec_comm. Qed.

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

(* two DISTINCT residues below the modulus never differ by a multiple of it.
   Kept mword-FREE and stated over a symbolic modulus so [lia] works normally
   here (durable-notes' zify-hook rule); every address-compare lemma below
   discharges its "the addresses differ" side through this. *)
Lemma bc_mod_diff_nonzero (m x y : Z) :
  (0 < m)%Z -> (0 <= x < m)%Z -> (0 <= y < m)%Z -> x <> y -> ((x - y) mod m <> 0)%Z.
Proof.
  intros Hm Hx Hy Hne Hd.
  destruct (Z.le_gt_cases y x) as [Hle | Hgt].
  - rewrite Z.mod_small in Hd; lia.
  - assert (Hd' : ((y - x) mod m = 0)%Z).
    { replace (y - x)%Z with (- (x - y))%Z by lia.
      rewrite Z.mod_opp_l_z; [reflexivity | lia | exact Hd]. }
    rewrite Z.mod_small in Hd'; lia.
Qed.

(* the cursor's unsigned value, once and for all.  NB the [: mword 64]
   ascription: [pa_add] lands in [Arch.pa], whose width is an unreduced
   [Z_idx (if xlen =? 32 then .. else ..)] match, and a [bv_unsigned]
   elaborated at THAT width does not rewrite in a goal stated at width 64. *)
Lemma pa_add_unsigned (p : mword 64) (k : nat) :
  bv_unsigned (pa_add p k : mword 64) = bv_wrap 64 (bv_unsigned p + Z.of_nat k).
Proof.
  unfold pa_add, add_vec_int. rewrite bc_add_vec_unsigned, bc_moi_unsigned.
  rewrite bv_wrap_add_idemp_r. reflexivity.
Qed.

(* the base fact every pointer-vs-pointer branch in a byte loop rests on:
   [p+a =? p+b] reflects the INDEX compare [a =? b].  The two addresses differ
   by [a - b], a nonzero residue mod 2^64 for any two distinct indices below
   2^64, so NO no-wrap assumption on the buffer is needed -- if the buffer wraps
   the address space the cursors wrap with it, exactly as the caller's
   [pa_add]-indexed resource does. *)
Lemma pa_add_eqb (p : mword 64) (a b : nat) :
  (Z.of_nat a < 18446744073709551616)%Z -> (Z.of_nat b < 18446744073709551616)%Z ->
  eq_vec (pa_add p a) (pa_add p b) = Nat.eqb a b.
Proof.
  intros Ha Hb.
  assert (Hmod64 : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  pose (Hu := pa_add_unsigned p).
  destruct (Nat.eqb_spec a b) as [He | Hne].
  - apply eq_vec_true_iff. apply bv_eq. rewrite !Hu, He. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite !Hu in Hc. unfold bv_wrap in Hc.
    (* equal residues => the modulus divides [a - b], which is too small *)
    assert (Hd : (((bv_unsigned p + Z.of_nat a) - (bv_unsigned p + Z.of_nat b))
                    mod bv_modulus 64 = 0)%Z).
    { rewrite Zminus_mod. rewrite Hc. rewrite Z.sub_diag. apply Zmod_0_l. }
    replace ((bv_unsigned p + Z.of_nat a) - (bv_unsigned p + Z.of_nat b))%Z
      with (Z.of_nat a - Z.of_nat b)%Z in Hd by ring.
    refine (bc_mod_diff_nonzero (bv_modulus 64) _ _ _ _ _ _ Hd).
    + rewrite Hmod64. lia.
    + rewrite Hmod64. split; [apply Nat2Z.is_nonneg | exact Ha].
    + rewrite Hmod64. split; [apply Nat2Z.is_nonneg | exact Hb].
    + intro Hz. apply Hne. apply Nat2Z.inj. exact Hz.
Qed.

(* the loop's end-pointer compare, in the spelling memmove's [bne] produces
   (the end pointer built as [len + base], so the operands are the other way
   round) -- the [c = 0] instance of [pa_add_eqb] through [pa_add_comm]. *)
Lemma pa_add_cmp_bound (p : mword 64) (len j : nat) :
  Z.of_nat len < 2 ^ 64 -> (j < len)%nat ->
  neq_vec (pa_add p (S j)) (add_vec (mword_of_int (Z.of_nat len) : mword 64) p)
    = negb (Nat.eqb (S j) len).
Proof.
  intros Hlen Hj.
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite E64 in Hlen.
  (* [lia] cannot be trusted on a bound against a big literal in this file (the
     bitvector zify hook), so the two premises are staged by hand. *)
  assert (HSj : (Z.of_nat (S j) < 18446744073709551616)%Z).
  { apply (Z.le_lt_trans _ (Z.of_nat len)); [apply Nat2Z.inj_le; lia | exact Hlen]. }
  rewrite (pa_add_comm p len). unfold neq_vec.
  rewrite (pa_add_eqb p (S j) len HSj Hlen). reflexivity.
Qed.

(* the OTHER reading of two cursors off one base: their DIFFERENCE.  copyinstr
   recovers the bytes still to go as [(base + (rem-1)) - (base + (n-1))], the
   [sub s3,a4,a1] its outer loop advances with. *)
Lemma pa_add_diff (p : mword 64) (a b : nat) :
  (b <= a)%nat -> (Z.of_nat a < 18446744073709551616)%Z ->
  sub_vec (pa_add p a) (pa_add p b) = (mword_of_int (Z.of_nat (a - b)) : mword 64).
Proof.
  intros Hle Ha. apply bv_eq.
  pose (Hu := pa_add_unsigned p).
  rewrite bc_sub_vec_unsigned, !Hu, bc_moi_unsigned.
  rewrite bv_wrap_sub_idemp_l, bv_wrap_sub_idemp_r.
  f_equal. rewrite (Nat2Z.inj_sub a b Hle). ring.
Qed.

(* ...and the cursor gcc reconstructs from a PRE-COMPUTED DIFFERENCE: copyinstr's
   inner loop keeps [a2 = src - dst] and forms the source address as
   [a2 + (dst + i)], so the base cancels. *)
Lemma pa_add_delta (x p : mword 64) (i : nat) :
  add_vec (sub_vec x p) (pa_add p i) = pa_add x i.
Proof.
  apply bv_eq.
  rewrite bc_add_vec_unsigned, bc_sub_vec_unsigned, !pa_add_unsigned.
  rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  f_equal. ring.
Qed.

(* two bumps off one base collapse into one.  A CHUNKED byte loop states its
   outer cursor as [pa_add dst done] and its inner one relative to THAT, while
   the caller's buffer is indexed from [dst] -- so every address the inner loop
   forms has to be brought back to the caller's indexing through this. *)
Lemma pa_add_assoc (p : mword 64) (a b : nat) :
  pa_add (pa_add p a) b = pa_add p (a + b).
Proof. exact (pa_add_bump p a b). Qed.

(* the SOURCE pointer copyinstr forms, [(pa0 + srcva) - va0]: whatever the
   in-page offset [srcva - va0] turns out to be, adding it to the page base
   lands at that offset in the page.  The offset arrives as a premise, since
   only the caller knows it (it comes out of [ProcPtOwn.pgd_off]). *)
Lemma pa_add_of_diff (q c v : mword 64) (off : nat) :
  sub_vec c v = (mword_of_int (Z.of_nat off) : mword 64) ->
  sub_vec (add_vec q c) v = pa_add q off.
Proof.
  intro Hoff.
  apply (f_equal bv_unsigned) in Hoff.
  rewrite bc_sub_vec_unsigned, bc_moi_unsigned in Hoff.
  apply bv_eq.
  rewrite bc_sub_vec_unsigned, bc_add_vec_unsigned, pa_add_unsigned.
  rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned q + bv_unsigned c - bv_unsigned v)%Z
    with (bv_unsigned q + (bv_unsigned c - bv_unsigned v))%Z by ring.
  rewrite <- bv_wrap_add_idemp_r, Hoff, bv_wrap_add_idemp_r.
  reflexivity.
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

(* [srli rd,rs,0xc] -- the same decoder spelling of the shift amount as
   [slli32_srli32] above, at 12: the instruction is unsigned division by the
   page size.  (uvmdealloc's [npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz))
   / PGSIZE].) *)
Local Lemma bc_z_div4096_range (v : Z) :
  0 <= v < 18446744073709551616 -> 0 <= v / 4096 < 18446744073709551616.
Proof.
  intros [H0 H1]. split; [apply Z.div_pos; lia |].
  apply Z.le_lt_trans with v; [| lia]. apply Z.div_le_upper_bound; lia.
Qed.

Lemma srli12_div4096 (x : mword 64) :
  shift_bits_right x (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (bv_unsigned x / 4096) : mword 64).
Proof.
  assert (Hr : shift_bits_right x
                 (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr x 12).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hr. apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (H12 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12)) = 12).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H12. rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  rewrite moi64_unsigned. symmetry. apply bvw64_small.
  apply bc_z_div4096_range.
  pose proof (bv_unsigned_in_range _ x) as Hr64.
  assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    by (vm_compute; reflexivity).
  rewrite Hm in Hr64. exact Hr64.
Qed.

(* ===================================================================== *)
(*  THE LOOP COUNTER.                                                     *)
(*                                                                        *)
(*  A byte count / remaining length lives in a register as                *)
(*  [mword_of_int (Z.of_nat k)].  These are the reads-back of every        *)
(*  instruction a chunked copy loop applies to it: the zero test the       *)
(*  [beqz] decides, the unsigned compare the [bgeu] decides, the [sub]     *)
(*  that decrements it, and the [uint] a caller's premise mentions.        *)
(* ===================================================================== *)

Lemma bc_bvmod64 : bv_modulus 64 = 18446744073709551616.
Proof. vm_compute; reflexivity. Qed.

Lemma bc_wrap_small (z : Z) : 0 <= z -> z < 18446744073709551616 -> bv_wrap 64 z = z.
Proof.
  intros H0 H1. unfold bv_wrap. rewrite bc_bvmod64. apply Z.mod_small. split; assumption.
Qed.

Lemma bc_moi_small (z : Z) : 0 <= z < 18446744073709551616 ->
  bv_unsigned (mword_of_int z : mword 64) = z.
Proof. intros [H0 H1]. rewrite bc_moi_unsigned. apply bc_wrap_small; assumption. Qed.

Lemma bc_zero_reg_unsigned : bv_unsigned (zero_reg : mword 64) = 0.
Proof. vm_compute; reflexivity. Qed.

Lemma bc_uint_moi_nat (k : nat) :
  (Z.of_nat k < 18446744073709551616)%Z ->
  uint (mword_of_int (Z.of_nat k) : mword 64) = Z.of_nat k.
Proof.
  intro Hk. rewrite uint_unsigned. apply bc_moi_small.
  split; [apply Nat2Z.is_nonneg | exact Hk].
Qed.

(* a cursor bumped by an IMMEDIATE, read back as the unsigned sum -- the
   non-wrapping case, where the caller already knows the running value.
   (uvmalloc's [a += PGSIZE].) *)
Lemma bc_add_moi (x : mword 64) (b k : Z) :
  bv_unsigned x = b -> 0 <= b -> 0 <= k -> b + k < 18446744073709551616 ->
  bv_unsigned (add_vec x (mword_of_int k)) = b + k.
Proof.
  intros Hx H0 Hk Hb.
  rewrite bc_add_vec_unsigned, Hx, (bc_moi_small k ltac:(lia)).
  apply bc_wrap_small; lia.
Qed.

(* the zero test a [beqz]/[bnez] on the counter decides *)
Lemma bc_eqz_moi (k : nat) : (Z.of_nat k < 18446744073709551616)%Z ->
  eq_vec (mword_of_int (Z.of_nat k) : mword 64) zero_reg = Nat.eqb k 0.
Proof.
  intro Hk.
  assert (Hzr : (zero_reg : mword 64) = mword_of_int 0)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hzr.
  destruct (Nat.eqb_spec k 0) as [-> | Hne].
  - apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
    rewrite (bc_moi_small (Z.of_nat k) ltac:(lia)) in Hc.
    rewrite (bc_moi_small 0 ltac:(lia)) in Hc. lia.
Qed.

(* the two one-sided readings of it that the branch arms want directly *)
Lemma bc_moi_iszero : eq_vec (mword_of_int 0 : mword 64) zero_reg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma bc_moi_nonzero (k : nat) :
  (Z.of_nat k < 18446744073709551616)%Z -> (k <> 0)%nat ->
  eq_vec (mword_of_int (Z.of_nat k) : mword 64) zero_reg = false.
Proof.
  intros Hk Hne. rewrite (bc_eqz_moi k Hk). apply Nat.eqb_neq. exact Hne.
Qed.

(* the unsigned compare a [bgeu] decides, at ARBITRARY operands -- the two
   one-sided readings.  A loop that compares two ADDRESSES (uvmunmap's
   [a < va + npages*PGSIZE]) has no [mword_of_int (Z.of_nat _)] to appeal to,
   so it wants the compare stated directly over [bv_unsigned]. *)
Lemma bc_geu (x y : mword 64) :
  (bv_unsigned y <= bv_unsigned x)%Z -> zopz0zKzJ_u x y = true.
Proof.
  intro H. unfold zopz0zKzJ_u. rewrite !uint_unsigned. rewrite Z.geb_leb.
  apply Z.leb_le. exact H.
Qed.

Lemma bc_ltu (x y : mword 64) :
  (bv_unsigned x < bv_unsigned y)%Z -> zopz0zKzJ_u x y = false.
Proof.
  intro H. unfold zopz0zKzJ_u. rewrite !uint_unsigned. rewrite Z.geb_leb.
  apply Z.leb_gt. exact H.
Qed.

(* ...and the counter-flavoured instance, off the same two readings *)
Lemma bc_ge_moi (a b : nat) :
  (Z.of_nat a < 18446744073709551616)%Z -> (Z.of_nat b < 18446744073709551616)%Z ->
  zopz0zKzJ_u (mword_of_int (Z.of_nat a) : mword 64) (mword_of_int (Z.of_nat b))
  = Nat.leb b a.
Proof.
  intros Ha Hb.
  destruct (Nat.leb_spec b a) as [Hle | Hlt].
  - apply bc_geu.
    rewrite (bc_moi_small (Z.of_nat a) ltac:(lia)).
    rewrite (bc_moi_small (Z.of_nat b) ltac:(lia)). lia.
  - apply bc_ltu.
    rewrite (bc_moi_small (Z.of_nat a) ltac:(lia)).
    rewrite (bc_moi_small (Z.of_nat b) ltac:(lia)). lia.
Qed.

(* the decrement *)
Lemma bc_sub_nat (a b : nat) :
  (b <= a)%nat -> (Z.of_nat a < 18446744073709551616)%Z ->
  sub_vec (mword_of_int (Z.of_nat a) : mword 64) (mword_of_int (Z.of_nat b))
  = (mword_of_int (Z.of_nat (a - b)) : mword 64).
Proof.
  intros Hle Ha. apply bv_eq.
  rewrite bc_sub_vec_unsigned.
  rewrite (bc_moi_small (Z.of_nat a) ltac:(lia)).
  rewrite (bc_moi_small (Z.of_nat b) ltac:(lia)).
  rewrite bc_moi_unsigned. f_equal.
  rewrite Nat2Z.inj_sub; [reflexivity | exact Hle].
Qed.

(* ...and the decrement gcc spells as an ADD of the immediate -1 rather than a
   [sub] (copyinstr's [addi a4,s3,-1]).  The immediate arrives sign-extended
   from 12 bits, so the caller passes it as a closed [o] it [vm_compute]s. *)
Lemma bc_add_m1_nat (k : nat) (o : mword 64) :
  o = (mword_of_int (-1) : mword 64) ->
  (1 <= k)%nat -> (Z.of_nat k < 18446744073709551616)%Z ->
  add_vec (mword_of_int (Z.of_nat k) : mword 64) o
  = (mword_of_int (Z.of_nat (k - 1)) : mword 64).
Proof.
  intros -> Hk1 Hk. apply bv_eq.
  rewrite bc_add_vec_unsigned, !bc_moi_unsigned.
  rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  f_equal. rewrite (Nat2Z.inj_sub k 1 Hk1).
  change (Z.of_nat 1) with 1%Z. ring.
Qed.

(* ===================================================================== *)
(* The BYTE a loop just loaded, tested against zero.                      *)
(* ===================================================================== *)
(* A [lbu] leaves the byte ZERO-EXTENDED in the register, and a string walk
   then branches on it -- so "the register is zero" has to be read back as
   "the byte is the NUL".  Both directions; the [bv_zero_extend_unsigned]
   side condition is an [N] inequality, which [lia] cannot see under the
   bitvector zify hook, hence the [vm_compute]. *)
Lemma bc_zext8_zero (b : mword 8) :
  eq_vec (zero_extend' 64 b) (zero_reg : mword 64) = true ->
  b = (mword_of_int 0 : mword 8).
Proof.
  intro H. apply eq_vec_true_iff in H.
  apply (f_equal bv_unsigned) in H.
  unfold zero_extend', Operators_mwords.zero_extend, Operators_mwords.extz_vec,
    SailStdpp.Values.to_word, to_word, get_word, MachineWord.MachineWord.zero_extend in H.
  rewrite bv_zero_extend_unsigned in H; [ | vm_compute; intro Hc; discriminate Hc ].
  change (bv_unsigned (zero_reg : mword 64)) with 0%Z in H.
  apply bv_eq. rewrite H. vm_compute. reflexivity.
Qed.

Lemma bc_zext8_nonzero (b : mword 8) :
  b <> (mword_of_int 0 : mword 8) ->
  eq_vec (zero_extend' 64 b) (zero_reg : mword 64) = false.
Proof.
  intro H. destruct (eq_vec (zero_extend' 64 b) (zero_reg : mword 64)) eqn:E;
    [ exfalso; apply H; exact (bc_zext8_zero b E) | reflexivity ].
Qed.

Lemma bc_zext8_iszero :
  eq_vec (zero_extend' 64 (mword_of_int 0 : mword 8)) (zero_reg : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.


(* ===================================================================== *)
(* Two cursors subtracted as C [int]s: [subw rd,rs1,rs2].                 *)
(* ===================================================================== *)
(* A function that returns a POINTER DIFFERENCE as an [int] (strlen's
   [subw a0,a3,a0]) narrows both cursors to 32 bits, subtracts, and
   sign-extends.  For a difference below 2^31 that is exactly the index, no
   matter where the buffer sits: the 32-bit truncation loses only the base,
   which cancels.  Stated over the two register values with the index
   relation as a PREMISE (discharged by [pa_add_unsigned]) so that both
   [subrange_vec_dec]s elaborate at the width-64 the register map gives
   them. *)
(* the [Z] identity, mword-free so [lia] behaves: narrowing both cursors to 32
   bits and subtracting recovers the index, because the base cancels. *)
Lemma bc_subw_arith (b k : Z) :
  (0 <= k < 2147483648)%Z ->
  ((((b + k) mod 18446744073709551616) mod 4294967296) - (b mod 4294967296))
    mod 4294967296 = k.
Proof.
  intro Hk.
  (* 2^32 divides 2^64, so the outer narrowing swallows the inner one *)
  assert (Hmm : forall z : Z,
            ((z mod 18446744073709551616) mod 4294967296)%Z = (z mod 4294967296)%Z).
  { intro z. rewrite (Z.mod_eq z 18446744073709551616 ltac:(lia)).
    replace (z - 18446744073709551616 * (z / 18446744073709551616))%Z
      with (z + (- 4294967296 * (z / 18446744073709551616)) * 4294967296)%Z by ring.
    apply Z_mod_plus_full. }
  rewrite Hmm.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  replace (b + k - b)%Z with k by ring.
  apply Z.mod_small. lia.
Qed.

Lemma bc_subw_diff (x y : mword 64) (k : nat) :
  (Z.of_nat k < 2147483648)%Z ->
  bv_unsigned x = bv_wrap 64 (bv_unsigned y + Z.of_nat k) ->
  sign_extend' 64 (sub_vec (subrange_vec_dec x 31 0 : mword 32)
                           (subrange_vec_dec y 31 0 : mword 32))
  = (mword_of_int (Z.of_nat k) : mword 64).
Proof.
  intros Hk Hxy.
  assert (Hk0 : (0 <= Z.of_nat k)%Z) by apply Nat2Z.is_nonneg.
  set (w := sub_vec (subrange_vec_dec x 31 0 : mword 32)
                    (subrange_vec_dec y 31 0 : mword 32)).
  assert (Hw : bv_unsigned w = Z.of_nat k).
  { unfold w. rewrite sub_vec32_unsigned.
    rewrite !subrange_31_0_unsigned, Hxy.
    unfold bv_wrap.
    assert (Hm32 : (bv_modulus 32 = 4294967296)%Z) by (vm_compute; reflexivity).
    assert (Hm64 : (bv_modulus 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
    rewrite Hm32, Hm64.
    exact (bc_subw_arith (bv_unsigned y) (Z.of_nat k) (conj Hk0 Hk)). }
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  apply bv_eq. rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold bv_signed. rewrite Hw.
  assert (Hhm : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2147483648)
    by (vm_compute; reflexivity).
  rewrite bv_swrap_small;
    [| rewrite Hhm; split; [apply (Z.le_trans _ 0); [lia | exact Hk0] | exact Hk]].
  rewrite bc_moi_unsigned. reflexivity.
Qed.

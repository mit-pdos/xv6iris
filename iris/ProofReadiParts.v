(* ProofReadiParts.v -- readi's vocabulary: everything its proof needs that
   is NOT a step of its instruction chain, so ProofReadi.v stays about
   control flow.  (The ProofBmapParts.v / ProofWriteiParts.v division of
   labour; a Proof file may not import another one, so the lemmas that also
   appear there are re-derived here.)

   Five groups:

   (1) ARITHMETIC.  readi is an arithmetic function: [c.addw]/[addw] for the
       three counters, [subw] for the clamp and the two [min] operands,
       [andi ...,1023] for [off % BSIZE], [srliw ...,0xa] for [off / BSIZE]
       and a [slli 32 / srli 32] pair for the zero-extension of the chunk
       length.  Every one is stated at a NAT literal, because that is what
       the loop invariant carries.

   (2) THE BYTE WINDOW inside a checked-out buffer -- READ-ONLY here, so it
       goes out and comes back at the SAME bytes and the buffer is
       reconstructed unchanged.  (writei's twin splices; readi does not
       modify a block at all.)

   (3) THE DELIVERED BYTES.  [SpecReadi.rd_delivered] is exact on both ends
       -- the file's bytes below [tot], the caller's own above it -- so one
       chunk's effect is three pointwise equalities and no existential.

   (4) THE FUEL.  [rd_blocks_step]: an iteration that fills its block to the
       boundary straddles one block fewer afterwards.  readi has no budget
       (it never touches the log), so this is termination alone.

   (5) THE HANDLE, exactly as in ProofBmapParts.v / ProofWriteiParts.v. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import VcGen.
Require Export W32Arith.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import WpLock.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks.
Require Import InodeInv.
Require Import ProcInv.
Require Import SpecReadi.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (0) nat division by BSIZE                                             *)
(* ===================================================================== *)

Lemma rd_bsize_val : BSIZE = 1024%nat.
Proof. reflexivity. Qed.

Lemma rd_maxfile_val : MAXFILE = 268%nat.
Proof. reflexivity. Qed.

Lemma rd_divmod (k : nat) : k = (BSIZE * (k `div` BSIZE) + k `mod` BSIZE)%nat.
Proof. apply Nat.div_mod_eq. Qed.

Lemma rd_mod_lt (k : nat) : (k `mod` BSIZE < BSIZE)%nat.
Proof. apply Nat.mod_upper_bound. unfold BSIZE. lia. Qed.

(* the byte at index [k] of the file lies in block [fb] exactly when [k] is
   inside that block's own range *)
Lemma rd_div_in (k fb r : nat) :
  (r < BSIZE)%nat -> k = (fb * BSIZE + r)%nat ->
  (k `div` BSIZE)%nat = fb /\ (k `mod` BSIZE)%nat = r.
Proof.
  intros Hr ->.
  assert (Hdiv : ((fb * BSIZE + r) `div` BSIZE)%nat = fb).
  { rewrite Nat.div_add_l; [| unfold BSIZE; lia].
    rewrite Nat.div_small; [lia | exact Hr]. }
  split; [exact Hdiv|].
  pose proof (rd_divmod (fb * BSIZE + r)%nat) as Hdm.
  rewrite Hdiv in Hdm. lia.
Qed.

Lemma rd_fbn_lt (x : nat) : (x < MAXFILE * BSIZE)%nat -> (x `div` BSIZE < MAXFILE)%nat.
Proof.
  intros H. apply Nat.div_lt_upper_bound; [unfold BSIZE; lia|].
  rewrite Nat.mul_comm. exact H.
Qed.

Lemma rd_div_z (x : nat) : Z.of_nat (x `div` BSIZE) = (Z.of_nat x / 1024)%Z.
Proof. rewrite Nat2Z.inj_div. reflexivity. Qed.

Lemma rd_mod_z (x : nat) : Z.of_nat (x `mod` BSIZE) = (Z.of_nat x mod 1024)%Z.
Proof. rewrite Nat2Z.inj_mod. reflexivity. Qed.

(* [bm_covers_off] answers at [Z.to_nat (o / BSIZE)]; the loop carries the
   nat division.  They are the same index. *)
Lemma rd_todiv (a : nat) :
  Z.to_nat (Z.of_nat a / Z.of_nat BSIZE) = (a `div` BSIZE)%nat.
Proof. rewrite -Nat2Z.inj_div Nat2Z.id. reflexivity. Qed.

(* ===================================================================== *)
(*  (1) Arithmetic                                                        *)
(* ===================================================================== *)

(* the small-argument law, at the literal bound readi's own facts are
   stated over; [W32Arith.w32_sext_moi] is the general one *)
Lemma rd_sext32 (z : Z) : 0 <= z -> z < 2147483648 ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intros H0 H1. apply w32_sext_moi.
  split; [lia | change (2 ^ 31)%Z with 2147483648%Z; lia].
Qed.

(* a 32-bit cell round-trips through its unsigned value... *)
Lemma rd_moi32_id (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  apply bv_eq. rewrite moi32_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* ...and a small one survives the ABI's sign extension *)
Lemma rd_sext32_unsigned (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  bv_unsigned (sign_extend' 64 w : mword 64) = bv_unsigned w.
Proof.
  intro Hw. pose proof (bv_unsigned_in_range _ w) as [H0 _].
  rewrite -{1}(rd_moi32_id w).
  rewrite (sext64_moi32_unsigned (bv_unsigned w)
             ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)).
  reflexivity.
Qed.

(* the TERM form: the sign-extended size IS the literal, which is what puts
   the clamp's [subw] at two [mword_of_int]s *)
Lemma rd_sext32_moi (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  (sign_extend' 64 w : mword 64) = mword_of_int (bv_unsigned w).
Proof.
  intro Hw. pose proof (bv_unsigned_in_range _ w) as [H0 _].
  etransitivity; [| exact (rd_sext32 (bv_unsigned w) H0 Hw)].
  rewrite (rd_moi32_id w). reflexivity.
Qed.

(* the file's size, as the nat the loop invariant counts in *)
Lemma rd_size_nat (w : bv 32) : Z.of_nat (Z.to_nat (bv_unsigned w)) = bv_unsigned w.
Proof. apply Z2Nat.id. apply bv_unsigned_in_range. Qed.

Lemma rd_uint_moi (z : Z) : 0 <= z -> z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof.
  intros H0 H1. rewrite RiscvExtras.uint_unsigned moi64_unsigned.
  apply bvw64_small. change (2 ^ 64)%Z with 18446744073709551616%Z. lia.
Qed.

Lemma rd_nat_u (k : nat) : (Z.of_nat k < 18446744073709551616)%Z ->
  bv_unsigned (mword_of_int (Z.of_nat k) : mword 64) = Z.of_nat k.
Proof. intro Hk. apply moi64_small. split; [apply Nat2Z.is_nonneg | exact Hk]. Qed.

(* [addw rd,rs1,rs2] at two small non-negative literals *)
Lemma rd_addw (a c : Z) : 0 <= a -> 0 <= c -> a + c < 2147483648 ->
  sign_extend' 64
    (add_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
             (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32))
  = (mword_of_int (a + c) : mword 64).
Proof.
  intros Ha Hc Hsum.
  rewrite -!trunc32_subrange !trunc32_mword_of_int.
  assert (Hadd : add_vec (mword_of_int a : mword 32) (mword_of_int c : mword 32)
                 = (mword_of_int (a + c) : mword 32)).
  { apply bv_eq. rewrite add_vec_unsigned !moi32_unsigned.
    unfold bv_wrap. change (bv_modulus 32) with 4294967296.
    rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r. reflexivity. }
  rewrite Hadd. apply rd_sext32; lia.
Qed.

(* [subw rd,rs1,rs2] at two small non-negative literals, no borrow *)
Lemma rd_subw (a c : Z) : 0 <= c -> c <= a -> a < 2147483648 ->
  sign_extend' 64
    (sub_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
             (subrange_vec_dec (mword_of_int c : mword 64) 31 0 : mword 32))
  = (mword_of_int (a - c) : mword 64).
Proof.
  intros Hc Hca Ha.
  rewrite -!trunc32_subrange !trunc32_mword_of_int.
  assert (Hsub : sub_vec (mword_of_int a : mword 32) (mword_of_int c : mword 32)
                 = (mword_of_int (a - c) : mword 32)).
  { apply bv_eq. rewrite sub_vec32_unsigned !moi32_unsigned.
    unfold bv_wrap. change (bv_modulus 32) with 4294967296.
    rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r. reflexivity. }
  rewrite Hsub. apply rd_sext32; lia.
Qed.

(* NOTE: the ABI's 32-bit ARGUMENT -- a [uint] at or above 2^31, which
   arrives sign-extended and hence NEGATIVE, as [SpecReadi]'s register
   premises spell it -- is not readi vocabulary and does not live here.  It
   is [W32Arith]'s [w32_uarg] (the word's unsigned value), its three
   orderings and [w32_addw_arg], required above. *)

(* [andi a5,s1,1023] : off % BSIZE *)
Lemma rd_andi1023 (z : Z) : 0 <= z -> z < 2147483648 ->
  and_vec (mword_of_int z : mword 64)
          (sign_extend' 64 (mword_of_int 1023 : mword 12))
  = (mword_of_int (z `mod` 1024) : mword 64).
Proof.
  intros H0 H1.
  assert (He : (sign_extend' 64 (mword_of_int 1023 : mword 12) : mword 64)
               = mword_of_int 1023) by (apply bv_eq; vm_compute; reflexivity).
  rewrite He. apply bv_eq. rewrite and_vec64_unsigned !moi64_unsigned.
  rewrite (bvw64_small z ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (bvw64_small 1023 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  assert (Hones : (1023 = Z.ones 10)%Z) by (vm_compute; reflexivity).
  rewrite Hones Z.land_ones; [| lia].
  change (2 ^ 10)%Z with 1024%Z.
  symmetry. apply bvw64_small.
  pose proof (Z.mod_pos_bound z 1024 ltac:(lia)) as [Hl Hh].
  change (2 ^ 64)%Z with 18446744073709551616%Z. lia.
Qed.

(* [srliw a1,s1,0xa] : off / BSIZE *)
Lemma rd_srliw10 (z : Z) : 0 <= z -> z < 2147483648 ->
  sign_extend' 64
    (shift_bits_right (subrange_vec_dec (mword_of_int z : mword 64) 31 0 : mword 32)
                      (mword_of_int 10 : mword 5))
  = (mword_of_int (z / 1024) : mword 64).
Proof.
  intros H0 H1.
  rewrite -trunc32_subrange trunc32_mword_of_int.
  assert (Hsh : shift_bits_right (mword_of_int z : mword 32) (mword_of_int 10 : mword 5)
                = (mword_of_int (z / 1024) : mword 32)).
  { unfold shift_bits_right.
    apply bv_eq.
    unfold shiftr, SailStdpp.Values.with_word, get_word,
      MachineWord.MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (H10 : bv_unsigned (MachineWord.MachineWord.N_to_word
                     (MachineWord.MachineWord.Z_idx 32)
                     (MachineWord.MachineWord.Z_idx
                        (uint (mword_of_int 10 : mword 5)))) = 10).
    { assert (Hu : uint (mword_of_int 10 : mword 5) = 10)
        by (vm_compute; reflexivity).
      rewrite Hu.
      unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      unfold bv_modulus; simpl; lia. }
    rewrite H10.
    rewrite !moi32_unsigned.
    rewrite (bvw32_small z ltac:(change (2^32)%Z with 4294967296%Z; lia)).
    rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 10)%Z with 1024%Z.
    symmetry. apply bvw32_small.
    assert (Hd : 0 <= z / 1024 <= z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    change (2 ^ 32)%Z with 4294967296%Z. lia. }
  rewrite Hsh. apply rd_sext32.
  - apply Z.div_pos; lia.
  - assert (Hd : z / 1024 <= z) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* [slli s11,s10,0x20 / srli s11,s11,0x20] : the zero-extension of a value
   that already fits in 32 bits is the identity. *)
Lemma rd_zext32 (x : mword 64) :
  bv_unsigned x < 4294967296 ->
  shift_bits_right
    (shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
  = x.
Proof.
  intro Hx.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
  assert (Hl : shift_bits_left x
                 (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : forall v : mword 64,
             shift_bits_right v
               (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr v 32).
  { intro v. unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned bv_shiftl_unsigned.
  assert (H32 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 64)
                   (MachineWord.MachineWord.Z_idx 32)) = 32).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H32.
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2 ^ 32)%Z with 4294967296%Z.
  rewrite (bv_wrap_small 64 (bv_unsigned x * 4294967296)).
  2:{ change (bv_modulus 64) with 18446744073709551616%Z. lia. }
  rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 32)%Z with 4294967296%Z.
  rewrite Z.div_mul; [| lia]. reflexivity.
Qed.

(* the three [c.li]s and the [li s9,1024] *)
Lemma rd_li_m1 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma rd_li_0 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma rd_li_1024 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (mword_of_int 1024 : mword 12))
  = (mword_of_int 1024 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* addresses *)
Lemma rd_pa_add_moi (p : mword 64) (nn : nat) :
  add_vec p (mword_of_int (Z.of_nat nn)) = pa_add p nn.
Proof. reflexivity. Qed.

Lemma rd_data_addr (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
              = mword_of_int (Z.of_nat 88%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H rd_pa_add_moi. reflexivity.
Qed.

(* [c.add a2,a2,a5] and [c.add s4,s4,s11]: the two cursors advance *)
Lemma rd_pa_step (p : mword 64) (a c : nat) :
  add_vec (pa_add p a) (mword_of_int (Z.of_nat c)) = pa_add p (a + c)%nat.
Proof. rewrite rd_pa_add_moi. apply pa_add_add. Qed.

(* the BLTU reading, at nat literals ([ByteCursor.bc_ge_moi] is the BGEU twin) *)
Lemma rd_lt_moi (a c : nat) :
  (Z.of_nat a < 18446744073709551616)%Z -> (Z.of_nat c < 18446744073709551616)%Z ->
  zopz0zI_u (mword_of_int (Z.of_nat a) : mword 64) (mword_of_int (Z.of_nat c))
  = Nat.ltb a c.
Proof.
  intros Ha Hc. unfold zopz0zI_u.
  rewrite !RiscvExtras.uint_unsigned.
  rewrite (moi64_small (Z.of_nat a) ltac:(lia)) (moi64_small (Z.of_nat c) ltac:(lia)).
  destruct (Nat.ltb_spec a c) as [Hlt|Hge];
    [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

(* the [bltu]/[bgeu] reading, off the two unsigned values *)
Lemma rd_ltu_read (x y : mword 64) (a c : Z) :
  bv_unsigned x = a -> bv_unsigned y = c -> zopz0zI_u x y = Z.ltb a c.
Proof.
  intros <- <-. unfold zopz0zI_u. rewrite !RiscvExtras.uint_unsigned. reflexivity.
Qed.

(* the [c.beqz] on bmap's answer, on the arm where a block WAS found -- which
   under [bm_covers] is the only arm *)
Lemma rd_sext_nonzero (w : mword 32) :
  bv_unsigned w <> 0 -> bv_unsigned w < 2147483648 ->
  eq_vec (sign_extend' 64 w : mword 64) zero_reg = false.
Proof.
  intros Hnz Hlt.
  apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite (rd_sext32_unsigned w Hlt) bc_zero_reg_unsigned in Hc. exact (Hnz Hc).
Qed.

(* THE COMPRESSED [c.addw a4,a3] at +0x022 decodes to the same RTYPEW as the
   4-byte form, but with its operands spelled through [creg2reg_idx]; these
   two conversions are what let [WpSconfAlu.wp_addw_s_sconf] apply. *)
Lemma rd_creg_a3 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx (mword_of_int 13 : mword 5).
Proof. vm_compute. reflexivity. Qed.

Lemma rd_creg_a4 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14 : mword 5).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  (2) THE READ-ONLY BYTE WINDOW inside a checked-out buffer             *)
(* ===================================================================== *)

(* THE BYTE-WINDOW SPLITTERS ARE TIER-GENERIC, and they need their own
   section for it: readi splits its DESTINATION (a caller buffer at [ktb])
   with the same lemmas that split the bio block window (static, KT0), and
   a section variable can only be instantiated from OUTSIDE the section. *)
Section ReadiBytes.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !fsLogG Σ, !bioG Σ}.
  Context `{KTR : !CurKtier}.

  (* --- conversion wands over ByteBuf's [⊣⊢]s.  Stated as wands so the call
     sites APPLY them (unification, hence conversion-tolerant between
     [BSIZE] and the buffer's literal 1024) instead of REWRITING with them,
     which matches syntactically and does not. --- *)

  Lemma rd_bytes_of_list (a : mword 64) (l : list (bv 8)) (nn : nat) :
    length l = nn ->
    ([∗ list] j ↦ x ∈ l, pa_add a j ↦ₘ x) -∗
    ([∗ list] j ∈ seq 0 nn, pa_add a j ↦ₘ (l !!! j)).
  Proof.
    intros <-. iIntros "H".
    iApply (bi.equiv_entails_1_1 _ _ (bb_bytes_of_list a l)). iExact "H".
  Qed.

  Lemma rd_list_of_bytes (a : mword 64) (l : list (bv 8)) (nn : nat) :
    length l = nn ->
    ([∗ list] j ∈ seq 0 nn, pa_add a j ↦ₘ (l !!! j)) -∗
    ([∗ list] j ↦ x ∈ l, pa_add a j ↦ₘ x).
  Proof.
    intros <-. iIntros "H".
    iApply (bi.equiv_entails_1_2 _ _ (bb_bytes_of_list a l)). iExact "H".
  Qed.

  Lemma rd_bytes_to_list (a : mword 64) (nn : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 nn, pa_add a j ↦ₘ (f j)) -∗
    ([∗ list] j ↦ x ∈ (f <$> seq 0 nn), pa_add a j ↦ₘ x).
  Proof.
    iIntros "H".
    iApply (bi.equiv_entails_1_1 _ _ (bb_bytes_to_list a nn f)). iExact "H".
  Qed.

  Lemma rd_split3 (pp : mword 64) (a bb c L : nat) (f : nat -> bv 8) :
    (a + bb + c = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add pp j ↦ₘ (f j)) -∗
    ([∗ list] j ∈ seq 0 a, pa_add pp j ↦ₘ (f j))
    ∗ ([∗ list] j ∈ seq 0 bb, pa_add (pa_add pp a) j ↦ₘ (f (a + j)%nat))
    ∗ ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add pp a) bb) j ↦ₘ (f (a + (bb + j))%nat)).
  Proof.
    intros H. iIntros "Hb".
    iApply (bi.equiv_entails_1_1 _ _ (bb_split3 pp a bb c L f H)). iExact "Hb".
  Qed.

  Lemma rd_join3 (pp : mword 64) (a bb c L : nat) (f : nat -> bv 8) :
    (a + bb + c = L)%nat ->
    ([∗ list] j ∈ seq 0 a, pa_add pp j ↦ₘ (f j)) -∗
    ([∗ list] j ∈ seq 0 bb, pa_add (pa_add pp a) j ↦ₘ (f (a + j)%nat)) -∗
    ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add pp a) bb) j ↦ₘ (f (a + (bb + j))%nat)) -∗
    ([∗ list] j ∈ seq 0 L, pa_add pp j ↦ₘ (f j)).
  Proof.
    intros H. iIntros "H1 H2 H3".
    iApply (bi.equiv_entails_1_2 _ _ (bb_split3 pp a bb c L f H)).
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|]. iExact "H3".
  Qed.

End ReadiBytes.

Section ReadiRes.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !fsLogG Σ, !bioG Σ}.

  (* A [len]-byte WINDOW of a checked-out buffer's data area, borrowed at
     offset [o] and handed back UNCHANGED -- readi's copy reads it, so the
     buffer is reconstructed at the same bytes and the [bio_locked] the
     caller must present to brelse is the one bread produced.  The window is
     handed out in exactly the shape either_copyout's SOURCE premise takes
     ([∗ list] i ∈ seq 0 len, pa_add src i ↦ₘ ...), with
     [src = bp->data + o]. *)
  Lemma rd_buf_win_acc (pb : mword 64) (bno dsk : mword 32)
      (bs : list (bv 8)) (o len : nat) :
    (o + len <= BSIZE)%nat ->
    buf_own pb bno dsk bs -∗
      ⌜length bs = BSIZE⌝ ∗
      ([∗ list] i ∈ seq 0 len, pa_add (pa_add (b_data pb) o) i ↦ₘ[KT0] (bs !!! (o + i)%nat)) ∗
      (([∗ list] i ∈ seq 0 len, pa_add (pa_add (b_data pb) o) i ↦ₘ[KT0] (bs !!! (o + i)%nat)) -∗
       buf_own pb bno dsk bs).
  Proof.
    intros Hol.
    iIntros "(Hb & Hd & %Hlen & Hby)".
    assert (HlenB : length bs = BSIZE) by exact Hlen.
    iDestruct (rd_bytes_of_list (KTR := KT0) (b_data pb) bs BSIZE HlenB with "Hby") as "Hby".
    iDestruct (rd_split3 (KTR := KT0) (b_data pb) o len (BSIZE - o - len)%nat BSIZE
                 (fun j => bs !!! j) ltac:(lia) with "Hby") as "(Hpre & Hmid & Hsuf)".
    iSplitR; [iPureIntro; exact HlenB|].
    iSplitL "Hmid"; [iExact "Hmid"|].
    iIntros "Hmid".
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hd"; [iExact "Hd"|].
    iSplitR; [iPureIntro; exact HlenB|].
    iApply (rd_list_of_bytes (KTR := KT0) (b_data pb) bs BSIZE HlenB).
    iApply (rd_join3 (KTR := KT0) (b_data pb) o len (BSIZE - o - len)%nat BSIZE
              (fun j => bs !!! j) ltac:(lia) with "Hpre Hmid Hsuf").
  Qed.

  (* ---- the handle, exactly as in ProofBmapParts.v ---- *)

  Lemma rd_held_swap (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗
      buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
      (∀ bs' : list (bv 8),
         buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs' -∗
         bio_held bn V k pidv dev bno bs' bsl bsd d).
  Proof.
    rewrite /bio_held.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iSplitL "H5"; [iExact "H5"|].
    iIntros (bs') "H5".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iExact "H7".
  Qed.

  Lemma rd_held_k (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗ ⌜(k < NBUF)%nat⌝.
  Proof. rewrite /bio_held. iIntros "(%A & _)". done. Qed.

  Lemma rd_held_content (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd bs0 : list (bv 8)) (d : bool) :
    fsblock γfs (uint bno) bs0 -∗
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
    ⌜bsl = bs0⌝.
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "Hc (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay)".
    destruct d.
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mdirty_agree with "Hc Hm").
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mclean_agree with "Hc Hm").
  Qed.

  (* readi PUTS THE BLOCK BACK UNCHANGED: [inode_blocks_acc]'s back-wand
     re-indexes [data] at the value it already had, which is [data] itself
     -- pointwise, hence through [inode_blocks_frame] rather than funext. *)
  Lemma rd_blocks_restore (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (i : nat) :
    inode_blocks γfs bm (<[i := data i]> data) -∗ inode_blocks γfs bm data.
  Proof.
    iApply inode_blocks_frame. intros k Hk. split; [reflexivity|].
    destruct (decide (k = i)) as [->|Hne].
    - rewrite fn_lookup_insert. reflexivity.
    - rewrite fn_lookup_insert_ne; [reflexivity | congruence].
  Qed.

End ReadiRes.

(* ===================================================================== *)
(*  (3) THE DELIVERED BYTES                                               *)
(* ===================================================================== *)

(* before the first chunk the destination is exactly what the caller gave *)
Lemma rd_deliver_0 (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off i : nat) :
  rd_delivered data dst_olds off 0%nat i = dst_olds i.
Proof. rewrite /rd_delivered. case_decide as H1; [exfalso; lia | reflexivity]. Qed.

(* the prefix already read is untouched by a later chunk *)
Lemma rd_deliver_lo (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off tot mm i : nat) :
  (i < tot)%nat ->
  rd_delivered data dst_olds off tot i
  = rd_delivered data dst_olds off (tot + mm)%nat i.
Proof.
  intro Hi. rewrite /rd_delivered.
  case_decide as H1; [| exfalso; lia].
  case_decide as H2; [reflexivity | exfalso; lia].
Qed.

(* the tail beyond the chunk is likewise untouched *)
Lemma rd_deliver_hi (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off tot mm i : nat) :
  (tot + mm <= i)%nat ->
  rd_delivered data dst_olds off tot i
  = rd_delivered data dst_olds off (tot + mm)%nat i.
Proof.
  intro Hi. rewrite /rd_delivered.
  case_decide as H1; [exfalso; lia |].
  case_decide as H2; [exfalso; lia | reflexivity].
Qed.

(* THE step of the loop's range invariant: the [mm] bytes either_copyout
   moved out of block [fb] at offset [o] ARE the file's bytes at
   [off+tot .. off+tot+mm). *)
Lemma rd_deliver_mid (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (off tot mm fb o jj : nat) :
  (o + mm <= BSIZE)%nat -> (fb * BSIZE + o = off + tot)%nat -> (jj < mm)%nat ->
  (data fb !!! (o + jj)%nat)
  = rd_delivered data dst_olds off (tot + mm)%nat (tot + jj)%nat.
Proof.
  intros Hol Hfb Hjj.
  rewrite /rd_delivered.
  case_decide as H1; [| exfalso; lia].
  rewrite /file_byte.
  destruct (rd_div_in (off + (tot + jj))%nat fb (o + jj)%nat
              ltac:(lia) ltac:(lia)) as [Hd Hm].
  rewrite Hd Hm. reflexivity.
Qed.

(* ===================================================================== *)
(*  (4) THE FUEL                                                          *)
(* ===================================================================== *)

(* the number of blocks the byte range [off, off+rem) can touch.  Every
   iteration but the last fills its block to the boundary, so this bounds
   the loop count.  readi has no budget -- it never reaches the log -- so
   this is purely the induction's decreasing measure. *)
Definition rd_blocks (off rem : nat) : nat :=
  ((off `mod` BSIZE + rem + BSIZE - 1) `div` BSIZE)%nat.

Lemma rd_blocks_pos (off rem : nat) : (1 <= rem)%nat -> (1 <= rd_blocks off rem)%nat.
Proof.
  intros Hrem. rewrite /rd_blocks.
  apply Nat.div_le_lower_bound; [unfold BSIZE; lia |].
  pose proof (rd_mod_lt off). lia.
Qed.

Lemma rd_blocks_step (off rem : nat) :
  ((BSIZE - off `mod` BSIZE)%nat <= rem)%nat ->
  (rd_blocks (off + (BSIZE - off `mod` BSIZE)) (rem - (BSIZE - off `mod` BSIZE)) + 1
   <= rd_blocks off rem)%nat.
Proof.
  intros Hrem.
  pose proof (rd_mod_lt off) as Hlt.
  pose proof (rd_divmod off) as Hdm.
  assert (Halign : ((off + (BSIZE - off `mod` BSIZE)) `mod` BSIZE)%nat = 0%nat).
  { replace (off + (BSIZE - off `mod` BSIZE))%nat
      with (BSIZE * (off `div` BSIZE + 1))%nat by lia.
    rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  unfold rd_blocks. rewrite Halign.
  assert (E1 : (0 + (rem - (BSIZE - off `mod` BSIZE)) + BSIZE - 1)%nat
             = (rem + off `mod` BSIZE - 1)%nat) by lia.
  assert (E2 : (off `mod` BSIZE + rem + BSIZE - 1)%nat
             = ((rem + off `mod` BSIZE - 1) + 1 * BSIZE)%nat) by lia.
  rewrite E1 E2 Nat.div_add; [lia | unfold BSIZE; lia].
Qed.

(* ===================================================================== *)
(*  (5) MISCELLANY                                                        *)
(* ===================================================================== *)

Lemma rd_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* ProofWriteiParts.v -- writei's vocabulary: everything its proof needs that
   is NOT a step of its instruction chain, so ProofWritei.v stays about
   control flow.  (The ProofBmapParts.v / ProofIupdateParts.v division of
   labour; a Proof file may not import another one, so the handful of
   lemmas that also appear there are re-derived here.)

   Five groups:

   (1) ARITHMETIC.  writei is an arithmetic function: [addw] for the two
       counters, [subw] for the two [min] operands, [andi ...,1023] for
       [off % BSIZE], [srliw ...,0xa] for [off / BSIZE] and a
       [slli 32 / srli 32] pair for the zero-extension of the chunk length.
       Every one is stated at a NAT literal, because that is what the loop
       invariant carries.

   (2) THE BYTE WINDOW inside a checked-out buffer.  [wi_splice] is the
       block content after a [len]-byte write at offset [o], and
       [wi_buf_win_acc] borrows exactly that window out of [buf_own] and
       takes it back at whatever either_copyin left there.  This is the
       [ByteBuf.bb_split3]/[bb_join3] pattern of the copy loops, at a
       buffer rather than a page.

   (3) THE FLAT FILE VIEW.  [InodeInv.file_byte] reads a byte out of the
       per-block [data]; the two lemmas here say what one spliced block does
       to it, which is the whole content of writei's postcondition.

   (4) THE BUDGET.  [wi_blocks_step] is the only non-obvious arithmetic in
       the whole proof: an iteration that fills its block to the boundary
       decreases the straddled-block count by exactly one, which is what
       pays the six units bmap and log_write may spend.

   (5) THE HANDLE.  [wi_held_swap] / [wi_held_content] / the slot-unit
       algebra, exactly as in ProofBmapParts.v. *)
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
Require Import WpMmodeLeafBase.
Require Import PrintintArith.
Require Import VcGen.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import ProcInv.
Require Import SpecWritei.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (0) nat division by BSIZE                                             *)
(* ===================================================================== *)

Lemma wi_bsize_pos : (0 < BSIZE)%nat.
Proof. unfold BSIZE. lia. Qed.

Lemma wi_divmod (k : nat) : k = (BSIZE * (k `div` BSIZE) + k `mod` BSIZE)%nat.
Proof. apply Nat.div_mod_eq. Qed.

Lemma wi_mod_lt (k : nat) : (k `mod` BSIZE < BSIZE)%nat.
Proof. apply Nat.mod_upper_bound. unfold BSIZE. lia. Qed.

(* the byte at index [k] of the file lies in block [fb] exactly when [k] is
   inside that block's own range -- the step every "which block did this
   byte land in" argument takes. *)
Lemma wi_div_in (k fb r : nat) :
  (r < BSIZE)%nat -> k = (fb * BSIZE + r)%nat ->
  (k `div` BSIZE)%nat = fb /\ (k `mod` BSIZE)%nat = r.
Proof.
  intros Hr ->.
  assert (Hdiv : ((fb * BSIZE + r) `div` BSIZE)%nat = fb).
  { rewrite Nat.div_add_l; [| unfold BSIZE; lia].
    rewrite Nat.div_small; [lia | exact Hr]. }
  split; [exact Hdiv|].
  pose proof (wi_divmod (fb * BSIZE + r)%nat) as Hdm.
  rewrite Hdiv in Hdm. lia.
Qed.

(* ===================================================================== *)
(*  (1) Arithmetic                                                        *)
(* ===================================================================== *)

Lemma wi_sext32 (z : Z) : 0 <= z -> z < 2147483648 ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intros H0 H1. apply PrintintArith.sext32_64_small.
  split; [lia | change (2 ^ 31)%Z with 2147483648%Z; lia].
Qed.

Lemma wi_uint_moi (z : Z) : 0 <= z -> z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof.
  intros H0 H1. rewrite RiscvExtras.uint_unsigned moi64_unsigned.
  apply bvw64_small. change (2 ^ 64)%Z with 18446744073709551616%Z. lia.
Qed.

(* [addw rd,rs1,rs2] at two small non-negative literals *)
Lemma wi_addw (a c : Z) : 0 <= a -> 0 <= c -> a + c < 2147483648 ->
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
  rewrite Hadd. apply wi_sext32; lia.
Qed.

(* [subw rd,rs1,rs2] at two small non-negative literals, no borrow *)
Lemma wi_subw (a c : Z) : 0 <= c -> c <= a -> a < 2147483648 ->
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
  rewrite Hsub. apply wi_sext32; lia.
Qed.

(* [andi a5,s2,1023] : off % BSIZE *)
Lemma wi_andi1023 (z : Z) : 0 <= z -> z < 2147483648 ->
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

(* [srliw a1,s2,0xa] : off / BSIZE *)
Lemma wi_srliw10 (z : Z) : 0 <= z -> z < 2147483648 ->
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
  rewrite Hsh. apply wi_sext32.
  - apply Z.div_pos; lia.
  - assert (Hd : z / 1024 <= z) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* [slli s11,s10,0x20 / srli s11,s11,0x20] : the zero-extension of a value
   that already fits in 32 bits is the identity. *)
Lemma wi_zext32 (x : mword 64) :
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

(* [lui a4,0x43] : MAXFILE * BSIZE *)
Lemma wi_lui43 : luival (mword_of_int 67 : mword 20) = (mword_of_int 274432 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* Stated over [Z], not [nat]: a [nat] literal "274432" -- however it is
   reached, [reflexivity], [vm_compute], even [vm_cast_no_check] -- can force
   SOME machinery to materialize a 274432-deep unary successor chain, and
   that overflows an 8 MB stack outright.  [Z]'s literals are binary
   [Z.pos] trees (~19 levels for this value), so routing the multiplication
   through [Z.of_nat] and closing at THIS type never touches unary [nat]
   above the two small factors [MAXFILE]/[BSIZE]. *)
Lemma wi_maxfile_bsize : Z.of_nat (MAXFILE * BSIZE) = 274432.
Proof. rewrite Nat2Z.inj_mul. unfold MAXFILE, BSIZE. vm_compute. reflexivity. Qed.

(* Stated with [Z.to_nat 274432] rather than a bare [274432%nat] literal:
   any route to a bare-nat-literal statement of this fact -- [reflexivity],
   [vm_compute], [lia] after unfolding [MAXFILE]/[BSIZE] to their [Z] values
   and back -- still needs the kernel to materialize (or the [abstract-large-
   number] machinery to unfold) an actual 274432-deep [nat] successor chain
   somewhere, and that overflows the stack in THIS file's ambient context
   even though the same reduction succeeds in isolation (the difference is
   headroom eaten by the surrounding Iris/stdpp imports, not this lemma).
   Going through [Z.to_nat] and [Nat2Z.id] instead never asks for that
   chain: both rewrites are symbolic (pattern match on the literal [Z] side,
   which is a cheap ~19-level [Z.pos] tree either way), so the proof is
   [O(1)] regardless of context. [lia] resolves [Z.to_nat] of a literal
   symbolically too, so this is a transparent drop-in for callers. *)
Lemma wi_maxfile_bsize_nat : (MAXFILE * BSIZE)%nat = Z.to_nat 274432.
Proof. rewrite <- wi_maxfile_bsize, Nat2Z.id. reflexivity. Qed.

(* the two [c.li]s and the [li s9,1024] *)
Lemma wi_li_m1 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma wi_li_0 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma wi_li_1024 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (mword_of_int 1024 : mword 12))
  = (mword_of_int 1024 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* addresses *)
Lemma wi_pa_add_moi (p : mword 64) (nn : nat) :
  add_vec p (mword_of_int (Z.of_nat nn)) = pa_add p nn.
Proof. reflexivity. Qed.

Lemma wi_data_addr (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
              = mword_of_int (Z.of_nat 88%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H wi_pa_add_moi. reflexivity.
Qed.

Lemma wi_off0 (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 0 : mword 12)) = p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
              = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. apply kv_addv_zero.
Qed.

(* [c.add a0,a0,a5] and [c.add s4,s4,s11]: the cursor advances *)
Lemma wi_pa_step (p : mword 64) (a c : nat) :
  add_vec (pa_add p a) (mword_of_int (Z.of_nat c)) = pa_add p (a + c)%nat.
Proof. rewrite wi_pa_add_moi. apply pa_add_add. Qed.

(* the BLTU reading, at nat literals ([ByteCursor.bc_ge_moi] is the BGEU twin) *)
Lemma wi_lt_moi (a c : nat) :
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

(* a 32-bit cell round-trips through its unsigned value... *)
Lemma wi_moi32_id (w : mword 32) : (mword_of_int (bv_unsigned w) : mword 32) = w.
Proof.
  apply bv_eq. rewrite moi32_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* ...and a small one survives the ABI's sign extension *)
Lemma wi_sext32_unsigned (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  bv_unsigned (sign_extend' 64 w : mword 64) = bv_unsigned w.
Proof.
  intro Hw. pose proof (bv_unsigned_in_range _ w) as [H0 _].
  rewrite -{1}(wi_moi32_id w).
  rewrite (sext64_moi32_unsigned (bv_unsigned w)
             ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia)).
  reflexivity.
Qed.

(* the two [bltu]/[bgeu] readings, at nat literals *)
Lemma wi_zero32 (w : mword 32) : bv_unsigned w = 0 -> w = (mword_of_int 0 : mword 32).
Proof. intro Hw. apply bv_eq. rewrite Hw moi32_unsigned. reflexivity. Qed.

(* ===================================================================== *)
(*  (2) THE BYTE WINDOW inside a checked-out buffer                       *)
(* ===================================================================== *)

Definition wi_splice (bs : list (bv 8)) (o len : nat) (g : nat -> bv 8)
    : list (bv 8) :=
  (fun i => if decide ((o <= i)%nat /\ (i < o + len)%nat)
            then g (i - o)%nat else bs !!! i) <$> seq 0 BSIZE.

Lemma wi_splice_len (bs : list (bv 8)) (o len : nat) (g : nat -> bv 8) :
  length (wi_splice bs o len g) = BSIZE.
Proof. apply bb_fmap_len. Qed.

Lemma wi_splice_lookup (bs : list (bv 8)) (o len i : nat) (g : nat -> bv 8) :
  (i < BSIZE)%nat ->
  wi_splice bs o len g !!! i
  = if decide ((o <= i)%nat /\ (i < o + len)%nat) then g (i - o)%nat else bs !!! i.
Proof.
  intros Hi.
  assert (Hlk : seq 0 BSIZE !! i = Some i) by (apply lookup_seq; lia).
  rewrite /wi_splice list_lookup_total_alt list_lookup_fmap Hlk /=. reflexivity.
Qed.

(* THE BYTE-WINDOW SPLITTERS ARE TIER-GENERIC (ProofReadiParts.ReadiBytes'
   twin): writei splits its SOURCE (a caller buffer at [ktb]) with the same
   lemmas that split the bio block window (static, KT0). *)
Section WriteiBytes.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{KTR : !CurKtier}.

  (* --- three conversion wands over ByteBuf's [⊣⊢]s.  Stated as wands so
     the call sites APPLY them (unification, hence conversion-tolerant
     between [BSIZE] and the buffer's literal 1024) instead of REWRITING
     with them, which matches syntactically and does not. --- *)

  Local Lemma wi_bytes_of_list (a : mword 64) (l : list (bv 8)) (nn : nat) :
    length l = nn ->
    ([∗ list] j ↦ x ∈ l, pa_add a j ↦ₘ x) -∗
    ([∗ list] j ∈ seq 0 nn, pa_add a j ↦ₘ (l !!! j)).
  Proof.
    intros <-. iIntros "H".
    iApply (bi.equiv_entails_1_1 _ _ (bb_bytes_of_list a l)). iExact "H".
  Qed.

  Local Lemma wi_bytes_to_list (a : mword 64) (nn : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 nn, pa_add a j ↦ₘ (f j)) -∗
    ([∗ list] j ↦ x ∈ (f <$> seq 0 nn), pa_add a j ↦ₘ x).
  Proof.
    iIntros "H".
    iApply (bi.equiv_entails_1_1 _ _ (bb_bytes_to_list a nn f)). iExact "H".
  Qed.

  Local Lemma wi_split3 (pp : mword 64) (a bb c L : nat) (f : nat -> bv 8) :
    (a + bb + c = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add pp j ↦ₘ (f j)) -∗
    ([∗ list] j ∈ seq 0 a, pa_add pp j ↦ₘ (f j))
    ∗ ([∗ list] j ∈ seq 0 bb, pa_add (pa_add pp a) j ↦ₘ (f (a + j)%nat))
    ∗ ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add pp a) bb) j ↦ₘ (f (a + (bb + j))%nat)).
  Proof.
    intros H. iIntros "Hb".
    iApply (bi.equiv_entails_1_1 _ _ (bb_split3 pp a bb c L f (DfracOwn 1) H)). iExact "Hb".
  Qed.

  Local Lemma wi_join3 (pp : mword 64) (a bb c L : nat) (f : nat -> bv 8) :
    (a + bb + c = L)%nat ->
    ([∗ list] j ∈ seq 0 a, pa_add pp j ↦ₘ (f j)) -∗
    ([∗ list] j ∈ seq 0 bb, pa_add (pa_add pp a) j ↦ₘ (f (a + j)%nat)) -∗
    ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add pp a) bb) j ↦ₘ (f (a + (bb + j))%nat)) -∗
    ([∗ list] j ∈ seq 0 L, pa_add pp j ↦ₘ (f j)).
  Proof.
    intros H. iIntros "H1 H2 H3".
    iApply (bi.equiv_entails_1_2 _ _ (bb_split3 pp a bb c L f (DfracOwn 1) H)).
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|]. iExact "H3".
  Qed.

End WriteiBytes.

Section WriteiRes.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* A [len]-byte WINDOW of a checked-out buffer's data area, borrowed at
     offset [o] and taken back at whatever the copy left there.  The window
     is handed out in exactly the shape either_copyin's destination premise
     takes ([∗ list] i ∈ seq 0 len, pa_add dst i ↦ₘ ...), with
     [dst = bp->data + o]. *)
  Lemma wi_buf_win_acc (pb : mword 64) (bno dsk : mword 32)
      (bs : list (bv 8)) (o len : nat) :
    (o + len <= BSIZE)%nat ->
    buf_own pb bno dsk bs -∗
      ⌜length bs = BSIZE⌝ ∗
      ([∗ list] i ∈ seq 0 len, pa_add (pa_add (b_data pb) o) i ↦ₘ (bs !!! (o + i)%nat)) ∗
      (∀ g : nat -> bv 8,
         ([∗ list] i ∈ seq 0 len, pa_add (pa_add (b_data pb) o) i ↦ₘ (g i)) -∗
         buf_own pb bno dsk (wi_splice bs o len g)).
  Proof.
    intros Hol.
    iIntros "(Hb & Hd & %Hlen & Hby)".
    assert (HlenB : length bs = BSIZE) by exact Hlen.
    iDestruct (wi_bytes_of_list (KTR := KT0) (b_data pb) bs BSIZE HlenB with "Hby") as "Hby".
    iDestruct (wi_split3 (KTR := KT0) (b_data pb) o len (BSIZE - o - len)%nat BSIZE
                 (fun j => bs !!! j) ltac:(lia) with "Hby") as "(Hpre & Hmid & Hsuf)".
    iSplitR; [iPureIntro; exact HlenB|].
    iSplitL "Hmid"; [iExact "Hmid"|].
    iIntros (g) "Hmid".
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hd"; [iExact "Hd"|].
    iSplitR; [iPureIntro; exact (wi_splice_len bs o len g)|].
    rewrite /wi_splice.
    iApply (wi_bytes_to_list (KTR := KT0) (b_data pb) BSIZE
              (fun i => if decide ((o <= i)%nat /\ (i < o + len)%nat)
                        then g (i - o)%nat else bs !!! i)).
    iApply (wi_join3 (KTR := KT0) (b_data pb) o len (BSIZE - o - len)%nat BSIZE
              (fun i => if decide ((o <= i)%nat /\ (i < o + len)%nat)
                        then g (i - o)%nat else bs !!! i) ltac:(lia)
              with "[Hpre] [Hmid] [Hsuf]").
    - iApply (big_sepL_mono with "Hpre"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_False; [reflexivity | lia].
    - iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_True; [| lia].
      replace (o + i - o)%nat with i by lia. reflexivity.
    - iApply (big_sepL_mono with "Hsuf"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite decide_False; [reflexivity | lia].
  Qed.

  (* ---- the handle, exactly as in ProofBmapParts.v ---- *)

  Lemma wi_slots_split (a c : nat) :
    bslots (a + c) -∗ bslots a ∗ bslots c.
  Proof. rewrite bslots_op. iIntros "$". Qed.

  Lemma wi_slots_join (a c : nat) :
    bslots a -∗ bslots c -∗ bslots (a + c).
  Proof.
    iIntros "H1 H2". rewrite bslots_op. iSplitL "H1"; [iExact "H1"|iExact "H2"].
  Qed.

  Lemma wi_held_swap (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗
      buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
      (∀ bs' : list (bv 8),
         buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs' -∗
         bio_held bn V k pidv dev bno bs' bsl bsd d).
  Proof.
    rewrite /bio_held.
    iIntros "(%A & %B & %C & H1 & H3 & H4 & H5 & H6 & H7)".
    iSplitL "H5"; [iExact "H5"|].
    iIntros (bs') "H5".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "H1"; [iExact "H1"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iExact "H7".
  Qed.

  Lemma wi_held_k (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗ ⌜(k < NBUF)%nat⌝.
  Proof. rewrite /bio_held. iIntros "(%A & _)". done. Qed.

  Lemma wi_held_content (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd bs0 : list (bv 8)) (d : bool) :
    fsblock γfs (uint bno) bs0 -∗
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
    ⌜bsl = bs0⌝.
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "Hc (_ & _ & _ & _ & _ & _ & _ & _ & Hpay)".
    destruct d.
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mdirty_agree with "Hc Hm").
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mclean_agree with "Hc Hm").
  Qed.

End WriteiRes.

(* ===================================================================== *)
(*  (3) THE FLAT FILE VIEW                                                *)
(* ===================================================================== *)

(* re-depositing a block at content it already had changes nothing *)
Lemma wi_file_byte_same (data : nat -> list (bv 8)) (i : nat)
    (v : list (bv 8)) (k : nat) :
  data i = v -> file_byte (<[i := v]> data) k = file_byte data k.
Proof.
  intros Hd. rewrite /file_byte.
  destruct (decide ((k `div` BSIZE)%nat = i)) as [He|Hne].
  - rewrite He fn_lookup_insert Hd. reflexivity.
  - rewrite fn_lookup_insert_ne; [reflexivity | congruence].
Qed.

(* THE step of the loop's range invariant: writing [len] bytes at offset [o]
   of block [fb] sets exactly the file bytes [fb*BSIZE+o .. +len) and leaves
   every other byte of the file alone. *)
Lemma wi_file_byte_splice (data : nat -> list (bv 8)) (fb o len : nat)
    (g : nat -> bv 8) (k : nat) :
  (o + len <= BSIZE)%nat ->
  file_byte (<[fb := wi_splice (data fb) o len g]> data) k
  = if decide ((fb * BSIZE + o <= k)%nat /\ (k < fb * BSIZE + o + len)%nat)
    then g (k - (fb * BSIZE + o))%nat
    else file_byte data k.
Proof.
  intros Hol. rewrite /file_byte.
  destruct (decide ((k `div` BSIZE)%nat = fb)) as [He|Hne].
  - rewrite He fn_lookup_insert.
    rewrite (wi_splice_lookup (data fb) o len (k `mod` BSIZE)%nat g (wi_mod_lt k)).
    pose proof (wi_divmod k) as Hdm. rewrite He in Hdm.
    destruct (decide ((o <= k `mod` BSIZE)%nat /\ (k `mod` BSIZE < o + len)%nat))
      as [Hin|Hout].
    + rewrite decide_True; [| lia].
      f_equal. lia.
    + rewrite decide_False; [| lia]. reflexivity.
  - rewrite fn_lookup_insert_ne; [| congruence].
    rewrite decide_False; [reflexivity |].
    intros [H1 H2]. apply Hne.
    destruct (wi_div_in k fb (k - fb * BSIZE)%nat ltac:(lia) ltac:(lia)) as [Hd _].
    exact Hd.
Qed.

(* --- the block index of the current cursor, and the two Z readings the
       instruction stream computes --- *)

Lemma wi_maxfile_val : MAXFILE = 268%nat.
Proof. reflexivity. Qed.

Lemma wi_bsize_val : BSIZE = 1024%nat.
Proof. reflexivity. Qed.

Lemma wi_fbn_lt (x : nat) : (x < MAXFILE * BSIZE)%nat -> (x `div` BSIZE < MAXFILE)%nat.
Proof.
  intros H. apply Nat.div_lt_upper_bound; [unfold BSIZE; lia|].
  rewrite Nat.mul_comm. exact H.
Qed.

Lemma wi_div_z (x : nat) : Z.of_nat (x `div` BSIZE) = (Z.of_nat x / 1024)%Z.
Proof. rewrite Nat2Z.inj_div. reflexivity. Qed.

Lemma wi_mod_z (x : nat) : Z.of_nat (x `mod` BSIZE) = (Z.of_nat x mod 1024)%Z.
Proof. rewrite Nat2Z.inj_mod. reflexivity. Qed.

(* --- what bmap's DEPOSIT does to the two invariants the loop carries.
       Both are consequences of the zero side condition on the deposit and
       of "bmap never un-allocates" (SpecBmap.v), and both are needed at
       EVERY iteration, not just the allocating one. --- *)

Lemma wi_bmap_data (bm : blkmap) (data data' : nat -> list (bv 8)) (fbn : nat) :
  blk_holes_zero bm data ->
  (fbn < MAXFILE)%nat ->
  (data' = data \/ (bv_unsigned (blkmap_get bm fbn) = 0
                    /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)) ->
  forall k : nat, file_byte data' k = file_byte data k.
Proof.
  intros Hhz Hfbn [-> | [Hz ->]] k; [reflexivity|].
  exact (wi_file_byte_same data fbn (replicate BSIZE (bv_0 8)) k (Hhz fbn Hfbn Hz)).
Qed.

Lemma wi_holes_bmap (bm bm' : blkmap) (data data' : nat -> list (bv 8)) (fbn : nat) :
  (fbn < MAXFILE)%nat ->
  (forall i : nat, (i < MAXFILE)%nat -> i <> fbn -> blkmap_get bm' i = blkmap_get bm i) ->
  (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
     blkmap_get bm' i = blkmap_get bm i) ->
  (data' = data \/ (bv_unsigned (blkmap_get bm fbn) = 0
                    /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)) ->
  blk_holes_zero bm data -> blk_holes_zero bm' data'.
Proof.
  intros Hfbn Hagr Hnoun Hdep Hhz i Hi Hz'.
  destruct (decide (i = fbn)) as [->|Hne].
  - destruct Hdep as [-> | [Hz ->]].
    + apply (Hhz fbn Hfbn).
      destruct (decide (bv_unsigned (blkmap_get bm fbn) = 0)) as [H0|Hnz]; [exact H0|].
      exfalso. rewrite (Hnoun fbn Hfbn Hnz) in Hz'. exact (Hnz Hz').
    + rewrite fn_lookup_insert. reflexivity.
  - assert (Hg : blkmap_get bm' i = blkmap_get bm i) by exact (Hagr i Hi Hne).
    rewrite Hg in Hz'.
    destruct Hdep as [-> | [_ ->]]; [exact (Hhz i Hi Hz')|].
    rewrite fn_lookup_insert_ne; [| congruence]. exact (Hhz i Hi Hz').
Qed.

(* --- the range invariant, one iteration at a time --- *)

(* the SUCCESS step: the chunk lands inside the written range, which grows *)
Lemma wi_range_step (data dataI : nat -> list (bv 8))
    (off tot mm fb o : nat) (wroteI g : nat -> bv 8) :
  (o + mm <= BSIZE)%nat ->
  (fb * BSIZE + o = off + tot)%nat ->
  (forall k : nat, file_byte dataI k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wroteI (k - off)%nat else file_byte data k) ->
  forall k : nat,
    file_byte (<[fb := wi_splice (dataI fb) o mm g]> dataI) k
    = if decide ((off <= k)%nat /\ (k < off + (tot + mm))%nat)
      then (fun i : nat => if decide (i < tot)%nat then wroteI i else g (i - tot)%nat)
             (k - off)%nat
      else file_byte data k.
Proof.
  intros Hol Hfb Hinv k.
  rewrite (wi_file_byte_splice dataI fb o mm g k Hol) Hfb.
  case_decide as Hc.
  - rewrite decide_True; [| lia]. rewrite decide_False; [| lia]. f_equal. lia.
  - rewrite Hinv. case_decide as Hd.
    + rewrite decide_True; [| lia]. rewrite decide_True; [reflexivity | lia].
    + rewrite decide_False; [reflexivity | lia].
Qed.

(* the FAILURE step: the chunk lands in the DISTURBED region instead --
   [tot] is not advanced, so the bytes are logged but not claimed. *)
Lemma wi_range_fail (data dataI : nat -> list (bv 8))
    (off tot mm fb o : nat) (wroteI g : nat -> bv 8) :
  (o + mm <= BSIZE)%nat ->
  (fb * BSIZE + o = off + tot)%nat ->
  (forall k : nat, file_byte dataI k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wroteI (k - off)%nat else file_byte data k) ->
  forall k : nat,
    file_byte (<[fb := wi_splice (dataI fb) o mm g]> dataI) k
    = if decide ((off <= k)%nat /\ (k < off + tot)%nat) then wroteI (k - off)%nat
      else if decide ((off + tot <= k)%nat /\ (k < off + tot + mm)%nat)
           then g (k - (off + tot))%nat
           else file_byte data k.
Proof.
  intros Hol Hfb Hinv k.
  rewrite (wi_file_byte_splice dataI fb o mm g k Hol) Hfb.
  case_decide as Hc.
  - rewrite decide_False; [| lia].
    first [ reflexivity | rewrite decide_True; [reflexivity | lia] ].
  - rewrite Hinv.
    first [ reflexivity
          | (case_decide as Hd; [reflexivity|]);
            rewrite decide_False; [reflexivity | lia] ].
Qed.

(* an UNDISTURBED exit: the two-clause invariant read as a three-clause
   postcondition with [dist = 0] *)
Lemma wi_range_dist0 (data data' : nat -> list (bv 8)) (off tot : nat)
    (wrote dstb : nat -> bv 8) :
  (forall k : nat, file_byte data' k
     = if decide ((off <= k)%nat /\ (k < off + tot)%nat)
       then wrote (k - off)%nat else file_byte data k) ->
  forall k : nat,
    file_byte data' k
    = if decide ((off <= k)%nat /\ (k < off + tot)%nat) then wrote (k - off)%nat
      else if decide ((off + tot <= k)%nat /\ (k < off + tot + 0)%nat)
           then dstb (k - (off + tot))%nat else file_byte data k.
Proof.
  intros H k. rewrite H. case_decide as Hc; [reflexivity|].
  rewrite decide_False; [reflexivity | lia].
Qed.

(* the kernel-arm tie, extended by one chunk *)
Lemma wi_ker_step (user : bool) (src_bytes wroteI g : nat -> bv 8) (tot mm : nat) :
  (user = false -> forall i : nat, (i < tot)%nat -> wroteI i = src_bytes i) ->
  (user = false -> forall i : nat, (i < mm)%nat -> g i = src_bytes (tot + i)%nat) ->
  user = false -> forall i : nat, (i < tot + mm)%nat ->
    (if decide (i < tot)%nat then wroteI i else g (i - tot)%nat) = src_bytes i.
Proof.
  intros H1 H2 Hu i Hi. case_decide as Hd; [exact (H1 Hu i Hd)|].
  rewrite (H2 Hu (i - tot)%nat ltac:(lia)). f_equal. lia.
Qed.

Lemma wi_nat_u (k : nat) : (Z.of_nat k < 18446744073709551616)%Z ->
  bv_unsigned (mword_of_int (Z.of_nat k) : mword 64) = Z.of_nat k.
Proof. intro Hk. apply moi64_small. split; [apply Nat2Z.is_nonneg | exact Hk]. Qed.

(* the [bltu] reading, off the two unsigned values *)
Lemma wi_ltu_read (x y : mword 64) (a c : Z) :
  bv_unsigned x = a -> bv_unsigned y = c -> zopz0zI_u x y = Z.ltb a c.
Proof.
  intros <- <-. unfold zopz0zI_u. rewrite !RiscvExtras.uint_unsigned. reflexivity.
Qed.

(* the [beqz] on bmap's answer, on the arm where a block WAS found *)
Lemma wi_sext_nonzero (w : mword 32) :
  bv_unsigned w <> 0 -> bv_unsigned w < 2147483648 ->
  eq_vec (sign_extend' 64 w : mword 64) zero_reg = false.
Proof.
  intros Hnz Hlt.
  apply eq_vec_false_iff. intro Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite (wi_sext32_unsigned w Hlt) bc_zero_reg_unsigned in Hc. exact (Hnz Hc).
Qed.

(* ===================================================================== *)
(*  (4) THE BUDGET                                                        *)
(* ===================================================================== *)

Lemma wi_blocks_pos (off rem : nat) : (1 <= rem)%nat -> (1 <= wi_blocks off rem)%nat.
Proof.
  intros Hrem. rewrite /wi_blocks.
  apply Nat.div_le_lower_bound; [unfold BSIZE; lia |].
  pose proof (wi_mod_lt off). lia.
Qed.

(* THE decrease: an iteration that fills its block to the boundary
   straddles one block fewer afterwards. *)
Lemma wi_blocks_step (off rem : nat) :
  ((BSIZE - off `mod` BSIZE)%nat <= rem)%nat ->
  (wi_blocks (off + (BSIZE - off `mod` BSIZE)) (rem - (BSIZE - off `mod` BSIZE)) + 1
   <= wi_blocks off rem)%nat.
Proof.
  intros Hrem.
  pose proof (wi_mod_lt off) as Hlt.
  pose proof (wi_divmod off) as Hdm.
  assert (Halign : ((off + (BSIZE - off `mod` BSIZE)) `mod` BSIZE)%nat = 0%nat).
  { replace (off + (BSIZE - off `mod` BSIZE))%nat
      with (BSIZE * (off `div` BSIZE + 1))%nat by lia.
    rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  unfold wi_blocks. rewrite Halign.
  assert (E1 : (0 + (rem - (BSIZE - off `mod` BSIZE)) + BSIZE - 1)%nat
             = (rem + off `mod` BSIZE - 1)%nat) by lia.
  assert (E2 : (off `mod` BSIZE + rem + BSIZE - 1)%nat
             = ((rem + off `mod` BSIZE - 1) + 1 * BSIZE)%nat) by lia.
  rewrite E1 E2 Nat.div_add; [lia | unfold BSIZE; lia].
Qed.

(* ===================================================================== *)
(*  (4b) COVERAGE: writei ALLOCATES AS IT EXTENDS                         *)
(*                                                                        *)
(*  readi requires [bm_covers bm (di_size dn)] -- every file block below   *)
(*  the size is allocated -- so writei must hand it back at the NEW size,  *)
(*  or a caller that writes and then reads could never re-establish it.    *)
(*  It is provable because writei allocates (via bmap) every block it      *)
(*  writes BEFORE advancing [tot], and installs [size' = max(size,         *)
(*  off + tot)].  Two facts do the work:                                   *)
(*                                                                        *)
(*    - [wi_covers_step]: one iteration extends coverage from [off + tot]  *)
(*      to [off + tot + m], because the chunk never leaves the block bmap  *)
(*      just allocated;                                                    *)
(*    - [wi_covers_final]: at the join, coverage at the OLD size (carried  *)
(*      across every bmap call by [InodeInv.bm_covers_keep]) and coverage  *)
(*      at [off + tot] (the loop's own invariant) combine into coverage at *)
(*      whichever of the two [wi_dinode] installs.                          *)
(*                                                                        *)
(*  Both break arms are covered without a special case: they stop [tot]    *)
(*  early, and coverage is only ever claimed strictly below the final      *)
(*  size, so the disturbed region -- which lies at or above [off + tot] -- *)
(*  is never in scope.                                                     *)
(* ===================================================================== *)

(* the index arithmetic of the step, kept [mword]-free so [lia] works
   (durable-notes: [lia] answers "Cannot find witness" with a [bv_unsigned]
   merely in context).  A byte offset at or above [off + tot] but below
   [off + tot + mm] lies in the ONE block [fbn] the iteration just bmapped,
   because a chunk never crosses a block boundary. *)
Lemma wi_cov_idx (i fbn o mm off tot : nat) :
  (fbn * BSIZE + o = off + tot)%nat ->
  (o + mm <= BSIZE)%nat ->
  (Z.of_nat i * Z.of_nat BSIZE < Z.of_nat (off + (tot + mm)))%Z ->
  ~ (Z.of_nat i * Z.of_nat BSIZE < Z.of_nat (off + tot))%Z ->
  i = fbn.
Proof.
  intros Hdm Hmm Hlt Hge.
  rewrite -Nat2Z.inj_mul in Hlt. apply Nat2Z.inj_lt in Hlt.
  assert (Hge' : (off + tot <= i * BSIZE)%nat).
  { destruct (Nat.le_gt_cases (off + tot) (i * BSIZE)) as [H | H]; [exact H |].
    exfalso. apply Hge. rewrite -Nat2Z.inj_mul. apply Nat2Z.inj_lt. exact H. }
  pose proof wi_bsize_val as HB.
  rewrite HB in Hdm Hmm Hge' Hlt. lia.
Qed.

(* ONE ITERATION.  [fbn] is the block bmap just returned nonzero for, [o] the
   offset inside it, [mm] the chunk length; [Hkeep] is bmap's own "never
   un-allocates" clause. *)
Lemma wi_covers_step (bmI bm2 : blkmap) (off tot fbn o mm : nat) :
  (fbn * BSIZE + o = off + tot)%nat ->
  (o + mm <= BSIZE)%nat ->
  bv_unsigned (blkmap_get bm2 fbn) <> 0 ->
  (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bmI i) <> 0 ->
     blkmap_get bm2 i = blkmap_get bmI i) ->
  bm_covers bmI (Z.of_nat (off + tot)) ->
  bm_covers bm2 (Z.of_nat (off + (tot + mm))).
Proof.
  intros Hdm Hmm Hnz Hkeep Hcov i Hi Hlt.
  destruct (Z_lt_le_dec (Z.of_nat i * Z.of_nat BSIZE) (Z.of_nat (off + tot)))
    as [Hin | Hout].
  - rewrite (Hkeep i Hi (Hcov i Hi Hin)). exact (Hcov i Hi Hin).
  - assert (Hnlt : ~ (Z.of_nat i * Z.of_nat BSIZE < Z.of_nat (off + tot))%Z)
      by (clear -Hout; lia).
    rewrite (wi_cov_idx i fbn o mm off tot Hdm Hmm Hlt Hnlt). exact Hnz.
Qed.

(* THE JOIN.  [wi_dinode] installs [max(old size, off + tot)], so coverage at
   each of the two candidates gives coverage at whichever is chosen. *)
Lemma wi_covers_final (bm' : blkmap) (dn : dinode) (off tot : nat) :
  (Z.of_nat (off + tot) < 4294967296)%Z ->
  bm_covers bm' (bv_unsigned (di_size dn)) ->
  bm_covers bm' (Z.of_nat (off + tot)) ->
  bm_covers bm' (bv_unsigned (di_size (wi_dinode dn bm' off tot))).
Proof.
  intros Hlt Hcs Hct. rewrite /wi_dinode. cbn [di_size].
  case_decide as Hd; [| exact Hcs].
  assert (Hlt32 : (0 <= Z.of_nat (off + tot) < 2 ^ 32)%Z).
  { split; [apply Nat2Z.is_nonneg |].
    change (2 ^ 32)%Z with 4294967296%Z. exact Hlt. }
  rewrite (moi32_small (Z.of_nat (off + tot)) Hlt32). exact Hct.
Qed.

(* THE SIZE CAP, [InodeLock.inode_ok]'s fifth conjunct.  [wi_dinode] installs
   [max(old size, off + tot)], so the cap is PRESERVED rather than
   established: the old size's cap is the caller's (it comes out of
   [inode_ok] going in) and the new candidate is capped by the +0x2a guard.
   Stated over [Z] throughout -- the [MAXFILE * BSIZE] product is never
   forced into a unary [nat] literal (see [wi_maxfile_bsize]'s comment). *)
Lemma wi_size_cap (bm' : blkmap) (dn : dinode) (off tot : nat) :
  (off + tot <= MAXFILE * BSIZE)%nat ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_size (wi_dinode dn bm' off tot))
    <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof.
  intros Hle Hcap.
  assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432).
  { rewrite <- Nat2Z.inj_mul. exact wi_maxfile_bsize. }
  assert (Hz : Z.of_nat (off + tot) <= 274432).
  { rewrite <- wi_maxfile_bsize. apply Nat2Z.inj_le. exact Hle. }
  rewrite /wi_dinode. cbn [di_size].
  case_decide as Hd; [| exact Hcap].
  assert (Hlt32 : (0 <= Z.of_nat (off + tot) < 2 ^ 32)%Z).
  { split; [apply Nat2Z.is_nonneg |].
    change (2 ^ 32)%Z with 4294967296%Z. clear - Hz. lia. }
  rewrite (moi32_small (Z.of_nat (off + tot)) Hlt32). rewrite Hmb. exact Hz.
Qed.

(* [InodeInv.inode_sized] across bmap's DEPOSIT: the deposited block is a
   [replicate BSIZE], so the length is on hand and the fact is preserved by
   [inode_sized_insert].  (The same lemma, at [wi_splice], covers writei's
   own block update -- see [wi_splice_len].) *)
Lemma wi_sized_bmap (bm : blkmap) (data data' : nat -> list (bv 8)) (fbn : nat) :
  (data' = data \/ (bv_unsigned (blkmap_get bm fbn) = 0
                    /\ data' = <[fbn := replicate BSIZE (bv_0 8)]> data)) ->
  inode_sized data -> inode_sized data'.
Proof.
  intros [-> | [_ ->]] Hs; [exact Hs|].
  apply (inode_sized_insert data fbn _ Hs). apply length_replicate.
Qed.

(* ...and across ONE WHOLE ITERATION: bmap's deposit, then the block update.
   [wi_splice] rebuilds the block out of [seq 0 BSIZE], so its length is
   BSIZE by construction ([wi_splice_len]). *)
Lemma wi_sized_step (bm : blkmap) (data dataI data2 : nat -> list (bv 8))
    (fbn o mm : nat) (g : nat -> bv 8) :
  (data2 = dataI \/ (bv_unsigned (blkmap_get bm fbn) = 0
                     /\ data2 = <[fbn := replicate BSIZE (bv_0 8)]> dataI)) ->
  (inode_sized data -> inode_sized dataI) ->
  inode_sized data ->
  inode_sized (<[fbn := wi_splice (data2 fbn) o mm g]> data2).
Proof.
  intros Hdep HI Hs.
  apply (inode_sized_insert data2 fbn _
           (wi_sized_bmap bm dataI data2 fbn Hdep (HI Hs))).
  apply wi_splice_len.
Qed.

(* ===================================================================== *)
(*  (5) MISCELLANY                                                        *)
(* ===================================================================== *)

Lemma wi_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

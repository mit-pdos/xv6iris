(* DinodeSlot.v -- THE ON-DISK DINODE SLOT: the arithmetic that finds it,
   the addresses it sits at, and the resource it is.  Shared vocabulary of
   the two functions that move a dinode between the disk and the icache --
   iupdate flushes it out, ilock loads it in -- so it lives in the
   definitional layer rather than in either one's proof: a Proof file may
   not require another Proof file, and duplicating 450 lines of bitvector
   arithmetic to work around that is exactly the shape
   claude-notes/durable-notes.md's guiding principle forbids.

   (It was iupdate's [ProofIupdateParts.v] until ilock needed every line of
   it; the names are unchanged so that ProofIupdate.v did not move.)

   Four groups:

   (1) THE ARITHMETIC.  Both functions compute two things out of ip->inum:
       IBLOCK(inum, sb) = inum / IPB + sb.inodestart, as
       [srliw a5,a5,0x4] then [addw]; and the slot's byte offset
       (inum % IPB) * 64, as [andi a4,a4,15] then [slli a4,a4,0x6].  Both
       start from a SIGN-EXTENDED [lw] of a uint, so both readings have to
       see through that.  Every [Z] step is factored into an mword-FREE
       helper, because [lia] answers "Cannot find witness" as soon as a
       [bv_unsigned] is in the goal (claude-notes/durable-notes.md).
       Also here: [trunc16_sext64], the 16-bit twin of
       [RiscvExtras.trunc32_sext64] -- an [lh] followed by an [sh] of the
       same register is the identity on the halfword, which is what all
       four metadata copies are, in EITHER direction.

   (2) THE ADDRESSES.  bp->data, the dinode slot inside it, its five field
       cells, and their alignment (bcache geometry, as in write_head and
       bmap).

   (3) THE DINODE SLOT AS A RESOURCE.  [dislot a d] is the 64 bytes at [a]
       read as [DinodeEnc.dinode_bytes d] -- four [|->2] cells, one [|->4]
       cell and a 52-byte [ByteBuf] window, i.e. exactly the six pieces the
       four halfword copies, the word copy and the [memmove] touch.
       [diblk_slot_acc] borrows slot [k] out of a whole block's byte image
       and gives it back AT A NEW DINODE (iupdate's whole effect on the
       buffer); ilock gives it back UNCHANGED and reads the six pieces
       instead.

   (4) THE HANDLE.  [iu_held_swap] / [iu_held_content] / [iu_held_k] are the
       bio-handle manipulations (ProofBmapParts has the same three). *)
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
Require Import PrintintArith.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import WpSmodeHalf.
Require Import WpLock.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (1) The arithmetic                                                    *)
(* ===================================================================== *)

(* ---- mword-FREE helpers over plain Z ---- *)

Local Lemma iu_div16_arith (u : Z) : 0 <= u -> u < 4294967296 ->
  0 <= u / 16 /\ u / 16 < 2147483648 /\ u / 16 < 4294967296.
Proof.
  intros H0 H1.
  assert (Ha : 0 <= u / 16) by (apply Z.div_pos; lia).
  assert (Hb : u / 16 < 2147483648) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Local Lemma iu_mod16_arith (u : Z) : 0 <= u ->
  0 <= u `mod` 16 < 16.
Proof. intros H0. apply Z.mod_pos_bound. lia. Qed.

Local Lemma z_land15 (x : Z) : Z.land x 15 = x `mod` 16.
Proof.
  assert (Ho : (15 = Z.ones 4)%Z) by (vm_compute; reflexivity).
  rewrite Ho Z.land_ones; [| lia].
  assert (Hp : (2 ^ 4 = 16)%Z) by (vm_compute; reflexivity).
  rewrite Hp. reflexivity.
Qed.

(* mod 16 does not see a wrap at any width that 16 divides *)
Local Lemma z_mod16_of_mod (x m : Z) : (16 | m) -> x `mod` m `mod` 16 = x `mod` 16.
Proof. intros Hd. apply Z.mod_mod_divide. exact Hd. Qed.

Local Lemma z_swrap32_mod16 (u : Z) :
  ((u + 2147483648) `mod` 4294967296 - 2147483648) `mod` 16 = u `mod` 16.
Proof.
  rewrite Zminus_mod.
  rewrite (z_mod16_of_mod (u + 2147483648) 4294967296
             ltac:(exists 268435456; reflexivity)).
  assert (H1 : (2147483648 `mod` 16)%Z = 0) by (vm_compute; reflexivity).
  rewrite H1 Z.sub_0_r Zmod_mod.
  rewrite Zplus_mod H1 Z.add_0_r Zmod_mod. reflexivity.
Qed.

(* ---- an [lh] followed by an [sh] of the same register is the identity
   on the halfword: the 16-bit twin of [RiscvExtras.trunc32_sext64].  All
   four metadata copies are exactly this. ---- *)
Lemma trunc16_sext64 (w : mword 16) : trunc16 (sign_extend' 64 w) = w.
Proof.
  apply bv_eq. unfold trunc16. rewrite autocast_id.
  unfold subrange_vec_dec, to_word_idx, to_word, get_word,
         MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (Z.sub (Z.mul 2 8) 1 - 0 + 1)) with 16%N.
  rewrite (bv_wrap_bv_wrap 16 64 _ ltac:(lia)).
  unfold bv_signed. rewrite bv_wrap_swrap.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ---- the low half of a sign extension ---- *)
Lemma iu_sub31_sext (w : mword 32) :
  (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32) = w.
Proof.
  change (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
    with (trunc32 (sign_extend' 64 w)).
  apply trunc32_sext64.
Qed.

Lemma iu_sub31_moi (k : Z) : 0 <= k -> k < 4294967296 ->
  (subrange_vec_dec (mword_of_int k : mword 64) 31 0 : mword 32) = mword_of_int k.
Proof.
  intros H0 H1.
  assert (Hk64 : 0 <= k < 2 ^ 64)
    by (change (2^64)%Z with 18446744073709551616%Z; lia).
  apply bv_eq. rewrite sub64_31 moi64_mod.
  unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 32)) with 4294967296.
  change 18446744073709551616 with (2^64).
  change (2^32) with 4294967296.
  rewrite (Z.mod_small k (2^64) Hk64). reflexivity.
Qed.

(* ---- [srliw a5,a5,0x4]: an unsigned divide of a uint by IPB ---- *)
Lemma iu_srliw4 (w : mword 32) :
  sign_extend' 64 (shift_bits_right
     (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
     (mword_of_int 4 : mword 5))
  = (mword_of_int (bv_unsigned w / 16) : mword 64).
Proof.
  rewrite iu_sub31_sext.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 Hw1].
  assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  rewrite Hm32 in Hw1.
  destruct (iu_div16_arith (bv_unsigned w) Hw0 Hw1) as (Hd0 & Hd1 & Hd2).
  assert (Hs : shift_bits_right w (mword_of_int 4 : mword 5) = shiftr w 4).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hs.
  assert (Hq : shiftr w 4 = (mword_of_int (bv_unsigned w / 16) : mword 32)).
  { apply bv_eq.
    unfold shiftr, SailStdpp.Values.with_word, get_word,
      MachineWord.MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (H4 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 32)
                   (MachineWord.MachineWord.Z_idx 4)) = 4).
    { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm32. lia. }
    rewrite H4 Z.shiftr_div_pow2; [| lia].
    change (2 ^ 4)%Z with 16%Z.
    rewrite moi32_unsigned. symmetry. apply bvw32_small.
    change (2^32)%Z with 4294967296%Z. lia. }
  rewrite Hq. apply sext32_64_small.
  change (2^31)%Z with 2147483648%Z. lia.
Qed.

(* ---- [addw a1,a1,a5]: IBLOCK, in 32 bits, with no wrap ---- *)
Local Lemma iu_ibl_arith (u st : Z) :
  0 <= u -> u < 4294967296 -> 0 <= st -> 0 <= u / 16 + st < 2147483648 ->
  (0 <= st < 4294967296)
  /\ (0 <= u / 16 < 4294967296)
  /\ (0 <= u / 16 + st < 4294967296)
  /\ st + u / 16 = u / 16 + st.
Proof.
  intros H0 H1 H2 H3.
  assert (Ha : 0 <= u / 16) by (apply Z.div_pos; lia).
  split_and!; lia.
Qed.

Lemma iu_addw_ibl (inum : mword 32) (inodestart : Z) :
  0 <= inodestart ->
  0 <= IBLOCK inum inodestart < 2147483648 ->
  sign_extend' 64
    (add_vec (subrange_vec_dec
                (sign_extend' 64 (mword_of_int inodestart : mword 32) : mword 64) 31 0
                : mword 32)
             (subrange_vec_dec
                (mword_of_int (bv_unsigned inum / 16) : mword 64) 31 0 : mword 32))
  = sign_extend' 64 (mword_of_int (IBLOCK inum inodestart) : mword 32).
Proof.
  intros Hst Hib.
  pose proof (bv_unsigned_in_range _ inum) as [Hw0 Hw1].
  assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  rewrite Hm32 in Hw1.
  destruct (iu_div16_arith (bv_unsigned inum) Hw0 Hw1) as (Hd0 & Hd1 & Hd2).
  unfold IBLOCK in Hib.
  destruct (iu_ibl_arith (bv_unsigned inum) inodestart Hw0 Hw1 Hst Hib)
    as (Hb1 & Hb2 & Hb3 & Hcomm).
  rewrite iu_sub31_sext.
  rewrite (iu_sub31_moi (bv_unsigned inum / 16) Hd0 Hd2).
  apply f_equal.
  apply bv_eq. rewrite bv_add_unsigned !moi32_unsigned.
  unfold IBLOCK.
  rewrite (bvw32_small inodestart Hb1).
  rewrite (bvw32_small (bv_unsigned inum / 16) Hb2).
  rewrite (bvw32_small (bv_unsigned inum / 16 + inodestart) Hb3).
  unfold bv_wrap. rewrite Hm32. rewrite Hcomm.
  apply Z.mod_small. exact Hb3.
Qed.

(* ---- [andi a4,a4,15]: the slot index ---- *)
Lemma iu_sext_mod16 (w : mword 32) :
  bv_unsigned (sign_extend' 64 w : mword 64) `mod` 16 = bv_unsigned w `mod` 16.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       SailStdpp.Values.to_word to_word get_word MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold bv_wrap.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Hm64.
  rewrite (z_mod16_of_mod (bv_signed w) 18446744073709551616
             ltac:(exists 1152921504606846976; reflexivity)).
  unfold bv_signed, bv_swrap, bv_wrap.
  assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  assert (Hh32 : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2147483648)
    by (vm_compute; reflexivity).
  rewrite Hm32 Hh32. apply z_swrap32_mod16.
Qed.

Lemma iu_andi15 (x : mword 64) :
  and_vec x (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)) : mword 64)
  = (mword_of_int (bv_unsigned x `mod` 16) : mword 64).
Proof.
  assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)) : mword 64)
               = mword_of_int 15) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply bv_eq. rewrite and_vec64_unsigned.
  assert (H15 : bv_unsigned (mword_of_int 15 : mword 64) = 15)
    by (vm_compute; reflexivity).
  rewrite H15 moi64_unsigned z_land15.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
  destruct (iu_mod16_arith (bv_unsigned x) Hx0) as [Hr0 Hr1].
  symmetry. apply bvw64_small.
  change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

(* ---- [slli a4,0x6]: scale the slot index to a byte offset ---- *)
Local Lemma iu_slli_arith (r : Z) : 0 <= r -> r < 16 ->
  0 <= r * 64 /\ r * 64 < 18446744073709551616 /\ 64 * r = r * 64.
Proof. intros H0 H1. split_and!; lia. Qed.

Lemma iu_slli6 (r : Z) : 0 <= r -> r < 16 ->
  shift_bits_left (mword_of_int r : mword 64)
    (subrange_vec_dec (mword_of_int 6 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (64 * r) : mword 64).
Proof.
  intros H0 H1.
  destruct (iu_slli_arith r H0 H1) as (Hl & Hh & Hc).
  assert (Hs : shift_bits_left (mword_of_int r : mword 64)
                 (subrange_vec_dec (mword_of_int 6 : mword 6) (Z.sub log2_xlen 1) 0)
               = shiftl (mword_of_int r : mword 64) 6).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftl, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H6 : bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 64)
                 (MachineWord.MachineWord.Z_idx 6)) = 6).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H6 !moi64_unsigned.
  rewrite (bvw64_small r ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftl_mul_pow2; [| lia]. change (2 ^ 6)%Z with 64%Z.
  rewrite Hc. reflexivity.
Qed.

(* ===================================================================== *)
(*  (2) Addresses                                                         *)
(* ===================================================================== *)

Lemma iu_pa_add_moi (p : mword 64) (nn : nat) :
  add_vec p (mword_of_int (Z.of_nat nn)) = pa_add p nn.
Proof. reflexivity. Qed.

(* [addi a5,a0,88] : a0 = bp, a5 = bp->data *)
Lemma iu_data_addr (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
              = mword_of_int (Z.of_nat 88%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H iu_pa_add_moi. reflexivity.
Qed.

(* [c.add a5,a5,a4] : a5 = bp->data + 64*(inum % IPB) *)
Lemma iu_slot_addr (p : mword 64) (k : nat) :
  add_vec (b_data p) (mword_of_int (64 * Z.of_nat k))
  = pa_add (b_data p) (64 * k)%nat.
Proof. rewrite -iu_pa_add_moi. f_equal. f_equal. lia. Qed.

(* a small non-negative displacement off a base *)
Lemma iu_disp (p : mword 64) (d : Z) (nn : nat) :
  0 <= d -> d < 2048 -> Z.of_nat nn = d ->
  add_vec p (sign_extend' 64 (mword_of_int d : mword 12)) = pa_add p nn.
Proof.
  intros H0 H1 Hn.
  assert (H : (sign_extend' 64 (mword_of_int d : mword 12) : mword 64)
              = mword_of_int (Z.of_nat nn)).
  { rewrite Hn. apply bv_eq.
    unfold sign_extend', Operators_mwords.sign_extend,
      Operators_mwords.exts_vec, SailStdpp.Values.to_word, to_word, get_word,
      MachineWord.MachineWord.sign_extend.
    rewrite bv_sign_extend_unsigned.
    assert (Hu : bv_signed (mword_of_int d : mword 12) = d).
    { unfold bv_signed, bv_swrap, bv_wrap.
      assert (Hm : bv_modulus (MachineWord.MachineWord.Z_idx 12) = 4096)
        by (vm_compute; reflexivity).
      assert (Hh : bv_half_modulus (MachineWord.MachineWord.Z_idx 12) = 2048)
        by (vm_compute; reflexivity).
      unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hm Hh.
      rewrite (Z.mod_small d 4096 ltac:(lia)).
      rewrite (Z.mod_small (d + 2048) 4096 ltac:(lia)). lia. }
    rewrite Hu moi64_mod. unfold bv_wrap.
    assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                   = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite Hm64. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma iu_off0 (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 0 : mword 12)) = p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
              = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. apply kv_addv_zero.
Qed.

(* [addi a1,s1,80] : the base of ip->addrs *)
Lemma iu_addrs0 (ip : mword 64) :
  add_vec ip (sign_extend' 64 (mword_of_int 80 : mword 12)) = i_addr ip 0.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 80 : mword 12) : mword 64)
              = mword_of_int (80 + 4 * Z.of_nat 0%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

(* ---- ALIGNMENT of the five field cells, from bcache's geometry.  The
   slot's base is [bcache + 24 + 1112*k + 88 + 64*q], and 8 divides every
   term, so the four halfword cells are 2-aligned and the size cell is
   4-aligned. ---- *)
(* [ByteBuf.bb_align_z] at an arbitrary alignment: the four halfword cells
   want 2 and the size cell wants 4. *)
Local Lemma iu_align_z (x dv : Z) :
  0 <= x -> x < 18446744073709551616 -> 0 < dv -> x `mod` dv = 0 ->
  Z.rem (bv_wrap 64 x) dv = 0.
Proof.
  intros H0 H1 Hd Hm.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite (Z.mod_small x); [| lia].
  rewrite Z.rem_mod_nonneg; [exact Hm | lia | lia].
Qed.

Local Lemma iu_align_arith (kk qq off dv : Z) :
  0 <= kk -> kk < 30 -> 0 <= qq -> qq < 16 -> 0 <= off -> off < 64 ->
  (dv = 2 \/ dv = 4) -> off `mod` dv = 0 ->
  (2147582464 + 1112 * kk + (88 + (64 * qq + off))) `mod` dv = 0
  /\ 0 <= 2147582464 + 1112 * kk + (88 + (64 * qq + off))
  /\ 2147582464 + 1112 * kk + (88 + (64 * qq + off)) < 18446744073709551616.
Proof.
  intros H1 H2 H3 H4 H5 H6 Hd Hoff. split_and!; [| lia | lia].
  assert (Hz : 2147582464 + 1112 * kk + (88 + (64 * qq + off))
               = (536895638 + 278 * kk + 16 * qq) * 4 + off) by lia.
  rewrite Hz. destruct Hd as [-> | ->].
  - rewrite Z.add_mod; [| lia]. rewrite Hoff.
    replace ((536895638 + 278 * kk + 16 * qq) * 4) with
      ((536895638 + 278 * kk + 16 * qq) * 2 * 2) by lia.
    rewrite Z_mod_mult. reflexivity.
  - rewrite Z.add_mod; [| lia]. rewrite Hoff Z_mod_mult. reflexivity.
Qed.

Lemma iu_align (k q : nat) (off : nat) (dv : Z) :
  (k < NBUF)%nat -> (q < 16)%nat -> (off < 64)%nat ->
  (dv = 2 \/ dv = 4) -> Z.of_nat off `mod` dv = 0 ->
  is_aligned_paddr
    (Physaddr (pa_add (b_data (bnode k)) (64 * q + off)%nat)) dv = true.
Proof.
  intros Hk Hq Hoff Hdv Hm.
  unfold b_data. rewrite pa_add_add.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  destruct (iu_align_arith (Z.of_nat k) (Z.of_nat q) (Z.of_nat off) dv
              ltac:(lia) ltac:(unfold NBUF in Hk; lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) Hdv Hm)
    as (Hmod & Hlo & Hhi).
  replace (0x800181e8 + 24 + 1112 * Z.of_nat k + Z.of_nat (88 + (64 * q + off)))
    with (2147582464 + 1112 * Z.of_nat k
          + (88 + (64 * Z.of_nat q + Z.of_nat off))) by lia.
  apply iu_align_z; [exact Hlo | exact Hhi | destruct Hdv as [-> | ->]; lia
                    | exact Hmod].
Qed.

(* ===================================================================== *)
(*  (3) The dinode slot as a resource                                     *)
(* ===================================================================== *)

Section IupdateRes.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !fsLogG Σ, !bioG Σ}.

  (* the 64 bytes at [a], read as [dinode_bytes d]: the six pieces the four
     [sh]s, the [sw] and the [memmove] touch, at the offsets those
     instructions encode *)
  Definition dislot (a : mword 64) (d : dinode) : iProp Σ :=
    (a ↦₂ di_type d ∗
     pa_add a 2 ↦₂ di_major d ∗
     pa_add a 4 ↦₂ di_minor d ∗
     pa_add a 6 ↦₂ di_nlink d ∗
     pa_add a 8 ↦₄ di_size d ∗
     bb_bytes (pa_add a 12) 52 (fun j => ind_bytes (di_addrs d) !!! j))%I.

  Definition dislot_align (a : mword 64) : Prop :=
    is_aligned_paddr (Physaddr a) 2 = true
    /\ is_aligned_paddr (Physaddr (pa_add a 2)) 2 = true
    /\ is_aligned_paddr (Physaddr (pa_add a 4)) 2 = true
    /\ is_aligned_paddr (Physaddr (pa_add a 6)) 2 = true
    /\ is_aligned_paddr (Physaddr (pa_add a 8)) 4 = true.

  (* re-anchoring a byte window: [bb_split3] produces NESTED bases and
     nested naming offsets, and the six-way split below normalises each *)
  Local Lemma bb_reanchor (a c : mword 64) (n : nat) (f g : nat -> bv 8) :
    a = c -> (forall j, (j < n)%nat -> f j = g j) ->
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, pa_add c j ↦ₘ g j).
  Proof.
    intros -> Hfg. apply big_sepL_proper. intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hfg;
      [reflexivity | lia].
  Qed.

  Local Lemma dislot_split (a : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 64, pa_add a j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ f j)
      ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 2) j ↦ₘ f (2 + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 4) j ↦ₘ f (4 + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 2, pa_add (pa_add a 6) j ↦ₘ f (6 + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 4, pa_add (pa_add a 8) j ↦ₘ f (8 + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 52, pa_add (pa_add a 12) j ↦ₘ f (12 + j)%nat).
  Proof.
    (* type@0 and major@2 *)
    rewrite (bb_split3 a 2 2 60 64 f ltac:(lia)).
    apply bi.sep_proper; [reflexivity |].
    apply bi.sep_proper; [reflexivity |].
    (* the remaining 60 bytes, re-anchored at a+4 *)
    rewrite (bb_reanchor (pa_add (pa_add a 2) 2) (pa_add a 4) 60
               (fun j => f (2 + (2 + j))%nat) (fun j => f (4 + j)%nat)
               ltac:(rewrite pa_add_add; reflexivity)
               ltac:(intros j _; f_equal; lia)).
    (* minor@4 and nlink@6 *)
    rewrite (bb_split3 (pa_add a 4) 2 2 56 60 (fun j => f (4 + j)%nat) ltac:(lia)).
    apply bi.sep_proper; [reflexivity |].
    apply bi.sep_proper.
    { apply bb_reanchor;
        [rewrite pa_add_add; reflexivity | intros j _; f_equal; lia]. }
    (* the remaining 56 bytes, re-anchored at a+8 *)
    rewrite (bb_reanchor (pa_add (pa_add (pa_add a 4) 2) 2) (pa_add a 8) 56
               (fun j => f (4 + (2 + (2 + j)))%nat) (fun j => f (8 + j)%nat)
               ltac:(rewrite !pa_add_add; reflexivity)
               ltac:(intros j _; f_equal; lia)).
    (* size@8 and addrs@12 *)
    rewrite (bb_split3 (pa_add a 8) 4 52 0 56 (fun j => f (8 + j)%nat) ltac:(lia)).
    rewrite big_sepL_nil bi.sep_emp.
    apply bi.sep_proper; [reflexivity |].
    apply bb_reanchor;
      [rewrite pa_add_add; reflexivity | intros j _; f_equal; lia].
  Qed.

  (* the two window-to-cell conversions, driven by a pointwise reading *)
  Local Lemma bb2_cell (a : mword 64) (w : bv 16) (f : nat -> bv 8) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    (forall j, (j < 2)%nat -> f j = nth_byte w j) ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ f j) ⊣⊢ a ↦₂ w.
  Proof.
    intros Hal Hf.
    rewrite /word2_pointsto (bi.pure_True _ Hal) bi.True_sep.
    apply big_sepL_proper. intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hf;
      [reflexivity | lia].
  Qed.

  Local Lemma bb4_cell (a : mword 64) (w : bv 32) (f : nat -> bv 8) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    (forall j, (j < 4)%nat -> f j = nth_byte w j) ->
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ f j) ⊣⊢ a ↦₄ w.
  Proof.
    intros Hal Hf.
    rewrite /word4_pointsto (bi.pure_True _ Hal) bi.True_sep.
    apply big_sepL_proper. intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hf;
      [reflexivity | lia].
  Qed.

  (* THE SLOT, at an abstract naming function.  Out at [d], back at any
     [d'] -- which is the whole of what the four [sh]s, the [sw] and the
     [memmove] do to the buffer. *)
  Lemma dislot_acc_gen (a : mword 64) (f : nat -> bv 8) (d : dinode) :
    dislot_align a ->
    (forall j, (j < 64)%nat -> f j = dinode_bytes d !!! j) ->
    ([∗ list] j ∈ seq 0 64, pa_add a j ↦ₘ f j) -∗
      dislot a d ∗
      (∀ (d' : dinode) (g : nat -> bv 8),
         ⌜forall j, (j < 64)%nat -> g j = dinode_bytes d' !!! j⌝ -∗
         dislot a d' -∗ ([∗ list] j ∈ seq 0 64, pa_add a j ↦ₘ g j)).
  Proof.
    intros (Ha0 & Ha2 & Ha4 & Ha6 & Ha8) Hf.
    (* the six pointwise readings, for an arbitrary record *)
    assert (Hp0 : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 2)%nat -> h j = nth_byte (di_type dd) j).
    { intros dd h Hh j Hj. rewrite (Hh j ltac:(lia)).
      apply dinode_bytes_type_t; exact Hj. }
    assert (Hp2 : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 2)%nat -> h (2 + j)%nat = nth_byte (di_major dd) j).
    { intros dd h Hh j Hj. rewrite (Hh (2 + j)%nat ltac:(lia)).
      apply dinode_bytes_major_t; exact Hj. }
    assert (Hp4 : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 2)%nat -> h (4 + j)%nat = nth_byte (di_minor dd) j).
    { intros dd h Hh j Hj. rewrite (Hh (4 + j)%nat ltac:(lia)).
      apply dinode_bytes_minor_t; exact Hj. }
    assert (Hp6 : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 2)%nat -> h (6 + j)%nat = nth_byte (di_nlink dd) j).
    { intros dd h Hh j Hj. rewrite (Hh (6 + j)%nat ltac:(lia)).
      apply dinode_bytes_nlink_t; exact Hj. }
    assert (Hp8 : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 4)%nat -> h (8 + j)%nat = nth_byte (di_size dd) j).
    { intros dd h Hh j Hj. rewrite (Hh (8 + j)%nat ltac:(lia)).
      apply dinode_bytes_size_t; exact Hj. }
    assert (Hpa : forall (dd : dinode) (h : nat -> bv 8),
              (forall j, (j < 64)%nat -> h j = dinode_bytes dd !!! j) ->
              forall j, (j < 52)%nat ->
                h (12 + j)%nat = ind_bytes (di_addrs dd) !!! j).
    { intros dd h Hh j Hj. rewrite (Hh (12 + j)%nat ltac:(lia)).
      apply dinode_bytes_addrs_t. }
    iIntros "H".
    rewrite (dislot_split a f).
    iDestruct "H" as "(H0 & H2 & H4 & H6 & H8 & Ha)".
    iSplitL "H0 H2 H4 H6 H8 Ha".
    { rewrite /dislot.
      iEval (rewrite (bb2_cell a (di_type d) f Ha0 (Hp0 d f Hf))) in "H0".
      iEval (rewrite (bb2_cell (pa_add a 2) (di_major d)
                        (fun j => f (2 + j)%nat) Ha2 (Hp2 d f Hf))) in "H2".
      iEval (rewrite (bb2_cell (pa_add a 4) (di_minor d)
                        (fun j => f (4 + j)%nat) Ha4 (Hp4 d f Hf))) in "H4".
      iEval (rewrite (bb2_cell (pa_add a 6) (di_nlink d)
                        (fun j => f (6 + j)%nat) Ha6 (Hp6 d f Hf))) in "H6".
      iEval (rewrite (bb4_cell (pa_add a 8) (di_size d)
                        (fun j => f (8 + j)%nat) Ha8 (Hp8 d f Hf))) in "H8".
      iEval (rewrite (bb_ext (pa_add a 12) 52 (fun j => f (12 + j)%nat)
                       (fun j => ind_bytes (di_addrs d) !!! j) (Hpa d f Hf)))
        in "Ha".
      rewrite /bb_bytes.
      iFrame "H0 H2 H4 H6 H8 Ha". }
    iIntros (d' g) "%Hg [B0 [B2 [B4 [B6 [B8 Ba]]]]]".
    rewrite (dislot_split a g).
    iEval (rewrite (bb2_cell a (di_type d') g Ha0 (Hp0 d' g Hg))).
    iEval (rewrite (bb2_cell (pa_add a 2) (di_major d')
                      (fun j => g (2 + j)%nat) Ha2 (Hp2 d' g Hg))).
    iEval (rewrite (bb2_cell (pa_add a 4) (di_minor d')
                      (fun j => g (4 + j)%nat) Ha4 (Hp4 d' g Hg))).
    iEval (rewrite (bb2_cell (pa_add a 6) (di_nlink d')
                      (fun j => g (6 + j)%nat) Ha6 (Hp6 d' g Hg))).
    iEval (rewrite (bb4_cell (pa_add a 8) (di_size d')
                      (fun j => g (8 + j)%nat) Ha8 (Hp8 d' g Hg))).
    iEval (rewrite (bb_ext (pa_add a 12) 52 (fun j => g (12 + j)%nat)
                     (fun j => ind_bytes (di_addrs d') !!! j) (Hpa d' g Hg))).
    iFrame "B0 B2 B4 B6 B8". rewrite /bb_bytes. iExact "Ba".
  Qed.

  (* borrow dinode slot [k] out of a whole block's byte image, and give it
     back AT A NEW DINODE. *)
  Lemma diblk_slot_acc (a : mword 64) (ds : list dinode) (k : nat) :
    diblk_wf ds -> (k < 16)%nat ->
    dislot_align (pa_add a (64 * k)%nat) ->
    bb_bytes a 1024 (fun j => diblk_bytes ds !!! j) -∗
      dislot (pa_add a (64 * k)%nat) (ds !!! k) ∗
      (∀ d : dinode, ⌜dinode_wf d⌝ -∗ dislot (pa_add a (64 * k)%nat) d -∗
         bb_bytes a 1024 (fun j => diblk_bytes (<[k := d]> ds) !!! j)).
  Proof.
    intros [Hlen Hall] Hk Hal.
    assert (Hklen : (k < length ds)%nat) by (rewrite Hlen; exact Hk).
    iIntros "H". rewrite /bb_bytes.
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes ds !!! j) ltac:(lia)).
    iDestruct "H" as "(Hpre & Hmid & Hsuf)".
    iDestruct (dislot_acc_gen (pa_add a (64 * k)%nat)
                 (fun j => diblk_bytes ds !!! (64 * k + j)%nat) (ds !!! k)
                 Hal
                 ltac:(intros j Hj; apply diblk_bytes_lookup_t;
                       [exact Hall | exact Hklen | exact Hj])
                 with "Hmid") as "[Hslot Hback]".
    iSplitL "Hslot"; [iExact "Hslot" |].
    iIntros (d) "%Hd Hslot".
    iDestruct ("Hback" $! d (fun j => diblk_bytes (<[k := d]> ds) !!! (64 * k + j)%nat)
                 with "[%] Hslot") as "Hmid".
    { intros j Hj. apply diblk_bytes_insert_same_t;
        [exact Hall | exact Hd | exact Hklen | exact Hj]. }
    rewrite (bb_split3 a (64 * k)%nat 64 (1024 - (64 * k + 64))%nat 1024
               (fun j => diblk_bytes (<[k := d]> ds) !!! j) ltac:(lia)).
    iSplitL "Hpre".
    { iApply (big_sepL_mono with "Hpre"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (diblk_bytes_insert_other_t ds k d i Hall Hd Hklen ltac:(left; lia)).
      reflexivity. }
    iSplitL "Hmid"; [iExact "Hmid" |].
    iApply (big_sepL_mono with "Hsuf"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (diblk_bytes_insert_other_t ds k d (64 * k + (64 + i))%nat
               Hall Hd Hklen ltac:(right; lia)).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (4) The handle                                                     *)
  (* ------------------------------------------------------------------ *)

  Lemma iu_held_k (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗ ⌜(k < NBUF)%nat⌝.
  Proof. rewrite /bio_held. iIntros "(%A & _)". done. Qed.

  (* THE traveling-bytes swap: the whole of what iupdate does to the buffer *)
  Lemma iu_held_swap (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗
      buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
      (∀ bs' : list (bv 8),
         buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs' -∗
         bio_held bn V k pidv dev bno bs' bsl bsd d).
  Proof.
    rewrite /bio_held.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iSplitL "H5"; [iExact "H5" |].
    iIntros (bs') "H5".
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitL "H1"; [iExact "H1" |]. iSplitL "H2"; [iExact "H2" |].
    iSplitL "H3"; [iExact "H3" |]. iSplitL "H4"; [iExact "H4" |].
    iSplitL "H5"; [iExact "H5" |]. iSplitL "H6"; [iExact "H6" |]. iExact "H7".
  Qed.

  (* THE COUPLING: the caller's own [fsblock] half against the handle's
     machinery half pins the buffer's logical content -- which is what
     makes the bytes bread returned BE [diblk_bytes ds]. *)
  Lemma iu_held_content (bn : bio_names) (γfs : fs_names) (γd : disk_names)
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

  (* the buffer's byte LIST, as the [ByteBuf] window the slot accessor
     takes, and back *)
  Lemma iu_buf_bytes (p : mword 64) (bno dsk : mword 32) (ds : list dinode) :
    diblk_wf ds ->
    buf_own p bno dsk (diblk_bytes ds) -∗
      bb_bytes (b_data p) 1024 (fun j => diblk_bytes ds !!! j) ∗
      (∀ ds' : list dinode, ⌜diblk_wf ds'⌝ -∗
         bb_bytes (b_data p) 1024 (fun j => diblk_bytes ds' !!! j) -∗
         buf_own p bno dsk (diblk_bytes ds')).
  Proof.
    intros Hwf.
    iIntros "(Hb & Hd & %Hlen & Hby)".
    iEval (rewrite (bb_bytes_of_list (b_data p) (diblk_bytes ds))
                   (diblk_bytes_length_16 ds Hwf)) in "Hby".
    iSplitL "Hby"; [iExact "Hby" |].
    iIntros (ds') "%Hwf' Hby".
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb" |]. iSplitL "Hd"; [iExact "Hd" |].
    iSplitR; [iPureIntro; exact (diblk_bytes_length_16 ds' Hwf') |].
    iEval (rewrite -(diblk_bytes_length_16 ds' Hwf')
                   -(bb_bytes_of_list (b_data p) (diblk_bytes ds'))) in "Hby".
    iExact "Hby".
  Qed.

  (* slot-unit bookkeeping *)
  Lemma iu_slots_split (bn : bio_names) (a c : nat) :
    bslots bn (a + c) -∗ bslots bn a ∗ bslots bn c.
  Proof. rewrite bslots_op. iIntros "$". Qed.

  Lemma iu_slots_join (bn : bio_names) (a c : nat) :
    bslots bn a -∗ bslots bn c -∗ bslots bn (a + c).
  Proof.
    iIntros "H1 H2". rewrite bslots_op. iSplitL "H1"; [iExact "H1" | iExact "H2"].
  Qed.

  (* THE MACHINERY HALF, out of the handle and back.  [InodeInv.ireg_read_blk]
     needs the block's OTHER [fs_L] half to pin the region's parked bytes to
     the ones bread returned, and the handle's payload carries exactly that --
     on BOTH polarities.

     This is [ProofIupdate.iu_held_L] / [ProofIalloc.ia_held_L], hoisted here
     (N5d) because every whole-block reader of the inode region wants it and a
     Proof file may not require another Proof file.  The two private copies are
     left where they are: retiring them would cost a recompile of their cones
     for nothing. *)
  Lemma ds_held_L (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
      (uint bno ↪[fs_L γfs]{#(1/2)} bsl) ∗
      ((uint bno ↪[fs_L γfs]{#(1/2)} bsl) -∗
       bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & H5 & H6 & Hpay)".
    destruct d.
    - rewrite /fs_mdirty. iDestruct "Hpay" as "[[HL HD] Hq]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD Hq".
    - rewrite /fs_mclean. iDestruct "Hpay" as "[[HL HD] %He]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H2 H3 H4 H5 H6". iFrame "HL HD". done.
  Qed.

End IupdateRes.

(* ===================================================================== *)
(*  (5) THE WHOLE-REGION SCAN'S ARITHMETIC                                *)
(*                                                                        *)
(*  ialloc and ireclaim both walk every inum in the region, and both do    *)
(*  the slot arithmetic on the SIGN-EXTENDED 64-bit inum rather than on    *)
(*  the 32-bit one iupdate/ilock start from, so group (1)'s [iu_srliw4]    *)
(*  and friends do not apply to them.  Hoisted out of ProofIalloc.v (N5d)  *)
(*  so that ireclaim -- and create, and any later scanner -- does not have *)
(*  to restate 100 lines of bitvector arithmetic.  ProofIalloc.v keeps its *)
(*  own [ia_*] copies; they are identical and retiring them would cost a   *)
(*  recompile for nothing.                                                *)
(* ===================================================================== *)

(* the sign extension of a value that fits in 31 bits is its own value *)
Lemma ds_sext_small (w : mword 32) :
  bv_unsigned w < 2147483648 -> (sign_extend' 64 w : mword 64)
                                = mword_of_int (bv_unsigned w).
Proof.
  intro Hw. pose proof (bv_unsigned_in_range _ w) as [Hw0 _].
  rewrite -(sext32_64_small (bv_unsigned w)
              ltac:(change (2^31)%Z with 2147483648%Z; lia)).
  f_equal. apply bv_eq. rewrite moi32_unsigned. symmetry.
  apply bvw32_small. change (2^32)%Z with 4294967296%Z. lia.
Qed.

(* [srli a1,s2,4] -- the 64-bit divide by IPB.  [iu_srliw4] is the [srliw]
   twin and does NOT apply: it truncates to 32 bits first. *)
Lemma ds_srli4 (w : mword 32) :
  bv_unsigned w < 2147483648 ->
  shift_bits_right (sign_extend' 64 w : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (bv_unsigned w / 16) : mword 64).
Proof.
  intros Hw.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 _].
  rewrite (ds_sext_small w Hw).
  assert (Hs : shift_bits_right (mword_of_int (bv_unsigned w) : mword 64)
                 (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
               = shiftr (mword_of_int (bv_unsigned w) : mword 64) 4).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H4 : bv_unsigned (MachineWord.MachineWord.N_to_word
                 (MachineWord.MachineWord.Z_idx 64)
                 (MachineWord.MachineWord.Z_idx 4)) = 4).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H4 !moi64_unsigned.
  rewrite (bvw64_small (bv_unsigned w)
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 4)%Z with 16%Z.
  symmetry. apply bvw64_small.
  assert (Hd0 : 0 <= bv_unsigned w / 16) by (apply Z.div_pos; lia).
  assert (Hd1 : bv_unsigned w / 16 <= bv_unsigned w)
    by (apply Z.div_le_upper_bound; lia).
  change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

(* [c.addw a1,a5] sums (inum/16) + inodestart; [iu_addw_ibl] is stated the
   other way round *)
Lemma ds_add_vec32_comm (x y : mword 32) : add_vec x y = add_vec y x.
Proof. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia. Qed.

(* [andi a5,s2,15] -- the BASE-encoding twin of [iu_andi15]'s [c.andi] *)
Lemma ds_andi15 (x : mword 64) :
  and_vec x (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
  = (mword_of_int (bv_unsigned x `mod` 16) : mword 64).
Proof.
  assert (Hc : (sign_extend' 64 (mword_of_int 15 : mword 12) : mword 64)
               = sign_extend' 64 (sign_extend' 12 (mword_of_int 15 : mword 6)))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply iu_andi15.
Qed.

(* the [lh]'s zero test, both ways -- ProofIlock's [il_type_*] pair *)
Lemma ds_sext64_16_inj (a c : mword 16) :
  (sign_extend' 64 a : mword 64) = sign_extend' 64 c -> a = c.
Proof.
  intro H. rewrite -(trunc16_sext64 a) -(trunc16_sext64 c) H. reflexivity.
Qed.

Lemma ds_type_zero (w : mword 16) :
  bv_unsigned w = 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro Hw.
  assert (Hz : w = (mword_of_int 0 : mword 16))
    by (apply bv_eq; rewrite Hw; vm_compute; reflexivity).
  rewrite Hz. vm_compute. reflexivity.
Qed.

Lemma ds_type_nonzero (w : mword 16) :
  bv_unsigned w <> 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hw. apply eq_vec_false_iff. intro Hq. apply Hw.
  assert (Hz : (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 16))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hz in Hq. apply ds_sext64_16_inj in Hq. rewrite Hq.
  vm_compute. reflexivity.
Qed.

(* the loop guards' branch predicates, at the two words the code compares *)
Lemma ds_uint64_moi (z : Z) : 0 <= z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro Hz. rewrite uint_unsigned. apply moi64_small. exact Hz. Qed.

Lemma ds_bgeu_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  zopz0zKzJ_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_u.
  rewrite (ds_uint64_moi x Hx) (ds_uint64_moi y Hy). reflexivity.
Qed.

Lemma ds_bltu_moi (x y : Z) :
  0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  zopz0zI_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.ltb x y.
Proof.
  intros Hx Hy. unfold zopz0zI_u.
  rewrite (ds_uint64_moi x Hx) (ds_uint64_moi y Hy). reflexivity.
Qed.

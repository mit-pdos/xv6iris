(* ProofBfree.v -- bfree over the SIE-agnostic sconf world.

     static void bfree(int dev, uint b) {
       struct buf *bp;  int bi, m;
       bp = bread(dev, BBLOCK(b, sb));
       bi = b % BPB;  m = 1 << (bi % 8);
       if((bp->data[bi/8] & m) == 0) panic("freeing free block");
       bp->data[bi/8] &= ~m;
       log_write(bp);
       brelse(bp);
     }

   STRAIGHT-LINE apart from the one panic arm, which is DEAD.  Two lemmas,
   entered left to right, so the file's two Qeds stay small:

     [bf_tail]          +0x4a .. +0x5e   log_write, brelse, pop, ret and
                                         the contract.
     [wp_bfree_sconf]   +0x00 .. +0x46   prologue, bread, the bit test, the
                                         clear and the byte store.

   HOW THE PANIC DIES (the point of the whole exercise).  The caller arrives
   holding [blk_own γfs b] -- a FULL-fraction ghost_map element -- while
   [BitmapInv.free_pool] holds one such token for every block below [size]
   whose bit is CLEAR.  [BitmapInv.free_pool_own_used] therefore gives
   [b ∈ used] outright, and [BitmapEnc.bm_bit_test] turns that into
   [bp->data[bi/8] & m = 2^(b mod 8) <> 0]: the [c.beqz] at +0x3a falls
   THROUGH, and the arm at +0x60 is never entered.  Nothing about the panic
   is proved -- it is refuted.  [panic_wp_any] is still threaded because
   bread's own interior panic arm wants one.

   ONE BITMAP BLOCK.  [size <= BPB] is a premise, so [BBLOCK b sb] collapses
   to [sb.bmapstart] ([BitmapInv.BBLOCK_single]): the [srliw a5,a1,0xd] at
   +0x0e contributes zero and the [(b << 51) >> 54] at +0x2a/+0x2c is just
   [b / 8].

   THE ONE MISSING LEAF.  [sllw rd,rs1,rs2] (the mask [1 << (bi % 8)] at
   +0x26) has no WP leaf in the S-mode ALU layer -- [slliw] is there, the
   register-register W shift is not -- so it is proved here, exactly the way
   [WpSconfSrliw.v] proves [srliw]: an exec bridge at the SLLW branch of
   [execute_RTYPEW] plus one [wp_gpr_write_s_sconf_base] instance.  It
   belongs in [WpMmodeShiftiop.v] + [WpSconfAlu.v] beside its ADDW/SUBW
   twins, and balloc needs the same leaf; homing it there is owed. *)
From Stdlib Require Import Eqdep_dec ZArith Bool Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext WpGpr.
Require Import WpMmodeLeafBase WpMmodeShiftiop.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import VcGen.
Require Import IntrDefs WpSmodeIntr.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfVc WpSconfBtype.
Require Import WpSconfSrliw.
Require Import ByteBuf.
Require Import PrintintArith.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import DinodeSlot.
Require Import BitmapEnc BitmapInv.
Require Import CodeBfree.
Require Import SpecPanic.
Require Import SpecBread SpecBrelse SpecLogWrite.
Require Import SpecBfree.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  bfree's own pure vocabulary.  All of it is over plain [Z] / closed     *)
(*  words, so no solver ever runs inside the WP context.                   *)
(* ===================================================================== *)

(* ---- the two mword-FREE arithmetic helpers ---- *)
Local Lemma bf_div8192_arith (u : Z) : 0 <= u -> u < 4294967296 ->
  0 <= u / 8192 /\ u / 8192 < 2147483648 /\ u / 8192 < 4294967296.
Proof.
  intros H0 H1.
  assert (Ha : 0 <= u / 8192) by (apply Z.div_pos; lia).
  assert (Hb : u / 8192 < 2147483648) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* EVERY arithmetic fact the WP proof needs about the freed block number and
   about [sb.bmapstart], proved here over plain [Z] variables: inside the WP
   context [lia] is unusable (an [mword] in scope defeats the zify hook --
   claude-notes/durable-notes.md), so nothing there may call it. *)
Local Lemma bf_range (bi size : Z) :
  0 <= bi < size -> 0 < size <= BPB ->
  0 <= bi
  /\ 0 <= bi < 8192
  /\ 0 <= bi < 2 ^ 31
  /\ 0 <= bi < 2 ^ 32
  /\ 0 <= bi < 2 ^ 64
  /\ 0 <= bi < BPB
  /\ 0 <= bi `mod` 8 < 8
  /\ (Z.to_nat (bi `div` 8) < 1024)%nat
  /\ Z.of_nat (Z.to_nat (bi `div` 8)) = bi `div` 8
  /\ 0 <= bi * 2251799813685248 < 18446744073709551616
  /\ bi `div` 8192 = 0.
Proof.
  intros Hb Hs. pose proof Hs as Hs'. rewrite BPB_value in Hs'.
  assert (Hd0 : 0 <= bi `div` 8) by (apply Z.div_pos; lia).
  assert (Hd1 : bi `div` 8 < 1024) by (apply Z.div_lt_upper_bound; lia).
  assert (Hm : 0 <= bi `mod` 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hz : bi `div` 8192 = 0) by (apply Z.div_small; lia).
  assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (H32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  assert (H64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  split_and!; solve [ lia | exact Hz ].
Qed.

Local Lemma bf_bm_range (st : Z) : 0 < st -> st < 2 ^ 31 ->
  0 <= st < 2147483648 /\ 0 <= st < 2 ^ 32.
Proof.
  intros H0 H1.
  assert (H31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (H32 : (2 ^ 32 = 4294967296)%Z) by (vm_compute; reflexivity).
  split_and!; lia.
Qed.

Local Lemma bf_z_land7 (x : Z) : Z.land x 7 = x `mod` 8.
Proof.
  assert (Ho : (7 = Z.ones 3)%Z) by (vm_compute; reflexivity).
  rewrite Ho Z.land_ones; [| lia].
  assert (Hp : (2 ^ 3 = 8)%Z) by (vm_compute; reflexivity).
  rewrite Hp. reflexivity.
Qed.

(* [(b << 51) >> 54] is [b / 8] *)
Local Lemma bf_shift_div (x : Z) : 0 <= x ->
  (x * 2251799813685248) / 18014398509481984 = x / 8.
Proof.
  intros Hx.
  assert (Hf : (18014398509481984 = 2251799813685248 * 8)%Z)
    by (vm_compute; reflexivity).
  rewrite Hf -Z.div_div; [| lia | lia].
  rewrite Z.div_mul; [reflexivity | lia].
Qed.

Local Lemma bf_pow_bound (r : Z) : 0 <= r < 8 -> 0 < 2 ^ r <= 128.
Proof.
  intros Hr. split.
  - apply Z.pow_pos_nonneg; lia.
  - assert (H7 : (2 ^ 7 = 128)%Z) by (vm_compute; reflexivity).
    rewrite -H7. apply Z.pow_le_mono_r; lia.
Qed.

(* a byte has no bits at or above 8 *)
Local Lemma bf_bits_high (x n : Z) : 0 <= x < 256 -> 8 <= n ->
  Z.testbit x n = false.
Proof.
  intros Hx Hn.
  assert (Hm : x = x `mod` 2 ^ 8)
    by (rewrite Z.mod_small; [reflexivity | change (2^8)%Z with 256%Z; lia]).
  rewrite {1}Hm. apply Z.mod_pow2_bits_high. lia.
Qed.

(* [xori a5,a5,-1] gives the 64-bit complement; against a BYTE that is the
   same mask as [Z.lnot], which is the form [BitmapEnc.bm_bit_clear] takes *)
Local Lemma bf_lnot_bridge (x r : Z) : 0 <= x < 256 -> 0 <= r < 8 ->
  Z.land x (Z.lxor (2 ^ r) 18446744073709551615) = Z.land x (Z.lnot (2 ^ r)).
Proof.
  intros Hx Hr. apply Z.bits_inj_iff'. intros n Hn.
  rewrite !Z.land_spec. rewrite Z.lxor_spec.
  rewrite (Z.lnot_spec (2 ^ r) n ltac:(lia)).
  destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - assert (Hones : (18446744073709551615 = Z.ones 64)%Z)
      by (vm_compute; reflexivity).
    rewrite Hones (Z.ones_spec_low 64 n ltac:(lia)).
    destruct (Z.testbit (2 ^ r) n); reflexivity.
  - rewrite (bf_bits_high x n Hx ltac:(lia)). reflexivity.
Qed.

(* ---- the bitvector readings ---- *)
Lemma bf_xor_vec64_unsigned (x y : mword 64) :
  bv_unsigned (xor_vec x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof.
  cbv [xor_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.xor. apply bv_xor_unsigned.
Qed.

Lemma bf_zext8_unsigned (x : mword 8) :
  bv_unsigned (zero_extend' 64 x : mword 64) = bv_unsigned x.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Values.to_word get_word MachineWord.MachineWord.zero_extend].
  rewrite bv_zero_extend_unsigned. reflexivity.
  first [ lia | vm_compute; discriminate | done ].
Qed.

Lemma bf_add_comm (x y : mword 64) : add_vec x y = add_vec y x.
Proof. apply bv_eq. rewrite !add_vec64_unsigned. apply f_equal. lia. Qed.

(* ---- [srliw a5,a1,0xd] : b / BPB, which is 0 for every in-range b ---- *)
Lemma bf_srliw13 (w : mword 32) :
  sign_extend' 64 (shift_bits_right
     (subrange_vec_dec (sign_extend' 64 w : mword 64) 31 0 : mword 32)
     (mword_of_int 13 : mword 5))
  = (mword_of_int (bv_unsigned w / 8192) : mword 64).
Proof.
  rewrite iu_sub31_sext.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 Hw1].
  assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 4294967296)
    by (vm_compute; reflexivity).
  rewrite Hm32 in Hw1.
  destruct (bf_div8192_arith (bv_unsigned w) Hw0 Hw1) as (Hd0 & Hd1 & Hd2).
  assert (Hs : shift_bits_right w (mword_of_int 13 : mword 5) = shiftr w 13).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hs.
  assert (Hq : shiftr w 13 = (mword_of_int (bv_unsigned w / 8192) : mword 32)).
  { apply bv_eq.
    unfold shiftr, SailStdpp.Values.with_word, get_word,
      MachineWord.MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (H13 : bv_unsigned (MachineWord.MachineWord.N_to_word
                    (MachineWord.MachineWord.Z_idx 32)
                    (MachineWord.MachineWord.Z_idx 13)) = 13).
    { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm32. lia. }
    rewrite H13 Z.shiftr_div_pow2; [| lia].
    change (2 ^ 13)%Z with 8192%Z.
    rewrite moi32_unsigned. symmetry. apply bvw32_small.
    change (2^32)%Z with 4294967296%Z. lia. }
  rewrite Hq. apply sext32_64_small.
  change (2^31)%Z with 2147483648%Z. lia.
Qed.

(* ---- [addw a1,a1,a5] with a5 = 0 : BBLOCK collapses to bmapstart ---- *)
Lemma bf_addw0 (st : Z) : 0 <= st < 2147483648 ->
  sign_extend' 64
    (add_vec (subrange_vec_dec
                (sign_extend' 64 (mword_of_int st : mword 32) : mword 64) 31 0
                : mword 32)
             (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32))
  = sign_extend' 64 (mword_of_int st : mword 32).
Proof.
  intros Hst.
  rewrite iu_sub31_sext.
  rewrite (iu_sub31_moi 0 ltac:(lia) ltac:(lia)).
  apply f_equal. apply bv_eq. rewrite bv_add_unsigned.
  assert (H0 : bv_unsigned (mword_of_int 0 : mword 32) = 0)
    by (vm_compute; reflexivity).
  rewrite H0 Z.add_0_r.
  rewrite (moi32_small st ltac:(change (2^32)%Z with 4294967296%Z; lia)).
  apply bvw32_small. change (2^32)%Z with 4294967296%Z. lia.
Qed.

(* ---- [andi a4,s1,7] : the bit offset inside its byte ---- *)
Lemma bf_andi7 (x : mword 64) :
  and_vec x (sign_extend' 64 (mword_of_int 7 : mword 12) : mword 64)
  = (mword_of_int (bv_unsigned x `mod` 8) : mword 64).
Proof.
  assert (Hc : (sign_extend' 64 (mword_of_int 7 : mword 12) : mword 64)
               = mword_of_int 7) by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hc. apply bv_eq. rewrite and_vec64_unsigned.
  assert (H7 : bv_unsigned (mword_of_int 7 : mword 64) = 7)
    by (vm_compute; reflexivity).
  rewrite H7 moi64_unsigned bf_z_land7.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
  assert (Hr : 0 <= bv_unsigned x `mod` 8 < 8)
    by (apply Z.mod_pos_bound; lia).
  symmetry. apply bvw64_small.
  change (2^64)%Z with 18446744073709551616%Z. lia.
Qed.

(* ---- [sllw a5,a5,a4] with a5 = 1 : the mask.  Eight cases, one per
   possible bit offset -- the shift amount is never symbolic. ---- *)
Lemma bf_sllw1 (r : Z) : 0 <= r < 8 ->
  sign_extend' 64
    (shift_bits_left
       (subrange_vec_dec (mword_of_int 1 : mword 64) 31 0 : mword 32)
       (subrange_vec_dec
          (subrange_vec_dec (mword_of_int r : mword 64) 31 0 : mword 32) 4 0))
  = (mword_of_int (2 ^ r) : mword 64).
Proof.
  intros Hr.
  assert (Hc : r = 0 \/ r = 1 \/ r = 2 \/ r = 3
               \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia.
  destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst r;
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- [slli s1,s1,0x33] then [srli s1,s1,0x36] ---- *)
Lemma bf_slli51 (x : Z) : 0 <= x < 8192 ->
  shift_bits_left (mword_of_int x : mword 64)
    (subrange_vec_dec (mword_of_int 51 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (x * 2251799813685248) : mword 64).
Proof.
  intros Hx.
  assert (Hs : shift_bits_left (mword_of_int x : mword 64)
                 (subrange_vec_dec (mword_of_int 51 : mword 6)
                    (Z.sub log2_xlen 1) 0)
               = shiftl (mword_of_int x : mword 64) 51).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftl, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H51 : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx 51)) = 51).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H51 !moi64_unsigned.
  rewrite (bvw64_small x
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftl_mul_pow2; [| lia].
  change (2 ^ 51)%Z with 2251799813685248%Z. reflexivity.
Qed.

Lemma bf_srli54 (y : Z) : 0 <= y < 18446744073709551616 ->
  shift_bits_right (mword_of_int y : mword 64)
    (subrange_vec_dec (mword_of_int 54 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (y / 18014398509481984) : mword 64).
Proof.
  intros Hy.
  assert (Hs : shift_bits_right (mword_of_int y : mword 64)
                 (subrange_vec_dec (mword_of_int 54 : mword 6)
                    (Z.sub log2_xlen 1) 0)
               = shiftr (mword_of_int y : mword 64) 54).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hs. apply bv_eq.
  unfold shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H54 : bv_unsigned (MachineWord.MachineWord.N_to_word
                  (MachineWord.MachineWord.Z_idx 64)
                  (MachineWord.MachineWord.Z_idx 54)) = 54).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite Hm64. lia. }
  rewrite H54 !moi64_unsigned.
  rewrite (bvw64_small y ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 54)%Z with 18014398509481984%Z.
  symmetry. apply bvw64_small.
  change (2^64)%Z with 18446744073709551616%Z.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* ---- the two bit facts, at the machine's words ---- *)
Lemma bf_test_val (u : gset Z) (bi : Z) :
  0 <= bi -> bi ∈ u ->
  bv_unsigned (and_vec (mword_of_int (2 ^ (bi `mod` 8)) : mword 64)
                       (zero_extend' 64 (bm_byte u (bi `div` 8) : mword 8) : mword 64))
  = 2 ^ (bi `mod` 8).
Proof.
  intros Hbi Hin.
  destruct (bf_pow_bound (bi `mod` 8) (bit_off_range bi Hbi)) as [Hp0 Hp1].
  rewrite and_vec64_unsigned bf_zext8_unsigned moi64_unsigned.
  rewrite (bvw64_small (2 ^ (bi `mod` 8))
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite Z.land_comm (bm_bit_test u bi Hbi).
  rewrite (bool_decide_eq_true_2 _ Hin). reflexivity.
Qed.

Lemma bf_clear_val (u : gset Z) (bi : Z) :
  0 <= bi ->
  and_vec (zero_extend' 64 (bm_byte u (bi `div` 8) : mword 8) : mword 64)
          (xor_vec (mword_of_int (2 ^ (bi `mod` 8)) : mword 64)
                   (mword_of_int 18446744073709551615 : mword 64))
  = (zero_extend' 64 (bm_byte (u ∖ {[bi]}) (bi `div` 8) : mword 8) : mword 64).
Proof.
  intros Hbi.
  destruct (bf_pow_bound (bi `mod` 8) (bit_off_range bi Hbi)) as [Hp0 Hp1].
  apply bv_eq.
  rewrite and_vec64_unsigned !bf_zext8_unsigned bf_xor_vec64_unsigned.
  rewrite !moi64_unsigned.
  rewrite (bvw64_small (2 ^ (bi `mod` 8))
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (bvw64_small 18446744073709551615
             ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (bf_lnot_bridge (bv_unsigned (bm_byte u (bi `div` 8)))
             (bi `mod` 8) (bm_byte_bound u (bi `div` 8))
             (bit_off_range bi Hbi)).
  exact (bm_bit_clear u bi Hbi).
Qed.

(* ---- the one address shape: [bp + q] then [+88], and [q + bp] then
   [+88], both of which are byte [q] of [bp->data] ---- *)
Lemma bf_data_off (X : mword 64) (q : nat) :
  add_vec (add_vec X (mword_of_int (Z.of_nat q)))
          (sign_extend' 64 (mword_of_int 88 : mword 12))
  = pa_add (b_data X) q.
Proof.
  rewrite iu_pa_add_moi iu_data_addr /b_data !pa_add_add.
  f_equal. lia.
Qed.

Lemma bf_data_off' (X : mword 64) (q : nat) :
  add_vec (add_vec (mword_of_int (Z.of_nat q)) X)
          (sign_extend' 64 (mword_of_int 88 : mword 12))
  = pa_add (b_data X) q.
Proof.
  rewrite (bf_add_comm (mword_of_int (Z.of_nat q)) X). apply bf_data_off.
Qed.

(* ===================================================================== *)
(*  THE MISSING LEAF: [sllw rd,rs1,rs2].                                  *)
(*  Exec bridge + WP leaf, exactly as WpSconfSrliw.v does for [srliw].    *)
(* ===================================================================== *)

Lemma exec_execute_RTYPEW_SLLW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg
                    (sign_extend' 64
                       (shift_bits_left
                          (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
                          (subrange_vec_dec
                             (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32)
                             4 0))))).
Proof.
  unfold gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) SLLW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.

Section WpBfreeSllw.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Lemma wp_sllw_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sign_extend' 64
      (shift_bits_left (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
         (subrange_vec_dec
            (subrange_vec_dec (rget m rs2) 31 0 : mword 32) 4 0)) = wval ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_SLLW_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_src. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

End WpBfreeSllw.

(* ===================================================================== *)

Module BfreeProof (BR : BREAD) (LW : LOG_WRITE) (BL : BRELSE) : BFREE.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.
Local Ltac bfidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  Vocabulary: the frame, the byte accessor, the continuation.           *)
(* ===================================================================== *)
Section BfreeDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* bfree's 32-byte frame: ra@24 s0@16 s1@8 s2@0 *)
  Definition bf_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64))%I.

  (* ONE BYTE of a buffer's data area, borrowed and given back at a new
     byte list -- [ByteBuf.bb_byte_acc] over [buf_own]'s list form. *)
  Lemma bf_buf_byte (pb : mword 64) (bno dsk : mword 32)
      (l : list (bv 8)) (d : nat) :
    length l = 1024%nat -> (d < 1024)%nat ->
    buf_own pb bno dsk l -∗
      pa_add (b_data pb) d ↦ₘ (l !!! d) ∗
      (∀ l' : list (bv 8),
         ⌜length l' = 1024%nat⌝ -∗
         ⌜forall k, (k < 1024)%nat -> k <> d -> l' !!! k = l !!! k⌝ -∗
         pa_add (b_data pb) d ↦ₘ (l' !!! d) -∗
         buf_own pb bno dsk l').
  Proof.
    intros Hlen Hd.
    iIntros "(Hb & Hdk & %Hl & Hby)".
    iEval (rewrite (bb_bytes_of_list (b_data pb) l) Hlen) in "Hby".
    iDestruct (bb_byte_acc (b_data pb) 1024 d (fun jj => l !!! jj)
                 (DfracOwn 1) Hd with "Hby") as "[Hcell Hback]".
    iSplitL "Hcell"; [iExact "Hcell" |].
    iIntros (l') "%Hlen' %Hag Hcell".
    iDestruct ("Hback" $! (fun jj => l' !!! jj) with "[%] Hcell") as "Hby".
    { intros k Hk Hne. exact (Hag k Hk Hne). }
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb" |]. iSplitL "Hdk"; [iExact "Hdk" |].
    iSplitR; [iPureIntro; exact Hlen' |].
    iAssert (bb_bytes (b_data pb) (length l') (fun jj => l' !!! jj))
      with "[Hby]" as "Hby".
    { rewrite Hlen' /bb_bytes. iExact "Hby". }
    iEval (rewrite -(bb_bytes_of_list (b_data pb) l')) in "Hby".
    iExact "Hby".
  Qed.

  (* THE CONTINUATION, named so it is not re-traversed by every proofmode
     split (claude-notes/optimization.md). *)
  Definition bf_cont `{GEN : GenId} `{CID0 : CpuId}
      (γfs : fs_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z) (bi : Z)
      (Bud : iProp Σ) (pidv : mword 32) (dq dqb : dfrac) (j : nat)
      (m : regfile) (K : nat) (C : iProp Σ) (b : bool) : iProp Σ :=
    wp_next b (proc_addr j) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 true (proc_addr j) C b -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        bitmap_res γfs bmapstart cov logstart size (used ∖ {[ bi ]}) -∗
        bslots bn 2 -∗
        Bud -∗
        WP (Loop : expr riscv_lang))%I.

End BfreeDefs.

(* the register-threading invariants: the four registers the frame saves *)
Definition bf_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Definition bf_sp (m M : regfile) : Prop :=
  M !!! Regidx csp_rs1
  = add_vec (m !!! Regidx csp_rs1 : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))).

(* ===================================================================== *)
(*  +0x4a .. +0x5e : log_write, brelse and the epilogue.                  *)
(* ===================================================================== *)
Section BfreeTail.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  Local Lemma bf_tail `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat)
      (γfs : fs_names) (γd : disk_names) (bn : bio_names) (γ : log_names)
      (cov : gset Z) (logstart bmapstart size : Z) (dev : mword 32)
      (used : gset Z) (bi : Z) (u : nat) (cr : bool) (Sb : gset Z)
      (kk : nat) (bnoB : mword 32) (bsd : list (bv 8)) (d0 : bool)
      (pidv : mword 32) (dq dqb : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ) (b : bool) :
    (K_bfree <= K)%nat ->
    bf_sp m M ->
    bf_thr m M ->
    M !!! Regidx Ra0 = bnode kk ->
    M !!! Regidx Rs2 = bnode kk ->
    (kk < NBUF)%nat ->
    uint bnoB = bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    bitmap_ok cov logstart size (used ∖ {[ bi ]}) ->
    (cr = true -> bmapstart ∈ Sb) ->
    sie_cap_gpr M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 true (proc_addr j) C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.bfree + 0x4a) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    bf_frame m -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    bslots bn 1 -∗
    log_opS γ (S u) Sb -∗
    fsblock γfs bmapstart (bitmap_bytes used) -∗
    free_pool γfs size (used ∖ {[ bi ]}) -∗
    bio_held bn (fs_view γfs γd dev cov) kk pidv dev bnoB
       (bitmap_bytes (used ∖ {[ bi ]})) (bitmap_bytes used) bsd d0 -∗
    bf_cont (CID0 := CID0) γfs bn γ cov logstart bmapstart size used bi
            (log_opS γ (if cr then S u else u) (Sb ∪ {[bmapstart]}))
            pidv dq dqb j m K C b -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hthr Ha0 Hs2 Hkk Hbno Hcov Hlog Hokdel Hcredit.
    pose proof HK as HK'. unfold K_bfree in HK'.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx #Hprocs Hframe Hppid Hsb Hsl Hop Hfsb Hpool Hheld Hcont".
    iPoseProof (bfi_4a with "Htext") as "Hi4a".
    iPoseProof (bfi_4e with "Htext") as "Hi4e".
    iPoseProof (bfi_50 with "Htext") as "Hi50".
    iPoseProof (bfi_54 with "Htext") as "Hi54".
    iPoseProof (bfi_56 with "Htext") as "Hi56".
    iPoseProof (bfi_58 with "Htext") as "Hi58".
    iPoseProof (bfi_5a with "Htext") as "Hi5a".
    iPoseProof (bfi_5c with "Htext") as "Hi5c".
    iPoseProof (bfi_5e with "Htext") as "Hi5e".
    (* ===== +0x4a jal ra,log_write ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bfree + 0x4a)) Rra
              (mword_of_int 4094 : mword 21) M (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (T0 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bfree + 0x4a) : mword 64) 4)]> M).
    assert (Htgtlw : add_vec (mword_of_int (KernelSyms.bfree + 0x4a) : mword 64)
                       (sign_extend' 64 (mword_of_int 4094 : mword 21))
                     = mword_of_int KernelSyms.log_write) by pcw.
    iEval (rewrite Htgtlw) in "Hpc".
    assert (HT0a0 : T0 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T0 upd_ne; [exact Ha0 | nz]).
    assert (HT0s2 : T0 !!! Regidx Rs2 = bnode kk)
      by (rewrite /T0 upd_ne; [exact Hs2 | nz]).
    assert (HT0sp : bf_sp m T0)
      by (rewrite /bf_sp /T0 upd_ne; [exact Hsp | nz]).
    assert (HT0ra : T0 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.bfree + 0x4a) : mword 64) 4)
      by (rewrite /T0; apply upd_eq).
    assert (HT0thr : bf_thr m T0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T0 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CID1 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID0) (CIDb := CID1) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKlw : (K_log_write <= K - 4)%nat) by (unfold K_log_write; lia).
    iEval (rewrite -Hbno) in "Hfsb".
    iApply (LW.wp_log_write_gen bn γ γfs γd cov logstart dev kk pidv bnoB
              (bitmap_bytes (used ∖ {[ bi ]})) (bitmap_bytes used) bsd d0 u cr Sb
              T0 0%nat true (proc_addr j) C (K - 4)%nat b
              HKlw ltac:(change (2 ^ 31)%Z with 2147483648%Z; lia) Hkk HT0a0
              ltac:(rewrite Hbno; exact Hcov)
              ltac:(rewrite Hbno; exact Hlog)
              ltac:(intros Hc; rewrite Hbno; exact (Hcredit Hc))
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hsl Hop Hfsb Hheld").
    iIntros (CID2 Hq2 mL) "Hcg Hcnt Hpc %Hcs1 Hop Hfsb Hlk Hsl".
    (* log_write recorded the block under its own name; it is the bitmap
       block, which is how the credit bfree returns matches the one its
       caller threads *)
    iEval (rewrite Hbno) in "Hop".
    assert (Hpc4e : ret_pc (T0 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.bfree + 0x4e)) by (rewrite HT0ra; pcw).
    iEval (rewrite Hpc4e) in "Hpc".
    iEval (rewrite Hbno) in "Hfsb".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmLs2 : mL !!! Regidx Rs2 = bnode kk)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HT0s2).
    assert (HmLsp : bf_sp m mL).
    { rewrite /bf_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT0sp. }
    assert (HmLthr : bf_thr m mL).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HT0thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x4e c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bfree + 0x4e)) Ra0 Rs2
              mL (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi4e").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (T1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mL Rs2))]> mL).
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode kk).
    { rewrite /T1 upd_eq. rgne. rewrite HmLs2. apply add_vec_zero_l. }
    assert (HT1sp : bf_sp m T1)
      by (rewrite /bf_sp /T1 upd_ne; [exact HmLsp | nz]).
    assert (HT1thr : bf_thr m T1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T1 upd_ne; [| regne]. exact (HmLthr c Hcs N2 N8 N9 N18). }
    assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x4e) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x50)) by pcw.
    iEval (rewrite Hpp50) in "Hpc".
    (* ===== +0x50 jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bfree + 0x50)) Rra
              (mword_of_int 2096836 : mword 21) T1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi50").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (T2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bfree + 0x50) : mword 64) 4)]> T1).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.bfree + 0x50) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096836 : mword 21))
                     = mword_of_int KernelSyms.brelse) by pcw.
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HT2a0 : T2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /T2 upd_ne; [exact HT1a0 | nz]).
    assert (HT2sp : bf_sp m T2)
      by (rewrite /bf_sp /T2 upd_ne; [exact HT1sp | nz]).
    assert (HT2ra : T2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.bfree + 0x50) : mword 64) 4)
      by (rewrite /T2; apply upd_eq).
    assert (HT2thr : bf_thr m T2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T2 upd_ne; [| regne]. exact (HT1thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID2 CID4 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID1) (CIDb := CID4) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 4)%nat) by (unfold K_brelse; lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk
              pidv dev bnoB dq T2 (K - 4)%nat true (proc_addr j) C
              (bitmap_bytes (used ∖ {[ bi ]})) bsd true b
              HKbl Hkk HT2a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk").
    iIntros (CID5 Hq5 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hsl1".
    assert (Hpc54 : ret_pc (T2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.bfree + 0x54)) by (rewrite HT2ra; pcw).
    iEval (rewrite Hpc54) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : bf_sp m mR).
    { rewrite /bf_sp
        (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT2sp. }
    assert (HmRthr : bf_thr m mR).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HT2thr c Hcs N2 N8 N9 N18). }
    iDestruct (iu_slots_join bn 1 1 with "Hsl Hsl1") as "Hsl".
    (* ===== +0x54 .. +0x5a : the four restores ===== *)
    rewrite /bf_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4)".
    assert (Hc1 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc2 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc3 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hc4 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    (* +0x54 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x54))
              (mword_of_int 3 : mword 6) Rra
              mR (K - 4)%nat (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID6 Hq6) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mR).
    assert (HP1sp : bf_sp m P1)
      by (rewrite /bf_sp /P1 upd_ne; [exact HmRsp | nz]).
    assert (HP1thr : bf_thr m P1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P1 upd_ne; [| regne]. exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (HP1ra : P1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P1; apply upd_eq).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x56)) by pcw.
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x56))
              (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi56 [Hf2]").
    { iEval (rewrite HP1sp -HmRsp Hc2). iExact "Hf2". }
    iIntros (CID7 Hq7) "Hcg Hpc Hf2".
    iEval (rewrite HP1sp -HmRsp Hc2) in "Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : bf_sp m P2)
      by (rewrite /bf_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2thr : bf_thr m P2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P2 upd_ne; [| regne]. exact (HP1thr c Hcs N2 N8 N9 N18). }
    assert (HP2ra : P2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1ra | nz]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x58)) by pcw.
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x58))
              (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi58 [Hf3]").
    { iEval (rewrite HP2sp -HmRsp Hc3). iExact "Hf3". }
    iIntros (CID8 Hq8) "Hcg Hpc Hf3".
    iEval (rewrite HP2sp -HmRsp Hc3) in "Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : bf_sp m P3)
      by (rewrite /bf_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (HP3thr : bf_thr m P3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P3 upd_ne; [| regne]. exact (HP2thr c Hcs N2 N8 N9 N18). }
    assert (HP3ra : P3 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2ra | nz]).
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x5a)) by pcw.
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x5a))
              (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi5a [Hf4]").
    { iEval (rewrite HP3sp -HmRsp Hc4). iExact "Hf4". }
    iIntros (CID9 Hq9) "Hcg Hpc Hf4".
    iEval (rewrite HP3sp -HmRsp Hc4) in "Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : bf_sp m P4)
      by (rewrite /bf_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (HP4thr : bf_thr m P4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P4 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N18). }
    assert (HP4ra : P4 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3ra | nz]).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.bfree + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x5c)) by pcw.
    iEval (rewrite Hpp5c) in "Hpc".
    (* ===== +0x5c c.addi16sp sp,32 : pop ===== *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp. apply bv_eq.
      rewrite !add_vec64_unsigned.
      rewrite bv_wrap_add_idemp_l.
      assert (Hz : bv_unsigned (sign_extend' 64
                     (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64)
                   = 18446744073709551584) by (vm_compute; reflexivity).
      assert (Hz2 : bv_unsigned (sign_extend' 64
                      (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64)
                    = 32) by (vm_compute; reflexivity).
      rewrite Hz Hz2.
      replace (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551584 + 32)
        with (bv_unsigned (m !!! Regidx csp_rs1 : mword 64)
                 + 18446744073709551616) by ring.
      rewrite -bv_wrap_add_idemp_r.
      assert (Hm0 : bv_wrap 64 18446744073709551616 = 0)
        by (vm_compute; reflexivity).
      rewrite Hm0 Z.add_0_r.
      apply bv_wrap_small. apply bv_unsigned_in_range. }
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hf1 Hf2 Hf3 Hf4]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iExists _; iExact "Hf1" |].
      iSplitL "Hf2"; [iExists _; iExact "Hf2" |].
      iSplitL "Hf3"; [iExists _; iExact "Hf3" |].
      iSplitL "Hf4"; [iExists _; iExact "Hf4" |].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.bfree + 0x5c))
              (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi5c Hstk").
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.bfree + 0x5c) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x5e)) by pcw.
    iEval (rewrite Hpp5e) in "Hpc".
    (* ===== +0x5e c.ret ===== *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4ra | nz]).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.bfree + 0x5e)) Rra P5 K b
              ltac:(nz) with "Hcg Hpc Hi5e").
    iIntros (CID11 Hq11) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CONTRACT ===== *)
    assert (Csp : P5 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_eq; exact Hwv).
    assert (Cs0 : P5 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_ne; [| nz]. rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_ne; [| nz].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P5 upd_ne; [| nz]. rewrite /P4 upd_eq. reflexivity. }
    assert (Hfin : bf_thr m P5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne]. exact (HP4thr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; bfidx).
    (* the bitmap resource, at the CLEARED bit *)
    iDestruct (bitmap_res_close γfs bmapstart cov logstart size
                 (used ∖ {[ bi ]}) Hokdel with "Hfsb Hpool") as "Hbmr".
    iDestruct (cpu_own_transport CID5 CID11 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    rewrite /bf_cont.
    iSpecialize ("Hcont" $! CID11 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Hpc Hppid Hsb Hbmr
                     Hsl Hop").
    { unfold callee_saved. split_and!; assumption. }
  Qed.

End BfreeTail.

(* ===================================================================== *)
(*  +0x00 .. +0x46 : the prologue, bread, the bit test and the clear.     *)
(* ===================================================================== *)
Section ProofBfreeMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_bfree_gen 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (bno : mword 32) (bs : list (bv 8))
      (u : nat) (cr : bool) (Sb : gset Z)
      (pidv : mword 32) (dq dqb : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_bfree_gen_body γs j γl γu γd γk pd pav pu bn γ γfs
                        cov logstart bmapstart size dev used bno bs u cr Sb
                        pidv dq dqb m K eb C b.
  Proof.
    cbv beta delta [wp_bfree_gen_body].
    intros pcE pj ret_tgt HK Hgeom Hsize Hbm0 Hbmcov Hbmlog
           Hbirange Hbicov Hbilog Hbslen Hcredit Hj Hgl Ha0 Ha1 Heb.
    subst eb.
    pose proof HK as HK'. unfold K_bfree in HK'.
    destruct Hgeom as [Hcovok Hlogsub].
    destruct (Hcovok _ Hbmcov) as [Hbmpos Hbmlt].
    (* ---- the pure arithmetic of the block number: all of it comes from
       [bf_range], proved over plain [Z]; nothing below calls [lia] on it ---- *)
    destruct (bf_range (bv_unsigned bno) size Hbirange Hsize)
      as (Hbi0 & Hbi8192 & Hbi31 & Hbi32 & Hbi64 & HbiBPB & Hrmod
          & Hdlt & Hdz & Hmul & Hdiv0).
    destruct (bf_bm_range bmapstart Hbmpos Hbmlt) as [Hbm31 Hbm32].
    remember (bv_unsigned bno) as bi eqn:Hbieq.
    remember (bi `mod` 8) as r eqn:Hreq.
    remember (bi `div` 8) as q eqn:Hqeq.
    remember (Z.to_nat q) as d eqn:Hdeq.
    assert (Hbisext : (sign_extend' 64 bno : mword 64) = mword_of_int bi).
    { assert (Hb32 : bno = (mword_of_int bi : mword 32)).
      { apply bv_eq. rewrite moi32_unsigned -Hbieq. symmetry.
        apply bvw32_small. exact Hbi32. }
      rewrite {1}Hb32. apply sext32_64_small. exact Hbi31. }
    (* the bitmap block number, as the 32-bit word the ABI passes *)
    set (bnoB := (mword_of_int bmapstart : mword 32)).
    assert (HbnoB : uint bnoB = bmapstart).
    { rewrite /bnoB bb_uint32 moi32_unsigned. apply bvw32_small. exact Hbm32. }
    assert (HbnoBlt : (uint bnoB < 2147483648)%Z).
    { rewrite HbnoB. exact (proj2 Hbm31). }
    assert (HbnoBcov : uint bnoB ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite HbnoB; exact Hbmcov).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx Hsb Hbmr Hfsb Hown Hppid
              #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    iAssert (bf_cont (CID0 := CID) γfs bn γ cov logstart bmapstart size used bi
               (log_opS γ (if cr then S u else u) (Sb ∪ {[bmapstart]}))
               pidv dq dqb j m K C b)%I with "[Hcont]" as "Hcont";
      [rewrite /bf_cont; iExact "Hcont" |].
    (* ---- THE PANIC REFUTATION, done before a single instruction ---- *)
    iDestruct (bitmap_res_open with "Hbmr") as "(%Hok & Hfsbm & Hpool)".
    iDestruct (free_pool_own_used γfs size used bi Hbirange
                 with "Hown Hpool") as %Hin.
    (* ---- and the pool step the postcondition needs ---- *)
    iDestruct (free_blk_intro γfs bi bs Hbslen with "Hfsb Hown") as "Hblk".
    iDestruct (free_pool_give γfs size used bi Hbirange Hin
                 with "Hblk Hpool") as "Hpool".
    assert (Hokdel : bitmap_ok cov logstart size (used ∖ {[ bi ]}))
      by (apply bitmap_ok_del; assumption).
    iPoseProof (bfi_00 with "Htext") as "Hi00".
    iPoseProof (bfi_02 with "Htext") as "Hi02".
    iPoseProof (bfi_04 with "Htext") as "Hi04".
    iPoseProof (bfi_06 with "Htext") as "Hi06".
    iPoseProof (bfi_08 with "Htext") as "Hi08".
    iPoseProof (bfi_0a with "Htext") as "Hi0a".
    iPoseProof (bfi_0c with "Htext") as "Hi0c".
    iPoseProof (bfi_0e with "Htext") as "Hi0e".
    iPoseProof (bfi_12 with "Htext") as "Hi12".
    iPoseProof (bfi_16 with "Htext") as "Hi16".
    iPoseProof (bfi_1a with "Htext") as "Hi1a".
    iPoseProof (bfi_1c with "Htext") as "Hi1c".
    (* ===== +0x00 c.addi sp,sp,-32 ===== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. pcw. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HR1sp : bf_sp m R1) by (rewrite /bf_sp /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hf1". iDestruct "S2" as (v2) "Hf2".
    iDestruct "S3" as (v3) "Hf3". iDestruct "S4" as (v4) "Hf4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HR1sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try pcw. }
    iEval (rewrite -Hb1) in "Hf1". iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3". iEval (rewrite -Hb4) in "Hf4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* ===== +0x02 .. +0x08 : the four saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x02))
              (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat v1 b with "Hcg Hpc Hi02 Hf1").
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x04))
              (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat v2 b with "Hcg Hpc Hi04 Hf2").
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x06))
              (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat v3 b with "Hcg Hpc Hi06 Hf3").
    iIntros (CID4 Hq4) "Hcg Hpc Hf3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.bfree + 0x08))
              (mword_of_int 0 : mword 6) Rs2
              R1 (K - 4)%nat v4 b with "Hcg Hpc Hi08 Hf4").
    iIntros (CID5 Hq5) "Hcg Hpc Hf4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    (* the frame, restated at the entry file *)
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | nz]).
    iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hf1".
    iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hf2".
    iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hf3".
    iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hf4".
    iAssert (bf_frame m) with "[Hf1 Hf2 Hf3 Hf4]" as "Hframe".
    { rewrite /bf_frame.
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |]. iExact "Hf4". }
    (* ===== +0x0a c.addi4spn s0,sp,32 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.bfree + 0x0a))
              (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (HR2sp : bf_sp m R2)
      by (rewrite /bf_sp /R2 upd_ne; [exact HR1sp | nz]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R2 upd_ne; [| nz]; rewrite /R1 upd_ne; [exact Ha0 | nz]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = (mword_of_int bi : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
      rewrite Ha1. exact Hbisext. }
    assert (HR2thr : bf_thr m R2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.bfree + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.mv s1,a1 : s1 := b ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bfree + 0x0c)) Rs1 Ra1
              R2 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra1))]> R2).
    assert (HR3s1 : R3 !!! Regidx Rs1 = (mword_of_int bi : mword 64)).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a1. apply add_vec_zero_l. }
    assert (HR3a1 : R3 !!! Regidx Ra1 = (mword_of_int bi : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR3a0 : R3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a0 | nz]).
    assert (HR3sp : bf_sp m R3)
      by (rewrite /bf_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3thr : bf_thr m R3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.bfree + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e srliw a5,a1,0xd : a5 := b / BPB = 0 ===== *)
    assert (Ha5z : sign_extend' 64
                     (shift_bits_right
                        (subrange_vec_dec (rget R3 Ra1) 31 0 : mword 32)
                        (mword_of_int 13 : mword 5))
                   = (mword_of_int 0 : mword 64)).
    { rgne. rewrite HR3a1 -Hbisext bf_srliw13 -Hbieq Hdiv0. reflexivity. }
    iApply (wp_srliw_s_sconf (mword_of_int (KernelSyms.bfree + 0x0e)) Ra5 Ra1
              (mword_of_int 13 : mword 5) (mword_of_int 0 : mword 64)
              R3 (K - 4)%nat b ltac:(nz) ltac:(rdok) Ha5z
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hq8) "Hcg Hpc".
    set (R4 := <[Regidx Ra5 := regval_into_reg (mword_of_int 0 : mword 64)]> R3).
    assert (HR4a5 : R4 !!! Regidx Ra5 = (mword_of_int 0 : mword 64))
      by (rewrite /R4; apply upd_eq).
    assert (HR4a0 : R4 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3a0 | nz]).
    assert (HR4s1 : R4 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /R4 upd_ne; [exact HR3s1 | nz]).
    assert (HR4sp : bf_sp m R4)
      by (rewrite /bf_sp /R4 upd_ne; [exact HR3sp | nz]).
    assert (HR4thr : bf_thr m R4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R4 upd_ne; [| regne]. exact (HR3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x0e) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 auipc a1,0x1e ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.bfree + 0x12)) Ra1
              (mword_of_int 30 : mword 20) R4 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi12").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (R5 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.bfree + 0x12) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R4).
    assert (HR5a1 : R5 !!! Regidx Ra1
                    = add_vec (mword_of_int (KernelSyms.bfree + 0x12) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /R5; apply upd_eq).
    assert (HR5a5 : R5 !!! Regidx Ra5 = (mword_of_int 0 : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a5 | nz]).
    assert (HR5a0 : R5 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4a0 | nz]).
    assert (HR5s1 : R5 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /R5 upd_ne; [exact HR4s1 | nz]).
    assert (HR5sp : bf_sp m R5)
      by (rewrite /bf_sp /R5 upd_ne; [exact HR4sp | nz]).
    assert (HR5thr : bf_thr m R5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 lw a1,-1246(a1) : a1 := sb.bmapstart ===== *)
    assert (Hsbadr : add_vec (rget R5 Ra1)
                       (sign_extend' 64 (mword_of_int 2850 : mword 12))
                     = sb_bmapstart).
    { rgne. rewrite HR5a1. rewrite /sb_bmapstart /pa_add /add_vec_int. pcw. }
    iEval (rewrite -Hsbadr) in "Hsb".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.bfree + 0x16)) Ra1 Ra1
              (mword_of_int 2850 : mword 12) R5 (K - 4)%nat
              (mword_of_int bmapstart : mword 32) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi16 Hsb").
    iIntros (CID10 Hq10) "Hcg Hpc Hsb".
    iEval (rewrite Hsbadr) in "Hsb".
    set (R6 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int bmapstart : mword 32))]> R5).
    assert (HR6a1 : R6 !!! Regidx Ra1
                    = (sign_extend' 64 (mword_of_int bmapstart : mword 32) : mword 64))
      by (rewrite /R6; apply upd_eq).
    assert (HR6a5 : R6 !!! Regidx Ra5 = (mword_of_int 0 : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a5 | nz]).
    assert (HR6a0 : R6 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5a0 | nz]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /R6 upd_ne; [exact HR5s1 | nz]).
    assert (HR6sp : bf_sp m R6)
      by (rewrite /bf_sp /R6 upd_ne; [exact HR5sp | nz]).
    assert (HR6thr : bf_thr m R6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.addw a1,a1,a5 : a1 := BBLOCK(b, sb) = bmapstart ===== *)
    iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.bfree + 0x1a)) Ra1 Ra5
              R6 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1a").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R7 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64
                     (add_vec (subrange_vec_dec (rget R6 Ra1) 31 0 : mword 32)
                              (subrange_vec_dec (rget R6 Ra5) 31 0 : mword 32)))]> R6).
    assert (HR7a1 : R7 !!! Regidx Ra1 = (sign_extend' 64 bnoB : mword 64)).
    { rewrite /R7 upd_eq. rgne. rgne. rewrite HR6a1 HR6a5.
      rewrite /bnoB. apply bf_addw0. exact Hbm31. }
    assert (HR7a0 : R7 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6a0 | nz]).
    assert (HR7s1 : R7 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /R7 upd_ne; [exact HR6s1 | nz]).
    assert (HR7sp : bf_sp m R7)
      by (rewrite /bf_sp /R7 upd_ne; [exact HR6sp | nz]).
    assert (HR7thr : bf_thr m R7).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R7 upd_ne; [| regne]. exact (HR6thr c Hcs N2 N8 N9 N18). }
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.bfree + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.bfree + 0x1c)) Rra
              (mword_of_int 2096624 : mword 21) R7 (K - 4)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi1c").
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (RA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.bfree + 0x1c) : mword 64) 4)]> R7).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.bfree + 0x1c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096624 : mword 21))
                     = mword_of_int KernelSyms.bread) by pcw.
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HRAa0 : RA !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
      by (rewrite /RA upd_ne; [exact HR7a0 | nz]).
    assert (HRAa1 : RA !!! Regidx Ra1 = (sign_extend' 64 bnoB : mword 64))
      by (rewrite /RA upd_ne; [exact HR7a1 | nz]).
    assert (HRAs1 : RA !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /RA upd_ne; [exact HR7s1 | nz]).
    assert (HRAsp : bf_sp m RA)
      by (rewrite /bf_sp /RA upd_ne; [exact HR7sp | nz]).
    assert (HRAra : RA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.bfree + 0x1c) : mword 64) 4)
      by (rewrite /RA; apply upd_eq).
    assert (HRAthr : bf_thr m RA).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /RA upd_ne; [| regne]. exact (HR7thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID CID12 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (wp_next_shift (CIDa := CID) (CIDb := CID12) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 4)%nat) by (unfold K_bread; lia).
    iDestruct (iu_slots_split bn 1 1 with "Hsl") as "[Hsl Hsl1]".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bnoB dq
              RA (K - 4)%nat true C b
              HKbr HbnoBlt eq_refl HbnoBcov eq_refl Hj Hgl HRAa0 HRAa1 eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hsl1").
    iIntros (CID13 Hq13 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc20 : ret_pc (RA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.bfree + 0x20)) by (rewrite HRAra; pcw).
    iEval (rewrite Hpc20) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HRAs1).
    assert (HmBsp : bf_sp m mB).
    { rewrite /bf_sp
        (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HRAsp. }
    assert (HmBthr : bf_thr m mB).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HRAthr c Hcs N2 N8 N9 N18). }
    (* THE COUPLING: the buffer's bytes ARE the bitmap's image of [used] *)
    iEval (rewrite /bio_locked) in "Hheld".
    iDestruct (iu_held_k with "Hheld") as %Hkk.
    iEval (rewrite -HbnoB) in "Hfsbm".
    iDestruct (iu_held_content with "Hfsbm Hheld") as %Hbs0.
    subst bs0.
    iDestruct (iu_held_swap with "Hheld") as "[Hbuf Hheldback]".
    (* the byte the code reads and writes *)
    assert (Hlkused : bitmap_bytes used !!! d = bm_byte used q).
    { rewrite (list_lookup_total_correct (bitmap_bytes used) d
                 (bm_byte used (Z.of_nat d))
                 (bitmap_bytes_lookup used d Hdlt)).
      rewrite Hdz. reflexivity. }
    assert (Hlknew : bitmap_bytes (used ∖ {[ bi ]}) !!! d
                     = bm_byte (used ∖ {[ bi ]}) q).
    { rewrite (list_lookup_total_correct (bitmap_bytes (used ∖ {[ bi ]})) d
                 (bm_byte (used ∖ {[ bi ]}) (Z.of_nat d))
                 (bitmap_bytes_lookup (used ∖ {[ bi ]}) d Hdlt)).
      rewrite Hdz. reflexivity. }
    assert (Hbmlen : length (bitmap_bytes used) = 1024%nat)
      by (rewrite bitmap_bytes_length; reflexivity).
    assert (Hbmlen' : length (bitmap_bytes (used ∖ {[ bi ]})) = 1024%nat)
      by (rewrite bitmap_bytes_length; reflexivity).
    iDestruct (bf_buf_byte (bpa kk) bnoB (mword_of_int 0 : mword 32)
                 (bitmap_bytes used) d Hbmlen Hdlt with "Hbuf")
      as "[Hbyte Hbyteback]".
    iEval (rewrite Hlkused) in "Hbyte".
    iPoseProof (bfi_20 with "Htext") as "Hi20".
    iPoseProof (bfi_24 with "Htext") as "Hi24".
    iPoseProof (bfi_26 with "Htext") as "Hi26".
    iPoseProof (bfi_2a with "Htext") as "Hi2a".
    iPoseProof (bfi_2c with "Htext") as "Hi2c".
    iPoseProof (bfi_2e with "Htext") as "Hi2e".
    iPoseProof (bfi_32 with "Htext") as "Hi32".
    iPoseProof (bfi_36 with "Htext") as "Hi36".
    iPoseProof (bfi_3a with "Htext") as "Hi3a".
    iPoseProof (bfi_3c with "Htext") as "Hi3c".
    iPoseProof (bfi_3e with "Htext") as "Hi3e".
    iPoseProof (bfi_40 with "Htext") as "Hi40".
    iPoseProof (bfi_44 with "Htext") as "Hi44".
    iPoseProof (bfi_46 with "Htext") as "Hi46".
    (* ===== +0x20 andi a4,s1,7 : a4 := b % 8 ===== *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.bfree + 0x20)) Ra4 Rs1
              (mword_of_int 7 : mword 12) (mword_of_int r : mword 64)
              mB (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HmBs1 bf_andi7 moi64_unsigned
                      (bvw64_small bi Hbi64) -Hreq; reflexivity)
              with "Hcg Hpc Hi20").
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (B0 := <[Regidx Ra4 := regval_into_reg (mword_of_int r : mword 64)]> mB).
    assert (HB0a4 : B0 !!! Regidx Ra4 = (mword_of_int r : mword 64))
      by (rewrite /B0; apply upd_eq).
    assert (HB0a0 : B0 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B0 upd_ne; [exact HmBa0 | nz]).
    assert (HB0s1 : B0 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /B0 upd_ne; [exact HmBs1 | nz]).
    assert (HB0sp : bf_sp m B0)
      by (rewrite /bf_sp /B0 upd_ne; [exact HmBsp | nz]).
    assert (HB0thr : bf_thr m B0).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B0 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x20) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 c.li a5,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.bfree + 0x24)) Ra5
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              B0 (K - 4)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc Hi24").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> B0).
    assert (HB1a5 : B1 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
      by (rewrite /B1; apply upd_eq).
    assert (HB1a4 : B1 !!! Regidx Ra4 = (mword_of_int r : mword 64))
      by (rewrite /B1 upd_ne; [exact HB0a4 | nz]).
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HB0a0 | nz]).
    assert (HB1s1 : B1 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /B1 upd_ne; [exact HB0s1 | nz]).
    assert (HB1sp : bf_sp m B1)
      by (rewrite /bf_sp /B1 upd_ne; [exact HB0sp | nz]).
    assert (HB1thr : bf_thr m B1).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B1 upd_ne; [| regne]. exact (HB0thr c Hcs N2 N8 N9 N18). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x26)) by pcw.
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 sllw a5,a5,a4 : a5 := m = 1 << (b % 8) ===== *)
    iApply (wp_sllw_s_sconf (mword_of_int (KernelSyms.bfree + 0x26)) Ra5 Ra5 Ra4
              (mword_of_int (2 ^ r) : mword 64) B1 (K - 4)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HB1a5 HB1a4; apply bf_sllw1; exact Hrmod)
              with "Hcg Hpc Hi26").
    iIntros (CID16 Hq16) "Hcg Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (2 ^ r) : mword 64)]> B1).
    assert (HB2a5 : B2 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B2; apply upd_eq).
    assert (HB2a0 : B2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1a0 | nz]).
    assert (HB2s1 : B2 !!! Regidx Rs1 = (mword_of_int bi : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1s1 | nz]).
    assert (HB2sp : bf_sp m B2)
      by (rewrite /bf_sp /B2 upd_ne; [exact HB1sp | nz]).
    assert (HB2thr : bf_thr m B2).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B2 upd_ne; [| regne]. exact (HB1thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a c.slli s1,s1,0x33 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.bfree + 0x2a))
              (Regidx Rs1) Rs1 (mword_of_int 51 : mword 6) B2 (K - 4)%nat b
              ltac:(reflexivity) ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
    iIntros (CID17 Hq17) "Hcg Hpc".
    set (B3 := <[Regidx Rs1 := regval_into_reg
                  (shift_bits_left (rget B2 Rs1)
                     (subrange_vec_dec (mword_of_int 51 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> B2).
    assert (HB3s1 : B3 !!! Regidx Rs1
                    = (mword_of_int (bi * 2251799813685248) : mword 64)).
    { rewrite /B3 upd_eq. rgne. rewrite HB2s1. apply bf_slli51. exact Hbi8192. }
    assert (HB3a5 : B3 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a5 | nz]).
    assert (HB3a0 : B3 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B3 upd_ne; [exact HB2a0 | nz]).
    assert (HB3sp : bf_sp m B3)
      by (rewrite /bf_sp /B3 upd_ne; [exact HB2sp | nz]).
    assert (HB3thr : bf_thr m B3).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B3 upd_ne; [| regne]. exact (HB2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.bfree + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x2c)) by pcw.
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c c.srli s1,s1,0x36 : s1 := b / 8 ===== *)
    iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.bfree + 0x2c))
              (Cregidx (mword_of_int 1)) Rs1 (mword_of_int 54 : mword 6)
              B3 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (B4 := <[Regidx Rs1 := regval_into_reg
                  (shift_bits_right (rget B3 Rs1)
                     (subrange_vec_dec (mword_of_int 54 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> B3).
    assert (HB4s1 : B4 !!! Regidx Rs1
                    = (mword_of_int (Z.of_nat d) : mword 64)).
    { rewrite /B4 upd_eq. rgne. rewrite HB3s1.
      rewrite (bf_srli54 (bi * 2251799813685248) Hmul).
      rewrite (bf_shift_div bi Hbi0) -Hqeq -Hdz. reflexivity. }
    assert (HB4a5 : B4 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a5 | nz]).
    assert (HB4a0 : B4 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B4 upd_ne; [exact HB3a0 | nz]).
    assert (HB4sp : bf_sp m B4)
      by (rewrite /bf_sp /B4 upd_ne; [exact HB3sp | nz]).
    assert (HB4thr : bf_thr m B4).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B4 upd_ne; [| regne]. exact (HB3thr c Hcs N2 N8 N9 N18). }
    assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.bfree + 0x2c) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x2e)) by pcw.
    iEval (rewrite Hpp2e) in "Hpc".
    (* ===== +0x2e add a4,a0,s1 ===== *)
    iApply (wp_add_s_sconf (mword_of_int (KernelSyms.bfree + 0x2e)) Ra4 Ra0 Rs1
              (add_vec (bnode kk) (mword_of_int (Z.of_nat d)))
              B4 (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HB4a0 HB4s1; reflexivity)
              with "Hcg Hpc Hi2e").
    iIntros (CID19 Hq19) "Hcg Hpc".
    set (B5 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (bnode kk) (mword_of_int (Z.of_nat d)))]> B4).
    assert (HB5a4 : B5 !!! Regidx Ra4
                    = add_vec (bnode kk) (mword_of_int (Z.of_nat d)))
      by (rewrite /B5; apply upd_eq).
    assert (HB5a5 : B5 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a5 | nz]).
    assert (HB5a0 : B5 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B5 upd_ne; [exact HB4a0 | nz]).
    assert (HB5s1 : B5 !!! Regidx Rs1 = (mword_of_int (Z.of_nat d) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4s1 | nz]).
    assert (HB5sp : bf_sp m B5)
      by (rewrite /bf_sp /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5thr : bf_thr m B5).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B5 upd_ne; [| regne]. exact (HB4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x2e) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x32 lbu a4,88(a4) : a4 := bp->data[b/8] ===== *)
    assert (Hbyadr : add_vec (rget B5 Ra4)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bpa kk)) d).
    { rgne. rewrite HB5a4. apply bf_data_off. }
    iEval (rewrite -Hbyadr) in "Hbyte".
    iApply (wp_lbu_s_sconf (mword_of_int (KernelSyms.bfree + 0x32)) Ra4 Ra4
              (mword_of_int 88 : mword 12) B5 (K - 4)%nat
              (bm_byte used q) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi32 Hbyte").
    iIntros (CID20 Hq20) "Hcg Hpc Hbyte".
    iEval (rewrite Hbyadr) in "Hbyte".
    set (B6 := <[Regidx Ra4 := regval_into_reg
                  (zero_extend' 64 (bm_byte used q : mword 8))]> B5).
    assert (HB6a4 : B6 !!! Regidx Ra4
                    = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B6; apply upd_eq).
    assert (HB6a5 : B6 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a5 | nz]).
    assert (HB6a0 : B6 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B6 upd_ne; [exact HB5a0 | nz]).
    assert (HB6s1 : B6 !!! Regidx Rs1 = (mword_of_int (Z.of_nat d) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5s1 | nz]).
    assert (HB6sp : bf_sp m B6)
      by (rewrite /bf_sp /B6 upd_ne; [exact HB5sp | nz]).
    assert (HB6thr : bf_thr m B6).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B6 upd_ne; [| regne]. exact (HB5thr c Hcs N2 N8 N9 N18). }
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x32) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ===== +0x36 and a3,a5,a4 : the BIT TEST ===== *)
    iApply (wp_and_s_sconf (mword_of_int (KernelSyms.bfree + 0x36)) Ra3 Ra5 Ra4
              (and_vec (mword_of_int (2 ^ r) : mword 64)
                       (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
              B6 (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rgne; rewrite HB6a5 HB6a4; reflexivity)
              with "Hcg Hpc Hi36").
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (B7 := <[Regidx Ra3 := regval_into_reg
                  (and_vec (mword_of_int (2 ^ r) : mword 64)
                     (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))]> B6).
    assert (HB7a3 : B7 !!! Regidx Ra3
                    = and_vec (mword_of_int (2 ^ r) : mword 64)
                        (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B7; apply upd_eq).
    assert (HB7a4 : B7 !!! Regidx Ra4
                    = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B7 upd_ne; [exact HB6a4 | nz]).
    assert (HB7a5 : B7 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B7 upd_ne; [exact HB6a5 | nz]).
    assert (HB7a0 : B7 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B7 upd_ne; [exact HB6a0 | nz]).
    assert (HB7s1 : B7 !!! Regidx Rs1 = (mword_of_int (Z.of_nat d) : mword 64))
      by (rewrite /B7 upd_ne; [exact HB6s1 | nz]).
    assert (HB7sp : bf_sp m B7)
      by (rewrite /bf_sp /B7 upd_ne; [exact HB6sp | nz]).
    assert (HB7thr : bf_thr m B7).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B7 upd_ne; [| regne]. exact (HB6thr c Hcs N2 N8 N9 N18). }
    assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x36) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x3a)) by pcw.
    iEval (rewrite Hpp3a) in "Hpc".
    (* ===== +0x3a c.beqz a3 : THE DEAD PANIC.  The bit is SET (the caller's
       [blk_own] token forced [bi ∈ used]), so the branch is not taken. ===== *)
    assert (Hnz : eq_vec (rget B7 Ra3) zero_reg = false).
    { destruct (bf_pow_bound r Hrmod) as [Hp0 Hp1].
      rgne. rewrite HB7a3. apply eq_vec_false_iff.
      intro Heq.
      assert (Hval : bv_unsigned (and_vec (mword_of_int (2 ^ r) : mword 64)
                        (zero_extend' 64 (bm_byte used q : mword 8) : mword 64)) = 2 ^ r)
        by (rewrite Hreq Hqeq; apply bf_test_val; [exact Hbi0 | exact Hin]).
      rewrite Heq in Hval.
      assert (Hz0 : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite Hz0 in Hval. lia. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.bfree + 0x3a))
              (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 5)) Ra3
              B7 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) Hnz
              with "Hcg Hpc Hi3a").
    iIntros (CID22 Hq22) "Hcg Hpc".
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.bfree + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x3c)) by pcw.
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c c.mv s2,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.bfree + 0x3c)) Rs2 Ra0
              B7 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3c").
    iIntros (CID23 Hq23) "Hcg Hpc".
    set (B8 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget B7 Ra0))]> B7).
    assert (HB8s2 : B8 !!! Regidx Rs2 = bnode kk).
    { rewrite /B8 upd_eq. rgne. rewrite HB7a0. apply add_vec_zero_l. }
    assert (HB8a0 : B8 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B8 upd_ne; [exact HB7a0 | nz]).
    assert (HB8a4 : B8 !!! Regidx Ra4
                    = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B8 upd_ne; [exact HB7a4 | nz]).
    assert (HB8a5 : B8 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B8 upd_ne; [exact HB7a5 | nz]).
    assert (HB8s1 : B8 !!! Regidx Rs1 = (mword_of_int (Z.of_nat d) : mword 64))
      by (rewrite /B8 upd_ne; [exact HB7s1 | nz]).
    assert (HB8sp : bf_sp m B8)
      by (rewrite /bf_sp /B8 upd_ne; [exact HB7sp | nz]).
    assert (HB8thr : bf_thr m B8).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B8 upd_ne; [| regne]. exact (HB7thr c Hcs N2 N8 N9 N18). }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.bfree + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x3e)) by pcw.
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x3e c.add s1,s1,a0 ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.bfree + 0x3e)) Rs1 Ra0
              B8 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi3e").
    iIntros (CID24 Hq24) "Hcg Hpc".
    set (B9 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (rget B8 Rs1) (rget B8 Ra0))]> B8).
    assert (HB9s1 : B9 !!! Regidx Rs1
                    = add_vec (mword_of_int (Z.of_nat d)) (bnode kk)).
    { rewrite /B9 upd_eq. rgne. rgne. rewrite HB8s1 HB8a0. reflexivity. }
    assert (HB9s2 : B9 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B9 upd_ne; [exact HB8s2 | nz]).
    assert (HB9a0 : B9 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B9 upd_ne; [exact HB8a0 | nz]).
    assert (HB9a4 : B9 !!! Regidx Ra4
                    = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B9 upd_ne; [exact HB8a4 | nz]).
    assert (HB9a5 : B9 !!! Regidx Ra5 = (mword_of_int (2 ^ r) : mword 64))
      by (rewrite /B9 upd_ne; [exact HB8a5 | nz]).
    assert (HB9sp : bf_sp m B9)
      by (rewrite /bf_sp /B9 upd_ne; [exact HB8sp | nz]).
    assert (HB9thr : bf_thr m B9).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B9 upd_ne; [| regne]. exact (HB8thr c Hcs N2 N8 N9 N18). }
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x40)) by pcw.
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 xori a5,a5,-1 ===== *)
    iApply (wp_xori_s_sconf (mword_of_int (KernelSyms.bfree + 0x40)) Ra5 Ra5
              (mword_of_int 4095 : mword 12)
              (xor_vec (mword_of_int (2 ^ r) : mword 64)
                       (mword_of_int 18446744073709551615 : mword 64))
              B9 (K - 4)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HB9a5;
                    assert (Hff : (sign_extend' 64 (mword_of_int 4095 : mword 12)
                                   : mword 64)
                                  = mword_of_int 18446744073709551615)
                      by pcw;
                    rewrite Hff; reflexivity)
              with "Hcg Hpc Hi40").
    iIntros (CID25 Hq25) "Hcg Hpc".
    set (B10 := <[Regidx Ra5 := regval_into_reg
                   (xor_vec (mword_of_int (2 ^ r) : mword 64)
                      (mword_of_int 18446744073709551615 : mword 64))]> B9).
    assert (HB10a5 : B10 !!! Regidx Ra5
                     = xor_vec (mword_of_int (2 ^ r) : mword 64)
                         (mword_of_int 18446744073709551615 : mword 64))
      by (rewrite /B10; apply upd_eq).
    assert (HB10a4 : B10 !!! Regidx Ra4
                     = (zero_extend' 64 (bm_byte used q : mword 8) : mword 64))
      by (rewrite /B10 upd_ne; [exact HB9a4 | nz]).
    assert (HB10s1 : B10 !!! Regidx Rs1
                     = add_vec (mword_of_int (Z.of_nat d)) (bnode kk))
      by (rewrite /B10 upd_ne; [exact HB9s1 | nz]).
    assert (HB10s2 : B10 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B10 upd_ne; [exact HB9s2 | nz]).
    assert (HB10a0 : B10 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B10 upd_ne; [exact HB9a0 | nz]).
    assert (HB10sp : bf_sp m B10)
      by (rewrite /bf_sp /B10 upd_ne; [exact HB9sp | nz]).
    assert (HB10thr : bf_thr m B10).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B10 upd_ne; [| regne]. exact (HB9thr c Hcs N2 N8 N9 N18). }
    assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x40) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x44)) by pcw.
    iEval (rewrite Hpp44) in "Hpc".
    (* ===== +0x44 c.and a4,a4,a5 : a4 := data & ~m ===== *)
    iApply (wp_cand_s_sconf (mword_of_int (KernelSyms.bfree + 0x44)) Ra4 Ra5
              B10 (K - 4)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi44").
    iIntros (CID26 Hq26) "Hcg Hpc".
    set (B11 := <[Regidx Ra4 := regval_into_reg
                   (and_vec (rget B10 Ra4) (rget B10 Ra5))]> B10).
    assert (HB11a4 : B11 !!! Regidx Ra4
                     = (zero_extend' 64 (bm_byte (used ∖ {[ bi ]}) q : mword 8)
                        : mword 64)).
    { rewrite /B11 upd_eq. rgne. rgne. rewrite HB10a4 HB10a5.
      rewrite Hreq Hqeq. apply bf_clear_val. exact Hbi0. }
    assert (HB11s1 : B11 !!! Regidx Rs1
                     = add_vec (mword_of_int (Z.of_nat d)) (bnode kk))
      by (rewrite /B11 upd_ne; [exact HB10s1 | nz]).
    assert (HB11s2 : B11 !!! Regidx Rs2 = bnode kk)
      by (rewrite /B11 upd_ne; [exact HB10s2 | nz]).
    assert (HB11a0 : B11 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B11 upd_ne; [exact HB10a0 | nz]).
    assert (HB11sp : bf_sp m B11)
      by (rewrite /bf_sp /B11 upd_ne; [exact HB10sp | nz]).
    assert (HB11thr : bf_thr m B11).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /B11 upd_ne; [| regne]. exact (HB10thr c Hcs N2 N8 N9 N18). }
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.bfree + 0x44) : mword 64) 2
                    = mword_of_int (KernelSyms.bfree + 0x46)) by pcw.
    iEval (rewrite Hpp46) in "Hpc".
    (* ===== +0x46 sb a4,88(s1) : bp->data[b/8] = data & ~m ===== *)
    assert (Hstadr : add_vec (rget B11 Rs1)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bpa kk)) d).
    { rgne. rewrite HB11s1. apply bf_data_off'. }
    iEval (rewrite -Hstadr) in "Hbyte".
    iApply (wp_sb_s_sconf (mword_of_int (KernelSyms.bfree + 0x46)) Ra4 Rs1
              (mword_of_int 88 : mword 12) B11 (K - 4)%nat
              (bm_byte used q) b with "Hcg Hpc Hi46 Hbyte").
    iIntros (CID27 Hq27) "Hcg Hpc Hbyte".
    iEval (rewrite Hstadr; rgne; rewrite HB11a4 trunc8_zext8 -Hlknew) in "Hbyte".
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.bfree + 0x46) : mword 64) 4
                    = mword_of_int (KernelSyms.bfree + 0x4a)) by pcw.
    iEval (rewrite Hpp4a) in "Hpc".
    (* ---- the buffer, at the CLEARED image ---- *)
    iDestruct ("Hbyteback" $! (bitmap_bytes (used ∖ {[ bi ]}))
                 with "[%] [%] Hbyte") as "Hbuf".
    { exact Hbmlen'. }
    { intros k Hk Hne.
      rewrite -(bitmap_bytes_clear_bit used bi HbiBPB) -Hqeq -Hdeq.
      rewrite !list_lookup_total_alt.
      rewrite list_lookup_insert_ne;
        [reflexivity | intro Hx; apply Hne; symmetry; exact Hx]. }
    iDestruct ("Hheldback" with "Hbuf") as "Hheld".
    iEval (rewrite HbnoB) in "Hfsbm".
    (* ---- into the tail ---- *)
    iDestruct (cpu_own_transport CID13 CID27 0 true (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    assert (HB11a0' : B11 !!! Regidx Ra0 = bnode kk) by exact HB11a0.
    iApply (bf_tail (CID0 := CID27)  γs j γfs γd bn γ cov logstart bmapstart size
              dev used bi u cr Sb kk bnoB bsd0 d0 pidv dq dqb m B11 K C b
              HK HB11sp HB11thr HB11a0' HB11s2 Hkk HbnoB Hbmcov Hbmlog Hokdel
              Hcredit
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hprocs Hframe
                    Hppid Hsb Hsl Hop Hfsbm Hpool Hheld [Hcont]").
    { iApply (wp_next_shift (CIDa := CID12) (CIDb := CID27) ltac:(wp_next_chain)
                with "Hcont"). }
  Qed.

  (* THE SET-FORGETTING CONTRACT, at [cr = false].  balloc and every other
     caller threads [log_op] and is unchanged; only itrunc, which must
     survive 269 frees on one bitmap block, reaches for the credited form. *)
  Lemma wp_bfree_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z) (bno : mword 32) (bs : list (bv 8))
      (u : nat)
      (pidv : mword 32) (dq dqb : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_bfree_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                          cov logstart bmapstart size dev used bno bs u
                          pidv dq dqb m K eb C b.
  Proof.
    cbv beta delta [wp_bfree_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hsize Hbm0 Hbmcov Hbmlog
           Hbirange Hbicov Hbilog Hbslen Hj Hgl Ha0 Ha1 Heb.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hbio #Hlctx Hsb Hbmr Hfsb Hown Hppid
              #Hprocs #Hdevi #Hdgeom #Hdlock Hsl Hop Hcont".
    rewrite /log_op. iDestruct "Hop" as (Sb) "Hop".
    iApply (wp_bfree_gen γs j γl γu γd γk pd pav pu bn γ γfs
              cov logstart bmapstart size dev used bno bs u false Sb
              pidv dq dqb m K eb C b
              HK Hgeom Hsize Hbm0 Hbmcov Hbmlog
              Hbirange Hbicov Hbilog Hbslen ltac:(discriminate) Hj Hgl Ha0 Ha1 Heb
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlctx Hsb Hbmr Hfsb Hown Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hsl Hop [Hcont]").
    iIntros (CIDx) "%Hchain". iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hchain|].
    iIntros (mf) "%Hcs Hsie Hcnt Hpc Hppid Hsb Hbmr Hsl HopS".
    iDestruct (log_opS_op with "HopS") as "Hop".
    iApply ("Hcont" $! mf with "[%] Hsie Hcnt Hpc Hppid Hsb Hbmr Hsl Hop").
    exact Hcs.
  Qed.

End ProofBfreeMain.

End BfreeProof.

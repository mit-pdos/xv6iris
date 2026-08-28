(* ProofSysOpenAUBits.v -- ITEM (5) OF [SpecSysOpenAU]'s prover list, and
   nothing else: the machine's andi/branch tests against the [om_*]
   readings of the caller's own trapframe word.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PURE leaf, top level and binder-free, for the reason
   [FsAbsStart]'s head lemmas are: these are the facts a whole-function
   proofmode context starves on.

   THE CHAIN, ONCE.  sys_open's [argint] leaves [om := arg_int32 vom]
   ([RiscvExtras.trunc32] of the trapframe word), the [lw] sign-extends it
   ([ProofSysOpenParts.so_omv]) and every mode test is an [andi] against a
   twelve-bit literal ([so_and]).  So each test is a statement about ONE
   BIT of [bv_unsigned om], and [bv_unsigned (arg_int32 vom)] IS
   [SpecSysOpenAU.om_arg vom] -- the sign extension does not disturb any
   bit below 32 ([soau_testbit_low]), which is the only fact the chain
   needs.

   The two mode BYTES are handled the same way: [f->readable] is
   [(om & 1) xor 1] and [f->writable] is [0 <u (om & 3)], and
   [ProofSysOpenParts]'s [so_rd_byte_bool] / [so_wr_byte_bool] already say
   each is a C bool -- what is added here is WHICH bool. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
(* for the ssreflect [rewrite], which every proof below is written in *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.          (* [trunc32], [and_vec64_unsigned]    *)
Require Import VcGen.                (* [trunc32_unsigned]                 *)
Require Import WpSconfMem.           (* [trunc8]                           *)
Require Import FileInvDefs.          (* [fdstate_bit_inj]                  *)
Require Import SpecArgint.           (* [arg_int32]                        *)
Require Import ProofSysOpenParts.    (* [so_omv], [so_and], [so_rd_word],
                                        [so_wr_word], [so_and1_01]         *)
Require Import SpecSysOpenAU.        (* [om_arg] and the four bit readings *)
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ARITHMETIC: A LOW BIT SURVIVES THE SIGN EXTENSION             *)
(* ===================================================================== *)

(* [DinodeSlot.iu_sext_mod16]'s argument, at any modulus dividing 2^32:
   the sign extension changes the value only by a multiple of 2^32. *)
Lemma soau_sext_mod (w : mword 32) (M : Z) :
  0 < M -> (M | 2 ^ 32) ->
  bv_unsigned (sign_extend' 64 w : mword 64) `mod` M = bv_unsigned w `mod` M.
Proof.
  intros HM Hdvd.
  assert (Hd64 : (M | 2 ^ 64)).
  { apply (Z.divide_trans M (2 ^ 32) (2 ^ 64) Hdvd).
    exists (2 ^ 32). vm_compute. reflexivity. }
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
       SailStdpp.Values.to_word to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned.
  unfold bv_wrap.
  assert (Hm64 : bv_modulus (MachineWord.MachineWord.Z_idx 64) = 2 ^ 64)
    by (vm_compute; reflexivity).
  rewrite Hm64 (Z.mod_mod_divide (bv_signed w) (2 ^ 64) M Hd64).
  unfold bv_signed, bv_swrap, bv_wrap.
  assert (Hm32 : bv_modulus (MachineWord.MachineWord.Z_idx 32) = 2 ^ 32)
    by (vm_compute; reflexivity).
  assert (Hh32 : bv_half_modulus (MachineWord.MachineWord.Z_idx 32) = 2 ^ 31)
    by (vm_compute; reflexivity).
  rewrite Hm32 Hh32.
  rewrite Zminus_mod
          (Z.mod_mod_divide (bv_unsigned w + 2 ^ 31) (2 ^ 32) M Hdvd)
          -Zminus_mod.
  f_equal. lia.
Qed.

Lemma soau_pow2_divide (k : Z) : 0 <= k < 32 -> (2 ^ (k + 1) | 2 ^ 32).
Proof.
  intros Hk. exists (2 ^ (32 - (k + 1))).
  rewrite -Z.pow_add_r; [| lia | lia]. f_equal. lia.
Qed.

(* THE ONE FACT THE CHAIN NEEDS. *)
Lemma soau_testbit_low (w : mword 32) (k : Z) :
  0 <= k < 32 ->
  Z.testbit (bv_unsigned (so_omv w)) k = Z.testbit (bv_unsigned w) k.
Proof.
  intros Hk. unfold so_omv.
  rewrite -(Z.mod_pow2_bits_low (bv_unsigned (sign_extend' 64 w : mword 64))
              (k + 1) k ltac:(lia)).
  rewrite (soau_sext_mod w (2 ^ (k + 1)) ltac:(lia) (soau_pow2_divide k Hk)).
  apply (Z.mod_pow2_bits_low (bv_unsigned w) (k + 1) k ltac:(lia)).
Qed.

(* ---- masks -------------------------------------------------------- *)

Lemma soau_land_pow2 (x k : Z) :
  0 <= k -> (Z.land x (2 ^ k) = 0 <-> Z.testbit x k = false).
Proof.
  intros Hk. split.
  - intros Hz.
    assert (Hb : Z.testbit (Z.land x (2 ^ k)) k = false)
      by (rewrite Hz; apply Z.bits_0).
    rewrite Z.land_spec (Z.pow2_bits_true k Hk) andb_true_r in Hb. exact Hb.
  - intros Hb. apply Z.bits_inj_0. intros n.
    rewrite Z.land_spec (Z.pow2_bits_eqb k n Hk).
    destruct (Z.eq_dec k n) as [-> | Hne].
    + rewrite Hb. reflexivity.
    + rewrite (proj2 (Z.eqb_neq k n) Hne). apply andb_false_r.
Qed.

Lemma soau_land3 (x : Z) :
  Z.land x 3 = 0 <-> (Z.testbit x 0 = false /\ Z.testbit x 1 = false).
Proof.
  split.
  - intros Hz. split.
    + assert (Hb : Z.testbit (Z.land x 3) 0 = false)
        by (rewrite Hz; apply Z.bits_0).
      rewrite Z.land_spec in Hb.
      change (Z.testbit 3 0) with true in Hb.
      by rewrite andb_true_r in Hb.
    + assert (Hb : Z.testbit (Z.land x 3) 1 = false)
        by (rewrite Hz; apply Z.bits_0).
      rewrite Z.land_spec in Hb.
      change (Z.testbit 3 1) with true in Hb.
      by rewrite andb_true_r in Hb.
  - intros [H0 H1]. apply Z.bits_inj_0. intros n.
    rewrite Z.land_spec.
    destruct (Z.lt_trichotomy n 0) as [Hn | [-> | Hn]].
    + rewrite (Z.testbit_neg_r x n Hn). reflexivity.
    + rewrite H0. reflexivity.
    + destruct (Z.eq_dec n 1) as [-> | Hne].
      * rewrite H1. reflexivity.
      * rewrite (Z.bits_above_log2 3 n ltac:(lia)
                   ltac:(change (Z.log2 3) with 1; lia)).
        apply andb_false_r.
Qed.

(* ===================================================================== *)
(*  2.  THE FOUR TESTS, AGAINST [SpecSysOpenAU]'s READINGS                *)
(* ===================================================================== *)

(* the argint'd word IS the contract's [om_arg] *)
Lemma soau_om_arg (vom : mword 64) :
  bv_unsigned (arg_int32 vom) = om_arg vom.
Proof.
  rewrite trunc32_unsigned /om_arg /bv_wrap /bv_modulus.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 32)) with 32. reflexivity.
Qed.

(* the general single-bit mask, at a literal the [andi] carries *)
Lemma soau_and_pow2_zero (om : mword 32) (k n : Z) :
  0 <= k < 32 -> n = 2 ^ k ->
  bv_unsigned (sign_extend' 64 (mword_of_int n : mword 12) : mword 64) = n ->
  (so_and om n = (mword_of_int 0 : mword 64)
   <-> Z.testbit (bv_unsigned om) k = false).
Proof.
  intros Hk Hn Hlit.
  assert (Hu : bv_unsigned (so_and om n)
               = Z.land (bv_unsigned (so_omv om)) (2 ^ k)).
  { unfold so_and. rewrite and_vec64_unsigned Hlit Hn. reflexivity. }
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 64) = 0)
    by (vm_compute; reflexivity).
  rewrite -(soau_testbit_low om k Hk).
  rewrite -(soau_land_pow2 (bv_unsigned (so_omv om)) k ltac:(lia)).
  rewrite -Hu. split.
  - intros ->. exact Hz.
  - intros Heq. apply bv_eq. by rewrite Heq Hz.
Qed.

(* O_CREATE (bit 9) -- the +0x32 [andi a5,a5,512] and its [c.beqz] *)
Lemma soau_create_zero (vom : mword 64) :
  om_create vom = false ->
  so_and (arg_int32 vom) 512 = (mword_of_int 0 : mword 64).
Proof.
  intros Hc.
  apply (proj2 (soau_and_pow2_zero (arg_int32 vom) 9 512
                  ltac:(lia) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))).
  rewrite soau_om_arg. exact Hc.
Qed.

Lemma soau_create_nonzero (vom : mword 64) :
  so_and (arg_int32 vom) 512 <> (mword_of_int 0 : mword 64) ->
  om_create vom = true.
Proof.
  intros Hne.
  destruct (om_create vom) eqn:Hc; [reflexivity |].
  exfalso. exact (Hne (soau_create_zero vom Hc)).
Qed.

(* O_TRUNC (bit 10) -- the +0xac [andi a5,a5,1024] *)
Lemma soau_trunc_zero_iff (vom : mword 64) :
  so_and (arg_int32 vom) 1024 = (mword_of_int 0 : mword 64)
  <-> om_trunc vom = false.
Proof.
  rewrite (soau_and_pow2_zero (arg_int32 vom) 10 1024
             ltac:(lia) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)).
  rewrite soau_om_arg. reflexivity.
Qed.

(* ---- the two mode BYTES ------------------------------------------- *)

(* [f->readable = !(omode & O_WRONLY)]: [andi a4,a5,1 ; xori a4,a4,1] *)
Lemma soau_rd_byte (vom : mword 64) :
  trunc8 (so_rd_word (arg_int32 vom))
  = ((if om_readable vom then mword_of_int 1 else mword_of_int 0) : mword 8).
Proof.
  rewrite /om_readable /om_wronly -soau_om_arg.
  unfold so_rd_word.
  destruct (Z.testbit (bv_unsigned (arg_int32 vom)) 0) eqn:Hb0; cbn [negb].
  - (* the bit is set, so the mask is 1 and the xor gives 0 *)
    assert (Hm : so_and (arg_int32 vom) 1 = (mword_of_int 1 : mword 64)).
    { destruct (so_and1_01 (arg_int32 vom)) as [H0 | H1]; [| exact H1].
      exfalso.
      assert (Hz : Z.testbit (bv_unsigned (arg_int32 vom)) 0 = false).
      { apply (proj1 (soau_and_pow2_zero (arg_int32 vom) 0 1
                        ltac:(lia) ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; reflexivity))). exact H0. }
      rewrite Hz in Hb0. discriminate. }
    rewrite Hm. apply bv_eq; vm_compute; reflexivity.
  - assert (Hm : so_and (arg_int32 vom) 1 = (mword_of_int 0 : mword 64)).
    { apply (proj2 (soau_and_pow2_zero (arg_int32 vom) 0 1
                      ltac:(lia) ltac:(vm_compute; reflexivity)
                      ltac:(vm_compute; reflexivity))). exact Hb0. }
    rewrite Hm. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [f->writable = (omode & O_WRONLY) || (omode & O_RDWR)]: the [snez] on
   the merged mask 3 *)
Lemma soau_wr_byte (vom : mword 64) :
  trunc8 (so_wr_word (arg_int32 vom))
  = ((if om_writable vom then mword_of_int 1 else mword_of_int 0) : mword 8).
Proof.
  rewrite /om_writable /om_wronly /om_rdwr -soau_om_arg.
  unfold so_wr_word.
  assert (Hu : bv_unsigned (so_and (arg_int32 vom) 3)
               = Z.land (bv_unsigned (so_omv (arg_int32 vom))) 3).
  { unfold so_and. rewrite and_vec64_unsigned.
    assert (H3 : bv_unsigned (sign_extend' 64 (mword_of_int 3 : mword 12)
                              : mword 64) = 3)
      by (vm_compute; reflexivity).
    by rewrite H3. }
  assert (Hb0 : Z.testbit (bv_unsigned (so_omv (arg_int32 vom))) 0
                = Z.testbit (bv_unsigned (arg_int32 vom)) 0)
    by (apply soau_testbit_low; lia).
  assert (Hb1 : Z.testbit (bv_unsigned (so_omv (arg_int32 vom))) 1
                = Z.testbit (bv_unsigned (arg_int32 vom)) 1)
    by (apply soau_testbit_low; lia).
  destruct (Z.testbit (bv_unsigned (arg_int32 vom)) 0
            || Z.testbit (bv_unsigned (arg_int32 vom)) 1)%bool eqn:Hor.
  - (* some bit is set, so the mask is nonzero and [snez] answers 1 *)
    assert (Hnz : bv_unsigned (so_and (arg_int32 vom) 3) <> 0).
    { rewrite Hu. intros Hz.
      destruct (proj1 (soau_land3 (bv_unsigned (so_omv (arg_int32 vom)))) Hz)
        as [Hz0 Hz1].
      rewrite Hb0 in Hz0. rewrite Hb1 in Hz1.
      rewrite Hz0 Hz1 in Hor. discriminate. }
    assert (Hlt : zopz0zI_u (zero_reg : mword 64) (so_and (arg_int32 vom) 3)
                  = true).
    { unfold zopz0zI_u. rewrite !uint_unsigned.
      assert (H0 : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite H0. apply Z.ltb_lt.
      pose proof (bv_unsigned_in_range _ (so_and (arg_int32 vom) 3)) as Hr.
      lia. }
    rewrite Hlt. apply bv_eq; vm_compute; reflexivity.
  - assert (Hz : bv_unsigned (so_and (arg_int32 vom) 3) = 0).
    { rewrite Hu. apply (proj2 (soau_land3 _)).
      rewrite Hb0 Hb1.
      destruct (Z.testbit (bv_unsigned (arg_int32 vom)) 0),
               (Z.testbit (bv_unsigned (arg_int32 vom)) 1);
        cbn in Hor; try discriminate; by split. }
    assert (Hlt : zopz0zI_u (zero_reg : mword 64) (so_and (arg_int32 vom) 3)
                  = false).
    { unfold zopz0zI_u. rewrite !uint_unsigned.
      assert (H0 : bv_unsigned (zero_reg : mword 64) = 0)
        by (vm_compute; reflexivity).
      rewrite H0. apply Z.ltb_ge. lia. }
    rewrite Hlt. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ...and the two READINGS a publication needs: [so_publish]'s [rb]/[wb]
   come out of [so_rd_byte_bool] / [so_wr_byte_bool] as bare booleans, and
   these say which ones they are. *)
Lemma soau_rb_is (vom : mword 64) (rb : bool) :
  trunc8 (so_rd_word (arg_int32 vom))
  = ((if rb then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  rb = om_readable vom.
Proof.
  intros H. apply (fdstate_bit_inj rb (om_readable vom)
                     (trunc8 (so_rd_word (arg_int32 vom)))).
  - exact H.
  - apply soau_rd_byte.
Qed.

Lemma soau_wb_is (vom : mword 64) (wb : bool) :
  trunc8 (so_wr_word (arg_int32 vom))
  = ((if wb then mword_of_int 1 else mword_of_int 0) : mword 8) ->
  wb = om_writable vom.
Proof.
  intros H. apply (fdstate_bit_inj wb (om_writable vom)
                     (trunc8 (so_wr_word (arg_int32 vom)))).
  - exact H.
  - apply soau_wr_byte.
Qed.

(* ===================================================================== *)
(*  3.  ITEM (6): THE MAJOR BOUND                                         *)
(* ===================================================================== *)

(* [ProofSysOpenParts.so_major_out] is the branch fact ([bltu] not taken
   means the halfword is at most 9); the contract asks for it at
   [ConsoleInv.NDEV_max].  One reading, so the arms never spell 9. *)
Lemma soau_major_bound (h : mword 16) :
  ~ (9 < bv_unsigned h) -> 0 <= bv_unsigned h <= ConsoleInv.NDEV_max.
Proof.
  intros Hle.
  pose proof (bv_unsigned_in_range _ h) as Hr.
  assert (Hnd : ConsoleInv.NDEV_max = 9) by (vm_compute; reflexivity).
  rewrite Hnd. lia.
Qed.

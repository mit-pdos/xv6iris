(* ProofDirlink.v -- the whole-function proof of dirlink.

     int
     dirlink(struct inode *dp, char *name, uint inum)

   170 bytes.  The shape of the walk, off the decode in CodeDirlink.v:

     +0x00 .. +0x14   the 10-slot frame, FIVE eager saves (ra s0 s2 s5 s6),
                      s0 = sp+80, s2 := dp, s5 := name, s6 := inum
     +0x16            jal dirlookup(dp, name, 0)
     +0x1a            [c.bnez a0]: FOUND -> +0x58
     +0x1c .. +0x22   the LAZY save of s1, s1 := dp->size, [c.beqz s1] -> the
                      empty-directory shortcut at +0x70 (with s1 = 0 = off)
     +0x24 .. +0x2e   the LAZY saves of s3/s4, s1 := 0, s4 := &de, s3 := 16
     +0x30 .. +0x4e   THE FREE-SLOT SCAN: readi, the [lhu] free test (break to
                      +0x6c), off += 16, the size re-read, [bltu] back
     +0x52 .. +0x56   the exhausted exit: restore s3/s4, jump to +0x70
     +0x58 .. +0x5e   THE FOUND ARM: iput(ip), a0 := -1, jump to +0x9c
     +0x60 .. +0x68   panic("dirlink read") -- DEAD
     +0x6c .. +0x6e   the break exit: restore s3/s4
     +0x70 .. +0x8c   strncpy(de.name, name, 14), de.inum := inum, writei
     +0x90 .. +0x96   the BRANCHLESS return: a0 = -(writei(...) != 16)
     +0x9a            the lazy restore of s1
     +0x9c .. +0xa8   the five restores, the pop, [c.ret]

   ---- THE PIECES THE PROOF IS BUILT FROM -------------------------------

   [Htail] -- the epilogue from +0x9c, a [□]-persistent [wp_next]-wrapped
   assertion with an ABSTRACT continuation (ProofDirlookup's shape).  TWO
   arms reach it: the found arm jumps straight to +0x9c (s1 was never saved
   and never clobbered), everything else falls through the [ld s1] at +0x9a.

   [Hafter] -- the shared tail from +0x70, reached by THREE arms (the
   empty-directory shortcut, the scan's break, the scan's exhaustion).  It
   is where strncpy / the [sh] / writei live, so unlike [Htail] it cannot
   hold an abstract continuation: it takes the contract's own continuation,
   spelled out, plus every linear resource writei and the postcondition
   need.

   [Hloop] -- the scan, ProofKexit's [∀ fuel, wp_next] shape (readi sleeps,
   so the hart moves inside the body).  Invariant at +0x30: [i < nrec],
   [dir_free_first data i = None], the register bundle at [off = 16i], and
   the linear resources.  [dir_free_first_step_live] advances it,
   [dir_slot_char] closes both exits at the slot the postcondition names.

   ---- THE FOUR REGISTER BUNDLES ---------------------------------------

   dirlink saves s1/s3/s4 LAZILY and its two early exits skip the matching
   restores, so ONE [callee_saved] transport does not fit the whole
   function.  There are four, each excluding exactly the registers that are
   live-but-unsaved at that point:

     [dl_eregs]  s0 s2 s5 s6 set; s1 s3 s4 still the caller's.  Holds from
                 +0x0e to +0x1e, and on the whole found arm.
     [dl_pregs]  + s1 written (value as a parameter).  +0x1e onwards, and
                 from +0x70 to +0x9a.
     [dl_regs]   + s3 = 16 and s4 = &de.  The scan.
     [dl_tregs]  only sp and the un-saved callee-saved registers: what the
                 epilogue at +0x9c needs, and what BOTH its arms have. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RiscvFetchExec.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import MinstretInv.
Require Import KptGhost.
Require Import SmodeCore.
Require Import KernelText.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpSconfVc.
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintkGen.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import FileInv ProcInv.
Require Import DirView.
Require Import SpecPanic.
Require Import SpecReadi SpecStrncpy SpecWritei SpecIput.
Require Import CodeDirlink.
Require Import SpecDirlookup.
Require Import SpecDirlink.
Require Import ProofDirlookupParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

Module DirlinkProof (DL : DIRLOOKUP) (RD : READI) (IP : IPUT)
                    (SNC : STRNCPY) (WI : WRITEI) : DIRLINK.

Notation DK := KernelSyms.dirlink (only parsing).
Notation Rra := (mword_of_int 1 : mword 5).
Notation Rz := (mword_of_int 0 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Rs5 := (mword_of_int 21 : mword 5).
Notation Rs6 := (mword_of_int 22 : mword 5).

(* ===================================================================== *)
(*  1.  THE TWO SPEC-FIT LEMMAS THE N3 LEDGER LEFT TO THIS FILE           *)
(* ===================================================================== *)

(* FIT 2 -- sixteen bytes never straddle a block at a 16-aligned offset
   (1024 = 64*16), which is why [dirlink_units] is a CONSTANT rather than a
   function of the slot. *)
Lemma dl_wi_cost (k : nat) : wi_cost (16 * k) 16 = 7%nat.
Proof.
  unfold wi_cost, wi_blocks.
  assert (HB : BSIZE = 1024%nat) by reflexivity.
  rewrite HB.
  assert (Hm : ((16 * k) mod 1024)%nat = (16 * (k mod 64))%nat).
  { change 1024%nat with (16 * 64)%nat. apply Nat.Div0.mul_mod_distr_l. }
  rewrite Hm.
  assert (Hlt : (k mod 64 < 64)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hd : (16 * (k mod 64) + 16 + 1024 - 1)%nat
               = (1024 * 1 + (16 * (k mod 64) + 15))%nat) by lia.
  rewrite Hd.
  rewrite (Nat.div_add_l 1 1024 (16 * (k mod 64) + 15)%nat ltac:(lia)).
  rewrite (Nat.div_small (16 * (k mod 64) + 15)%nat 1024 ltac:(lia)).
  reflexivity.
Qed.

(* FIT 3 -- the free slot is at most [nrec], so the write is at
   [off <= size]: writei's OWN -1 arm is DEAD and the only failure dirlink
   can report is a SHORT WRITE. *)
Lemma dl_slot_off (data : nat -> list (bv 8)) (sz : Z) :
  0 <= sz -> Z.of_nat (16 * dir_slot data (dir_nrec sz))%nat <= sz.
Proof.
  intros Hnn.
  pose proof (dir_slot_le data (dir_nrec sz)) as Hle.
  pose proof (dlk_nrec_mul_le sz Hnn) as He.
  rewrite Nat2Z.inj_mul in He. rewrite Nat2Z.inj_mul.
  assert (Hz : Z.of_nat (dir_slot data (dir_nrec sz))
               <= Z.of_nat (dir_nrec sz)) by lia.
  lia.
Qed.

(* ===================================================================== *)
(*  2.  ARITHMETIC AND COMPARISONS                                        *)
(* ===================================================================== *)

(* The numeric side conditions, factored into lemmas over PLAIN [Z]/[nat] --
   [lia] answers "Cannot find witness" whenever an [mword] is merely in
   context, and a whole-function context is full of them (durable-notes). *)

Lemma dl_le_add (x a c : Z) : x <= a -> a + 16 <= c -> x + 16 <= c.
Proof. lia. Qed.

Lemma dl_lt31 (x : Z) : x + 16 <= 274432 -> x + 16 < 2 ^ 31.
Proof. change (2 ^ 31) with 2147483648. lia. Qed.

Lemma dl_nle (x y : Z) : x <= y -> ~ (y < x).
Proof. lia. Qed.

Lemma dl_nnle (x y : nat) : (x <= y)%nat -> ~ (y < x)%nat.
Proof. lia. Qed.

Lemma dl_lt16 (t : nat) : (t <= 16)%nat -> t <> 16%nat -> (t < 16)%nat.
Proof. lia. Qed.

Lemma dl_subrng (a x t : nat) : (a <= x)%nat -> (x < a + t)%nat -> (x - a < t)%nat.
Proof. lia. Qed.

Lemma dl_fuel0 (n i : nat) : (n - i <= 0)%nat -> (i < n)%nat -> False.
Proof. lia. Qed.

Lemma dl_fuelinit (n : nat) : (n - 0 <= n)%nat.
Proof. lia. Qed.

Lemma dl_fuelS (n i f : nat) : (n - i <= S f)%nat -> (n - S i <= f)%nat.
Proof. lia. Qed.

Lemma dl_si (i : nat) : (16 * i + 16)%nat = (16 * S i)%nat.
Proof. lia. Qed.

Lemma dl_offmul (i : nat) : Z.of_nat (16 * i)%nat = Z.of_nat i * 16.
Proof. rewrite Nat2Z.inj_mul. change (Z.of_nat 16%nat) with 16. lia. Qed.

Lemma dl_sioff (i : nat) :
  Z.of_nat (16 * S i)%nat = Z.of_nat (16 * i)%nat + 16.
Proof.
  rewrite -(dl_si i) Nat2Z.inj_add. change (Z.of_nat 16%nat) with 16.
  reflexivity.
Qed.

Lemma dl_b64 (x : Z) : 0 <= x -> x < 2 ^ 31 -> 0 <= x < 2 ^ 64.
Proof.
  change (2 ^ 31) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  lia.
Qed.

Lemma dl_eqn (i n : nat) : (i < n)%nat -> (n <= S i)%nat -> S i = n.
Proof. lia. Qed.

Lemma dl_3le (n : nat) : (dirlink_units <= n)%nat -> (iput_units <= n)%nat.
Proof. unfold dirlink_units, iput_units. lia. Qed.

Lemma dl_budget3 (n n' nc : nat) :
  (dirlink_units <= nc)%nat -> ((nc - iput_units)%nat <= n')%nat ->
  (n' <= nc)%nat ->
  ((nc - dirlink_units)%nat <= n')%nat /\ (n' <= nc)%nat.
Proof. unfold dirlink_units, iput_units. lia. Qed.

Lemma dl_kb (K : nat) : (K_dirlink <= K)%nat ->
  (10 <= K)%nat /\ (K_dirlookup <= K - 10)%nat /\ (K_readi <= K - 10)%nat
  /\ (K_iput <= K - 10)%nat /\ (K_writei <= K - 10)%nat /\ (2 <= K - 10)%nat
  /\ ((K - 10) + 10)%nat = K.
Proof.
  unfold K_dirlink, K_dirlookup, K_readi, K_iput, K_writei. lia.
Qed.

Lemma dl_bltu (x y : Z) : (0 <= x < 2 ^ 64) -> (0 <= y < 2 ^ 64) ->
  zopz0zI_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.ltb x y.
Proof.
  intros Hx Hy. unfold zopz0zI_u.
  rewrite (dlk_uint_moi x Hx) (dlk_uint_moi y Hy). reflexivity.
Qed.

Lemma dl_sz_eqz (sz : mword 32) :
  bv_unsigned sz = 0 ->
  eq_vec (sign_extend' 64 sz : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro H.
  assert (Hz : sz = (bv_0 32 : mword 32))
    by (apply bv_eq; rewrite H; vm_compute; reflexivity).
  rewrite Hz. apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma dl_sz_nez (sz : mword 32) :
  bv_unsigned sz < 2 ^ 31 -> bv_unsigned sz <> 0 ->
  eq_vec (sign_extend' 64 sz : mword 64) (zero_reg : mword 64) = false.
Proof.
  intros Hlt Hne. apply eq_vec_false_iff.
  rewrite (dlk_sext32_moi sz Hlt). intro Hc. apply Hne.
  assert (Hb : 0 <= bv_unsigned sz < 2 ^ 64).
  { pose proof (bv_unsigned_in_range _ sz) as [Hl Hh]. split; [exact Hl |].
    apply (Z.lt_trans _ (bv_modulus 32) _);
      [exact Hh | vm_compute; reflexivity]. }
  pose proof (dlk_uint_moi (bv_unsigned sz) Hb) as Hu.
  rewrite Hc in Hu.
  assert (H0 : uint (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite H0 in Hu. symmetry. exact Hu.
Qed.

Lemma dl_sz_zero_val (sz : mword 32) :
  bv_unsigned sz < 2 ^ 31 -> bv_unsigned sz = 0 ->
  (sign_extend' 64 sz : mword 64) = (mword_of_int (Z.of_nat (16 * 0)%nat) : mword 64).
Proof.
  intros Hlt H0. rewrite (dlk_sext32_moi sz Hlt) H0. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma dl_nrec_zero (sz : Z) : sz = 0 -> dir_nrec sz = 0%nat.
Proof. intro H. subst sz. unfold dir_nrec. reflexivity. Qed.

Lemma dl_nrec_pos (sz : Z) :
  0 <= sz -> (16 | sz) -> sz <> 0 -> (0 < dir_nrec sz)%nat.
Proof.
  intros Hnn Hd Hne. apply (dir_nrec_bound sz 0 Hnn Hd). simpl. lia.
Qed.

Lemma dl_slot_zero (data : nat -> list (bv 8)) : dir_slot data 0 = 0%nat.
Proof. unfold dir_slot, dir_free_first. rewrite dfirst_0. reflexivity. Qed.

(* the [sh s6,-80(s0)] stores exactly the low sixteen bits of the
   zero-extended inum, i.e. the inum itself *)
Lemma dl_trunc16_subrange (w : mword 64) : trunc16 w = subrange_vec_dec w 15 0.
Proof.
  unfold trunc16.
  change (Z.sub (Z.mul 2 8) 1) with 15%Z.
  change (15 - 0 + 1)%Z with 16%Z.
  apply autocast_id.
Qed.

Lemma dl_trunc16_unsigned (w : mword 64) :
  bv_unsigned (trunc16 w) = bv_wrap 16 (bv_unsigned w).
Proof.
  rewrite dl_trunc16_subrange.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, SailStdpp.Values.to_word.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold SailStdpp.Values.get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  rewrite bv_extract_0_unsigned.
  change (MachineWord.MachineWord.Z_idx (15 - 0 + 1)) with 16%N.
  reflexivity.
Qed.

Lemma dl_trunc16_zext (x : mword 16) :
  trunc16 (zero_extend' 64 x : mword 64) = x.
Proof.
  apply bv_eq. rewrite dl_trunc16_unsigned (dlk_zext64_unsigned x).
  apply bv_wrap_bv_unsigned.
Qed.

(* the branchless return: [addi a0,a0,-16] then [snez] then [negw] *)
Lemma dl_snez_eq :
  zopz0zI_u (zero_reg : mword 64)
    (add_vec (mword_of_int (Z.of_nat 16%nat) : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
  = false.
Proof. vm_compute. reflexivity. Qed.

Lemma dl_snez_lt (t : nat) : (t < 16)%nat ->
  zopz0zI_u (zero_reg : mword 64)
    (add_vec (mword_of_int (Z.of_nat t) : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
  = true.
Proof.
  intro Ht.
  do 16 (destruct t as [| t]; [ vm_compute; reflexivity |]).
  exfalso. clear - Ht. lia.
Qed.

Lemma dl_negw_0 :
  sign_extend' 64 (sub_vec (subrange_vec_dec (zero_reg : mword 64) 31 0 : mword 32)
                     (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_negw_1 :
  sign_extend' 64 (sub_vec (subrange_vec_dec (zero_reg : mword 64) 31 0 : mword 32)
                     (subrange_vec_dec (mword_of_int 1 : mword 64) 31 0 : mword 32))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_bit_0 :
  (zero_extend' 64 (bool_to_bit false) : mword 64) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_bit_1 :
  (zero_extend' 64 (bool_to_bit true) : mword 64) = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the zero displacement of [addi a2,s0,-80] is not zero; this is the one
   [i_dev]-style zero displacement dirlink needs (none), kept for the
   [c.mv]/[add_vec_zero_l] chain only *)
Lemma dl_add_vec_0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof.
  unfold add_vec, word_binop, with_word', with_word, MachineWord.MachineWord.add.
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  FRAME GEOMETRY -- the 10-slot frame                               *)
(* ===================================================================== *)

Lemma dl_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_pop (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_fp (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (wrap64 (uint (mword_of_int (- (8 * 10)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. exact H.
Qed.

Lemma dl_frm1 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm2 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm3 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm4 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm5 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm6 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm7 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_frm8 (X : mword 64) :
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 8.
Proof. apply dl_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* [&de = s0-80] and [&de.name = s0-78] *)
Lemma dl_de_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4016 : mword 12)) = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dl_dename_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4018 : mword 12))
  = pa_add (pa_stk X 10) 2.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc. unfold add_vec_int.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  4.  THE de RECORD: the two frame slots, and what strncpy leaves       *)
(* ===================================================================== *)

Lemma dl_rec_hi (fn : nat -> bv 8) (i : bv 16) (j : nat) :
  (j < 2)%nat ->
  dirent_bytes (de_of_name i (bname 14 fn)) !!! j = nth_byte i j.
Proof. intro Hj. exact (dirent_bytes_inum_t (de_of_name i (bname 14 fn)) j Hj). Qed.

Lemma dl_rec_nm (fn h : nat -> bv 8) (i : bv 16) (t : nat) :
  dl_snc fn h 14 -> (t < 14)%nat ->
  dirent_bytes (de_of_name i (bname 14 fn)) !!! (2 + t)%nat = h t.
Proof.
  intros Hsnc Ht.
  rewrite (dirent_bytes_name_t (de_of_name i (bname 14 fn)) t).
  unfold de_of_name. cbn [de_name].
  rewrite -(snc_bview fn h Hsnc).
  exact (list_lookup_total_correct _ _ _ (bview_lookup 14 h t Ht)).
Qed.

Section DlBuf.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the two frame slots the [de] occupies (10 and 9), carved into sixteen
     named bytes and put back *)
  Lemma dl_slots_bytes (sp0 : Arch.pa) (w1 w2 : bv 64) :
    (pa_stk sp0 10) ↦₈ w1 -∗ (pa_stk sp0 9) ↦₈ w2 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16.
  Proof.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "H1 H2".
    iDestruct (slot_bytes_own with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own with "H2") as "[%Ha2 B2]".
    iSplitR; [done |].
    change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iSplitL "B1"; [iExact "B1" | iExact "B2"].
  Qed.

  Lemma dl_bytes_slots (sp0 : Arch.pa) :
    is_aligned_paddr (Physaddr (pa_stk sp0 10)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 9)) 8 = true ->
    bytes_own (DfracOwn 1) (pa_stk sp0 10) 16 ⊢
    ∃ w1 w2 : bv 64, (pa_stk sp0 10) ↦₈ w1 ∗ (pa_stk sp0 9) ↦₈ w2.
  Proof.
    intros Ha1 Ha2.
    assert (E1 : pa_add (pa_stk sp0 10) 8 = pa_stk sp0 9)
      by (rewrite (pa_stk_next sp0 10 ltac:(lia)); reflexivity).
    iIntros "B". change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iDestruct "B" as "[B1 B2]".
    iDestruct (bytes_own_slot _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot _ Ha2 with "B2") as (w2) "H2".
    iExists w1, w2. iFrame.
  Qed.

  (* ANY two bytes are a halfword: the [sh] leaf wants a [↦₂] to overwrite,
     and the value it overwrites is whatever the frame slot happened to
     hold.  The witness is the [assemble_bytes] one [DirView.dir_inum] is
     built out of, so [nth_byte_assemble_len] gives the two readings. *)
  Lemma dl_bytes_half (a : Arch.pa) (g : nat -> bv 8) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ g j) ⊢ ∃ w : bv 16, a ↦₂ w.
  Proof.
    intro Hal. iIntros "H".
    iExists (Z_to_bv (16%N) (assemble_bytes [g 0%nat; g 1%nat])).
    iApply (word2_pointsto_intro a (DfracOwn 1) _ Hal).
    rewrite (bb_ext a 2 g
               (fun j => nth_byte (Z_to_bv (16%N) (assemble_bytes [g 0%nat; g 1%nat])) j)).
    - iExact "H".
    - intros j Hj. destruct j as [| [| j]]; [| | exfalso; lia].
      + symmetry.
        rewrite (nth_byte_assemble_len (16%N) [g 0%nat; g 1%nat] 0%nat);
          [reflexivity | cbn; lia | cbn; lia].
      + symmetry.
        rewrite (nth_byte_assemble_len (16%N) [g 0%nat; g 1%nat] 1%nat);
          [reflexivity | cbn; lia | cbn; lia].
  Qed.

  Lemma dl_bs3 (bn : bio_names) :
    (bslots bn 3 : iProp Σ) ⊣⊢ bslot bn ∗ bslots bn 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.

  (* SpecDirlink's [ic_sleeplocks] is a private copy of SpecFileclose's, so
     it needs its own accessor rather than that file's. *)
  Lemma dl_slk_acc (cn : ic_names) (k : nat) :
    (k < NINODE)%nat ->
    (SpecDirlink.ic_sleeplocks cn -∗
     ∃ γil γisl : gname,
       is_sleeplock γil γisl (i_lock (ientry k)) "inode"%string (ic_tok cn k)
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /SpecDirlink.ic_sleeplocks.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma dl_esc_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

End DlBuf.

(* ===================================================================== *)
(*  5.  THE FOUR REGISTER BUNDLES                                         *)
(* ===================================================================== *)

Definition dl_thr (m : regfile) (Mx : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
    Mx !!! Regidx c = m !!! Regidx c.

Definition dl_thr1 (m : regfile) (Mx : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
    Mx !!! Regidx c = m !!! Regidx c.

Definition dl_thr3 (m : regfile) (Mx : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
    c <> Rs5 -> c <> Rs6 ->
    Mx !!! Regidx c = m !!! Regidx c.

Definition dl_tregs (m : regfile) (sp0 : mword 64) (Mt : regfile) : Prop :=
  Mt !!! Regidx csp_rs1 = pa_stk sp0 10 /\ dl_thr m Mt.

Definition dl_eregs (m : regfile) (sp0 ip nb sinum : mword 64)
    (Me : regfile) : Prop :=
  Me !!! Regidx csp_rs1 = pa_stk sp0 10
  /\ Me !!! Regidx Rs0 = sp0
  /\ Me !!! Regidx Rs2 = ip
  /\ Me !!! Regidx Rs5 = nb
  /\ Me !!! Regidx Rs6 = sinum
  /\ dl_thr m Me.

Definition dl_pregs (m : regfile) (sp0 ip nb sinum : mword 64) (v1 : mword 64)
    (Mp : regfile) : Prop :=
  Mp !!! Regidx csp_rs1 = pa_stk sp0 10
  /\ Mp !!! Regidx Rs0 = sp0
  /\ Mp !!! Regidx Rs1 = v1
  /\ Mp !!! Regidx Rs2 = ip
  /\ Mp !!! Regidx Rs5 = nb
  /\ Mp !!! Regidx Rs6 = sinum
  /\ dl_thr1 m Mp.

Definition dl_regs (m : regfile) (sp0 ip nb sinum : mword 64) (off : nat)
    (Ml : regfile) : Prop :=
  Ml !!! Regidx csp_rs1 = pa_stk sp0 10
  /\ Ml !!! Regidx Rs0 = sp0
  /\ Ml !!! Regidx Rs1 = (mword_of_int (Z.of_nat off) : mword 64)
  /\ Ml !!! Regidx Rs2 = ip
  /\ Ml !!! Regidx Rs3 = (mword_of_int 16 : mword 64)
  /\ Ml !!! Regidx Rs4 = pa_stk sp0 10
  /\ Ml !!! Regidx Rs5 = nb
  /\ Ml !!! Regidx Rs6 = sinum
  /\ dl_thr3 m Ml.

(* ---- the transports ---- *)

Lemma dl_thr_caller (m Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_thr m Mx -> dl_thr m (<[Regidx r := v]> Mx).
Proof.
  intros Hr H c Hc N2 N8 N18 N21 N22.
  rewrite upd_ne; [exact (H c Hc N2 N8 N18 N21 N22) | dlk_rne2 Hr Hc].
Qed.

Lemma dl_thr1_caller (m Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_thr1 m Mx -> dl_thr1 m (<[Regidx r := v]> Mx).
Proof.
  intros Hr H c Hc N2 N8 N9 N18 N21 N22.
  rewrite upd_ne; [exact (H c Hc N2 N8 N9 N18 N21 N22) | dlk_rne2 Hr Hc].
Qed.

Lemma dl_thr3_caller (m Mx : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_thr3 m Mx -> dl_thr3 m (<[Regidx r := v]> Mx).
Proof.
  intros Hr H c Hc N2 N8 N9 N18 N19 N20 N21 N22.
  rewrite upd_ne; [exact (H c Hc N2 N8 N9 N18 N19 N20 N21 N22) | dlk_rne2 Hr Hc].
Qed.

Lemma dl_thr_cs (m Mx My : regfile) :
  callee_saved Mx My -> dl_thr m Mx -> dl_thr m My.
Proof.
  intros Hcs H c Hc N2 N8 N18 N21 N22.
  rewrite (callee_saved_lookup Hcs c Hc). exact (H c Hc N2 N8 N18 N21 N22).
Qed.

Lemma dl_thr1_cs (m Mx My : regfile) :
  callee_saved Mx My -> dl_thr1 m Mx -> dl_thr1 m My.
Proof.
  intros Hcs H c Hc N2 N8 N9 N18 N21 N22.
  rewrite (callee_saved_lookup Hcs c Hc). exact (H c Hc N2 N8 N9 N18 N21 N22).
Qed.

Lemma dl_thr3_cs (m Mx My : regfile) :
  callee_saved Mx My -> dl_thr3 m Mx -> dl_thr3 m My.
Proof.
  intros Hcs H c Hc N2 N8 N9 N18 N19 N20 N21 N22.
  rewrite (callee_saved_lookup Hcs c Hc).
  exact (H c Hc N2 N8 N9 N18 N19 N20 N21 N22).
Qed.

Lemma dl_thr1_of_thr (m Mx : regfile) : dl_thr m Mx -> dl_thr1 m Mx.
Proof. intros H c Hc N2 N8 N9 N18 N21 N22. exact (H c Hc N2 N8 N18 N21 N22). Qed.

Lemma dl_thr3_of_thr1 (m Mx : regfile) : dl_thr1 m Mx -> dl_thr3 m Mx.
Proof.
  intros H c Hc N2 N8 N9 N18 N19 N20 N21 N22. exact (H c Hc N2 N8 N9 N18 N21 N22).
Qed.

Lemma dl_eregs_caller (m : regfile) (sp0 ip nb sinum : mword 64)
    (Me : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_eregs m sp0 ip nb sinum Me ->
  dl_eregs m sp0 ip nb sinum (<[Regidx r := v]> Me).
Proof.
  intros Hr (H2 & H8 & H18 & H21 & H22 & Hthr). unfold dl_eregs. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H18 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - exact (dl_thr_caller m Me r v Hr Hthr).
Qed.

Lemma dl_eregs_cs (m : regfile) (sp0 ip nb sinum : mword 64) (Me Mr : regfile) :
  callee_saved Me Mr -> dl_eregs m sp0 ip nb sinum Me ->
  dl_eregs m sp0 ip nb sinum Mr.
Proof.
  intros Hcs (H2 & H8 & H18 & H21 & H22 & Hthr). unfold dl_eregs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)). exact H22.
  - exact (dl_thr_cs m Me Mr Hcs Hthr).
Qed.

Lemma dl_pregs_caller (m : regfile) (sp0 ip nb sinum v1 : mword 64)
    (Mp : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_pregs m sp0 ip nb sinum v1 Mp ->
  dl_pregs m sp0 ip nb sinum v1 (<[Regidx r := v]> Mp).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H21 & H22 & Hthr).
  unfold dl_pregs. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H9 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H18 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - exact (dl_thr1_caller m Mp r v Hr Hthr).
Qed.

Lemma dl_pregs_cs (m : regfile) (sp0 ip nb sinum v1 : mword 64)
    (Mp Mr : regfile) :
  callee_saved Mp Mr -> dl_pregs m sp0 ip nb sinum v1 Mp ->
  dl_pregs m sp0 ip nb sinum v1 Mr.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H21 & H22 & Hthr).
  unfold dl_pregs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)). exact H22.
  - exact (dl_thr1_cs m Mp Mr Hcs Hthr).
Qed.

Lemma dl_regs_caller (m : regfile) (sp0 ip nb sinum : mword 64) (off : nat)
    (Ml : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dl_regs m sp0 ip nb sinum off Ml ->
  dl_regs m sp0 ip nb sinum off (<[Regidx r := v]> Ml).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold dl_regs. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H9 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H18 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H19 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H20 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - exact (dl_thr3_caller m Ml r v Hr Hthr).
Qed.

Lemma dl_regs_cs (m : regfile) (sp0 ip nb sinum : mword 64) (off : nat)
    (Ml Mr : regfile) :
  callee_saved Ml Mr -> dl_regs m sp0 ip nb sinum off Ml ->
  dl_regs m sp0 ip nb sinum off Mr.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold dl_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs Rs2 ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs Rs3 ltac:(vm_compute; reflexivity)). exact H19.
  - rewrite (callee_saved_lookup Hcs Rs4 ltac:(vm_compute; reflexivity)). exact H20.
  - rewrite (callee_saved_lookup Hcs Rs5 ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)). exact H22.
  - exact (dl_thr3_cs m Ml Mr Hcs Hthr).
Qed.

(* the loop's one callee-saved write, the [c.addiw s1,s1,16] at +0x48 *)
Lemma dl_regs_s1 (m : regfile) (sp0 ip nb sinum : mword 64) (off off' : nat)
    (Ml : regfile) (v : mword 64) :
  v = (mword_of_int (Z.of_nat off') : mword 64) ->
  dl_regs m sp0 ip nb sinum off Ml ->
  dl_regs m sp0 ip nb sinum off' (<[Regidx Rs1 := v]> Ml).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold dl_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H19 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22)
      | dlk_xne N9 ].
Qed.

(* ---- the four bridges between the bundles ---- *)

Lemma dl_tregs_of_eregs (m : regfile) (sp0 ip nb sinum : mword 64)
    (Me : regfile) :
  dl_eregs m sp0 ip nb sinum Me -> dl_tregs m sp0 Me.
Proof. intros (H2 & _ & _ & _ & _ & Hthr). split; assumption. Qed.

(* the [ld s1,56(sp)] at +0x9a *)
Lemma dl_tregs_of_pregs (m : regfile) (sp0 ip nb sinum v1 : mword 64)
    (Mp : regfile) (v : mword 64) :
  v = (m !!! Regidx Rs1 : mword 64) ->
  dl_pregs m sp0 ip nb sinum v1 Mp ->
  dl_tregs m sp0 (<[Regidx Rs1 := v]> Mp).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H21 & H22 & Hthr). split.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - intros c Hc N2 N8 N18 N21 N22.
    destruct (decide (c = Rs1)) as [-> | Hne].
    + rewrite upd_eq. exact Hv.
    + rewrite upd_ne; [ exact (Hthr c Hc N2 N8 Hne N18 N21 N22) | dlk_xne Hne ].
Qed.

(* the [lw s1,76(s2)] at +0x1e *)
Lemma dl_pregs_of_eregs (m : regfile) (sp0 ip nb sinum : mword 64)
    (Me : regfile) (v : mword 64) :
  dl_eregs m sp0 ip nb sinum Me ->
  dl_pregs m sp0 ip nb sinum v (<[Regidx Rs1 := v]> Me).
Proof.
  intros (H2 & H8 & H18 & H21 & H22 & Hthr). unfold dl_pregs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_eq. reflexivity.
  - rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N21 N22.
    rewrite upd_ne;
      [ exact (dl_thr1_of_thr m Me Hthr c Hc N2 N8 N9 N18 N21 N22)
      | dlk_xne N9 ].
Qed.

(* the two restores at +0x52/+0x54 and +0x6c/+0x6e *)
Lemma dl_pregs_of_regs (m : regfile) (sp0 ip nb sinum : mword 64) (off : nat)
    (Ml : regfile) (v3 v4 : mword 64) :
  v3 = (m !!! Regidx Rs3 : mword 64) -> v4 = (m !!! Regidx Rs4 : mword 64) ->
  dl_regs m sp0 ip nb sinum off Ml ->
  dl_pregs m sp0 ip nb sinum (mword_of_int (Z.of_nat off) : mword 64)
    (<[Regidx Rs4 := v4]> (<[Regidx Rs3 := v3]> Ml)).
Proof.
  intros Hv3 Hv4 (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hthr).
  unfold dl_pregs. split_and!.
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H9 | vm_compute; discriminate].
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [| vm_compute; discriminate].
    rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N21 N22.
    destruct (decide (c = Rs4)) as [-> | Hn4].
    + rewrite upd_eq. exact Hv4.
    + rewrite upd_ne; [| dlk_xne Hn4].
      destruct (decide (c = Rs3)) as [-> | Hn3].
      * rewrite upd_eq. exact Hv3.
      * rewrite upd_ne;
          [ exact (Hthr c Hc N2 N8 N9 N18 Hn3 Hn4 N21 N22) | dlk_xne Hn3 ].
Qed.

(* ===================================================================== *)
(*  6.  THE PROOF                                                         *)
(* ===================================================================== *)

Section ProofDirlinkMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            ICFG : icfg, !icacheG Σ, !irefslotG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* readi's sixteen delivered bytes as the [lhu]'s halfword plus the name *)
  Lemma dl_de_view (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] jj ∈ seq 0 16, pa_add a jj ↦ₘ file_byte data (16 * i + jj)%nat)
    ⊣⊢ a ↦₂ dir_inum data i
       ∗ ([∗ list] jj ∈ seq 0 14, pa_add (pa_add a 2) jj ↦ₘ dir_name data i jj).
  Proof.
    intro Hal.
    rewrite -(dlk_half_acc data i a Hal).
    rewrite -(dlk_name_acc data i (pa_add a 2)).
    exact (dlk_de_split a (fun jj => file_byte data (16 * i + jj)%nat)).
  Qed.

  (* the [V] slot of readi's contract is dead on the kernel arm *)
  Definition dl_dummyV : pprivate :=
    MkPPriv (mword_of_int 0)
            (UPTD (mword_of_int 0) (mword_of_int 0) ∅ ∅)
            [] [] (mword_of_int 0) [].

  Lemma wp_dirlink_sconf
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname) (gpr : gname)
      (cov : gset Z) (logstart : Z) (inodestart : Z) (nib : nat)
      (bmapstart : Z) (size : Z) (dev : mword 32)
      (used : gset Z)
      (ip : mword 64) (dinum : mword 32)
      (bm : blkmap) (data : nat -> list (bv 8))
      (dn dn0 : dinode)
      (fn : nat -> bv 8)
      (inum : mword 16)
      (ncount : nat)
      (pidv : mword 32) (dq dqd dqn dqs dqb dqbs dqf : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_dirlink_sconf_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                            ga gf gpr cov logstart inodestart nib bmapstart
                            size dev used ip dinum bm data dn dn0 fn inum
                            ncount pidv dq dqd dqn dqs dqb dqbs dqf
                            m K eb C b.
  Proof.
    cbv beta delta [wp_dirlink_sconf_body].
    intros pcE pjv nb ret_tgt nrec s k0 HK Htype Hbmcov Hszb Hinums Hfit
           Hlg Hbmwf Hholes Haddrs Hsz31 Hist0 Hiblk Hiblog Hdinb Hcinb Hbmgeo Hpkc
           Hsize Hbms0 Hbmsc Hbmsl Hcovb Hiregb Hnc Hj Hgs Ha0 Ha2 Heb.
    (* [Hcinb] -- the LINKED inum's range -- is NOT used below: dirlink's
       [sh] stores sixteen bits whatever they are.  It rides in the contract
       for the writer-side [DirView.dir_ok] re-park (fs-icache.md §15.1(i),
       fs-sysfile item 3); see SpecDirlink.v's header. *)
    clear Hcinb.
    destruct (dl_kb K HK) as (HK10 & HKdl & HKrd & HKip & HKwi & HK2 & HKsum).
    assert (Hpjd : proc_addr j = pjv) by reflexivity.
    (* ---- numeric preliminaries, all over plain Z/nat ---- *)
    assert (Hszmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)
      by (vm_compute; reflexivity).
    assert (Hmbn : Z.of_nat (MAXFILE * BSIZE)%nat = 274432)
      by (rewrite Nat2Z.inj_mul; exact Hszmb).
    assert (Hsznn : 0 <= bv_unsigned (di_size dn))
      by exact (proj1 (bv_unsigned_in_range _ (di_size dn))).
    assert (Hfit' : bv_unsigned (di_size dn) + 16 <= 274432)
      by (rewrite Hszmb in Hfit; exact Hfit).
    assert (Hk0le : Z.of_nat (16 * k0)%nat <= bv_unsigned (di_size dn))
      by exact (dl_slot_off data (bv_unsigned (di_size dn)) Hsznn).
    assert (Hk0fit : Z.of_nat (16 * k0)%nat + 16 <= 274432)
      by exact (dl_le_add _ _ _ Hk0le Hfit').
    assert (Hk0n : (16 * k0 + 16 <= MAXFILE * BSIZE)%nat).
    { apply Nat2Z.inj_le. rewrite Hmbn Nat2Z.inj_add.
      change (Z.of_nat 16%nat) with 16. exact Hk0fit. }
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hkd #Hpk #Hbio #Hlog #Hkenv
              Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr
              #Hiregi Hdat Hppid #Hprocs #Hdev #Hgeom #Hdlk Hbsl
              #Hitb2 #Hitbl #Hesc #Hslks Hislot Hop Hcont".
    (* PIN THE INDEX.  This contract still carries [eb = true ->], and at
       level 0 [cpu_own_eb_agree] gives [eb = b], so [b] IS the literal
       [true] here.  The crossings below are the literal [true] (this
       function parks), and a [b]-indexed [cpu_own_transport] cannot be
       discharged from a [true]-indexed guard -- [b = false] tells you
       nothing about the hart.  When this function is itself generalized,
       this derivation is what goes. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    first [ iEval (rewrite -Hpjd) in "Hcg" | idtac ].
    first [ iEval (rewrite -Hpjd) in "Hcnt" | idtac ].
    first [ iEval (rewrite -Hpjd) in "Hppid" | idtac ].
    first [ iEval (rewrite -Hpjd) in "Hcont" | idtac ].
    iPoseProof (dki_00 with "Htext") as "Hi00".
    iPoseProof (dki_02 with "Htext") as "Hi02".
    iPoseProof (dki_04 with "Htext") as "Hi04".
    iPoseProof (dki_06 with "Htext") as "Hi06".
    iPoseProof (dki_08 with "Htext") as "Hi08".
    iPoseProof (dki_0a with "Htext") as "Hi0a".
    iPoseProof (dki_0c with "Htext") as "Hi0c".
    iPoseProof (dki_0e with "Htext") as "Hi0e".
    iPoseProof (dki_10 with "Htext") as "Hi10".
    iPoseProof (dki_12 with "Htext") as "Hi12".
    iPoseProof (dki_14 with "Htext") as "Hi14".
    iPoseProof (dki_16 with "Htext") as "Hi16".
    iPoseProof (dki_1a with "Htext") as "Hi1a".
    (* ===== +0x00 c.addi16sp sp,-80 : the 10-slot frame ===== *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10) by apply dl_push.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 59 : mword 6) m K 10 b
              ltac:(exact HK10) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R1 upd_eq; exact Hpush).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as
      "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply dl_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply dl_frm2).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HR1sp; apply dl_frm4).
    assert (Hf7 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HR1sp; apply dl_frm7).
    assert (Hf8 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HR1sp; apply dl_frm8).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf4) in "Hb4". iEval (rewrite -Hf7) in "Hb7".
    iEval (rewrite -Hf8) in "Hb8".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (DK + 0x02)) by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    assert (HR1o : forall c : mword 5, c <> csp_rs1 ->
                     R1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /R1 upd_ne;
        [reflexivity
        | intro Hq; apply Hc;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    (* ===== +0x02 .. +0x0a : the five EAGER saves ===== *)
    iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x02)) (mword_of_int 9 : mword 6)
              Rra R1 (K - 10)%nat u1 b with "Hcg Hpc Hi02 Hb1").
    iIntros (CID2 Hq2) "Hcg Hpc Hb1".
    iEval (rgne; rewrite (HR1o Rra ltac:(nz)) Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (DK + 0x02) : mword 64) 2
                    = mword_of_int (DK + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x04)) (mword_of_int 8 : mword 6)
              Rs0 R1 (K - 10)%nat u2 b with "Hcg Hpc Hi04 Hb2").
    iIntros (CID3 Hq3) "Hcg Hpc Hb2".
    iEval (rgne; rewrite (HR1o Rs0 ltac:(nz)) Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (DK + 0x04) : mword 64) 2
                    = mword_of_int (DK + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x06)) (mword_of_int 6 : mword 6)
              Rs2 R1 (K - 10)%nat u4 b with "Hcg Hpc Hi06 Hb4").
    iIntros (CID4 Hq4) "Hcg Hpc Hb4".
    iEval (rgne; rewrite (HR1o Rs2 ltac:(nz)) Hf4) in "Hb4".
    assert (Hpp08 : add_vec_int (mword_of_int (DK + 0x06) : mword 64) 2
                    = mword_of_int (DK + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x08)) (mword_of_int 3 : mword 6)
              Rs5 R1 (K - 10)%nat u7 b with "Hcg Hpc Hi08 Hb7").
    iIntros (CID5 Hq5) "Hcg Hpc Hb7".
    iEval (rgne; rewrite (HR1o Rs5 ltac:(nz)) Hf7) in "Hb7".
    assert (Hpp0a : add_vec_int (mword_of_int (DK + 0x08) : mword 64) 2
                    = mword_of_int (DK + 0x0a)) by pcw.
    iEval (rewrite Hpp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x0a)) (mword_of_int 2 : mword 6)
              Rs6 R1 (K - 10)%nat u8 b with "Hcg Hpc Hi0a Hb8").
    iIntros (CID6 Hq6) "Hcg Hpc Hb8".
    iEval (rgne; rewrite (HR1o Rs6 ltac:(nz)) Hf8) in "Hb8".
    assert (Hpp0c : add_vec_int (mword_of_int (DK + 0x0a) : mword 64) 2
                    = mword_of_int (DK + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.addi4spn s0,sp,80 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (DK + 0x0c))
              (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) Rs0
              R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0).
    { rewrite /R2 upd_eq. rewrite HR1sp. apply dl_fp. }
    assert (HR2a0 : R2 !!! Regidx Ra0 = ip).
    { rewrite /R2 upd_ne; [| nz]. rewrite (HR1o Ra0 ltac:(nz)). exact Ha0. }
    assert (HR2a1 : R2 !!! Regidx Ra1 = nb).
    { rewrite /R2 upd_ne; [| nz]. exact (HR1o Ra1 ltac:(nz)). }
    assert (HR2a2 : R2 !!! Regidx Ra2 = (zero_extend' 64 (inum : mword 16) : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite (HR1o Ra2 ltac:(nz)). exact Ha2. }
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 10).
    { rewrite /R2 upd_ne; [exact HR1sp | nz]. }
    assert (HR2o : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                     c <> Rs0 -> R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hc N2 N8. rewrite /R2 upd_ne;
        [ exact (HR1o c N2)
        | intro Hq; apply N8;
          first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]]. }
    assert (Hpp0e : add_vec_int (mword_of_int (DK + 0x0c) : mword 64) 2
                    = mword_of_int (DK + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e c.mv s2,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x0e)) Rs2 Ra0 R2 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0e").
    iIntros (CID8 Hq8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R2 !!! Regidx Ra0))]> R2).
    assert (HR3s2 : R3 !!! Regidx Rs2 = ip).
    { rewrite /R3 upd_eq. rewrite HR2a0. apply add_vec_zero_l. }
    assert (Hpp10 : add_vec_int (mword_of_int (DK + 0x0e) : mword 64) 2
                    = mword_of_int (DK + 0x10)) by pcw.
    iEval (rewrite Hpp10) in "Hpc".
    (* ===== +0x10 c.mv s5,a1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x10)) Rs5 Ra1 R3 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID9 Hq9) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R3 !!! Regidx Ra1))]> R3).
    assert (HR3a1 : R3 !!! Regidx Ra1 = nb)
      by (rewrite /R3 upd_ne; [exact HR2a1 | nz]).
    assert (HR4s5 : R4 !!! Regidx Rs5 = nb).
    { rewrite /R4 upd_eq. rewrite HR3a1. apply add_vec_zero_l. }
    assert (Hpp12 : add_vec_int (mword_of_int (DK + 0x10) : mword 64) 2
                    = mword_of_int (DK + 0x12)) by pcw.
    iEval (rewrite Hpp12) in "Hpc".
    (* ===== +0x12 c.mv s6,a2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x12)) Rs6 Ra2 R4 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi12").
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (R4 !!! Regidx Ra2))]> R4).
    assert (HR4a2 : R4 !!! Regidx Ra2 = (zero_extend' 64 (inum : mword 16) : mword 64)).
    { rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [exact HR2a2 | nz]. }
    assert (HR5s6 : R5 !!! Regidx Rs6
                    = (zero_extend' 64 (inum : mword 16) : mword 64)).
    { rewrite /R5 upd_eq. rewrite HR4a2. apply add_vec_zero_l. }
    assert (Hpp14 : add_vec_int (mword_of_int (DK + 0x12) : mword 64) 2
                    = mword_of_int (DK + 0x14)) by pcw.
    iEval (rewrite Hpp14) in "Hpc".
    (* ===== +0x14 c.li a2,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (DK + 0x14)) Ra2 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) R5 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi14").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (R6 := <[Regidx Ra2 := regval_into_reg (mword_of_int 0 : mword 64)]> R5).
    (* ---- the entry register bundle ---- *)
    assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
    assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
    assert (Hcsa2 : is_cs_idx Ra2 = false) by (vm_compute; reflexivity).
    assert (Hcsa3 : is_cs_idx Ra3 = false) by (vm_compute; reflexivity).
    assert (Hcsa4 : is_cs_idx Ra4 = false) by (vm_compute; reflexivity).
    assert (Hcsa5 : is_cs_idx Ra5 = false) by (vm_compute; reflexivity).
    assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
    assert (HR6e : dl_eregs m sp0 ip nb
                     (zero_extend' 64 (inum : mword 16) : mword 64) R6).
    { unfold dl_eregs. split_and!.
      - rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
        rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2sp.
      - rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
        rewrite /R4 upd_ne; [| nz]. rewrite /R3 upd_ne; [| nz]. exact HR2s0.
      - rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz].
        rewrite /R4 upd_ne; [| nz]. exact HR3s2.
      - rewrite /R6 upd_ne; [| nz]. rewrite /R5 upd_ne; [| nz]. exact HR4s5.
      - rewrite /R6 upd_ne; [| nz]. exact HR5s6.
      - intros c Hc N2 N8 N18 N21 N22.
        rewrite /R6 upd_ne; [| dlk_rne2 Hcsa2 Hc].
        rewrite /R5 upd_ne; [| dlk_xne N22].
        rewrite /R4 upd_ne; [| dlk_xne N21].
        rewrite /R3 upd_ne; [| dlk_xne N18].
        exact (HR2o c Hc N2 N8). }
    (* ---- the [de] scratch record: frame slots 10 and 9 as sixteen bytes ---- *)
    iDestruct (dl_slots_bytes sp0 u10 u9 with "Hb10 Hb9") as "[%Hal Hdeb]".
    destruct Hal as [Hal10 Hal9].
    iDestruct (dlk_bytes_name with "Hdeb") as (dolds0) "Hde".
    (* ================================================================= *)
    (*  THE SHARED EPILOGUE at +0x9c -- five restores, the pop, [c.ret].  *)
    (*  Both arms have s1/s3/s4 back at the caller's values by the time   *)
    (*  they get here, which is what [dl_tregs] says.                     *)
    (* ================================================================= *)
    iAssert (□ wp_next (CID0 := CID) true (proc_addr j) (fun CIDt : CpuId =>
               ∀ (Mt : regfile) (w3 w5 w6 : mword 64) (dnew : nat -> bv 8),
                 ⌜dl_tregs m sp0 Mt⌝ -∗
                 sie_cap_gpr Mt (K - 10)%nat b (proc_addr j) -∗
                 pc_is (mword_of_int (DK + 0x9c)) -∗
                 (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
                 (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
                 (pa_stk sp0 3) ↦₈ w3 -∗
                 (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
                 (pa_stk sp0 5) ↦₈ w5 -∗
                 (pa_stk sp0 6) ↦₈ w6 -∗
                 (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
                 (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
                 ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ dnew jj) -∗
                 wp_next (CID0 := CIDt) true (proc_addr j) (fun CIDf : CpuId =>
                   ∀ mf : regfile,
                     ⌜callee_saved m mf⌝ -∗
                     ⌜mf !!! Regidx Ra0 = (Mt !!! Regidx Ra0 : mword 64)⌝ -∗
                     sie_cap_gpr mf K b (proc_addr j) -∗
                     pc_is ret_tgt -∗
                     WP (Loop : expr riscv_lang)) -∗
                 WP (Loop : expr riscv_lang)))%I with "[]" as "#Htail".
    { iModIntro.
      iIntros (CIDt Hst Mt w3 w5 w6 dnew)
        "%HTr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde Hqc".
      destruct HTr as [HTsp HTthr].
      iPoseProof (dki_9c with "Htext") as "Hi9c".
      iPoseProof (dki_9e with "Htext") as "Hi9e".
      iPoseProof (dki_a0 with "Htext") as "Hia0".
      iPoseProof (dki_a2 with "Htext") as "Hia2".
      iPoseProof (dki_a4 with "Htext") as "Hia4".
      iPoseProof (dki_a6 with "Htext") as "Hia6".
      iPoseProof (dki_a8 with "Htext") as "Hia8".
      (* +0x9c c.ldsp ra,72(sp) *)
      assert (HT1 : add_vec (Mt !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                    = pa_stk sp0 1) by (rewrite HTsp; apply dl_frm1).
      iEval (rewrite -HT1) in "Hb1".
      iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x9c)) (mword_of_int 9 : mword 6)
                Rra Mt (K - 10)%nat (m !!! Regidx Rra : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9c Hb1").
      iIntros (CIDT1 HqT1) "Hcg Hpc Hb1".
      set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> Mt).
      assert (HP1sp : P1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /P1 upd_ne; [exact HTsp | nz]).
      assert (Hqq9e : add_vec_int (mword_of_int (DK + 0x9c) : mword 64) 2
                      = mword_of_int (DK + 0x9e)) by pcw.
      iEval (rewrite Hqq9e) in "Hpc".
      (* +0x9e c.ldsp s0,64(sp) *)
      assert (HT2 : add_vec (P1 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                    = pa_stk sp0 2) by (rewrite HP1sp; apply dl_frm2).
      iEval (rewrite -HT2) in "Hb2".
      iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x9e)) (mword_of_int 8 : mword 6)
                Rs0 P1 (K - 10)%nat (m !!! Regidx Rs0 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9e Hb2").
      iIntros (CIDT2 HqT2) "Hcg Hpc Hb2".
      set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /P2 upd_ne; [exact HP1sp | nz]).
      assert (Hqqa0 : add_vec_int (mword_of_int (DK + 0x9e) : mword 64) 2
                      = mword_of_int (DK + 0xa0)) by pcw.
      iEval (rewrite Hqqa0) in "Hpc".
      (* +0xa0 c.ldsp s2,48(sp) *)
      assert (HT4 : add_vec (P2 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite HP2sp; apply dl_frm4).
      iEval (rewrite -HT4) in "Hb4".
      iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0xa0)) (mword_of_int 6 : mword 6)
                Rs2 P2 (K - 10)%nat (m !!! Regidx Rs2 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia0 Hb4").
      iIntros (CIDT3 HqT3) "Hcg Hpc Hb4".
      set (P3 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P2).
      assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /P3 upd_ne; [exact HP2sp | nz]).
      assert (Hqqa2 : add_vec_int (mword_of_int (DK + 0xa0) : mword 64) 2
                      = mword_of_int (DK + 0xa2)) by pcw.
      iEval (rewrite Hqqa2) in "Hpc".
      (* +0xa2 c.ldsp s5,24(sp) *)
      assert (HT7 : add_vec (P3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk sp0 7) by (rewrite HP3sp; apply dl_frm7).
      iEval (rewrite -HT7) in "Hb7".
      iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0xa2)) (mword_of_int 3 : mword 6)
                Rs5 P3 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia2 Hb7").
      iIntros (CIDT4 HqT4) "Hcg Hpc Hb7".
      set (P4 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P3).
      assert (HP4sp : P4 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /P4 upd_ne; [exact HP3sp | nz]).
      assert (Hqqa4 : add_vec_int (mword_of_int (DK + 0xa2) : mword 64) 2
                      = mword_of_int (DK + 0xa4)) by pcw.
      iEval (rewrite Hqqa4) in "Hpc".
      (* +0xa4 c.ldsp s6,16(sp) *)
      assert (HT8 : add_vec (P4 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk sp0 8) by (rewrite HP4sp; apply dl_frm8).
      iEval (rewrite -HT8) in "Hb8".
      iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0xa4)) (mword_of_int 2 : mword 6)
                Rs6 P4 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hia4 Hb8").
      iIntros (CIDT5 HqT5) "Hcg Hpc Hb8".
      set (P5 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P4).
      assert (HP5sp : P5 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /P5 upd_ne; [exact HP4sp | nz]).
      assert (Hqqa6 : add_vec_int (mword_of_int (DK + 0xa4) : mword 64) 2
                      = mword_of_int (DK + 0xa6)) by pcw.
      iEval (rewrite Hqqa6) in "Hpc".
      iEval (rewrite HT1) in "Hb1". iEval (rewrite HT2) in "Hb2".
      iEval (rewrite HT4) in "Hb4". iEval (rewrite HT7) in "Hb7".
      iEval (rewrite HT8) in "Hb8".
      (* ---- the [de] buffer goes back to being two frame slots ---- *)
      iDestruct (dlk_name_bytes with "Hde") as "Hdeb2".
      iDestruct (dl_bytes_slots sp0 Hal10 Hal9 with "Hdeb2") as (w10 w9) "[Hc10 Hc9]".
      iAssert (stack_own sp0 10) with
        "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hc9 Hc10]" as "Hstk".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hb1"; [iExists _; iExact "Hb1" |].
        iSplitL "Hb2"; [iExists _; iExact "Hb2" |].
        iSplitL "Hb3"; [iExists _; iExact "Hb3" |].
        iSplitL "Hb4"; [iExists _; iExact "Hb4" |].
        iSplitL "Hb5"; [iExists _; iExact "Hb5" |].
        iSplitL "Hb6"; [iExists _; iExact "Hb6" |].
        iSplitL "Hb7"; [iExists _; iExact "Hb7" |].
        iSplitL "Hb8"; [iExists _; iExact "Hb8" |].
        iSplitL "Hc9"; [iExists _; iExact "Hc9" |].
        iSplitL "Hc10"; [iExists _; iExact "Hc10" |].
        done. }
      (* ===== +0xa6 c.addi16sp sp,80 : the pop ===== *)
      assert (Hwv : add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                    = sp0) by (rewrite HP5sp; apply dl_pop).
      assert (Hpop : (P5 !!! Regidx csp_rs1 : mword 64)
                     = pa_stk (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
        by (rewrite Hwv; exact HP5sp).
      iEval (rewrite -Hwv) in "Hstk".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (DK + 0xa6))
                (mword_of_int 5 : mword 6) P5 (K - 10)%nat 10 b Hpop
                with "Hcg Hpc Hia6 Hstk").
      iIntros (CIDT6 HqT6) "Hcg Hpc".
      set (P6 := <[Regidx csp_rs1 := regval_into_reg
                     (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P5).
      iEval (rewrite HKsum) in "Hcg".
      assert (Hqqa8 : add_vec_int (mword_of_int (DK + 0xa6) : mword 64) 2
                      = mword_of_int (DK + 0xa8)) by pcw.
      iEval (rewrite Hqqa8) in "Hpc".
      (* ===== +0xa8 c.ret ===== *)
      assert (CPra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_eq. reflexivity. }
      iApply (wp_cret_s_sconf (mword_of_int (DK + 0xa8)) Rra P6 K b
                ltac:(nz) with "Hcg Hpc Hia8").
      iIntros (CIDT7 HqT7) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64) = ret_tgt)
        by (rewrite CPra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* ===== the register facts the arms consume ===== *)
      assert (CPsp : P6 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
      { rewrite /P6 upd_eq. rewrite Hwv. symmetry. exact Hspm. }
      assert (CPs0 : P6 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_eq. reflexivity. }
      assert (CPs2 : P6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_eq. reflexivity. }
      assert (CPs5 : P6 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_eq. reflexivity. }
      assert (CPs6 : P6 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_eq. reflexivity. }
      assert (CPo : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
                P6 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hc N2 N8 N18 N21 N22.
        rewrite /P6 upd_ne; [| dlk_xne N2].
        rewrite /P5 upd_ne; [| dlk_xne N22].
        rewrite /P4 upd_ne; [| dlk_xne N21].
        rewrite /P3 upd_ne; [| dlk_xne N18].
        rewrite /P2 upd_ne; [| dlk_xne N8].
        rewrite /P1 upd_ne; [| dlk_rne2 Hcsra Hc].
        exact (HTthr c Hc N2 N8 N18 N21 N22). }
      assert (CPa0 : P6 !!! Regidx Ra0 = (Mt !!! Regidx Ra0 : mword 64)).
      { rewrite /P6 upd_ne; [| nz]. rewrite /P5 upd_ne; [| nz].
        rewrite /P4 upd_ne; [| nz]. rewrite /P3 upd_ne; [| nz].
        rewrite /P2 upd_ne; [| nz]. rewrite /P1 upd_ne; [reflexivity | nz]. }
      iSpecialize ("Hqc" $! CIDT7 with "[%]"); [wp_next_chain |].
      iApply ("Hqc" $! P6 with "[%] [%] Hcg Hpc").
      - unfold callee_saved. split_and!;
          first [ exact CPsp | exact CPs0 | exact CPs2 | exact CPs5 | exact CPs6
                | apply CPo; first [ vm_compute; reflexivity
                                   | vm_compute; discriminate ] ].
      - exact CPa0. }
    (* ================================================================= *)
    (*  +0x16 jal dirlookup(dp, name, 0)                                  *)
    (* ================================================================= *)
    assert (Htgtdl : add_vec (mword_of_int (DK + 0x16) : mword 64)
              (sign_extend' 64 (mword_of_int 2096640 : mword 21))
              = mword_of_int KernelSyms.dirlookup) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (DK + 0x16)) Rra
              (mword_of_int 2096640 : mword 21) R6 (K - 10)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi16").
    iIntros (CID12 Hq12) "Hcg Hpc".
    iEval (rewrite Htgtdl) in "Hpc".
    set (R7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (DK + 0x16) : mword 64) 4)]> R6).
    assert (HR7e : dl_eregs m sp0 ip nb
                     (zero_extend' 64 (inum : mword 16) : mword 64) R7)
      by (rewrite /R7; apply dl_eregs_caller; [exact Hcsra | exact HR6e]).
    assert (HR7a0 : R7 !!! Regidx Ra0 = ip).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      rewrite /R3 upd_ne; [exact HR2a0 | nz]. }
    assert (HR7a1 : R7 !!! Regidx Ra1 = nb).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_ne; [| nz].
      rewrite /R5 upd_ne; [| nz]. rewrite /R4 upd_ne; [| nz].
      exact HR3a1. }
    assert (HR7a2 : R7 !!! Regidx Ra2 = (mword_of_int 0 : mword 64)).
    { rewrite /R7 upd_ne; [| nz]. rewrite /R6 upd_eq. reflexivity. }
    assert (HR7ra : R7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (DK + 0x16) : mword 64) 4)
      by (rewrite /R7; apply upd_eq).
    iEval (rewrite -HR7a1) in "Hnm".
    iDestruct (dl_bs3 bn with "Hbsl") as "[Hbs1 Hbs2]".
    iDestruct (cpu_own_transport CID CID12 0%nat eb (proc_addr j) C b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (DL.wp_dirlookup_sconf gs j gl gu gd gk pd pav pu bn gfs gi cn gtl
              ga gf cov logstart nib dev ip bm data dn fn
              false (mword_of_int 0 : mword 32)
              pidv dq dqd dqn R7 (K - 10)%nat eb C b
              ltac:(exact HKdl) Htype Hlg Hbmwf Hbmcov Hszb Hinums Hj Hgs
              HR7a0
              ltac:(cbn [negb]; rewrite HR7a2 dlk_zero_moi; exact (eq_vec_refl _))
              Heb
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta Hmap
                    Hblocks Hnm [] Hppid Hprocs Hdev Hgeom Hdlk Hbs1
                    Hitb2 Hitbl Hesc Hislot [-]").
    { done. }
    iIntros (CIDdl Hsdl mdl found kk kslot qq)
      "%Hcsdl Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks Hnm Hppid Hbs1 Hres".
    iEval (rewrite HR7a1) in "Hnm".
    assert (Hpcdl : ret_pc (R7 !!! Regidx Rra : mword 64)
                    = mword_of_int (DK + 0x1a)) by (rewrite HR7ra; pcw).
    iEval (rewrite Hpcdl) in "Hpc".
    assert (Hdle : dl_eregs m sp0 ip nb
                     (zero_extend' 64 (inum : mword 16) : mword 64) mdl)
      by exact (dl_eregs_cs m sp0 ip nb _ R7 mdl Hcsdl HR7e).
    assert (Htgt58 : add_vec (mword_of_int (DK + 0x1a) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 31 : mword 8) ('b"0"))))
              = mword_of_int (DK + 0x58)) by pcw.
    destruct found.
    - (* =============== THE FOUND ARM: iput, a0 := -1 =============== *)
      iDestruct "Hres" as "((%Hsome & %Hkslot & %Hdla0) & Href & _)".
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (DK + 0x1a))
                (mword_of_int 31 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mdl (K - 10)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite Hdla0; apply dlk_neqz_true;
                      intro Hcz;
                      apply (ientry_ne_zero kslot (Nat.lt_le_incl _ _ Hkslot));
                      rewrite Hcz; exact dlk_zero_moi)
                ltac:(rewrite Htgt58; vm_compute; reflexivity)
                with "Hcg Hpc Hi1a").
      iNext. iIntros (CID13 Hq13) "Hcg Hpc".
      iEval (rewrite Htgt58) in "Hpc".
      iPoseProof (dki_58 with "Htext") as "Hi58".
      iPoseProof (dki_5c with "Htext") as "Hi5c".
      iPoseProof (dki_5e with "Htext") as "Hi5e".
      (* +0x58 jal ra,iput *)
      assert (Htgtip : add_vec (mword_of_int (DK + 0x58) : mword 64)
                (sign_extend' 64 (mword_of_int 2095520 : mword 21))
                = mword_of_int KernelSyms.iput) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (DK + 0x58)) Rra
                (mword_of_int 2095520 : mword 21) mdl (K - 10)%nat b
                ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi58").
      iIntros (CID14 Hq14) "Hcg Hpc".
      iEval (rewrite Htgtip) in "Hpc".
      set (E1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (DK + 0x58) : mword 64) 4)]> mdl).
      assert (HE1e : dl_eregs m sp0 ip nb
                       (zero_extend' 64 (inum : mword 16) : mword 64) E1)
        by (rewrite /E1; apply dl_eregs_caller; [exact Hcsra | exact Hdle]).
      assert (HE1a0 : E1 !!! Regidx Ra0 = ientry kslot)
        by (rewrite /E1 upd_ne; [exact Hdla0 | nz]).
      assert (HE1ra : E1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (DK + 0x58) : mword 64) 4)
        by (rewrite /E1; apply upd_eq).
      (* the child's inum is inside the inode region: [dir_inums_ok] at the
         record dirlookup stopped on *)
      assert (Hklt : (kk < nrec)%nat) by exact (dir_first_lt data nrec kk s Hsome).
      assert (Hklive : dir_live data kk) by exact (dir_first_live data nrec kk s Hsome).
      assert (Hinb : bv_unsigned
                (zero_extend' 32 (dir_inum data kk : mword 16) : mword 32)
                < 16 * Z.of_nat nib).
      { rewrite (dlk_zext32_unsigned (dir_inum data kk)).
        exact (Hinums kk Hklt Hklive). }
      destruct (Hiregb (zero_extend' 32 (dir_inum data kk : mword 16) : mword 32)
                  Hinb) as [Hcblk Hcblog].
      iDestruct (dl_esc_acc cn gfs gi cov logstart kslot Hkslot with "Hesc")
        as "#Hesck".
      iDestruct (dl_slk_acc cn kslot Hkslot with "Hslks") as (gil gisl) "#Hslk".
      iDestruct (dl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
        [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
      iDestruct (cpu_own_transport CIDdl CID14 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (IP.wp_iput_sconf gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                gil gisl cov logstart bmapstart inodestart nib size dev used
                kslot qq (zero_extend' 32 (dir_inum data kk : mword 16) : mword 32)
                ncount pidv dq dqb dqs E1 (K - 10)%nat eb C b
                ltac:(exact HKip) Hkslot Hlg Hsize Hbms0 Hbmsc Hbmsl Hist0
                Hcblk Hcblog Hinb Hcovb ltac:(exact (dl_3le ncount Hnc)) Hj Hgs
                HE1a0 Heb
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlog Hitb2 Hitbl Hesck
                      Hiregi Hslk Href Hsbb Hsbi Hbmr Hppid Hprocs Hdev Hgeom
                      Hdlk Hbsl Hop [-]").
      iIntros (CIDip Hsip mip nn uu)
        "%Hcsip Hcg Hcnt Hpc Hppid Hsbb Hsbi %Huu Hbmr Hbsl %Hnn Hop Hislot".
      assert (Hpcip : ret_pc (E1 !!! Regidx Rra : mword 64)
                      = mword_of_int (DK + 0x5c)) by (rewrite HE1ra; pcw).
      iEval (rewrite Hpcip) in "Hpc".
      assert (HEip : dl_eregs m sp0 ip nb
                       (zero_extend' 64 (inum : mword 16) : mword 64) mip)
        by exact (dl_eregs_cs m sp0 ip nb _ E1 mip Hcsip HE1e).
      (* +0x5c c.li a0,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (DK + 0x5c)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                mip (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hi5c").
      iIntros (CID15 Hq15) "Hcg Hpc".
      set (E2 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> mip).
      assert (HE2e : dl_eregs m sp0 ip nb
                       (zero_extend' 64 (inum : mword 16) : mword 64) E2)
        by (rewrite /E2; apply dl_eregs_caller; [exact Hcsa0 | exact HEip]).
      assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /E2; apply upd_eq).
      assert (Hpp5e : add_vec_int (mword_of_int (DK + 0x5c) : mword 64) 2
                      = mword_of_int (DK + 0x5e)) by pcw.
      iEval (rewrite Hpp5e) in "Hpc".
      (* +0x5e c.j +0x9c *)
      assert (Htgt9c : add_vec (mword_of_int (DK + 0x5e) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 31 : mword 11) ('b"0"))))
                = mword_of_int (DK + 0x9c)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (DK + 0x5e))
                (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0")))
                E2 (K - 10)%nat b
                ltac:(rewrite Htgt9c; vm_compute; reflexivity)
                with "Hcg Hpc Hi5e").
      iIntros (CID16 Hq16). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt9c) in "Hpc".
      iPoseProof ("Htail" $! CID16) as "Ht".
      iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
      iApply ("Ht" $! E2 u3 u5 u6 dolds0 with
                "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde [-]").
      { exact (dl_tregs_of_eregs m sp0 ip nb _ E2 HE2e). }
      iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CIDip CIDf 0%nat eb (proc_addr j) C b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf true bm data dn dn0 nn uu 0%nat with
                "[%] Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi
                 Hsbs Hsbb Hbmr Hdat Hppid Hbsl Hislot [%] Hop [%]").
      { exact Hcsf. }
      { exact (dl_budget3 ncount nn ncount Hnc (proj1 Hnn) (proj2 Hnn)). }
      { split; [rewrite Hsome; discriminate |].
        split; [rewrite Ha0f; exact HE2a0 |].
        split_and!; try reflexivity. exact Huu. }
    - (* ============ THE NOT-FOUND ARM: the free-slot scan ============ *)
      iDestruct "Hres" as "((%Hnone & %Hdla0) & Hislot & _)".
      pose proof Hdle as Hdle'.
      destruct Hdle' as (Hd2 & Hd8 & Hd18 & Hd21 & Hd22 & Hdthr).
      assert (Hds1 : mdl !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
        by (apply Hdthr; first [ vm_compute; reflexivity
                               | vm_compute; discriminate ]).
      iPoseProof (dki_1c with "Htext") as "Hi1c".
      iPoseProof (dki_1e with "Htext") as "Hi1e".
      iPoseProof (dki_22 with "Htext") as "Hi22".
      (* +0x1a c.bnez a0 : falls through *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (DK + 0x1a))
                (mword_of_int 31 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mdl (K - 10)%nat b
                ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; exact (dlk_neqz_false _ Hdla0))
                with "Hcg Hpc Hi1a").
      iIntros (CID13 Hq13) "Hcg Hpc".
      assert (Hpp1c : add_vec_int (mword_of_int (DK + 0x1a) : mword 64) 2
                      = mword_of_int (DK + 0x1c)) by pcw.
      iEval (rewrite Hpp1c) in "Hpc".
      (* +0x1c c.sdsp s1,56(sp) : the LAZY save *)
      assert (Hf3 : add_vec (mdl !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite Hd2; apply dl_frm3).
      iEval (rewrite -Hf3) in "Hb3".
      iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x1c)) (mword_of_int 7 : mword 6)
                Rs1 mdl (K - 10)%nat u3 b with "Hcg Hpc Hi1c Hb3").
      iIntros (CID14 Hq14) "Hcg Hpc Hb3".
      iEval (rgne; rewrite Hds1 Hf3) in "Hb3".
      assert (Hpp1e : add_vec_int (mword_of_int (DK + 0x1c) : mword 64) 2
                      = mword_of_int (DK + 0x1e)) by pcw.
      iEval (rewrite Hpp1e) in "Hpc".
      (* +0x1e lw s1,76(s2) : s1 := dp->size *)
      iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
      iEval (rewrite /i_size) in "Hisz".
      iApply (wp_lw_s_sconf (mword_of_int (DK + 0x1e)) Rs1 Rs2
                (mword_of_int 76 : mword 12) mdl (K - 10)%nat
                (di_size dn : mword 32) b
                ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi1e [Hisz]").
      { iEval (rgne; rewrite Hd18). iExact "Hisz". }
      iIntros (CID15 Hq15) "Hcg Hpc Hisz".
      iEval (rgne; rewrite Hd18) in "Hisz".
      iAssert (inode_meta ip dn) with "[Hity Himaj Himin Hinl Hisz]" as "Hmeta".
      { rewrite /inode_meta /i_size. iFrame. }
      set (Q1 := <[Regidx Rs1 := regval_into_reg
                    (sign_extend' 64 (di_size dn : mword 32) : mword 64)]> mdl).
      assert (HQ1p : dl_pregs m sp0 ip nb
                       (zero_extend' 64 (inum : mword 16) : mword 64)
                       (sign_extend' 64 (di_size dn : mword 32) : mword 64) Q1)
        by (rewrite /Q1; apply dl_pregs_of_eregs; exact Hdle).
      assert (HQ1s1 : Q1 !!! Regidx Rs1
                      = (sign_extend' 64 (di_size dn : mword 32) : mword 64))
        by (rewrite /Q1; apply upd_eq).
      assert (Hpp22 : add_vec_int (mword_of_int (DK + 0x1e) : mword 64) 4
                      = mword_of_int (DK + 0x22)) by pcw.
      iEval (rewrite Hpp22) in "Hpc".
      (* ================================================================= *)
      (*  THE SHARED TAIL at +0x70: strncpy, the [sh], writei, and the      *)
      (*  branchless return.  Three arms reach it and each brings the whole *)
      (*  linear bundle, so unlike [Htail] this one takes the contract's    *)
      (*  own continuation.                                                 *)
      (* ================================================================= *)
      iAssert (□ wp_next (CID0 := CID) true (proc_addr j) (fun CIDa : CpuId =>
                 ∀ (Mp : regfile) (dolz : nat -> bv 8) (w5 w6 : mword 64),
                   ⌜dl_pregs m sp0 ip nb
                      (zero_extend' 64 (inum : mword 16) : mword 64)
                      (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) Mp⌝ -∗
                   sie_cap_gpr Mp (K - 10)%nat b (proc_addr j) -∗
                   cpu_own 0 eb (proc_addr j) C b -∗
                   pc_is (mword_of_int (DK + 0x70)) -∗
                   (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
                   (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
                   (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
                   (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
                   (pa_stk sp0 5) ↦₈ w5 -∗
                   (pa_stk sp0 6) ↦₈ w6 -∗
                   (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
                   (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
                   ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ dolz jj) -∗
                   i_dev ip ↦₄{dqd} dev -∗
                   i_inum ip ↦₄{dqf} dinum -∗
                   inode_meta ip dn -∗
                   inode_map gfs ip bm -∗
                   inode_blocks gfs bm data -∗
                   ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
                   sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                   sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
                   sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                   bitmap_res gfs bmapstart cov logstart size used -∗
                   dinode_at gi dinum dn0 -∗
                   p_pid (proc_addr j) ↦₄{dq} pidv -∗
                   bslots bn 3 -∗
                   iref_slot -∗
                   log_op g ncount -∗
                   wp_next (CID0 := CID) true (proc_addr j) (fun CIDc : CpuId =>
                     ∀ (mf : regfile) (found : bool)
                       (bm' : blkmap) (data' : nat -> list (bv 8))
                       (dn' dn0' : dinode) (n' : nat) (used' : gset Z)
                       (tot : nat),
                         ⌜callee_saved m mf⌝ -∗
                         sie_cap_gpr mf K b (proc_addr j) -∗
                         cpu_own 0 eb (proc_addr j) C b -∗
                         pc_is ret_tgt -∗
                         i_dev ip ↦₄{dqd} dev -∗
                         i_inum ip ↦₄{dqf} dinum -∗
                         inode_meta ip dn' -∗
                         inode_map gfs ip bm' -∗
                         inode_blocks gfs bm' data' -∗
                         ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ{dqn} fn i) -∗
                         sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                         sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
                         sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                         bitmap_res gfs bmapstart cov logstart size used' -∗
                         dinode_at gi dinum dn0' -∗
                         p_pid (proc_addr j) ↦₄{dq} pidv -∗
                         bslots bn 3 -∗
                         iref_slot -∗
                         ⌜((ncount - dirlink_units)%nat <= n')%nat
                          /\ (n' <= ncount)%nat⌝ -∗
                         log_op g n' -∗
                         ⌜if found
                           then dir_first data nrec s <> None
                                /\ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
                                /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
                                /\ used' ⊆ used
                                /\ tot = 0%nat
                           else dir_first data nrec s = None
                                /\ used ⊆ used'
                                /\ blkmap_wf cov logstart bm'
                                /\ blk_holes_zero bm' data'
                                /\ di_addrs dn' = bm_cells bm'
                                /\ bv_unsigned (di_size dn') < 2 ^ 31
                                /\ bm_covers bm' (bv_unsigned (di_size dn'))
                                /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
                                /\ dn0' = dn'
                                /\ (tot <= 16)%nat
                                /\ (forall x : nat,
                                      file_byte data' x
                                      = if decide ((16 * k0 <= x)%nat
                                                   /\ (x < 16 * k0 + tot)%nat)
                                        then dirent_bytes (de_of_name inum s)
                                               !!! (x - 16 * k0)%nat
                                        else file_byte data x)
                                /\ ((mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)
                                     /\ tot = 16%nat)
                                    \/ (mf !!! Regidx Ra0
                                          = (mword_of_int (-1) : mword 64)
                                        /\ (tot < 16)%nat))⌝ -∗
                         WP (Loop : expr riscv_lang)) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "#Hafter".
      { iModIntro.
        iIntros (CIDa Hsa Mp dolz w5 w6)
          "%Hpr Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde Hidev Hiinum
           Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr Hdat Hppid Hbsl Hislot
           Hop Hqc".
        pose proof Hpr as HprW.
        destruct Hpr as (Hp2 & Hp8 & Hp9 & Hp18 & Hp21 & Hp22 & Hpthr).
        iPoseProof (dki_70 with "Htext") as "Hi70".
        iPoseProof (dki_72 with "Htext") as "Hi72".
        iPoseProof (dki_74 with "Htext") as "Hi74".
        iPoseProof (dki_78 with "Htext") as "Hi78".
        iPoseProof (dki_7c with "Htext") as "Hi7c".
        iPoseProof (dki_80 with "Htext") as "Hi80".
        iPoseProof (dki_82 with "Htext") as "Hi82".
        iPoseProof (dki_84 with "Htext") as "Hi84".
        iPoseProof (dki_88 with "Htext") as "Hi88".
        iPoseProof (dki_8a with "Htext") as "Hi8a".
        iPoseProof (dki_8c with "Htext") as "Hi8c".
        iPoseProof (dki_90 with "Htext") as "Hi90".
        iPoseProof (dki_92 with "Htext") as "Hi92".
        iPoseProof (dki_96 with "Htext") as "Hi96".
        iPoseProof (dki_9a with "Htext") as "Hi9a".
        (* +0x70 c.li a2,14 *)
        iApply (wp_cli_s_sconf (mword_of_int (DK + 0x70)) Ra2
                  (mword_of_int 14 : mword 6)
                  (mword_of_int (Z.of_nat 14%nat) : mword 64) Mp (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi70").
        iIntros (CIDA1 HqA1) "Hcg Hpc".
        set (W1 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int (Z.of_nat 14%nat) : mword 64)]> Mp).
        assert (HW1p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) W1)
          by (rewrite /W1; apply dl_pregs_caller; [exact Hcsa2 | exact HprW]).
        assert (Hqq72 : add_vec_int (mword_of_int (DK + 0x70) : mword 64) 2
                        = mword_of_int (DK + 0x72)) by pcw.
        iEval (rewrite Hqq72) in "Hpc".
        (* +0x72 c.mv a1,s5 *)
        iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x72)) Ra1 Rs5 W1
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi72").
        iIntros (CIDA2 HqA2) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (W2 := <[Regidx Ra1 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (W1 !!! Regidx Rs5))]> W1).
        assert (HW2p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) W2)
          by (rewrite /W2; apply dl_pregs_caller; [exact Hcsa1 | exact HW1p]).
        assert (HW2a1 : W2 !!! Regidx Ra1 = nb).
        { rewrite /W2 upd_eq.
          destruct HW1p as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
          rewrite D5. apply add_vec_zero_l. }
        assert (Hqq74 : add_vec_int (mword_of_int (DK + 0x72) : mword 64) 2
                        = mword_of_int (DK + 0x74)) by pcw.
        iEval (rewrite Hqq74) in "Hpc".
        (* +0x74 addi a0,s0,-78 : &de.name *)
        iApply (wp_addi4_s_sconf (mword_of_int (DK + 0x74)) Ra0 Rs0
                  (mword_of_int 4018 : mword 12) W2 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
        iIntros (CIDA3 HqA3) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (W3 := <[Regidx Ra0 := regval_into_reg
                       (add_vec (W2 !!! Regidx Rs0)
                          (sign_extend' 64 (mword_of_int 4018 : mword 12)))]> W2).
        assert (HW3p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) W3)
          by (rewrite /W3; apply dl_pregs_caller; [exact Hcsa0 | exact HW2p]).
        assert (HW3a0 : W3 !!! Regidx Ra0 = pa_add (pa_stk sp0 10) 2).
        { rewrite /W3 upd_eq.
          destruct HW2p as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
          rewrite D2. apply dl_dename_addr. }
        assert (HW3a1 : W3 !!! Regidx Ra1 = nb)
          by (rewrite /W3 upd_ne; [exact HW2a1 | nz]).
        assert (HW3a2 : W3 !!! Regidx Ra2
                        = (mword_of_int (Z.of_nat 14%nat) : mword 64)).
        { rewrite /W3 upd_ne; [| nz]. rewrite /W2 upd_ne; [| nz].
          rewrite /W1. apply upd_eq. }
        assert (Hqq78 : add_vec_int (mword_of_int (DK + 0x74) : mword 64) 4
                        = mword_of_int (DK + 0x78)) by pcw.
        iEval (rewrite Hqq78) in "Hpc".
        (* +0x78 jal ra,strncpy *)
        assert (Htgtsn : add_vec (mword_of_int (DK + 0x78) : mword 64)
                  (sign_extend' 64 (mword_of_int 2085880 : mword 21))
                  = mword_of_int KernelSyms.strncpy) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (DK + 0x78)) Rra
                  (mword_of_int 2085880 : mword 21) W3 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi78").
        iIntros (CIDA4 HqA4) "Hcg Hpc".
        iEval (rewrite Htgtsn) in "Hpc".
        set (W4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (DK + 0x78) : mword 64) 4)]> W3).
        assert (HW4p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) W4)
          by (rewrite /W4; apply dl_pregs_caller; [exact Hcsra | exact HW3p]).
        assert (HW4a0 : W4 !!! Regidx Ra0 = pa_add (pa_stk sp0 10) 2)
          by (rewrite /W4 upd_ne; [exact HW3a0 | nz]).
        assert (HW4a1 : W4 !!! Regidx Ra1 = nb)
          by (rewrite /W4 upd_ne; [exact HW3a1 | nz]).
        assert (HW4a2 : W4 !!! Regidx Ra2
                        = (mword_of_int (Z.of_nat 14%nat) : mword 64))
          by (rewrite /W4 upd_ne; [exact HW3a2 | nz]).
        assert (HW4ra : W4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (DK + 0x78) : mword 64) 4)
          by (rewrite /W4; apply upd_eq).
        (* the [de] buffer splits into the inum halfword and the name *)
        iEval (rewrite (dlk_de_split (pa_stk sp0 10) dolz)) in "Hde".
        iDestruct "Hde" as "[Hdehi Hdenm]".
        iEval (rewrite -HW4a0) in "Hdenm".
        iEval (rewrite -HW4a1) in "Hnm".
        iApply (SNC.wp_strncpy_sconf W4 14%nat fn (fun jj => dolz (2 + jj)%nat)
                  (K - 10)%nat dqn b (proc_addr j)
                  ltac:(exact HK2) HW4a2 ltac:(vm_compute; reflexivity)
                  with "Hcg Htext Hpc Hnm Hdenm [-]").
        iIntros (CIDsn Hssn msn hh) "Hcg Hpc Hnm Hdenm %Hcssn %Hsna0 %Hsnp".
        iEval (rewrite HW4a1) in "Hnm".
        iEval (rewrite HW4a0) in "Hdenm".
        assert (Hsnc : dl_snc fn hh 14%nat).
        { destruct Hsnp as [[Hbad _] | [_ Hp]]; [discriminate | exact Hp]. }
        assert (Hsnp' : dl_pregs m sp0 ip nb
                          (zero_extend' 64 (inum : mword 16) : mword 64)
                          (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) msn)
          by exact (dl_pregs_cs m sp0 ip nb _ _ W4 msn Hcssn HW4p).
        pose proof Hsnp' as HsnpW.
        destruct Hsnp' as (Hs2 & Hs8 & Hs9 & Hs18 & Hs21 & Hs22 & Hsthr).
        assert (Hpcsn : ret_pc (W4 !!! Regidx Rra : mword 64)
                        = mword_of_int (DK + 0x7c)) by (rewrite HW4ra; pcw).
        iEval (rewrite Hpcsn) in "Hpc".
        (* +0x7c sh s6,-80(s0) : de.inum := inum *)
        iDestruct (dl_bytes_half (pa_stk sp0 10) dolz
                     (dlk_align_8_2 _ Hal10) with "Hdehi") as (vold) "Hdehi".
        assert (Hdeadr : add_vec (msn !!! Regidx Rs0)
                           (sign_extend' 64 (mword_of_int 4016 : mword 12))
                         = pa_stk sp0 10) by (rewrite Hs8; apply dl_de_addr).
        iEval (rewrite -Hdeadr) in "Hdehi".
        iApply (wp_sh_s_sconf (mword_of_int (DK + 0x7c)) Rs6 Rs0
                  (mword_of_int 4016 : mword 12) msn (K - 10)%nat vold b
                  with "Hcg Hpc Hi7c [Hdehi]").
        { iEval (rgne). iExact "Hdehi". }
        iIntros (CIDA5 HqA5) "Hcg Hpc Hdehi".
        iEval (rgne; rgne; rewrite Hdeadr Hs22 dl_trunc16_zext) in "Hdehi".
        assert (Hqq80 : add_vec_int (mword_of_int (DK + 0x7c) : mword 64) 4
                        = mword_of_int (DK + 0x80)) by pcw.
        iEval (rewrite Hqq80) in "Hpc".
        (* ---- the sixteen bytes ARE [dirent_bytes (de_of_name inum s)] ---- *)
        iDestruct (word2_pointsto_bytes with "Hdehi") as "Hdehi".
        iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj
                   ↦ₘ (dirent_bytes (de_of_name inum s) !!! jj))%I
          with "[Hdehi Hdenm]" as "Hsrc".
        { rewrite (dlk_de_split (pa_stk sp0 10)
                     (fun jj => dirent_bytes (de_of_name inum s) !!! jj)).
          iSplitL "Hdehi".
          - rewrite (bb_ext (pa_stk sp0 10) 2
                       (fun jj => nth_byte inum jj)
                       (fun jj => dirent_bytes (de_of_name inum s) !!! jj)
                       (fun jj Hjj => eq_sym (dl_rec_hi fn inum jj Hjj))).
            iExact "Hdehi".
          - rewrite (bb_ext (pa_add (pa_stk sp0 10) 2) 14 hh
                       (fun jj => dirent_bytes (de_of_name inum s) !!! (2 + jj)%nat)
                       (fun jj Hjj => eq_sym (dl_rec_nm fn hh inum jj Hsnc Hjj))).
            iExact "Hdenm". }
        (* +0x80 c.li a4,16 *)
        iApply (wp_cli_s_sconf (mword_of_int (DK + 0x80)) Ra4
                  (mword_of_int 16 : mword 6)
                  (mword_of_int (Z.of_nat 16%nat) : mword 64) msn (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc Hi80").
        iIntros (CIDA6 HqA6) "Hcg Hpc".
        set (V1 := <[Regidx Ra4 := regval_into_reg
                      (mword_of_int (Z.of_nat 16%nat) : mword 64)]> msn).
        assert (HV1p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V1)
          by (rewrite /V1; apply dl_pregs_caller; [exact Hcsa4 | exact HsnpW]).
        assert (Hqq82 : add_vec_int (mword_of_int (DK + 0x80) : mword 64) 2
                        = mword_of_int (DK + 0x82)) by pcw.
        iEval (rewrite Hqq82) in "Hpc".
        (* +0x82 c.mv a3,s1 : off *)
        iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x82)) Ra3 Rs1 V1
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi82").
        iIntros (CIDA7 HqA7) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (V2 := <[Regidx Ra3 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (V1 !!! Regidx Rs1))]> V1).
        assert (HV2p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V2)
          by (rewrite /V2; apply dl_pregs_caller; [exact Hcsa3 | exact HV1p]).
        assert (HV2a3 : V2 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64)).
        { rewrite /V2 upd_eq.
          destruct HV1p as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
          rewrite D3. apply add_vec_zero_l. }
        assert (HV2a4 : V2 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16%nat) : mword 64)).
        { rewrite /V2 upd_ne; [| nz]. rewrite /V1. apply upd_eq. }
        assert (Hqq84 : add_vec_int (mword_of_int (DK + 0x82) : mword 64) 2
                        = mword_of_int (DK + 0x84)) by pcw.
        iEval (rewrite Hqq84) in "Hpc".
        (* +0x84 addi a2,s0,-80 : &de *)
        iApply (wp_addi4_s_sconf (mword_of_int (DK + 0x84)) Ra2 Rs0
                  (mword_of_int 4016 : mword 12) V2 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi84").
        iIntros (CIDA8 HqA8) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (V3 := <[Regidx Ra2 := regval_into_reg
                       (add_vec (V2 !!! Regidx Rs0)
                          (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> V2).
        assert (HV3p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V3)
          by (rewrite /V3; apply dl_pregs_caller; [exact Hcsa2 | exact HV2p]).
        assert (HV3a2 : V3 !!! Regidx Ra2 = pa_stk sp0 10).
        { rewrite /V3 upd_eq.
          destruct HV2p as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
          rewrite D2. apply dl_de_addr. }
        assert (HV3a3 : V3 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64))
          by (rewrite /V3 upd_ne; [exact HV2a3 | nz]).
        assert (HV3a4 : V3 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16%nat) : mword 64))
          by (rewrite /V3 upd_ne; [exact HV2a4 | nz]).
        assert (Hqq88 : add_vec_int (mword_of_int (DK + 0x84) : mword 64) 4
                        = mword_of_int (DK + 0x88)) by pcw.
        iEval (rewrite Hqq88) in "Hpc".
        (* +0x88 c.li a1,0 : the KERNEL source *)
        iApply (wp_cli_s_sconf (mword_of_int (DK + 0x88)) Ra1
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) V3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi88").
        iIntros (CIDA9 HqA9) "Hcg Hpc".
        set (V4 := <[Regidx Ra1 := regval_into_reg
                      (mword_of_int 0 : mword 64)]> V3).
        assert (HV4p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V4)
          by (rewrite /V4; apply dl_pregs_caller; [exact Hcsa1 | exact HV3p]).
        assert (HV4a1 : V4 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /V4; apply upd_eq).
        assert (HV4a2 : V4 !!! Regidx Ra2 = pa_stk sp0 10)
          by (rewrite /V4 upd_ne; [exact HV3a2 | nz]).
        assert (HV4a3 : V4 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64))
          by (rewrite /V4 upd_ne; [exact HV3a3 | nz]).
        assert (HV4a4 : V4 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16%nat) : mword 64))
          by (rewrite /V4 upd_ne; [exact HV3a4 | nz]).
        assert (Hqq8a : add_vec_int (mword_of_int (DK + 0x88) : mword 64) 2
                        = mword_of_int (DK + 0x8a)) by pcw.
        iEval (rewrite Hqq8a) in "Hpc".
        (* +0x8a c.mv a0,s2 : dp *)
        iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x8a)) Ra0 Rs2 V4
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
        iIntros (CIDA10 HqA10) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (V5 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (zero_reg : mword 64) (V4 !!! Regidx Rs2))]> V4).
        assert (HV5p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V5)
          by (rewrite /V5; apply dl_pregs_caller; [exact Hcsa0 | exact HV4p]).
        assert (HV5a0 : V5 !!! Regidx Ra0 = ip).
        { rewrite /V5 upd_eq.
          destruct HV4p as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
          rewrite D4. apply add_vec_zero_l. }
        assert (HV5a1 : V5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /V5 upd_ne; [exact HV4a1 | nz]).
        assert (HV5a2 : V5 !!! Regidx Ra2 = pa_stk sp0 10)
          by (rewrite /V5 upd_ne; [exact HV4a2 | nz]).
        assert (HV5a3 : V5 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64))
          by (rewrite /V5 upd_ne; [exact HV4a3 | nz]).
        assert (HV5a4 : V5 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16%nat) : mword 64))
          by (rewrite /V5 upd_ne; [exact HV4a4 | nz]).
        assert (Hqq8c : add_vec_int (mword_of_int (DK + 0x8a) : mword 64) 2
                        = mword_of_int (DK + 0x8c)) by pcw.
        iEval (rewrite Hqq8c) in "Hpc".
        (* +0x8c jal ra,writei *)
        assert (Htgtwi : add_vec (mword_of_int (DK + 0x8c) : mword 64)
                  (sign_extend' 64 (mword_of_int 2096238 : mword 21))
                  = mword_of_int KernelSyms.writei) by pcw.
        iApply (wp_jal_s_sconf (mword_of_int (DK + 0x8c)) Rra
                  (mword_of_int 2096238 : mword 21) V5 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi8c").
        iIntros (CIDA11 HqA11) "Hcg Hpc".
        iEval (rewrite Htgtwi) in "Hpc".
        set (V6 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (DK + 0x8c) : mword 64) 4)]> V5).
        assert (HV6p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V6)
          by (rewrite /V6; apply dl_pregs_caller; [exact Hcsra | exact HV5p]).
        assert (HV6a0 : V6 !!! Regidx Ra0 = ip)
          by (rewrite /V6 upd_ne; [exact HV5a0 | nz]).
        assert (HV6a1 : V6 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
          by (rewrite /V6 upd_ne; [exact HV5a1 | nz]).
        assert (HV6a2 : V6 !!! Regidx Ra2 = pa_stk sp0 10)
          by (rewrite /V6 upd_ne; [exact HV5a2 | nz]).
        assert (HV6a3 : V6 !!! Regidx Ra3
                        = (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64))
          by (rewrite /V6 upd_ne; [exact HV5a3 | nz]).
        assert (HV6a4 : V6 !!! Regidx Ra4
                        = (mword_of_int (Z.of_nat 16%nat) : mword 64))
          by (rewrite /V6 upd_ne; [exact HV5a4 | nz]).
        assert (HV6ra : V6 !!! Regidx Rra
                        = add_vec_int (mword_of_int (DK + 0x8c) : mword 64) 4)
          by (rewrite /V6; apply upd_eq).
        iEval (rewrite -HV6a2) in "Hsrc".
        iDestruct (cpu_own_transport CIDa CIDA11 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iApply (WI.wp_writei_sconf gs j gl gu gd gk pd pav pu bn g gfs gi ga gf
                  cov logstart inodestart nib bmapstart size dev used gpr
                  ip dinum bm data dn dn0
                  false (16 * k0)%nat 16%nat
                  (fun jj => dirent_bytes (de_of_name inum s) !!! jj)
                  dl_dummyV ncount
                  pidv dq dqd dqf dqs dqb dqbs V6 (K - 10)%nat eb C b
                  ltac:(exact HKwi)
                  ltac:(rewrite (dl_wi_cost k0); unfold dirlink_units in Hnc;
                        exact Hnc)
                  Hlg Hist0 Hiblk Hiblog Hdinb Haddrs
                  ltac:(rewrite Htype; vm_compute; discriminate)
                  Hbmwf Hholes Hbmcov
                  ltac:(change (Z.of_nat 16%nat) with 16;
                        exact (dl_lt31 _ Hk0fit))
                  Hsz31 Hbmgeo Hpkc Hj Hgs HV6a0
                  ltac:(cbn [negb]; rewrite HV6a1 dlk_zero_moi;
                        exact (eq_vec_refl _))
                  HV6a3 HV6a4 Heb
                  with "Hcg Hcnt Htext Hpc Hpanic Hkd Hpk Hbio Hlog Hkenv
                        Hidev Hiinum Hmeta Hmap Hblocks Hsbi Hsbs Hsbb Hbmr
                        Hiregi Hdat Hsrc Hppid Hprocs Hdev Hgeom Hdlk Hbsl
                        Hop [-]").
        iIntros (CIDwi Hswi mwi tot bm' data' dn' dn0' nn wrote dist dstb P' used')
          "%Hcswi %Hused %Hwf' %Hholes' %Haddrs' %Hsz' %Hcov' %Hdistb %Hdist0
           %Hdistk %Hrange %Htie %Harm %Hbud %Hupt Hcg Hcnt Hpc Hppid Hidev Hiinum
           Hmeta Hmap Hblocks Hsbi Hsbs Hsbb Hbmr Hdat Hsrc Hbsl Hop".
        (* THE DISTURBED REGION IS EMPTY (fs-icache.md §15.1(i)): dirlink's
           source is its own stack record, so writei ran on the KERNEL arm
           and [dist = 0].  Substituting it here is what turns the range
           clause below from three-way into two-way -- and with it, dir-wf
           over a middle-slot link from underivable into derivable. *)
        pose proof (Hdistk eq_refl) as Hdist_zero.
        subst dist.
        iEval (rewrite HV6a2) in "Hsrc".
        assert (Hpcwi : ret_pc (V6 !!! Regidx Rra : mword 64)
                        = mword_of_int (DK + 0x90)) by (rewrite HV6ra; pcw).
        iEval (rewrite Hpcwi) in "Hpc".
        (* writei's OWN -1 arm is DEAD: the write is at [off <= size] and
           ends at [off + 16 <= MAXFILE*BSIZE] *)
        assert (Hwiok : mwi !!! Regidx Ra0
                          = (mword_of_int (Z.of_nat tot) : mword 64)
                        /\ (tot <= 16)%nat
                        /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
                        /\ dn0' = dn').
        { destruct Harm as [(_ & [Hbad | Hbad] & _) | Hgood];
            [ exfalso; exact (dl_nle _ _ Hk0le Hbad)
            | exfalso; exact (dl_nnle _ _ Hk0n Hbad)
            | exact Hgood ]. }
        destruct Hwiok as (Hwia0 & Htotle & Hdn' & Hdn0').
        assert (Hwip : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) mwi)
          by exact (dl_pregs_cs m sp0 ip nb _ _ V6 mwi Hcswi HV6p).
        (* +0x90 c.addi a0,a0,-16 *)
        iApply (wp_caddi_s_sconf (mword_of_int (DK + 0x90)) Ra0
                  (mword_of_int 48 : mword 6) mwi (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi90").
        iIntros (CIDA12 HqA12) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (V7 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (mwi !!! Regidx Ra0)
                         (sign_extend' 64
                            (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mwi).
        assert (Hqq92 : add_vec_int (mword_of_int (DK + 0x90) : mword 64) 2
                        = mword_of_int (DK + 0x92)) by pcw.
        iEval (rewrite Hqq92) in "Hpc".
        assert (HV7p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V7)
          by (rewrite /V7; apply dl_pregs_caller; [exact Hcsa0 | exact Hwip]).
        assert (HV7a0 : V7 !!! Regidx Ra0
                        = add_vec (mword_of_int (Z.of_nat tot) : mword 64)
                            (sign_extend' 64
                               (sign_extend' 12 (mword_of_int 48 : mword 6)))).
        { rewrite /V7 upd_eq. rewrite Hwia0. reflexivity. }
        (* +0x92 sltu a0,zero,a0  ([snez]) *)
        iDestruct (sie_cap_gpr_x0 V7 (K - 10)%nat b (proc_addr j) Rz
                     ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0 Hcg]".
        iApply (wp_sltu_s_sconf (mword_of_int (DK + 0x92)) Ra0 Rz Ra0
                  (if decide (tot = 16%nat) then (mword_of_int 0 : mword 64)
                   else (mword_of_int 1 : mword 64)) V7 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok)
                  ltac:(rgne; rgne; rewrite Hz0 HV7a0;
                        destruct (decide (tot = 16%nat)) as [Hte | Htn];
                        [ rewrite Hte dl_snez_eq; exact dl_bit_0
                        | rewrite (dl_snez_lt tot (dl_lt16 tot Htotle Htn));
                          exact dl_bit_1 ])
                  with "Hcg Hpc Hi92").
        iIntros (CIDA13 HqA13) "Hcg Hpc".
        set (V8 := <[Regidx Ra0 := regval_into_reg
                      (if decide (tot = 16%nat) then (mword_of_int 0 : mword 64)
                       else (mword_of_int 1 : mword 64))]> V7).
        assert (HV8p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V8)
          by (rewrite /V8; apply dl_pregs_caller; [exact Hcsa0 | exact HV7p]).
        assert (HV8a0 : V8 !!! Regidx Ra0
                        = (if decide (tot = 16%nat) then (mword_of_int 0 : mword 64)
                           else (mword_of_int 1 : mword 64)))
          by (rewrite /V8; apply upd_eq).
        assert (Hqq96 : add_vec_int (mword_of_int (DK + 0x92) : mword 64) 4
                        = mword_of_int (DK + 0x96)) by pcw.
        iEval (rewrite Hqq96) in "Hpc".
        (* +0x96 subw a0,zero,a0  ([negw]) *)
        iDestruct (sie_cap_gpr_x0 V8 (K - 10)%nat b (proc_addr j) Rz
                     ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hz0' Hcg]".
        iApply (wp_subw_s_sconf (mword_of_int (DK + 0x96)) Ra0 Rz Ra0
                  V8 (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi96").
        iIntros (CIDA14 HqA14) "Hcg Hpc".
        set (V9 := <[Regidx Ra0 := regval_into_reg
                      (sign_extend' 64
                         (sub_vec (subrange_vec_dec (rget V8 Rz) 31 0 : mword 32)
                            (subrange_vec_dec (rget V8 Ra0) 31 0 : mword 32)))]> V8).
        assert (HV9p : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) V9)
          by (rewrite /V9; apply dl_pregs_caller; [exact Hcsa0 | exact HV8p]).
        pose proof HV9p as HV9pW.
        destruct HV9p as (Hv2 & Hv8 & Hv9 & Hv18 & Hv21 & Hv22 & Hvthr).
        assert (HV9a0 : V9 !!! Regidx Ra0
                        = (if decide (tot = 16%nat) then (mword_of_int 0 : mword 64)
                           else (mword_of_int (-1) : mword 64))).
        { rewrite /V9 upd_eq. rgne. rgne. rewrite Hz0' HV8a0.
          destruct (decide (tot = 16%nat)) as [Hte | Htn];
            [exact dl_negw_0 | exact dl_negw_1]. }
        assert (Hqq9a : add_vec_int (mword_of_int (DK + 0x96) : mword 64) 4
                        = mword_of_int (DK + 0x9a)) by pcw.
        iEval (rewrite Hqq9a) in "Hpc".
        (* +0x9a c.ldsp s1,56(sp) : the LAZY restore *)
        assert (HfT3 : add_vec (V9 !!! Regidx csp_rs1)
                         (zero_extend' 64
                            (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                       = pa_stk sp0 3) by (rewrite Hv2; apply dl_frm3).
        iEval (rewrite -HfT3) in "Hb3".
        iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x9a)) (mword_of_int 7 : mword 6)
                  Rs1 V9 (K - 10)%nat (m !!! Regidx Rs1 : mword 64) b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi9a Hb3").
        iIntros (CIDA15 HqA15) "Hcg Hpc Hb3".
        iEval (rewrite HfT3) in "Hb3".
        set (V10 := <[Regidx Rs1 := regval_into_reg
                       (m !!! Regidx Rs1 : mword 64)]> V9).
        assert (HV10t : dl_tregs m sp0 V10)
          by (rewrite /V10;
              exact (dl_tregs_of_pregs m sp0 ip nb _ _ V9 _ eq_refl HV9pW)).
        assert (HV10a0 : V10 !!! Regidx Ra0
                         = (if decide (tot = 16%nat) then (mword_of_int 0 : mword 64)
                            else (mword_of_int (-1) : mword 64)))
          by (rewrite /V10 upd_ne; [exact HV9a0 | nz]).
        assert (Hqq9c : add_vec_int (mword_of_int (DK + 0x9a) : mword 64) 2
                        = mword_of_int (DK + 0x9c)) by pcw.
        iEval (rewrite Hqq9c) in "Hpc".
        (* ---- into the shared epilogue ---- *)
        iPoseProof ("Htail" $! CIDA15) as "Ht".
        iSpecialize ("Ht" with "[%]"); [wp_next_chain |].
        iApply ("Ht" $! V10 (m !!! Regidx Rs1 : mword 64) w5 w6
                  (fun jj => dirent_bytes (de_of_name inum s) !!! jj) with
                  "[%] Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hsrc [-]").
        { exact HV10t. }
        iIntros (CIDf Hsf mf) "%Hcsf %Ha0f Hcg Hpc".
        iDestruct (cpu_own_transport CIDwi CIDf 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hqc" $! CIDf with "[%]"); [wp_next_chain |].
        iApply ("Hqc" $! mf false bm' data' dn' dn0' nn used' tot with
                  "[%] Hcg Hcnt Hpc Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi
                   Hsbs Hsbb Hbmr Hdat Hppid Hbsl Hislot [%] Hop [%]").
        { exact Hcsf. }
        { rewrite (dl_wi_cost k0) in Hbud. unfold dirlink_units. exact Hbud. }
        { split; [exact Hnone |].
          split; [exact Hused |].
          split; [exact Hwf' |].
          split; [exact Hholes' |].
          split; [exact Haddrs' |].
          split; [exact Hsz' |].
          split; [exact Hcov' |].
          split; [exact Hdn' |].
          split; [exact Hdn0' |].
          split; [exact Htotle |].
          split.
          - intro x. rewrite (Hrange x).
            destruct (decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat))
              as [[Hxl Hxr] | Hxn].
            + rewrite (Htie eq_refl (x - 16 * k0)%nat
                         (dl_subrng (16 * k0)%nat x tot Hxl Hxr)). reflexivity.
            + (* THE MIDDLE TEST IS DEAD: [dist = 0] on the kernel arm, so
                 the disturbed window [16*k0+tot, 16*k0+tot) is empty *)
              rewrite decide_False; [reflexivity | lia].
          - rewrite Ha0f HV10a0.
            destruct (decide (tot = 16%nat)) as [Hte | Htn].
            + left. split; [reflexivity | exact Hte].
            + right. split; [reflexivity | exact (dl_lt16 tot Htotle Htn)]. } }
      (* ================================================================= *)
      (*  +0x22 [c.beqz s1]: the EMPTY-DIRECTORY shortcut.                  *)
      (* ================================================================= *)
      assert (Htgt70 : add_vec (mword_of_int (DK + 0x22) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 39 : mword 8) ('b"0"))))
                = mword_of_int (DK + 0x70)) by pcw.
      destruct (decide (bv_unsigned (di_size dn) = 0)) as [Hsz0 | Hszn].
      + (* ---------- the directory is EMPTY: s1 = 0 is already [off] ------ *)
        iApply (wp_cbeqz_taken_s_sconf (mword_of_int (DK + 0x22))
                  (mword_of_int 39 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  Q1 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ1s1; exact (dl_sz_eqz _ Hsz0))
                  ltac:(rewrite Htgt70; vm_compute; reflexivity)
                  with "Hcg Hpc Hi22").
        iNext. iIntros (CID16 Hq16) "Hcg Hpc".
        iEval (rewrite Htgt70) in "Hpc".
        assert (Hk00 : k0 = 0%nat)
          by exact (eq_trans (f_equal (dir_slot data) (dl_nrec_zero _ Hsz0))
                      (dl_slot_zero data)).
        assert (HQ1v : dl_pregs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64)
                         (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64) Q1).
        { rewrite Hk00. rewrite -(dl_sz_zero_val (di_size dn) Hsz31 Hsz0).
          exact HQ1p. }
        iDestruct (dl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
          [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
        iDestruct (cpu_own_transport CIDdl CID16 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iPoseProof ("Hafter" $! CID16) as "Ha".
        iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
        iApply ("Ha" $! Q1 dolds0 u5 u6 with
                  "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde Hidev
                   Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr Hdat Hppid
                   Hbsl Hislot Hop Hcont").
        { exact HQ1v. }
      + (* ---------- the directory is NON-EMPTY: the scan ---------------- *)
        iApply (wp_cbeqz_fall_s_sconf (mword_of_int (DK + 0x22))
                  (mword_of_int 39 : mword 8) (Cregidx (mword_of_int 1)) Rs1
                  Q1 (K - 10)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(nz)
                  ltac:(rgne; rewrite HQ1s1; exact (dl_sz_nez _ Hsz31 Hszn))
                  with "Hcg Hpc Hi22").
        iIntros (CID16 Hq16) "Hcg Hpc".
        assert (Hpp24 : add_vec_int (mword_of_int (DK + 0x22) : mword 64) 2
                        = mword_of_int (DK + 0x24)) by pcw.
        iEval (rewrite Hpp24) in "Hpc".
        iPoseProof (dki_24 with "Htext") as "Hi24".
        iPoseProof (dki_26 with "Htext") as "Hi26".
        iPoseProof (dki_28 with "Htext") as "Hi28".
        iPoseProof (dki_2a with "Htext") as "Hi2a".
        iPoseProof (dki_2e with "Htext") as "Hi2e".
        pose proof HQ1p as HQ1pW.
        destruct HQ1p as (Hu2 & Hu8 & Hu9 & Hu18 & Hu21 & Hu22 & Huthr).
        assert (Hus3 : Q1 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
          by (apply Huthr; first [ vm_compute; reflexivity
                                 | vm_compute; discriminate ]).
        assert (Hus4 : Q1 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64))
          by (apply Huthr; first [ vm_compute; reflexivity
                                 | vm_compute; discriminate ]).
        (* +0x24 c.sdsp s3,40(sp) : the LAZY save *)
        assert (Hf5 : add_vec (Q1 !!! Regidx csp_rs1)
                        (zero_extend' 64
                           (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                      = pa_stk sp0 5) by (rewrite Hu2; apply dl_frm5).
        iEval (rewrite -Hf5) in "Hb5".
        iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x24)) (mword_of_int 5 : mword 6)
                  Rs3 Q1 (K - 10)%nat u5 b with "Hcg Hpc Hi24 Hb5").
        iIntros (CID17 Hq17) "Hcg Hpc Hb5".
        iEval (rgne; rewrite Hus3 Hf5) in "Hb5".
        assert (Hpp26 : add_vec_int (mword_of_int (DK + 0x24) : mword 64) 2
                        = mword_of_int (DK + 0x26)) by pcw.
        iEval (rewrite Hpp26) in "Hpc".
        (* +0x26 c.sdsp s4,32(sp) *)
        assert (Hf6 : add_vec (Q1 !!! Regidx csp_rs1)
                        (zero_extend' 64
                           (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                      = pa_stk sp0 6) by (rewrite Hu2; apply dl_frm6).
        iEval (rewrite -Hf6) in "Hb6".
        iApply (wp_csdsp_s_sconf (mword_of_int (DK + 0x26)) (mword_of_int 4 : mword 6)
                  Rs4 Q1 (K - 10)%nat u6 b with "Hcg Hpc Hi26 Hb6").
        iIntros (CID18 Hq18) "Hcg Hpc Hb6".
        iEval (rgne; rewrite Hus4 Hf6) in "Hb6".
        assert (Hpp28 : add_vec_int (mword_of_int (DK + 0x26) : mword 64) 2
                        = mword_of_int (DK + 0x28)) by pcw.
        iEval (rewrite Hpp28) in "Hpc".
        (* +0x28 c.li s1,0 : off := 0 *)
        iApply (wp_cli_s_sconf (mword_of_int (DK + 0x28)) Rs1
                  (mword_of_int 0 : mword 6)
                  (mword_of_int (Z.of_nat (16 * 0)%nat) : mword 64) Q1
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi28").
        iIntros (CID19 Hq19) "Hcg Hpc".
        set (Q2 := <[Regidx Rs1 := regval_into_reg
                      (mword_of_int (Z.of_nat (16 * 0)%nat) : mword 64)]> Q1).
        assert (HQ2s0 : Q2 !!! Regidx Rs0 = sp0)
          by (rewrite /Q2 upd_ne; [exact Hu8 | nz]).
        assert (Hpp2a : add_vec_int (mword_of_int (DK + 0x28) : mword 64) 2
                        = mword_of_int (DK + 0x2a)) by pcw.
        iEval (rewrite Hpp2a) in "Hpc".
        (* +0x2a addi s4,s0,-80 : s4 := &de *)
        iApply (wp_addi4_s_sconf (mword_of_int (DK + 0x2a)) Rs4 Rs0
                  (mword_of_int 4016 : mword 12) Q2 (K - 10)%nat b
                  ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi2a").
        iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (Q3 := <[Regidx Rs4 := regval_into_reg
                       (add_vec (Q2 !!! Regidx Rs0)
                          (sign_extend' 64 (mword_of_int 4016 : mword 12)))]> Q2).
        assert (HQ3s4 : Q3 !!! Regidx Rs4 = pa_stk sp0 10).
        { rewrite /Q3 upd_eq. rewrite HQ2s0. apply dl_de_addr. }
        assert (Hpp2e : add_vec_int (mword_of_int (DK + 0x2a) : mword 64) 4
                        = mword_of_int (DK + 0x2e)) by pcw.
        iEval (rewrite Hpp2e) in "Hpc".
        (* +0x2e c.li s3,16 *)
        iApply (wp_cli_s_sconf (mword_of_int (DK + 0x2e)) Rs3
                  (mword_of_int 16 : mword 6) (mword_of_int 16 : mword 64) Q3
                  (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                  with "Hcg Hpc Hi2e").
        iIntros (CID21 Hq21) "Hcg Hpc".
        set (Q4 := <[Regidx Rs3 := regval_into_reg
                      (mword_of_int 16 : mword 64)]> Q3).
        assert (HQ4r : dl_regs m sp0 ip nb
                         (zero_extend' 64 (inum : mword 16) : mword 64) 0%nat Q4).
        { unfold dl_regs. split_and!.
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_ne; [exact Hu2 | nz].
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_ne; [exact Hu8 | nz].
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_eq. reflexivity.
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_ne; [exact Hu18 | nz].
          - rewrite /Q4 upd_eq. reflexivity.
          - rewrite /Q4 upd_ne; [exact HQ3s4 | nz].
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_ne; [exact Hu21 | nz].
          - rewrite /Q4 upd_ne; [| nz]. rewrite /Q3 upd_ne; [| nz].
            rewrite /Q2 upd_ne; [exact Hu22 | nz].
          - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22.
            rewrite /Q4 upd_ne; [| dlk_xne N19].
            rewrite /Q3 upd_ne; [| dlk_xne N20].
            rewrite /Q2 upd_ne; [| dlk_xne N9].
            exact (Huthr c Hc N2 N8 N9 N18 N21 N22). }
        assert (Hpp30 : add_vec_int (mword_of_int (DK + 0x2e) : mword 64) 2
                        = mword_of_int (DK + 0x30)) by pcw.
        iEval (rewrite Hpp30) in "Hpc".
        (* =============================================================== *)
        (*  THE SCAN.  A fuel induction wrapped in [wp_next]: readi sleeps, *)
        (*  so the hart moves inside the body.  Measure [nrec - i].         *)
        (* =============================================================== *)
        iAssert (∀ fuel : nat,
          wp_next (CID0 := CID) true (proc_addr j) (fun CIDl : CpuId =>
            ∀ (i : nat) (Ml : regfile) (dol : nat -> bv 8),
              ⌜(S nrec - i <= fuel)%nat⌝ -∗
              (* §15(b): THE LOOP TEST, not [i < nrec] -- without
                 granularity the code takes one turn past [nrec], whose
                 readi is short and whose next branch panics. *)
              ⌜Z.of_nat i * 16 < bv_unsigned (di_size dn)⌝ -∗
              ⌜dir_free_first data i = None⌝ -∗
              ⌜dl_regs m sp0 ip nb
                 (zero_extend' 64 (inum : mword 16) : mword 64) (16 * i)%nat Ml⌝ -∗
              sie_cap_gpr Ml (K - 10)%nat b (proc_addr j) -∗
              cpu_own 0 eb (proc_addr j) C b -∗
              pc_is (mword_of_int (DK + 0x30)) -∗
              (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
              (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
              (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
              (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
              (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
              (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
              (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
              (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
              ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj ↦ₘ dol jj) -∗
              i_dev ip ↦₄{dqd} dev -∗
              i_inum ip ↦₄{dqf} dinum -∗
              inode_meta ip dn -∗
              inode_map gfs ip bm -∗
              inode_blocks gfs bm data -∗
              ([∗ list] i0 ∈ seq 0 14, pa_add nb i0 ↦ₘ{dqn} fn i0) -∗
              sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
              sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
              sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
              bitmap_res gfs bmapstart cov logstart size used -∗
              dinode_at gi dinum dn0 -∗
              p_pid (proc_addr j) ↦₄{dq} pidv -∗
              bslot bn -∗
              bslots bn 2 -∗
              iref_slot -∗
              log_op g ncount -∗
              wp_next (CID0 := CID) true (proc_addr j) (fun CIDc : CpuId =>
                ∀ (mf : regfile) (found : bool)
                  (bm' : blkmap) (data' : nat -> list (bv 8))
                  (dn' dn0' : dinode) (n' : nat) (used' : gset Z)
                  (tot : nat),
                    ⌜callee_saved m mf⌝ -∗
                    sie_cap_gpr mf K b (proc_addr j) -∗
                    cpu_own 0 eb (proc_addr j) C b -∗
                    pc_is ret_tgt -∗
                    i_dev ip ↦₄{dqd} dev -∗
                    i_inum ip ↦₄{dqf} dinum -∗
                    inode_meta ip dn' -∗
                    inode_map gfs ip bm' -∗
                    inode_blocks gfs bm' data' -∗
                    ([∗ list] i0 ∈ seq 0 14, pa_add nb i0 ↦ₘ{dqn} fn i0) -∗
                    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
                    sb_size ↦₄{dqbs} (mword_of_int size : mword 32) -∗
                    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
                    bitmap_res gfs bmapstart cov logstart size used' -∗
                    dinode_at gi dinum dn0' -∗
                    p_pid (proc_addr j) ↦₄{dq} pidv -∗
                    bslots bn 3 -∗
                    iref_slot -∗
                    ⌜((ncount - dirlink_units)%nat <= n')%nat
                     /\ (n' <= ncount)%nat⌝ -∗
                    log_op g n' -∗
                    ⌜if found
                      then dir_first data nrec s <> None
                           /\ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)
                           /\ bm' = bm /\ data' = data /\ dn' = dn /\ dn0' = dn0
                           /\ used' ⊆ used
                           /\ tot = 0%nat
                      else dir_first data nrec s = None
                           /\ used ⊆ used'
                           /\ blkmap_wf cov logstart bm'
                           /\ blk_holes_zero bm' data'
                           /\ di_addrs dn' = bm_cells bm'
                           /\ bv_unsigned (di_size dn') < 2 ^ 31
                           /\ bm_covers bm' (bv_unsigned (di_size dn'))
                           /\ dn' = wi_dinode dn bm' (16 * k0)%nat tot
                           /\ dn0' = dn'
                           /\ (tot <= 16)%nat
                           /\ (forall x : nat,
                                 file_byte data' x
                                 = if decide ((16 * k0 <= x)%nat
                                              /\ (x < 16 * k0 + tot)%nat)
                                   then dirent_bytes (de_of_name inum s)
                                          !!! (x - 16 * k0)%nat
                                   else file_byte data x)
                           /\ ((mf !!! Regidx Ra0 = (mword_of_int 0 : mword 64)
                                /\ tot = 16%nat)
                               \/ (mf !!! Regidx Ra0
                                     = (mword_of_int (-1) : mword 64)
                                   /\ (tot < 16)%nat))⌝ -∗
                    WP (Loop : expr riscv_lang)) -∗
              WP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
        { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
          { iIntros (CIDl Hsl i Ml dol)
              "%Hfuel %Hilt16 %Hffn %Hregs Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6
               Hb7 Hb8 Hde Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb
               Hbmr Hdat Hppid Hbs1 Hbs2 Hislot Hop Hqc".
            exfalso.
            assert (Hile : (i <= nrec)%nat)
              by exact (dlk_le_nrec (bv_unsigned (di_size dn)) i Hsznn Hilt16).
            lia. }
          iIntros (CIDl Hsl i Ml dol)
            "%Hfuel %Hilt16 %Hffn %Hregs Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6
             Hb7 Hb8 Hde Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb
             Hbmr Hdat Hppid Hbs1 Hbs2 Hislot Hop Hqc".
          assert (Hoff31 : Z.of_nat (16 * i)%nat + 16 < 2 ^ 31)
            by exact (dlk_off_lt31' (bv_unsigned (di_size dn)) i Hsznn Hilt16 Hszb).
          pose proof Hregs as HregsW.
          destruct Hregs as (Hm2 & Hm8 & Hm9 & Hm18 & Hm19 & Hm20 & Hm21 & Hm22
                            & Hmthr).
          iPoseProof (dki_30 with "Htext") as "Hj30".
          iPoseProof (dki_32 with "Htext") as "Hj32".
          iPoseProof (dki_34 with "Htext") as "Hj34".
          iPoseProof (dki_36 with "Htext") as "Hj36".
          iPoseProof (dki_38 with "Htext") as "Hj38".
          iPoseProof (dki_3a with "Htext") as "Hj3a".
          iPoseProof (dki_3e with "Htext") as "Hj3e".
          iPoseProof (dki_42 with "Htext") as "Hj42".
          iPoseProof (dki_46 with "Htext") as "Hj46".
          (* +0x30 c.mv a4,s3 : n := 16 *)
          iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x30)) Ra4 Rs3 Ml
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj30").
          iIntros (CIDB1 HqB1) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (L1 := <[Regidx Ra4 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (Ml !!! Regidx Rs3))]> Ml).
          assert (HL1r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L1)
            by (rewrite /L1; apply dl_regs_caller; [exact Hcsa4 | exact HregsW]).
          assert (HL1a4 : L1 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64)).
          { rewrite /L1 upd_eq. rewrite Hm19 add_vec_zero_l. pcw. }
          assert (Hbb32 : add_vec_int (mword_of_int (DK + 0x30) : mword 64) 2
                          = mword_of_int (DK + 0x32)) by pcw.
          iEval (rewrite Hbb32) in "Hpc".
          (* +0x32 c.mv a3,s1 : off *)
          iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x32)) Ra3 Rs1 L1
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj32").
          iIntros (CIDB2 HqB2) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (L2 := <[Regidx Ra3 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (L1 !!! Regidx Rs1))]> L1).
          assert (HL2r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L2)
            by (rewrite /L2; apply dl_regs_caller; [exact Hcsa3 | exact HL1r]).
          assert (HL2a3 : L2 !!! Regidx Ra3
                          = (mword_of_int (Z.of_nat (16 * i)%nat) : mword 64)).
          { rewrite /L2 upd_eq.
            destruct HL1r as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
            rewrite D3. apply add_vec_zero_l. }
          assert (HL2a4 : L2 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64))
            by (rewrite /L2 upd_ne; [exact HL1a4 | nz]).
          assert (Hbb34 : add_vec_int (mword_of_int (DK + 0x32) : mword 64) 2
                          = mword_of_int (DK + 0x34)) by pcw.
          iEval (rewrite Hbb34) in "Hpc".
          (* +0x34 c.mv a2,s4 : &de *)
          iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x34)) Ra2 Rs4 L2
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj34").
          iIntros (CIDB3 HqB3) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (L3 := <[Regidx Ra2 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (L2 !!! Regidx Rs4))]> L2).
          assert (HL3r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L3)
            by (rewrite /L3; apply dl_regs_caller; [exact Hcsa2 | exact HL2r]).
          assert (HL3a2 : L3 !!! Regidx Ra2 = pa_stk sp0 10).
          { rewrite /L3 upd_eq.
            destruct HL2r as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
            rewrite D6. apply add_vec_zero_l. }
          assert (HL3a3 : L3 !!! Regidx Ra3
                          = (mword_of_int (Z.of_nat (16 * i)%nat) : mword 64))
            by (rewrite /L3 upd_ne; [exact HL2a3 | nz]).
          assert (HL3a4 : L3 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64))
            by (rewrite /L3 upd_ne; [exact HL2a4 | nz]).
          assert (Hbb36 : add_vec_int (mword_of_int (DK + 0x34) : mword 64) 2
                          = mword_of_int (DK + 0x36)) by pcw.
          iEval (rewrite Hbb36) in "Hpc".
          (* +0x36 c.li a1,0 : the KERNEL destination *)
          iApply (wp_cli_s_sconf (mword_of_int (DK + 0x36)) Ra1
                    (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) L3
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                    with "Hcg Hpc Hj36").
          iIntros (CIDB4 HqB4) "Hcg Hpc".
          set (L4 := <[Regidx Ra1 := regval_into_reg
                        (mword_of_int 0 : mword 64)]> L3).
          assert (HL4r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L4)
            by (rewrite /L4; apply dl_regs_caller; [exact Hcsa1 | exact HL3r]).
          assert (HL4a1 : L4 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
            by (rewrite /L4; apply upd_eq).
          assert (HL4a2 : L4 !!! Regidx Ra2 = pa_stk sp0 10)
            by (rewrite /L4 upd_ne; [exact HL3a2 | nz]).
          assert (HL4a3 : L4 !!! Regidx Ra3
                          = (mword_of_int (Z.of_nat (16 * i)%nat) : mword 64))
            by (rewrite /L4 upd_ne; [exact HL3a3 | nz]).
          assert (HL4a4 : L4 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64))
            by (rewrite /L4 upd_ne; [exact HL3a4 | nz]).
          assert (Hbb38 : add_vec_int (mword_of_int (DK + 0x36) : mword 64) 2
                          = mword_of_int (DK + 0x38)) by pcw.
          iEval (rewrite Hbb38) in "Hpc".
          (* +0x38 c.mv a0,s2 : dp *)
          iApply (wp_cmv_s_sconf (mword_of_int (DK + 0x38)) Ra0 Rs2 L4
                    (K - 10)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj38").
          iIntros (CIDB5 HqB5) "Hcg Hpc". iEval (rgne) in "Hcg".
          set (L5 := <[Regidx Ra0 := regval_into_reg
                        (add_vec (zero_reg : mword 64) (L4 !!! Regidx Rs2))]> L4).
          assert (HL5r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L5)
            by (rewrite /L5; apply dl_regs_caller; [exact Hcsa0 | exact HL4r]).
          assert (HL5a0 : L5 !!! Regidx Ra0 = ip).
          { rewrite /L5 upd_eq.
            destruct HL4r as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
            rewrite D4. apply add_vec_zero_l. }
          assert (HL5a1 : L5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
            by (rewrite /L5 upd_ne; [exact HL4a1 | nz]).
          assert (HL5a2 : L5 !!! Regidx Ra2 = pa_stk sp0 10)
            by (rewrite /L5 upd_ne; [exact HL4a2 | nz]).
          assert (HL5a3 : L5 !!! Regidx Ra3
                          = (mword_of_int (Z.of_nat (16 * i)%nat) : mword 64))
            by (rewrite /L5 upd_ne; [exact HL4a3 | nz]).
          assert (HL5a4 : L5 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64))
            by (rewrite /L5 upd_ne; [exact HL4a4 | nz]).
          assert (Hbb3a : add_vec_int (mword_of_int (DK + 0x38) : mword 64) 2
                          = mword_of_int (DK + 0x3a)) by pcw.
          iEval (rewrite Hbb3a) in "Hpc".
          (* +0x3a jal ra,readi *)
          assert (Htgtrd : add_vec (mword_of_int (DK + 0x3a) : mword 64)
                    (sign_extend' 64 (mword_of_int 2096078 : mword 21))
                    = mword_of_int KernelSyms.readi) by pcw.
          iApply (wp_jal_s_sconf (mword_of_int (DK + 0x3a)) Rra
                    (mword_of_int 2096078 : mword 21) L5 (K - 10)%nat b
                    ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hj3a").
          iIntros (CIDB6 HqB6) "Hcg Hpc".
          iEval (rewrite Htgtrd) in "Hpc".
          set (L6 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (DK + 0x3a) : mword 64) 4)]> L5).
          assert (HL6r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat L6)
            by (rewrite /L6; apply dl_regs_caller; [exact Hcsra | exact HL5r]).
          assert (HL6a0 : L6 !!! Regidx Ra0 = ip)
            by (rewrite /L6 upd_ne; [exact HL5a0 | nz]).
          assert (HL6a1 : L6 !!! Regidx Ra1 = (mword_of_int 0 : mword 64))
            by (rewrite /L6 upd_ne; [exact HL5a1 | nz]).
          assert (HL6a2 : L6 !!! Regidx Ra2 = pa_stk sp0 10)
            by (rewrite /L6 upd_ne; [exact HL5a2 | nz]).
          assert (HL6a3 : L6 !!! Regidx Ra3
                          = (mword_of_int (Z.of_nat (16 * i)%nat) : mword 64))
            by (rewrite /L6 upd_ne; [exact HL5a3 | nz]).
          assert (HL6a4 : L6 !!! Regidx Ra4
                          = (mword_of_int (Z.of_nat 16%nat) : mword 64))
            by (rewrite /L6 upd_ne; [exact HL5a4 | nz]).
          assert (HL6ra : L6 !!! Regidx Rra
                          = add_vec_int (mword_of_int (DK + 0x3a) : mword 64) 4)
            by (rewrite /L6; apply upd_eq).
          iAssert (([∗ list] ii ∈ seq 0 16,
                      pa_add (L6 !!! Regidx Ra2 : mword 64) ii ↦ₘ dol ii)
                   ∗ p_pid (proc_addr j) ↦₄{dq} pidv)%I
            with "[Hde Hppid]" as "Hdst".
          { iEval (rewrite HL6a2). iFrame. }
          iDestruct (cpu_own_transport CIDl CIDB6 0%nat eb (proc_addr j) C b
                       ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
          iApply (RD.wp_readi_sconf gs j gl gu gd gk pd pav pu bn gfs ga gf
                    cov logstart dev ip bm data dn
                    false (16 * i)%nat 16%nat dol dl_dummyV
                    pidv dq dqd L6 (K - 10)%nat eb C b
                    ltac:(exact HKrd) Hlg Hbmwf Hbmcov Hszb
                    ltac:(change (Z.of_nat 16%nat) with 16; exact Hoff31)
                    Hj Hgs HL6a0
                    ltac:(cbn [negb]; rewrite HL6a1 dlk_zero_moi;
                          exact (eq_vec_refl _))
                    HL6a3 HL6a4 Heb
                    with "Hcg Hcnt Htext Hpc Hpanic Hbio Hkenv Hidev Hmeta Hmap
                          Hblocks Hdst Hprocs Hdev Hgeom Hdlk Hbs1 [-]").
          iIntros (CIDrd Hsrd mrd tot P')
            "%Hcsrd %Hupt %Htotcl %Hrdret Hcg Hcnt Hpc Hidev Hmeta Hmap Hblocks
             Hdst2 Hbs1".
          iAssert (([∗ list] ii ∈ seq 0 16,
                      pa_add (L6 !!! Regidx Ra2 : mword 64) ii
                        ↦ₘ rd_delivered data dol (16 * i) tot ii)
                   ∗ p_pid (proc_addr j) ↦₄{dq} pidv)%I
            with "[Hdst2]" as "[Hde Hppid]".
          { iExact "Hdst2". }
          destruct Hrdret as [[_ Hbad] | [Hra0rd Hteq]]; [discriminate |].
          assert (Hrdr : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat mrd)
            by exact (dl_regs_cs m sp0 ip nb _ (16 * i)%nat L6 mrd Hcsrd HL6r).
          pose proof Hrdr as HrdrW.
          destruct Hrdr as (Hr2 & Hr8 & Hr9 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22
                           & Hrthr).
          assert (Hpcrd : ret_pc (L6 !!! Regidx Rra : mword 64)
                          = mword_of_int (DK + 0x3e)) by (rewrite HL6ra; pcw).
          iEval (rewrite Hpcrd) in "Hpc".
          (* ============ §15(b): THE READ MAY BE SHORT =================
             dirlink's OWN short-write arm is what can leave a directory
             non-granular, so this is not a hypothetical: at [i = nrec]
             with [16*nrec < size] readi returns fewer than sixteen bytes
             and the [bne a0,s3] at +0x3e is TAKEN into
             panic("dirlink read") at +0x60. *)
          destruct (decide (Z.to_nat (bv_unsigned (di_size dn)) < 16 * i + 16)%nat)
            as [Hshort | Hfull].
          { (* -------------- THE SHORT READ: dirlink DIVERGES ---------- *)
            assert (Htlt : (tot < 16)%nat).
            { rewrite Hteq (dlk_rd_clamp_short (di_size dn) i Hshort).
              exact (dlk_short_lt16 (bv_unsigned (di_size dn)) i Hsznn Hilt16
                       Hshort). }
            iPoseProof (dki_60 with "Htext") as "Hj60".
            iPoseProof (dki_64 with "Htext") as "Hj64".
            iPoseProof (dki_68 with "Htext") as "Hj68".
            assert (Htk60 : add_vec (mword_of_int (DK + 0x3e) : mword 64)
                      (sign_extend' 64 (mword_of_int 34 : mword 13))
                    = mword_of_int (DK + 0x60)) by pcw.
            (* +0x3e bne a0,s3 : TAKEN *)
            iApply (wp_bne_taken_s_sconf (mword_of_int (DK + 0x3e))
                      (mword_of_int 34 : mword 13) Rs3 Ra0 mrd (K - 10)%nat b
                      ltac:(nz) ltac:(nz)
                      ltac:(rgne; rgne; rewrite Hra0rd Hr19;
                            exact (dlk_neq16 tot Htlt))
                      ltac:(rewrite Htk60; vm_compute; reflexivity)
                      with "Hcg Hpc Hj3e").
            iNext. iIntros (CIDpa1 Hqpa1) "Hcg Hpc".
            iEval (rewrite Htk60) in "Hpc".
            (* +0x60 auipc a0,0x4 *)
            iApply (wp_auipc_s_sconf (mword_of_int (DK + 0x60)) Ra0
                      (mword_of_int 4 : mword 20) mrd (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj60").
            iIntros (CIDpa2 Hqpa2) "Hcg Hpc".
            set (PB1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (mword_of_int (DK + 0x60) : mword 64)
                              (auipc_off (mword_of_int 4 : mword 20)))]> mrd).
            assert (Hpp64 : add_vec_int (mword_of_int (DK + 0x60) : mword 64) 4
                            = mword_of_int (DK + 0x64)) by pcw.
            iEval (rewrite Hpp64) in "Hpc".
            (* +0x64 addi a0,a0,2818 *)
            iApply (wp_addi4_s_sconf (mword_of_int (DK + 0x64)) Ra0 Ra0
                      (mword_of_int 2818 : mword 12) PB1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj64").
            iIntros (CIDpa3 Hqpa3) "Hcg Hpc".
            set (PB2 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (rget PB1 Ra0)
                              (sign_extend' 64 (mword_of_int 2818 : mword 12)))]> PB1).
            assert (Hpp68 : add_vec_int (mword_of_int (DK + 0x64) : mword 64) 4
                            = mword_of_int (DK + 0x68)) by pcw.
            iEval (rewrite Hpp68) in "Hpc".
            (* +0x68 jal ra,panic -- and panic() never returns *)
            iApply (wp_jal_s_sconf (mword_of_int (DK + 0x68)) Rra
                      (mword_of_int 2084440 : mword 21) PB2 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc Hj68").
            iIntros (CIDpa4 Hqpa4) "Hcg Hpc".
            assert (Htgtpn : add_vec (mword_of_int (DK + 0x68) : mword 64)
                               (sign_extend' 64 (mword_of_int 2084440 : mword 21))
                             = mword_of_int KernelSyms.panic) by pcw.
            iEval (rewrite Htgtpn) in "Hpc".
            iPoseProof (panic_wp_any_at CIDpa4 with "Hpanic") as "Hpan".
            iApply ("Hpan" with "Htext Hpc Hcg"). }
          (* -------------- THE FULL READ: exactly as before ----------- *)
          assert (Hclamp : rd_clamp (di_size dn) (16 * i) 16 = 16%nat)
            by exact (dlk_rd_clamp_full' (di_size dn) i Hfull).
          assert (Htot : tot = 16%nat) by (rewrite Hteq; exact Hclamp).
          assert (Hilt : (i < nrec)%nat)
            by exact (dlk_full_lt (bv_unsigned (di_size dn)) i Hsznn Hfull).
          assert (Ha0rd : mrd !!! Regidx Ra0 = (mword_of_int 16 : mword 64))
            by (rewrite Hra0rd Htot; pcw).
          (* the delivered bytes ARE the file's bytes, split into the two views *)
          iEval (rewrite HL6a2 Htot
                   (bb_ext (pa_stk sp0 10) 16
                      (fun jj => rd_delivered data dol (16 * i) 16 jj)
                      (fun jj => file_byte data (16 * i + jj)%nat)
                      (fun jj Hjj => dlk_rd_delivered data dol i jj Hjj))
                   (dl_de_view data i (pa_stk sp0 10) (dlk_align_8_2 _ Hal10)))
            in "Hde".
          iDestruct "Hde" as "[Hdehi Hdenm]".
          (* +0x3e bne a0,s3 : panic("dirlink read") is DEAD *)
          iApply (wp_bne_fall_s_sconf (mword_of_int (DK + 0x3e))
                    (mword_of_int 34 : mword 13) Rs3 Ra0 mrd (K - 10)%nat b
                    ltac:(nz) ltac:(nz)
                    ltac:(rgne; rgne; rewrite Ha0rd Hr19; apply dlk_neq_refl)
                    with "Hcg Hpc Hj3e").
          iIntros (CIDB7 HqB7) "Hcg Hpc".
          assert (Hbb42 : add_vec_int (mword_of_int (DK + 0x3e) : mword 64) 4
                          = mword_of_int (DK + 0x42)) by pcw.
          iEval (rewrite Hbb42) in "Hpc".
          (* +0x42 lhu a5,-80(s0) : de.inum *)
          iApply (wp_lhu_s_sconf (mword_of_int (DK + 0x42)) Ra5 Rs0
                    (mword_of_int 4016 : mword 12) mrd (K - 10)%nat
                    (dir_inum data i) b ltac:(nz) ltac:(rdok)
                    with "Hcg Hpc Hj42 [Hdehi]").
          { iEval (rgne; rewrite Hr8 (dl_de_addr sp0)). iExact "Hdehi". }
          iIntros (CIDB8 HqB8) "Hcg Hpc Hdehi".
          iEval (rgne; rewrite Hr8 (dl_de_addr sp0)) in "Hdehi".
          set (N1 := <[Regidx Ra5 := regval_into_reg
                        (zero_extend' 64 (dir_inum data i : mword 16)
                         : mword 64)]> mrd).
          assert (HN1r : dl_regs m sp0 ip nb
                           (zero_extend' 64 (inum : mword 16) : mword 64)
                           (16 * i)%nat N1)
            by (rewrite /N1; apply dl_regs_caller; [exact Hcsa5 | exact HrdrW]).
          assert (HN1a5 : N1 !!! Regidx Ra5
                          = (zero_extend' 64 (dir_inum data i : mword 16)
                             : mword 64))
            by (rewrite /N1; apply upd_eq).
          assert (Hbb46 : add_vec_int (mword_of_int (DK + 0x42) : mword 64) 4
                          = mword_of_int (DK + 0x46)) by pcw.
          iEval (rewrite Hbb46) in "Hpc".
          assert (Htgt6c : add_vec (mword_of_int (DK + 0x46) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
                    = mword_of_int (DK + 0x6c)) by pcw.
          destruct (decide (dir_inum data i = bv_0 16)) as [Hfree | Hlive].
          * (* ---- the record is FREE: break to +0x6c ---- *)
            iApply (wp_cbeqz_taken_s_sconf (mword_of_int (DK + 0x46))
                      (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      N1 (K - 10)%nat b
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HN1a5; exact (dlk_eqz_true _ Hfree))
                      ltac:(rewrite Htgt6c; vm_compute; reflexivity)
                      with "Hcg Hpc Hj46").
            iNext. iIntros (CIDB9 HqB9) "Hcg Hpc".
            iEval (rewrite Htgt6c) in "Hpc".
            iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj
                       ↦ₘ file_byte data (16 * i + jj)%nat)%I
              with "[Hdehi Hdenm]" as "Hde".
            { iEval (rewrite (dl_de_view data i (pa_stk sp0 10)
                                (dlk_align_8_2 _ Hal10))).
              iSplitL "Hdehi"; [iExact "Hdehi" | iExact "Hdenm"]. }
            assert (Hk0e : k0 = i)
              by exact (dir_slot_char data nrec i (Nat.lt_le_incl _ _ Hilt)
                          (proj1 (dir_free_first_None data i) Hffn)
                          (or_intror Hfree)).
            iPoseProof (dki_6c with "Htext") as "Hj6c".
            iPoseProof (dki_6e with "Htext") as "Hj6e".
            (* +0x6c c.ldsp s3,40(sp) *)
            assert (HN1sp : N1 !!! Regidx csp_rs1 = pa_stk sp0 10).
            { destruct HN1r as (D1 & _). exact D1. }
            assert (Hg5 : add_vec (N1 !!! Regidx csp_rs1)
                            (zero_extend' 64
                               (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                          = pa_stk sp0 5) by (rewrite HN1sp; apply dl_frm5).
            iEval (rewrite -Hg5) in "Hb5".
            iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x6c))
                      (mword_of_int 5 : mword 6) Rs3 N1 (K - 10)%nat
                      (m !!! Regidx Rs3 : mword 64) b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6c Hb5").
            iIntros (CIDB10 HqB10) "Hcg Hpc Hb5".
            iEval (rewrite Hg5) in "Hb5".
            set (N2 := <[Regidx Rs3 := regval_into_reg
                          (m !!! Regidx Rs3 : mword 64)]> N1).
            assert (HN2sp : N2 !!! Regidx csp_rs1 = pa_stk sp0 10)
              by (rewrite /N2 upd_ne; [exact HN1sp | nz]).
            assert (Hbb6e : add_vec_int (mword_of_int (DK + 0x6c) : mword 64) 2
                            = mword_of_int (DK + 0x6e)) by pcw.
            iEval (rewrite Hbb6e) in "Hpc".
            (* +0x6e c.ldsp s4,32(sp) *)
            assert (Hg6 : add_vec (N2 !!! Regidx csp_rs1)
                            (zero_extend' 64
                               (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                          = pa_stk sp0 6) by (rewrite HN2sp; apply dl_frm6).
            iEval (rewrite -Hg6) in "Hb6".
            iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x6e))
                      (mword_of_int 4 : mword 6) Rs4 N2 (K - 10)%nat
                      (m !!! Regidx Rs4 : mword 64) b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj6e Hb6").
            iIntros (CIDB11 HqB11) "Hcg Hpc Hb6".
            iEval (rewrite Hg6) in "Hb6".
            assert (HN3p : dl_pregs m sp0 ip nb
                             (zero_extend' 64 (inum : mword 16) : mword 64)
                             (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64)
                             (<[Regidx Rs4 := regval_into_reg
                                  (m !!! Regidx Rs4 : mword 64)]>
                                (<[Regidx Rs3 := regval_into_reg
                                     (m !!! Regidx Rs3 : mword 64)]> N1))).
            { rewrite Hk0e.
              exact (dl_pregs_of_regs m sp0 ip nb _ (16 * i)%nat N1 _ _
                       eq_refl eq_refl HN1r). }
            assert (Hbb70 : add_vec_int (mword_of_int (DK + 0x6e) : mword 64) 2
                            = mword_of_int (DK + 0x70)) by pcw.
            iEval (rewrite Hbb70) in "Hpc".
            iDestruct (dl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
              [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
            iDestruct (cpu_own_transport CIDrd CIDB11 0%nat eb (proc_addr j) C b
                         ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
            iPoseProof ("Hafter" $! CIDB11) as "Ha".
            iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
            iApply ("Ha" $! _ (fun jj => file_byte data (16 * i + jj)%nat)
                      (m !!! Regidx Rs3 : mword 64) (m !!! Regidx Rs4 : mword 64)
                      with
                      "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde
                       Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr
                       Hdat Hppid Hbsl Hislot Hop Hqc").
            { exact HN3p. }
          * (* ---- the record is LIVE: advance ---- *)
            iPoseProof (dki_48 with "Htext") as "Hj48".
            iPoseProof (dki_4a with "Htext") as "Hj4a".
            iPoseProof (dki_4e with "Htext") as "Hj4e".
            iApply (wp_cbeqz_fall_s_sconf (mword_of_int (DK + 0x46))
                      (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                      N1 (K - 10)%nat b
                      ltac:(vm_compute; reflexivity) ltac:(nz)
                      ltac:(rgne; rewrite HN1a5; exact (dlk_eqz_false _ Hlive))
                      with "Hcg Hpc Hj46").
            iIntros (CIDB9 HqB9) "Hcg Hpc".
            assert (Hbb48 : add_vec_int (mword_of_int (DK + 0x46) : mword 64) 2
                            = mword_of_int (DK + 0x48)) by pcw.
            iEval (rewrite Hbb48) in "Hpc".
            iAssert ([∗ list] jj ∈ seq 0 16, pa_add (pa_stk sp0 10) jj
                       ↦ₘ file_byte data (16 * i + jj)%nat)%I
              with "[Hdehi Hdenm]" as "Hde".
            { iEval (rewrite (dl_de_view data i (pa_stk sp0 10)
                                (dlk_align_8_2 _ Hal10))).
              iSplitL "Hdehi"; [iExact "Hdehi" | iExact "Hdenm"]. }
            assert (Hffs : dir_free_first data (S i) = None)
              by exact (dir_free_first_step_live data i Hffn Hlive).
            (* +0x48 c.addiw s1,s1,16 *)
            assert (Haddiw : (sign_extend' 64 (subrange_vec_dec
                       (add_vec (N1 !!! Regidx Rs1 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 12 (mword_of_int 16 : mword 6))))
                       31 0) : mword 64)
                     = (mword_of_int (Z.of_nat (16 * S i)%nat) : mword 64)).
            { destruct HN1r as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
              rewrite D3 (dlk_addiw16 (16 * i) Hoff31) (dl_si i). reflexivity. }
            iApply (wp_caddiw_s_sconf (mword_of_int (DK + 0x48)) Rs1
                      (mword_of_int 16 : mword 6) N1 (K - 10)%nat b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj48").
            iIntros (CIDB10 HqB10) "Hcg Hpc".
            iEval (rgne; rewrite Haddiw) in "Hcg".
            set (N2 := <[Regidx Rs1 := regval_into_reg
                          (mword_of_int (Z.of_nat (16 * S i)%nat)
                           : mword 64)]> N1).
            assert (HN2r : dl_regs m sp0 ip nb
                             (zero_extend' 64 (inum : mword 16) : mword 64)
                             (16 * S i)%nat N2)
              by exact (dl_regs_s1 m sp0 ip nb _ (16 * i)%nat (16 * S i)%nat N1 _
                          eq_refl HN1r).
            assert (HN2s1 : N2 !!! Regidx Rs1
                            = (mword_of_int (Z.of_nat (16 * S i)%nat) : mword 64))
              by (rewrite /N2; apply upd_eq).
            assert (HN2s2 : N2 !!! Regidx Rs2 = ip).
            { destruct HN2r as (D1 & D2 & D3 & D4 & _). exact D4. }
            assert (Hbb4a : add_vec_int (mword_of_int (DK + 0x48) : mword 64) 2
                            = mword_of_int (DK + 0x4a)) by pcw.
            iEval (rewrite Hbb4a) in "Hpc".
            (* +0x4a lw a5,76(s2) : the size is re-read every iteration *)
            iDestruct "Hmeta" as "(Hity & Himaj & Himin & Hinl & Hisz)".
            iEval (rewrite /i_size) in "Hisz".
            iApply (wp_lw_s_sconf (mword_of_int (DK + 0x4a)) Ra5 Rs2
                      (mword_of_int 76 : mword 12) N2 (K - 10)%nat
                      (di_size dn : mword 32) b
                      ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj4a [Hisz]").
            { iEval (rgne; rewrite HN2s2). iExact "Hisz". }
            iIntros (CIDB11 HqB11) "Hcg Hpc Hisz".
            iEval (rgne; rewrite HN2s2) in "Hisz".
            iAssert (inode_meta ip dn) with "[Hity Himaj Himin Hinl Hisz]"
              as "Hmeta".
            { rewrite /inode_meta /i_size. iFrame. }
            set (N3 := <[Regidx Ra5 := regval_into_reg
                          (sign_extend' 64 (di_size dn : mword 32)
                           : mword 64)]> N2).
            assert (HN3r : dl_regs m sp0 ip nb
                             (zero_extend' 64 (inum : mword 16) : mword 64)
                             (16 * S i)%nat N3)
              by (rewrite /N3; apply dl_regs_caller; [exact Hcsa5 | exact HN2r]).
            assert (HN3s1 : N3 !!! Regidx Rs1
                            = (mword_of_int (Z.of_nat (16 * S i)%nat) : mword 64))
              by (rewrite /N3 upd_ne; [exact HN2s1 | nz]).
            assert (HN3a5 : N3 !!! Regidx Ra5
                            = (mword_of_int (bv_unsigned (di_size dn))
                               : mword 64)).
            { rewrite /N3 upd_eq. exact (dlk_sext32_moi (di_size dn) Hsz31). }
            assert (Hbb4e : add_vec_int (mword_of_int (DK + 0x4a) : mword 64) 4
                            = mword_of_int (DK + 0x4e)) by pcw.
            iEval (rewrite Hbb4e) in "Hpc".
            (* +0x4e bltu s1,a5 : one more record? *)
            assert (Hsi31 : Z.of_nat (16 * S i)%nat < 2 ^ 31)
              by (rewrite (dl_sioff i); exact Hoff31).
            assert (Hcmp : zopz0zI_u (N3 !!! Regidx Rs1 : mword 64)
                             (N3 !!! Regidx Ra5 : mword 64)
                           = Z.ltb (Z.of_nat (16 * S i)%nat)
                               (bv_unsigned (di_size dn))).
            { rewrite HN3s1 HN3a5.
              exact (dl_bltu _ _ (dl_b64 _ (Nat2Z.is_nonneg _) Hsi31)
                       (dl_b64 _ Hsznn Hsz31)). }
            assert (Htgt30 : add_vec (mword_of_int (DK + 0x4e) : mword 64)
                      (sign_extend' 64 (mword_of_int 8162 : mword 13))
                      = mword_of_int (DK + 0x30)) by pcw.
            destruct (Z.ltb (Z.of_nat (16 * S i)%nat) (bv_unsigned (di_size dn)))
              eqn:Hge.
            -- (* ---- another record: back to +0x30 with i+1 ---- *)
               iApply (wp_bltu_taken_s_sconf (mword_of_int (DK + 0x4e))
                         (mword_of_int 8162 : mword 13) Ra5 Rs1 N3 (K - 10)%nat b
                         ltac:(nz) ltac:(nz)
                         ltac:(rgne; rgne; rewrite Hcmp;
                               first [ exact Hge | reflexivity ])
                         ltac:(rewrite Htgt30; vm_compute; reflexivity)
                         with "Hcg Hpc Hj4e").
               iNext. iIntros (CIDB12 HqB12) "Hcg Hpc".
               iEval (rewrite Htgt30) in "Hpc".
               assert (Hgtc : Z.of_nat (S i) * 16 < bv_unsigned (di_size dn)).
               { rewrite -(dl_offmul (S i)). apply Z.ltb_lt. exact Hge. }
               iDestruct (cpu_own_transport CIDrd CIDB12 0%nat eb (proc_addr j) C b
                            ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
               iSpecialize ("IHf" $! CIDB12 with "[%]"); [wp_next_chain |].
               iApply ("IHf" $! (S i) N3 (fun jj => file_byte data (16 * i + jj)%nat)
                         with
                         "[%] [%] [%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6
                          Hb7 Hb8 Hde Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi
                          Hsbs Hsbb Hbmr Hdat Hppid Hbs1 Hbs2 Hislot Hop Hqc").
               { exact (dl_fuelS (S nrec) i fuel Hfuel). }
               { exact Hgtc. }
               { exact Hffs. }
               { exact HN3r. }
            -- (* ---- the scan is exhausted: [S i = nrec] ---- *)
               iApply (wp_bltu_fall_s_sconf (mword_of_int (DK + 0x4e))
                         (mword_of_int 8162 : mword 13) Ra5 Rs1 N3 (K - 10)%nat b
                         ltac:(nz) ltac:(nz)
                         ltac:(rgne; rgne; rewrite Hcmp;
                               first [ exact Hge | reflexivity ])
                         with "Hcg Hpc Hj4e").
               iIntros (CIDB12 HqB12) "Hcg Hpc".
               assert (Hbb52 : add_vec_int (mword_of_int (DK + 0x4e) : mword 64) 4
                               = mword_of_int (DK + 0x52)) by pcw.
               iEval (rewrite Hbb52) in "Hpc".
               assert (Hle : bv_unsigned (di_size dn)
                             <= Z.of_nat (16 * S i)%nat)
                 by (apply Z.ltb_ge; exact Hge).
               assert (Hnle : (nrec <= S i)%nat).
               { destruct (Nat.le_gt_cases nrec (S i)) as [Hx | Hx];
                   [exact Hx | exfalso].
                 rewrite (dl_offmul (S i)) in Hle.
                 exact (dlk_nle_of_ge (bv_unsigned (di_size dn)) (S i)
                          Hsznn Hle Hx). }
               assert (Hsieq : S i = nrec) by exact (dl_eqn i nrec Hilt Hnle).
               assert (Hffnn : dir_free_first data nrec = None)
                 by (rewrite -Hsieq; exact Hffs).
               assert (Hk0e : k0 = nrec)
                 by exact (dir_slot_char data nrec nrec (Nat.le_refl nrec)
                             (proj1 (dir_free_first_None data nrec) Hffnn)
                             (or_introl eq_refl)).
               iPoseProof (dki_52 with "Htext") as "Hj52".
               iPoseProof (dki_54 with "Htext") as "Hj54".
               iPoseProof (dki_56 with "Htext") as "Hj56".
               assert (HN3sp : N3 !!! Regidx csp_rs1 = pa_stk sp0 10).
               { destruct HN3r as (D1 & _). exact D1. }
               (* +0x52 c.ldsp s3,40(sp) *)
               assert (Hg5 : add_vec (N3 !!! Regidx csp_rs1)
                               (zero_extend' 64
                                  (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                             = pa_stk sp0 5) by (rewrite HN3sp; apply dl_frm5).
               iEval (rewrite -Hg5) in "Hb5".
               iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x52))
                         (mword_of_int 5 : mword 6) Rs3 N3 (K - 10)%nat
                         (m !!! Regidx Rs3 : mword 64) b
                         ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj52 Hb5").
               iIntros (CIDB13 HqB13) "Hcg Hpc Hb5".
               iEval (rewrite Hg5) in "Hb5".
               set (N4 := <[Regidx Rs3 := regval_into_reg
                             (m !!! Regidx Rs3 : mword 64)]> N3).
               assert (HN4sp : N4 !!! Regidx csp_rs1 = pa_stk sp0 10)
                 by (rewrite /N4 upd_ne; [exact HN3sp | nz]).
               assert (Hbb54 : add_vec_int (mword_of_int (DK + 0x52) : mword 64) 2
                               = mword_of_int (DK + 0x54)) by pcw.
               iEval (rewrite Hbb54) in "Hpc".
               (* +0x54 c.ldsp s4,32(sp) *)
               assert (Hg6 : add_vec (N4 !!! Regidx csp_rs1)
                               (zero_extend' 64
                                  (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                             = pa_stk sp0 6) by (rewrite HN4sp; apply dl_frm6).
               iEval (rewrite -Hg6) in "Hb6".
               iApply (wp_cldsp_s_sconf (mword_of_int (DK + 0x54))
                         (mword_of_int 4 : mword 6) Rs4 N4 (K - 10)%nat
                         (m !!! Regidx Rs4 : mword 64) b
                         ltac:(nz) ltac:(rdok) with "Hcg Hpc Hj54 Hb6").
               iIntros (CIDB14 HqB14) "Hcg Hpc Hb6".
               iEval (rewrite Hg6) in "Hb6".
               assert (HN5p : dl_pregs m sp0 ip nb
                                (zero_extend' 64 (inum : mword 16) : mword 64)
                                (mword_of_int (Z.of_nat (16 * k0)%nat) : mword 64)
                                (<[Regidx Rs4 := regval_into_reg
                                     (m !!! Regidx Rs4 : mword 64)]>
                                   (<[Regidx Rs3 := regval_into_reg
                                        (m !!! Regidx Rs3 : mword 64)]> N3))).
               { rewrite Hk0e -Hsieq.
                 exact (dl_pregs_of_regs m sp0 ip nb _ (16 * S i)%nat N3 _ _
                          eq_refl eq_refl HN3r). }
               assert (Hbb56 : add_vec_int (mword_of_int (DK + 0x54) : mword 64) 2
                               = mword_of_int (DK + 0x56)) by pcw.
               iEval (rewrite Hbb56) in "Hpc".
               (* +0x56 c.j +0x70 *)
               assert (Htgt70b : add_vec (mword_of_int (DK + 0x56) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 13 : mword 11) ('b"0"))))
                         = mword_of_int (DK + 0x70)) by pcw.
               iApply (wp_cj_s_sconf (mword_of_int (DK + 0x56))
                         (sign_extend' 21
                            (concat_vec (mword_of_int 13 : mword 11) ('b"0")))
                         (<[Regidx Rs4 := regval_into_reg
                              (m !!! Regidx Rs4 : mword 64)]>
                            (<[Regidx Rs3 := regval_into_reg
                                 (m !!! Regidx Rs3 : mword 64)]> N3))
                         (K - 10)%nat b
                         ltac:(rewrite Htgt70b; vm_compute; reflexivity)
                         with "Hcg Hpc Hj56").
               iIntros (CIDB15 HqB15). iNext. iIntros "Hcg Hpc".
               iEval (rewrite Htgt70b) in "Hpc".
               iDestruct (dl_bs3 bn with "[Hbs1 Hbs2]") as "Hbsl";
                 [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
               iDestruct (cpu_own_transport CIDrd CIDB15 0%nat eb (proc_addr j) C b
                            ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
               iPoseProof ("Hafter" $! CIDB15) as "Ha".
               iSpecialize ("Ha" with "[%]"); [wp_next_chain |].
               iApply ("Ha" $! _ (fun jj => file_byte data (16 * i + jj)%nat)
                         (m !!! Regidx Rs3 : mword 64)
                         (m !!! Regidx Rs4 : mword 64) with
                         "[%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hde
                          Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr
                          Hdat Hppid Hbsl Hislot Hop Hqc").
               { exact HN5p. } }
        (* ---------- the loop is entered at +0x30 with off = 0 ---------- *)
        iDestruct (cpu_own_transport CIDdl CID21 0%nat eb (proc_addr j) C b
                     ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
        iSpecialize ("Hloop" $! (S nrec) CID21 with "[%]"); [wp_next_chain |].
        iApply ("Hloop" $! 0%nat Q4 dolds0 with
                  "[%] [%] [%] [%] Hcg Hcnt Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8
                   Hde Hidev Hiinum Hmeta Hmap Hblocks Hnm Hsbi Hsbs Hsbb Hbmr
                   Hdat Hppid Hbs1 Hbs2 Hislot Hop Hcont").
        { exact (dl_fuelinit (S nrec)). }
        { exact (dlk_off0_lt (bv_unsigned (di_size dn)) Hsznn Hszn). }
        { unfold dir_free_first. apply dfirst_0. }
        { exact HQ4r. }
  Qed.

End ProofDirlinkMain.

End DirlinkProof.

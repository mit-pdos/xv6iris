(* ProofFilestatParts.v -- the STAT BUFFER, carved out of filestat's own frame
   and handed to copyout as a byte run.

   filestat's [struct stat st] is a 24-byte local at [s0-72] = [sp+8] in an
   80-byte (10-slot) frame, i.e. frame slots 9, 8 and 7:

     pa_stk sp0 9 = st + 0    st->dev  @0 (4)   st->ino   @4  (4)
     pa_stk sp0 8 = st + 8    st->type @8 (2)   st->nlink @10 (2)   HOLE @12 (4)
     pa_stk sp0 7 = st + 16   st->size @16 (8)

   Three resources have to be the same bytes in turn, and this file is the two
   conversions between them:

   * [StackOwn.stack_own] hands the frame out as 8-byte WORDS with existential
     contents.  [StackBytes.slots3_bytes_own] already turns three of them into
     a 24-byte run ([bytes_own]); what is missing is the split of that run into
     the FIVE TYPED CELLS [SpecStati.stat_at] is stated over, plus the four
     loose bytes of the alignment hole.  That is [fst_bytes_stat] below.

   * [SpecCopyout] wants a NAMED byte run ([∗ list] j ∈ seq 0 24, pa_add st j
     ↦ₘ f j) at a single naming function.  After stati has run, four of the
     six pieces hold KNOWN values and the hole holds whatever the frame held,
     so the naming function is [stat_byte] and the conversion is
     [fst_stat_bytes].

   WHY THE HOLE NEEDS NO CONTRACT CLAUSE.  Bytes 12..15 are never written by
   stati ([SpecStati.v]'s header) and never mentioned by [stat_at].  They are
   filestat's OWN frame bytes, existential in [stack_own], and copyout's
   contract says nothing about what the user pages end up holding.  So they are
   carried through as an arbitrary [h : nat -> bv 8] and dropped at the
   epilogue; see SpecFilestat.v's header.

   THE ALIGNMENT DISCIPLINE (the [word_pointsto_split4] rule, InstrBytes.v):
   a typed cell carries its alignment fact and a byte run does not, so every
   alignment is taken out BEFORE a split and fed back at the rebuild.  All five
   of them come off the three SLOT alignments, which is why the two-byte
   analogues of [InstrBytes.aligned8_aligned4] had to be proved here. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import StackOwn StackBytes.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import SpecStati.
Require Import CodeFilestat.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(*  ADDRESS IDENTITIES: stat_at's 12-bit displacement form IS [pa_add]      *)
(* ---------------------------------------------------------------------- *)
(* [SpecStati] spells the five field addresses the way the [sw]/[sh]/[sd]
   that reach them encode -- [add_vec st (sign_extend' 64 (mword_of_int c))]
   -- so that a store's effective address unifies with the cell.  A BYTE RUN
   indexes with [pa_add].  These five lemmas are the bridge, and they are the
   [fr_frm*] pattern: peel the [add_vec], compare the two 64-bit constants by
   computation. *)
Lemma fst_pa_dev (X : mword 64) : st_dev X = pa_add X 0.
Proof.
  unfold st_dev, pa_add, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fst_pa_ino (X : mword 64) : st_ino X = pa_add X 4.
Proof.
  unfold st_ino, pa_add, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fst_pa_type (X : mword 64) : st_type X = pa_add X 8.
Proof.
  unfold st_type, pa_add, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fst_pa_nlink (X : mword 64) : st_nlink X = pa_add X 10.
Proof.
  unfold st_nlink, pa_add, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fst_pa_size (X : mword 64) : st_size X = pa_add X 16.
Proof.
  unfold st_size, pa_add, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE TWO-BYTE ALIGNMENTS, off an 8-byte one                             *)
(* ---------------------------------------------------------------------- *)
(* [InstrBytes] proves the 4-byte pair ([aligned8_aligned4] and
   [aligned8_aligned4_hi]); [st->type]@8 and [st->nlink]@10 need the 2-byte
   pair, at the SECOND slot's base and at that base + 2.  Its [z_rem8_*]
   helpers are [Local], so the arithmetic is redone here rather than exported
   -- three lines each. *)
Local Lemma fst_z_rem8_rem2 (u : Z) : (0 <= u)%Z -> Z.rem u 8 = 0%Z -> Z.rem u 2 = 0%Z.
Proof.
  intros H0 H8.
  rewrite (Z.rem_mod_nonneg u 8 H0 ltac:(lia)) in H8.
  rewrite (Z.rem_mod_nonneg u 2 H0 ltac:(lia)).
  apply Z.mod_divide in H8; [| lia]. apply Z.mod_divide; [lia|].
  destruct H8 as [kk Hk]. exists (4 * kk)%Z. lia.
Qed.

Local Lemma fst_z_rem8_rem2_hi (u : Z) :
  (0 <= u)%Z -> Z.rem u 8 = 0%Z -> Z.rem (u + 2) 2 = 0%Z.
Proof.
  intros H0 H8.
  rewrite (Z.rem_mod_nonneg u 8 H0 ltac:(lia)) in H8.
  rewrite (Z.rem_mod_nonneg (u + 2) 2 ltac:(lia) ltac:(lia)).
  apply Z.mod_divide in H8; [| lia]. apply Z.mod_divide; [lia|].
  destruct H8 as [kk Hk]. exists (4 * kk + 1)%Z. lia.
Qed.

(* [pa_add a 2]'s numeric value, given the 8-alignment that rules out wrap --
   the [InstrBytes.pa_add_4_unsigned] argument at offset 2. *)
Local Lemma fst_z_rem8_no_wrap (u : Z) :
  (0 <= u < 18446744073709551616)%Z -> Z.rem u 8 = 0%Z ->
  (u + 2 < 18446744073709551616)%Z.
Proof.
  intros [H0 Hh] H8.
  rewrite (Z.rem_mod_nonneg u 8 H0 ltac:(lia)) in H8.
  apply Z.mod_divide in H8; [| lia]. destruct H8 as [kk Hk]. lia.
Qed.

Lemma fst_pa_add_2_unsigned (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true ->
  bv_unsigned (pa_add a 2) = (bv_unsigned a + 2)%Z.
Proof.
  unfold is_aligned_paddr. rewrite uint_unsigned. intro H8.
  apply Z.eqb_eq in H8.
  pose proof (bv_unsigned_in_range _ a) as [Hlo Hhi].
  unfold bv_modulus in Hhi. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in Hhi.
  pose proof (fst_z_rem8_no_wrap _ (conj Hlo Hhi) H8) as Hnw.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (H2 : bv_unsigned (mword_of_int (Z.of_nat 2) : mword 64) = 2%Z)
    by (vm_compute; reflexivity).
  rewrite H2. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  split; [apply Z.add_nonneg_nonneg; [exact Hlo | discriminate] | exact Hnw].
Qed.

Lemma fst_aligned8_aligned2 (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true -> is_aligned_paddr (Physaddr a) 2 = true.
Proof.
  unfold is_aligned_paddr. rewrite !uint_unsigned.
  pose proof (bv_unsigned_in_range _ a) as [Hlo _].
  intro H8. apply Z.eqb_eq in H8. apply Z.eqb_eq.
  apply (fst_z_rem8_rem2 _ Hlo H8).
Qed.

Lemma fst_aligned8_aligned2_hi (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true ->
  is_aligned_paddr (Physaddr (pa_add a 2)) 2 = true.
Proof.
  intro H8. pose proof (fst_pa_add_2_unsigned a H8) as Hpa.
  revert H8. unfold is_aligned_paddr. rewrite !uint_unsigned. rewrite Hpa.
  pose proof (bv_unsigned_in_range _ a) as [Hlo _].
  intro H8. apply Z.eqb_eq in H8. apply Z.eqb_eq.
  apply (fst_z_rem8_rem2_hi _ Hlo H8).
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE NARROW ANALOGUES OF [StackBytes.bytes_own_slot]                    *)
(* ---------------------------------------------------------------------- *)
(* Four (resp. two) arbitrary owned bytes at an aligned address are a [↦₄]
   (resp. [↦₂]) cell holding SOME value -- which is all filestat needs going
   in, since stati overwrites every one of them.  [nth_byte_assemble_len] at
   width 32 and 16, exactly as [bytes_own_slot] uses it at 64. *)
Lemma fst_nth_byte4 (b0 b1 b2 b3 : bv 8) (j : nat) :
  (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (assemble_bytes [b0;b1;b2;b3]) : bv 32) j
  = [b0;b1;b2;b3] !!! j.
Proof. intro Hj. apply nth_byte_assemble_len; cbn [length]; lia. Qed.

Lemma fst_nth_byte2 (b0 b1 : bv 8) (j : nat) :
  (j < 2)%nat ->
  nth_byte (Z_to_bv 16 (assemble_bytes [b0;b1]) : bv 16) j = [b0;b1] !!! j.
Proof. intro Hj. apply nth_byte_assemble_len; cbn [length]; lia. Qed.

Section FilestatParts.
  Context `{!riscvGS Σ}.

  Lemma fst_bytes_w4 (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    bytes_own (DfracOwn 1) a 4 ⊢ ∃ w : bv 32, a ↦₄ w.
  Proof.
    intro Hal. rewrite /bytes_own. cbn [seq].
    iIntros "(H0 & H1 & H2 & H3 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2". iDestruct "H3" as (b3) "H3".
    set (W := Z_to_bv 32 (assemble_bytes [b0;b1;b2;b3]) : bv 32).
    assert (Hw0 : b0 = nth_byte W 0%nat) by (symmetry; apply fst_nth_byte4; lia).
    assert (Hw1 : b1 = nth_byte W 1%nat) by (symmetry; apply fst_nth_byte4; lia).
    assert (Hw2 : b2 = nth_byte W 2%nat) by (symmetry; apply fst_nth_byte4; lia).
    assert (Hw3 : b3 = nth_byte W 3%nat) by (symmetry; apply fst_nth_byte4; lia).
    iEval (rewrite Hw0) in "H0". iEval (rewrite Hw1) in "H1".
    iEval (rewrite Hw2) in "H2". iEval (rewrite Hw3) in "H3".
    iExists W. iApply word4_pointsto_intro; [exact Hal |].
    cbn [seq]. iFrame "H0 H1 H2 H3". done.
  Qed.

  Lemma fst_bytes_w2 (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    bytes_own (DfracOwn 1) a 2 ⊢ ∃ w : bv 16, a ↦₂ w.
  Proof.
    intro Hal. rewrite /bytes_own. cbn [seq].
    iIntros "(H0 & H1 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    set (W := Z_to_bv 16 (assemble_bytes [b0;b1]) : bv 16).
    assert (Hw0 : b0 = nth_byte W 0%nat) by (symmetry; apply fst_nth_byte2; lia).
    assert (Hw1 : b1 = nth_byte W 1%nat) by (symmetry; apply fst_nth_byte2; lia).
    iEval (rewrite Hw0) in "H0". iEval (rewrite Hw1) in "H1".
    iExists W. iApply word2_pointsto_intro; [exact Hal |].
    cbn [seq]. iFrame "H0 H1". done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  IN: three frame slots -> [stat_at] at arbitrary values + the hole   *)
  (* ------------------------------------------------------------------ *)
  (* The run is split 4/4/2/2/4/8.  Note the two 8-aligned interior points:
     [st+8] and [st+16] are themselves SLOT bases ([pa_stk_next]), which is
     where [st->type]'s and [st->size]'s alignments come from -- not from any
     arithmetic on [st]. *)
  Lemma fst_bytes_stat (st : mword 64) :
    is_aligned_paddr (Physaddr st) 8 = true ->
    is_aligned_paddr (Physaddr (pa_add st 8)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_add st 16)) 8 = true ->
    bytes_own (DfracOwn 1) st 24 ⊢
    ∃ (dev ino : mword 32) (ty nl : mword 16) (sz : mword 64),
      stat_at st dev ino ty nl sz ∗ bytes_own (DfracOwn 1) (pa_add st 12) 4.
  Proof.
    intros Ha0 Ha8 Ha16.
    (* 24 = 4 + (4 + (2 + (2 + (4 + 8)))) *)
    (* the run splits 4/4/2/2/4/8; each [change] is what lets [bytes_own_app]
       see a [_ + _] where the goal holds a numeral (the [bytes_own_slots3]
       discipline). *)
    assert (E4  : pa_add (pa_add st 4)  4 = pa_add st 8)
      by (rewrite pa_add_add; reflexivity).
    assert (E8  : pa_add (pa_add st 8)  2 = pa_add st 10)
      by (rewrite pa_add_add; reflexivity).
    assert (E10 : pa_add (pa_add st 10) 2 = pa_add st 12)
      by (rewrite pa_add_add; reflexivity).
    assert (E12 : pa_add (pa_add st 12) 4 = pa_add st 16)
      by (rewrite pa_add_add; reflexivity).
    iIntros "B".
    change 24%nat with (4 + 20)%nat.
    rewrite bytes_own_app. iDestruct "B" as "[Bdev B]".
    change 20%nat with (4 + 16)%nat.
    rewrite bytes_own_app. iDestruct "B" as "[Bino B]".
    rewrite E4.
    change 16%nat with (2 + 14)%nat.
    rewrite bytes_own_app. iDestruct "B" as "[Bty B]".
    rewrite E8.
    change 14%nat with (2 + 12)%nat.
    rewrite bytes_own_app. iDestruct "B" as "[Bnl B]".
    rewrite E10.
    change 12%nat with (4 + 8)%nat.
    rewrite bytes_own_app. iDestruct "B" as "[Bhole Bsz]".
    rewrite E12.
    (* the five alignments *)
    assert (A0 : is_aligned_paddr (Physaddr st) 4 = true)
      by (apply aligned8_aligned4; exact Ha0).
    assert (A4 : is_aligned_paddr (Physaddr (pa_add st 4)) 4 = true)
      by (apply aligned8_aligned4_hi; exact Ha0).
    assert (A8 : is_aligned_paddr (Physaddr (pa_add st 8)) 2 = true)
      by (apply fst_aligned8_aligned2; exact Ha8).
    assert (A10 : is_aligned_paddr (Physaddr (pa_add st 10)) 2 = true).
    { assert (E : pa_add st 10 = pa_add (pa_add st 8) 2)
        by (rewrite pa_add_add; reflexivity).
      rewrite E. apply fst_aligned8_aligned2_hi; exact Ha8. }
    iDestruct (fst_bytes_w4 st A0 with "Bdev") as (dev) "Hdev".
    iDestruct (fst_bytes_w4 _ A4 with "Bino") as (ino) "Hino".
    iDestruct (fst_bytes_w2 _ A8 with "Bty") as (ty) "Hty".
    iDestruct (fst_bytes_w2 _ A10 with "Bnl") as (nl) "Hnl".
    iDestruct (bytes_own_slot _ Ha16 with "Bsz") as (sz) "Hsz".
    iExists dev, ino, ty, nl, sz. iFrame "Bhole".
    rewrite /stat_at fst_pa_dev fst_pa_ino fst_pa_type fst_pa_nlink fst_pa_size.
    rewrite pa_add_0. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  OUT: [stat_at] at KNOWN values + the hole -> copyout's byte run     *)
  (* ------------------------------------------------------------------ *)
  (* copyout is parametric in the naming function, so this is the one place
     the struct's layout is written down as a function of the offset. *)
  (* NOT re-indexed piece by piece into one naming function: copyout is
     PARAMETRIC in [src_bytes], so an EXISTENTIAL naming function is all the
     call site needs, and going through the anonymous [bytes_own] form makes
     the join the same [bytes_own_app] chain as the split -- run backwards.
     Naming the 24 bytes explicitly would mean re-anchoring five sub-lists
     from [seq 0 n] onto [seq o n], which buys nothing here. *)
  Lemma fst_w4_bytes (a : Arch.pa) (w : mword 32) :
    a ↦₄ w ⊢ bytes_own (DfracOwn 1) a 4.
  Proof.
    iIntros "Hw". iDestruct (word4_pointsto_bytes with "Hw") as "Hbs".
    rewrite /bytes_own. iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (kk jj Hk) "Hb". by iExists (nth_byte w jj).
  Qed.

  Lemma fst_w2_bytes (a : Arch.pa) (w : mword 16) :
    a ↦₂ w ⊢ bytes_own (DfracOwn 1) a 2.
  Proof.
    iIntros "Hw". iDestruct (word2_pointsto_bytes with "Hw") as "Hbs".
    rewrite /bytes_own. iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (kk jj Hk) "Hb". by iExists (nth_byte w jj).
  Qed.

  Lemma fst_stat_bytes (st : mword 64) (dev ino : mword 32) (ty nl : mword 16)
      (sz : mword 64) :
    stat_at st dev ino ty nl sz -∗
    bytes_own (DfracOwn 1) (pa_add st 12) 4 -∗
    bytes_own (DfracOwn 1) st 24.
  Proof.
    assert (E4  : pa_add (pa_add st 4)  4 = pa_add st 8)
      by (rewrite pa_add_add; reflexivity).
    assert (E8  : pa_add (pa_add st 8)  2 = pa_add st 10)
      by (rewrite pa_add_add; reflexivity).
    assert (E10 : pa_add (pa_add st 10) 2 = pa_add st 12)
      by (rewrite pa_add_add; reflexivity).
    assert (E12 : pa_add (pa_add st 12) 4 = pa_add st 16)
      by (rewrite pa_add_add; reflexivity).
    iIntros "Hs Hh".
    rewrite /stat_at fst_pa_dev fst_pa_ino fst_pa_type fst_pa_nlink fst_pa_size.
    rewrite pa_add_0.
    iDestruct "Hs" as "(Hdev & Hino & Hty & Hnl & Hsz)".
    iDestruct (fst_w4_bytes with "Hdev") as "Hdev".
    iDestruct (fst_w4_bytes with "Hino") as "Hino".
    iDestruct (fst_w2_bytes with "Hty") as "Hty".
    iDestruct (fst_w2_bytes with "Hnl") as "Hnl".
    iDestruct (slot_bytes_own with "Hsz") as "[_ Hsz]".
    change 24%nat with (4 + 20)%nat.
    rewrite bytes_own_app. iSplitL "Hdev"; [iExact "Hdev" |].
    change 20%nat with (4 + 16)%nat.
    rewrite bytes_own_app. iSplitL "Hino"; [iExact "Hino" |].
    rewrite E4.
    change 16%nat with (2 + 14)%nat.
    rewrite bytes_own_app. iSplitL "Hty"; [iExact "Hty" |].
    rewrite E8.
    change 14%nat with (2 + 12)%nat.
    rewrite bytes_own_app. iSplitL "Hnl"; [iExact "Hnl" |].
    rewrite E10.
    change 12%nat with (4 + 8)%nat.
    rewrite bytes_own_app. iSplitL "Hh"; [iExact "Hh" |].
    rewrite E12. iExact "Hsz".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  BACK: copyout's byte run -> the anonymous run the slots want        *)
  (* ------------------------------------------------------------------ *)
  (* copyout returns the source unchanged, so the run comes back at the same
     naming function; the frame does not care what it holds. *)
  Lemma fst_bytes_any (st : mword 64) (f : nat -> bv 8) (n : nat) :
    ([∗ list] j ∈ seq 0 n, (pa_add st j) ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) st n.
  Proof.
    rewrite /bytes_own. iIntros "H".
    iApply (big_sepL_mono with "H"). intros i j Hj. iIntros "Hb". by iExists (f j).
  Qed.

End FilestatParts.

(* ====================================================================== *)
(*  S3b: THE FRAME, THE DISPATCH ARITHMETIC AND THE SHARED EPILOGUE        *)
(* ====================================================================== *)
(* filestat's frame is TEN slots ([c.addi16sp sp,-80]):

     slot 1  = 72(sp)  saved ra        slot  6 = 32(sp)  saved s4
     slot 2  = 64(sp)  saved s0        slot  7 = 24(sp)  \
     slot 3  = 56(sp)  saved s1        slot  8 = 16(sp)   > struct stat
     slot 4  = 48(sp)  saved s2        slot  9 =  8(sp)  /
     slot 5  = 40(sp)  saved s3        slot 10 =  0(sp)  unused

   ra/s0/s1/s4 are spilled in the prologue (+0x02..+0x08), BEFORE the type
   dispatch; s2 and s3 are spilled at +0x1e/+0x20, i.e. only on the arm that
   carries an inode.  So the type-error exit -- +0x1a -> +0x5e -> +0x60 ->
   +0x52 -- never writes frame slots 4 and 5 and never restores s2/s3, whose
   caller values are still live in the registers.  The shared epilogue at
   +0x52 therefore takes slots 4 and 5 as ARBITRARY words and gets its
   [callee_saved] for s2/s3 from a PREMISE about the incoming map, exactly as
   fileread's does for its lazily-spilled s1/s3.

   [struct stat] occupies slots 9/8/7 -- [StackBytes.slots3_bytes_own] at
   [k = 9] -- and the epilogue takes those three as arbitrary words too: what
   stati wrote into them is dead by then. *)

Notation FST := KernelSyms.filestat (only parsing).

(* ---- the 80-byte frame: push, frame pointer, pop ---- *)
Lemma fst_push_80 (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
  = StackOwn.pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fst_pop_80 (X : mword 64) :
  add_vec (StackOwn.pa_stk X 10)
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fst_fp_80 (X : mword 64) :
  add_vec (StackOwn.pa_stk X 10)
          (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the six spill/restore displacements, off the PUSHED sp ---- *)
Local Ltac fst_frm_tac :=
  unfold pa_stk, add_vec_int; rewrite add_vec_off2; apply f_equal;
  apply bv_eq; vm_compute; reflexivity.

Lemma fst_frm1 (X : mword 64) :          (* 72(sp) : saved ra *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. fst_frm_tac. Qed.

Lemma fst_frm2 (X : mword 64) :          (* 64(sp) : saved s0 *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. fst_frm_tac. Qed.

Lemma fst_frm3 (X : mword 64) :          (* 56(sp) : saved s1 *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. fst_frm_tac. Qed.

Lemma fst_frm4 (X : mword 64) :          (* 48(sp) : saved s2 *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. fst_frm_tac. Qed.

Lemma fst_frm5 (X : mword 64) :          (* 40(sp) : saved s3 *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. fst_frm_tac. Qed.

Lemma fst_frm6 (X : mword 64) :          (* 32(sp) : saved s4 *)
  add_vec (pa_stk X 10) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. fst_frm_tac. Qed.

(* [addi s2,s0,-72] : &st, off the FRAME POINTER (which is the entry sp) *)
Lemma fst_stbuf (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4024 : mword 12)) = pa_stk X 9.
Proof.
  unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma fst_frame_back (K : nat) : (10 <= K)%nat -> ((K - 10) + 10)%nat = K.
Proof. lia. Qed.

(* the stat buffer's two interior 8-aligned points, as SLOT bases -- which is
   where [fst_bytes_stat]'s second and third alignment premises come from. *)
Lemma fst_stk9_8 (X : mword 64) : pa_add (pa_stk X 9) 8 = pa_stk X 8.
Proof. exact (pa_stk_next X 9 ltac:(lia)). Qed.

Lemma fst_stk9_16 (X : mword 64) : pa_add (pa_stk X 9) 16 = pa_stk X 7.
Proof.
  assert (E : pa_add (pa_stk X 9) 16 = pa_add (pa_add (pa_stk X 9) 8) 8)
    by (rewrite pa_add_add; reflexivity).
  rewrite E (pa_stk_next X 9 ltac:(lia)).
  exact (pa_stk_next X 8 ltac:(lia)).
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE DISPATCH: [c.lw a5,0(s1); c.addiw a5,a5,-2; c.li a4,1; bltu a4,a5] *)
(* ---------------------------------------------------------------------- *)
(* The BTYPE field order is [(imm, rs2, rs1, op)], so the recorded
   [BTYPE (68, a5, a4, BLTU)] is [bltu a4,a5] and the branch is TAKEN exactly
   when [1 <u (int)(type - 2)] -- i.e. when the type is NEITHER FD_INODE (2)
   nor FD_DEVICE (3).  Everything below is that one sentence, in two
   directions. *)

Lemma fst_addv32_unsigned (a b : mword 32) :
  bv_unsigned (add_vec a b) = bv_wrap 32 (bv_unsigned a + bv_unsigned b).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N. reflexivity.
Qed.

(* what the [c.addiw] leaves, as a 32-bit word: [t + (2^32 - 2)] *)
Lemma fst_addiw_m2 (t : mword 32) :
  subrange_vec_dec
    (add_vec (sign_extend' 64 t : mword 64)
       (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))) 31 0
  = add_vec t (mword_of_int 4294967294 : mword 32).
Proof.
  rewrite -trunc32_subrange trunc32_add trunc32_sext.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))
               = (mword_of_int 4294967294 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  by rewrite HK.
Qed.

(* the modular arithmetic, over PLAIN [Z] variables: [lia] answers "Cannot
   find witness" on a goal that so much as mentions [bv_unsigned]
   (durable-notes' zify-hook trap), so the reasoning is factored out here and
   fed the unsigned readings as ordinary integers. *)
Lemma fst_mod32_sub2 (u z : Z) :
  (0 <= u < 4294967296)%Z -> (0 <= z < 2)%Z ->
  ((u + 4294967294) mod 4294967296)%Z = z -> u = (z + 2)%Z.
Proof.
  intros Hu Hz He.
  destruct (Z_lt_le_dec u 2) as [Hlt | Hge].
  - exfalso.
    rewrite (Z.mod_small (u + 4294967294)%Z 4294967296%Z ltac:(lia)) in He. lia.
  - assert (Hrw : ((u + 4294967294) mod 4294967296)%Z = (u - 2)%Z).
    { replace (u + 4294967294)%Z with (u - 2 + 1 * 4294967296)%Z by lia.
      rewrite Z.mod_add; [| lia]. apply Z.mod_small. lia. }
    rewrite Hrw in He. lia.
Qed.

(* ...and its inverse, on the two values that matter: a difference of 0 or 1
   pins the type at 2 or 3. *)
Lemma fst_sub2_eq (t : mword 32) (z r : Z) :
  (0 <= z < 2)%Z -> r = (z + 2)%Z ->
  add_vec t (mword_of_int 4294967294 : mword 32) = (mword_of_int z : mword 32) ->
  t = (mword_of_int r : mword 32).
Proof.
  intros Hz Hr He. subst r.
  pose proof (bv_unsigned_in_range _ t) as [Hlo Hhi0].
  unfold bv_modulus in Hhi0.
  assert (Hhi : (bv_unsigned t < 4294967296)%Z)
    by (first [ change (2 ^ Z.of_N 32)%Z with 4294967296%Z in Hhi0; exact Hhi0
              | change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 32))%Z
                  with 4294967296%Z in Hhi0; exact Hhi0 ]).
  clear Hhi0.
  apply (f_equal bv_unsigned) in He.
  rewrite fst_addv32_unsigned in He.
  assert (HC : bv_unsigned (mword_of_int 4294967294 : mword 32) = 4294967294%Z)
    by (vm_compute; reflexivity).
  rewrite HC in He.
  rewrite (moi32_small z ltac:(change (2 ^ 32)%Z with 4294967296%Z; lia)) in He.
  unfold bv_wrap, bv_modulus in He.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z in He.
  apply bv_eq.
  rewrite (moi32_small (z + 2) ltac:(change (2 ^ 32)%Z with 4294967296%Z; lia)).
  exact (fst_mod32_sub2 (bv_unsigned t) z (conj Hlo Hhi) Hz He).
Qed.

(* [1 <u X] holds of every 64-bit word that is neither 0 nor 1 -- which is
   all the sign extension's arithmetic this dispatch needs. *)
Lemma fst_gt1_of_ne (X : mword 64) :
  X <> (mword_of_int 0 : mword 64) -> X <> (mword_of_int 1 : mword 64) ->
  zopz0zI_u (mword_of_int 1 : mword 64) X = true.
Proof.
  intros H0 H1. unfold zopz0zI_u. apply Z.ltb_lt.
  rewrite !uint_unsigned.
  assert (Hone : bv_unsigned (mword_of_int 1 : mword 64) = 1%Z)
    by (vm_compute; reflexivity).
  rewrite Hone.
  pose proof (bv_unsigned_in_range _ X) as [Hlo _].
  destruct (Z.eq_dec (bv_unsigned X) 0) as [E0 | N0].
  { exfalso. apply H0. apply bv_eq. rewrite E0. vm_compute. reflexivity. }
  destruct (Z.eq_dec (bv_unsigned X) 1) as [E1 | N1].
  { exfalso. apply H1. apply bv_eq. rewrite E1. vm_compute. reflexivity. }
  lia.
Qed.

Lemma fst_bltu_in (t : mword 32) :
  t = (mword_of_int 2 : mword 32) \/ t = (mword_of_int 3 : mword 32) ->
  zopz0zI_u (mword_of_int 1 : mword 64)
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 t : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))) 31 0))
  = false.
Proof. intros [-> | ->]; vm_compute; reflexivity. Qed.

Lemma fst_bltu_out (t : mword 32) :
  t <> (mword_of_int 2 : mword 32) -> t <> (mword_of_int 3 : mword 32) ->
  zopz0zI_u (mword_of_int 1 : mword 64)
    (sign_extend' 64 (subrange_vec_dec
       (add_vec (sign_extend' 64 t : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6)))) 31 0))
  = true.
Proof.
  intros H2 H3. rewrite fst_addiw_m2. apply fst_gt1_of_ne.
  - intro Hc. apply H2. apply (f_equal trunc32) in Hc.
    rewrite trunc32_sext trunc32_mword_of_int in Hc.
    exact (fst_sub2_eq t 0 2 ltac:(lia) ltac:(lia) Hc).
  - intro Hc. apply H3. apply (f_equal trunc32) in Hc.
    rewrite trunc32_sext trunc32_mword_of_int in Hc.
    exact (fst_sub2_eq t 1 3 ltac:(lia) ltac:(lia) Hc).
Qed.

(* ---------------------------------------------------------------------- *)
(*  [sraiw a0,a0,31] : the [< 0 ? -1 : 0] idiom over copyout's two values   *)
(* ---------------------------------------------------------------------- *)
Lemma fst_sraiw_0 :
  sign_extend' 64 (shift_bits_right_arith
    (subrange_vec_dec (mword_of_int 0 : mword 64) 31 0 : mword 32)
    (mword_of_int 31 : mword 5)) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fst_sraiw_m1 :
  sign_extend' 64 (shift_bits_right_arith
    (subrange_vec_dec (mword_of_int (-1) : mword 64) 31 0 : mword 32)
    (mword_of_int 31 : mword 5)) = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Section ProofFilestatParts.
  Context `{!riscvGS Σ, !sieG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* ------------------------------------------------------------------ *)
  (*  NAMING the 24-byte run copyout is parametric in                     *)
  (* ------------------------------------------------------------------ *)
  (* [bytes_own] owns each byte at an EXISTENTIAL value; copyout wants one
     naming function.  Since the length is a literal, the cheapest honest
     route is to peel the twenty-four existentials and read the function off
     the resulting list -- no [big_sepL_exist] and no list/function bridge. *)
  Lemma fst_bytes_name24 (a : Arch.pa) :
    bytes_own (DfracOwn 1) a 24 ⊢
    ∃ f : nat -> bv 8, ([∗ list] j ∈ seq 0 24, (pa_add a j) ↦ₘ f j).
  Proof.
    rewrite /bytes_own. cbn [seq].
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 &
              H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 &
              H22 & H23 & _)".
    iDestruct "H0" as (b0) "H0".   iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2".   iDestruct "H3" as (b3) "H3".
    iDestruct "H4" as (b4) "H4".   iDestruct "H5" as (b5) "H5".
    iDestruct "H6" as (b6) "H6".   iDestruct "H7" as (b7) "H7".
    iDestruct "H8" as (b8) "H8".   iDestruct "H9" as (b9) "H9".
    iDestruct "H10" as (b10) "H10". iDestruct "H11" as (b11) "H11".
    iDestruct "H12" as (b12) "H12". iDestruct "H13" as (b13) "H13".
    iDestruct "H14" as (b14) "H14". iDestruct "H15" as (b15) "H15".
    iDestruct "H16" as (b16) "H16". iDestruct "H17" as (b17) "H17".
    iDestruct "H18" as (b18) "H18". iDestruct "H19" as (b19) "H19".
    iDestruct "H20" as (b20) "H20". iDestruct "H21" as (b21) "H21".
    iDestruct "H22" as (b22) "H22". iDestruct "H23" as (b23) "H23".
    iExists (fun j => nth j [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;
                             b12;b13;b14;b15;b16;b17;b18;b19;b20;b21;b22;b23] b0).
    cbn [nth]. iFrame. all: try done.
  Qed.

  (* =================================================================== *)
  (*  +0x52 .. +0x5c -- THE EPILOGUE.  Both exits reach it.               *)
  (* =================================================================== *)
  Lemma fst_epi `{GEN : GenId} `{CID0 : CpuId}
      (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s40 : mword 64) (rv : mword 64)
      (w4 w5 w7 w8 w9 w10 : mword 64)
      (p : mword 64) (b : bool) :
    (10 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs4 = s40 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 10 ->
    Mt !!! Regidx Ra0 = rv ->
    (* s2 and s3 are in here, and that is the whole point: the type-error
       exit never spilled them. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 10)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (FST + 0x52) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) w4 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) s40 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs40 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hcont".
    iPoseProof (fsti_52 with "Htext") as "Hi52".
    iPoseProof (fsti_54 with "Htext") as "Hi54".
    iPoseProof (fsti_56 with "Htext") as "Hi56".
    iPoseProof (fsti_58 with "Htext") as "Hi58".
    iPoseProof (fsti_5a with "Htext") as "Hi5a".
    iPoseProof (fsti_5c with "Htext") as "Hi5c".
    (* ---- +0x52: c.ldsp ra,72(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                   = pa_stk sp0 1) by (rewrite Hmtsp; apply fst_frm1).
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x52)) (mword_of_int 9 : mword 6) Rra
              Mt (K - 10)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 Hb1 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp54 : add_vec_int (mword_of_int (FST + 0x52) : mword 64) 2
                    = mword_of_int (FST + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* ---- +0x54: c.ldsp s0,64(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                   = pa_stk sp0 2) by (rewrite HT1sp; apply fst_frm2).
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x54)) (mword_of_int 8 : mword 6) Rs0
              T1 (K - 10)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 Hb2 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp56 : add_vec_int (mword_of_int (FST + 0x54) : mword 64) 2
                    = mword_of_int (FST + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* ---- +0x56: c.ldsp s1,56(sp) ---- *)
    assert (Hpa3 : add_vec (T2 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                   = pa_stk sp0 3) by (rewrite HT2sp; apply fst_frm3).
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x56)) (mword_of_int 7 : mword 6) Rs1
              T2 (K - 10)%nat s10 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 Hb3 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp58 : add_vec_int (mword_of_int (FST + 0x56) : mword 64) 2
                    = mword_of_int (FST + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* ---- +0x58: c.ldsp s4,32(sp) ---- *)
    assert (Hpa6 : add_vec (T3 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HT3sp; apply fst_frm6).
    iEval (rewrite -Hpa6) in "Hb6".
    iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x58)) (mword_of_int 4 : mword 6) Rs4
              T3 (K - 10)%nat s40 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 Hb6 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hb6". iEval (rewrite Hpa6) in "Hb6".
    set (T4 := <[Regidx Rs4 := regval_into_reg s40]> T3).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (Hpp5a : add_vec_int (mword_of_int (FST + 0x58) : mword 64) 2
                    = mword_of_int (FST + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* ---- +0x5a: c.addi16sp sp,80 -- the frame goes back ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0)
      by (rewrite HT4sp; apply fst_pop_80).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10)
      by (rewrite Hwv; exact HT4sp).
    iAssert (stack_own sp0 10) with "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10]"
      as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      iSplitL "Hb9"; [iExists _; iExact "Hb9"|].
      iSplitL "Hb10"; [iExists _; iExact "Hb10"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (FST + 0x5a)) (mword_of_int 5 : mword 6)
              T4 (K - 10)%nat 10 b Hpop with "Hcg Hpc Hi5a Hframe [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((K - 10) + 10)%nat = K) by exact (fst_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T4 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> T4) with T5.
    assert (Hpp5c : add_vec_int (mword_of_int (FST + 0x5a) : mword 64) 2
                    = mword_of_int (FST + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* ---- +0x5c: c.jr ra ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (FST + 0x5c)) Rra T5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi5c [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc". iEval (rewrite HT5ra) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] Hcg Hpc").
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs1 -> r <> Rs4 -> r <> Rra ->
                      T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns4 Nra.
      rewrite /T5 upd_ne; [| regne].
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns1 Ns4). }
    assert (HT5a0 : T5 !!! Regidx Ra0 = rv).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact Hmta0 | vm_compute; discriminate]. }
    split; [| exact HT5a0].
    rewrite /callee_saved. split_and!.
    7-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    4-5: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T5 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs10. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq Hs40. reflexivity.
  Qed.

End ProofFilestatParts.

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
Require Import SpecStati.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

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

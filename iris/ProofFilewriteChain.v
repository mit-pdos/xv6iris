(* ProofFilewriteChain.v -- filewrite's CHUNK LOOP INVARIANT, and its five
   moves.  A PROOF-SIDE LEAF: nothing above [ProofFilewrite.v] needs any of
   it, so it does not belong in a statement file -- statement files stay
   statements.

   [fw_au_raw Γ i γo n M ua Q t p x] is "[p] chunks have fired, they wrote
   [t] bytes in total, their concatenation is the caller's own run at [ua],
   and here is the rest of the chain, resuming [x] nodes past them" -- [x]
   is 0 on every loop entry and becomes 1 only at the exit a SHORT chunk
   forces, when its offset move spent the chain's partial arm
   ([FsAbsWriteFire.awrite_part_at]).  It is the ONLY iProp the loop
   carries; the two facts that make it a loop INVARIANT are Coq-level and
   ride as ordinary premises of [ProofFilewrite.fw_loop]:

     t = iz   /\   t = FW_MAX * Z.of_nat p

   -- the fired total IS the running offset, and every fired chunk was
   exactly [FW_MAX].  THERE IS NO [clean] FLAG AND NO SLACK: a chunk fires
   only when its start is INSIDE the file ([wri_pre]'s [off <= length bs0]),
   and [SpecWritei]'s SUCCESS ARM REPORTS THAT GUARD, so no chunk the loop
   completes has to be skipped.

   WHY THE TIE IS NOT INSIDE THE iProp.  The last chunk may be SHORT, so
   [t = FW_MAX * p] is false of the state the exhausted exit hands out; it
   is a truth about every LOOP ENTRY, not about every state.  Keeping it
   Coq-level is what lets the five moves below be tie-free.

   THERE IS NO RECEIPT ACCUMULATOR.  The state carries the chain and the
   BYTES; everything a caller wants per chunk it records in the PREFIX
   CURSOR [Q], inside the phase 2 that builds the next node.  So [_take]
   takes back only the chunk's bytes and its content premise, and
   [_spend_part] takes back nothing but the tail.

   THE FIVE MOVES, one per thing the loop does with it: start it ([_init]),
   spend one node's FULL arm at a chunk's fire ([_take]), spend one node's
   PARTIAL arm at a short chunk's offset move ([_spend_part]), and read it
   off at each of the two exits ([_ok] at [t = n], [_fail] at [t < n] or at
   the capstone's never-entered loop). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.
Require Import FdSlots.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import FsStateDefs.
Require Import Xv6G.
Require Import SysWriteDefs.     (* [FW_MAX], [wchunks], [wri_pre]        *)
Require Import FsAbsWriteFire.     (* [awrite_chain] and its two arms       *)
Require Import SpecCopyin.         (* [ubytes_at]: the content seam         *)
Require Import SpecFilewrite.      (* [write_post_ok_at], [write_post_fail_at] *)
Require Import AppInv.             (* [appE]                                *)
Require Import TsoCtx.

Local Open Scope Z_scope.

Section FilewriteChain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  Definition fw_au_raw Γ (i : Z) (γo : gname) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64) (Q : nat -> iProp Σ)
      (t : Z) (p x : nat) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜length bss = p⌝ ∗
       ⌜Z.of_nat (length (concat bss)) = t⌝ ∗
       ⌜(p + x <= wchunks n)%nat⌝ ∗
       ⌜(x <= 1)%nat⌝ ∗
       (* THE CONTENT HALF (RULING A).  What has been spliced so far IS the
          caller's own run at [ua].  It rides INSIDE the iProp rather than
          as a Coq-level tie beside it, because unlike [t = FW_MAX * p] it
          is true of every state the loop hands out -- the exhausted exit
          included -- and both exits read it off unchanged. *)
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       awrite_chain Γ appE i γo M ua Q (p + x) (wchunks n - p - x)%nat)%I.

  Lemma fw_au_raw_init Γ (i : Z) γo (n : Z) M ua Q :
    awrite_chain Γ appE i γo M ua Q 0%nat (wchunks n) -∗
    fw_au_raw Γ i γo n M ua Q 0 0%nat 0%nat.
  Proof.
    iIntros "Hcm". rewrite /fw_au_raw. iExists [].
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; apply ubytes_at_nil |].
    rewrite !Nat.sub_0_r (Nat.add_0_r 0). iExact "Hcm".
  Qed.

  (* ONE CHUNK'S FIRE, both halves: the head node's FULL arm comes out at
     the index the chain handed it out at (its continuation IS the rest of
     the chain), and the closer takes that rest back with the chunk's
     bytes.  The chain's own [Q k] conjunct is DROPPED here -- the kernel
     eliminates to an arm when it fires. *)
  Lemma fw_au_raw_take Γ (i : Z) γo (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo n M ua Q t p 0%nat -∗
      awrite_full_at Γ appE i γo M ua p
        (awrite_chain Γ appE i γo M ua Q (S p) (wchunks n - S p)) ∗
      (∀ bs : list (bv 8),
         ⌜ubytes_at M (add_vec_int ua t) bs⌝ -∗
         awrite_chain Γ appE i γo M ua Q (S p) (wchunks n - S p) -∗
         fw_au_raw Γ i γo n M ua Q (t + Z.of_nat (length bs)) (S p) 0%nat).
  Proof.
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    (* the peel: the chain has at least one node left, and the FULL arm is
       its second conjunct's first ([awrite_chain]'s shape) *)
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_S.
    iDestruct "Hcm" as "[_ [Hhead _]]".
    iFrame "Hhead". iIntros (bs) "%Hbyc Htail".
    iExists (bss ++ [bs])%list.
    assert (Hlen' : length ((bss ++ [bs])%list) = S p)
      by (rewrite length_app Hlen /=; lia).
    iSplitR; [by iPureIntro |].
    iSplitR.
    { iPureIntro. rewrite concat_app length_app /= app_nil_r. lia. }
    iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; lia |].
    (* THE APPEND: the accumulated run and this chunk are ADJACENT at [ua],
       because [t] IS the accumulated length ([Htot]). *)
    iSplitR.
    { iPureIntro. rewrite concat_app /= app_nil_r.
      apply (ubytes_at_app M ua (concat bss) bs Hby).
      rewrite Htot. exact Hbyc. }
    rewrite (Nat.add_0_r (S p)) (Nat.sub_0_r (wchunks n - S p)). iExact "Htail".
  Qed.

  (* ONE SHORT CHUNK'S INSTANT: the head node's PARTIAL arm comes out, and
     the closer takes the rest of the chain back one node further on.  The
     cursor at that position is whatever the caller built inside the arm's
     own phase 2, so the fail exit reads off what landed. *)
  Lemma fw_au_raw_spend_part Γ (i : Z) γo (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo n M ua Q t p 0%nat -∗
      awrite_part_at Γ appE i γo M ua p
        (awrite_chain Γ appE i γo M ua Q (S p) (wchunks n - S p)) ∗
      (awrite_chain Γ appE i γo M ua Q (S p) (wchunks n - S p) -∗
       fw_au_raw Γ i γo n M ua Q t p 1%nat).
  Proof.
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_S.
    iDestruct "Hcm" as "[_ [_ Hpart]]".
    iFrame "Hpart". iIntros "Htail".
    iExists bss.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |].
    assert (Hcnt' : (wchunks n - p - 1 = wchunks n - S p)%nat) by lia.
    rewrite Hcnt' Nat.add_1_r. iExact "Htail".
  Qed.

  (* THE EXITS *)
  Lemma fw_au_raw_ok Γ (i : Z) γo (n : Z) M ua Q (p : nat) :
    fw_au_raw Γ i γo n M ua Q n p 0%nat -∗ write_post_ok_at Γ i γo n M ua Q.
  Proof.
    iIntros "Hst". rewrite /fw_au_raw /write_post_ok_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    iExists bss. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [by iPureIntro |].
    rewrite Hlen (Nat.add_0_r p) (Nat.sub_0_r (wchunks n - p)). iExact "Hcm".
  Qed.

  (* THE FAIL EXIT, AT BOTH OF ITS TWO SHAPES.  [t < n] is the loop's own
     (the short-write break, the only way out of the loop that is not the
     count); the second disjunct is the CAPSTONE's, on the [n < 0] guard at
     +0x20, where the loop is never entered and the chain refunds whole. *)
  Lemma fw_au_raw_fail Γ (i : Z) γo (n : Z) M ua Q (t : Z) (p x : nat) :
    (t < n)%Z \/ (n < 0)%Z /\ p = 0%nat ->
    fw_au_raw Γ i γo n M ua Q t p x -∗ write_post_fail_at Γ i γo n M ua Q.
  Proof.
    intros Hex. iIntros "Hst". rewrite /fw_au_raw /write_post_fail_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    iExists bss, x. iSplitR.
    { iPureIntro. destruct Hex as [Htn | [Hneg Hp0]].
      - left. lia.
      - right. split; [exact Hneg |].
        apply nil_length_inv. rewrite Hlen. exact Hp0. }
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |].
    rewrite Hlen. iExact "Hcm".
  Qed.

End FilewriteChain.

Global Typeclasses Opaque fw_au_raw.

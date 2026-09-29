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
From xv6iris Require Import StepIndex.
From iris.algebra Require Import auth gmap frac dfrac.
From transfinite.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
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
Require Import FsCfg.              (* [fsc_fs]: the fs configuration         *)
Require Import SpecWritei.         (* [wi_blocks]                           *)
Require Import FsBytesGamma.       (* [fs_gamma_L]                          *)
Require Import InodeInv.           (* [MAXFILE]                             *)
Require Import BioDefs.            (* [BSIZE]                               *)
Require Import FsNode.             (* [fs_node]                             *)
Require Import FsAbsDefs.          (* [abs_row], [anode]                    *)
Require Import FsState.            (* [top_frag]                            *)
Require Import FsBlocks.           (* [fs_names], [blk_splice]              *)
Require Import InodeRegion.        (* [ftop_inv], [top_frag]                *)
Require Import FsAbsWriteFire.     (* [awrite_chain] and its two arms       *)
Require Import UserOff.            (* [uoff]: the held walk's carrier       *)
Require Import UserPtTree.         (* [uptd]: the partial arm's table       *)
Require Import SpecCopyin.         (* [ubytes_at]: the content seam         *)
Require Import UserPerm.   (* [uperm], [perm_of] -- RULING WR-TB *)
Require Import SpecFilewrite.      (* [write_post_ok_at], [write_post_fail_at] *)
Require Import AppInv.             (* [appE]                                *)
Require Import CtxIdDefs.

Local Open Scope Z_scope.

Section FilewriteChain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* [P] IS THE TABLE THE PARTIAL ARMS NAME (lane WRITE-RELAY-2): the chain
     the contract hands in owes EVERY table ([FsAbsWriteFire.awrite_chain]'s
     [∀ P]) and the walk fixes its own once, at [fw_au_raw_init]. *)
  Definition fw_au_raw Γ (i : Z) (γo : gname) (P : uptd) (n : Z)
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
       awrite_chain_at Γ appE i γo M ua P n Q (p + x) (wchunks n - p - x)%nat)%I.

  (* ===================================================================== *)
  (*  THE HELD WALK'S CARRIER (lane OFF-LINK-5; design/app-file.md SS3)     *)
  (* ===================================================================== *)
  (* [fw_au_raw] AT THE CLIENT-ADVANCED CHAIN, AND NOTHING ELSE CHANGES.
     A held descriptor's user half is in the CLIENT's closure, not the
     kernel's, so this carrier holds no [UserOff.uoff] and the loop carries
     no second resource: every pure row below is [fw_au_raw]'s verbatim and
     the five moves are its five, with [FsAbsWriteFire.awrite_chain_adv] in
     place of [awrite_chain_at].

     (LANE OFF-LINK-4'S ANCHORED CARRIER IS GONE, and so is the anchor it
     existed to carry.  The equation [off = off0] that the anchored node
     took as a relayed premise is read by the client off the half it holds,
     INSIDE the node's own [forall off] -- see [FsAbsWriteFire]'s section
     2b.  The consequence here is the one that matters to the loop: the
     kernel neither carries a half across the iterations nor answers a
     supplier at the fire, so the loop's own shape is untouched.) *)
  Definition fw_au_adv Γ (i : Z) (γo : gname) (P : uptd) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64) (Q : nat -> iProp Σ)
      (t : Z) (p x : nat) : iProp Σ :=
    (∃ bss : list (list (bv 8)),
       ⌜length bss = p⌝ ∗
       ⌜Z.of_nat (length (concat bss)) = t⌝ ∗
       ⌜(p + x <= wchunks n)%nat⌝ ∗
       ⌜(x <= 1)%nat⌝ ∗
       ⌜ubytes_at M ua (concat bss)⌝ ∗
       awrite_chain_adv Γ appE i γo M ua P n Q (p + x) (wchunks n - p - x)%nat)%I.

  Lemma fw_au_adv_init Γ (i : Z) γo (P : uptd) (n : Z) M ua Q :
    awrite_chain_adv Γ appE i γo M ua P n Q 0%nat (wchunks n) -∗
    fw_au_adv Γ i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    iIntros "Hcm". rewrite /fw_au_adv. iExists [].
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; lia |].
    iSplitR; [iPureIntro; apply ubytes_at_nil |].
    rewrite !Nat.sub_0_r (Nat.add_0_r 0). iExact "Hcm".
  Qed.

  (* THE FULL ARM'S PEEL, [fw_au_raw_take]'s twin. *)
  Lemma fw_au_adv_take Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_adv Γ i γo P n M ua Q t p 0%nat -∗
      awrite_full_adv Γ appE i γo M ua n p
        (awrite_chain_adv Γ appE i γo M ua P n Q (S p) (wchunks n - S p)) ∗
      (∀ bs : list (bv 8),
         ⌜ubytes_at M (add_vec_int ua t) bs⌝ -∗
         awrite_chain_adv Γ appE i γo M ua P n Q (S p) (wchunks n - S p) -∗
         fw_au_adv Γ i γo P n M ua Q (t + Z.of_nat (length bs)) (S p) 0%nat).
  Proof using .
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_adv.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_adv_S.
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
    iSplitR.
    { iPureIntro. rewrite concat_app /= app_nil_r.
      apply (ubytes_at_app M ua (concat bss) bs Hby).
      rewrite Htot. exact Hbyc. }
    rewrite (Nat.add_0_r (S p)) (Nat.sub_0_r (wchunks n - S p)). iExact "Htail".
  Qed.

  (* ...and the short chunk's, [fw_au_raw_spend_part]'s twin. *)
  Lemma fw_au_adv_spend_part Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_adv Γ i γo P n M ua Q t p 0%nat -∗
      awrite_part_adv Γ appE i γo M ua P n p
        (awrite_chain_adv Γ appE i γo M ua P n Q (S p) (wchunks n - S p)) ∗
      (awrite_chain_adv Γ appE i γo M ua P n Q (S p) (wchunks n - S p) -∗
       fw_au_adv Γ i γo P n M ua Q t p 1%nat).
  Proof using .
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_adv.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_adv_S.
    iDestruct "Hcm" as "[_ [_ Hpart]]".
    iFrame "Hpart". iIntros "Htail".
    iExists bss.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |].
    assert (Hcnt' : (wchunks n - p - 1 = wchunks n - S p)%nat) by lia.
    rewrite Hcnt' Nat.add_1_r. iExact "Htail".
  Qed.

  (* THE TWO EXITS, AND THEY REPORT THE LANDED POST.  Nothing above the fire
     learns that this call was a held one: the residue converts down at
     [FsAbsWriteFire.awrite_chain_at_of_adv], so [SpecFilewrite]'s
     [write_arms_at] is what a held write answers with, unchanged.  What the
     CLIENT gets back that a parked caller does not -- its own half, at the
     position the file reached -- rides in its own cursor [Q], which is
     where its nodes put it. *)
  Lemma fw_au_adv_ok Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (p : nat) :
    fw_au_adv Γ i γo P n M ua Q n p 0%nat -∗
    write_post_ok_at Γ i γo P n M ua Q.
  Proof using .
    iIntros "Hst". rewrite /fw_au_adv /write_post_ok_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    iExists bss. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; lia |]. iSplitR; [by iPureIntro |].
    rewrite Hlen (Nat.add_0_r p) (Nat.sub_0_r (wchunks n - p)).
    iApply (awrite_chain_at_of_adv with "Hcm").
  Qed.

  Lemma fw_au_adv_fail Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p x : nat) :
    (t < n)%Z \/ (n < 0)%Z /\ p = 0%nat ->
    fw_au_adv Γ i γo P n M ua Q t p x -∗
    write_post_fail_at Γ i γo P n M ua Q.
  Proof using .
    intros Hex. iIntros "Hst". rewrite /fw_au_adv /write_post_fail_at.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    iExists bss, x. iSplitR.
    { iPureIntro. destruct Hex as [Htn | [Hneg Hp0]].
      - left. lia.
      - right. split; [exact Hneg |].
        apply nil_length_inv. rewrite Hlen. exact Hp0. }
    iSplitR; [iPureIntro; lia |]. iSplitR; [iPureIntro; lia |].
    iSplitR; [by iPureIntro |].
    rewrite Hlen. iApply (awrite_chain_at_of_adv with "Hcm").
  Qed.

  Lemma fw_au_raw_init Γ (i : Z) γo (P : uptd) (n : Z) M ua Q :
    awrite_chain Γ appE i γo M ua n Q 0%nat (wchunks n) -∗
    fw_au_raw Γ i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    iIntros "Hcm".
    iDestruct (awrite_chain_at_of Γ appE i γo M ua n Q 0%nat (wchunks n) P
                 with "Hcm") as "Hcm".
    rewrite /fw_au_raw. iExists [].
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
  Lemma fw_au_raw_take Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo P n M ua Q t p 0%nat -∗
      awrite_full_at Γ appE i γo M ua n p
        (awrite_chain_at Γ appE i γo M ua P n Q (S p) (wchunks n - S p)) ∗
      (∀ bs : list (bv 8),
         ⌜ubytes_at M (add_vec_int ua t) bs⌝ -∗
         awrite_chain_at Γ appE i γo M ua P n Q (S p) (wchunks n - S p) -∗
         fw_au_raw Γ i γo P n M ua Q (t + Z.of_nat (length bs)) (S p) 0%nat).
  Proof using .
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    (* the peel: the chain has at least one node left, and the FULL arm is
       its second conjunct's first ([awrite_chain]'s shape) *)
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_at_S.
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
  Lemma fw_au_raw_spend_part Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p : nat) :
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    fw_au_raw Γ i γo P n M ua Q t p 0%nat -∗
      awrite_part_at Γ appE i γo M ua P n p
        (awrite_chain_at Γ appE i γo M ua P n Q (S p) (wchunks n - S p)) ∗
      (awrite_chain_at Γ appE i γo M ua P n Q (S p) (wchunks n - S p) -∗
       fw_au_raw Γ i γo P n M ua Q t p 1%nat).
  Proof using .
    intros Ht Htn Htie. iIntros "Hst".
    assert (Hsp : (S p <= wchunks n)%nat)
      by exact (wri_count_step n t p Ht Htn Htie).
    rewrite /fw_au_raw.
    iDestruct "Hst" as (bss) "(%Hlen & %Htot & %Hp & %Hx & %Hby & Hcm)".
    assert (Hcnt : (wchunks n - p - 0 = S (wchunks n - S p))%nat) by lia.
    rewrite Hcnt (Nat.add_0_r p) awrite_chain_at_S.
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
  Lemma fw_au_raw_ok Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (p : nat) :
    fw_au_raw Γ i γo P n M ua Q n p 0%nat -∗
    write_post_ok_at Γ i γo P n M ua Q.
  Proof using .
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
  Lemma fw_au_raw_fail Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p x : nat) :
    (t < n)%Z \/ (n < 0)%Z /\ p = 0%nat ->
    fw_au_raw Γ i γo P n M ua Q t p x -∗
    write_post_fail_at Γ i γo P n M ua Q.
  Proof using .
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

  (* ===================================================================== *)
  (*  THE LOOP'S CARRIER, KEYED ON THE ROW'S OFFSET MODE (lane OFF-LINK-5)  *)
  (* ===================================================================== *)
  (* ONE SUPPLIER NOTION FOR THE TWO WAYS THE KERNEL MAY MOVE THE SHADOW
     ITSELF: the descriptor row's existential invariant (mode park) or the
     taint (an object already disconnected, which is what the generic tier
     leaves and what a held row's OTHER arm carries).  Both are PERSISTENT,
     so the loop carries this beside the chain at no cost and no exit has
     to give it back. *)
  Definition fw_supply (γo : gname) : iProp Σ :=
    (off_user_inv γo ∨ app_taint)%I.

  Global Instance fw_supply_persistent γo : Persistent (fw_supply γo).
  Proof using . rewrite /fw_supply. apply _. Qed.

  Lemma fw_supply_off (E : coPset) (γo : gname) (off d : nat) :
    ↑foffN ⊆ E -> fw_supply γo -∗ off_supply γo E off d True.
  Proof using .
    intros HE. iIntros "[#Hinv | #Ht]".
    - iApply (off_supply_parked E γo off d HE with "Hinv").
    - iApply (off_supply_taint E γo off d with "Ht").
  Qed.

  (* AND THE CARRIER ITSELF.  A PARKED row walks the landed carrier beside
     that supplier.  A HELD one walks the CLIENT-ADVANCED carrier -- whose
     nodes move the shadow themselves, so no supplier appears -- or, if the
     object was disconnected before the call, the landed carrier beside the
     taint, which is the other arm of [SpecFilewrite.filewrite_in_held].
     The disjunction does not move during the loop: each arm's fire
     reproduces its own arm. *)
  Definition fw_au_st (om : offmode) Γ (i : Z) (γo : gname) (P : uptd) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64) (Q : nat -> iProp Σ)
      (t : Z) (p x : nat) : iProp Σ :=
    match om with
    | OffParked => (fw_supply γo ∗ fw_au_raw Γ i γo P n M ua Q t p x)%I
    | OffHeld => (fw_au_adv Γ i γo P n M ua Q t p x
                  ∨ (fw_supply γo ∗ fw_au_raw Γ i γo P n M ua Q t p x))%I
    end.

  (* THE ENTRY, at each mode's own input ([SpecFilewrite.filewrite_in]). *)
  Lemma fw_au_st_init_parked Γ (i : Z) γo (P : uptd) (n : Z) M ua Q :
    off_user_inv γo -∗
    awrite_chain Γ appE i γo M ua n Q 0%nat (wchunks n) -∗
    fw_au_st OffParked Γ i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    iIntros "#Hinv Hcm". rewrite /fw_au_st. iSplitR.
    { rewrite /fw_supply. by iLeft. }
    iApply (fw_au_raw_init with "Hcm").
  Qed.

  Lemma fw_au_st_init_held Γ (i : Z) γo (P : uptd) (n : Z) M ua Q :
    awrite_chain_adv Γ appE i γo M ua P n Q 0%nat (wchunks n) -∗
    fw_au_st OffHeld Γ i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    iIntros "Hcm". rewrite /fw_au_st. iLeft.
    iApply (fw_au_adv_init with "Hcm").
  Qed.

  Lemma fw_au_st_init_taint Γ (i : Z) γo (P : uptd) (n : Z) M ua Q :
    app_taint -∗
    awrite_chain Γ appE i γo M ua n Q 0%nat (wchunks n) -∗
    fw_au_st OffHeld Γ i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    iIntros "#Ht Hcm". rewrite /fw_au_st. iRight. iSplitR.
    { rewrite /fw_supply. by iRight. }
    iApply (fw_au_raw_init with "Hcm").
  Qed.

  (* ...AND THE ENTRY A WALK ACTUALLY HAS: the row (whose mode it is keyed
     on) and the contract's input at that mode.  At PARK the row IS the
     supplier; at HAND it is [emp] and the two arms of
     [SpecFilewrite.filewrite_in_held] pick which carrier the loop starts
     in. *)
  (* ...AND THE TABLE GUARD IS DISCHARGED HERE AND NOWHERE ELSE (RULING
     WR-TB).  The kernel is the party that knows [P], and at this one site
     it has all three of the guard's conjuncts about its own
     [ProcDefs.pv_upt]: the table's well-formedness and the lazy bit's claim
     are [ProcInv.proc_priv_pt_wf] and [proc_priv_lazy], and the permission
     map's equation is [UexecSlot.uvis_of]'s own definition -- the key's
     [uvis_perm] IS [perm_of (ud_um P) (uvis_sz)].  So the client's chain
     comes out of its [∀ P] with the guard paid, and no U-tier supplier has
     to know which table it will be fired at. *)
  Lemma fw_au_st_init (om : offmode) (rb wb : bool) (i : Z) (γo : gname)
      (pmv : gmap (mword 27) uperm) (sz : Z) (lz : bool)
      (P : uptd) (n : Z) M ua Q :
    wr_tb pmv sz lz P ->
    foff_row (FdOpen rb wb (FdInode i γo om)) -∗
    filewrite_in_inode_om pmv sz lz om i γo n M ua Q -∗
    fw_au_st om (fs_gamma_L fsc_fs) i γo P n M ua Q 0 0%nat 0%nat.
  Proof using .
    intros Htb. destruct om; rewrite /filewrite_in_inode_om.
    - iIntros "#Hrow Hcm". iApply (fw_au_st_init_parked with "Hrow Hcm").
    - iIntros "_ [Hcm | [Hcm #Ht]]".
      + iApply (fw_au_st_init_held with "[Hcm]").
        iApply ("Hcm" $! P with "[//]").
      + iApply (fw_au_st_init_taint with "Ht Hcm").
  Qed.

  (* THE TWO EXITS, AT THE LANDED POST -- which is the whole point of the
     client-advanced shape: nothing above the fire learns the row's mode. *)
  Lemma fw_au_st_ok om Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (p : nat) :
    fw_au_st om Γ i γo P n M ua Q n p 0%nat -∗
    write_post_ok_at Γ i γo P n M ua Q.
  Proof using .
    destruct om; rewrite /fw_au_st.
    - iIntros "[_ H]". iApply (fw_au_raw_ok with "H").
    - iIntros "[H | [_ H]]";
        [ iApply (fw_au_adv_ok with "H") | iApply (fw_au_raw_ok with "H") ].
  Qed.

  Lemma fw_au_st_fail om Γ (i : Z) γo (P : uptd) (n : Z) M ua Q (t : Z) (p x : nat) :
    (t < n)%Z \/ (n < 0)%Z /\ p = 0%nat ->
    fw_au_st om Γ i γo P n M ua Q t p x -∗
    write_post_fail_at Γ i γo P n M ua Q.
  Proof using .
    intros Hex. destruct om; rewrite /fw_au_st.
    - iIntros "[_ H]". iApply (fw_au_raw_fail _ _ _ _ _ _ _ _ _ _ _ Hex with "H").
    - iIntros "[H | [_ H]]";
        [ iApply (fw_au_adv_fail _ _ _ _ _ _ _ _ _ _ _ Hex with "H")
        | iApply (fw_au_raw_fail _ _ _ _ _ _ _ _ _ _ _ Hex with "H") ].
  Qed.

  (* ONE CHUNK'S FIRE, PACKAGED: the peel, the fire and the closer in one
     step, so [ProofFilewrite]'s loop body branches on the mode HERE and
     not in the middle of its own 300-hypothesis context.  The two arms
     differ in exactly one line -- which fire lemma runs -- because the
     client-advanced node needs no supplier and the landed one does. *)
  Lemma fw_st_fire_full (om : offmode) (γfs : fs_names) (E : coPset)
      (i : Z) (γo : gname) (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd)
      (n : Z) (Q : nat -> iProp Σ) (t : Z) (p : nat)
      (off : nat) (bs bs0 : list (bv 8)) (nl : nat) (nd nd' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i nd' ->
    (0 < length bs)%nat ->
    (off <= length bs0)%nat ->
    (off + length bs <= MAXFILE * BSIZE)%nat ->
    fn_type nd <> 0 ->
    abs_row nd = MkAnode (AFile bs0) nl ->
    fn_type nd' <> 0 ->
    abs_row nd' = MkAnode (AFile (blk_splice off bs bs0)) nl ->
    ubytes_at M (add_vec_int ua t) bs ->
    Z.of_nat (length bs) = wchunk_at n p ->
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    ftop_inv γfs -∗ app_inv γfs -∗
    fw_au_st om (fs_gamma_L γfs) i γo P n M ua Q t p 0%nat -∗
    top_frag (fs_gamma_L γfs) i nd -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i nd'
      ∗ off_link γo (Z.of_nat (off + length bs))
      ∗ fw_au_st om (fs_gamma_L γfs) i γo P n M ua Q
          (t + Z.of_nat (length bs)) (S p) 0%nat.
  Proof using .
    intros HE Hloc Hpos Hoff Hcap Hnz Habs Hnz' Habs' Hby Hlen Ht Htn Htie.
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    assert (Hbyk : ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat p)) bs)
      by (rewrite -Htie; exact Hby).
    iIntros "#Hi #Hai Hst Hf Hg".
    rewrite /fw_au_st.
    destruct om.
    - iDestruct "Hst" as "[#Hsup Hau]".
      iDestruct (fw_au_raw_take (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie with "Hau")
        as "[Hcm Hback]".
      iMod (wrf_awrite_fire_gen γfs E i γo M ua n p _ True off bs bs0 nl nd nd'
              HE Hloc Hpos Hoff Hcap Hnz Habs Hnz' Habs' Hbyk Hlen
              with "Hi Hai [] Hcm Hf Hg") as "(Hf & Hg & _ & Htail)".
      { iApply (fw_supply_off E γo off (length bs) Hfoff with "Hsup"). }
      iModIntro. iFrame "Hf Hg". iSplitR; [iExact "Hsup" |].
      iApply ("Hback" $! bs with "[//] Htail").
    - iDestruct "Hst" as "[Hau | [#Hsup Hau]]".
      + iDestruct (fw_au_adv_take (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie with "Hau")
          as "[Hcm Hback]".
        iMod (wrf_awrite_fire_adv γfs E i γo M ua n p _ off bs bs0 nl nd nd'
                HE Hloc Hpos Hoff Hcap Hnz Habs Hnz' Habs' Hbyk Hlen
                with "Hi Hai Hcm Hf Hg") as "(Hf & Hg & Htail)".
        iModIntro. iFrame "Hf Hg". iLeft.
        iApply ("Hback" $! bs with "[//] Htail").
      + iDestruct (fw_au_raw_take (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie with "Hau")
          as "[Hcm Hback]".
        iMod (wrf_awrite_fire_gen γfs E i γo M ua n p _ True off bs bs0 nl nd nd'
                HE Hloc Hpos Hoff Hcap Hnz Habs Hnz' Habs' Hbyk Hlen
                with "Hi Hai [] Hcm Hf Hg") as "(Hf & Hg & _ & Htail)".
        { iApply (fw_supply_off E γo off (length bs) Hfoff with "Hsup"). }
        iModIntro. iFrame "Hf Hg". iRight. iSplitR; [iExact "Hsup" |].
        iApply ("Hback" $! bs with "[//] Htail").
  Qed.

  (* ...and the short chunk's, at the same packaging.  The offset advances
     by the COUNT [r] and the carrier moves to [x = 1]: the loop's last
     step. *)
  Lemma fw_st_fire_part (om : offmode) (γfs : fs_names) (E : coPset)
      (i : Z) (γo : gname) (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd)
      (n : Z) (Q : nat -> iProp Σ) (t : Z) (p : nat)
      (off r : nat) (bs bs0 : list (bv 8)) (nl : nat) (nd nd' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i nd' ->
    (0 < length bs)%nat ->
    (off <= length bs0)%nat ->
    (off + length bs <= MAXFILE * BSIZE)%nat ->
    (r <= length bs)%nat ->
    (length bs <= r + BSIZE)%nat ->
    fn_type nd <> 0 ->
    abs_row nd = MkAnode (AFile bs0) nl ->
    fn_type nd' <> 0 ->
    abs_row nd' = MkAnode (AFile (blk_splice off bs bs0)) nl ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat p)) (take r bs) ->
    Z.of_nat r < wchunk_at n p ->
    ((r < length bs)%nat -> wr_fail_why P ua (Z.to_nat n)) ->
    (wi_blocks off (Z.to_nat (wchunk_at n p)) = 1%nat -> r = 0%nat) ->
    (0 <= t)%Z -> (t < n)%Z -> t = FW_MAX * Z.of_nat p ->
    ftop_inv γfs -∗ app_inv γfs -∗
    fw_au_st om (fs_gamma_L γfs) i γo P n M ua Q t p 0%nat -∗
    top_frag (fs_gamma_L γfs) i nd -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i nd'
      ∗ off_link γo (Z.of_nat (off + r))
      ∗ fw_au_st om (fs_gamma_L γfs) i γo P n M ua Q t p 1%nat.
  Proof using .
    intros HE Hloc Hpos Hoff Hcap Hr Hgap Hnz Habs Hnz' Habs' Hby Hshort Hwhy
           Hsb1 Ht Htn Htie.
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    iIntros "#Hi #Hai Hst Hf Hg".
    rewrite /fw_au_st.
    destruct om.
    - iDestruct "Hst" as "[#Hsup Hau]".
      iDestruct (fw_au_raw_spend_part (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie
                   with "Hau") as "[Hcm Hback]".
      iMod (wrf_apart_fire_gen γfs E i γo M ua P n p _ True off r bs bs0 nl nd nd'
              HE Hloc Hpos Hoff Hcap Hr Hgap Hnz Habs Hnz' Habs' Hby Hshort
              Hwhy Hsb1
              with "Hi Hai [] Hcm Hf Hg") as "(Hf & Hg & _ & Htail)".
      { iApply (fw_supply_off E γo off r Hfoff with "Hsup"). }
      iModIntro. iFrame "Hf Hg". iSplitR; [iExact "Hsup" |].
      iApply ("Hback" with "Htail").
    - iDestruct "Hst" as "[Hau | [#Hsup Hau]]".
      + iDestruct (fw_au_adv_spend_part (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie
                     with "Hau") as "[Hcm Hback]".
        iMod (wrf_apart_fire_adv γfs E i γo M ua P n p _ off r bs bs0 nl nd nd'
                HE Hloc Hpos Hoff Hcap Hr Hgap Hnz Habs Hnz' Habs' Hby Hshort
                Hwhy Hsb1
                with "Hi Hai Hcm Hf Hg") as "(Hf & Hg & Htail)".
        iModIntro. iFrame "Hf Hg". iLeft.
        iApply ("Hback" with "Htail").
      + iDestruct (fw_au_raw_spend_part (fs_gamma_L γfs) i γo P n M ua Q t p Ht Htn Htie
                     with "Hau") as "[Hcm Hback]".
        iMod (wrf_apart_fire_gen γfs E i γo M ua P n p _ True off r bs bs0 nl nd nd'
                HE Hloc Hpos Hoff Hcap Hr Hgap Hnz Habs Hnz' Habs' Hby Hshort
                Hwhy Hsb1
                with "Hi Hai [] Hcm Hf Hg") as "(Hf & Hg & _ & Htail)".
        { iApply (fw_supply_off E γo off r Hfoff with "Hsup"). }
        iModIntro. iFrame "Hf Hg". iRight. iSplitR; [iExact "Hsup" |].
        iApply ("Hback" with "Htail").
  Qed.

End FilewriteChain.

Global Typeclasses Opaque fw_au_raw.
Global Typeclasses Opaque fw_au_adv.
Global Typeclasses Opaque fw_supply.

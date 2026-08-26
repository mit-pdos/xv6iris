(* ProofBreadParts.v -- the two pieces of bread's proof that are NOT a step of
   its instruction chain, factored out so the chain file stays about control
   flow.  (ProofBread.v is the chain; this file is its vocabulary.)

   (2) THE GHOST STEPS over [BioInv.bcache_scan] (the OPEN form of the bcache
       resource) and (3) the (c)-SWAPS of the recycle block -- the pool
       exchange, the eviction, the mid-recycle window -- live below, so
       ProofBread.v's recycle block is three [wp_sw_au_s_sconf]s over three
       one-line lemma applications.

   (1) The two MASK-CARRYING width-4 memory leaves no longer live here.
       bread opens the per-buffer escrow around four single instructions --
       the three field stores of the recycle block ([sw s2,8(s1)] /
       [sw s3,12(s1)] / [sw zero,0(s1)]) and the [lw a5,0(s1)] of the tail's
       checkout swap -- so each needs the cell produced and returned INSIDE
       the engine callback's own mask.  Those two wrappers are
       [WpAu4.wp_lw_au_s_sconf] / [wp_sw_au_s_sconf]: they were first proved
       here, but a proof file may not import a proof file, so the five
       icache proofs each restated them verbatim.  They now sit in their own
       definitional file, [WpAu4.v], which this file imports.  Only the
       ESCROW-shaped glue below is bread's own.                              *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import VcGen.
Require Import RiscvExtras.
Require Import BufOwn BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (1) The escrow, in the raw [inv] shape [iInv] recognizes.             *)
(*      (The mask-carrying width-4 load/store are [WpAu4.v]'s now.)       *)
(* ===================================================================== *)

Section BreadEscrowLeaves.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the escrow, in the raw [inv] shape [iInv] recognizes *)
  Lemma buf_escrow_inv (bn : bio_names) (V : bio_view Σ) (k : nat) :
    buf_escrow bn V k -∗ inv bioN (buf_escrow_body bn V k).
  Proof. iIntros "H". iExact "H". Qed.

End BreadEscrowLeaves.

(* ===================================================================== *)
(*  (2) Fraction arithmetic, over Qp VARIABLES.                           *)
(*                                                                        *)
(*  Stated at the top level so no solver ever runs inside the WP context   *)
(*  (claude-notes/optimization.md); these are ProofBpin's [bp_*] family,   *)
(*  which bread's hit path needs at the same shapes.                      *)
(* ===================================================================== *)

Lemma bd_quarter_half : ((1/4) + (1/4))%Qp = (1/2)%Qp.
Proof. compute_done. Qed.

Lemma bd_half_le_one : ((1/2) ≤ 1)%Qp.
Proof. compute_done. Qed.

Lemma bd_quarter_valid : ✓ (1/4)%Qp.
Proof. apply frac_valid. compute_done. Qed.

Lemma bd_div2_le (q : Qp) : (q/2 ≤ q)%Qp.
Proof. pose proof (Qp.le_add_l (q/2) (q/2)) as H. rewrite Qp.div_2 in H. exact H. Qed.

(* the minted fraction is legal: the entry's outstanding total only ever
   grows toward the 1/2 the bcache resource started with. *)
Lemma bd_incr_valid (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ✓ (qt + qr/2)%Qp.
Proof.
  intro Htie. apply frac_valid.
  etrans; [| exact bd_half_le_one].
  rewrite -Htie. apply Qp.add_le_mono; [reflexivity | apply bd_div2_le].
Qed.

(* and the slot's cell tie survives the mint *)
Lemma bd_incr_tie (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ((qt + qr/2) + qr/2)%Qp = (1/2)%Qp.
Proof. intro Htie. rewrite -Qp.add_assoc Qp.div_2. exact Htie. Qed.

(* ===================================================================== *)
(*  (3) The two ghost steps over [BioInv.bcache_scan] -- the OPEN form of  *)
(*  the bcache resource (defined there, next to the closed one, because     *)
(*  the scans must carry it or the devs/bnos exit tie dies).                *)
(* ===================================================================== *)

Section BreadScan.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{XI : CurCtx}.

  (* the one-slot update of the scan's [devs] / [bnos] functions.  Named (not
     an inline [fun j => if decide (j = k) then v else f j]) because the
     recycle's pool exchange, the injectivity re-establishment and the
     [bio_slots_acc] update wand all mention it, and an inline copy makes
     every one of those unify against a different beta-redex. *)
  Definition bfun_upd (f : nat -> mword 32) (k : nat) (v : mword 32)
    : nat -> mword 32 :=
    fun j => if decide (j = k) then v else f j.

  Lemma bfun_upd_eq (f : nat -> mword 32) (k : nat) (v : mword 32) :
    bfun_upd f k v k = v.
  Proof. rewrite /bfun_upd. case_decide as Hd; [reflexivity | congruence]. Qed.

  Lemma bfun_upd_ne (f : nat -> mword 32) (k : nat) (v : mword 32) (j : nat) :
    j ≠ k -> bfun_upd f k v j = f j.
  Proof. intro Hj. rewrite /bfun_upd. case_decide as Hd; [congruence | reflexivity]. Qed.

  (* [uint] IS [bv_unsigned] (RiscvExtras.uint_unsigned's proof, at width 32
     -- restated here rather than pulling UserBits in for one equation), so a
     blockno compare on [uint] is a compare on the word. *)
  Lemma bd_uint32 (a : mword 32) : uint a = bv_unsigned a.
  Proof.
    pose proof (bv_unsigned_in_range _ a) as Hr.
    unfold uint, get_word, MachineWord.MachineWord.word_to_N.
    rewrite Z2N.id; [ reflexivity | lia ].
  Qed.

  Lemma bd_uint32_inj (a b : mword 32) : uint a = uint b -> a = b.
  Proof. rewrite !bd_uint32. intro H. by apply bv_eq. Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE MISS FACT, out of the forward scan's exit tie.                  *)
  (*                                                                     *)
  (*  The scan's per-slot exit fact is the negation of the code's [&&]    *)
  (*  -- [devs i ≠ dev \/ bnos i ≠ bno] -- which alone does NOT say the   *)
  (*  block is uncached.  The scan's DEV PIN closes it: a slot claiming a *)
  (*  covered block is on the view's device, and the request is too, so   *)
  (*  the dev disjunct is impossible at the requested block and the       *)
  (*  blockno disjunct is what remains.                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma bd_miss_of_tie (V : bio_view Σ) (devs bnos : nat -> mword 32)
      (D B : mword 32) :
    D = bv_dev V ->
    uint B ∈ bv_cov V ->
    (forall i, (i < NBUF)%nat -> uint (bnos i) ∈ bv_cov V -> devs i = bv_dev V) ->
    (forall i, (i < NBUF)%nat -> ¬ (devs i = D /\ bnos i = B)) ->
    forall j, (j < NBUF)%nat -> uint (bnos j) ≠ uint B.
  Proof.
    intros HD Hcov Hpin Htie j Hj Heq.
    apply (Htie j Hj). split; [| exact (bd_uint32_inj _ _ Heq)].
    rewrite (Hpin j Hj ltac:(rewrite Heq; exact Hcov)) HD. reflexivity.
  Qed.

  (* the DEV PIN survives the recycle: slot k's new dev IS the view's
     device (bread's spec premise), every other slot is untouched. *)
  Lemma bd_devpin_upd (V : bio_view Σ) (devs bnos : nat -> mword 32)
      (k : nat) (D B : mword 32) :
    D = bv_dev V ->
    (forall k', (k' < NBUF)%nat -> uint (bnos k') ∈ bv_cov V ->
       devs k' = bv_dev V) ->
    forall k', (k' < NBUF)%nat ->
      uint (bfun_upd bnos k B k') ∈ bv_cov V ->
      bfun_upd devs k D k' = bv_dev V.
  Proof.
    intros HD Hpin k' Hk' Hcov.
    destruct (decide (k' = k)) as [->|Hne].
    - rewrite bfun_upd_eq. exact HD.
    - rewrite (bfun_upd_ne devs k D k' Hne).
      rewrite (bfun_upd_ne bnos k B k' Hne) in Hcov.
      exact (Hpin k' Hk' Hcov).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The covered-blockno INJECTIVITY, re-established at the recycle.     *)
  (*                                                                     *)
  (*  Slot k's claim moves to the requested block [B]; every OTHER slot's *)
  (*  claim is untouched, and the forward scan's exit says none of them   *)
  (*  claims [B] -- so the only new pair to check is (k, j), which that   *)
  (*  same miss fact kills.  Pure, and stated over variables so no solver *)
  (*  ever runs inside the WP context.                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma bd_inj_upd (V : bio_view Σ) (bnos : nat -> mword 32)
      (k : nat) (B : mword 32) :
    (k < NBUF)%nat ->
    uint B ∈ bv_cov V ->
    (forall jj, (jj < NBUF)%nat -> uint (bnos jj) ≠ uint B) ->
    (forall k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
       uint (bnos k1) ∈ bv_cov V ->
       uint (bnos k1) = uint (bnos k2) -> k1 = k2) ->
    forall k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
      uint (bfun_upd bnos k B k1) ∈ bv_cov V ->
      uint (bfun_upd bnos k B k1) = uint (bfun_upd bnos k B k2) -> k1 = k2.
  Proof.
    intros Hk HcovB Hmiss Hinj k1 k2 Hk1 Hk2 Hcov Heq.
    destruct (decide (k1 = k)) as [->|Hn1]; destruct (decide (k2 = k)) as [->|Hn2].
    - reflexivity.
    - exfalso. rewrite bfun_upd_eq (bfun_upd_ne _ _ _ _ Hn2) in Heq.
      exact (Hmiss k2 Hk2 (eq_sym Heq)).
    - exfalso. rewrite bfun_upd_eq (bfun_upd_ne _ _ _ _ Hn1) in Heq.
      exact (Hmiss k1 Hk1 Heq).
    - rewrite (bfun_upd_ne _ _ _ _ Hn1) (bfun_upd_ne _ _ _ _ Hn2) in Heq.
      rewrite (bfun_upd_ne _ _ _ _ Hn1) in Hcov.
      exact (Hinj k1 k2 Hk1 Hk2 Hcov Heq).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The HIT path's refcnt++.                                           *)
  (*                                                                     *)
  (*  ProofBpin's ghost recipe, restated over the OPEN form so the minted *)
  (*  reference comes back at the RECORDED [devs k] / [bnos k] -- which   *)
  (*  is exactly what the scan's compare has just pinned to the caller's  *)
  (*  [dev] / [bno].  Both arms of [bio_slot_res] are joined BEFORE the   *)
  (*  load, as one [∃ cw, refcnt ↦ cw ∗ (refcnt ↦ incr32 cw ==∗ …)], so   *)
  (*  the three instructions of the critical section are proved once over  *)
  (*  an abstract count word.                                            *)
  (*                                                                     *)
  (*  The None arm is REAL on this path: a parked idle buffer whose        *)
  (*  dev/blockno still match a previous user's key is a legitimate hit,   *)
  (*  and then the mint is the FIRST reference (1/4 off the bcache half)   *)
  (*  rather than a split of the retainder.                               *)
  (*                                                                     *)
  (*  Neither the pool nor the injectivity conjunct moves here: [bnos] is  *)
  (*  unchanged, so both ride through untouched.                          *)
  (* ------------------------------------------------------------------ *)
  Definition incr32 (cw : mword 32) : mword 32 :=
    trunc32 (sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)).

  Lemma incr32_pos (z : Z) :
    (0 <= z)%Z -> (z + 1 < 2 ^ 31)%Z ->
    incr32 (mword_of_int z : mword 32) = (mword_of_int (z + 1) : mword 32).
  Proof. intros H0 H1. rewrite /incr32. by apply moi32_storeval_succ. Qed.

  Lemma bcache_scan_incr (bn : bio_names) (V : bio_view Σ) M ord devs bnos (k : nat) :
    (k < NBUF)%nat ->
    bcache_scan bn V M ord devs bnos -∗ bslot -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      (brefcnt k ↦₄ (incr32 cw) ==∗
         bcache_res bn V ∗ ∃ q : Qp, bref bn k q (devs k) (bnos k)).
  Proof.
    iIntros (Hk) "Hscan Hbslot".
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (bio_slots_acc bn M devs bnos k Hk with "Hslots") as "[Hslot Hback]".
    destruct (M !! k) as [[qt cnt]|] eqn:HMk.
    - (* ---- busy buffer: halve the retained share ---- *)
      iEval (rewrite /bio_slot_res HMk) in "Hslot".
      iDestruct "Hslot" as "(%Hcnt & Hcell & Hfd & Hqr)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iDestruct (bslots_no_overflow with "Hsauth Hfd") as %[Hn1 Hn2].
      iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int (Z.pos cnt) : mword 32)
                     = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
      { rewrite (incr32_pos (Z.pos cnt) ltac:(lia)
                   ltac:(pose proof Hn2 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
        f_equal. rewrite Pos2Z.inj_succ. lia. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_incr_step bn M k qt cnt (qr/2)%Qp HMk (bd_incr_valid qt qr Htie)
              with "Hauth") as "[Hauth Htok]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hbno". }
      assert (Hsucc : Pos.to_nat (Pos.succ cnt) = (Pos.to_nat cnt + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res bn (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) k (devs k) (bnos k))
        with "[Hcell Hfd Hbslot Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res lookup_insert.
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
        iFrame "Hcell".
        iSplitL "Hfd Hbslot".
        { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
        iExists (qr/2)%Qp. iSplitR.
        { iPureIntro. exact (bd_incr_tie qt qr Htie). }
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hdev2 Hbno2".
      + iApply (bcache_scan_to_res bn V (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) ord devs bnos).
        rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + iExists (qr/2)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
    - (* ---- parked idle buffer with a matching key: the FIRST reference ---- *)
      iEval (rewrite /bio_slot_res HMk) in "Hslot".
      iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
      { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
              with "Hauth") as "[Hauth Htok]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) k (devs k) (bnos k))
        with "[Hcell Hbslot Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res lookup_insert.
        iSplitR. { iPureIntro. vm_compute. reflexivity. }
        iFrame "Hcell".
        iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
        iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hdev2 Hbno2".
      + iApply (bcache_scan_to_res bn V (<[k := ((1/4)%Qp, 1%positive)]> M) ord devs bnos).
        rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + iExists (1/4)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The RECYCLE path.                                                  *)
  (*                                                                     *)
  (*  At [M !! k = None] the slot holds the refcnt cell at 0 and the      *)
  (*  bcache HALF of dev/blockno.  The three field stores need those two  *)
  (*  halves joined with the escrow's (each store opens [buf_escrow]      *)
  (*  around itself), so the accessor hands them OUT together with the    *)
  (*  authority -- which the escrow open needs, since [M !! k = None] is  *)
  (*  what refutes the checked-out arm ([BioInv.escrow_open_free]).        *)
  (*                                                                     *)
  (*  NEW over the physical layer: the UNCACHED POOL comes out too (the   *)
  (*  blockno store performs the one-shot exchange, which is the instant  *)
  (*  [bnos] -- the function the pool's domain subtracts -- changes), and *)
  (*  the covered-blockno injectivity is handed out as a PURE fact (the   *)
  (*  eviction deposit's uniqueness premise) and re-established for the   *)
  (*  updated [bnos] from the forward scan's miss fact.                   *)
  (*                                                                     *)
  (*  The closing wand takes the three cells back AT THE NEW VALUES and   *)
  (*  performs the [refcnt = 1] ghost step in one go: mint the chain's     *)
  (*  first reference at 1/4 off the returned half, retain 1/4 (the tie    *)
  (*  1/4 + 1/4 = 1/2), and absorb the caller's [bslot].                  *)
  (* ------------------------------------------------------------------ *)
  Lemma bcache_scan_recycle (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (ord : list nat)
      (devs bnos : nat -> mword 32) (k : nat) (D B : mword 32) :
    (k < NBUF)%nat ->
    M !! k = None ->
    D = bv_dev V ->
    uint B ∈ bv_cov V ->
    (* the forward scan's exit tie, at EVERY slot (the negation of the
       code's [b->dev == dev && b->blockno == blockno]) *)
    (forall i, (i < NBUF)%nat -> ¬ (devs i = D /\ bnos i = B)) ->
    bcache_scan bn V M ord devs bnos -∗ bslot -∗
    (* the two pure facts the escrow's blockno store needs, read off the
       scan's own conjuncts: the block really is uncached, and the evicted
       block is claimed by no other slot *)
    ⌜(forall jj, (jj < NBUF)%nat -> uint (bnos jj) ≠ uint B)
     /\ (uint (bnos k) ∈ bv_cov V ->
           forall j, (j < NBUF)%nat -> j ≠ k -> uint (bnos j) ≠ uint (bnos k))⌝ ∗
    own (bn_auth bn) (● M) ∗
    brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} (devs k) ∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k) ∗
    bio_pool V bnos ∗
    (own (bn_auth bn) (● M) -∗
     brefcnt k ↦₄ (mword_of_int 1 : mword 32) -∗
     b_dev (bpa k) ↦₄{DfracOwn (1/2)} D -∗
     b_blockno (bpa k) ↦₄{DfracOwn (1/2)} B -∗
     bio_pool V (bfun_upd bnos k B) ==∗
     bcache_res bn V ∗ bref bn k (1/4)%Qp D B).
  Proof.
    iIntros (Hk HMk HD HcovB Htie) "Hscan Hbslot".
    rewrite /bcache_scan.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    pose proof (bd_miss_of_tie V devs bnos D B HD HcovB Hdevpin Htie) as Hmiss.
    iDestruct (bio_slots_acc bn M devs bnos k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res HMk) in "Hslot".
    iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
    iSplitR.
    { iPureIntro. split; [exact Hmiss|].
      intros Hcov j Hj Hjk Heq. apply Hjk. symmetry.
      exact (Hinj k j Hk Hj Hcov (eq_sym Heq)). }
    iFrame "Hauth Hcell Hdev Hbno Hpool".
    iIntros "Hauth Hcell Hdev Hbno Hpool".
    set (dv := D).
    iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
            with "Hauth") as "[Hauth Htok]".
    iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} dv ∗
             b_dev (bpa k) ↦₄{DfracOwn (1/4)} dv)%I
      with "[Hdev]" as "[Hdev1 Hdev2]".
    { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hdev". }
    iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} B ∗
             b_blockno (bpa k) ↦₄{DfracOwn (1/4)} B)%I
      with "[Hbno]" as "[Hbno1 Hbno2]".
    { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
    iEval (rewrite /bslot) in "Hbslot".
    iAssert (bio_slot_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) k dv B)
      with "[Hcell Hbslot Hdev1 Hbno1]" as "Hslot".
    { rewrite /bio_slot_res lookup_insert.
      iSplitR. { iPureIntro. vm_compute. reflexivity. }
      iFrame "Hcell".
      iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
      iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
      iFrame "Hdev1 Hbno1". }
    iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M)
                 (bfun_upd devs k dv) (bfun_upd bnos k B)
                 with "[%] [Hslot]") as "Hslots".
    { intros j Hj. split_and!;
        [ rewrite lookup_insert_ne; [reflexivity | congruence]
        | exact (bfun_upd_ne devs k dv j Hj)
        | exact (bfun_upd_ne bnos k B j Hj) ]. }
    { rewrite (bfun_upd_eq devs k dv) (bfun_upd_eq bnos k B). iExact "Hslot". }
    iModIntro. iSplitR "Htok Hdev2 Hbno2".
    - iApply (bcache_scan_to_res bn V (<[k := ((1/4)%Qp, 1%positive)]> M) ord
                (bfun_upd devs k dv) (bfun_upd bnos k B)).
      rewrite /bcache_scan. iFrame "Hauth Hsauth".
      iSplitR.
      { iPureIntro. intros j Hj.
        destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
        apply Hdom. by rewrite lookup_insert_ne in Hj. }
      iSplitR; [iPureIntro; exact Hord|].
      iSplitR.
      { iPureIntro. exact (bd_inj_upd V bnos k B Hk HcovB Hmiss Hinj). }
      iSplitR.
      { iPureIntro. exact (bd_devpin_upd V devs bnos k dv B HD Hdevpin). }
      iFrame "Hlru Hpool Hslots".
    - rewrite /bref. iFrame "Htok Hdev2 Hbno2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (4) The (c) swap: the recycle block's THREE field rewrites.         *)
  (*                                                                     *)
  (*  Each of [sw s2,8(s1)] / [sw s3,12(s1)] / [sw zero,0(s1)] opens       *)
  (*  [buf_escrow] around ITSELF, so no bundle is carried across an        *)
  (*  instruction boundary -- which is what makes the recycler-vs-hit-     *)
  (*  thread race safe for free (whoever wins the sleeplock takes the       *)
  (*  parked bundle; whoever sees valid = 0 at the tail does the read).     *)
  (*                                                                     *)
  (*  The three stores are NOT symmetric any more (design/fs-log.md, the   *)
  (*  A3 bullet).  The dev store re-parks a NORMAL arm (the payload only    *)
  (*  has to be re-aimed at the new dev value, which is legal because a     *)
  (*  covered payload pins its dev to [bv_dev V] and the request is on      *)
  (*  that device).  The blockno store OPENS the mid-recycle window: it     *)
  (*  evicts the old payload into the pool, exchanges the pool bundles and  *)
  (*  re-closes with cells only, the dev cell FULL and the recycle token    *)
  (*  in the recycler's hand.  The valid store closes the window.           *)
  (*                                                                     *)
  (*  Each lemma is used INSIDE one [iInv] of [buf_escrow] (mask           *)
  (*  ⊤ ∖ ↑minstretN ∖ ↑bioN) wrapped around one [wp_sw_au_s_sconf].       *)
  (* ------------------------------------------------------------------ *)

  (* re-aiming a parked payload at a new dev value.  A COVERED payload
     pins its dev to the view's device, and the recycler stores exactly
     that device (bread's spec premise [dev = bv_dev V]), so the two
     values coincide and the payload re-forms verbatim; an uncovered
     payload is [emp] on both sides.  (The dirty arm's [bref] mentions the
     dev value too -- it re-forms for the same reason.) *)
  Lemma bd_pay_retarget (bn : bio_names) (V : bio_view Σ) (k : nat)
      (v : bool) (d1 d2 bno : mword 32) (bs : list (bv 8)) :
    d2 = bv_dev V ->
    buf_pay bn V k v d1 bno bs -∗ buf_pay bn V k v d2 bno bs.
  Proof.
    iIntros (Hd2) "H". rewrite /buf_pay.
    case_decide as Hc; [| iExact "H"].
    iDestruct "H" as "[%Hd1 H]". subst d1 d2.
    iSplitR; [done|]. iExact "H".
  Qed.

  (* dev: escrow half + slot half -> full; re-park at the stored value *)
  Lemma escrow_recyc_dev (bn : bio_names) (V : bio_view Σ) (k : nat)
      (M : gmap nat (Qp * positive)) (devr dnew : mword 32) :
    M !! k = None ->
    dnew = bv_dev V ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn V k -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} devr -∗
    own (bn_auth bn) (● M) ∗
    b_dev (bpa k) ↦₄ devr ∗
    (b_dev (bpa k) ↦₄ dnew -∗
       buf_escrow_body bn V k ∗ b_dev (bpa k) ↦₄{DfracOwn (1/2)} dnew).
  Proof.
    iIntros (HMk Hdnew) "Hauth Hbody Hslot".
    iDestruct (escrow_open_free bn V k M devr HMk with "Hauth Hslot Hbody")
      as "(Hauth & Hslot & Hpark & Hclose)".
    iDestruct "Hpark" as (v de bno bs) "(Hvld & Hdev & Hbuf & Hpay & Hbmid)".
    iDestruct (word4_pointsto_agree with "Hslot Hdev") as %Heq. subst de.
    iFrame "Hauth".
    iSplitL "Hslot Hdev".
    { iApply (word4_pointsto_half_join with "Hslot Hdev"). }
    iIntros "Hfull".
    iDestruct (word4_pointsto_half_split with "Hfull") as "[Hd1 Hd2]".
    iSplitR "Hd2"; [| iExact "Hd2"].
    iApply "Hclose". rewrite /buf_parked.
    iExists v, dnew, bno, bs.
    iDestruct (bd_pay_retarget bn V k v devr dnew bno bs Hdnew with "Hpay") as "Hpay".
    iFrame "Hvld Hd1 Hbuf Hpay Hbmid".
  Qed.

  (* blockno: the escrow's half lives inside [buf_own]; joining it with the
     slot's makes the cell storable.  This is where the CACHE MEMBERSHIP
     moves, so it is also where the pool exchange happens -- the evicted
     block's payload is read out with [buf_pay_evict] (the authority kills
     the dirty arm: only clean, disk-agreeing content ever leaves the
     cache) and deposited, and the requested block's bundle is withdrawn.
     The escrow re-closes as the MID window: cells only, the dev cell FULL
     (the bcache-retained half joined in), the recycle token OUT. *)
  Lemma escrow_recyc_bno (bn : bio_names) (V : bio_view Σ) (k : nat)
      (M : gmap nat (Qp * positive)) (bnos : nat -> mword 32)
      (devr B : mword 32) :
    M !! k = None ->
    (k < NBUF)%nat ->
    uint B ∈ bv_cov V ->
    (forall j, (j < NBUF)%nat -> uint (bnos j) ≠ uint B) ->
    (uint (bnos k) ∈ bv_cov V ->
       forall j, (j < NBUF)%nat -> j ≠ k -> uint (bnos j) ≠ uint (bnos k)) ->
    devr = bv_dev V ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn V k -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} devr -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k) -∗
    bio_pool V bnos -∗
    own (bn_auth bn) (● M) ∗
    b_blockno (bpa k) ↦₄ (bnos k) ∗
    (b_blockno (bpa k) ↦₄ B -∗
       buf_escrow_body bn V k ∗ bmid bn k ∗ pool_blk V (uint B) ∗
       b_blockno (bpa k) ↦₄{DfracOwn (1/2)} B ∗
       bio_pool V (bfun_upd bnos k B)).
  Proof.
    iIntros (HMk Hk HcovB Hmiss Huniq Hdevr) "Hauth Hbody Hdevr Hbno Hpool".
    iDestruct (escrow_open_free bn V k M devr HMk with "Hauth Hdevr Hbody")
      as "(Hauth & Hdevr & Hpark & _)".
    iDestruct "Hpark" as (v de bno bs) "(Hvld & Hdev & Hbuf & Hpay & Hbmid)".
    iDestruct (word4_pointsto_agree with "Hdevr Hdev") as %Heqd. subst de.
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno0 & Hdisk & %Hlen & Hdata)".
    iDestruct (word4_pointsto_agree with "Hbno Hbno0") as %Heqb. subst bno.
    iDestruct (buf_pay_evict bn V k M v devr (bnos k) bs HMk with "Hauth Hpay")
      as "[Hauth Hold]".
    iFrame "Hauth".
    iSplitL "Hbno Hbno0".
    { iApply (word4_pointsto_half_join with "Hbno Hbno0"). }
    iIntros "Hfull".
    iDestruct (word4_pointsto_half_split with "Hfull") as "[Hb1 Hb2]".
    (* the pool exchange, at the one instant [bnos] changes *)
    iDestruct (bio_pool_recycle V bnos (bfun_upd bnos k B) k (bnos k) B
                 Hk eq_refl (bfun_upd_eq bnos k B)
                 (fun j Hj => bfun_upd_ne bnos k B j Hj)
                 HcovB Hmiss Huniq with "Hpool") as "[HpoolB Hpoolback]".
    iDestruct ("Hpoolback" with "[Hold]") as "Hpool".
    { case_decide as Hc; [iDestruct "Hold" as "[_ $]" | done]. }
    (* and re-close as the mid-recycle window *)
    iDestruct (word4_pointsto_half_join with "Hdevr Hdev") as "Hdevfull".
    iSplitL "Hvld Hdevfull Hb1 Hdisk Hdata".
    { iApply (escrow_close_mid bn V k). rewrite /buf_mid.
      iExists (if v then (mword_of_int 1 : mword 32) else (mword_of_int 0 : mword 32)),
              B, bs.
      iSplitR. { iPureIntro. destruct v; [by right | by left]. }
      rewrite -Hdevr.
      iFrame "Hvld Hdevfull". rewrite /buf_own. iFrame "Hb1 Hdisk Hdata". done. }
    iFrame "Hbmid HpoolB Hb2 Hpool".
  Qed.

  (* valid: the recycle token refutes BOTH normal arms, so what comes out is
     the window this recycler itself parked -- with the dev cell FULL at the
     view's device, which is what lets the re-parked payload's dev pin (and
     the handle's dev half) be identified at all.  The stored 0 is what makes
     the arm INVALID, i.e. what hands the block's pool bundle -- withdrawn at
     the blockno store -- to WHOEVER wins the sleeplock race and does the
     fill.  The retained blockno half pins the window's block to [B]. *)
  Lemma escrow_recyc_valid (bn : bio_names) (V : bio_view Σ) (k : nat)
      (B : mword 32) :
    uint B ∈ bv_cov V ->
    bmid bn k -∗
    buf_escrow_body bn V k -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} B -∗
    pool_blk V (uint B) -∗
    (∃ vld : mword 32, b_valid (bpa k) ↦₄ vld) ∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} B ∗
    (b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗
       buf_escrow_body bn V k ∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} (bv_dev V)).
  Proof.
    iIntros (HcovB) "Hbmid Hbody Hbno Hpool".
    iDestruct (escrow_open_mid bn V k with "Hbmid Hbody")
      as "(Hbmid & Hmid & Hclose)".
    iDestruct "Hmid" as (vld bno bs) "(%Hpin & Hvld & Hdevfull & Hbuf)".
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno0 & Hdisk & %Hlen & Hdata)".
    iDestruct (word4_pointsto_agree with "Hbno Hbno0") as %Heqb. subst bno.
    iSplitL "Hvld"; [by iExists vld|].
    iFrame "Hbno".
    iIntros "Hvld".
    iDestruct (word4_pointsto_half_split with "Hdevfull") as "[Hd1 Hd2]".
    iSplitR "Hd2"; [| iExact "Hd2"].
    iAssert (buf_pay bn V k false (bv_dev V) B bs) with "[Hpool]" as "Hpay".
    { rewrite /buf_pay. case_decide as Hc; [| exfalso; exact (Hc HcovB)].
      iSplitR; [done|]. iExact "Hpool". }
    iApply "Hclose". rewrite /buf_parked.
    iExists false, (bv_dev V), B, bs. cbv iota.
    iFrame "Hvld Hd1 Hpay Hbmid".
    rewrite /buf_own. iFrame "Hbno0 Hdisk Hdata". done.
  Qed.

End BreadScan.

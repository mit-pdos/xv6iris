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

  (* v1 [bcache_scan_incr]/[bcache_scan_recycle] deleted (R2): their v2 twins
     over [bcache_scan2] are in [BreadScan2] below. *)

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
    iDestruct (ctx_word4_pointsto_agree with "Hslot Hdev") as %Heq. subst de.
    iFrame "Hauth".
    iSplitL "Hslot Hdev".
    { iApply (ctx_word4_pointsto_half_join with "Hslot Hdev"). }
    iIntros "Hfull".
    iDestruct (ctx_word4_pointsto_half_split with "Hfull") as "[Hd1 Hd2]".
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
    iDestruct (ctx_word4_pointsto_agree with "Hdevr Hdev") as %Heqd. subst de.
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno0 & Hdisk & %Hlen & Hdata)".
    iDestruct (ctx_word4_pointsto_agree with "Hbno Hbno0") as %Heqb. subst bno.
    iDestruct (buf_pay_evict bn V k M v devr (bnos k) bs HMk with "Hauth Hpay")
      as "[Hauth Hold]".
    iFrame "Hauth".
    iSplitL "Hbno Hbno0".
    { iApply (ctx_word4_pointsto_half_join with "Hbno Hbno0"). }
    iIntros "Hfull".
    iDestruct (ctx_word4_pointsto_half_split with "Hfull") as "[Hb1 Hb2]".
    (* the pool exchange, at the one instant [bnos] changes *)
    iDestruct (bio_pool_recycle V bnos (bfun_upd bnos k B) k (bnos k) B
                 Hk eq_refl (bfun_upd_eq bnos k B)
                 (fun j Hj => bfun_upd_ne bnos k B j Hj)
                 HcovB Hmiss Huniq with "Hpool") as "[HpoolB Hpoolback]".
    iDestruct ("Hpoolback" with "[Hold]") as "Hpool".
    { case_decide as Hc; [iDestruct "Hold" as "[_ $]" | done]. }
    (* and re-close as the mid-recycle window *)
    iDestruct (ctx_word4_pointsto_half_join with "Hdevr Hdev") as "Hdevfull".
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
    iDestruct (ctx_word4_pointsto_agree with "Hbno Hbno0") as %Heqb. subst bno.
    iSplitL "Hvld"; [by iExists vld|].
    iFrame "Hbno".
    iIntros "Hvld".
    iDestruct (ctx_word4_pointsto_half_split with "Hdevfull") as "[Hd1 Hd2]".
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

(* ====================================================================== *)
(*  R2 (A): the same two scan steps over the v2 payload ([bcache_scan2]),  *)
(*  with the TRANSIT BOX taking the resting content at refs 0 -> 1.        *)
(*  The recycler's three field stores are plain cell writes on cells this  *)
(*  thread holds (the None arm lives in the lock payload, not in an        *)
(*  invariant), so [escrow_recyc_*] have no v2 twins: the accessor hands   *)
(*  the FULL cells out and takes them back at the new values in one wand.  *)
(* ====================================================================== *)
Section BreadScan2.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{CID : CpuId} `{XI : CurCtx}.

  Local Lemma bd_pos1_lt : (Z.pos 1 < 2 ^ 31)%Z.
  Proof. vm_compute. reflexivity. Qed.

  (* the hit path's refcnt++ : the FIRST reference bumps the box (the
     resting content leaves the payload's None arm for the box's IN arm),
     a later one takes another fragment out of the box. *)
  Lemma bcache_scan2_incr (bn : bio_names) (V : bio_view Σ) M ord devs bnos
      (tl k : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗ bslot -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      (own_context cur_ctx -∗ brefcnt k ↦₄ (incr32 cw) ={E}=∗
         own_context cur_ctx ∗ bcache_res2 bn V cur_ctx ∗
         ∃ q : Qp, bref bn k q (devs k) (bnos k)).
  Proof.
    iIntros (HE Hk) "#Hbox #Hfl Hscan Hbslot".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    destruct (M !! k) as [[qt cnt]|] eqn:HMk.
    - (* ---- busy buffer: halve the retained share; another fragment ---- *)
      iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (%Hcnt & Hcell & Hfd & Hc & Hqr)]".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iDestruct (bslots_no_overflow with "Hsauth Hfd") as %[Hn1 Hn2].
      iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
      iIntros "Hrun Hcell".
      assert (Hinc : incr32 (mword_of_int (Z.pos cnt) : mword 32)
                     = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
      { rewrite (incr32_pos (Z.pos cnt) ltac:(lia)
                   ltac:(pose proof Hn2 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
        f_equal. rewrite Pos2Z.inj_succ. lia. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_incr_step bn M k qt cnt (qr/2)%Qp HMk (bd_incr_valid qt qr Htie)
              with "Hauth") as "[Hauth Htok]".
      iMod (box_ref_another bn V k cnt E HE with "Hbox Hc") as "[Hc Hfr]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -ctx_word4_pointsto_frac_split Qp.div_2. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -ctx_word4_pointsto_frac_split Qp.div_2. iExact "Hbno". }
      assert (Hsucc : Pos.to_nat (Pos.succ cnt) = (Pos.to_nat cnt + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res2 bn V (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) k
                 (devs k) (bnos k) tl cur_ctx)
        with "[Hregs Hcell Hfd Hbslot Hc Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert. iFrame "Hregs".
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
        iFrame "Hcell".
        iSplitL "Hfd Hbslot".
        { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
        iSplitL "Hc". { rewrite -Pos.add_1_r. iExact "Hc". }
        iExists (qr/2)%Qp. iSplitR.
        { iPureIntro. exact (bd_incr_tie qt qr Htie). }
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iFrame "Hrun". iSplitR "Htok Hfr Hdev2 Hbno2".
      + iApply (bcache_res2_fold bn V (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) ord devs bnos tl).
        iFrame "Hfl". rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + iExists (qr/2)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
        iDestruct "Hfr" as (rb) "(Hfr & _ & #Hllb)". iExists rb. iFrame "Hfr Hllb".
    - (* ---- idle buffer with a matching key: the FIRST reference BUMPS ---- *)
      iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (Hcell & Hc & Hcont)]".
      iDestruct "Hcont" as (v bs) "(Hvld & Hdev & Hbuf & Hbno & Hpay)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iIntros "Hrun Hcell".
      assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
      { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
              with "Hauth") as "[Hauth Htok]".
      (* the dev cell: the bundle's half, then the bcache half in quarters *)
      iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdevb Hdevs]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k))%I
        with "[Hdevs]" as "[Hdev1 Hdev2]".
      { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hdevs". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
      (* the bundle leaves the payload for the box *)
      iMod (box_swap_bump bn V k cur_ctx E HE with "Hbox Hrun Hc [Hvld Hdevb Hbuf Hpay]")
        as "(Hrun & Hc & Hfr)".
      { rewrite /buf_bundle. iExists v, (devs k), (bnos k), bs. iFrame "Hvld Hdevb Hbuf Hpay". }
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res2 bn V (<[k := ((1/4)%Qp, 1%positive)]> M) k (devs k) (bnos k) tl cur_ctx)
        with "[Hregs Hcell Hbslot Hc Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert. iFrame "Hregs".
        iSplitR. { iPureIntro. exact bd_pos1_lt. }
        iFrame "Hcell".
        iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
        iSplitL "Hc". { change (Pos.to_nat 1) with 1%nat. iExact "Hc". }
        iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iFrame "Hrun". iSplitR "Htok Hfr Hdev2 Hbno2".
      + iApply (bcache_res2_fold bn V (<[k := ((1/4)%Qp, 1%positive)]> M) ord devs bnos tl).
        iFrame "Hfl". rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + iExists (1/4)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
        iDestruct "Hfr" as (rb) "(Hfr & _ & #Hllb)". iExists rb. iFrame "Hfr Hllb".
  Qed.

  (* the RECYCLE path: the idle slot's content cells come out FULL (the
     bcache half joined with the bundle's), the closing wand takes them
     back at the recycler's values, evicts the old payload into the pool,
     withdraws the new block's bundle, and BUMPS the box with the (invalid)
     bundle at [refcnt = 1]. *)
  Lemma bcache_scan2_recycle (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (Qp * positive)) (ord : list nat)
      (devs bnos : nat -> mword 32) (tl k : nat) (D B : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    M !! k = None ->
    D = bv_dev V ->
    uint B ∈ bv_cov V ->
    (forall i, (i < NBUF)%nat -> ¬ (devs i = D /\ bnos i = B)) ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗ bslot -∗
    brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
    (∃ vld : mword 32, b_valid (bpa k) ↦₄ vld) ∗
    b_dev (bpa k) ↦₄ (devs k) ∗
    b_blockno (bpa k) ↦₄ (bnos k) ∗
    (own_context cur_ctx -∗
     brefcnt k ↦₄ (mword_of_int 1 : mword 32) -∗
     b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗
     b_dev (bpa k) ↦₄ D -∗
     b_blockno (bpa k) ↦₄ B ={E}=∗
     own_context cur_ctx ∗ bcache_res2 bn V cur_ctx ∗ bref bn k (1/4)%Qp D B).
  Proof.
    iIntros (HE Hk HMk HD HcovB Htie) "#Hbox #Hfl Hscan Hbslot".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    pose proof (bd_miss_of_tie V devs bnos D B HD HcovB Hdevpin Htie) as Hmiss.
    assert (Huniq : uint (bnos k) ∈ bv_cov V ->
              forall j, (j < NBUF)%nat -> j ≠ k -> uint (bnos j) ≠ uint (bnos k)).
    { intros Hcov j Hj Hjk Heq. apply Hjk. symmetry.
      exact (Hinj k j Hk Hj Hcov (eq_sym Heq)). }
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
    iDestruct "Hslot" as "[Hregs (Hcell & Hc & Hcont)]".
    iDestruct "Hcont" as (v bs) "(Hvld & Hdev & Hbuf & Hbno & Hpay)".
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno0 & Hdisk & %Hlen & Hdata)".
    iDestruct (ctx_word4_pointsto_half_join with "Hbno Hbno0") as "Hbnofull".
    iFrame "Hcell Hdev Hbnofull".
    iSplitL "Hvld". { by iExists _. }
    iIntros "Hrun Hcell Hvld Hdev Hbno".
    (* the old payload leaves for the pool; the new block's bundle comes out *)
    iDestruct (buf_pay_evict bn V k M v (devs k) (bnos k) bs HMk with "Hauth Hpay")
      as "[Hauth Hold]".
    iDestruct (bio_pool_recycle V bnos (bfun_upd bnos k B) k (bnos k) B
                 Hk eq_refl (bfun_upd_eq bnos k B)
                 (fun j Hj => bfun_upd_ne bnos k B j Hj)
                 HcovB Hmiss Huniq with "Hpool") as "[HpoolB Hpoolback]".
    iDestruct ("Hpoolback" with "[Hold]") as "Hpool".
    { case_decide as Hc; [iDestruct "Hold" as "[_ $]" | done]. }
    iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
            with "Hauth") as "[Hauth Htok]".
    (* the cells at the new values: the bundle's shares and the bcache quarters *)
    iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdevb Hdevs]".
    iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} D ∗ b_dev (bpa k) ↦₄{DfracOwn (1/4)} D)%I
      with "[Hdevs]" as "[Hdev1 Hdev2]".
    { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hdevs". }
    iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbnob Hbnos]".
    iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} B ∗ b_blockno (bpa k) ↦₄{DfracOwn (1/4)} B)%I
      with "[Hbnos]" as "[Hbno1 Hbno2]".
    { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hbnos". }
    iAssert (buf_pay bn V k false D B bs) with "[HpoolB]" as "Hpay".
    { rewrite /buf_pay. case_decide as Hc; [| exfalso; exact (Hc HcovB)].
      iSplitR; [by iPureIntro|]. iExact "HpoolB". }
    (* the (invalid) bundle enters the box *)
    iMod (box_swap_bump bn V k cur_ctx E HE
            with "Hbox Hrun Hc [Hvld Hdevb Hbnob Hdisk Hdata Hpay]")
      as "(Hrun & Hc & Hfr)".
    { rewrite /buf_bundle. iExists false, D, B, bs. cbv iota.
      iFrame "Hvld Hdevb Hpay". rewrite /buf_own. iFrame "Hbnob Hdisk Hdata". done. }
    iEval (rewrite /bslot) in "Hbslot".
    iAssert (bio_slot_res2 bn V (<[k := ((1/4)%Qp, 1%positive)]> M) k D B tl cur_ctx)
      with "[Hregs Hcell Hbslot Hc Hdev1 Hbno1]" as "Hslot".
    { rewrite /bio_slot_res2 lookup_insert. iFrame "Hregs".
      iSplitR. { iPureIntro. exact bd_pos1_lt. }
      iFrame "Hcell".
      iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
      iSplitL "Hc". { change (Pos.to_nat 1) with 1%nat. iExact "Hc". }
      iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
      iFrame "Hdev1 Hbno1". }
    iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M)
                 (bfun_upd devs k D) (bfun_upd bnos k B)
                 with "[%] [Hslot]") as "Hslots".
    { intros j Hj. split_and!;
        [ rewrite lookup_insert_ne; [reflexivity | congruence]
        | exact (bfun_upd_ne devs k D j Hj)
        | exact (bfun_upd_ne bnos k B j Hj) ]. }
    { rewrite (bfun_upd_eq devs k D) (bfun_upd_eq bnos k B). iExact "Hslot". }
    iModIntro. iFrame "Hrun". iSplitR "Htok Hfr Hdev2 Hbno2".
    - iApply (bcache_res2_fold bn V (<[k := ((1/4)%Qp, 1%positive)]> M) ord
                (bfun_upd devs k D) (bfun_upd bnos k B) tl).
      iFrame "Hfl". rewrite /bcache_scan2. iFrame "Hauth Hsauth".
      iSplitR.
      { iPureIntro. intros j Hj.
        destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
        apply Hdom. by rewrite lookup_insert_ne in Hj. }
      iSplitR; [iPureIntro; exact Hord|].
      iSplitR.
      { iPureIntro. exact (bd_inj_upd V bnos k B Hk HcovB Hmiss Hinj). }
      iSplitR.
      { iPureIntro. exact (bd_devpin_upd V devs bnos k D B HD Hdevpin). }
      iFrame "Hlru Hpool Hslots".
    - rewrite /bref. iFrame "Htok Hdev2 Hbno2".
      iDestruct "Hfr" as (rb) "(Hfr & _ & #Hllb)". iExists rb. iFrame "Hfr Hllb".
  Qed.

End BreadScan2.

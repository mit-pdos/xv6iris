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
Require Import TsoMemPa TsoGhost.   (* [llb] *)
Require Import CtxBox.              (* [reference], [max_stamp] *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (1) The escrow, in the raw [inv] shape [iInv] recognizes.             *)
(*      (The mask-carrying width-4 load/store are [WpAu4.v]'s now.)       *)
(* ===================================================================== *)

(* the v1 escrow leaves are gone: the box is CtxBox.v (endgame §3.5) *)

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

  (* the slot tie's steps (A6.155): a fractioned refs++ halves the retained
     share; a chain refs++ leaves it alone; a fractioned refs-- returns it. *)
  Local Lemma bd_btie_incr (ot : option Qp) (qr : Qp) :
    btie ot qr -> btie (ot ⋅ Some (qr/2)%Qp) (qr/2)%Qp.
  Proof.
    destruct ot as [q|]; intros Htie; cbn in Htie.
    - rewrite -Some_op frac_op. cbn. rewrite -Qp.add_assoc Qp.div_2. exact Htie.
    - rewrite left_id_L. cbn. rewrite Htie. apply Qp.div_2.
  Qed.
  Local Lemma bd_btie_incr_valid (ot : option Qp) (qr : Qp) :
    btie ot qr -> ✓ (ot ⋅ Some (qr/2)%Qp).
  Proof.
    destruct ot as [q|]; intros Htie; cbn in Htie.
    - rewrite -Some_op frac_op. apply Some_valid, frac_valid.
      etrans; [| exact bd_half_le_one].
      rewrite -Htie. apply Qp.add_le_mono; [reflexivity | apply bd_div2_le].
    - rewrite left_id_L. apply Some_valid, frac_valid. rewrite Htie.
      etrans; [apply bd_div2_le | exact bd_half_le_one].
  Qed.
  Local Lemma bd_btie_incr0 (ot : option Qp) (qr : Qp) :
    btie ot qr -> btie (ot ⋅ None) qr.
  Proof. intros Htie. by rewrite right_id_L. Qed.
  Local Lemma bd_btie_decr (q : Qp) (orem : option Qp) (qr : Qp) :
    btie (Some q ⋅ orem) qr -> btie orem (qr + q)%Qp.
  Proof.
    destruct orem as [r|]; intros Htie.
    - rewrite -Some_op frac_op in Htie. cbn in Htie. cbn.
      rewrite (Qp.add_comm qr q) Qp.add_assoc (Qp.add_comm r q). exact Htie.
    - rewrite right_id_L in Htie. cbn in Htie. cbn. rewrite Qp.add_comm. exact Htie.
  Qed.

  (* the payload's re-formed pieces after a count edge: the floor slot may
     have moved to [tl'] (with its llb); the scan at [tl'].  The caller
     re-floors through the _in release (R2: every L1 release). *)
  Definition bd_scan2_after (bn : bio_names) (V : bio_view Σ) (tl : nat) : iProp Σ :=
    (∃ (M : gmap nat (option Qp * positive)) (ord : list nat)
       (devs bnos : nat -> mword 32) (tl' : nat),
       ⌜(tl <= tl')%nat⌝ ∗ llb loglen_name tl' ∗
       bcache_scan2 bn V M ord devs bnos tl' cur_ctx)%I.

  Local Lemma bd_llb_max (tl T : nat) :
    llb loglen_name tl -∗ llb loglen_name T -∗ llb loglen_name (Nat.max tl T).
  Proof.
    iIntros "#H1 #H2". destruct (Nat.max_spec tl T) as [[_ ->] | [_ ->]]; [iExact "H2" | iExact "H1"].
  Qed.

  (* the common tail: the slot re-formed at the new entry, the scan re-formed
     at the same floor slot *)
  Local Lemma bd_scan2_close (bn : bio_names) (V : bio_view Σ) M ord devs bnos (tl k : nat)
      (e : option Qp * positive) :
    (k < NBUF)%nat ->
    ⌜∀ k0, is_Some (M !! k0) -> (k0 < NBUF)%nat⌝ -∗
    ⌜ord ≡ₚ seq 0 NBUF⌝ -∗
    ⌜∀ k1 k2, (k1 < NBUF)%nat -> (k2 < NBUF)%nat ->
        uint (bnos k1) ∈ bv_cov V -> uint (bnos k1) = uint (bnos k2) -> k1 = k2⌝ -∗
    ⌜∀ k0, (k0 < NBUF)%nat -> uint (bnos k0) ∈ bv_cov V -> devs k0 = bv_dev V⌝ -∗
    TsoCtx.ctx_floor cur_ctx tl -∗ llb loglen_name tl -∗
    own (bn_auth bn) (● (<[k := e]> M)) -∗ bslots_auth -∗
    bcache_lru bhead (map bnode ord) -∗ bio_pool V bnos -∗
    ([∗ list] k0 ∈ seq 0 NBUF, bio_slot_res2 bn V (<[k := e]> M) k0 (devs k0) (bnos k0) tl cur_ctx) -∗
    bcache_res2 bn V cur_ctx.
  Proof.
    iIntros (Hk Hdom Hord Hinj Hdevpin) "#Hfl #Hllbtl Hauth Hsauth Hlru Hpool Hslots".
    iApply (bcache_res2_fold bn V (<[k := e]> M) ord devs bnos tl).
    iFrame "Hfl Hllbtl". rewrite /bcache_scan2. iFrame "Hauth Hsauth".
    iSplitR.
    { iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
      apply Hdom. by rewrite lookup_insert_ne in Hj. }
    iSplitR; [iPureIntro; exact Hord|].
    iSplitR; [iPureIntro; exact Hinj|].
    iSplitR; [iPureIntro; exact Hdevpin|].
    iFrame "Hlru Hpool Hslots".
  Qed.

  (* the reference's own llb, at its stamp (R1's presentation at an acquire) *)
  Lemma bd_ref_llb (bn : bio_names) (k : nat) (dev bno : mword 32) (t : nat) :
    CtxBox.reference (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]} -∗
    CtxBox.reference (X := bio_x) (bn_box bn k) (dev, bno) {[((dev, bno), t) := 1%Qp]} ∗
    llb loglen_name t.
  Proof.
    iIntros "H". iDestruct "H" as "(%H1 & %H2 & Hf & #Hllb)".
    iSplitL "Hf".
    { iSplitR; [iPureIntro; exact H1|]. iSplitR; [iPureIntro; exact H2|]. iFrame "Hf Hllb". }
    iEval (rewrite /max_stamp map_fold_singleton /max_step /= Nat.max_0_r) in "Hllb". iExact "Hllb".
  Qed.

  (* the L1 row, re-formed at an unchanged stamp *)
  Local Lemma bd_regs_same (bn : bio_names) (k tl : nat) (r : slot_reg bio_id bio_x)
      (dev bno : mword 32) :
    sr_win r = false -> sr_x r = None -> sr_ident r = (dev, bno) -> (sr_td r <= tl)%nat ->
    reg_drop bn k r -∗ llb loglen_name (sr_td r) -∗ bslot_regs bn k tl dev bno.
  Proof.
    iIntros (Hw Hx Hid Hb) "Hrd #Hllb". iExists r. iFrame "Hrd Hllb". iPureIntro. split_and!; done.
  Qed.

  (* ---- refs++ (box lemma (c)) for a FRACTIONED reference (bpin) ---- *)
  Lemma bcache_scan2_incr (bn : bio_names) (V : bio_view Σ) M ord devs bnos
      (tl k : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    llb loglen_name tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗ bslot -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      (brefcnt k ↦₄ (incr32 cw) ={E}=∗
         bcache_res2 bn V cur_ctx ∗ ∃ q : Qp, bref bn k q (devs k) (bnos k)).
  Proof.
    iIntros (HE Hk) "#Hbox #Hfl #Hllbtl Hscan Hbslot".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    destruct (M !! k) as [[ot cnt]|] eqn:HMk.
    - (* ---- busy buffer: halve the retained share ---- *)
      iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (%Hcnt & Hcell & Hfd & Hc & Hqr)]".
      iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
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
      iMod (bio_incr_step bn M k ot cnt (Some (qr/2)%Qp) HMk (bd_btie_incr_valid ot qr Htie)
              with "Hauth") as "[Hauth Htok]".
      iMod (bbox_ref_incr bn V k r (Pos.to_nat cnt) (devs k) (bnos k) E HE Hw Hid with "Hbox Hrd Hc") as "(Hrd & Hc & Hgh)".
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
      iAssert (bio_slot_res2 bn V (<[k := (ot ⋅ Some (qr/2)%Qp, Pos.succ cnt)]> M) k
                 (devs k) (bnos k) tl cur_ctx)
        with "[Hrd Hcell Hfd Hbslot Hc Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert.
        iSplitL "Hrd". { iApply (bd_regs_same _ _ _ _ _ _ Hw Hxn Hid Hb with "Hrd Hllbd"). }
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
        iFrame "Hcell".
        iSplitL "Hfd Hbslot".
        { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
        iSplitL "Hc".
        { assert (Hsucc' : Pos.to_nat (Pos.succ cnt) = S (Pos.to_nat cnt)) by lia.
          rewrite Hsucc'. iExact "Hc". }
        iExists (qr/2)%Qp. iSplitR.
        { iPureIntro. exact (bd_btie_incr ot qr Htie). }
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := (ot ⋅ Some (qr/2)%Qp, Pos.succ cnt)]> M) devs bnos tl
                   with "[%] [%] Hslot") as "Hslots"; [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hgh Hdev2 Hbno2".
      + iApply (bd_scan2_close bn V M ord devs bnos tl k _ Hk
                  with "[%] [%] [%] [%] Hfl Hllbtl Hauth Hsauth Hlru Hpool Hslots"); done.
      + iExists (qr/2)%Qp. rewrite /bref /bref_tok. iFrame "Htok Hgh Hdev2 Hbno2".
    - (* ---- idle buffer: the FIRST reference; the content stays in the box ---- *)
      iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (Hcell & Hc & Hdev & Hbno)]".
      iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
      { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_first_ref_step bn M k (Some (1/4)%Qp) HMk bd_quarter_valid
              with "Hauth") as "[Hauth Htok]".
      iMod (bbox_ref_incr bn V k r 0 (devs k) (bnos k) E HE Hw Hid with "Hbox Hrd Hc") as "(Hrd & Hc & Hgh)".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -ctx_word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res2 bn V (<[k := (Some (1/4)%Qp, 1%positive)]> M) k (devs k) (bnos k) tl cur_ctx)
        with "[Hrd Hcell Hbslot Hc Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert.
        iSplitL "Hrd". { iApply (bd_regs_same _ _ _ _ _ _ Hw Hxn Hid Hb with "Hrd Hllbd"). }
        iSplitR. { iPureIntro. exact bd_pos1_lt. }
        iFrame "Hcell".
        iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
        iSplitL "Hc". { change (Pos.to_nat 1) with 1%nat. iExact "Hc". }
        iExists (1/4)%Qp. iSplitR; [iPureIntro; cbn; exact bd_quarter_half|].
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := (Some (1/4)%Qp, 1%positive)]> M) devs bnos tl
                   with "[%] [%] Hslot") as "Hslots"; [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hgh Hdev2 Hbno2".
      + iApply (bd_scan2_close bn V M ord devs bnos tl k _ Hk
                  with "[%] [%] [%] [%] Hfl Hllbtl Hauth Hsauth Hlru Hpool Hslots"); done.
      + iExists (1/4)%Qp. rewrite /bref /bref_tok. iFrame "Htok Hgh Hdev2 Hbno2".
  Qed.

  (* ---- refs++ (box lemma (c)) for THE CHAIN (bread's hit path) ---- *)
  Lemma bcache_scan2_incr0 (bn : bio_names) (V : bio_view Σ) M ord devs bnos
      (tl k : nat) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    llb loglen_name tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗ bslot -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      (brefcnt k ↦₄ (incr32 cw) ={E}=∗ bcache_res2 bn V cur_ctx ∗ bchain bn k (devs k) (bnos k)).
  Proof.
    iIntros (HE Hk) "#Hbox #Hfl #Hllbtl Hscan Hbslot".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    destruct (M !! k) as [[ot cnt]|] eqn:HMk.
    - iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (%Hcnt & Hcell & Hfd & Hc & Hqr)]".
      iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iDestruct (bslots_no_overflow with "Hsauth Hfd") as %[Hn1 Hn2].
      iDestruct (bio_auth_entry_valid bn M k ot cnt HMk with "Hauth") as %Hvot.
      iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int (Z.pos cnt) : mword 32)
                     = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
      { rewrite (incr32_pos (Z.pos cnt) ltac:(lia)
                   ltac:(pose proof Hn2 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
        f_equal. rewrite Pos2Z.inj_succ. lia. }
      iEval (rewrite Hinc) in "Hcell".
      assert (Hv0 : ✓ (ot ⋅ None)) by (rewrite right_id; exact Hvot).
      iMod (bio_incr_step bn M k ot cnt None HMk Hv0 with "Hauth") as "[Hauth Htok]".
      iMod (bbox_ref_incr bn V k r (Pos.to_nat cnt) (devs k) (bnos k) E HE Hw Hid with "Hbox Hrd Hc") as "(Hrd & Hc & Hgh)".
      assert (Hsucc : Pos.to_nat (Pos.succ cnt) = (Pos.to_nat cnt + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res2 bn V (<[k := (ot ⋅ None, Pos.succ cnt)]> M) k
                 (devs k) (bnos k) tl cur_ctx)
        with "[Hrd Hcell Hfd Hbslot Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert.
        iSplitL "Hrd". { iApply (bd_regs_same _ _ _ _ _ _ Hw Hxn Hid Hb with "Hrd Hllbd"). }
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
        iFrame "Hcell".
        iSplitL "Hfd Hbslot".
        { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
        iSplitL "Hc".
        { assert (Hsucc' : Pos.to_nat (Pos.succ cnt) = S (Pos.to_nat cnt)) by lia.
          rewrite Hsucc'. iExact "Hc". }
        iExists qr. iSplitR.
        { iPureIntro. exact (bd_btie_incr0 ot qr Htie). }
        iFrame "Hdev Hbno". }
      iDestruct ("Hback" $! (<[k := (ot ⋅ None, Pos.succ cnt)]> M) devs bnos tl
                   with "[%] [%] Hslot") as "Hslots"; [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hgh".
      + iApply (bd_scan2_close bn V M ord devs bnos tl k _ Hk
                  with "[%] [%] [%] [%] Hfl Hllbtl Hauth Hsauth Hlru Hpool Hslots"); done.
      + rewrite /bchain /bref_tok0. iFrame "Htok Hgh".
    - iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
      iDestruct "Hslot" as "[Hregs (Hcell & Hc & Hdev & Hbno)]".
      iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
      { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_first_ref_step bn M k None HMk I with "Hauth") as "[Hauth Htok]".
      iMod (bbox_ref_incr bn V k r 0 (devs k) (bnos k) E HE Hw Hid with "Hbox Hrd Hc") as "(Hrd & Hc & Hgh)".
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res2 bn V (<[k := (None, 1%positive)]> M) k (devs k) (bnos k) tl cur_ctx)
        with "[Hrd Hcell Hbslot Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert.
        iSplitL "Hrd". { iApply (bd_regs_same _ _ _ _ _ _ Hw Hxn Hid Hb with "Hrd Hllbd"). }
        iSplitR. { iPureIntro. exact bd_pos1_lt. }
        iFrame "Hcell".
        iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
        iSplitL "Hc". { change (Pos.to_nat 1) with 1%nat. iExact "Hc". }
        iExists (1/2)%Qp. iSplitR; [iPureIntro; done|].
        iFrame "Hdev Hbno". }
      iDestruct ("Hback" $! (<[k := (None, 1%positive)]> M) devs bnos tl
                   with "[%] [%] Hslot") as "Hslots"; [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hgh".
      + iApply (bd_scan2_close bn V M ord devs bnos tl k _ Hk
                  with "[%] [%] [%] [%] Hfl Hllbtl Hauth Hsauth Hlru Hpool Hslots"); done.
      + rewrite /bchain /bref_tok0. iFrame "Htok Hgh".
  Qed.

  (* ---- the RECYCLE (box lemmas (a) + three stores + (b)): the idle slot's
     header comes out of the box FULL (the bundle's halves joined with the
     bcache halves); the closing wand takes the cells back at the recycler's
     values, evicts the old payload into the pool, withdraws the new block's
     bundle, deposits the (invalid) header at the new stamp, and mints the
     chain's reference there.  The floor slot grows to the new stamp. ---- *)
  Lemma bcache_scan2_recycle (bn : bio_names) (V : bio_view Σ)
      (M : gmap nat (option Qp * positive)) (ord : list nat)
      (devs bnos : nat -> mword 32) (tl k : nat) (D B : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    M !! k = None ->
    D = bv_dev V ->
    uint B ∈ bv_cov V ->
    (forall i, (i < NBUF)%nat -> ¬ (devs i = D /\ bnos i = B)) ->
    buf_box bn V k -∗
    TsoCtx.own_context cur_ctx -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    llb loglen_name tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗ bslot ={E}=∗
    TsoCtx.own_context cur_ctx ∗
    brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
    (∃ vld : mword 32, b_valid (bpa k) ↦₄ vld) ∗
    b_dev (bpa k) ↦₄ (devs k) ∗
    b_blockno (bpa k) ↦₄ (bnos k) ∗
    (TsoCtx.own_context cur_ctx -∗
     brefcnt k ↦₄ (mword_of_int 1 : mword 32) -∗
     b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗
     b_dev (bpa k) ↦₄ D -∗
     b_blockno (bpa k) ↦₄ B ={E}=∗
     TsoCtx.own_context cur_ctx ∗ bd_scan2_after bn V tl ∗ bchain bn k D B).
  Proof.
    iIntros (HE Hk HMk HD HcovB Htie) "#Hbox Hrun #Hfl #Hllbtl Hscan Hbslot".
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
    iDestruct "Hslot" as "[Hregs (Hcell & Hc & Hdev & Hbno)]".
    iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
    (* (a): the header out of the box at the slot's identity; the window opens *)
    iMod (bbox_withdraw_L1 bn V k cur_ctx r tl E HE Hw Hb with "Hbox Hrun Hfl Hrd Hc")
      as "(Hrun & Hc & Hout)".
    iDestruct "Hout" as (bs) "[Hrd Hhdr]".
    iEval (rewrite /bhdr Hid; cbn [fst snd]) in "Hhdr".
    iDestruct "Hhdr" as (v) "(Hvld & Hdevb & Hbnob & Hpay)".
    iDestruct (ctx_word4_pointsto_half_join with "Hdevb Hdev") as "Hdev".
    iDestruct (ctx_word4_pointsto_half_join with "Hbnob Hbno") as "Hbno".
    iModIntro. iFrame "Hrun Hcell Hdev Hbno".
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
    iAssert (buf_pay bn V k false D B bs) with "[HpoolB]" as "Hpay".
    { rewrite /buf_pay. case_decide as Hc; [| exfalso; exact (Hc HcovB)].
      iSplitR; [by iPureIntro|]. iExact "HpoolB". }
    (* the cells at the new values: the bundle's halves and the bcache halves *)
    iDestruct (ctx_word4_pointsto_half_split with "Hdev") as "[Hdevb Hdevs]".
    iDestruct (ctx_word4_pointsto_half_split with "Hbno") as "[Hbnob Hbnos]".
    (* (b): the (invalid) header enters the box at the new stamp; the chain's
       unit is minted there *)
    iMod (bbox_deposit_L1 bn V k cur_ctx (sr_td r) (sr_ident r) bs D B E HE
            with "Hbox Hrun Hrd Hc [Hvld Hdevb Hbnob Hpay]")
      as "(Hrun & %T' & Hrd & Hc & Hgh & #Hllb')".
    { rewrite /bhdr. iExists false. cbn [fst snd]. rewrite /buf_hdr. cbv iota.
      iFrame "Hvld Hdevb Hbnob Hpay". }
    iMod (bio_first_ref_step bn M k None HMk I with "Hauth") as "[Hauth Htok]".
    iEval (rewrite /bslot) in "Hbslot".
    iAssert (bio_slot_res2 bn V (<[k := (None, 1%positive)]> M) k D B (Nat.max tl T') cur_ctx)
      with "[Hrd Hcell Hbslot Hc Hdevs Hbnos]" as "Hslot".
    { rewrite /bio_slot_res2 lookup_insert.
      iSplitL "Hrd".
      { iExists (SlotReg T' false (D, B) None). iFrame "Hrd Hllb'". iPureIntro. cbn.
        split_and!; [done | done | done | lia]. }
      iSplitR. { iPureIntro. exact bd_pos1_lt. }
      iFrame "Hcell".
      iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
      iFrame "Hc".
      iExists (1/2)%Qp. iSplitR; [iPureIntro; done|].
      iFrame "Hdevs Hbnos". }
    iDestruct ("Hback" $! (<[k := (None, 1%positive)]> M)
                 (bfun_upd devs k D) (bfun_upd bnos k B) (Nat.max tl T')
                 with "[%] [%] [Hslot]") as "Hslots"; [| lia | |].
    { intros j Hj. split_and!;
        [ rewrite lookup_insert_ne; [reflexivity | congruence]
        | exact (bfun_upd_ne devs k D j Hj)
        | exact (bfun_upd_ne bnos k B j Hj) ]. }
    { rewrite (bfun_upd_eq devs k D) (bfun_upd_eq bnos k B). iExact "Hslot". }
    iModIntro. iFrame "Hrun". iSplitR "Htok Hgh".
    - iExists (<[k := (None, 1%positive)]> M), ord, (bfun_upd devs k D), (bfun_upd bnos k B), (Nat.max tl T').
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iApply (bd_llb_max with "Hllbtl Hllb'")|].
      rewrite /bcache_scan2. iFrame "Hauth Hsauth".
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
    - rewrite /bchain /bref_tok0. iFrame "Htok Hgh".
  Qed.

  (* ---- refs-- (box lemma (d)) for a FRACTIONED reference in hand (bunpin);
     refs 1 -> 0 IS (d): the content stays in the box. ---- *)
  Lemma bcache_scan2_decr (bn : bio_names) (V : bio_view Σ) M ord devs bnos
      (tl k : nat) (q : Qp) (dev bno : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    llb loglen_name tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗
    bref bn k q dev bno -∗
    ∃ cnt : positive,
      ⌜(Z.pos cnt < 2 ^ 31)%Z⌝ ∗
      brefcnt k ↦₄ (mword_of_int (Z.pos cnt) : mword 32) ∗
      (brefcnt k ↦₄ (mword_of_int (Z.pos cnt - 1) : mword 32) ={E}=∗
         bd_scan2_after bn V tl ∗ bslot).
  Proof.
    iIntros (HE Hk) "#Hbox #Hfl #Hllbtl Hscan Href".
    iDestruct "Href" as "(Hrtok & Hgh & Hrdev & Hrbno)".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (btok_lookup with "Hauth Hrtok") as %(ot & cnt & HMk & Hincl & Hsole).
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
    iDestruct "Hslot" as "[Hregs (%Hcnt & Hcell & Hfd & Hc & Hqr)]".
    iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
    iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
    iDestruct (ctx_word4_pointsto_agree with "Hrdev Hdev") as %->.
    iDestruct (ctx_word4_pointsto_agree with "Hrbno Hbno") as %->.
    iExists cnt. iSplitR; [iPureIntro; exact Hcnt|]. iFrame "Hcell".
    iIntros "Hcell".
    assert (Hex : exists c', Pos.to_nat cnt = S c').
    { exists (Pos.to_nat cnt - 1)%nat. pose proof (Pos2Nat.is_pos cnt). lia. }
    destruct Hex as [c' Hc'].
    iEval (rewrite Hc') in "Hc".
    iMod (bbox_ref_decr bn V k r c' _ _ E HE Hw with "Hbox Hrd Hllbd Hc Hgh")
      as "(%td' & %Htd' & Hrd & Hc & #Hllbd')".
    iAssert (bslot_regs bn k (Nat.max tl td') (devs k) (bnos k)) with "[Hrd]" as "Hregs".
    { iExists (SlotReg td' false (sr_ident r) (sr_x r)). iFrame "Hrd Hllbd'". iPureIntro. cbn.
      split_and!; [done | exact Hxn | exact Hid | lia]. }
    destruct (decide (cnt = 1%positive)) as [->|Hne].
    - (* the last reference: the entry disappears; the bcache half re-forms *)
      assert (Hot : ot = Some q) by (apply Hsole; reflexivity). subst ot.
      iMod (bio_last_ref_step bn M k (Some q) HMk with "Hauth Hrtok") as "Hauth".
      assert (Hz0 : (Z.pos 1 - 1)%Z = 0%Z) by reflexivity.
      iEval (rewrite Hz0) in "Hcell".
      assert (Hc'0 : c' = 0%nat) by (change (Pos.to_nat 1) with 1%nat in Hc'; lia). subst c'.
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/2)} (devs k))%I with "[Hrdev Hdev]" as "Hdev".
      { cbn in Htie. rewrite -(Qp.add_comm qr q) in Htie. rewrite -Htie ctx_word4_pointsto_frac_split.
        iFrame "Hdev Hrdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k))%I with "[Hrbno Hbno]" as "Hbno".
      { cbn in Htie. rewrite -(Qp.add_comm qr q) in Htie. rewrite -Htie ctx_word4_pointsto_frac_split.
        iFrame "Hbno Hrbno". }
      assert (Hdel : delete k M !! k = None) by apply lookup_delete.
      iAssert (bio_slot_res2 bn V (delete k M) k (devs k) (bnos k) (Nat.max tl td') cur_ctx)
        with "[Hregs Hcell Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 Hdel. iFrame "Hregs Hcell Hc Hdev Hbno". }
      iDestruct ("Hback" $! (delete k M) devs bnos (Nat.max tl td') with "[%] [%] Hslot") as "Hslots";
        [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_delete_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Hfd".
      + iExists (delete k M), ord, devs, bnos, (Nat.max tl td').
        iSplitR; [iPureIntro; lia|].
        iSplitR; [iApply (bd_llb_max with "Hllbtl Hllbd'")|].
        rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj. apply Hdom.
          destruct (decide (j = k)) as [->|Hnk].
          - rewrite Hdel in Hj. by destruct Hj as [x Hx].
          - rewrite lookup_delete_ne in Hj; [exact Hj | congruence]. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + rewrite /bslot. change (Pos.to_nat 1) with 1%nat. iExact "Hfd".
    - (* survivors: the share returns to the slot *)
      assert (Hex2 : exists cp, cnt = Pos.succ cp).
      { exists (Pos.pred cnt). symmetry. by apply Pos.succ_pred. }
      destruct Hex2 as [cp Hcp]. subst cnt.
      destruct Hincl as [orem Horem]. apply leibniz_equiv in Horem.
      iMod (bio_decr_step bn M k (Some q) ot orem cp HMk Horem with "Hauth Hrtok") as "Hauth".
      assert (Hzp : (Z.pos (Pos.succ cp) - 1)%Z = Z.pos cp)
        by (rewrite Pos2Z.inj_succ; lia).
      iEval (rewrite Hzp) in "Hcell".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr + q)} (devs k))%I
        with "[Hrdev Hdev]" as "Hdev".
      { rewrite ctx_word4_pointsto_frac_split. iFrame "Hdev Hrdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr + q)} (bnos k))%I
        with "[Hrbno Hbno]" as "Hbno".
      { rewrite ctx_word4_pointsto_frac_split. iFrame "Hbno Hrbno". }
      assert (Hsucc : Pos.to_nat (Pos.succ cp) = (Pos.to_nat cp + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      assert (Hcp' : c' = Pos.to_nat cp) by lia. subst c'.
      iEval (rewrite Hsucc bslots_op) in "Hfd".
      iDestruct "Hfd" as "[Hfd Hout]".
      iAssert (bio_slot_res2 bn V (<[k := (orem, cp)]> M) k (devs k) (bnos k) (Nat.max tl td') cur_ctx)
        with "[Hregs Hcell Hfd Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert. iFrame "Hregs".
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ in Hcnt. lia. }
        iFrame "Hcell Hfd Hc".
        iExists (qr + q)%Qp. iSplitR.
        { iPureIntro. apply bd_btie_decr. rewrite -Horem. exact Htie. }
        iFrame "Hdev Hbno". }
      iDestruct ("Hback" $! (<[k := (orem, cp)]> M) devs bnos (Nat.max tl td') with "[%] [%] Hslot") as "Hslots";
        [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Hout".
      + iExists (<[k := (orem, cp)]> M), ord, devs, bnos, (Nat.max tl td').
        iSplitR; [iPureIntro; lia|].
        iSplitR; [iApply (bd_llb_max with "Hllbtl Hllbd'")|].
        rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hnk]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + rewrite /bslot. iExact "Hout".
  Qed.

  (* ---- refs-- (box lemma (d)) for THE CHAIN after its park (brelse) ---- *)
  Lemma bcache_scan2_decr0 (bn : bio_names) (V : bio_view Σ) M ord devs bnos
      (tl k : nat) (dev bno : mword 32) (E : coPset) :
    ↑bioxN ⊆ E ->
    (k < NBUF)%nat ->
    buf_box bn V k -∗
    TsoCtx.ctx_floor cur_ctx tl -∗
    llb loglen_name tl -∗
    bcache_scan2 bn V M ord devs bnos tl cur_ctx -∗
    bchain bn k dev bno -∗
    ∃ cnt : positive,
      ⌜(Z.pos cnt < 2 ^ 31)%Z⌝ ∗
      brefcnt k ↦₄ (mword_of_int (Z.pos cnt) : mword 32) ∗
      (brefcnt k ↦₄ (mword_of_int (Z.pos cnt - 1) : mword 32) ={E}=∗
         bd_scan2_after bn V tl ∗ bslot).
  Proof.
    iIntros (HE Hk) "#Hbox #Hfl #Hllbtl Hscan Hch".
    iDestruct "Hch" as "[Hrtok Hgh]".
    rewrite /bcache_scan2.
    iDestruct "Hscan" as
      "(Hauth & Hsauth & %Hdom & %Hord & %Hinj & %Hdevpin & Hlru & Hpool & Hslots)".
    iDestruct (btok_lookup with "Hauth Hrtok") as %(ot & cnt & HMk & _ & Hsole).
    iDestruct (bio_slots_acc2 bn V M devs bnos tl k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res2 HMk) in "Hslot".
    iDestruct "Hslot" as "[Hregs (%Hcnt & Hcell & Hfd & Hc & Hqr)]".
    iDestruct "Hregs" as (r) "(Hrd & %Hw & %Hxn & %Hid & #Hllbd & %Hb)".
    iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
    iExists cnt. iSplitR; [iPureIntro; exact Hcnt|]. iFrame "Hcell".
    iIntros "Hcell".
    assert (Hex : exists c', Pos.to_nat cnt = S c').
    { exists (Pos.to_nat cnt - 1)%nat. pose proof (Pos2Nat.is_pos cnt). lia. }
    destruct Hex as [c' Hc'].
    iEval (rewrite Hc') in "Hc".
    iMod (bbox_ref_decr bn V k r c' _ _ E HE Hw with "Hbox Hrd Hllbd Hc Hgh")
      as "(%td' & %Htd' & Hrd & Hc & #Hllbd')".
    iAssert (bslot_regs bn k (Nat.max tl td') (devs k) (bnos k)) with "[Hrd]" as "Hregs".
    { iExists (SlotReg td' false (sr_ident r) (sr_x r)). iFrame "Hrd Hllbd'". iPureIntro. cbn.
      split_and!; [done | exact Hxn | exact Hid | lia]. }
    destruct (decide (cnt = 1%positive)) as [->|Hne].
    - assert (Hot : ot = None) by (apply Hsole; reflexivity). subst ot.
      cbn in Htie. subst qr.
      iMod (bio_last_ref_step bn M k None HMk with "Hauth Hrtok") as "Hauth".
      assert (Hz0 : (Z.pos 1 - 1)%Z = 0%Z) by reflexivity.
      iEval (rewrite Hz0) in "Hcell".
      assert (Hc'0 : c' = 0%nat) by (change (Pos.to_nat 1) with 1%nat in Hc'; lia). subst c'.
      assert (Hdel : delete k M !! k = None) by apply lookup_delete.
      iAssert (bio_slot_res2 bn V (delete k M) k (devs k) (bnos k) (Nat.max tl td') cur_ctx)
        with "[Hregs Hcell Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 Hdel. iFrame "Hregs Hcell Hc Hdev Hbno". }
      iDestruct ("Hback" $! (delete k M) devs bnos (Nat.max tl td') with "[%] [%] Hslot") as "Hslots";
        [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_delete_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Hfd".
      + iExists (delete k M), ord, devs, bnos, (Nat.max tl td').
        iSplitR; [iPureIntro; lia|].
        iSplitR; [iApply (bd_llb_max with "Hllbtl Hllbd'")|].
        rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj. apply Hdom.
          destruct (decide (j = k)) as [->|Hnk].
          - rewrite Hdel in Hj. by destruct Hj as [x Hx].
          - rewrite lookup_delete_ne in Hj; [exact Hj | congruence]. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + rewrite /bslot. change (Pos.to_nat 1) with 1%nat. iExact "Hfd".
    - assert (Hex2 : exists cp, cnt = Pos.succ cp).
      { exists (Pos.pred cnt). symmetry. by apply Pos.succ_pred. }
      destruct Hex2 as [cp Hcp]. subst cnt.
      assert (Hsub : ot = None ⋅ ot) by (by rewrite left_id).
      iMod (bio_decr_step bn M k None ot ot cp HMk Hsub with "Hauth Hrtok") as "Hauth".
      assert (Hzp : (Z.pos (Pos.succ cp) - 1)%Z = Z.pos cp)
        by (rewrite Pos2Z.inj_succ; lia).
      iEval (rewrite Hzp) in "Hcell".
      assert (Hsucc : Pos.to_nat (Pos.succ cp) = (Pos.to_nat cp + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      assert (Hcp' : c' = Pos.to_nat cp) by lia. subst c'.
      iEval (rewrite Hsucc bslots_op) in "Hfd".
      iDestruct "Hfd" as "[Hfd Hout]".
      iAssert (bio_slot_res2 bn V (<[k := (ot, cp)]> M) k (devs k) (bnos k) (Nat.max tl td') cur_ctx)
        with "[Hregs Hcell Hfd Hc Hdev Hbno]" as "Hslot".
      { rewrite /bio_slot_res2 lookup_insert. iFrame "Hregs".
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ in Hcnt. lia. }
        iFrame "Hcell Hfd Hc".
        iExists qr. iSplitR; [iPureIntro; exact Htie|].
        iFrame "Hdev Hbno". }
      iDestruct ("Hback" $! (<[k := (ot, cp)]> M) devs bnos (Nat.max tl td') with "[%] [%] Hslot") as "Hslots";
        [| lia |].
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Hout".
      + iExists (<[k := (ot, cp)]> M), ord, devs, bnos, (Nat.max tl td').
        iSplitR; [iPureIntro; lia|].
        iSplitR; [iApply (bd_llb_max with "Hllbtl Hllbd'")|].
        rewrite /bcache_scan2. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hnk]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iSplitR; [iPureIntro; exact Hinj|].
        iSplitR; [iPureIntro; exact Hdevpin|].
        iFrame "Hlru Hpool Hslots".
      + rewrite /bslot. iExact "Hout".
  Qed.

End BreadScan2.

(** * WkOwnPingPong.v — the OWNERSHIP PING-PONG (φ-upgrade §1c, Stage 1)

    THE MIGRATION TEST FOR THE C/D/S POINTS-TO.  [WkStartedMp] is the
    message-passing example where the payload is PERSISTENT and nothing is
    ever taken away from the sender.  This file is the other half: a byte
    whose OWNERSHIP moves, back and forth, between two harts through a lock,
    while a second byte owned by the first hart stays behind — dirty and
    untouched — across both handoffs.  It is the acid test the φ-upgrade's
    design note asks for, because it exercises the three-state protocol at a
    REAL release site rather than at a lemma statement.

    ==================== THE TWO PROGRAMS ====================

    [x] is the TRANSFERRED byte, [y] is hart A's PRIVATE byte, [lk] is the
    lock word.  In xv6's own idiom (the [acquire]/[release] of
    [kernel/spinlock.c], and [kernel.asm]'s encoding of them):

      hart A                                hart B
      ------------------------------------  ----------------------------------
        sb   1, 0(x)     # x := 1  (D-A)      1: amoswap.w.aq a5, a4, 0(lk)
        sb   1, 0(y)     # y := 1  (D-A)         bnez a5, 1b        # acquire
        fence rw,w       # arms w_relp         lb  a5, 0(x)         # reads 1
        sw   zero, 0(lk) # release  ==>        sb   2, 0(x)  # x := 2   (D-B)
                                               fence rw,w
      1: amoswap.w.aq a5, a4, 0(lk)            sw zero, 0(lk)  # release  ==>
         bnez a5, 1b     # re-acquire
         lb  a5, 0(x)    # reads 2
         sb  3, 0(y)     # y is STILL A's, still dirty

    ==================== WHAT IT DEMONSTRATES ====================

    (1) THE [WDirty A] → [WClean] → [WDirty B] CYCLE.  A's [sb] to [x] is a
        [WCplain] message, so [x]'s state element goes [WDirty A] and only A
        may hold it ([WeakVProp.wpt_own], the [↦wo] form — EXCLUSIVE, no
        fractions).  The lock's payload is a CLEAN [x ↦w{1} 1]: a clean
        full-fraction byte is what any hart may take ([wpt_own_of_wpt]).  The
        conversion is the release's own D→C FLIP (§3 below), and after B
        takes it and stores, [x] is [WDirty B] — the author alternated, with
        no ghost state changing hands but the one state element.

    (2) THE FLIP IS PER-BYTE SELECTIVE — the frame is real.  [y] is dirtied by
        the same hart at the same time as [x], travels through the same
        release, and is NOT flipped: §3's release lemma carries a
        [wpt_dirty A y] conjunct IN and OUT, so the statement itself witnesses
        that [y]'s state element is still [WDirty A] on the far side of the
        handoff.  [WeakGhost.wlat_flip] consumes ONE byte's state element per
        call; a release flips exactly the deposit it is about to egress.

    (3) THE VIEW TRANSFER RIDES THE PAYLOAD, unchanged from the spinlock.  The
        deposit is frozen at the release store's own timestamp
        ([WeakInstr.wwp_release_deposit], which needs only [ws_bounded] — no
        fence), the lock invariant holds it at [view_scl t] with [t] the lock
        word's latest-write timestamp, and the acquiring [amoswap.w.aq] thaws
        it at the acquirer's index ([WeakLock.wacquire_core]).  §5's load then
        collapses every admissible timestamp for [x] onto the transferred
        value: B's [lb] returns 1, A's returns 2.

    (4) ALL THREE ARMS OF φ ARE PAID, and by three different resources.  Every
        instruction fetches, so every leaf owes [nv_hart] at its post-log
        ([WeakGhost] §5b's finding); §6 exhibits the three payers this example
        uses — the FETCH window ([nv_ok_unwritten], text is never written),
        the OWNED byte [x] under A's dirty element ([nv_ok_of_own_st] — the
        [WDirty] arm, the one a clean fragment cannot pay), and the LOCK WORD
        under the invariant's clean bundle ([nv_ok_of_pointsto], via the
        AMO/release path).  The lock word stays CLEAN throughout: nothing
        racy-READS it (the spin is an [ak_latest] AMO, whose read half is
        pinned), so the [WSync] mint of §1b is not needed here — mint it only
        if a racy lock read ever appears.

    ================= THE FLIP ROUTE THAT PROVED OUT =================

    THE LANDED [WeakLock.wrelease_core] CANNOT DO THE FLIP, and the obstacle
    is a seam rather than a subtlety: it takes the payload at the release's
    PRE-state ([vwp_hold R (wm_ws σ)]), whereas [WeakGhost.wlat_flip] needs
    the authority at the POST-state — its whole premise is that the releasing
    hart's [WCrel] message is the log's LAST.  The two never coexist inside
    that lemma.  So a release that egresses a dirty byte is a DIFFERENT core,
    and §3's [wrelease_flip_core] is it: same script, with the flip spliced in
    between the lock word's element update and the deposit.  The recipe for a
    ported release site is therefore

      take the payload in OWNED form (↦wo), do the lock's element update,
      flip, reassemble ↦w{1} at the SAME timestamp the element already had,
      then freeze with [wwp_release_deposit] — the deposit is view arithmetic
      and does not care that the state element moved under it.

    THE ONE PIECE THAT WAS MISSING is the message's CLASS.  [wlat_flip] wants
    [wm_ak mrel = WCrel] on the nose, and [WeakInstr.wQ_store_w] deliberately
    leaves the class existential (it must, or [wQ_amo_aq_w] — defined through
    it — would be unprovable), offering only [w_relp → k ≠ WCplain].  That is
    strictly too weak: [WCexcl] also satisfies it.  §1 closes the gap with NO
    new certificate: the φ-upgrade's own trace-carrying conjunct
    [WeakCert.wQ_eff] already determines the appended message exactly, and
    [wQ_eff_store_rel] reads the class off it under the two facts every
    release site has in hand ([ak_latest akw = false], and
    [w_relp (wm_ws σ) = true] — which [WeakAcquire.wrel_cb] already delivers
    at the store's pre-state).  A ported release therefore keeps the leaf
    interface it has; it gains one pure lemma application. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakExec.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakCert.
Require Import WeakViolation.
Require Import WeakLock.
Require Import WeakAcquire.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpLock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. READING THE RELEASE MESSAGE'S CLASS OFF THE TRACE

    The flip's missing premise, recovered from what the certificate already
    carries.  [WeakCert.wQ_eff] — the conjunct [wstep_cert_fr] pairs onto
    EVERY leaf certificate, generically, for φ's sake — says the successor's
    log is the fold of the instruction's own effect trace.  For the release
    [sw] that trace is [fetch; write], the fetch leaves [w_relp] alone
    ([WeakInstr.wread_post_relp]), and [WeakInterp.wm_class_of] then computes
    [WCrel] outright.

    This is stated at the release site's own shape and is the ONLY new pure
    fact the ported release recipe needs. *)

Lemma wQ_eff_store_rel (tid : option nat)
    (akf : akinfo) (pf : Arch.pa) (nf : N)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) (σ σ' : wmstate) :
  ak_latest akw = false ->
  w_relp (wm_ws σ) = true ->
  wQ_eff tid [WEread akf pf nf; WEwrite akw ea 4 v] σ σ' ->
  wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCrel ea 4 v])%list.
Proof.
  intros Hlat Hrelp (_ & Hlog & _).
  rewrite Hlog weffs_cons2 weff_apply_read weff_apply_write.
  rewrite wwrite_post_log wread_post_log.
  do 2 f_equal.
  rewrite /wm_class_of Hlat wread_post_relp Hrelp //.
Qed.

(** The same fact for the AMO's write half, for symmetry: it is [WCexcl]
    whatever the releaser's flag says, and [WeakInstr.wQ_amo_aq_w] already
    pins it — recorded here only to make the contrast explicit.  A lock word
    therefore never leaves the CLEAN state
    ([WeakGhost.wcds_ok_store_nonplain]), which is why §6's lock arm is an
    [nv_ok_of_pointsto] and not an [nv_ok_of_own_st]. *)
Lemma wQ_amo_aq_class (tid : option nat) (ea : Arch.pa) (v : bv 32) σ σ' :
  wQ_amo_aq tid ea v σ σ' ->
  wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCexcl ea 4 v])%list.
Proof. apply wQ_amo_aq_excl. Qed.

Section pingpong.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  (* THE THREAD'S CONTEXT, ambient (φ-upgrade §1.7).  A release site is code
     inside ONE thread, so the context is the section's; the acquiring thread
     is a different context and is nowhere in these statements — the medium
     between them is the lock body, whose payload is the CONTEXT-FREE clean
     [x ↦w{1} v]. *)
  Context `{XI : CurCtx}.
  Implicit Types P R : vProp Σ.

(* ====================================================================== *)
(** ** 2. A POINTS-TO THAT SAYS "DIRTY", so the frame is visible

    [WeakVProp.wpt_own] absorbs clean-and-dirty on purpose — no store site
    ever case-splits.  For THIS example that is one bit too coarse: the whole
    claim about [y] is that it is dirty on BOTH sides of the handoff, and a
    [↦wo] on the far side would be satisfied by a byte the release had
    flipped.  [wpt_dirty] is [wpt_own] with the disjunction resolved; it is
    used only in the statements, never in a proof obligation. *)

  Definition wpt_dirty (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8) : vProp Σ :=
    (∃ t : nat, ⎡ wlat_elem a (DfracOwn 1) t v ∗ wdirty c a ∗
                  ctx_wrote ξ c (view_byte a t) ⎤ ∗ ⊒(view_byte a t))%I.

  Lemma wpt_dirty_own ξ c a v : wpt_dirty ξ c a v ⊢ wpt_own ξ a v.
  Proof.
    rewrite /wpt_dirty /wpt_own. constructor => V.
    rewrite !monPred_at_exist. apply bi.exist_mono => t.
    rewrite !monPred_at_sep !monPred_at_embed.
    iIntros "[(He & Hd & #Hw) $]". iFrame "He".
    by iApply (wown_ctx_of_dirty with "Hd Hw").
  Qed.

  Lemma wpt_dirty_mono ξ c a v ws ws' :
    ws_le ws ws' ->
    vwp_hold (wpt_dirty ξ c a v) ws ⊢ vwp_hold (wpt_dirty ξ c a v) ws'.
  Proof. apply vwp_hold_mono. Qed.

  (** Its decode, the twin of [WeakVProp.wpt_own_at]. *)
  Lemma wpt_dirty_at ξ c a v ws :
    vwp_hold (wpt_dirty ξ c a v) ws ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wdirty c a ∗
                 ctx_wrote ξ c (view_byte a t) ∗
                 ⌜(t ≤ flr (ws_view ws) a)%nat⌝.
  Proof.
    rewrite /vwp_hold /wpt_dirty monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => t.
    iSplit.
    - iIntros "[(He & Hd & Hw) %H]". iFrame "He Hd Hw". iPureIntro.
      by apply view_byte_le.
    - iIntros "(He & Hd & Hw & %H)". iFrame "He Hd Hw". iPureIntro.
      by apply view_byte_le.
  Qed.

  (** ... and its introduction form, which is what an own STORE's
      postcondition gives when the message it appended was [WCplain]. *)
  Lemma wpt_dirty_at_intro ξ c a v t ws :
    (t ≤ flr (ws_view ws) a)%nat ->
    wlat_elem a (DfracOwn 1) t v -∗ wdirty c a -∗
    ctx_wrote ξ c (view_byte a t) -∗
    vwp_hold (wpt_dirty ξ c a v) ws.
  Proof.
    intros Ht. rewrite wpt_dirty_at. iIntros "He Hd Hw". iExists t. by iFrame.
  Qed.

(* ====================================================================== *)
(** ** 3. THE RELEASE THAT EGRESSES A DIRTY BYTE — the D→C flip at a real site

    [WeakLock.wrelease_core] with the deposit's own byte flipped clean on the
    way out.  Read the premises: they are [wrelease_core]'s, with
    [w_relp (wm_ws σ) = true] REPLACED by the sharper fact §1 derives from it
    — that the message the step appended is [WCrel] on the nose.  (Sharper in
    exactly the direction the flip needs; a caller with the [wQ_fr]-shaped
    certificate every leaf now carries gets it from [wQ_eff_store_rel].)

    THE PAYLOAD GOES IN OWNED AND COMES OUT CLEAN.  What the caller hands over
    is [wpt_own i x v] — the shape an owned [sb] leaves, absorbing both "I
    stored to it" and "I never did" — and what the lock invariant ends up
    holding is the CLEAN [x ↦w{1} v] that any hart may take.  The frame
    [wpt_dirty i y w] is threaded verbatim: it is A's own byte, it is DIRTY,
    and it is dirty on the far side too.  Nothing in the script touches it —
    that IS the per-byte selectivity, and the reason to state it here rather
    than assert it. *)

  Lemma wrelease_flip_core (γ : gname) (lk : Arch.pa) (x : Z)
      (v : bv 8) (i : CPU) (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) lk lock_zero σ σ' ->
    (* §1: the release store's own message, class and all *)
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero])%list ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    (* the log authority at the POST-log and the scheduler's migration
       invariant — what every owned rule takes since φ-upgrade §1.6, and
       neither of them a fact about [x] *)
    wlog_auth (wm_log σ') -∗ ctx_migr cur_ctx i -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) -∗
    locked γ i -∗
    vwp_hold (x ↦wo v) (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr cur_ctx i ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk (x ↦w v).
  Proof.
    intros (Himg & _ & Hle & Hflr) Hlog Hbnd.
    iIntros "Hlg Hmg Hi Hinv Htok Hpt".
    iDestruct "Hinv" as (st t w) "(Hw & Ha & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    (* the payload's element and its DIRTY-or-clean state, at the timestamp
       the byte's latest write took *)
    rewrite wpt_own_at. iDestruct "Hpt" as (t0) "(Hel & Hs & %Ht0)".
    (* THE RETARGET, leaf-internally: if this context dirtied [x] on a hart it
       has since left, the migration invariant flips it clean here — the
       release site's script does not know and does not care *)
    iMod (wown_ctx_retarget cur_ctx i x t0 v (wm_img σ) (wm_log σ) (wm_log σ')
            ltac:(rewrite Hlog; by apply pub_transfer_snoc)
            with "Hlg Hmg Hi Hel Hs") as "(Hlg & Hmg & Hi & Hel & Hs)".
    iFrame "Hlg Hmg".
    (* the lock word's own bundle moves to the fresh top — it stays CLEAN,
       because a [WCrel] message is not an owned store *)
    iMod (wlat4L_store_gen (Some (fin_to_nat i)) WCrel σ σ' lk t w lock_zero
            (wlock_shaped_rel _ WCrel _ ltac:(discriminate)) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    (* THE FLIP.  The authority is now at the POST-log, whose last message is
       this hart's release — which is [wlat_flip]'s entire premise. *)
    rewrite Hlog.
    iMod (wlat_flip (wm_img σ') (wm_log σ)
            (wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero) i x
            eq_refl eq_refl with "Hi Hs") as "[Hi Hcl]".
    (* the deposit: clean element + covered timestamp = [↦w{1}], frozen at the
       store's own timestamp by [ws_bounded] alone (no fence content) *)
    iAssert (monPred_at (x ↦w v) (view_scl (S (length (wm_log σ)))))%I
      with "[Hel Hcl]" as "HR".
    { iApply (wwp_release_deposit (x ↦w v) σ Hbnd).
      iApply (wpt_at_intro x (DfracOwn 1) v t0 (wm_ws σ) Ht0).
      rewrite /wlat_pointsto. iFrame "Hel Hcl". }
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. rewrite -Hlog. iFrame "Hi".
    iExists None, (S (length (wm_log σ))), lock_zero.
    iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hfrag HR".
  Qed.

  (** THE SAME LEMMA WITH THE PRIVATE BYTE IN THE FRAME.  This is the
      statement the design note asks for: [y] enters DIRTY-[i] and leaves
      DIRTY-[i], at the releaser's post-state index, having crossed a release
      that flipped [x].  Its proof is [iFrame] plus one monotonicity step —
      which is the point. *)
  Lemma wrelease_flip_frame (γ : gname) (lk : Arch.pa) (x y : Z)
      (v w : bv 8) (i : CPU) (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) lk lock_zero σ σ' ->
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero])%list ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    wlog_auth (wm_log σ') -∗ ctx_migr cur_ctx i -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) -∗
    locked γ i -∗
    vwp_hold (x ↦wo v) (wm_ws σ) -∗
    vwp_hold (wpt_dirty cur_ctx i y w) (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr cur_ctx i ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk (x ↦w v) ∗
    vwp_hold (wpt_dirty cur_ctx i y w) (wm_ws σ').
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hlg Hmg Hi Hinv Htok Hpt Hy".
    iMod (wrelease_flip_core γ lk x v i σ σ' HQ Hlog Hbnd
            with "Hlg Hmg Hi Hinv Htok Hpt") as "($ & $ & $ & $)".
    iModIntro. iApply (wpt_dirty_mono cur_ctx i y w (wm_ws σ) (wm_ws σ'));
      [|iFrame].
    exact (proj1 (proj2 (proj2 HQ))).
  Qed.

End pingpong.

(* ====================================================================== *)
(** ** 3'. THE RECEIVING SIDE: take the clean byte, then dirty it

    The acquire needs NO new machinery at all — [WeakLock.wacquire_core] is
    verbatim what a lock does, and the payload it thaws is an ordinary
    [x ↦w{1} v].  The two steps below are what the RECEIVER does with it: one
    line to re-own ([wpt_own_of_wpt] — a clean full-fraction byte is owned by
    whoever holds it, which is the whole reason the payload had to be flipped
    on the way out), and one store to dirty it again, under the NEW author.
    That closes the cycle [WDirty A] → [WClean] → [WDirty B]. *)

Section receive.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  (* the RECEIVING thread's context — again exactly one (§1.7) *)
  Context `{XI : CurCtx}.

  Lemma vwp_hold_ent (P Q : vProp Σ) (ws : wstate) :
    (P ⊢ Q) -> vwp_hold P ws ⊢ vwp_hold Q ws.
  Proof. intros HPQ. rewrite /vwp_hold HPQ. done. Qed.

  (** RE-OWNING.  One line, and it is the whole "receive". *)
  Lemma pp_receive (x : Z) (v : bv 8) (ws : wstate) :
    vwp_hold (x ↦w v) ws ⊢ vwp_hold (x ↦wo v) ws.
  Proof. apply vwp_hold_ent, wpt_own_of_wpt. Qed.

  (** DIRTYING IT AGAIN, under the new author.  [WeakVProp.wpt_store_rule_own]
      with the message's class pinned to [WCplain], so that the postcondition
      is the SHARP [wpt_dirty] rather than the absorbing [↦wo] — which is what
      makes "the author alternated" a statement and not a hope.  (A ported
      store site wants the absorbing form; this one exists for the exhibit.) *)
  Lemma wpt_store_rule_dirty (ξ : CtxId) (c : CPU) σ σ' m a v v' :
    msg_byte m a = Some v' ->
    (∀ a', a' ≠ a -> msg_byte m a' = None) ->
    wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain ->
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [m])%list ->
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat ->
    wlog_auth (wm_log σ') -∗ ctx_migr ξ c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own ξ a v) (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr ξ c ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_dirty ξ c a v') (wm_ws σ').
  Proof.
    intros Hma Hother Htid Hk Himg Hlog Hfl.
    iIntros "Hlg Hmg Hi Hpt". rewrite wpt_own_at.
    iDestruct "Hpt" as (t) "(He & Hs & _)".
    iMod (wown_ctx_retarget ξ c a t v (wm_img σ) (wm_log σ) (wm_log σ')
            ltac:(rewrite Hlog; by apply pub_transfer_snoc)
            with "Hlg Hmg Hi He Hs") as "(Hlg & Hmg & Hi & He & Hs)".
    iMod (ctx_migr_mint ξ c (wm_log σ') (S (length (wm_log σ)))
            ltac:(rewrite Hlog length_app /=; lia) with "Hlg Hmg")
      as "(Hlg & Hmg & #Hbc)".
    iDestruct (ctx_wrote_byte ξ c a (S (length (wm_log σ))) with "Hbc")
      as "#Hbca".
    iFrame "Hlg Hmg".
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hcauth & %Hagc)".
    rewrite /wlat_elem /wcds_el.
    iDestruct (ghost_map_lookup with "Hcauth Hsel") as %Hlk.
    iMod (ghost_map_update (S (length (wm_log σ)), v') with "Hauth He")
      as "[Hauth He]".
    iMod (ghost_map_update (WDirty c) with "Hcauth Hsel") as "[Hcauth Hsel]".
    iModIntro. rewrite Himg Hlog. iSplitL "Hauth Hcauth".
    - iExists _, _. iFrame "Hauth Hcauth". iSplitR.
      { iPureIntro. by apply wlat_agree_store. }
      iPureIntro. intros a' s' Ha'.
      destruct (decide (a' = a)) as [->|Hne].
      + rewrite lookup_insert in Ha'. simplify_eq.
        replace (WDirty c) with (wcds_own_step c (wm_ak m) s)
          by (rewrite Hk; reflexivity).
        by apply wcds_ok_store_own; [| |apply (Hagc a s Hlk)].
      + rewrite lookup_insert_ne // in Ha'.
        apply wcds_ok_app; [|by apply Hagc].
        intros m0 Hm0. apply elem_of_list_singleton in Hm0 as ->.
        by apply Hother.
    - rewrite wpt_dirty_at. iExists (S (length (wm_log σ))).
      rewrite /wdirty /wcds_el. iFrame "He Hsel Hbca". by iPureIntro.
  Qed.

  (** ... at the machine's own store post-state, where the view premise is
      automatic — the [WeakVProp.wpt_store_post_own] twin. *)
  Lemma wpt_store_post_dirty (ξ : CtxId) (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' ->
    (∀ a', a' ≠ a -> msg_byte m a' = None) ->
    wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain ->
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr ξ c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own ξ a v) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr ξ c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (wpt_dirty ξ c a v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Htid Hk.
    iApply (wpt_store_rule_dirty ξ c
              (WMState (wm_regs σ) (wm_img σ) (wm_log σ) (wm_ws σ) (wm_dev σ))
              (WMState (wm_regs σ) (wm_img σ) ((wm_log σ ++ [m])%list)
                       (store_post (wm_ws σ) rl a (S (length (wm_log σ))))
                       (wm_dev σ)));
      [exact Hma|exact Hother|exact Htid|exact Hk|reflexivity|reflexivity|].
    apply flr_store_post.
  Qed.

  (** ... and its AMBIENT form (φ-upgrade §1.7), which is what an access site
      writes: the context comes from the [CurCtx] instance, so the line is the
      same before and after a migration.  [wpt_store_rule_dirty] /
      [wpt_store_post_dirty] stay [ξ]-explicit above, as the primitives a
      two-context proof can still use at both of its contexts. *)
  Lemma wpt_store_post_dirty_cur (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' ->
    (∀ a', a' ≠ a -> msg_byte m a' = None) ->
    wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain ->
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr cur_ctx c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (a ↦wo v) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr cur_ctx c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (wpt_dirty cur_ctx c a v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof. apply wpt_store_post_dirty. Qed.

(* ====================================================================== *)
(** ** 4'. ONE ACQUIRE, AND WHAT THE ACQUIRER GETS

    [WeakLock.wacquire_core] specialised to "the lock word read 0", which is
    the branch a spin loop eventually takes.  At the WP altitude the caller
    knows the word because [WeakAcquire.wacq_cb] hands it the flat fact; here
    it is the premise, and [WeakAcquire.wflat_word_agree] identifies the two
    readings — exactly as [wwp_acquire_swap] does internally. *)

  Lemma pp_acquire_payload (γ : gname) (lk : Arch.pa) (x : Z) (v : bv 8)
      (c : CPU) (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) -> acc_wf lk 4 ->
    wQ_amo_aq tid lk lock_one σ σ' ->
    (∀ j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk (x ↦w v) ∗
    locked γ c ∗ vwp_hold (x ↦w v) (wm_ws σ').
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv".
    iDestruct (wacquire_core γ lk (x ↦w v) c tid σ σ' Hwf Hacc HQ with "Hi Hinv")
      as (v0) "[%Hflat Hupd]".
    assert (Hv : lock_zero = v0)
      by exact (wflat_word_agree σ lk lock_zero v0 Hzero Hflat).
    iMod "Hupd" as "(Hi & Hbody & Harm)".
    iDestruct "Harm" as "[(_ & HR & Htok)|%Hne]"; [|by rewrite -Hv in Hne].
    iModIntro. by iFrame "Hi Hbody Htok HR".
  Qed.

  Corollary pp_acquire_own (γ : gname) (lk : Arch.pa) (x : Z)
      (v : bv 8) (c : CPU) (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) -> acc_wf lk 4 ->
    wQ_amo_aq tid lk lock_one σ σ' ->
    (∀ j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ lk (x ↦w v) ∗
    locked γ c ∗ vwp_hold (x ↦wo v) (wm_ws σ').
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv".
    iMod (pp_acquire_payload γ lk x v c tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hinv") as "($ & $ & $ & HR)".
    iModIntro. by iApply (pp_receive x v (wm_ws σ')).
  Qed.

  (** THE RECEIVER'S OWN STORE, in one step from the payload: take the clean
      byte the handoff delivered and plain-store to it.  The postcondition is
      [wpt_dirty c] at the RECEIVING hart — the author has alternated, and the
      byte is now unpublishable by anyone else until [c] releases it. *)
  Corollary pp_receive_and_dirty (c : CPU) (σ : wmstate) (m : wmsg)
      (x : Z) (v v' : bv 8) (rl : bool) :
    msg_byte m x = Some v' ->
    (∀ a', a' ≠ x -> msg_byte m a' = None) ->
    wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain ->
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr cur_ctx c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (x ↦w v) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr cur_ctx c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (wpt_dirty cur_ctx c x v')
      (store_post (wm_ws σ) rl x (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Htid Hk. iIntros "Hlg Hmg Hi HR".
    iApply (wpt_store_post_dirty_cur c σ m x v v' rl Hma Hother Htid Hk
              with "Hlg Hmg Hi").
    by iApply (pp_receive x v (wm_ws σ)).
  Qed.

End receive.

(* ====================================================================== *)
(** ** 4. THE SAME RELEASE AT THE WP ALTITUDE — one [sw] through the invariant

    [WeakAcquire.wwp_release_store] with the owned payload, and the exemplar a
    ported release site copies.  The DIFF from the landed rule is exactly
    three lines of statement and two of proof:

      - the callback hands over [wpt_own cpu_id x v] instead of an abstract
        [R] (and gets its private [wpt_dirty cpu_id y w] back on the far
        side, at the post-state index);
      - the rule takes [ak_latest akw = false] — the release [sw] is not an
        AMO — which is what §1 needs to read [WCrel] off the trace;
      - the proof calls [wrelease_flip_core] where the original called
        [WeakLock.wrelease_core], and derives its log premise with
        [wQ_eff_store_rel] from the [wQ_eff] conjunct the certificate already
        carries for φ's sake.

    The φ payment is UNCHANGED, and that is worth noticing: the store's own
    footprint is the fetch window and the lock word, neither of which is the
    byte that got flipped, so the flip costs the violation-freedom argument
    nothing. *)

Section wp_pingpong.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context `{XI : CurCtx}.

  Definition wrel_own_cb (x y : Z) (v w : bv 8)
      (pc : SailStdpp.Values.mword 64) (P : wmstate → Prop) : iProp Σ :=
    (∀ σ : wmstate,
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑wlockN, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜P σ⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → nv_ok (wm_log σ) cpu_id (acc_addr pc j)⌝ ∗
         (* the [fence rw,w] at [pc-4], as in [WeakAcquire.wrel_cb] — and here
            it is LOAD-BEARING twice over: it makes the message [WCrel], which
            is both what keeps the lock word clean and what licenses the flip *)
         ⌜w_relp (wm_ws σ) = true⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         vwp_hold (x ↦wo v) (wm_ws σ) ∗
         vwp_hold (wpt_dirty cur_ctx cpu_id y w) (wm_ws σ) ∗
         ∃ t0 t1 : mstate,
           ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
           ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
           ▷ (∀ (tick : bool) (σ' : wmstate),
                ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
                vwp_hold (wpt_dirty cur_ctx cpu_id y w) (wm_ws σ') -∗
                |={∅, ⊤ ∖ ↑wlockN}=> wmstate_rest_nonv σ' ∗
                  (* the migration invariant comes back to the thread: it is
                     scheduler state, not part of the memory frame *)
                  (ctx_migr cur_ctx cpu_id -∗ WWP Loop)))%I.

  Lemma wwp_release_flip (γ : gname) (lk : Arch.pa) (x y : Z)
      (v w : bv 8) (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    (* the release store is a plain [sw], not an AMO — §1's side condition *)
    ak_latest akw = false →
    (∀ a : Z, weff_touches (WEread akf pf nf) a →
       ∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) →
    inv wlockN (wlock_inv γ lk (x ↦w v)) -∗
    locked γ cpu_id -∗
    (* the scheduler resource the ctx conversion threads anyway; NOT a memory
       fact, and it comes straight back out *)
    ctx_migr cur_ctx cpu_id -∗
    wrel_own_cb x y v w pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw lk 4 lock_zero]) -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc Hacclk Hlatw Hfetch. iIntros "#Hinv Htok Hmg Hk".
    rewrite /wrel_own_cb.
    assert (Hfoot : ∀ a : Z,
              weffs_touch [WEread akf pf nf; WEwrite akw lk 4 lock_zero] a →
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) ∨
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr lk j)).
    { intros a Ha. apply weffs_touch_cons in Ha as [Ha|Ha].
      - left. by apply Hfetch.
      - right. destruct (weffs_touch_write1 _ lk _ _ a Ha) as (j & Hj & ->).
        exists j. split; [cbn in Hj; lia|done]. }
    iApply (wp_winstr pc
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread akf pf nf; WEwrite akw lk 4 lock_zero])
              (wQ_fr (wQ_store (Some (fin_to_nat cpu_id)) lk lock_zero)
                     (Some (fin_to_nat cpu_id))
                     [WEread akf pf nf; WEwrite akw lk 4 lock_zero])
              Hgid Haccpc).
    { apply wstep_cert_fr.
      exact (wcert_store (fin_to_nat cpu_id) pc akf pf nf akw lk lock_zero). }
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    iDestruct (wmstate_rest_nv with "Hrest") as %Hnvσ.
    iInv wlockN as "Hbody" "Hclose".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & %Hnvpc & %Hrelp & Hlat & Hx & Hy & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQfr".
    destruct HQfr as [HQ HQeff].
    (* §1: the class of the message this step appended *)
    assert (Hlog : wm_log σ' =
              (wm_log σ ++ [wwrite_msg (Some (fin_to_nat cpu_id))
                              WCrel lk 4 lock_zero])%list)
      by exact (wQ_eff_store_rel _ akf pf nf akw lk lock_zero σ σ'
                  Hlatw Hrelp HQeff).
    (* the continuation FIRST: the log authority the retarget and the mint
       ride lives in the POST-state remainder it returns *)
    iMod ("Hcont" $! tick σ' with "[%] [Hy]") as "[Hrest Hk2]"; [exact Hpost| |].
    { iApply (wpt_dirty_mono cur_ctx cpu_id y w (wm_ws σ) (wm_ws σ'));
        [|iFrame].
      exact (wstep_post_ws_le σ σ' _ Hpost). }
    iDestruct "Hrest" as "(%Hb' & %Hw' & Hr & Hd & Hlogauth & Hws)".
    iMod (wrelease_flip_core γ lk x v cpu_id σ σ' HQ Hlog Hbnd
            with "Hlogauth Hmg Hlat Hbody Htok Hx")
      as "(Hlogauth & Hmg & Hlat & Hbody)".
    (* the φ payment, verbatim [WeakAcquire.wwp_release_store]'s: the fetch
       window transports across an own append, and the lock word's bundle
       comes back CLEAN out of the invariant *)
    iAssert (⌜nv_hart (wm_log σ') cpu_id (wm_ws σ')⌝)%I as %Hnv'.
    { iDestruct "Hbody" as (st' t' v'') "[Hw' Hlk']".
      iDestruct (nv_ok_wlat4L cpu_id _ _ lk t' v''
                   with "Hlat Hw'") as %Hnvlk.
      iPureIntro.
      apply (nv_hart_of_wQ_eff_ok cpu_id σ σ'
               [WEread akf pf nf; WEwrite akw lk 4 lock_zero] HQeff Hnvσ).
      intros a Ha. destruct (Hfoot a Ha) as [(j & Hj & ->)|(j & Hj & ->)].
      - rewrite Hlog. intros n. apply nv_byte_app_own; [by apply Hnvpc|].
        intros m Hm. apply elem_of_list_singleton in Hm as ->. reflexivity.
      - by apply Hnvlk. }
    iSpecialize ("Hk2" with "Hmg").
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iFrame "Hk2".
    iApply (wmstate_interp_split σ'). iFrame "Hlat".
    iApply (wmstate_rest_of_nonv σ' with "[%]"); [exact Hnv'|].
    rewrite /wmstate_rest_nonv. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iFrame "Hr Hd Hws Hlogauth".
  Qed.

  (** ... AND THE OTHER SIDE OF THE HANDOFF NEEDS NO NEW RULE AT ALL.  The
      spin-acquire is [WeakAcquire.wwp_acquire_loop_cert] at [R := x ↦w{1} v],
      instantiated and nothing else — the payload being a transferred owned
      byte rather than a persistent fact is invisible to the acquire, because
      the flip already happened on the far side.  That asymmetry (all of the
      protocol's work at the release, none at the acquire) is the design's,
      not this file's; recording it as a one-line corollary is the cheapest
      way to keep it checked. *)
  Corollary wwp_pingpong_acquire (γ : gname) (lk : Arch.pa) (x : Z) (v : bv 8)
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (aka akw : akinfo) (K : iProp Σ) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf lk 4 →
    ak_coh aka = false →
    ak_sync aka = true →
    ak_latest akw = true →
    (∀ a : Z, weff_touches (WEread akf pf nf) a →
       ∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) →
    inv wlockN (wlock_inv γ lk (x ↦w v)) -∗
    □ (K -∗ ▷ (K -∗ WWP Loop) -∗
         wacq_cb γ lk (x ↦w v) pc
           (wP_eff (Some (fin_to_nat cpu_id))
              [WEread akf pf nf; WEread aka lk 4; WEwrite akw lk 4 lock_one])) -∗
    K -∗ WWP Loop.
  Proof.
    exact (wwp_acquire_loop_cert γ lk (x ↦w v) pc akf pf nf aka akw K).
  Qed.

End wp_pingpong.

(* ====================================================================== *)
(** ** 5. THE PAYOFF: what the receiving hart's load returns

    The composition, at the altitude [WkStartedMp]'s §4 states it: one hart's
    acquire followed by its own plain load of the transferred byte.  Every
    admissible timestamp for that byte carries the value the OTHER hart wrote
    before its release — no staleness is reachable — and the loading hart ends
    up OWNING it.

    WHY THE TWO LEGS ARE NOT ONE LEMMA is [WkStartedMp]'s reason verbatim:
    [wlat_interp] is the authority over the latest-write map, so no
    proposition can hold it at the releaser's state and at the acquirer's
    later state at once.  The two halves are joined by the machine, and the
    medium is the lock body — literally the same [wlock_inv γ lk (x ↦w v)] on
    both sides.  That IS the handoff. *)

Section payoff.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{XI : CurCtx}.

  Corollary pp_handoff_load (γ : gname) (lk : Arch.pa) (x : Z)
      (v : bv 8) (c : CPU) (tid : option nat) (σ σ' σn : wmstate)
      (ak : akinfo) (t' : nat) (b : bv 8) :
    (* --- the acquire: the swap read 0, so the payload is thawed here --- *)
    wlog_wf (wm_log σ) -> acc_wf lk 4 ->
    wQ_amo_aq tid lk lock_one σ σ' ->
    (∀ j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) ->
    (* --- and then a PLAIN load of [x] at a state with the same memory --- *)
    ak_coh ak = false ->
    wm_img σn = wm_img σ' -> wm_log σn = wm_log σ' ->
    ws_le (wm_ws σ') (wm_ws σn) ->
    wbyte_ok σn ak x t' b ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) ==∗
    wlat_interp (wm_img σn) (wm_log σn) ∗ wlock_inv γ lk (x ↦w v) ∗
    locked γ c ∗ ⌜b = v⌝ ∗ vwp_hold (x ↦wo v) (wm_ws σn).
  Proof.
    intros Hwf Hacc HQ Hzero Hcoh Himg Hlog Hle Hok. iIntros "Hi Hinv".
    iMod (pp_acquire_payload γ lk x v c tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hinv") as "(Hi & Hbody & Htok & HR)".
    (* carry the payload to the load's own state, then collapse the load *)
    iDestruct (vwp_hold_mono (x ↦w v) (wm_ws σ') (wm_ws σn) Hle with "HR")
      as "HR".
    rewrite -Himg -Hlog.
    iDestruct (wpt_load_rule σn σn ak x (DfracOwn 1) v t' b
                 Hcoh Hok eq_refl eq_refl ltac:(lia) with "Hi HR")
      as "(%Hv & Hi & HR)".
    iModIntro. iFrame "Hi Hbody Htok". iSplitR; [by iPureIntro|].
    by iApply (pp_receive x v (wm_ws σn)).
  Qed.

  (** THE RETURN LEG, and the whole point of calling it a PING-PONG: the same
      statement at the hart that STARTED the example, carrying its private
      byte through.  [y] entered A's first release dirty, crossed the handoff
      to B and back, and is still [WDirty A] here — while [x], which made the
      same trip, is now A's again with the value B left in it.

      Two bytes, one release, one flip: the protocol is per-byte, and this
      statement is where that stops being a claim. *)
  Corollary pp_return_leg (γ : gname) (lk : Arch.pa) (x y : Z)
      (v w : bv 8) (cA : CPU) (tid : option nat) (σ σ' σn : wmstate)
      (ak : akinfo) (t' : nat) (b : bv 8) :
    wlog_wf (wm_log σ) -> acc_wf lk 4 ->
    wQ_amo_aq tid lk lock_one σ σ' ->
    (∀ j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) ->
    ak_coh ak = false ->
    wm_img σn = wm_img σ' -> wm_log σn = wm_log σ' ->
    ws_le (wm_ws σ') (wm_ws σn) ->
    wbyte_ok σn ak x t' b ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ lk (x ↦w v) -∗
    vwp_hold (wpt_dirty cur_ctx cA y w) (wm_ws σ) ==∗
    wlat_interp (wm_img σn) (wm_log σn) ∗ wlock_inv γ lk (x ↦w v) ∗
    locked γ cA ∗ ⌜b = v⌝ ∗
    vwp_hold (x ↦wo v) (wm_ws σn) ∗
    vwp_hold (wpt_dirty cur_ctx cA y w) (wm_ws σn).
  Proof.
    intros Hwf Hacc HQ Hzero Hcoh Himg Hlog Hle Hok.
    iIntros "Hi Hinv Hy".
    iMod (pp_handoff_load γ lk x v cA tid σ σ' σn ak t' b
            Hwf Hacc HQ Hzero Hcoh Himg Hlog Hle Hok with "Hi Hinv")
      as "($ & $ & $ & $ & $)".
    iModIntro.
    iApply (wpt_dirty_mono cur_ctx cA y w (wm_ws σ) (wm_ws σn)); [|iFrame].
    etrans; [exact (proj1 (proj2 (proj2 (proj1 HQ)))) | exact Hle].
  Qed.

(* ====================================================================== *)
(** ** 6. THE THREE ARMS OF φ, IN ONE STATEMENT

    Every instruction of both programs fetches, so every leaf owes the
    interpretation's violation-freedom conjunct at its POST-log, one
    [WeakGhost.nv_byte] per byte its own effect trace touches
    ([WeakCert.nv_hart_of_wQ_eff_ok]).  Across this example the bytes touched
    are of exactly three kinds, and each is paid by a DIFFERENT resource — the
    exhibit below is the whole trichotomy at one state:

      - the FETCH WINDOW: text, never written, [nv_ok_unwritten] (the
        vacuous arm every leaf uses);
      - the TRANSFERRED / PRIVATE byte: owned, possibly DIRTY, paid by the
        owned points-to itself ([WeakVProp.nv_ok_of_wpt_own_at], which case-
        splits on the dirty author internally) — this is the arm no clean
        fragment and no view bound can substitute for, and the reason the
        C/D/S protocol exists;
      - the LOCK WORD: clean inside the invariant, paid by the ordinary
        points-to ([nv_ok_of_pointsto]).  It stays clean because the AMO's
        write half is [WCexcl] and the release's is [WCrel] — neither is an
        owned store — so no [WSync] mint is needed. *)

  Lemma pp_phi_three_arms (c : CPU) (img : _) (log : list wmsg)
      (ws : wstate) (pcb x lkb : Z) (vx : bv 8) (dq : dfrac) (t : nat)
      (vl : bv 8) :
    latest_ts log pcb = 0%nat ->
    wlog_auth log -∗ ctx_migr cur_ctx c -∗
    wlat_interp img log -∗
    vwp_hold (x ↦wo vx) ws -∗
    wlat_pointsto lkb dq t vl -∗
    ⌜nv_ok log c pcb ∧ nv_ok log c x ∧ nv_ok log c lkb⌝.
  Proof.
    intros Htext. iIntros "Hlg Hmg Hi Hx Hlk".
    iDestruct (nv_ok_of_wpt_own_at_cur c x vx img log ws with "Hlg Hmg Hi Hx")
      as %Hnx.
    iDestruct (nv_ok_of_pointsto img log c lkb dq t vl with "Hi Hlk") as %Hnl.
    iPureIntro. split_and!; [by apply nv_ok_unwritten|exact Hnx|exact Hnl].
  Qed.

End payoff.

(* ======================================================================
   WHAT A PORTED PROOF TAKES FROM THIS FILE, in the order it needs it.

   1. Own-store sites are uniform: [WeakVProp.wpt_store_rule_own] in,
      [wpt_own ξ] out — or, ambiently (item 5),
      [wpt_store_rule_own_cur] in and [a ↦wo v'] out.
      Do NOT case-split on the class; the absorbing form is
      there so you never have to.  ([wpt_store_rule_dirty] above exists only
      because this file has to SAY "dirty" in a statement.)  Since φ-upgrade
      §1.6 the rule also takes the POST-log authority and the context's
      migration invariant [WeakGhost.ctx_migr ξ c] — both threaded at every
      store site whether or not the thread has ever been rescheduled, and
      both returned unchanged; they are what let the rule retarget a byte
      this context dirtied on a hart it has since left, WITHOUT the caller
      knowing that is what happened.

   2. At a release that egresses owned memory, three things change and no
      more:
        (a) the payload enters the release core in [↦wo] form;
        (b) the core is [wrelease_flip_core], not [WeakLock.wrelease_core];
        (c) its log premise comes from [wQ_eff_store_rel], off the [wQ_eff]
            conjunct the certificate already carries, under
            [ak_latest akw = false] (the store is an [sw], not an AMO) and
            the [w_relp] fact [WeakAcquire.wrel_cb] already delivers.
      The φ payment, the footprint premises and the fetch-window arm are all
      untouched — see [wwp_release_flip], whose proof differs from
      [WeakAcquire.wwp_release_store]'s in two lines.

   3. On the receiving side there is nothing to do but [wpt_own_of_wpt].
      A thread that wants to re-read what it just wrote uses
      [WeakVProp.wpt_load_rule_own], which is stated over the owned form and
      needs no migration machinery at all — a load moves no [wcds] state, so
      it reads a foreign-author dirty byte verbatim.  (This closes the gap
      this file recorded at Stage 1: the loads below sit before the receiving
      store only because that is the program's order.)

   4. THE INDEX IS A CONTEXT, NOT A HART.  [wpt_own ξ] and [wpt_dirty ξ c]
      are propositions about the thread, so they frame across a yield
      unchanged; [WkYieldFrame] is where that is exercised, and §4a of that
      file applies one access block on both sides of a migration.  The
      hart-indexed byte form [WeakVProp.wpt_own_h] survives only as the
      carrier of the M-mode 4/8-byte towers, which never migrate.

   5. AND THE CONTEXT IS NOT WRITTEN AT ALL (φ-upgrade §1.7).  Every section
      of this file takes ONE [`{XI : CurCtx}] — a thread's own context, the
      way a hart arrives as [`{CID : CpuId}] — so the resource is the bare
      [x ↦wo v] and the rules are quoted in their ambient form
      ([WeakVProp]'s [_cur] wrappers, [wpt_store_post_dirty_cur] here).  The
      [ξ]-explicit primitives are still there and are what a lemma with TWO
      contexts in scope must use: a lemma joining a release leg to an
      acquire leg has the releaser's context AND the acquirer's, and written
      ambiently it would compile while silently identifying them.  Each
      lemma below is one leg, which is why the ambient form is honest here.
      See [WeakVProp] §3'' for the convention and the measured hazard. *)

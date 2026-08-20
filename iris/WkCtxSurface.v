(** * WkCtxSurface.v — THE ACCEPTANCE TEST FOR THE iPROP SURFACE
      (φ-upgrade §1.8)

    [WkYieldFrame] and [WkOwnPingPong] are the two migration tests: one thread
    keeping its own bytes across a change of CPU, and two threads handing a
    byte back and forth through a lock.  Their FUNCTION-PROOF-SIDE lemmas are
    restated here over the [iProp] surface — [WeakCtxPt]'s [↦wpo] / [↦wp{dq}]
    and [ctx_own], [WeakCtxLock]'s lock contexts — and the test is what the
    STATEMENTS look like.  Read §2 and §4 next to their originals:

      - NO VIEW AND NO [monPred] APPEARS IN ANY STATEMENT.  The [vProp]
        versions carry [vwp_hold P ws] in every memory slot, so the [wstate]
        of the pre-state and of the post-state are written into the
        specification; here [x ↦wpo v] is a proposition with no state in it at
        all, and the fact in the precondition and the fact in the
        postcondition are literally the same term.
      - NO FRAMING STEP AT A STATE CHANGE.  [WkYieldFrame] §4a ends with
        [vwp_hold_mono] to carry the untouched [z] across the store's view
        growth; [WkOwnPingPong]'s [wrelease_flip_frame] and [pp_return_leg]
        each end with [wpt_dirty_mono] for the same reason.  Here those lines
        are [iFrame], because there is nothing to move.
      - NO FREEZE AND NO THAW AT THE YIELD.  [WkYieldFrame] §4c freezes T's
        facts at the parking index and §4d thaws them with [vwp_hold_intro];
        §3 below frames them through the park and the resume with [iFrame],
        and the resume's [⌜V ⊑ ws_view …⌝] postcondition is gone from the
        specification entirely — it is inside [ctx_own].
      - NO UPGRADE AND NO RE-INDEX AT AN ACCESS SITE.  §2's access block is
        ONE lemma, applied on the hart that dirtied the byte and on the hart
        that resumed the thread; the ξ_L ↔ ξ re-indexing appears only in the
        signatures of §4's lock lemmas, whose bodies a function proof never
        opens.

    WHAT IS THE API.  This file's spellings are.  [WkYieldFrame] and
    [WkOwnPingPong] keep their [vProp] statements — they are the internal
    glue's own tests, and the lemmas here are proved BY them, which is the
    cheapest possible check that the two layers agree. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
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
Require Import WeakCtx.
Require Import WeakCtxPt.
Require Import WeakCtxLock.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakCert.
Require Import WeakViolation.
Require Import WeakLock.
Require Import WeakAcquire.
Require Import WkOwnPingPong.
Require Import WkYieldFrame.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpLock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE SHARP EXHIBIT FORM — a points-to that SAYS "dirty"

    [WeakCtxPt.wptsto] absorbs clean-and-dirty on purpose, and a ported store
    site wants exactly that.  For the two examples' claims — "the private byte
    is still dirty on the far side of the handoff", "the author alternated
    across a migration" — the absorbing form is one bit too coarse, exactly as
    [WkOwnPingPong.wpt_dirty] is the sharpened [wpt_own].  This is the same
    sharpening at the [iProp] altitude, used only in statements. *)

Section dirty.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wptsto_dirty (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8) : iProp Σ :=
    (∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wdirty c a ∗
                ctx_wrote ξ c (view_byte a t) ∗
                ctx_view_lb ξ (view_byte a t))%I.

  Lemma wptsto_dirty_own ξ c a v : wptsto_dirty ξ c a v -∗ wptsto ξ a v.
  Proof.
    iIntros "[%t (He & Hd & #Hw & #Hf)]". iExists t. iFrame "He Hf".
    by iApply (wown_ctx_of_dirty with "Hd Hw").
  Qed.

  Lemma wptsto_dirty_to_pt ξ c ws a v :
    ctx_lb ξ ws -∗ wptsto_dirty ξ c a v -∗
    ctx_lb ξ ws ∗ vwp_hold (wpt_dirty ξ c a v) ws.
  Proof.
    iIntros "Hlb [%t (He & Hd & #Hw & #Hf)]".
    iDestruct (ctx_lb_valid with "Hlb Hf") as "[$ %Hle]".
    iApply (wpt_dirty_at_intro ξ c a v t ws with "He Hd Hw").
    by apply view_byte_le.
  Qed.

  Lemma wptsto_dirty_of_pt ξ c ws a v :
    ctx_auth ξ (ws_view ws) -∗ vwp_hold (wpt_dirty ξ c a v) ws -∗
    ctx_auth ξ (ws_view ws) ∗ wptsto_dirty ξ c a v.
  Proof.
    iIntros "Ha Hpt". rewrite wpt_dirty_at.
    iDestruct "Hpt" as (t) "(He & Hd & Hw & %Ht)".
    iDestruct (ctx_view_lb_get ξ (ws_view ws) (view_byte a t) with "Ha")
      as "#Hf"; [by apply view_byte_le|].
    iFrame "Ha". iExists t. by iFrame "He Hd Hw Hf".
  Qed.

End dirty.

(* ====================================================================== *)
(** ** 2. THE ACCESS BLOCK — [WkYieldFrame] §4a on the [iProp] surface

    [load x; x := 2; load z], with [x] owned (and possibly dirtied on a hart
    the thread has since left) and [z] a shared clean byte.  This is Stage
    1.6's acid test at Stage 1.8's altitude: §2b instantiates it on hart A
    BEFORE the yield and §2c on hart B AFTER the migration, and the two lines
    differ in the hart and the state and in nothing else.

    COMPARE THE STATEMENT WITH [WkYieldFrame.wyf_touch]:

      there   vwp_hold (x ↦wo vx) (wm_ws σ) -∗ vwp_hold (z ↦w{q} vz) (wm_ws σ)
              …
              vwp_hold (wpt_dirty cur_ctx c x byte2) (store_post …) ∗
              vwp_hold (z ↦w{q} vz)                 (store_post …)
      here    (x ↦wpo vx) -∗ (z ↦wp{q} vz)
              …
              wptsto_dirty cur_ctx c x byte2 ∗ (z ↦wp{q} vz)

    — the clean byte's slot is the SAME TERM in the precondition and the
    postcondition, and neither slot names a [wstate].  What replaced the
    [ctx_migr] argument is [ctx_own_at], which carries it. *)

Section touch.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  (** THREAD T'S CONTEXT, AMBIENT — ONE instance for the section, exactly as
      in [WkYieldFrame] §4 and for the same reason: the [x ↦wpo vx] of §2b (on
      hart A) and the [x ↦wpo vx] of §2c (on hart B) must be the SAME
      proposition, and they are, because they resolve to this hypothesis. *)
  Context `{XI : CurCtx}.

  Lemma wcs_touch (c : CPU) (σ : wmstate) (m : wmsg)
      (x z : Z) (vx vz : bv 8) (q : dfrac)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) (rl : bool) :
    ak_coh akx = false → wbyte_ok σ akx x tx bx →
    ak_coh akz = false → wbyte_ok σ akz z tz bz →
    msg_byte m x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_ak m = WCplain →
    wlog_auth ((wm_log σ ++ [m])%list) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    ctx_own_at cur_ctx c (wm_ws σ) -∗
    (x ↦wpo vx) -∗ (z ↦wp{q} vz) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ctx_own_at cur_ctx c (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) ∗
    ⌜bx = vx⌝ ∗ ⌜bz = vz⌝ ∗
    wptsto_dirty cur_ctx c x byte2 ∗ (z ↦wp{q} vz).
  Proof.
    intros Hcohx Hokx Hcohz Hokz Hmb Hother Htid Hk.
    iIntros "Hlg Hi [Hlb Hmg] Hx Hz".
    (* into the internal glue … *)
    iDestruct (wptsto_to_own with "Hlb Hx") as "[Hlb Hx]".
    iDestruct (wptsto_cl_to_pt with "Hlb Hz") as "[Hlb Hz]".
    (* … the landed [vProp] access block, unchanged … *)
    iMod (wyf_touch c σ m x z vx vz q akx akz tx tz bx bz rl
            Hcohx Hokx Hcohz Hokz Hmb Hother Htid Hk
            with "Hlg Hmg Hi Hx Hz")
      as "($ & Hmg & $ & $ & $ & Hx & Hz)".
    (* … and back out, with the ledger registered at the store's post-view *)
    iMod (ctx_lb_sync cur_ctx
            (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) with "[Hlb]")
      as "Ha".
    { iApply (ctx_lb_mono with "Hlb"). apply ws_view_mono, store_post_le. }
    iDestruct (wptsto_dirty_of_pt with "Ha Hx") as "[Ha $]".
    iDestruct (wptsto_cl_of_pt with "Ha Hz") as "[Ha $]".
    iModIntro. iFrame "Hmg". by iApply (ctx_lb_of_auth with "Ha").
  Qed.

(* ---------------------------------------------------------------------- *)
(** *** 2b/2c. THE SAME LEMMA ON BOTH SIDES OF A MIGRATION

    Two corollaries whose statements differ only in the hart and the machine
    state, and whose proofs are the same one line.  In §2c the byte [x] is
    still [WDirty A] in the ghost map and [B ≠ A]; there is no upgrade lemma
    in either proof and no token threaded that could make one possible. *)

  Corollary wcs_touch_A (A : CPU) (σ : wmstate) (m : wmsg)
      (x z : Z) (vz : bv 8) (q : dfrac)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) (rl : bool) :
    ak_coh akx = false → wbyte_ok σ akx x tx bx →
    ak_coh akz = false → wbyte_ok σ akz z tz bz →
    msg_byte m x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat A) →
    wm_ak m = WCplain →
    wlog_auth ((wm_log σ ++ [m])%list) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    ctx_own_at cur_ctx A (wm_ws σ) -∗
    (x ↦wpo byte1) -∗ (z ↦wp{q} vz) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ctx_own_at cur_ctx A (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) ∗
    ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
    wptsto_dirty cur_ctx A x byte2 ∗ (z ↦wp{q} vz).
  Proof. apply wcs_touch. Qed.

  Corollary wcs_touch_B (B : CPU) (σ : wmstate) (m : wmsg)
      (x z : Z) (vz : bv 8) (q : dfrac)
      (akx akz : akinfo) (tx tz : nat) (bx bz : bv 8) (rl : bool) :
    ak_coh akx = false → wbyte_ok σ akx x tx bx →
    ak_coh akz = false → wbyte_ok σ akz z tz bz →
    msg_byte m x = Some byte2 →
    (∀ a', a' ≠ x → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat B) →
    wm_ak m = WCplain →
    wlog_auth ((wm_log σ ++ [m])%list) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    ctx_own_at cur_ctx B (wm_ws σ) -∗
    (x ↦wpo byte1) -∗ (z ↦wp{q} vz) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ctx_own_at cur_ctx B (store_post (wm_ws σ) rl x (S (length (wm_log σ)))) ∗
    ⌜bx = byte1⌝ ∗ ⌜bz = vz⌝ ∗
    wptsto_dirty cur_ctx B x byte2 ∗ (z ↦wp{q} vz).
  Proof. apply wcs_touch. Qed.

(* ====================================================================== *)
(** ** 3. THE YIELD, WITH T'S FACTS IN THE FRAME

    [WkYieldFrame] §4c/§4d at this altitude, and the two statements ARE the
    deliverable.  The framed facts appear in the premise and in the conclusion
    as the same terms; the park's postcondition is one scheduler resource
    ([ctx_parked]), the resume's is [ctx_own] at the NEW cpu — a ∀-bound
    argument of the lemma, which is the [wp_next]-style re-binding.

    There is no freeze, no thaw, no [monPred_at], and no [⌜V ⊑ ws_view …⌝]
    anywhere: the proofs are the core plus [iFrame]. *)

  Corollary wcs_park_frames (γ : gname) (hf : Arch.pa) (A : CPU)
      (σ σ' : wmstate) (x z : Z) (vx vz : bv 8) (q : dfrac) :
    wQ_store (Some (fin_to_nat A)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat A)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton cur_ctx) -∗ locked γ A -∗
    ctx_own_at cur_ctx A (wm_ws σ) -∗
    (* ------------------------ THE FRAME ------------------------ *)
    (x ↦wpo vx) -∗ (z ↦wp{q} vz) ==∗
    (* ----------------------------------------------------------- *)
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wctx_baton cur_ctx) ∗ ctx_parked cur_ctx ∗
    (x ↦wpo vx) ∗ (z ↦wp{q} vz).
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hlog Hi Hinv Htok Hrun Hx Hz".
    iMod (wctx_park_core cur_ctx γ hf A σ σ' HQ Hlog Hbnd
            with "Hlog Hi Hinv Htok Hrun") as "($ & $ & $ & $)".
    by iFrame "Hx Hz".
  Qed.

  Corollary wcs_resume_frames (γ : gname) (hf : Arch.pa) (B : CPU)
      (tid : option nat) (σ σ' : wmstate) (x z : Z) (vx vz : bv 8)
      (q : dfrac) :
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton cur_ctx) -∗ ctx_parked cur_ctx -∗
    (* ------------------------ THE FRAME ------------------------ *)
    (x ↦wpo vx) -∗ (z ↦wp{q} vz) ==∗
    (* ----------------------------------------------------------- *)
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wctx_baton cur_ctx) ∗ locked γ B ∗
    ctx_own_at cur_ctx B (wm_ws σ') ∗
    (x ↦wpo vx) ∗ (z ↦wp{q} vz).
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv Hall Hx Hz".
    iMod (wctx_resume_core cur_ctx γ hf B tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hinv Hall") as "($ & $ & $ & $)".
    by iFrame "Hx Hz".
  Qed.

  (** ... and the composite the design asks for, at the shape a caller reads:
      the whole yield's user-facing pre/post is [ctx_own] in, [ctx_own] out,
      MEMORY-SILENT — no byte appears in either, and the thread's facts are
      the frame.  (The two halves cannot be one lemma: [wlat_interp] is the
      authority over the latest-write map, so no proposition holds it at the
      parking hart's state and at the resuming hart's later state at once —
      [WkStartedMp] §2's reason, verbatim.) *)
  Corollary wcs_yield_is_memory_silent (γ : gname) (hf : Arch.pa)
      (A B : CPU) (tid : option nat) (σ σ' σ2 σ2' : wmstate) :
    wQ_store (Some (fin_to_nat A)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat A)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_wf (wm_log σ2) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ2 σ2' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ2) (wm_log σ2) !! pa_add hf j
         = Some (nth_byte lock_zero j)) →
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton cur_ctx) -∗ locked γ A -∗
    ctx_own_at cur_ctx A (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wctx_baton cur_ctx) ∗
    (* the whole of what crosses: a scheduler resource, and the promise that
       WHATEVER cpu the scheduler picks, the bundle comes back there *)
    (wlat_interp (wm_img σ2) (wm_log σ2) -∗
     wlock_inv γ hf (wctx_baton cur_ctx) ==∗
       wlat_interp (wm_img σ2') (wm_log σ2') ∗
       wlock_inv γ hf (wctx_baton cur_ctx) ∗ locked γ B ∗
       ctx_own_at cur_ctx B (wm_ws σ2')).
  Proof.
    intros HQ Hlog Hbnd Hwf Hacc HQa Hzero.
    iIntros "Hlog Hi Hinv Htok Hrun".
    iMod (wctx_park_core cur_ctx γ hf A σ σ' HQ Hlog Hbnd
            with "Hlog Hi Hinv Htok Hrun") as "($ & $ & $ & Hall)".
    iModIntro. iIntros "Hi2 Hinv2".
    by iApply (wctx_resume_core cur_ctx γ hf B tid σ2 σ2' Hwf Hacc HQa Hzero
                 with "Hi2 Hinv2 Hall").
  Qed.

End touch.

(* ====================================================================== *)
(** ** 4. THE PING-PONG'S TWO LEGS, THROUGH A LOCK CONTEXT

    [WkOwnPingPong]'s function-proof-side lemmas restated.  The lock's own
    context ξ_L appears in the signatures — and ONLY there: it is bound by
    [WeakCtxLock.wctx_is_lock]'s existential (§4d), introduced into a proof
    once, and no access site and no function specification mentions it.  The
    re-indexing [ptsto[ξ_p] → ptsto[ξ_L]] at the release and
    [ptsto[ξ_L] → ptsto[ξ_q]] at the acquire happens inside these two
    lemmas' proofs, and there is nothing in either script here that does it. *)

Section legs.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  (* ONE thread's context per lemma — each of these is one leg (the releasing
     side's context and the acquiring side's are different contexts, and the
     medium between them is the lock).  ξ_L is the OTHER context in scope and
     is therefore spelled explicitly, per [WeakVProp] §3'''s convention. *)
  Context `{XI : CurCtx}.

  (** *** 4a. THE RELEASE LEG, with the private byte in the frame.

      [WkOwnPingPong.wrelease_flip_frame]'s statement, and the improvement is
      visible: there the private byte's slot is
      [vwp_hold (wpt_dirty …) (wm_ws σ)] IN and
      [vwp_hold (wpt_dirty …) (wm_ws σ')] OUT — two different propositions,
      joined by a [wpt_dirty_mono] step at the end of the proof.  Here it is
      the same proposition, and the step is [iFrame]. *)
  Lemma wcs_release_leg (γ : gname) (ξL : CtxId) (lk : Arch.pa) (x y : Z)
      (v w : bv 8) (i : CPU) (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) lk lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ') -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk <{ x ↦wp v }> ξL -∗
    wctx_held γ ξL cur_ctx i -∗
    ctx_own_at cur_ctx i (wm_ws σ) -∗
    (x ↦wpo v) -∗ wptsto_dirty cur_ctx i y w ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wclock_body γ lk <{ x ↦wp v }> ξL ∗
    ctx_own_at cur_ctx i (wm_ws σ) ∗ wptsto_dirty cur_ctx i y w.
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hlg Hi Hinv Hheld Hrun Hx Hy".
    iMod (wctx_release_byte γ ξL cur_ctx lk x v i σ σ' HQ Hlog Hbnd
            with "Hlg Hi Hinv Hheld Hrun Hx") as "($ & $ & $ & $)".
    by iFrame "Hy".
  Qed.

  (** *** 4b. THE ACQUIRE LEG — take the byte, re-own it.

      [WkOwnPingPong.pp_acquire_own] at this altitude.  The payload comes out
      of the lock's context and lands in the acquirer's, and the "receive" —
      [pp_receive], the clean-to-owned line — is [wptsto_of_cl], inside. *)
  Lemma wcs_acquire_leg (γ : gname) (ξL : CtxId) (lk : Arch.pa) (x : Z)
      (v : bv 8) (c : CPU) (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf lk 4 →
    wQ_amo_aq tid lk lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk <{ x ↦wp v }> ξL -∗
    ctx_own_at cur_ctx c (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wclock_body γ lk <{ x ↦wp v }> ξL ∗
    wctx_held γ ξL cur_ctx c ∗ ctx_own_at cur_ctx c (wm_ws σ') ∗
    (x ↦wpo v).
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv Hrun".
    iMod (wctx_acquire_core γ ξL cur_ctx lk <{ x ↦wp v }> c tid σ σ'
            Hwf Hacc HQ Hzero with "Hi Hinv Hrun") as "($ & $ & $ & $ & HR)".
    iModIntro. by iApply wptsto_of_cl.
  Qed.

  (** *** 4c. THE PAYOFF — the acquire followed by the receiver's own load.

      [WkOwnPingPong.pp_handoff_load]'s statement: every admissible timestamp
      for the transferred byte carries the value the OTHER thread wrote before
      its release, and the loading thread ends up owning it. *)
  Corollary wcs_handoff_load (γ : gname) (ξL : CtxId) (lk : Arch.pa) (x : Z)
      (v : bv 8) (c : CPU) (tid : option nat) (σ σ' σn : wmstate)
      (ak : akinfo) (t' : nat) (b : bv 8) :
    wlog_wf (wm_log σ) → acc_wf lk 4 →
    wQ_amo_aq tid lk lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) →
    ak_coh ak = false →
    wm_img σn = wm_img σ' → wm_log σn = wm_log σ' →
    ws_le (wm_ws σ') (wm_ws σn) →
    wbyte_ok σn ak x t' b →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk <{ x ↦wp v }> ξL -∗
    ctx_own_at cur_ctx c (wm_ws σ) ==∗
    wlat_interp (wm_img σn) (wm_log σn) ∗
    wclock_body γ lk <{ x ↦wp v }> ξL ∗
    wctx_held γ ξL cur_ctx c ∗ ctx_own_at cur_ctx c (wm_ws σn) ∗
    ⌜b = v⌝ ∗ (x ↦wpo v).
  Proof.
    intros Hwf Hacc HQ Hzero Hcoh Himg Hlog Hle Hok.
    iIntros "Hi Hinv Hrun".
    iMod (wcs_acquire_leg γ ξL lk x v c tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hinv Hrun") as "(Hi & $ & $ & Hrun & Hx)".
    iDestruct (ctx_own_at_mono cur_ctx c _ _ Hle with "Hrun") as "Hrun".
    rewrite -Himg -Hlog.
    iMod (wptsto_load_rule cur_ctx c σn σn ak x v t' b Hcoh Hok
            eq_refl eq_refl ltac:(reflexivity) with "Hi Hrun Hx")
      as "($ & $ & $ & $)".
    done.
  Qed.

  (** *** 4d. ξ_L IS INTERNAL — the client's handle, and its one destruct.

      This is the shape a ported lock spec has: the payload is written with
      bare [↦wp] inside [<{ … }>] and mentions no context at all, and the
      lock's context is the handle's existential.  A function proof opens it
      once, at the top, and every lemma of §4 is then applied at that name. *)
  Lemma wcs_is_lock_internal (γ : gname) (lk : Arch.pa) (x : Z) (v : bv 8) :
    wctx_is_lock γ lk <{ x ↦wp v }> -∗
    ∃ ξL : CtxId, inv wlockN (wclock_body γ lk <{ x ↦wp v }> ξL).
  Proof. iIntros "H". iExact "H". Qed.

(* ====================================================================== *)
(** ** 5. THE THREE ARMS OF φ, ON THE [iProp] SURFACE

    [WkOwnPingPong] §6 restated: the fetch window (text, never written), the
    owned byte (paid by the points-to itself, whichever hart dirtied it), and
    the lock word (clean inside the invariant).  The migration invariant comes
    out of [ctx_own]; nothing else changed. *)

  Lemma wcs_phi_three_arms (c : CPU) (img : _) (log : list wmsg)
      (ws : wstate) (pcb x lkb : Z) (vx : bv 8) (dq : dfrac) (t : nat)
      (vl : bv 8) :
    latest_ts log pcb = 0%nat →
    wlog_auth log -∗ ctx_own_at cur_ctx c ws -∗ wlat_interp img log -∗
    (x ↦wpo vx) -∗ wlat_pointsto lkb dq t vl -∗
    ⌜nv_ok log c pcb ∧ nv_ok log c x ∧ nv_ok log c lkb⌝.
  Proof.
    intros Htext. iIntros "Hlg [_ Hmg] Hi Hx Hlk".
    iDestruct (nv_ok_of_wptsto_cur c x vx img log with "Hlg Hmg Hi Hx") as %Hnx.
    iDestruct (nv_ok_of_pointsto img log c lkb dq t vl with "Hi Hlk") as %Hnl.
    iPureIntro. split_and!; [by apply nv_ok_unwritten|exact Hnx|exact Hnl].
  Qed.

End legs.

(* ====================================================================== *)
(** ** 6. THE PARK AT THE WP ALTITUDE, IN THE NEW SURFACE

    [WkYieldFrame] §5's rule with the handoff flag's payload changed from the
    raw view baton [⊒V] to the parking context's own LEDGER
    ([WeakCtxLock.wctx_baton]).  What the park hands the flag is then exactly
    what the resume needs to rebuild [ctx_own] — so the resume's
    postcondition stops being a view inequality the caller must spend, and
    the pair's user-facing pre/post is [ctx_own] in, [ctx_own] out.

    THE CALLBACK IS [WkYieldFrame.wyield_park_cb] VERBATIM.  It already
    asserts [V ⊑ ws_view (wm_ws σ)] — the only fact the deposit needs — and
    already ends in [ctx_migr_all ξ -∗ WWP Loop], which is [ctx_parked ξ].
    The diff against the landed rule is ONE premise (the ledger that
    travels) and ONE line of proof (the deposit is that authority rather
    than a view receipt).

    WHY THE PREMISE IS THE LEDGER AND NOT [ctx_own].  [ctx_own] bundles the
    hart's own [wstate] fragment, and at this altitude that fragment belongs
    to the CALLBACK's obligation: the callback returns [wmstate_rest_nonv σ'],
    whose [wws_auth] it can only move to [σ'] by holding the client half.  So
    a caller splits its [ctx_own] once ([WeakCtxPt.ctx_own_open]) — ledger and
    migration invariant to this rule, [hart_ws] to its own callback — and
    reassembles on the far side with [WeakCtxPt.ctx_own_close].  Making the
    rule take [ctx_own] whole would mean threading [hart_ws] through
    [wyield_park_cb]'s type, i.e. rewriting the landed WP rule rather than
    surfacing over it. *)

Section wp_park.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_ctx_yield_park (ξ : CtxId) (V : view) (γ : gname) (hf : Arch.pa)
      (pc : SailStdpp.Values.mword 64)
      (akf : akinfo) (pf : Arch.pa) (nf : N) (akw : akinfo) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf hf 4 →
    (* the handoff store is a plain [sw], not an AMO *)
    ak_latest akw = false →
    (∀ a : Z, weff_touches (WEread akf pf nf) a →
       ∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) →
    inv wlockN (wlock_inv γ hf (wctx_baton ξ)) -∗
    locked γ cpu_id -∗
    ctx_auth ξ V -∗
    ctx_migr ξ cpu_id -∗
    wyield_park_cb ξ V pc
      (wP_eff (Some (fin_to_nat cpu_id))
         [WEread akf pf nf; WEwrite akw hf 4 lock_zero]) -∗
    WWP Loop.
  Proof.
    intros Hgid Haccpc Hacchf Hlatw Hfetch. iIntros "#Hinv Htok Hau Hmg Hk".
    rewrite /wyield_park_cb.
    assert (Hfoot : ∀ a : Z,
              weffs_touch [WEread akf pf nf; WEwrite akw hf 4 lock_zero] a →
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr pc j) ∨
              (∃ j : nat, (j < 4)%nat ∧ a = acc_addr hf j)).
    { intros a Ha. apply weffs_touch_cons in Ha as [Ha|Ha].
      - left. by apply Hfetch.
      - right. destruct (weffs_touch_write1 _ hf _ _ a Ha) as (j & Hj & ->).
        exists j. split; [cbn in Hj; lia|done]. }
    iApply (wp_winstr pc
              (wP_eff (Some (fin_to_nat cpu_id))
                 [WEread akf pf nf; WEwrite akw hf 4 lock_zero])
              (wQ_fr (wQ_store (Some (fin_to_nat cpu_id)) hf lock_zero)
                     (Some (fin_to_nat cpu_id))
                     [WEread akf pf nf; WEwrite akw hf 4 lock_zero])
              Hgid Haccpc).
    { apply wstep_cert_fr.
      exact (wcert_store (fin_to_nat cpu_id) pc akf pf nf akw hf lock_zero). }
    iIntros (σ) "Hσ".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    iDestruct (wmstate_rest_nv with "Hrest") as %Hnvσ.
    iInv wlockN as "Hbody" "Hclose".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & %Hnvpc & %Hrelp & %HV & Hlat & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    iDestruct "Hcont" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iExists t0, t1. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQfr".
    destruct HQfr as [HQ HQeff].
    assert (Hlog : wm_log σ' =
              (wm_log σ ++ [wwrite_msg (Some (fin_to_nat cpu_id))
                              WCrel hf 4 lock_zero])%list)
      by exact (wQ_eff_store_rel _ akf pf nf akw hf lock_zero σ σ'
                  Hlatw Hrelp HQeff).
    (* the continuation FIRST: it returns the state remainder, and the log
       authority inside it is what the mint rides *)
    iMod ("Hcont" $! tick σ' with "[%]") as "[Hrest Hk2]"; [exact Hpost|].
    iDestruct "Hrest" as "(%Hb' & %Hw' & Hr & Hd & Hlogauth & Hws)".
    iEval (rewrite Hlog) in "Hlogauth".
    iDestruct (pub_floor_mint (wm_log σ)
                 (wwrite_msg (Some (fin_to_nat cpu_id)) WCrel hf 4 lock_zero)
                 cpu_id eq_refl eq_refl with "Hlogauth") as "[Hlogauth #Hpf]".
    (* THE PARK on the migration invariant, in one line and with no byte
       named: the floor the release just minted covers everything the context
       wrote through this hart, so the invariant re-forms in its parked form *)
    assert (Hlen : (length (wm_log σ ++
              [wwrite_msg (Some (fin_to_nat cpu_id)) WCrel hf 4 lock_zero])
              <= S (length (wm_log σ)))%nat) by (rewrite length_app /=; lia).
    iDestruct (ctx_migr_park ξ cpu_id _ _ Hlen with "Hlogauth Hpf Hmg")
      as "[Hlogauth Hall]".
    iSpecialize ("Hk2" with "Hall").
    (* the release itself, and the φ payment — [wwp_release_store]'s verbatim *)
    iMod (wrelease_core γ hf (wctx_baton ξ) cpu_id (Some (fin_to_nat cpu_id))
            σ σ' HQ Hrelp Hbnd with "Hlat Hbody Htok [Hau]") as "[Hlat Hbody]".
    { rewrite /wctx_baton wledger_pay_at. iExists V. by iFrame "Hau". }
    iAssert (⌜nv_hart (wm_log σ') cpu_id (wm_ws σ')⌝)%I as %Hnv'.
    { iDestruct "Hbody" as (st' t' v'') "[Hw' Hlk']".
      iDestruct (nv_ok_wlat4L cpu_id _ _ hf t' v''
                   with "Hlat Hw'") as %Hnvhf.
      iPureIntro.
      apply (nv_hart_of_wQ_eff_ok cpu_id σ σ'
               [WEread akf pf nf; WEwrite akw hf 4 lock_zero] HQeff Hnvσ).
      intros a Ha. destruct (Hfoot a Ha) as [(j & Hj & ->)|(j & Hj & ->)].
      - rewrite Hlog. intros n. apply nv_byte_app_own; [by apply Hnvpc|].
        intros m Hm. apply elem_of_list_singleton in Hm as ->. reflexivity.
      - by apply Hnvhf. }
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iFrame "Hk2".
    iApply (wmstate_interp_split σ'). iFrame "Hlat".
    iApply (wmstate_rest_of_nonv σ' with "[%]"); [exact Hnv'|].
    rewrite /wmstate_rest_nonv. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iFrame "Hr Hd Hws".
    iEval (rewrite -Hlog) in "Hlogauth". iExact "Hlogauth".
  Qed.


End wp_park.

(* ======================================================================
   WHAT THIS FILE CHECKS, IN ONE LIST

   1. §2: an access site's script is the same before and after a migration,
      and its STATEMENT mentions no view, no [monPred], no [wstate] in the
      memory slots.  [wcs_touch_A] and [wcs_touch_B] are one lemma applied
      twice, with [cur_ctx] the same instance on both sides.

   2. §3: the thread's facts frame around the yield by [iFrame], and the
      yield's own pre/post are [ctx_own] in / [ctx_own] out with the cpu
      re-bound — memory-silent, both halves.

   3. §4: the ξ_L ↔ ξ re-indexing appears only in the lock lemmas'
      signatures, and ξ_L itself only under [wctx_is_lock]'s existential.  A
      release that egresses owned memory keeps its one extra premise (the
      class of its own message), exactly as at Stage 1.

   4. §5: φ is paid by the same lemma at every arm, out of [ctx_own].

   5. §6: the park's WP-altitude rule, with the handoff flag carrying the
      parking context's LEDGER instead of a raw view receipt — the callback
      is [WkYieldFrame.wyield_park_cb] verbatim, and the resume side needs no
      rule at all ([WeakAcquire.wwp_acquire_loop_cert] at [wctx_baton ξ]). *)

Print Assumptions wcs_touch.
Print Assumptions wcs_park_frames.
Print Assumptions wcs_resume_frames.
Print Assumptions wcs_yield_is_memory_silent.
Print Assumptions wcs_release_leg.
Print Assumptions wcs_acquire_leg.
Print Assumptions wcs_handoff_load.
Print Assumptions wcs_phi_three_arms.
Print Assumptions wwp_ctx_yield_park.

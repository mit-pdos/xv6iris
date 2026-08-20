(** * WeakCtxLock.v — EVERY LOCK OWNS A CONTEXT (φ-upgrade §1.8)

    THE ONE CONSTRUCTION THIS FILE IS.  A lock's payload is

      [wledger_pay ξ P]  :=  ∃ V, ⎡ ctx_auth ξ V ∗ P ⎤ ∗ ⊒V

    — the LEDGER of a context ξ, the (view-free, [iProp]) facts [P] whose
    floors are registered against that ledger, and the receipt that whoever
    holds the payload has observed the ledger's view.  Reading it:

      - the deposit is Cosmo's "the lock protects a view", with the view
        ledger as the lock's CONTEXT.  The releaser raises the lock's ledger
        to its own view and re-registers the deposited facts there; the
        acquirer's [amoswap.w.aq] delivers [⊒V], which puts the lock's ledger
        below the acquirer's view, so the acquirer may re-register the facts
        against ITS context.  Function proofs see none of it;
      - the payload [P] is an ordinary [iProp].  That is the point of the
        stage: a ported lock invariant is [iProp]-shaped, exactly as it is in
        the SC tree, and the [vProp] wrapper above is the lock library's.

    ξ_L IS INTERNAL.  The client-facing handle is
    [wctx_is_lock γ lk R := ∃ ξ_L, inv wlockN (wclock_body γ lk R ξ_L)] and
    the payload is a FUNCTION [R : CtxId → iProp], written [<{ … }>] so that
    a client writes bare [↦wp] spellings and never a context.  A proof learns
    ξ_L by destructing that existential ONCE, at the top; from then on ξ_L is
    a proof-local name that appears in no specification.  Acquire hands back
    [R cur_ctx]; release consumes [R cur_ctx]; the re-indexing between
    [R ξ_L] and [R cur_ctx] is [WeakCtxPt.ctx_morph], applied inside these
    lemmas and nowhere else.

    THE HANDOFF IS THE SAME CONSTRUCTION WITH AN EMPTY PAYLOAD (§5).  A yield
    parks a context by DEPOSITING ITS LEDGER in the scheduler's handoff flag;
    the resuming hart withdraws it and the ledger lands below the new hart's
    view.  So [ctx_own ξ c] in, [ctx_own ξ c'] out, and nothing memory-shaped
    crosses — the park's whole postcondition is the Stage-1.6 migration
    invariant in its parked form.  [WkYieldFrame]'s bare view baton is the
    special case where the traveling ledger is spelled as a raw [⊒V]; here it
    travels as the authority itself, which is what removes the requirement
    that the lock's view parameter be the parking hart's on the nose. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac excl.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakExec.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakCtx.
Require Import WeakCtxPt.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakBridge.
Require Import WeakLock.
Require Import WeakAcquire.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE PAYLOAD: a context's ledger, and the facts registered in it *)

Section pay.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wledger_pay (ξ : CtxId) (P : iProp Σ) : vProp Σ :=
    (∃ V : view, ⎡ ctx_auth ξ V ∗ P ⎤ ∗ ⊒V)%I.

  Lemma wledger_pay_at_view ξ P (W : view) :
    monPred_at (wledger_pay ξ P) W ⊣⊢ ∃ V : view, ctx_auth ξ V ∗ P ∗ ⌜V ⊑ W⌝.
  Proof.
    rewrite /wledger_pay monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => V. iSplit.
    - iIntros "[[$ $] $]".
    - iIntros "($ & $ & $)".
  Qed.

  Lemma wledger_pay_at ξ P ws :
    vwp_hold (wledger_pay ξ P) ws ⊣⊢
      ∃ V : view, ctx_auth ξ V ∗ P ∗ ⌜V ⊑ ws_view ws⌝.
  Proof. apply wledger_pay_at_view. Qed.

  Lemma wledger_pay_intro ξ P V (W : view) :
    V ⊑ W → ctx_auth ξ V -∗ P -∗ monPred_at (wledger_pay ξ P) W.
  Proof.
    intros Hle. iIntros "Ha HP". rewrite wledger_pay_at_view.
    iExists V. by iFrame "Ha HP".
  Qed.

End pay.

(* ====================================================================== *)
(** ** 2. THE LOCK WITH A CONTEXT *)

Section clock.
  Context `{!riscvGS Σ, !weakGS Σ, !lockG Σ}.

  (** The invariant BODY, with the lock's context named.  A client never
      writes this: it writes [wctx_is_lock] below, whose existential is the
      whole of "ξ_L is internal". *)
  Definition wclock_body (γ : gname) (lk : Arch.pa) (R : CtxId → iProp Σ)
      (ξL : CtxId) : iProp Σ :=
    wlock_inv γ lk (wledger_pay ξL (R ξL)).

  (** THE CLIENT-FACING HANDLE.  Persistent, objective, and free of the
      lock's context — which is bound here and introduced into a proof
      exactly once. *)
  Definition wctx_is_lock (γ : gname) (lk : Arch.pa) (R : CtxId → iProp Σ)
      : iProp Σ :=
    (∃ ξL : CtxId, inv wlockN (wclock_body γ lk R ξL))%I.

  Global Instance wctx_is_lock_persistent γ lk R :
    Persistent (wctx_is_lock γ lk R).
  Proof. apply _. Qed.

  (** THE CRITICAL-SECTION TOKEN.  The holder token, plus the lock's ledger
      authority (which travels with the payload and must come back at the
      release), plus the persistent receipt that the HOLDER's ledger already
      dominates the lock's — minted at the acquire, and what lets the release
      raise the lock's ledger to the holder's view.

      It names both contexts, per [WeakVProp] §3'''s convention: this is a
      two-context object.  It is proof-internal — it lives between one
      acquire and the matching release inside a single function proof — so
      naming ξ_L here costs a client nothing. *)
  Definition wctx_held (γ : gname) (ξL ξ : CtxId) (i : CPU) : iProp Σ :=
    (locked γ i ∗ ∃ V : view, ctx_auth ξL V ∗ ctx_view_lb ξ V)%I.

(* ====================================================================== *)
(** ** 3. ACQUIRE — the withdraw, and the re-index into the acquirer

    [WeakLock.wacquire_core] with three lines after it: decode the payload,
    bump the acquirer's ledger to its hart's view (which the [aq] transfer
    has put above the lock's), and move the facts.  [CtxMorph] does the last
    step for WHATEVER the client's payload is. *)

  Lemma wctx_acquire_core (γ : gname) (ξL ξ : CtxId) (lk : Arch.pa)
      (R : CtxId → iProp Σ) `{!CtxMorph R} (i : CPU) (tid : option nat)
      (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf lk 4 →
    wQ_amo_aq tid lk lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add lk j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk R ξL -∗
    ctx_own_at ξ i (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wclock_body γ lk R ξL ∗
    wctx_held γ ξL ξ i ∗ ctx_own_at ξ i (wm_ws σ') ∗ R ξ.
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv Hrun".
    assert (Hle : ws_le (wm_ws σ) (wm_ws σ'))
      by exact (proj1 (proj2 (proj2 (proj1 HQ)))).
    iDestruct (ctx_own_at_mono ξ i _ _ Hle with "Hrun") as "[Hlb Hmg]".
    iDestruct (wacquire_core γ lk (wledger_pay ξL (R ξL)) i tid σ σ'
                 Hwf Hacc HQ with "Hi Hinv") as (v0) "[%Hflat Hupd]".
    assert (Hv : lock_zero = v0)
      by exact (wflat_word_agree σ lk lock_zero v0 Hzero Hflat).
    iMod "Hupd" as "(Hi & Hbody & Harm)".
    iDestruct "Harm" as "[(_ & HR & Htok)|%Hne]"; [|by rewrite -Hv in Hne].
    (* the payload: the lock's ledger, the facts, and the [aq] view fact *)
    rewrite wledger_pay_at. iDestruct "HR" as (V) "(HaL & HR & %HV)".
    (* the acquirer's own ledger, bumped to its hart's view — which the
       transfer has put above the lock's *)
    iMod (ctx_lb_sync ξ (wm_ws σ') with "Hlb") as "Ha".
    iDestruct (ctx_view_lb_get ξ (ws_view (wm_ws σ')) V with "Ha") as "#Hd";
      [exact HV|].
    (* THE RE-INDEX, once, for whatever the payload is *)
    iDestruct (ctx_dom_intro ξL ξ V with "HaL Hd") as "Hdom".
    iMod (ctx_morph ξL ξ V with "Hdom HR") as "[Hdom $]".
    iDestruct (ctx_dom_auth with "Hdom") as "HaL".
    iModIntro. iFrame "Hi Hbody Htok Hmg".
    iSplitL "HaL"; [iExists V; by iFrame "HaL Hd"|].
    by iApply (ctx_lb_of_auth with "Ha").
  Qed.

(* ====================================================================== *)
(** ** 4. RELEASE — the re-index out, and the deposit

    Two cores, for the reason [WkOwnPingPong] §3 records: a release that
    EGRESSES OWNED MEMORY needs the latest-write authority at the POST-state
    (where its [WCrel] message is the log's last) in order to flip the
    deposit clean, and [WeakLock.wrelease_core] consumes its payload at the
    PRE-state.  §4a is the release whose payload is already clean — fully
    generic in [R], and [wrelease_core] plus the re-index; §4b is the
    one-byte owned deposit, with the flip spliced in, and it is the shape a
    ported [release] that hands over memory copies. *)

  (** *** 4a. THE GENERIC RELEASE — any [CtxMorph] payload, already clean. *)
  Lemma wctx_release_core (γ : gname) (ξL ξ : CtxId) (lk : Arch.pa)
      (R : CtxId → iProp Σ) `{!CtxMorph R} (i : CPU) (tid : option nat)
      (σ σ' : wmstate) :
    wQ_store tid lk lock_zero σ σ' →
    w_relp (wm_ws σ) = true →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk R ξL -∗ wctx_held γ ξL ξ i -∗
    ctx_own_at ξ i (wm_ws σ) -∗ R ξ ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wclock_body γ lk R ξL ∗
    ctx_own_at ξ i (wm_ws σ).
  Proof.
    intros HQ Hrelp Hbnd.
    iIntros "Hi Hinv [Htok [%VL [HaL #Hd]]] [Hlb Hmg] HR".
    (* the depositor's ledger at its hart's view, and the lock's below it *)
    iMod (ctx_lb_sync ξ (wm_ws σ) with "Hlb") as "Ha".
    iDestruct (ctx_view_lb_valid with "Ha Hd") as %HVL.
    (* THE MINT: raise the lock's ledger to the release view *)
    iMod (ctx_dom_mint ξ ξL (ws_view (wm_ws σ)) VL HVL with "Ha HaL")
      as "[HaL Hdom]".
    (* THE RE-INDEX, once, for whatever the payload is *)
    iMod (ctx_morph ξ ξL (ws_view (wm_ws σ)) with "Hdom HR") as "[Hdom HR]".
    iDestruct (ctx_dom_auth with "Hdom") as "Ha".
    (* the deposit is now an ordinary [wrelease_core] at the wrapped payload *)
    iMod (wrelease_core γ lk (wledger_pay ξL (R ξL)) i tid σ σ' HQ Hrelp Hbnd
            with "Hi Hinv Htok [HaL HR]") as "[$ $]".
    { rewrite wledger_pay_at. iExists (ws_view (wm_ws σ)). by iFrame "HaL HR". }
    iModIntro. iFrame "Hmg". by iApply (ctx_lb_of_auth with "Ha").
  Qed.

  (** *** 4b. THE OWNED ONE-BYTE RELEASE — the D→C flip at a real site.

      [WkOwnPingPong.wrelease_flip_core] restated over the [iProp] surface.
      The payload the caller hands over is the OWNED [wptsto ξ x v] (what a
      plain [sb] leaves); what the lock ends up holding is the CLEAN
      [wptsto_cl ξL x v] that any context may take.  The three ghost steps in
      between — retarget (a byte this context dirtied on a hart it has since
      left), flip (D→C at the release's own message), re-index (into the
      lock's ledger) — are all here and none of them is visible in a function
      proof. *)
  Lemma wctx_release_byte (γ : gname) (ξL ξ : CtxId) (lk : Arch.pa) (x : Z)
      (v : bv 8) (i : CPU) (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) lk lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ') -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wclock_body γ lk <{ x ↦wp v }> ξL -∗
    wctx_held γ ξL ξ i -∗
    ctx_own_at ξ i (wm_ws σ) -∗ wptsto ξ x v ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wclock_body γ lk <{ x ↦wp v }> ξL ∗
    ctx_own_at ξ i (wm_ws σ).
  Proof.
    intros (Himg & _ & Hle & Hflr) Hlog Hbnd.
    iIntros "Hlg Hi Hinv [Htok [%VL [HaL #Hd]]] [Hlb Hmg] Hpt".
    rewrite /wclock_body. iDestruct "Hinv" as (st t w) "(Hw & Ha & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    (* the byte's element and its state, with the LEDGER REGISTRATION kept
       (it is persistent, so the round trip through the [vProp] layer that
       the [vProp] core needs is not one here) *)
    iDestruct "Hpt" as (t0) "(Hel & Hs & #Hf)".
    (* THE RETARGET, leaf-internally *)
    iMod (wown_ctx_retarget ξ i x t0 v (wm_img σ) (wm_log σ) (wm_log σ')
            ltac:(rewrite Hlog; by apply pub_transfer_snoc)
            with "Hlg Hmg Hi Hel Hs") as "(Hlg & Hmg & Hi & Hel & Hs)".
    iFrame "Hlg".
    (* the lock word's own bundle moves to the fresh top, and stays CLEAN *)
    iMod (wlat4L_store_gen (Some (fin_to_nat i)) WCrel σ σ' lk t w lock_zero
            (wlock_shaped_rel _ WCrel _ ltac:(discriminate)) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    (* THE FLIP, at the post-log whose last message is this hart's release *)
    rewrite Hlog.
    iMod (wlat_flip (wm_img σ') (wm_log σ)
            (wwrite_msg (Some (fin_to_nat i)) WCrel lk 4 lock_zero) i x
            eq_refl eq_refl with "Hi Hs") as "[Hi Hcl]".
    (* the deposit's CLEAN form, at the ledger registration it already had *)
    iAssert (wptsto_cl ξ x (DfracOwn 1) v) with "[Hel Hcl]" as "HR".
    { iExists t0. rewrite /wlat_pointsto. by iFrame "Hel Hcl Hf". }
    (* THE MINT and THE RE-INDEX *)
    iMod (ctx_lb_sync ξ (wm_ws σ) with "Hlb") as "Hau".
    iDestruct (ctx_view_lb_valid with "Hau Hd") as %HVL.
    iMod (ctx_dom_mint ξ ξL (ws_view (wm_ws σ)) VL HVL with "Hau HaL")
      as "[HaL Hdom]".
    iMod (ctx_morph ξ ξL (ws_view (wm_ws σ)) with "Hdom HR") as "[Hdom HR]".
    iDestruct (ctx_dom_auth with "Hdom") as "Hau".
    (* the deposit itself: view arithmetic and [ws_bounded], nothing else *)
    iAssert (monPred_at (wledger_pay ξL ((<{ x ↦wp v }> : CtxId → iProp Σ) ξL))
               (view_scl (S (length (wm_log σ)))))%I
      with "[HaL HR]" as "Hdep".
    { iApply (wwp_release_deposit
                (wledger_pay ξL ((<{ x ↦wp v }> : CtxId → iProp Σ) ξL)) σ Hbnd).
      iApply (wledger_pay_intro ξL _ (ws_view (wm_ws σ)) (ws_view (wm_ws σ))
                ltac:(reflexivity) with "HaL HR"). }
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. rewrite -Hlog. iFrame "Hi Hmg".
    iSplitR "Hau".
    - iExists None, (S (length (wm_log σ))), lock_zero.
      iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|].
      iFrame "Hfrag Hdep".
    - by iApply (ctx_lb_of_auth with "Hau").
  Qed.

(* ====================================================================== *)
(** ** 5. YIELD IN THE NEW SURFACE — [ctx_own ξ c] in, [ctx_own ξ c'] out

    The handoff flag is §1's construction with an EMPTY payload: what the
    park deposits is the context's LEDGER, and nothing else.  Read the two
    statements below and note what does not appear in either: no byte, no
    view variable in the postcondition, no publication token, no hart's
    memory state.  The park's whole output is [ctx_migr_all ξ], the
    scheduler-side migration invariant in its parked form; the resume's whole
    output is [ctx_own] at the NEW cpu, which is the lemma's ∀-bound [c'].

    Every [wptsto] a thread owns therefore frames across the pair with
    nothing to prove — it is an [iProp] that neither lemma mentions.  §6 of
    [WkCtxSurface] is that statement. *)

  Definition wctx_baton (ξ : CtxId) : vProp Σ := wledger_pay ξ emp%I.

  (** THE PARKED CONTEXT: a scheduler resource naming no byte, no view and no
      hart.  (Its ledger is not here — it is in the handoff flag.) *)
  Definition ctx_parked (ξ : CtxId) : iProp Σ := ctx_migr_all ξ.

  Lemma wctx_park_core (ξ : CtxId) (γ : gname) (hf : Arch.pa) (i : CPU)
      (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton ξ) -∗ locked γ i -∗
    ctx_own_at ξ i (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wctx_baton ξ) ∗ ctx_parked ξ.
  Proof.
    intros (Himg & _ & Hle & Hflr) Hlog Hbnd.
    iIntros "Hlog Hi Hinv Htok [Hlb Hmg]".
    iDestruct "Hinv" as (st t w) "(Hw & Ha & _)".
    iDestruct (locked_state with "Ha Htok") as %->.
    (* the flag word's bundle moves to the fresh top and stays CLEAN *)
    iMod (wlat4L_store_gen (Some (fin_to_nat i)) WCrel σ σ' hf t w lock_zero
            (wlock_shaped_rel _ WCrel _ ltac:(discriminate)) Himg Hlog
            with "Hi Hw") as "[Hi Hw]".
    (* THE MINT: the handoff store is this hart's, release-class, at the log's
       fresh top, so it publishes every earlier position at once *)
    iMod (wlog_update (wm_log σ)
            [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero]
            with "Hlog") as "Hlog".
    iDestruct (pub_floor_mint (wm_log σ)
                 (wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero) i
                 eq_refl eq_refl with "Hlog") as "[Hlog #Hpf]".
    assert (Hlen : (length (wm_log σ ++
              [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])
              <= S (length (wm_log σ)))%nat) by (rewrite length_app /=; lia).
    iDestruct (ctx_migr_park ξ i _ _ Hlen with "Hlog Hpf Hmg")
      as "[Hlog Hall]".
    (* THE DEPOSIT: the context's LEDGER travels through the flag *)
    iMod (ctx_lb_sync ξ (wm_ws σ) with "Hlb") as "Hau".
    iAssert (monPred_at (wctx_baton ξ) (view_scl (S (length (wm_log σ)))))%I
      with "[Hau]" as "Hdep".
    { iApply (wwp_release_deposit (wctx_baton ξ) σ Hbnd).
      iApply (wledger_pay_intro ξ emp%I (ws_view (wm_ws σ)) (ws_view (wm_ws σ))
                ltac:(reflexivity) with "Hau []"); done. }
    iMod (lock_clrcpu γ (Some (i, true)) i with "Ha Htok") as "(_ & Ha & Hpre)".
    iMod (lock_give γ (Some (i, false)) i with "Ha Hpre") as "(_ & Ha & Hfrag)".
    iModIntro. rewrite -Hlog. iFrame "Hlog Hi Hall".
    iExists None, (S (length (wm_log σ))), lock_zero.
    iFrame "Hw Ha". iLeft. iSplitR; [done|]. iSplitR; [done|].
    iFrame "Hfrag Hdep".
  Qed.

  (** THE RESUME, at WHATEVER cpu the scheduler picked — [c'] is this
      lemma's binder, and the [wp_next]-style re-binding is exactly that
      quantifier.  Nothing about the resuming hart has to be checked: the
      parked invariant covers every hart, and the withdrawn ledger lands
      below the new hart's view by the [aq] transfer. *)
  Lemma wctx_resume_core (ξ : CtxId) (γ : gname) (hf : Arch.pa) (c' : CPU)
      (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton ξ) -∗ ctx_parked ξ ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ hf (wctx_baton ξ) ∗
    locked γ c' ∗ ctx_own_at ξ c' (wm_ws σ').
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hi Hinv Hall".
    iDestruct (wacquire_core γ hf (wctx_baton ξ) c' tid σ σ' Hwf Hacc HQ
                 with "Hi Hinv") as (v0) "[%Hflat Hupd]".
    assert (Hv : lock_zero = v0)
      by exact (wflat_word_agree σ hf lock_zero v0 Hzero Hflat).
    iMod "Hupd" as "(Hi & Hbody & Harm)".
    iDestruct "Harm" as "[(_ & HR & Htok)|%Hne]"; [|by rewrite -Hv in Hne].
    rewrite /wctx_baton wledger_pay_at.
    iDestruct "HR" as (V) "(Hau & _ & %HV)".
    iModIntro. iFrame "Hi Hbody Htok".
    iSplitL "Hau"; [iExists V; by iFrame "Hau"|].
    by iApply (ctx_migr_all_run with "Hall").
  Qed.

  (** ... and the bundle form, which is the user-facing shape: [ctx_own ξ i]
      in, [ctx_own ξ c'] out, with the hart's own [wstate] fragment supplied
      by the machine on each side. *)
  Lemma wctx_park (ξ : CtxId) (γ : gname) (hf : Arch.pa) (i : CPU)
      (σ σ' : wmstate) :
    wQ_store (Some (fin_to_nat i)) hf lock_zero σ σ' →
    wm_log σ' =
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat i)) WCrel hf 4 lock_zero])%list →
    ws_bounded (wm_ws σ) (length (wm_log σ)) →
    wws_auth i (wm_ws σ) -∗ wlog_auth (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton ξ) -∗ locked γ i -∗
    ctx_own ξ i ==∗
    wws_auth i (wm_ws σ) ∗ hart_ws i (wm_ws σ) ∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    wlock_inv γ hf (wctx_baton ξ) ∗ ctx_parked ξ.
  Proof.
    intros HQ Hlog Hbnd. iIntros "Hwsa Hlog Hi Hinv Htok Hrun".
    iDestruct (ctx_own_acc with "Hwsa Hrun") as "($ & $ & Hrun)".
    by iApply (wctx_park_core ξ γ hf i σ σ' HQ Hlog Hbnd
                 with "Hlog Hi Hinv Htok Hrun").
  Qed.

  Lemma wctx_resume (ξ : CtxId) (γ : gname) (hf : Arch.pa) (c' : CPU)
      (tid : option nat) (σ σ' : wmstate) :
    wlog_wf (wm_log σ) → acc_wf hf 4 →
    wQ_amo_aq tid hf lock_one σ σ' →
    (∀ j : nat, (j < 4)%nat →
       wflat (wm_img σ) (wm_log σ) !! pa_add hf j = Some (nth_byte lock_zero j)) →
    hart_ws c' (wm_ws σ') -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlock_inv γ hf (wctx_baton ξ) -∗ ctx_parked ξ ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wlock_inv γ hf (wctx_baton ξ) ∗
    locked γ c' ∗ ctx_own ξ c'.
  Proof.
    intros Hwf Hacc HQ Hzero. iIntros "Hws Hi Hinv Hall".
    iMod (wctx_resume_core ξ γ hf c' tid σ σ' Hwf Hacc HQ Hzero
            with "Hi Hinv Hall") as "($ & $ & $ & Hrun)".
    iModIntro. by iApply (ctx_own_close with "Hws Hrun").
  Qed.

End clock.

(* ======================================================================
   WHAT A PORTED LOCK LIBRARY TAKES FROM THIS FILE

   1. [wctx_is_lock γ lk R] is the handle, with [R : CtxId → iProp] written
      [<{ … }>].  A client's lock invariant is plain [iProp] with bare
      [↦wp] spellings; the lock's own context is bound by the handle's
      existential and enters a proof once.

   2. Acquire returns [R cur_ctx] and the critical-section token; release
      consumes [R cur_ctx] and the token.  The re-indexing between the
      lock's context and the client's is [WeakCtxPt.ctx_morph], applied
      inside §3 and §4 and nowhere else, and the [CtxMorph] instance is
      found by instance resolution from the payload's SHAPE.

   3. A release that egresses OWNED memory uses §4b (which flips D→C at the
      release's own message, exactly as [WkOwnPingPong.wrelease_flip_core]
      does); a release whose payload is already clean or context-free uses
      §4a, which is generic in the payload.

   4. A yield is §5: the same construction with an empty payload, so the
      context's LEDGER is what travels.  Pre [ctx_own ξ c], post
      [ctx_own ξ c'] with [c'] the resume lemma's binder, and no memory
      fact in either. *)

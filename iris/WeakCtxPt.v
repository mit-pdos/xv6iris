(** * WeakCtxPt.v — THE iPROP RESURFACING (φ-upgrade §1.8)

    WHY THIS FILE EXISTS.  Stages 1.5–1.7 built an owned points-to that frames
    across a migration ([WeakVProp.wpt_own], indexed by a context, with the
    bare [↦wo] notation) — but it is a [vProp], and its subjective conjunct
    [⊒(view_byte a t)] is exactly what makes it one.  The 500K lines of
    existing SC proofs are [iProp]-shaped, and the mass port must not convert
    them.  So the target API is an [iProp] points-to, and the question is
    where the view receipt goes.

    IT GOES INTO THE CONTEXT'S LEDGER.  [WeakCtx] already carries, per
    context, an authority on the context's own view ([ctx_auth]) with a
    PERSISTENT lower-bound fragment ([ctx_view_lb]) that is monotone along
    [⊑] and nothing finer.  A byte's floor registered there is a fact ABOUT
    THE CONTEXT rather than about the index the assertion is read at, so it
    can live inside an objective [iProp]:

      [wptsto ξ a v]  =  the value element + the C/D/S state (with its
                         breadcrumb) + [ctx_view_lb ξ (view_byte a t)]

    and nothing in it mentions a view variable, a [monPred_at], or a hart.
    Framing across a yield is then not a lemma at all — the proposition does
    not change, so there is nothing to frame.

    THE ONE INVARIANT THAT MAKES THE FLOORS USABLE is [ctx_own]'s: "ξ's
    ledger is below the hart's view".  Every leaf that touches a byte reads
    the byte's floor out of the ledger and the ledger out of [ctx_own], so a
    points-to never has to carry the index itself.  [ctx_own] is the running
    bundle — the successor of [WeakCtx.wrunning] with the CPU made an
    EXPLICIT argument, because it is re-bound at a migration exactly the way
    [cur_proc] is (and unlike ξ, which is invariant: φ-upgrade §1.7).

    WHAT IS AND IS NOT THE API.  This file's [wptsto] / [wptsto_cl] /
    [ctx_own] are THE API for the port.  [WeakVProp]'s [wpt_own] / [wpt] and
    the [vwp_hold] discipline remain as the INTERNAL GLUE: [monPred_at] is
    how a leaf hands a fact to the WP layer, and every rule below is its
    [vProp] twin with two conversions wrapped around it (§4).  Nothing in
    Stages 1.5–1.7 is replaced.

    THE TWO SPELLINGS, and why there are two (mirroring [↦w{dq}] / [↦wo]):

      [a ↦wp{dq} v]  ([wptsto_cl]) — CLEAN, fractional.  The shared or
                     read-only byte, and the form a lock payload is
                     deposited in.  A clean byte names no author, so it is
                     the only form that can be RE-INDEXED between contexts
                     (§6) — which is what the lock library's release and
                     acquire do.
      [a ↦wpo v]     ([wptsto]) — OWNED, exclusive, clean-or-dirty.  The
                     mutable byte: what a plain store consumes and produces.
                     [a ↦wp v] (clean at full fraction) entails it.

    Both are ambiently ξ-indexed through [WeakVProp]'s [CurCtx] class, under
    that file's one-context convention: where two contexts meet, spell
    [wptsto ξ …] explicitly. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakCtx.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE TWO POINTS-TO *)

Section defs.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE CLEAN FORM.  [WeakVProp.wpt]'s payload with the subjective receipt
      [⊒(view_byte a t)] replaced by the ledger registration.  The two are the
      same statement read at different altitudes: "[t] is below what I have
      observed" versus "[t] is below what ξ has observed", and ξ's observation
      is the one that survives a change of hart. *)
  Definition wptsto_cl (ξ : CtxId) (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, wlat_pointsto a dq t v ∗ ctx_view_lb ξ (view_byte a t))%I.

  (** THE OWNED FORM.  [WeakVProp.wpt_own]'s payload, same substitution.  The
      C/D/S state and its migration breadcrumb ride inside [wown_ctx]
      untouched — this stage changes the RECEIPT, not the protocol. *)
  Definition wptsto (ξ : CtxId) (a : Z) (v : bv 8) : iProp Σ :=
    (∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_ctx ξ a t ∗
                ctx_view_lb ξ (view_byte a t))%I.

End defs.

(** The ambient spellings (φ-upgrade §1.7's class, this stage's surface). *)
Notation "a ↦wp dq v" := (wptsto_cl cur_ctx a dq v)
  (at level 20, dq custom dfrac at level 1, format "a  ↦wp dq  v") : bi_scope.
Notation "a ↦wpo v" := (wptsto cur_ctx a v)
  (at level 20, format "a  ↦wpo  v") : bi_scope.

(* ====================================================================== *)
(** ** 2. [ctx_own] — the running bundle

    [WeakCtx.wrunning] with the hart made an EXPLICIT argument and the ledger
    tie RELAXED from equality to [⊑].

    WHY EXPLICIT.  A thread's context is invariant across a migration and its
    hart is not (φ-upgrade §1.7): so ξ is ambient and the CPU is written.
    [ctx_own ξ c] is re-bound at a yield exactly as [cur_proc] is — the park
    consumes it at [c], the resume produces it at whatever [c'] the scheduler
    picked (§5 of [WeakCtxLock]).

    WHY [⊑] AND NOT [=].  [WeakCtx.ctx_run] pins the ledger to the hart's
    view exactly, which costs a ghost update at every view growth.  The
    inequality is what every consumer actually needs (a floor below the
    ledger is a floor below the hart's view), it is monotone in the [wstate]
    FOR FREE, and it is restored to the exact form by one [ctx_auth_update]
    where a rule needs to register a NEW floor.  That update is
    [ctx_lb_sync], and it is the only ghost operation this surface performs
    on the ledger. *)

Section running.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE INVARIANT: "ξ's ledger is below this hart's view". *)
  Definition ctx_lb (ξ : CtxId) (ws : wstate) : iProp Σ :=
    (∃ V : view, ctx_auth ξ V ∗ ⌜V ⊑ ws_view ws⌝)%I.

  (** ... plus the Stage-1.6 migration invariant, which is the OTHER half of
      the bundle and is not a memory fact: publication is not view-implied
      (the "[w_pub] is not a view component" finding stands), so the two
      halves are independent and both are needed. *)
  Definition ctx_own_at (ξ : CtxId) (c : CPU) (ws : wstate) : iProp Σ :=
    (ctx_lb ξ ws ∗ ctx_migr ξ c)%I.

  (** THE CALLER-FACING BUNDLE, with the [wstate] hidden behind the hart's
      own exclusive fragment — which is what pins it to the machine's when a
      leaf agrees the two halves ([ctx_own_acc]). *)
  Definition ctx_own (ξ : CtxId) (c : CPU) : iProp Σ :=
    (∃ ws : wstate, hart_ws c ws ∗ ctx_own_at ξ c ws)%I.

  Lemma ctx_lb_of_auth ξ ws : ctx_auth ξ (ws_view ws) -∗ ctx_lb ξ ws.
  Proof. iIntros "H". iExists (ws_view ws). by iFrame "H". Qed.

  (** THE SYNC — the one ledger update the surface performs.  Raising the
      ledger to the hart's own view is always permitted ([⊑]-monotone) and is
      what lets a rule REGISTER a floor the hart has just acquired. *)
  Lemma ctx_lb_sync ξ ws : ctx_lb ξ ws ==∗ ctx_auth ξ (ws_view ws).
  Proof.
    iIntros "[%V [Ha %Hle]]". by iApply (ctx_auth_update with "Ha").
  Qed.

  Lemma ctx_lb_mono ξ ws ws' :
    ws_view ws ⊑ ws_view ws' → ctx_lb ξ ws -∗ ctx_lb ξ ws'.
  Proof.
    iIntros (Hle) "[%V [Ha %H]]". iExists V. iFrame "Ha". iPureIntro.
    by etrans.
  Qed.

  (** The ledger's floors are the hart's floors — the ONE fact that makes
      every points-to's registration usable at every leaf. *)
  Lemma ctx_lb_valid ξ ws V :
    ctx_lb ξ ws -∗ ctx_view_lb ξ V -∗ ctx_lb ξ ws ∗ ⌜V ⊑ ws_view ws⌝.
  Proof.
    iIntros "[%V0 [Ha %H0]] #Hlb".
    iDestruct (ctx_view_lb_valid with "Ha Hlb") as %HV.
    iSplitL "Ha"; [iExists V0; by iFrame "Ha"|iPureIntro; by etrans].
  Qed.

  Lemma ctx_own_at_mono ξ c ws ws' :
    ws_le ws ws' → ctx_own_at ξ c ws -∗ ctx_own_at ξ c ws'.
  Proof.
    iIntros (Hle) "[Hlb $]". iApply (ctx_lb_mono with "Hlb").
    by apply ws_le_view.
  Qed.

  (** The migration invariant, borrowed — what the store leaf needs and the
      only thing it needs out of the bundle besides the ledger. *)
  Lemma ctx_own_at_migr ξ c ws :
    ctx_own_at ξ c ws -∗ ctx_migr ξ c ∗ (ctx_migr ξ c -∗ ctx_own_at ξ c ws).
  Proof. iIntros "[$ $]". iIntros "$". Qed.

  Lemma ctx_own_open ξ c :
    ctx_own ξ c -∗ ∃ ws : wstate, hart_ws c ws ∗ ctx_own_at ξ c ws.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma ctx_own_close ξ c ws :
    hart_ws c ws -∗ ctx_own_at ξ c ws -∗ ctx_own ξ c.
  Proof. iIntros "H1 H2". iExists ws. iFrame. Qed.

  (** THE LEAF ACCESSOR.  Against the machine's own authority the bundle's
      hidden [wstate] IS the machine's, so a leaf that holds [wmstate_rest σ]
      may read the caller's ledger at [wm_ws σ] with nothing to prove. *)
  Lemma ctx_own_acc ξ c ws :
    wws_auth c ws -∗ ctx_own ξ c -∗
    wws_auth c ws ∗ hart_ws c ws ∗ ctx_own_at ξ c ws.
  Proof.
    iIntros "Ha [%ws0 [Hf Hrun]]".
    iDestruct (hart_ws_agree with "Ha Hf") as %->. iFrame.
  Qed.

  (** ... and the step: the hart's [wstate] grew, so the bundle follows.  No
      ghost update, because the ledger tie is an inequality. *)
  Lemma ctx_own_step ξ c ws ws' :
    ws_le ws ws' → ctx_own_at ξ c ws -∗ hart_ws c ws' -∗ ctx_own ξ c.
  Proof.
    iIntros (Hle) "Hrun Hws".
    iApply (ctx_own_close with "Hws"). by iApply (ctx_own_at_mono with "Hrun").
  Qed.

  (** The bridge to [WeakCtx]'s own bundle, both ways.  [wrunning] pins the
      ledger exactly, so the way back is the sync. *)
  Lemma ctx_own_of_running `{CID : CpuId} ξ : wrunning ξ -∗ ctx_own ξ cpu_id.
  Proof.
    iIntros "[%ws [Hws [Ha $]]]". iExists ws. iFrame "Hws".
    by iApply (ctx_lb_of_auth with "Ha").
  Qed.

  Lemma ctx_own_to_running `{CID : CpuId} ξ : ctx_own ξ cpu_id ==∗ wrunning ξ.
  Proof.
    iIntros "[%ws [Hws [Hlb $]]]". iMod (ctx_lb_sync with "Hlb") as "Ha".
    iModIntro. iExists ws. iFrame.
  Qed.

End running.

(* ====================================================================== *)
(** ** 3. THE INTERCONVERSION with the [vProp] surface

    This is the whole seam.  Read it at [ws := wm_ws σ]: an [iProp] fact plus
    the ledger invariant IS the [vProp] fact at the hart's index, and back.
    Every rule in §4 is its [vProp] twin between one of these and the other,
    which is why the derivations are three lines each. *)

Section convert.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wptsto_to_own ξ ws a v :
    ctx_lb ξ ws -∗ wptsto ξ a v -∗
    ctx_lb ξ ws ∗ vwp_hold (wpt_own ξ a v) ws.
  Proof.
    iIntros "Hlb [%t (He & Hs & #Hf)]".
    iDestruct (ctx_lb_valid with "Hlb Hf") as "[$ %Hle]".
    iApply (wpt_own_at_intro ξ a v t ws with "He Hs").
    by apply view_byte_le.
  Qed.

  Lemma wptsto_of_own ξ ws a v :
    ctx_auth ξ (ws_view ws) -∗ vwp_hold (wpt_own ξ a v) ws -∗
    ctx_auth ξ (ws_view ws) ∗ wptsto ξ a v.
  Proof.
    iIntros "Ha Hpt". rewrite wpt_own_at.
    iDestruct "Hpt" as (t) "(He & Hs & %Ht)".
    iDestruct (ctx_view_lb_get ξ (ws_view ws) (view_byte a t) with "Ha")
      as "#Hf"; [by apply view_byte_le|].
    iFrame "Ha". iExists t. by iFrame "He Hs Hf".
  Qed.

  Lemma wptsto_cl_to_pt ξ ws a dq v :
    ctx_lb ξ ws -∗ wptsto_cl ξ a dq v -∗
    ctx_lb ξ ws ∗ vwp_hold (a ↦w{dq} v) ws.
  Proof.
    iIntros "Hlb [%t (He & #Hf)]".
    iDestruct (ctx_lb_valid with "Hlb Hf") as "[$ %Hle]".
    iApply (wpt_at_intro a dq v t ws with "He").
    by apply view_byte_le.
  Qed.

  Lemma wptsto_cl_of_pt ξ ws a dq v :
    ctx_auth ξ (ws_view ws) -∗ vwp_hold (a ↦w{dq} v) ws -∗
    ctx_auth ξ (ws_view ws) ∗ wptsto_cl ξ a dq v.
  Proof.
    iIntros "Ha Hpt". rewrite wpt_at. iDestruct "Hpt" as (t) "[He %Ht]".
    iDestruct (ctx_view_lb_get ξ (ws_view ws) (view_byte a t) with "Ha")
      as "#Hf"; [by apply view_byte_le|].
    iFrame "Ha". iExists t. by iFrame "He Hf".
  Qed.

  (** A CLEAN FULL-FRACTION BYTE IS OWNED, at every context — [WeakVProp]'s
      [wpt_own_of_wpt] at this altitude, and the receiving side of every
      transfer in one line. *)
  Lemma wptsto_of_cl ξ a v : wptsto_cl ξ a (DfracOwn 1) v -∗ wptsto ξ a v.
  Proof.
    iIntros "[%t [[He Hc] $]]". iFrame "He".
    by iApply (wown_ctx_of_clean with "Hc").
  Qed.

  (** ... and the characterisation that says what the surface IS: the
      objective-ownership functor of [WeakCtx] applied to the Stage-1.6
      points-to.  Not used below — recorded because it is the honest
      one-line answer to "where did the view go". *)
  Lemma wptsto_cobj ξ a v : wptsto ξ a v ⊣⊢ cobj ξ (wpt_own ξ a v).
  Proof.
    rewrite /wptsto /cobj. iSplit.
    - iIntros "[%t (He & Hs & #Hf)]". iExists (view_byte a t). iFrame "Hf".
      rewrite wpt_own_at_view. iExists t. iFrame "He Hs". iPureIntro.
      rewrite flr_byte_eq. lia.
    - iIntros "[%V [#Hf Hpt]]". rewrite wpt_own_at_view.
      iDestruct "Hpt" as (t) "(He & Hs & %Ht)". iExists t. iFrame "He Hs".
      iApply (ctx_view_lb_mono with "Hf"). by apply view_byte_le.
  Qed.

  Lemma wptsto_cl_cobj ξ a dq v :
    wptsto_cl ξ a dq v ⊣⊢ cobj ξ (a ↦w{dq} v).
  Proof.
    rewrite /wptsto_cl /cobj. iSplit.
    - iIntros "[%t (He & #Hf)]". iExists (view_byte a t). iFrame "Hf".
      rewrite wpt_at_view. iExists t. iFrame "He". iPureIntro.
      rewrite flr_byte_eq. lia.
    - iIntros "[%V [#Hf Hpt]]". rewrite wpt_at_view.
      iDestruct "Hpt" as (t) "[He %Ht]". iExists t. iFrame "He".
      iApply (ctx_view_lb_mono with "Hf"). by apply view_byte_le.
  Qed.

  Lemma wptsto_agree ξ ξ' a v v' :
    wptsto ξ a v -∗ wptsto ξ' a v' -∗ ⌜v = v'⌝.
  Proof.
    iIntros "[%t (He & _)] [%t' (He' & _)]".
    by iDestruct (wlat_elem_agree with "He He'") as %[_ ?].
  Qed.

End convert.

(* ====================================================================== *)
(** ** 4. THE iPROP-SURFACE LEAF RULES

    [WeakVProp] §4'/§5's owned rules, with §3's conversions wrapped around
    them.  What the caller sees:

      - the memory fact carries NO index, so the [σ]/[σ'] plumbing that the
        [vProp] forms impose on it disappears — the [wptsto] in and the
        [wptsto] out are the SAME proposition;
      - the floor comes from [ctx_own], not from the fact.  That is the
        stage's whole content, and it is why a store must REGISTER the new
        floor (the sync in [ctx_lb_sync]) where the [vProp] rule merely
        widened a receipt;
      - [ctx_own] is threaded, at exactly the two places it is threaded
        today ([ctx_migr] in the store rule, the ledger everywhere). *)

Section rules.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE OWNED LOAD.  A hart reads its own byte — clean, own-dirty, or
      dirtied on a hart it has since left; [WeakVProp.wpt_load_rule_own] does
      not care and neither does this. *)
  Lemma wptsto_load_rule (ξ : CtxId) (c : CPU) σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    ws_view (wm_ws σ) ⊑ ws_view (wm_ws σ') →
    wlat_interp (wm_img σ) (wm_log σ) -∗ ctx_own_at ξ c (wm_ws σ) -∗
    wptsto ξ a v ==∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    ctx_own_at ξ c (wm_ws σ') ∗ wptsto ξ a v.
  Proof.
    intros Hcoh Hok Himg Hlog Hview.
    iIntros "Hi [Hlb Hmg] Hpt".
    iDestruct (wptsto_to_own with "Hlb Hpt") as "[Hlb Hpt]".
    iDestruct (wpt_load_rule_own ξ σ σ' ak a v t' b Hcoh Hok Himg Hlog
                 ltac:(apply Hview) with "Hi Hpt") as "(%Hb & Hi & Hpt)".
    iMod (ctx_lb_sync ξ (wm_ws σ') with "[Hlb]") as "Ha".
    { by iApply (ctx_lb_mono with "Hlb"). }
    iDestruct (wptsto_of_own with "Ha Hpt") as "[Ha $]".
    iModIntro. iSplitR; [by iPureIntro|]. iFrame "Hi Hmg".
    by iApply (ctx_lb_of_auth with "Ha").
  Qed.

  (** The framing side conditions at the interpreter's own read post-state,
      as [WeakVProp.wpt_load_wread_own] discharges them. *)
  Lemma wptsto_load_wread (ξ : CtxId) (c : CPU) σ ak a v pa ts t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wlat_interp (wm_img σ) (wm_log σ) -∗ ctx_own_at ξ c (wm_ws σ) -∗
    wptsto ξ a v ==∗
    ⌜b = v⌝ ∗
    wlat_interp (wm_img (wread_post σ ak pa ts))
                (wm_log (wread_post σ ak pa ts)) ∗
    ctx_own_at ξ c (wm_ws (wread_post σ ak pa ts)) ∗ wptsto ξ a v.
  Proof.
    intros Hcoh Hok.
    iApply (wptsto_load_rule ξ c σ (wread_post σ ak pa ts) ak a v t' b
              Hcoh Hok (wread_post_img _ _ _ _) (wread_post_log _ _ _ _)).
    apply ws_view_mono, (wread_post_ws_le σ ak pa ts).
  Qed.

  (** THE OWNED STORE.  Three things enter beyond [WeakVProp]'s: the post-log
      authority and the migration invariant (both already threaded at every
      store site, and both riding in [ctx_own] now), and the REGISTRATION of
      the new floor in ξ's ledger — the one ghost operation this surface adds,
      performed here, inside the rule, where the [vProp] form merely handed
      the caller a wider receipt. *)
  Lemma wptsto_store_rule (ξ : CtxId) (c : CPU) σ σ' m a v v' :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_img σ' = wm_img σ →
    wm_log σ' = (wm_log σ ++ [m])%list →
    ws_view (wm_ws σ) ⊑ ws_view (wm_ws σ') →
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlog_auth (wm_log σ') -∗ wlat_interp (wm_img σ) (wm_log σ) -∗
    ctx_own_at ξ c (wm_ws σ) -∗ wptsto ξ a v ==∗
    wlog_auth (wm_log σ') ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    ctx_own_at ξ c (wm_ws σ') ∗ wptsto ξ a v'.
  Proof.
    intros Hma Hother Htid Himg Hlog Hview Hfl.
    iIntros "Hlg Hi [Hlb Hmg] Hpt".
    iDestruct (wptsto_to_own with "Hlb Hpt") as "[Hlb Hpt]".
    iMod (wpt_store_rule_own ξ c σ σ' m a v v' Hma Hother Htid Himg Hlog Hfl
            with "Hlg Hmg Hi Hpt") as "($ & Hmg & $ & Hpt)".
    iMod (ctx_lb_sync ξ (wm_ws σ') with "[Hlb]") as "Ha".
    { by iApply (ctx_lb_mono with "Hlb"). }
    iDestruct (wptsto_of_own with "Ha Hpt") as "[Ha $]".
    iModIntro. iFrame "Hmg". by iApply (ctx_lb_of_auth with "Ha").
  Qed.

  (** ... at the machine's own store post-state, where both view premises are
      automatic. *)
  Lemma wptsto_store_post (ξ : CtxId) (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wlog_auth ((wm_log σ ++ [m])%list) -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    ctx_own_at ξ c (wm_ws σ) -∗ wptsto ξ a v ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ctx_own_at ξ c (store_post (wm_ws σ) rl a (S (length (wm_log σ)))) ∗
    wptsto ξ a v'.
  Proof.
    intros Hma Hother Htid.
    iApply (wptsto_store_rule ξ c
              (WMState (wm_regs σ) (wm_img σ) (wm_log σ) (wm_ws σ) (wm_dev σ))
              (WMState (wm_regs σ) (wm_img σ) ((wm_log σ ++ [m])%list)
                       (store_post (wm_ws σ) rl a (S (length (wm_log σ))))
                       (wm_dev σ)));
      [exact Hma|exact Hother|exact Htid|reflexivity|reflexivity| |].
    - apply ws_view_mono, store_post_le.
    - apply flr_store_post.
  Qed.

  (** THE φ PAYMENT.  [WeakVProp.nv_ok_of_wpt_own] at this altitude: the
      owned byte pays [nv_ok] at the running hart whether or not the context
      has migrated since it dirtied the byte, and the ledger plays no part —
      the case split is [wown_ctx]'s, inside. *)
  Lemma nv_ok_of_wptsto (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8)
      img (log logA : list wmsg) :
    pub_transfer logA log c →
    wlog_auth logA -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    wptsto ξ a v -∗ ⌜nv_ok log c a⌝.
  Proof.
    intros Htr. iIntros "Hlog Hmg Hi [%t (He & Hs & _)]".
    by iApply (nv_ok_of_wown_ctx ξ c a t v img log logA Htr
                 with "Hlog Hmg Hi He Hs").
  Qed.

  Lemma nv_ok_of_wptsto_at (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8)
      img (log : list wmsg) :
    wlog_auth log -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    wptsto ξ a v -∗ ⌜nv_ok log c a⌝.
  Proof.
    iApply (nv_ok_of_wptsto ξ c a v img log log (pub_transfer_refl log c)).
  Qed.

  (** ... and the clean byte's, which needs neither the invariant nor the log
      authority (a clean byte is never anybody's outstanding store). *)
  Lemma nv_ok_of_wptsto_cl (ξ : CtxId) (c : CPU) (a : Z) (dq : dfrac)
      (v : bv 8) img (log : list wmsg) :
    wlat_interp img log -∗ wptsto_cl ξ a dq v -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hi [%t [He _]]".
    by iApply (nv_ok_of_pointsto img log c a dq t v with "Hi He").
  Qed.

End rules.

(* ====================================================================== *)
(** ** 5. THE AMBIENT API (φ-upgrade §1.7's convention, this surface)

    The rules above with the context read out of the [CurCtx] instance.  Thin
    wrappers and nothing else; the ξ-explicit primitives stay, because a proof
    with TWO contexts in scope — every lock library lemma below — must be able
    to use them at both. *)

Section cur_api.
  Context `{!riscvGS Σ, !weakGS Σ} `{XI : CurCtx}.

  Lemma wptsto_of_cl_cur a v : (a ↦wp v) -∗ a ↦wpo v.
  Proof. apply wptsto_of_cl. Qed.

  Lemma wptsto_load_rule_cur (c : CPU) σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    ws_view (wm_ws σ) ⊑ ws_view (wm_ws σ') →
    wlat_interp (wm_img σ) (wm_log σ) -∗ ctx_own_at cur_ctx c (wm_ws σ) -∗
    (a ↦wpo v) ==∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    ctx_own_at cur_ctx c (wm_ws σ') ∗ a ↦wpo v.
  Proof. apply wptsto_load_rule. Qed.

  Lemma wptsto_store_post_cur (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wlog_auth ((wm_log σ ++ [m])%list) -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    ctx_own_at cur_ctx c (wm_ws σ) -∗ (a ↦wpo v) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    ctx_own_at cur_ctx c (store_post (wm_ws σ) rl a (S (length (wm_log σ)))) ∗
    a ↦wpo v'.
  Proof. apply wptsto_store_post. Qed.

  Lemma nv_ok_of_wptsto_cur (c : CPU) (a : Z) (v : bv 8)
      img (log : list wmsg) :
    wlog_auth log -∗ ctx_migr cur_ctx c -∗ wlat_interp img log -∗
    (a ↦wpo v) -∗ ⌜nv_ok log c a⌝.
  Proof. apply nv_ok_of_wptsto_at. Qed.

End cur_api.

(* ====================================================================== *)
(** ** 6. RE-INDEXING: [ctx_dom] and the [CtxMorph] structural class
    (φ-upgrade §1.8, coordinator's refinement)

    A lock owns a CONTEXT, exactly as a process does, and its invariant holds
    that context's facts.  Moving a fact between contexts is therefore the
    lock library's basic operation, and it must be INVISIBLE to function
    proofs: the release and the acquire do it, once, for whatever payload the
    client wrote.  "Whatever payload" is what makes it a structural class.

    [ctx_dom ξ ξ'] is the permission: "ξ''s ledger dominates ξ's".  It is
    minted at exactly two places — a release (out of the releasing context's
    own ledger authority, after raising the lock context's ledger to the
    release view) and an acquire (out of the acquiring hart's view, which the
    [aq] transfer put above the lock's) — and spent only inside the lock
    library's own lemmas.

    IT IS NOT PERSISTENT, AND THAT IS FORCED.  A persistent "ξ' dominates ξ"
    would license registering a floor into ξ' for a fact created LATER, after
    ξ's ledger has grown past ξ''s — which is precisely the unsound step (it
    would hand a lock a floor it never had).  So the token CARRIES ξ's ledger
    authority, is threaded THROUGH the morphism rather than consumed by it,
    and — since an authority pins the view it is at — the token names that
    view.  Those are the two deviations from the signature the design
    sketched ([ctx_dom ξ ξ'] consumed, unindexed); both are what the ledger's
    algebra permits, and neither is visible to a client, because the token is
    minted and spent inside one lock lemma. *)

Section morph.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** "at view [V], ξ' 's ledger dominates ξ's": ξ's authority (which bounds
      every floor ξ ever registered by [V]) together with ξ' 's registration
      of [V] (which turns any such floor into one of ξ' 's). *)
  Definition ctx_dom (ξ ξ' : CtxId) (V : view) : iProp Σ :=
    (ctx_auth ξ V ∗ ctx_view_lb ξ' V)%I.

  (** THE CORE STEP, and the only thing any instance below does: a floor
      registered against ξ is a floor registered against ξ'. *)
  Lemma ctx_dom_lb ξ ξ' V V0 :
    ctx_dom ξ ξ' V -∗ ctx_view_lb ξ V0 -∗
    ctx_dom ξ ξ' V ∗ ctx_view_lb ξ' V0.
  Proof.
    iIntros "[Ha #Hd] #Hf".
    iDestruct (ctx_view_lb_valid with "Ha Hf") as %Hle.
    iFrame "Ha Hd". by iApply (ctx_view_lb_mono with "Hd").
  Qed.

  (** THE MINT.  Raise the target's ledger to the source's view; the source's
      authority then reads every floor the source ever registered.  This is
      the release direction ([ξ] = the depositor, [ξ'] = the lock) and, with
      the roles swapped, the acquire direction. *)
  Lemma ctx_dom_mint ξ ξ' V V' :
    V' ⊑ V →
    ctx_auth ξ V -∗ ctx_auth ξ' V' ==∗ ctx_auth ξ' V ∗ ctx_dom ξ ξ' V.
  Proof.
    iIntros (Hle) "Ha Ha'".
    iMod (ctx_auth_update ξ' V' V Hle with "Ha'") as "Ha'".
    iDestruct (ctx_view_lb_get ξ' V V with "Ha'") as "#Hd"; [reflexivity|].
    iModIntro. iFrame "Ha' Ha Hd".
  Qed.

  (** THE OTHER MINT — the acquire direction, where nothing has to be
      raised: the lock's ledger is already below the acquiring hart's view
      (the [aq] transfer put it there), so the acquirer's own authority
      registers it directly. *)
  Lemma ctx_dom_intro ξ ξ' V :
    ctx_auth ξ V -∗ ctx_view_lb ξ' V -∗ ctx_dom ξ ξ' V.
  Proof. iIntros "H1 #H2". by iFrame "H1 H2". Qed.

  (** ... and the token's source authority, given back — which is how a
      release returns the depositor's ledger to its [ctx_own]. *)
  Lemma ctx_dom_auth ξ ξ' V : ctx_dom ξ ξ' V -∗ ctx_auth ξ V.
  Proof. by iIntros "[$ _]". Qed.

  (** THE STRUCTURAL CLASS.  A payload is a FUNCTION of the context; being a
      [CtxMorph] is the (structural, instance-resolved) statement that it can
      be moved to another context given the permission. *)
  Class CtxMorph (R : CtxId → iProp Σ) := ctx_morph :
    ∀ (ξ ξ' : CtxId) (V : view),
      ⊢ ctx_dom ξ ξ' V -∗ R ξ ==∗ ctx_dom ξ ξ' V ∗ R ξ'.

  (** THE REAL INSTANCE — the re-registration.  Note it is the CLEAN
      points-to: the owned form carries a dirty author's breadcrumb, which is
      a fact about ξ's own ghost and has no image in ξ'.  That is not a gap
      but the protocol: a deposit is flipped clean by the release
      ([WeakGhost.wlat_flip]) before it is re-indexed, exactly as it is
      today. *)
  Global Instance ctx_morph_cl a dq v : CtxMorph (λ ξ, wptsto_cl ξ a dq v).
  Proof.
    iIntros (ξ ξ' V) "Hd [%t [He #Hf]]".
    iDestruct (ctx_dom_lb with "Hd Hf") as "[$ #Hf']".
    iModIntro. iExists t. by iFrame "He Hf'".
  Qed.

  (** ... and the SAME instance at the spelling the client's [<{ … }>]
      wrapper produces, where the bound context reaches the points-to through
      the [CurCtx] projection.  A separate instance is needed and not merely
      convenient: [Typeclasses Opaque cur_ctx] (φ-upgrade §1.7's hygiene) stops
      instance search from seeing through the projection, so the two spellings
      are the same term to CONVERSION but not to RESOLUTION. *)
  Global Instance ctx_morph_cl_cur a dq v :
    CtxMorph (λ XLK : CurCtx, wptsto_cl cur_ctx a dq v).
  Proof. apply (ctx_morph_cl a dq v). Qed.

  (** CONTEXT-FREE FACTS — tokens, pure facts, persistent knowledge, and the
      residue a payload carries.  Low priority so that a payload which really
      does mention its context is matched by the instances that move it. *)
  Global Instance ctx_morph_const (P : iProp Σ) :
    CtxMorph (λ _ : CtxId, P) | 100.
  Proof. iIntros (ξ ξ' V) "Hd HP". iModIntro. iFrame. Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ)
      `{!CtxMorph R1, !CtxMorph R2} : CtxMorph (λ ξ, (R1 ξ ∗ R2 ξ)%I).
  Proof.
    iIntros (ξ ξ' V) "Hd [H1 H2]".
    iMod (ctx_morph ξ ξ' V with "Hd H1") as "[Hd $]".
    by iMod (ctx_morph ξ ξ' V with "Hd H2") as "[$ $]".
  Qed.

  Global Instance ctx_morph_exist {A : Type} (Φ : A → CtxId → iProp Σ)
      `{!∀ x, CtxMorph (Φ x)} : CtxMorph (λ ξ, (∃ x : A, Φ x ξ)%I).
  Proof.
    iIntros (ξ ξ' V) "Hd [%x H]".
    iMod (ctx_morph ξ ξ' V with "Hd H") as "[$ H]".
    iModIntro. by iExists x.
  Qed.

  Global Instance ctx_morph_or (R1 R2 : CtxId → iProp Σ)
      `{!CtxMorph R1, !CtxMorph R2} : CtxMorph (λ ξ, (R1 ξ ∨ R2 ξ)%I).
  Proof.
    iIntros (ξ ξ' V) "Hd [H|H]".
    - iMod (ctx_morph ξ ξ' V with "Hd H") as "[$ H]". iModIntro. by iLeft.
    - iMod (ctx_morph ξ ξ' V with "Hd H") as "[$ H]". iModIntro. by iRight.
  Qed.

  (** The OWNED points-to, moved: available only through the clean form, and
      recorded here so that the asymmetry is a lemma rather than folklore. *)
  Lemma ctx_dom_ptsto ξ ξ' V a v :
    ctx_dom ξ ξ' V -∗ wptsto_cl ξ a (DfracOwn 1) v ==∗
    ctx_dom ξ ξ' V ∗ wptsto ξ' a v.
  Proof.
    iIntros "Hd Hpt".
    iMod (ctx_morph ξ ξ' V with "Hd Hpt") as "[$ Hpt]".
    iModIntro. by iApply wptsto_of_cl.
  Qed.

End morph.

(** THE PAYLOAD WRAPPER.  A client writes a lock payload as a plain [iProp]
    with the bare [↦wp] spellings; this turns it into the [CtxId → iProp]
    the library needs, by making the bound context the AMBIENT one inside.
    So the lock's own context is never written down at a client's lock
    invariant, and the payload's re-indexing is the library's business.
    THE SPELLING IS [<{ P }>] AND NOT [<[ P ]>] (which the design sketched):
    stdpp's insert notation [<[ k := v ]>] shares the [<[] prefix, and Coq
    reports the two as having "incompatible prefixes — one of them will
    likely not work".  Measured, not guessed; the brace form is free. *)
Notation "<{ P }>" := (λ XLK : CurCtx, P%I)
  (at level 0, P at level 200, format "<{  P  }>").

(* ======================================================================
   WHAT A PORTED PROOF TAKES FROM THIS FILE

   1. Memory facts are [a ↦wpo v] (mutable) and [a ↦wp{dq} v] (shared or
      deposited).  They are [iProp]s: they frame across ANY call, including
      a yield, because there is nothing in them to move.

   2. The running bundle [ctx_own ξ c] is threaded exactly as [cur_proc] is —
      one resource per function, re-bound at a migration.  Its ledger half is
      what makes every points-to's floor usable; its [ctx_migr] half is the
      Stage-1.6 migration invariant and is scheduler state.

   3. A leaf converts with §3 and calls the [vProp] rule.  The conversions
      are the ONLY place [monPred_at] appears in a ported proof, and they are
      inside the leaves.

   4. A lock's payload is a [CtxId → iProp] written [<{ … }>]; the library
      re-indexes it with [ctx_morph] at the release and the acquire.  If a
      payload's shape is not structural (a sealed abstraction), export its
      [CtxMorph] instance once, next to the sealing. *)

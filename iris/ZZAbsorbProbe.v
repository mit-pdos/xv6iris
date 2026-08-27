(* TsoCtxTwin2.v -- THE TWIN, REBUILT ON THE CORRECTED CONSTRUCTION
   ([claude-notes/projects/tso-port.md] checkpoint 0.3/0.5).

   [TsoCtxTwin.v] proved a TSO context machinery EXISTS; [TsoCtxRehearsal.v]
   then showed its GLOBAL-MAP ghost shape refutes two of the surface's
   exports ([own_context_alloc], [CtxMorph]'s bare update) and forces the
   interp into every transport.  Three rounds of review distilled the
   correction, and this file IS that correction, proved:

     - PER-CONTEXT STATE IS ONE MONOTONE NAT -- the context's BOUND [B],
       mirroring the machine's one-nat-per-hart view.  No per-address
       ledger: a ledger ENTRY duplicated the heap cell's timestamp and only
       its key did work.
     - THE PER-FACT STATE IS A BIT, RIDING IN THE POINTS-TO: CLEAN
       (justified by the bound -- a persistent [mono_nat_lb_own] at the
       context's own gname) or DIRTY (justified by the author's own
       unpublished write -- a fragment of the context's dirty set, whose
       author-tie lives in the running bundle, NOT in the fact; a fact that
       named its hart could not survive migration).
     - THE AUTHORITY TRAVELS WITH THE TOKEN.  [own_context]/[ctx_parked]
       carry the bound and dirty-set authorities; the state interpretation
       owns MACHINE ghosts only (latest-heap, log entries, log length, hart
       views) and mentions no context anywhere.  This is what makes
       [CtxMorph]'s original bare-update shape TRUE AS WRITTEN
       ([ctx_morph_pointsto] below), the fork mint read the parent's bound
       off the token ([twin_fork]), and park/resume/exchange/deposit all
       INTERP-FREE.
     - THE STABLE VIEW LOWER BOUND EXISTS: [view_lb h K] is persistent and
       monotone ("hart h's view has passed K", never falsified by later
       steps); [twin_resume]'s premise is [view_lb h K ∗ ⌜T ≤ K⌝] -- the
       honest form of "the resuming hart is at least as fresh as the parked
       stamp", checkpoint 0.4 item 3.

   WHAT CHANGED AGAINST THE REHEARSAL'S VERDICTS (each verified here):

     1. [CtxMorph] IS SATISFIABLE IN ITS BARE SHAPE: [ctx_dom ξ ξ'] itself
        carries ξ's (half-)authorities plus a bound-lb of ξ', so
        re-indexing a fact is a ghost-free entailment for clean facts and a
        fragment drop for dirty ones.  No interp.  ([no_ctx_morph_pointsto]
        refuted the shape only because the twin's ledger authority sat in
        the interp.)
     2. A FREE RUNNING MINT IS SOUND AGAIN ([twin_run_alloc]): a fresh
        context at bound 0 claims nothing (every timestamp-0 fact is
        visible to every agent at every view).  [no_own_context_alloc]'s
        refutation was an artefact of the hart-keyed run map, which this
        construction does not have.  THE INTERFACE RULING STANDS -- boot
        mints, fork mints PARKED, swtch exchanges -- as kernel meaning
        (a conjured context can hold nothing but boot-image facts and pins
        no hart); the mint's existence just means the SC-era caller shim
        is not a lie.
     3. CROSS-CONTEXT SHARING IS LEGAL ([twin_share]): the old twin's
        per-byte ledger uniqueness is gone, a clean fact re-indexes by
        COPYING its persistent lb, so a discarded byte lives at every
        context that ever received it and [ctx_pointsto_persist] no longer
        fights transport (checkpoint 0.4 item 6 dissolves).
     4. PARK CONVERTS DIRTY TO CLEAN BY ONE BOUND-RAISE ([twin_park]),
        interp-free: the parked stamp is K ⊔ W (the bundle's view receipt
        joined with its dirty watermark), and every dirty entry falls
        under it.  Resume re-founds the bundle purely ([twin_resume] is a
        WAND); the exchange composes ([twin_exchange]).

   THE GHOST MAP (who owns what):

     interp (machine only):
       γheap   : Z ↪ (nat * bv 8)   per-byte latest write (frags in facts);
       γlogm   : nat ↪ wmsg          log entries, PERSISTED at append --
                                     "log[i] = m" is stable because the log
                                     is append-only; the dirty author-tie
                                     rides on these;
       γloglen : mono_nat            log length (persistent lbs [llb]);
       γview   : auth (agent -d> max_nat)   hart views ([view_lb] frags).
     token (per context; [CtxId] carries BOTH gnames -- the twin's old
     bare-[nat] identity is what forced every claim into a global map):
       tc_bnd   : mono_nat           the BOUND -- clean facts' justification;
       tc_dirty : ghost_map (nat*Z) unit   the dirty set -- keys are
                                     (timestamp, byte); keyed by timestamp
                                     so a morphed-away fraction pins a key
                                     that is never reused, and a multi-byte
                                     message dirties distinct keys.

   Imports: stdpp + Iris + [TsoMem] (+ [TsoCtxTwin]'s PURE layer, qualified
   -- [latest], the read bridge, the append lemmas).  No WP, no language,
   no main tree. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.algebra Require Import auth dfrac numbers functions.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map mono_nat.
From xv6iris Require Import TsoMem.
From xv6iris Require TsoCtxTwin.

Local Open Scope Z_scope.

Local Notation latest := TsoCtxTwin.latest.
Local Notation img_fun := TsoCtxTwin.img_fun.

(* ================================================================== *)
(** * 1.  The view algebra: one auth over all harts' single-nat views  *)
(* ================================================================== *)

(* The per-hart view collapses [WeakCtx]'s per-byte floor function to a
   per-AGENT one: the whole per-hart state is one nat ([TsoMem]), so the
   monotone summary of "what hart h has observed" is [MaxNat (tvs h)]. *)
Definition viewUR : ucmra := discrete_funUR (λ _ : agent, max_natUR).

Definition vf (tvs : agent → nat) : viewUR := λ h, MaxNat (tvs h).

Definition vone (h : agent) (K : nat) : viewUR :=
  λ h', MaxNat (if decide (h' = h) then K else 0%nat).

Global Instance vf_core_id tvs : CoreId (vf tvs).
Proof. constructor => h. reflexivity. Qed.

Global Instance vone_core_id h K : CoreId (vone h K).
Proof. constructor => h'. reflexivity. Qed.

Lemma vone_incl_vf h K tvs : (K ≤ tvs h)%nat → vone h K ≼ vf tvs.
Proof.
  intros HK. exists (vf tvs). intros h'.
  rewrite discrete_fun_lookup_op /vone /vf max_nat_op.
  rewrite Nat.max_r; [done|].
  destruct (decide (h' = h)) as [->|Hne]; lia.
Qed.

Lemma vf_local_update tvs tvs' :
  (∀ h, tvs h ≤ tvs' h)%nat → (vf tvs, vf tvs) ~l~> (vf tvs', vf tvs').
Proof.
  intros Hle. rewrite local_update_unital_discrete => z _ Heq.
  split; [by intros h|]. intros h. specialize (Heq h). specialize (Hle h).
  rewrite discrete_fun_lookup_op in Heq. rewrite discrete_fun_lookup_op.
  rewrite /vf in Heq |- *.
  destruct (z h) as [zh].
  rewrite max_nat_op in Heq. rewrite max_nat_op.
  revert Heq. intros [= Heq]. rewrite Nat.max_l; [done|lia].
Qed.

(* ================================================================== *)
(** * 2.  The ghost classes                                            *)
(* ================================================================== *)

Class tsoCtx2G Σ := TsoCtx2G {
  tc2_heapG :: ghost_mapG Σ Z (nat * bv 8);
  tc2_logmG :: ghost_mapG Σ nat wmsg;
  tc2_natG :: mono_natG Σ;
  tc2_viewG :: inG Σ (authR viewUR);
  tc2_dirtyG :: ghost_mapG Σ (nat * Z) unit;
}.

(* The corrected identity: BOTH per-context gnames ride in it, so a token
   (and hence every authority) can be minted wherever the identity can. *)
Record CtxId := MkCtxId { tc_bnd : gname; tc_dirty : gname }.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
Global Instance ctx_id_inhabited : Inhabited CtxId :=
  populate (MkCtxId inhabitant inhabitant).
Global Instance ctx_id_countable : Countable CtxId.
Proof.
  apply (inj_countable' (λ ξ, (tc_bnd ξ, tc_dirty ξ))
           (λ p, MkCtxId p.1 p.2)).
  by intros [].
Qed.

Section twin2.
  Context {Σ : gFunctors} `{!tsoCtx2G Σ}.
  Context (γheap γlogm γloglen γview : gname).

  (* ---------------------------------------------------------------- *)
  (** ** 3. The machine-side persistent receipts                       *)
  (* ---------------------------------------------------------------- *)

  (** The log-length lower bound ("the log was at least this long").
      The [K = 0] arm keeps the empty receipt pure (minting the unit
      fragment would cost a bupd). *)
  Definition llb (K : nat) : iProp Σ :=
    (mono_nat_lb_own γloglen K ∨ ⌜K = 0%nat⌝)%I.

  Global Instance llb_persistent K : Persistent (llb K).
  Proof. apply _. Qed.
  Global Instance llb_timeless K : Timeless (llb K).
  Proof. apply _. Qed.

  Lemma llb_0 : ⊢ llb 0.
  Proof. by iRight. Qed.

  Lemma llb_le K K' : (K' ≤ K)%nat → llb K -∗ llb K'.
  Proof.
    iIntros (Hle) "[Hlb|%Hz]".
    - iLeft. by iApply mono_nat_lb_own_le.
    - iRight. iPureIntro. lia.
  Qed.

  Lemma llb_max K1 K2 : llb K1 -∗ llb K2 -∗ llb (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2". destruct (decide (K1 ≤ K2)%nat) as [Hle|Hgt].
    - iClear "H1". iApply (llb_le with "H2"). lia.
    - iClear "H2". iApply (llb_le with "H1"). lia.
  Qed.

  Lemma llb_valid n K : mono_nat_auth_own γloglen 1 n -∗ llb K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  (** THE STABLE HART-VIEW LOWER BOUND (checkpoint 0.4 item 3): "hart [h]'s
      view has passed [K]".  Persistent and monotone -- "h is at the log
      top" is false one step later, but this is never falsified.  It
      carries an [llb K] because a view never exceeds the log length, so
      every consumer that needs "K is a legal log position" has it without
      the interp. *)
  Definition view_lb (h : agent) (K : nat) : iProp Σ :=
    ((own γview (◯ vone h K) ∗ mono_nat_lb_own γloglen K) ∨ ⌜K = 0%nat⌝)%I.

  Global Instance view_lb_persistent h K : Persistent (view_lb h K).
  Proof. apply _. Qed.
  Global Instance view_lb_timeless h K : Timeless (view_lb h K).
  Proof. apply _. Qed.

  Lemma view_lb_0 h : ⊢ view_lb h 0.
  Proof. by iRight. Qed.

  Lemma view_lb_llb h K : view_lb h K -∗ llb K.
  Proof.
    iIntros "[[_ Hlb]|%Hz]"; [by iLeft | by iRight].
  Qed.

  (** The machine-side view authority.  [WeakCtx.ctx_auth]'s shape (auth
      and fragment at the same value) so a receipt is INCLUSION rather
      than an update. *)
  Definition view_auth (tvs : agent → nat) : iProp Σ :=
    own γview (● vf tvs ⋅ ◯ vf tvs).

  Lemma view_auth_frag tvs h K :
    (K ≤ tvs h)%nat → view_auth tvs -∗ own γview (◯ vone h K).
  Proof.
    iIntros (HK) "Hv". iApply (own_mono with "Hv").
    etrans; [apply auth_frag_mono, vone_incl_vf, HK | apply cmra_included_r].
  Qed.

  Lemma view_auth_valid tvs h K :
    view_auth tvs -∗ view_lb h K -∗ ⌜(K ≤ tvs h)%nat⌝.
  Proof.
    iIntros "Ha [[Hf _]|%Hz]"; last (iPureIntro; lia).
    iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro.
    move: Hv. rewrite -assoc -auth_frag_op.
    rewrite auth_both_valid_discrete => -[Hincl _].
    apply (discrete_fun_included_spec_1 _ _ h) in Hincl.
    move: Hincl. rewrite discrete_fun_lookup_op /vf /vone max_nat_op.
    rewrite decide_True; last done.
    move => /max_nat_included /=. lia.
  Qed.

  Lemma view_auth_update tvs tvs' :
    (∀ h, tvs h ≤ tvs' h)%nat → view_auth tvs ==∗ view_auth tvs'.
  Proof.
    iIntros (Hle). iApply own_update.
    by apply auth_update, vf_local_update.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 4. The tokens and the fact                                    *)
  (* ---------------------------------------------------------------- *)

  (** Both per-context authorities, at a fraction (the halves are what
      [ctx_dom] borrows; agreement across halves is what pins the borrow). *)
  Definition ctx_at (ξ : CtxId) (q : Qp) (B : nat)
      (D : gmap (nat * Z) unit) : iProp Σ :=
    (mono_nat_auth_own (tc_bnd ξ) q B ∗ ghost_map_auth (tc_dirty ξ) q D)%I.

  Lemma ctx_at_halves ξ B D :
    ctx_at ξ 1 B D ⊣⊢ ctx_at ξ (1/2) B D ∗ ctx_at ξ (1/2) B D.
  Proof.
    rewrite /ctx_at.
    rewrite (fractional_half (mono_nat_auth_own (tc_bnd ξ) 1 B)).
    rewrite (fractional_half (ghost_map_auth (tc_dirty ξ) 1 D)).
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma ctx_at_agree ξ q1 q2 B1 D1 B2 D2 :
    ctx_at ξ q1 B1 D1 -∗ ctx_at ξ q2 B2 D2 -∗ ⌜B1 = B2 ∧ D1 = D2⌝.
  Proof.
    iIntros "[Hb1 Hd1] [Hb2 Hd2]".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb2") as %[_ ?].
    iDestruct (ghost_map_auth_agree with "Hd1 Hd2") as %?.
    by iPureIntro.
  Qed.

  (** THE DIRTY ENTRY'S JUSTIFICATION, kept in the RUNNING BUNDLE (never in
      the fact): the entry's timestamp is already under the bound (morally
      clean, flipped lazily), or it is the hart's own message -- the
      forwarding arm of [visibleb].  The author-tie names the BUNDLE's
      hart, which is exactly why park must raise the bound before the
      context can leave [h]: the weak-memory branch's migration invariant,
      at a single nat. *)
  Definition dirty_ok (h : agent) (B : nat) (k : nat * Z) : iProp Σ :=
    (⌜(k.1 ≤ B)%nat⌝ ∨
     ∃ i m, ⌜k.1 = S i⌝ ∗ i ↪[γlogm]□ m ∗ ⌜wm_tid m = h⌝)%I.

  Global Instance dirty_ok_persistent h B k : Persistent (dirty_ok h B k).
  Proof. apply _. Qed.

  Lemma dirty_ok_mono h B B' k :
    (B ≤ B')%nat → dirty_ok h B k -∗ dirty_ok h B' k.
  Proof.
    iIntros (Hle) "[%Hb|H]"; [iLeft; iPureIntro; lia | by iRight].
  Qed.

  (** THE RUNNING BUNDLE.  "This hart is running as ξ": the two authorities,
      the stable view receipt tying the bound to the hart ([B ≤ K] and
      [view_lb h K] -- forever, since views only grow), the dirty watermark
      [W] (every dirty timestamp is a legal log position at most W -- what
      lets park and fork stamp without the interp), and the per-entry
      justification. *)
  Definition own_context (ξ : CtxId) (h : agent) : iProp Σ :=
    (∃ (B K W : nat) (D : gmap (nat * Z) unit),
      ctx_at ξ 1 B D ∗
      view_lb h K ∗ ⌜(B ≤ K)%nat⌝ ∗
      llb W ∗ ⌜∀ k, k ∈ dom D → (k.1 ≤ W)%nat⌝ ∗
      [∗ map] k ↦ _ ∈ D, dirty_ok h B k)%I.

  (** THE PARKED TOKEN.  The bound IS the stamp: park raises the bound past
      every dirty entry (that is the dirty→clean conversion), so a parked
      context's facts are all clean at [T] and the resumer needs exactly
      [T ≤ its view].  [llb T] keeps the stamp a legal log position. *)
  Definition ctx_parked (ξ : CtxId) (T : nat) : iProp Σ :=
    (∃ D : gmap (nat * Z) unit,
      ctx_at ξ 1 T D ∗ llb T ∗ ⌜∀ k, k ∈ dom D → (k.1 ≤ T)%nat⌝)%I.

  (** THE FACT.  The heap element plus the BIT: clean (a persistent lb of
      ξ's own bound -- nothing else; no ledger entry, no hart, no view) or
      dirty (a fragment of ξ's dirty set at the fact's own dq).  Sealed
      above the surface; the disjunction is never client-visible. *)
  Definition ctx_pointsto (ξ : CtxId) (a : Z) (dq : dfrac) (v : bv 8)
      : iProp Σ :=
    (∃ t : nat, a ↪[γheap]{dq} (t, v) ∗
       (mono_nat_lb_own (tc_bnd ξ) t ∨ (t, a) ↪[tc_dirty ξ]{dq} ()))%I.

  (** THE TRANSPORT PERMISSION -- and the checkpoint's "one correction,
      three problems" in one definition.  It carries HALF of ξ's own
      authorities (borrowed out of ξ's token, value-pinned by agreement
      with the half left behind) plus a bound-lb of ξ' dominating both ξ's
      bound and ξ's dirty watermark.  Nothing about the machine: Σ's
      constraint that [ctx_dom] be statable without the state
      interpretation holds BY CONSTRUCTION. *)
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ :=
    (∃ (B W B' : nat) (D : gmap (nat * Z) unit),
      ctx_at ξ (1/2) B D ∗
      ⌜∀ k, k ∈ dom D → (k.1 ≤ W)%nat⌝ ∗
      ⌜(B ≤ B')%nat⌝ ∗ ⌜(W ≤ B')%nat⌝ ∗
      mono_nat_lb_own (tc_bnd ξ') B')%I.

  (* Exclusivity / pairwise collisions: one authority, one token. *)
  Lemma own_context_excl ξ h1 h2 :
    own_context ξ h1 -∗ own_context ξ h2 -∗ False.
  Proof.
    iIntros "(%B1 & %K1 & %W1 & %D1 & [Hb1 _] & _)".
    iIntros "(%B2 & %K2 & %W2 & %D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Lemma ctx_parked_excl ξ T1 T2 :
    ctx_parked ξ T1 -∗ ctx_parked ξ T2 -∗ False.
  Proof.
    iIntros "(%D1 & [Hb1 _] & _) (%D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Lemma own_context_parked_excl ξ h T :
    own_context ξ h -∗ ctx_parked ξ T -∗ False.
  Proof.
    iIntros "(%B & %K & %W & %D & [Hb1 _] & _) (%D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Global Instance own_context_timeless ξ h : Timeless (own_context ξ h).
  Proof. apply _. Qed.
  Global Instance ctx_parked_timeless ξ T : Timeless (ctx_parked ξ T).
  Proof. apply _. Qed.
  Global Instance ctx_pointsto_timeless ξ a dq v :
    Timeless (ctx_pointsto ξ a dq v).
  Proof. apply _. Qed.
  Global Instance ctx_dom_timeless ξ ξ' : Timeless (ctx_dom ξ ξ').
  Proof. apply _. Qed.

  (** A discarded byte is persistent -- the dq is mirrored onto the dirty
      fragment precisely so this instance exists definitionally. *)
  Global Instance ctx_pointsto_discarded_persistent ξ a v :
    Persistent (ctx_pointsto ξ a DfracDiscarded v).
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 5. The state interpretation -- MACHINE ONLY                   *)
  (* ---------------------------------------------------------------- *)

  (* No run map, no parked map, no ledger: the interp does not know the
     contexts exist.  That is the corrected design's punchline, and it is
     why every context-lifecycle rule below is interp-free. *)
  Definition tso_interp (img : gmap Z (bv 8)) (log : list wmsg)
      (tvs : agent → nat) : iProp Σ :=
    (∃ (HM : gmap Z (nat * bv 8)) (LM : gmap nat wmsg),
      ghost_map_auth γheap 1 HM ∗
      ⌜∀ a t v, HM !! a = Some (t, v) → latest (img_fun img) log a t v⌝ ∗
      ghost_map_auth γlogm 1 LM ∗
      ⌜∀ i, LM !! i = log !! i⌝ ∗
      mono_nat_auth_own γloglen 1 (length log) ∗
      view_auth tvs ∗
      ⌜∀ h, (tvs h ≤ length log)%nat⌝)%I.

  (** The view receipt, minted at the hart's current view.  (The only
      producer of [view_lb]s above 0; in the real system this sits in the
      load/AMO leaves, where the interp is open.) *)
  Lemma twin_view_lb_get img log tvs h :
    tso_interp img log tvs -∗ tso_interp img log tvs ∗ view_lb h (tvs h).
  Proof.
    iIntros "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iDestruct (view_auth_frag tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hlen") as "#Hlb".
    iSplitL; last first.
    { iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs. }
    iExists HM, LM. by iFrame.
  Qed.

  (** The machine's view advance (the load's drain nondeterminism). *)
  Lemma twin_view_advance img log tvs h tv' :
    (tvs h ≤ tv')%nat → (tv' ≤ length log)%nat →
    tso_interp img log tvs ==∗
    tso_interp img log (λ h0, if decide (h0 = h) then tv' else tvs h0).
  Proof.
    iIntros (Hle Htop) "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iMod (view_auth_update tvs (λ h0, if decide (h0 = h) then tv' else tvs h0)
            with "Hv") as "Hv".
    { intros h0. destruct (decide (h0 = h)); [subst; lia | lia]. }
    iModIntro. iExists HM, LM. iFrame.
    iPureIntro. split_and!; [done|done|].
    intros h0. destruct (decide (h0 = h)); [lia | apply Htvs].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 6. Gate lemma: LOAD                                           *)
  (* ---------------------------------------------------------------- *)

  (** A running context's fact predicts the machine's load at EVERY
      admissible view advance of its hart -- both arms: a clean fact
      through the bound-under-view tie, a dirty one through the
      author/forwarding arm.  Any fraction. *)
  Lemma twin_load_ok img log tvs ξ h a dq v :
    tso_interp img log tvs -∗ own_context ξ h -∗ ctx_pointsto ξ a dq v -∗
    ⌜∀ tv', (tvs h ≤ tv')%nat →
       tso_read (img_fun img) log h tv' a = Some v⌝.
  Proof.
    iIntros "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & _ & _ & #Hoks)".
    iIntros "(%t & Hpt & Hbit)".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    iAssert (⌜∀ tv', (tvs h ≤ tv')%nat →
               visibleb h tv' log t = true⌝)%I as %Hvis; last first.
    { iPureIntro. move => tv' Htv'.
      apply (TsoCtxTwin.tso_read_of_latest _ _ _ _ _ t).
      - by apply (Hlat _ _ _ HHa).
      - by apply Hvis. }
    iDestruct "Hbit" as "[Hcl | Hdt]".
    - (* clean: t ≤ B ≤ K ≤ tvs h ≤ tv' *)
      iDestruct (mono_nat_lb_own_valid with "Hb Hcl") as %[_ HtB].
      iPureIntro. move => tv' Htv'. apply visibleb_below. lia.
    - (* dirty: the bundle's justification *)
      iDestruct (ghost_map_lookup with "Hd Hdt") as %HDt.
      iDestruct (big_sepM_lookup _ _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
      + iPureIntro. move => tv' Htv'. apply visibleb_below. simpl in HtB. lia.
      + iDestruct "Hown" as (i m) "(%Hti & Hi & %Htid)".
        iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
        iPureIntro. move => tv' _. simpl in Hti. rewrite Hti.
        apply (visibleb_own _ _ _ _ m); [by rewrite -HLM | done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 7. Gate lemma: STORE                                          *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_store_ok img log tvs ξ h a v w :
    tso_interp img log tvs -∗ own_context ξ h -∗
    ctx_pointsto ξ a (DfracOwn 1) v ==∗
    tso_interp img (store_log log h a [w]) tvs ∗ own_context ξ h ∗
    ctx_pointsto ξ a (DfracOwn 1) w.
  Proof.
    iIntros "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iIntros "(%t & Hpt & Hbit)".
    set (m := WMsg a [w] h).
    set (t' := S (length log)).
    (* the machine-side ghosts *)
    iMod (ghost_map_update (t', w) with "Hh Hpt") as "[Hh Hpt]".
    iDestruct (llb_valid with "Hlen HW") as %HWlen.
    have HLMfresh : LM !! length log = None.
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length log) m HLMfresh with "Hm")
      as "[Hm #Hlogm]".
    iMod (mono_nat_own_update (length (store_log log h a [w]))
            with "Hlen") as "[Hlen #Hlen']".
    { rewrite /store_log length_app /=. lia. }
    (* the dirty set: fresh key (t', a) *)
    have HDfresh : D !! (t', a) = None.
    { destruct (D !! (t', a)) eqn:HDt; last done. exfalso.
      have : ((t', a).1 ≤ W)%nat by apply HDW; eapply elem_of_dom_2.
      simpl. lia. }
    iMod (ghost_map_insert (t', a) () HDfresh with "Hd") as "[Hd Hdt]".
    (* drop the old bit (clean lb, or the old full dirty fragment) *)
    iClear "Hbit".
    iModIntro.
    iSplitR "Hb Hd Hpt Hdt"; last first.
    { iSplitR "Hpt Hdt"; last first.
      { iExists t'. iFrame "Hpt". iRight. iExact "Hdt". }
      iExists B, K, t', (<[(t', a) := ()]> D).
      iFrame "Hb Hd HK".
      iSplitR; first done.
      iSplitR.
      { iLeft. iApply (mono_nat_lb_own_le with "Hlen'").
        rewrite /store_log length_app /=. lia. }
      iSplitR.
      { iPureIntro. intros k Hk.
        apply dom_insert in Hk. apply elem_of_union in Hk as [Hk|Hk].
        - apply elem_of_singleton in Hk. subst k. simpl. lia.
        - have := HDW _ Hk. lia. }
      rewrite big_sepM_insert; last done.
      iSplitR; last done.
      iRight. iExists (length log), m. iFrame "Hlogm".
      iPureIntro. by split. }
    iExists (<[a := (t', w)]> HM), (<[length log := m]> LM).
    iFrame "Hh Hm Hlen".
    iSplitR.
    { iPureIntro. intros a0 t0 v0.
      destruct (decide (a0 = a)) as [->|Hne].
      - rewrite lookup_insert. intros [= <- <-].
        apply TsoCtxTwin.latest_app_new.
      - rewrite lookup_insert_ne; last congruence.
        intros HH0. rewrite /store_log.
        apply TsoCtxTwin.latest_app_frame; last by apply (Hlat _ _ _ HH0).
        by apply TsoCtxTwin.msg_byte_singleton_ne. }
    iSplitR.
    { iPureIntro. intros i. rewrite /store_log.
      destruct (decide (i = length log)) as [->|Hne].
      - rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      - rewrite lookup_insert_ne; last congruence.
        rewrite HLM.
        destruct (decide (i < length log)%nat) as [Hlt|Hge].
        + by rewrite lookup_app_l.
        + rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia. }
    rewrite /store_log length_app /=.
    have -> : (length log + 1 = S (length log))%nat by lia.
    iFrame "Hv".
    iPureIntro. intros h0. have := Htvs h0. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 8. Gate lemma: TRANSPORT ([CtxMorph], bare shape, as written)  *)
  (* ---------------------------------------------------------------- *)

  (** The class in the SURFACE's exact shape -- no interp, no view, no
      machine state.  [TsoCtxRehearsal.no_ctx_morph_pointsto] refuted this
      shape at the ledger twin; the authority-in-the-token construction
      proves it. *)
  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.

  Global Instance ctx_morph_pointsto a dq v :
    CtxMorph (λ ξ, ctx_pointsto ξ a dq v).
  Proof.
    iIntros (ξ ξ') "(%B & %W & %B' & %D & [Hb Hd] & %HDW & %HBB' & %HWB' & #Hlb')".
    iIntros "(%t & Hpt & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - (* clean: t ≤ B ≤ B' *)
        iDestruct (mono_nat_lb_own_valid with "Hb Hcl") as %[_ HtB].
        iPureIntro. lia.
      - (* dirty: t ≤ W ≤ B' *)
        iDestruct (ghost_map_lookup with "Hd Hdt") as %HDt.
        have HtW : ((t, a).1 ≤ W)%nat by apply HDW; eapply elem_of_dom_2.
        simpl in HtW. iPureIntro. lia. }
    (* The source's bit is dropped: a clean lb is spent nowhere, and a
       dirty fragment's key is a timestamp, never reused, so the pinned
       entry is inert.  The dom's halves are untouched, so they still
       agree with the token's. *)
    iClear "Hbit". iModIntro.
    iSplitL "Hb Hd".
    { iExists B, W, B', D. iFrame "Hb Hd Hlb'". by iPureIntro. }
    iExists t. iFrame "Hpt". iLeft.
    iApply (mono_nat_lb_own_le with "Hlb'"). lia.
  Qed.

  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P) | 100.
  Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR1 HR2]".
    iMod (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iMod (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ ξ') "Hd [%x HR]".
    iMod (ctx_morph with "Hd HR") as "[Hd HR]".
    iModIntro. iFrame "Hd". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_morph_big_sepL {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMorph (Φ i x)) →
    CtxMorph (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ ξ') "Hd _ !>". by iFrame.
    - iIntros (ξ ξ') "Hd [HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH (λ i y, Φ (S i) y) _ ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame.
  Qed.

  (* The surface's composition acid test, at the twin. *)
  Lemma ctx_morph_demo a1 a2 v1 (P : iProp Σ) :
    CtxMorph (λ ξ, ctx_pointsto ξ a1 (DfracOwn 1) v1 ∗
                   (∃ v2 : bv 8, ⌜v2 ≠ v1⌝ ∗
                      ctx_pointsto ξ a2 (DfracOwn 1) v2) ∗ P)%I.
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 9. The [ctx_dom] mints -- borrow accessors on the tokens      *)
  (* ---------------------------------------------------------------- *)

  (** RELEASE-SIDE / FORK-SIDE MINT, INTERP-FREE: domination into a PARKED
      target.  The target's stamp is raised to cover everything the source
      could deposit (its bound receipt K and its dirty watermark W -- both
      legal log positions by their [llb]s, so no interp is consulted).
      The give-back wand re-agrees the halves, so the source token comes
      back exactly as it went in. *)
  Lemma ctx_dom_to_parked ξ ξ' h T :
    own_context ξ h -∗ ctx_parked ξ' T ==∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξ' T' ∗ ctx_dom ξ ξ' ∗
          (ctx_dom ξ ξ' -∗ own_context ξ h).
  Proof.
    iIntros "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iIntros "(%D' & [Hb' Hd'] & #HT & %HD'T)".
    set (T' := Nat.max T (Nat.max K W)).
    iMod (mono_nat_own_update T' with "Hb'") as "[Hb' #Hlb']"; first lia.
    iModIntro. iExists T'.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitR; first (iPureIntro; lia).
    iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd'".
      iSplitR.
      { iApply (llb_max with "HT").
        iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
      iPureIntro. intros k Hk. have := HD'T _ Hk. lia. }
    iSplitL "Hat1".
    { iExists B, W, T', D. iFrame "Hat1 Hlb'". iPureIntro.
      split_and!; [done | lia | lia]. }
    (* the give-back *)
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _ & _ & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat".
    rewrite -ctx_at_halves.
    iExists B, K, W, D. iFrame "Hat HK HW Hoks". by iPureIntro.
  Qed.

  (** ACQUIRE-SIDE MINT: domination FROM a parked source INTO the running
      acquirer, whose hart sits at the log top (what the AMO delivers).
      The one mint that needs the interp -- it must compare the source's
      stamp with the log length and raise the acquirer's bound to its
      hart's view. *)
  Lemma ctx_dom_of_parked img log tvs ξ ξ' h T :
    (length log ≤ tvs h)%nat →
    tso_interp img log tvs -∗ own_context ξ' h -∗ ctx_parked ξ T ==∗
    tso_interp img log tvs ∗ own_context ξ' h ∗
    ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).
  Proof.
    iIntros (Htop) "Hint Hrun Hpk".
    iDestruct "Hint" as "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iDestruct "Hrun" as "(%B' & %K & %W & %D' & [Hb' Hd'] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D & Hat & #HT & %HDT)".
    (* the source stamp is a legal log position, hence under the view *)
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    (* raise the acquirer's bound to its (top) view *)
    iMod (mono_nat_own_update (tvs h) with "Hb'") as "[Hb' #Hlb']".
    { lia. }
    iDestruct (view_auth_frag tvs h (tvs h) with "Hv") as "#Hfr"; first done.
    iDestruct (mono_nat_lb_own_get with "Hlen") as "#Hlogl".
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    iSplitL "Hh Hm Hlen Hv".
    { iExists HM, LM. by iFrame. }
    iSplitL "Hb' Hd'".
    { iExists (tvs h), (tvs h), W, D'. iFrame "Hb' Hd'".
      iSplitR.
      { iLeft. iFrame "Hfr". iApply (mono_nat_lb_own_le with "Hlogl").
        apply Htvs. }
      iSplitR; first done.
      iFrame "HW". iSplitR; first done.
      iApply (big_sepM_mono with "Hoks").
      intros k u Hk. apply bi.wand_entails, dirty_ok_mono. lia. }
    iSplitL "Hat1".
    { iExists T, T, (tvs h), D. iFrame "Hat1 Hlb'".
      iPureIntro. split_and!; [exact HDT | lia | lia]. }
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* NOTE the asymmetry, and that it is the machine's: the parked-target
     mint is free because a parked context's stamp may be raised at will
     (its resume premise absorbs it), while the running-target mint must
     tie the new bound to the hart's actual view -- which only the AMO's
     at-the-top evidence supplies.  "Suspects (2) and (3) want the same
     token" (rehearsal), and that token is [view_lb] at the top. *)

  (* ---------------------------------------------------------------- *)
  (** ** 10. Gate lemma: PARK / RESUME / EXCHANGE -- all interp-free   *)
  (* ---------------------------------------------------------------- *)

  (** PARK: one bound-raise converts every dirty entry to clean.  The stamp
      is K ⊔ W -- the token's own receipts -- so the scheduler needs
      nothing from the machine.  (In the kernel the stamp is dominated by
      the log top at the handoff release, which is what the resumer's
      acquire then passes.) *)
  Lemma twin_park ξ h :
    own_context ξ h ==∗ ∃ T, ctx_parked ξ T.
  Proof.
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & _)".
    set (T := Nat.max K W).
    iMod (mono_nat_own_update T with "Hb") as "[Hb _]"; first lia.
    iModIntro. iExists T, D. iFrame "Hb Hd".
    iSplitR.
    { iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
    iPureIntro. intros k Hk. have := HDW _ Hk. lia.
  Qed.

  (** RESUME: a WAND.  The premise is the checkpoint's stable form --
      [view_lb h' K] persistent-monotone, [T ≤ K] pure -- and NOTHING
      relates the parking and resuming harts.  The bundle is re-founded
      with every dirty entry on its clean arm. *)
  Lemma twin_resume ξ T h K :
    (T ≤ K)%nat →
    view_lb h K -∗ ctx_parked ξ T -∗ own_context ξ h.
  Proof.
    iIntros (HTK) "#HK (%D & Hat & #HT & %HDT)".
    iExists T, K, T, D. iFrame "Hat HK HT".
    iSplitR; first done.
    iSplitR; first done.
    iApply big_sepM_intro. iIntros "!>" (k [] Hk).
    iLeft. iPureIntro. apply HDT. by eapply elem_of_dom_2.
  Qed.

  (** THE ACQUIRE→SWTCH EVIDENCE MINT (checkpoint 0.4 item 2, closed).
      The parked stamp [T] and the resumer's view receipt are both
      lower-bound facts, so they cannot be order-compared token-to-token;
      the ONE place both meet an authority is the lock-acquire leaf, where
      the AMO has just put the hart at the log top.  This lemma is that
      leaf's mint: the record's own [llb T] (exported off the parked token
      by [ctx_parked_llb]) plus at-the-top yields the STABLE pair
      [view_lb h K ∗ ⌜T ≤ K⌝] that [twin_resume]/[twin_exchange] consume —
      persistent-monotone, so it survives every step between the acquire
      and the swtch. *)
  Lemma ctx_parked_llb ξ T : ctx_parked ξ T -∗ ctx_parked ξ T ∗ llb T.
  Proof.
    iIntros "(%D & Hat & #HT & %HDT)".
    iSplitL "Hat"; last iExact "HT".
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  Lemma twin_passed_get img log tvs h T :
    (length log ≤ tvs h)%nat →
    tso_interp img log tvs -∗ llb T -∗
    tso_interp img log tvs ∗ view_lb h (tvs h) ∗ ⌜(T ≤ tvs h)%nat⌝.
  Proof.
    iIntros (Htop) "Hint #HT".
    iDestruct "Hint" as "(%HM & %LM & Hh & %Hlat & Hm & %HLM & Hlen & Hv & %Htvs)".
    iDestruct (llb_valid with "Hlen HT") as %HTlen.
    iDestruct (view_auth_frag tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hlen") as "#Hlb".
    iSplitL.
    { iExists HM, LM. by iFrame. }
    iSplitR; last (iPureIntro; lia).
    iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs.
  Qed.

  (** THE SWTCH EXCHANGE, derived: a hart always runs exactly one thread,
      and the intermediate tokenless state is not forbidden. *)
  Lemma twin_exchange ξ1 ξ2 T h K :
    (T ≤ K)%nat →
    view_lb h K -∗ own_context ξ1 h -∗ ctx_parked ξ2 T ==∗
    own_context ξ2 h ∗ ∃ T1, ctx_parked ξ1 T1.
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iMod (twin_park with "Hrun") as (T1) "Hpk1".
    iModIntro. iSplitR "Hpk1"; last by iExists T1.
    iApply (twin_resume with "HK Hpk"); done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 11. Gate lemma: THE FORK MINT AND THE FREE DEPOSIT            *)
  (* ---------------------------------------------------------------- *)

  (** The child is born PARKED, stamped off the parent's own token (K ⊔ W
      -- at least the parent's bound, and past its dirty writes), with
      both its gnames freshly allocated: [CtxId] carrying its own gnames
      is exactly what lets the mint run without any global authority.
      NO INTERP, and no freshness side conditions at all. *)
  Lemma twin_fork ξ h :
    own_context ξ h ==∗ own_context ξ h ∗ ∃ ξc T, ctx_parked ξc T.
  Proof.
    iIntros "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    set (T := Nat.max K W).
    iMod (mono_nat_own_alloc T) as (γb) "[Hbc _]".
    iMod (ghost_map_alloc_empty (K := nat * Z) (V := unit)) as (γd) "Hdc".
    iModIntro.
    iSplitL "Hat".
    { iExists B, K, W, D. iFrame "Hat HK HW Hoks". by iPureIntro. }
    iExists (MkCtxId γb γd), T, ∅. iFrame "Hbc Hdc".
    iSplitR.
    { iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
    iPureIntro. intros k Hk. rewrite dom_empty in Hk. set_solver.
  Qed.

  (** THE PURE BIRTH: a fresh parked context from NOTHING, at stamp 0.  The
      rehearsal's [no_ctx_parked_alloc] refuted exactly this under the
      global-map twin; with the authorities in the token it is one
      allocation.  This is [ProofForkretPark]'s mint (ruling 2d.4.1: fresh
      allocation yields a PARKED context and is pure); the parent-stamp
      refinement is subsumed by [twin_deposit] below, which raises the
      child's stamp per deposited fact. *)
  Lemma twin_parked_alloc : ⊢ |==> ∃ ξc, ctx_parked ξc 0.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod (ghost_map_alloc_empty (K := nat * Z) (V := unit)) as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), ∅. iFrame "Hb Hd".
    iSplitR; first by iApply llb_0.
    iPureIntro. intros k Hk. rewrite dom_empty in Hk. set_solver.
  Qed.

  (** THE GENERAL DEPOSIT, interp-free: a running context hands ANY
      morphable payload to a parked one, the parked stamp raised to cover
      it.  This is the surface's fork-deposit law and the release-side
      half of a lock handoff. *)
  Lemma twin_deposit (R : CtxId → iProp Σ) `{!CtxMorph R} ξ ξc h T :
    own_context ξ h -∗ ctx_parked ξc T -∗ R ξ ==∗
    own_context ξ h ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξc T' ∗ R ξc.
  Proof.
    iIntros "Hrun Hpk HR".
    iMod (ctx_dom_to_parked ξ ξc h T with "Hrun Hpk")
      as (T') "(%HTT' & Hpk & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iSplitL "Hback Hdom"; first by iApply "Hback".
    iExists T'. by iFrame.
  Qed.

  (** THE ACID TEST, now INTERP-FREE end to end: the parent hands the child
      a byte fact -- clean OR dirty, any fraction -- with nothing to prove.
      (The rehearsal's [twin_deposit_at_fork] needed the ledger authority,
      i.e. the interp; the corrected construction does not.) *)
  Lemma twin_fork_deposit ξ h a dq v :
    own_context ξ h -∗ ctx_pointsto ξ a dq v ==∗
    own_context ξ h ∗ ∃ ξc T, ctx_parked ξc T ∗ ctx_pointsto ξc a dq v.
  Proof.
    iIntros "Hrun Hpt".
    iMod (twin_fork with "Hrun") as "[Hrun (%ξc & %T & Hpk)]".
    iMod (ctx_dom_to_parked ξ ξc h T with "Hrun Hpk")
      as (T') "(%HTT' & Hpk & Hdom & Hback)".
    iMod (ctx_morph (R := λ ξ0, ctx_pointsto ξ0 a dq v) with "Hdom Hpt")
      as "[Hdom Hpt]".
    iModIntro. iSplitL "Hback Hdom"; first by iApply "Hback".
    iExists ξc, T'. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 12. The mint verdict, revisited                               *)
  (* ---------------------------------------------------------------- *)

  (** A free running mint IS satisfiable here (see the header): a context
      born at bound 0 with an empty dirty set claims nothing any agent at
      any view could not honour.  The interface ruling (boot mints, fork
      mints parked, swtch exchanges) stands as kernel meaning, not as a
      soundness necessity. *)
  Lemma twin_run_alloc h : ⊢ |==> ∃ ξ, own_context ξ h.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod (ghost_map_alloc_empty (K := nat * Z) (V := unit)) as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), 0%nat, 0%nat, 0%nat, ∅.
    iFrame "Hb Hd".
    iSplitR; first by iApply view_lb_0.
    iSplitR; first done.
    iSplitR; first by iApply llb_0.
    iSplitR; first (iPureIntro; intros k Hk; rewrite dom_empty in Hk; set_solver).
    by iApply big_sepM_empty.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 13. The dq law surface (the [mem_pointsto]-mirroring laws)    *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_pointsto_agree ξ1 ξ2 a dq1 v1 dq2 v2 :
    ctx_pointsto ξ1 a dq1 v1 -∗ ctx_pointsto ξ2 a dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "(%t1 & H1 & _) (%t2 & H2 & _)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= _ ->]. done.
  Qed.

  Lemma ctx_pointsto_ne ξ1 ξ2 a1 a2 dq v1 v2 :
    ctx_pointsto ξ1 a1 (DfracOwn 1) v1 -∗ ctx_pointsto ξ2 a2 dq v2 -∗
    ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "(%t1 & H1 & _) (%t2 & H2 & _)".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  Lemma ctx_pointsto_frac_split ξ a q1 q2 v :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) v ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) v ∗ ctx_pointsto ξ a (DfracOwn q2) v.
  Proof.
    iSplit.
    - iIntros "(%t & Hpt & Hbit)".
      iDestruct "Hpt" as "[Hpt1 Hpt2]".
      iDestruct "Hbit" as "[#Hcl | Hdt]".
      + iSplitL "Hpt1"; iExists t; iFrame; by iLeft.
      + iDestruct "Hdt" as "[Hdt1 Hdt2]".
        iSplitL "Hpt1 Hdt1"; iExists t; iFrame; by iRight.
    - iIntros "[(%t1 & Hpt1 & Hbit1) (%t2 & Hpt2 & Hbit2)]".
      iDestruct (ghost_map_elem_combine with "Hpt1 Hpt2") as "[Hpt %Heq]".
      injection Heq as <-.
      rewrite dfrac_op_own.
      iExists t1. iFrame "Hpt".
      iDestruct "Hbit1" as "[#Hcl | Hdt1]"; first by iLeft.
      iDestruct "Hbit2" as "[#Hcl | Hdt2]"; first by iLeft.
      iDestruct (ghost_map_elem_combine with "Hdt1 Hdt2") as "[Hdt _]".
      rewrite dfrac_op_own. by iRight.
  Qed.

  Lemma ctx_pointsto_persist ξ a dq v :
    ctx_pointsto ξ a dq v ==∗ ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "(%t & Hpt & Hbit)".
    iMod (ghost_map_elem_persist with "Hpt") as "Hpt".
    iDestruct "Hbit" as "[#Hcl | Hdt]".
    - iModIntro. iExists t. iFrame "Hpt". by iLeft.
    - iMod (ghost_map_elem_persist with "Hdt") as "Hdt".
      iModIntro. iExists t. iFrame "Hpt". by iRight.
  Qed.

  (** CROSS-CONTEXT SHARING, the checkpoint-0.4-item-6 dissolution: a byte
      really can live at two contexts at once -- transport COPIES a clean
      justification instead of moving a ledger entry.  (Under the old twin
      this was refutable: [reh_pt_one_context].) *)
  Lemma twin_share ξ ξ' a v :
    ctx_dom ξ ξ' -∗ ctx_pointsto ξ a (DfracOwn 1) v ==∗
    ctx_dom ξ ξ' ∗ ctx_pointsto ξ a (DfracOwn (1/2)) v ∗
    ctx_pointsto ξ' a (DfracOwn (1/2)) v.
  Proof.
    iIntros "Hdom Hpt".
    rewrite -{1}(Qp.div_2 1) ctx_pointsto_frac_split.
    iDestruct "Hpt" as "[Hpt1 Hpt2]".
    iMod (ctx_morph (R := λ ξ0, ctx_pointsto ξ0 a (DfracOwn (1/2)) v)
            with "Hdom Hpt2") as "[Hdom Hpt2]".
    iModIntro. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 14. Bound receipts for the boot image                         *)
  (* ---------------------------------------------------------------- *)

  (** Every context can hold a timestamp-0 fact: the bound is a mono-nat,
      so the zero receipt is free off any token.  (This is the twin image
      of "kernel text is context-free": an image byte needs no transport,
      any holder can justify it.) *)
  Lemma own_context_lb0 ξ h :
    own_context ξ h -∗ own_context ξ h ∗ mono_nat_lb_own (tc_bnd ξ) 0.
  Proof.
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct (mono_nat_lb_own_get with "Hb") as "#Hlb".
    iSplitL.
    { iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iApply (mono_nat_lb_own_le with "Hlb"). lia.
  Qed.

  Lemma ctx_pointsto_intro_zero ξ a dq v :
    a ↪[γheap]{dq} ((0%nat, v) : nat * bv 8) -∗
    mono_nat_lb_own (tc_bnd ξ) 0 -∗
    ctx_pointsto ξ a dq v.
  Proof.
    iIntros "Hpt #Hlb". iExists 0%nat. iFrame "Hpt". by iLeft.
  Qed.


  (* ================================================================== *)
  (** PROBE (read-only design analysis, 2026-08-26): the ABSORB law's
      twin image -- the running-context dual of [twin_deposit].          *)
  (* ================================================================== *)

  Lemma view_lb_max h K1 K2 :
    view_lb h K1 -∗ view_lb h K2 -∗ view_lb h (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2". destruct (decide (K1 ≤ K2)%nat) as [Hle|Hgt].
    - rewrite Nat.max_r; [ iExact "H2" | lia ].
    - rewrite Nat.max_l; [ iExact "H1" | lia ].
  Qed.

  (* the bound-raise with FOREIGN t and view evidence, as a ctx_dom mint:
     [ctx_dom_of_parked] with the interp's at-the-top evidence replaced by
     the STABLE pair [twin_resume] already consumes. *)
  Lemma ctx_dom_of_parked_stable ξ ξ' h T K :
    (T ≤ K)%nat →
    view_lb h K -∗ own_context ξ' h -∗ ctx_parked ξ T ==∗
    own_context ξ' h ∗ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iDestruct "Hrun" as "(%B' & %K0 & %W' & %D' & [Hb' Hd'] & #HK0 & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D & Hat & #HT & %HDT)".
    iMod (mono_nat_own_update (Nat.max B' T) with "Hb'") as "[Hb' #Hlb']".
    { lia. }
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    iSplitL "Hb' Hd'".
    { iExists (Nat.max B' T), (Nat.max K0 K), W', D'. iFrame "Hb' Hd' HW".
      iSplitR.
      { iApply (view_lb_max with "HK0 HK"). }
      iSplitR; first (iPureIntro; lia).
      iSplitR; first done.
      iApply (big_sepM_mono with "Hoks").
      intros k u Hk. apply bi.wand_entails, dirty_ok_mono. lia. }
    iSplitL "Hat1".
    { iExists T, T, (Nat.max B' T), D. iFrame "Hat1 Hlb'".
      iPureIntro. split_and!; [ exact HDT | lia | lia ]. }
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* THE ABSORB LAW, at the twin.  Dual of [twin_deposit]: a RUNNING context
     takes a morphable payload out of a PARKED record whose stamp its own
     hart's view has passed, and the record's token is handed straight back
     (so the invariant re-closes and the claim is REPEATABLE). *)
  Lemma twin_absorb (R : CtxId → iProp Σ) `{!CtxMorph R} ξ ξ' h T K :
    (T ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ctx_parked ξ T -∗ R ξ ==∗
    own_context ξ' h ∗ ctx_parked ξ T ∗ R ξ'.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk HR".
    iMod (ctx_dom_of_parked_stable ξ ξ' h T K HTK with "HK Hrun Hpk")
      as "(Hrun & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iFrame "Hrun HR". by iApply "Hback".
  Qed.

  (* the acid test, mirroring [twin_fork_deposit]: the escrow's own shape --
     a byte fact (any dq, clean OR dirty) claimed out of a parked record. *)
  Lemma twin_absorb_byte ξ ξ' h T K a dq v :
    (T ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ctx_parked ξ T -∗
    ctx_pointsto ξ a dq v ==∗
    own_context ξ' h ∗ ctx_parked ξ T ∗ ctx_pointsto ξ' a dq v.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk Hpt".
    iApply (twin_absorb (λ ξ0, ctx_pointsto ξ0 a dq v) ξ ξ' h T K with "Hrun HK Hpk Hpt").
    done.
  Qed.

  (* AND THE ROUND TRIP: absorb then re-deposit is the escrow's open/close.
     [ctx_deposit]'s twin is [twin_deposit], already proved above. *)
  Lemma twin_escrow_roundtrip (R R' : CtxId → iProp Σ)
      `{!CtxMorph R} `{!CtxMorph R'} ξ ξ' h T K :
    (T ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ctx_parked ξ T -∗ R ξ -∗
    (R ξ' -∗ R' ξ') ==∗
    own_context ξ' h ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξ T' ∗ R' ξ.
  Proof.
    iIntros (HTK) "Hrun #HK Hpk HR Hstep".
    iMod (twin_absorb R ξ ξ' h T K HTK with "Hrun HK Hpk HR")
      as "(Hrun & Hpk & HR)".
    iDestruct ("Hstep" with "HR") as "HR'".
    iMod (twin_deposit R' ξ' ξ h T with "Hrun Hpk HR'") as "[Hrun Hres]".
    by iModIntro; iFrame.
  Qed.

  (* the missing structural instance the escrow body needs (three arms). *)
  Global Instance ctx_morph_or (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∨ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR|HR]".
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]". iModIntro.
      iFrame "Hd". iLeft. iExact "HR".
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]". iModIntro.
      iFrame "Hd". iRight. iExact "HR".
  Qed.

End twin2.

(* ================================================================== *)
(** * 15. Satisfiability: the interp at the boot image                 *)
(* ================================================================== *)

Lemma twin2_init `{!tsoCtx2G Σ} (img : gmap Z (bv 8)) :
  ⊢ |==> ∃ γheap γlogm γloglen γview,
      tso_interp γheap γlogm γloglen γview img [] (λ _, 0%nat) ∗
      [∗ map] a ↦ v ∈ img, a ↪[γheap] ((0%nat, v) : nat * bv 8).
Proof.
  iMod (ghost_map_alloc ((λ v, (0%nat, v)) <$> img)) as (γheap) "[Hh Hfr]".
  iMod (ghost_map_alloc_empty (K := nat) (V := wmsg)) as (γlogm) "Hm".
  iMod (mono_nat_own_alloc 0) as (γloglen) "[Hlen _]".
  iMod (own_alloc (● vf (λ _, 0%nat) ⋅ ◯ vf (λ _, 0%nat))) as (γview) "Hv".
  { apply auth_both_valid_discrete. split; [done | by intros h]. }
  iModIntro. iExists γheap, γlogm, γloglen, γview.
  iSplitR "Hfr"; last first.
  { iApply (big_sepM_impl with "[Hfr]").
    { by rewrite big_sepM_fmap. }
    iIntros "!>" (a v Hlk) "H". iExact "H". }
  iExists ((λ v, (0%nat, v)) <$> img), ∅.
  iFrame "Hh Hm Hlen Hv".
  iPureIntro. split_and!.
  - intros a t v. rewrite lookup_fmap.
    destruct (img !! a) as [v0|] eqn:Ha; last done.
    simpl. intros [= <- <-]. split.
    + rewrite /log_byte /img_fun Ha //.
    + intros t' Ht'. destruct t' as [|i]; first lia.
      rewrite /log_byte /=. done.
  - intros i. rewrite lookup_empty lookup_nil //.
  - intros h. simpl. lia.
Qed.

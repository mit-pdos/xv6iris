(** * WeakCtx.v — THE EXECUTION CONTEXT, and objective ownership indexed by it.

    WHY THIS FILE EXISTS.  [WeakObj.wobj] is indexed by [CpuId]: its lower
    bounds live under [weak_view_name cpu_id].  That is fine as long as a
    proof never changes hart.  It stops being fine the moment an S-mode step
    can trap, yield, and RESUME ON A DIFFERENT HART -- which is exactly what
    [WpNext.wp_next] models:

      wp_next b p (fun (CID : CpuId) => K CID)

    Every resource written inside [K] is elaborated at the RESUMING hart,
    because the binder [CID] shadows the ambient one.  For SC resources that
    is a feature and costs nothing.  For [wobj] it is fatal: [@wobj CA F] and
    [@wobj CB F] are DIFFERENT PROPOSITIONS, so a frame written outside the
    binder does not mean the same thing inside it, and Iris's frame rule --
    which needs the frame's statement to be literally unchanged -- does not
    apply.  A caller would have to thread every owned resource into every
    call that might be preempted, which is every call.

    THE FIX IS NOT A NEW FRAME RULE.  It is to notice that two different
    things are indexed by the hart today:

      [hart_ws c ws]                     the hart's wstate.  MACHINE state.
                                         Genuinely per-hart.  Stays.
      [ws_auth (weak_view_name c) ws]    the authority behind the view LOWER
                                         BOUNDS that [wobj] is built from.

    The second has no business being per-hart.  "This resource was observable
    from view V" is a fact about a THREAD OF CONTROL, not about the silicon it
    is running on.  The two are conflated only because the port has never had
    more than one context per hart.  So: keep [hart_ws] per-hart, move the
    view authority to a CONTEXT, and objective ownership becomes hart-free.

    [CtxId] IS DELIBERATELY NOT A TYPECLASS, unlike [CpuId].  That asymmetry
    IS the design: [CpuId] is ambient so that [wp_next] can rebind it and
    every hart-resource follows automatically; [CtxId] is an explicit
    parameter so that nothing can rebind it and every context-resource is
    spelled identically on both sides of the binder.  Making [CtxId] a class
    -- or worse, giving it an instance derived from [CpuId] -- would silently
    reintroduce the bug this file exists to remove.

    WHY THE AUTHORITY IS A SINGLE [flr]-INDEXED AUTH, and not [ws_auth].
    This is the one real finding of the exercise, and it is not cosmetic.
    [ws_auth] carries five scalars and a coherence map, and is monotone along
    [ws_le] -- pointwise on the map, pointwise on the scalars.  Neither is
    available across a migration:

      - [ws_le wsA wsB] would demand hart B's [w_vrOld] / [w_vwOld] /
        [w_vwNew] / [w_vRel] dominate hart A's.  Nothing gives that; B may
        never have issued a load.
      - even POINTWISE-ON-THE-MAP fails.  If context ξ observed a write at
        byte [a] at timestamp 5, ξ's coherence map says 5 at [a]; hart B's
        map may say 0 there, because B never touched [a].  B still SEES the
        write -- its [w_vrNew] is above 5 after the acquire -- but that
        shows up in the FLOOR, not in the map.

    So the migrating object must be ordered by [⊑], i.e. by [flr], and not by
    any finer structure.  [ctx_auth] is therefore an authority on the single
    function [λ a, MaxNat (flr V a)], monotone exactly along [⊑] -- which is
    exactly what release/acquire delivers.  [WeakPtOwn.wflr_lb]'s three-way
    disjunction (coherence floor, scalar floor, or zero) is the shadow of the
    finer structure and is what makes it hart-shaped; here there is one
    disjunct and a unit case, and that is the whole difference. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.algebra Require Import auth numbers functions.
From iris.base_logic.lib Require Import iprop own.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import RiscvLang.
Require Import WeakMem WeakView WeakVProp WeakGhost WeakViewMono.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The algebra: a view as a single monotone function of floors. *)

Definition flr_fun (V : view) : cohUR := λ a, MaxNat (flr V a).

Lemma flr_fun_incl V V' : V ⊑ V' -> flr_fun V ≼ flr_fun V'.
Proof.
  intros Hle. exists (flr_fun V'). intros a.
  rewrite discrete_fun_lookup_op /flr_fun max_nat_op.
  rewrite Nat.max_r; [done|apply Hle].
Qed.

Lemma flr_fun_local_update V V' g :
  V ⊑ V' -> (flr_fun V, g) ~l~> (flr_fun V', flr_fun V').
Proof.
  intros Hle. rewrite local_update_unital_discrete => z _ Heq.
  split; [by intros a|]. intros a. specialize (Heq a). specialize (Hle a).
  rewrite discrete_fun_lookup_op in Heq. rewrite discrete_fun_lookup_op.
  rewrite /flr_fun in Heq |- *.
  destruct (g a) as [ga], (z a) as [za].
  rewrite max_nat_op in Heq. rewrite max_nat_op.
  revert Heq. intros [= Heq]. rewrite Nat.max_l; [done|lia].
Qed.

Global Instance flr_fun_core_id V : CoreId (flr_fun V).
Proof. constructor=> a. reflexivity. Qed.

(** A context is named by ONE ghost name.  Not a class -- see the header. *)
Definition CtxId : Type := gname.

(* ====================================================================== *)
(** ** 2. The context's view: authority and floors. *)

Section ctx.
  Context `{!weakViewG Σ}.

  (** The context's current view, exactly.  Carries the fragment at the same
      value, so handing out a floor is inclusion rather than an update. *)
  Definition ctx_auth (ξ : CtxId) (V : view) : iProp Σ :=
    own ξ (● flr_fun V ⋅ ◯ flr_fun V).

  (** THE PERSISTENT FLOOR, whole-view.  A single fragment rather than a
      family of per-byte ones: the object we need to be monotone in is
      exactly [flr], so making the floor one [own] at [flr_fun V] means
      validity, weakening and joining are each ONE [own] step instead of a
      quantified family.  ([WeakPtOwn.wflr_lb] is per-byte because its
      authority is [ws_auth], which has no single monotone summary.)

      The right disjunct is the unit case: [flr_fun view_bot] is [ε], and
      [own ξ ε] is not derivable without a [bupd], so an all-zero floor is
      carried as a pure fact instead. *)
  Definition ctx_view_lb (ξ : CtxId) (V : view) : iProp Σ :=
    (own ξ (◯ flr_fun V) ∨ ⌜∀ a, flr V a = 0%nat⌝)%I.

  Global Instance ctx_view_lb_persistent ξ V : Persistent (ctx_view_lb ξ V).
  Proof. apply _. Qed.

  Lemma flr_fun_op V1 V2 : flr_fun V1 ⋅ flr_fun V2 ≡ flr_fun (V1 ⊔ V2).
  Proof.
    intros a. rewrite discrete_fun_lookup_op /flr_fun max_nat_op flr_join //.
  Qed.

  Lemma ctx_view_lb_get ξ V V' :
    V' ⊑ V -> ctx_auth ξ V -∗ ctx_view_lb ξ V'.
  Proof.
    iIntros (Hle) "Ha". rewrite /ctx_auth own_op.
    iDestruct "Ha" as "[_ #Hf]". iLeft. iApply (own_mono with "Hf").
    apply auth_frag_mono, flr_fun_incl, Hle.
  Qed.

  Lemma ctx_view_lb_valid ξ V V' :
    ctx_auth ξ V -∗ ctx_view_lb ξ V' -∗ ⌜V' ⊑ V⌝.
  Proof.
    iIntros "Ha [Hf|%Hz]"; [|iPureIntro; intros a; rewrite Hz; lia].
    iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro. intros a.
    move: Hv. rewrite -assoc -auth_frag_op.
    rewrite auth_both_valid_discrete => -[Hincl _].
    apply (discrete_fun_included_spec_1 _ _ a) in Hincl.
    rewrite discrete_fun_lookup_op /flr_fun max_nat_op in Hincl.
    apply max_nat_included in Hincl. simpl in Hincl. lia.
  Qed.

  Lemma ctx_view_lb_bot ξ : ⊢ ctx_view_lb ξ view_bot.
  Proof. iRight. iPureIntro. apply flr_bot. Qed.

  Lemma ctx_view_lb_mono ξ V V' :
    V' ⊑ V -> ctx_view_lb ξ V -∗ ctx_view_lb ξ V'.
  Proof.
    iIntros (Hle) "[Hf|%Hz]".
    - iLeft. iApply (own_mono with "Hf").
      apply auth_frag_mono, flr_fun_incl, Hle.
    - iRight. iPureIntro. intros a. specialize (Hle a). specialize (Hz a). lia.
  Qed.

  Lemma ctx_view_lb_join ξ V1 V2 :
    ctx_view_lb ξ V1 -∗ ctx_view_lb ξ V2 -∗ ctx_view_lb ξ (V1 ⊔ V2).
  Proof.
    iIntros "[H1|%Z1] [H2|%Z2]".
    - iLeft. rewrite -flr_fun_op auth_frag_op own_op. iFrame "H1 H2".
    - iLeft. iApply (own_mono with "H1"). apply auth_frag_mono.
      apply flr_fun_incl. intros a. rewrite flr_join Z2. lia.
    - iLeft. iApply (own_mono with "H2"). apply auth_frag_mono.
      apply flr_fun_incl. intros a. rewrite flr_join Z1. lia.
    - iRight. iPureIntro. intros a. rewrite flr_join Z1 Z2 //.
  Qed.

  (** THE UPDATE.  Monotone along [⊑] and nothing finer -- which is the
      whole point of the header's finding. *)
  Lemma ctx_auth_update ξ V V' :
    V ⊑ V' -> ctx_auth ξ V ==∗ ctx_auth ξ V'.
  Proof.
    iIntros (Hle). iApply own_update.
    by apply auth_update, flr_fun_local_update.
  Qed.

  Lemma ctx_alloc V : ⊢ |==> ∃ ξ : CtxId, ctx_auth ξ V.
  Proof.
    iMod (own_alloc (● flr_fun V ⋅ ◯ flr_fun V)) as (ξ) "H".
    { apply auth_both_valid_discrete. split; [done|by intros a]. }
    by iExists ξ.
  Qed.

End ctx.

(* ====================================================================== *)
(** ** 3. [cobj]: objective ownership at a context.

    Verbatim [WeakObj.wobj] with the index changed.  The structural laws are
    the same laws, proved the same way -- they only ever use the lower
    bound's semilattice structure, which is why re-indexing costs nothing
    but the binder. *)

Section cobj.
  Context `{!weakViewG Σ}.

  Definition cobj (ξ : CtxId) (R : vProp Σ) : iProp Σ :=
    (∃ V : view, ctx_view_lb ξ V ∗ monPred_at R V)%I.

  Global Instance cobj_mono' ξ : Proper ((⊢) ==> (⊢)) (cobj ξ).
  Proof.
    intros R R' HR. rewrite /cobj.
    apply bi.exist_mono => V. apply bi.sep_mono_r. by apply monPred_at_mono.
  Qed.

  Lemma cobj_mono ξ R R' : (R ⊢ R') -> cobj ξ R -∗ cobj ξ R'.
  Proof. intros HR. apply bi.entails_wand, cobj_mono', HR. Qed.

  (** Needed so that ordinary [rewrite]s of [bi] laws can fire UNDER [cobj]
      -- e.g. [big_sepL_nil] inside the modality. *)
  Global Instance cobj_proper ξ : Proper ((≡) ==> (≡)) (cobj ξ).
  Proof.
    intros R R' HR. apply bi.equiv_entails.
    apply bi.equiv_entails in HR as [H1 H2].
    split; by apply bi.wand_entails, cobj_mono.
  Qed.

  Lemma cobj_sep ξ R R' : cobj ξ (R ∗ R') ⊣⊢ cobj ξ R ∗ cobj ξ R'.
  Proof.
    rewrite /cobj. iSplit.
    - iIntros "[%V [#Hlb [HR HR']]]". iSplitL "HR"; iExists V; by iFrame "Hlb".
    - iIntros "[[%V1 [#H1 HR]] [%V2 [#H2 HR']]]".
      iExists (V1 ⊔ V2). iSplitR.
      { by iApply (ctx_view_lb_join with "H1 H2"). }
      rewrite monPred_at_sep. iSplitL "HR".
      + iApply (monPred_mono with "HR"). intros a. rewrite flr_join. lia.
      + iApply (monPred_mono with "HR'"). intros a. rewrite flr_join. lia.
  Qed.

  Lemma cobj_exist ξ {A : Type} (Φ : A -> vProp Σ) :
    cobj ξ (∃ x, Φ x) ⊣⊢ ∃ x, cobj ξ (Φ x).
  Proof.
    rewrite /cobj. iSplit.
    - iIntros "[%V [#Hlb HR]]". rewrite monPred_at_exist.
      iDestruct "HR" as (x) "HR". iExists x, V. by iFrame "Hlb".
    - iIntros "[%x [%V [#Hlb HR]]]". iExists V. iFrame "Hlb".
      rewrite monPred_at_exist. by iExists x.
  Qed.

  Lemma cobj_pure ξ (φ : Prop) : cobj ξ ⌜φ⌝ ⊣⊢ ⌜φ⌝.
  Proof.
    rewrite /cobj. iSplit.
    - iIntros "[%V [_ HR]]". by rewrite monPred_at_pure.
    - iIntros "%H". iExists view_bot. iSplitR; [iApply ctx_view_lb_bot|].
      by rewrite monPred_at_pure.
  Qed.

  Lemma cobj_embed ξ (P : iProp Σ) : cobj ξ ⎡ P ⎤ ⊣⊢ P.
  Proof.
    rewrite /cobj. iSplit.
    - iIntros "[%V [_ HR]]". by rewrite monPred_at_embed.
    - iIntros "HP". iExists view_bot. iSplitR; [iApply ctx_view_lb_bot|].
      by rewrite monPred_at_embed.
  Qed.

  Lemma cobj_emp ξ : cobj ξ emp ⊣⊢ emp.
  Proof.
    rewrite /cobj. iSplit.
    - by iIntros "[%V [_ H]]".
    - iIntros "H". iExists view_bot. iSplitR; [iApply ctx_view_lb_bot|done].
  Qed.

  Lemma cobj_big_sepL ξ {A : Type} (l : list A) (Φ : nat -> A -> vProp Σ) :
    cobj ξ ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, cobj ξ (Φ k x).
  Proof.
    revert Φ. induction l as [|x l IH]; intros Φ.
    { rewrite !big_sepL_nil. apply cobj_emp. }
    rewrite !big_sepL_cons cobj_sep (IH (fun k y => Φ (S k) y)) //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. THE LEAF BRIDGE.  A leaf takes its frame as [vwp_hold F ws],
      indexed by the wstate the caller must not name.  These two convert, for
      an arbitrary [R], given only the context's authority. *)

  Lemma cobj_to_hold ξ ws R :
    ctx_auth ξ (ws_view ws) -∗ cobj ξ R -∗
    ctx_auth ξ (ws_view ws) ∗ vwp_hold R ws.
  Proof.
    iIntros "Ha [%V [#Hlb HR]]".
    iDestruct (ctx_view_lb_valid with "Ha Hlb") as %Hle.
    iFrame "Ha". rewrite /vwp_hold. by iApply (monPred_mono with "HR").
  Qed.

  Lemma cobj_of_hold ξ ws R :
    ctx_auth ξ (ws_view ws) -∗ vwp_hold R ws -∗
    ctx_auth ξ (ws_view ws) ∗ cobj ξ R.
  Proof.
    iIntros "Ha HR". rewrite /vwp_hold.
    iDestruct (ctx_view_lb_get ξ (ws_view ws) (ws_view ws) with "Ha") as "#Hlb";
      [reflexivity|].
    iFrame "Ha". iExists (ws_view ws). by iFrame "HR".
  Qed.

  (** The two halves of a lock/park boundary, for an arbitrary payload. *)
  Lemma cobj_release ξ V T R :
    (∀ a, (flr V a ≤ T)%nat) ->
    ctx_auth ξ V -∗ cobj ξ R -∗ ctx_auth ξ V ∗ monPred_at R (view_scl T).
  Proof.
    iIntros (HT) "Ha [%V0 [#Hlb HR]]".
    iDestruct (ctx_view_lb_valid with "Ha Hlb") as %Hle.
    iFrame "Ha". iApply (monPred_mono with "HR").
    intros a. rewrite flr_scl_eq. etrans; [apply Hle|apply HT].
  Qed.

  Lemma cobj_acquire ξ V T R :
    (∀ a, (T ≤ flr V a)%nat) ->
    ctx_auth ξ V -∗ monPred_at R (view_scl T) -∗ ctx_auth ξ V ∗ cobj ξ R.
  Proof.
    iIntros (HT) "Ha HR".
    iDestruct (ctx_view_lb_get ξ V (view_scl T) with "Ha") as "#Hlb".
    { intros a. rewrite flr_scl_eq. apply HT. }
    iFrame "Ha". iExists (view_scl T). by iFrame "HR".
  Qed.

End cobj.

(* ====================================================================== *)
(** ** 5. [wrunning]: which context this hart is running.

    The successor of [WeakGhost.hart_view].  Same shape -- the hart's wstate
    paired with the authority that tracks it -- but the authority belongs to
    the CONTEXT, so the pairing is what migrates. *)

Section running.
  Context `{!weakGS Σ}.

  Definition wrunning `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    (∃ ws : wstate, hart_ws cpu_id ws ∗ ctx_auth ξ (ws_view ws))%I.

  Lemma ws_le_view ws ws' : ws_le ws ws' -> ws_view ws ⊑ ws_view ws'.
  Proof.
    intros (Hc & _ & _ & H3 & _). intros a. rewrite !flr_ws_view.
    specialize (Hc a). lia.
  Qed.

  Lemma wrunning_open `{CID : CpuId} ξ :
    wrunning ξ -∗ ∃ ws, hart_ws cpu_id ws ∗ ctx_auth ξ (ws_view ws).
  Proof. iIntros "H". iExact "H". Qed.

  Lemma wrunning_close `{CID : CpuId} ξ ws :
    hart_ws cpu_id ws -∗ ctx_auth ξ (ws_view ws) -∗ wrunning ξ.
  Proof. iIntros "H1 H2". iExists ws. iFrame. Qed.

  (** The ordinary step: the hart's wstate grew, so the context's view grows
      with it.  This is the only update a leaf performs. *)
  Lemma wrunning_step `{CID : CpuId} ξ ws ws' :
    ws_le ws ws' ->
    ctx_auth ξ (ws_view ws) -∗ hart_ws cpu_id ws' ==∗ wrunning ξ.
  Proof.
    iIntros (Hle) "Ha Hws".
    iMod (ctx_auth_update _ _ (ws_view ws') with "Ha") as "Ha".
    { by apply ws_le_view. }
    iModIntro. iApply (wrunning_close with "Hws Ha").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 6. MIGRATION.

      Hart A parks the context at whatever view it had; hart B picks it up.
      The only premises are the two halves of the synchronisation the
      scheduler already performs -- A released past its entire view, B
      acquired past that timestamp -- and NEITHER MENTIONS A RESOURCE.  Every
      [cobj ξ R] the context owns is untouched, because [ξ] is the same ghost
      and its floors only grew.

      Note what is NOT required: no relation between hart A's and hart B's
      wstates.  That is the header's finding in lemma form -- [ws_le] between
      two harts is unavailable and unnecessary; [⊑] between the context's
      parked view and the resuming hart's view is available and sufficient. *)
  Lemma wrunning_resume `{CID : CpuId} (ξ : CtxId) (VA : view) (ws : wstate)
      (T : nat) :
    (∀ a, (flr VA a ≤ T)%nat) ->      (* A released past its whole view *)
    (T ≤ w_vrNew ws)%nat ->            (* B acquired past T *)
    ctx_auth ξ VA -∗ hart_ws cpu_id ws ==∗ wrunning ξ.
  Proof.
    iIntros (HT Hacq) "Ha Hws".
    iMod (ctx_auth_update _ _ (ws_view ws) with "Ha") as "Ha".
    { intros a. rewrite flr_ws_view. etrans; [apply HT|lia]. }
    iModIntro. iApply (wrunning_close with "Hws Ha").
  Qed.

End running.

(* ====================================================================== *)
(** ** 7. THE M-MODE BRIDGE.

    [WeakAdequacy] hands each hart a [hart_view], which pairs the hart's
    wstate with [ws_auth (weak_view_name c)] -- the OLD, hart-indexed view
    authority.  A hart turns that into a context exactly once, at the top of
    its chain, which is the honest reading anyway: a boot context comes into
    existence when execution starts.

    The [ws_auth] half is DROPPED.  Once objective ownership is indexed by a
    context, nothing consumes the hart-indexed authority, and carrying both
    would mean every leaf performing two updates to keep them in step.  The
    [weak_view_name] field of [weakGS] is consequently vestigial; removing
    it is an adequacy-level change and is deliberately not bundled here. *)
Section bridge.
  Context `{!weakGS Σ}.

  Lemma hart_view_to_run `{CID : CpuId} :
    hart_view cpu_id ==∗ ∃ ξ : CtxId, wrunning ξ.
  Proof.
    iIntros "[%ws [Hws _]]".
    iMod (ctx_alloc (ws_view ws)) as (ξ) "Ha".
    iModIntro. iExists ξ. iApply (wrunning_close with "Hws Ha").
  Qed.

End bridge.

(* ====================================================================== *)
(** ** 8. THE RELEASE INTERFACE: a floor at a FINITE SET of addresses.

    This is the constructor [WeakLeafO] §10 records as missing, and the
    reason it was missing is that it had nowhere to live.  A release store
    hands back

      ⌜∀ j < 8, T ≤ flr (ws_view ws') (acc_addr ea j)⌝

    -- the released timestamp sits below the post-state view at the eight
    bytes it wrote, which is exactly what lets the acquirer of the lock
    recover the payload.  That statement NAMES [ws'], so any wrapper that
    hides the post-state erases it, and every other leaf in [WeakLeafO] is
    precisely such a wrapper.  Hence [c.sd] stopped at layer A.

    [ctx_view_lb] is the objective form: persistent, monotone, naming
    neither a hart nor a [wstate], and already equipped with the two laws
    this needs ([ctx_view_lb_get] to build one from the authority,
    [ctx_view_lb_valid] to spend it).  What remains is only to say WHICH
    view -- the join of the [n] single-byte views -- and that is a fold.

    NOTE WHAT MAKES THE FOLD WORK.  [ctx_view_lb] is a lower bound on ONE
    view, not a family indexed by address, so [n] separate byte-bounds have
    to become one view before they can be a single resource.  They can,
    because a join of byte views IS a view and [flr] distributes over it
    ([flr_join]).  That is the same collapse §2's header describes for
    [ctx_view_lb] as a whole, applied at the address axis: the per-byte
    family the hart-indexed layer needed is unnecessary once the bound is
    stated about a view.

    ADDRESSES ARE A FUNCTION [f : nat -> Z], not [acc_addr ea] -- so this
    file does not have to import [WeakInterp], and so the same lemmas serve
    a store of any width and any address pattern.  Nothing here requires
    [f] to be injective: [view_addrs_ge] holds even if two indices collide,
    since the join takes a maximum. *)

Fixpoint view_addrs (f : nat -> Z) (n : nat) (T : nat) : view :=
  match n with
  | O => view_bot
  | S k => view_byte (f k) T ⊔ view_addrs f k T
  end.

(** The bound is BELOW a view exactly when it holds at each address. *)
Lemma view_addrs_le (f : nat -> Z) (n T : nat) (V : view) :
  (∀ j : nat, (j < n)%nat -> (T ≤ flr V (f j))%nat) -> view_addrs f n T ⊑ V.
Proof.
  induction n as [|k IH]; simpl; intros Hj.
  - apply view_bot_le.
  - apply view_join_lub.
    + apply view_byte_le, Hj. lia.
    + apply IH. intros j Hlt. apply Hj. lia.
Qed.

(** ... and it really does bound each address (the converse direction, which
    is what a consumer spends). *)
Lemma view_addrs_ge (f : nat -> Z) (n T : nat) (j : nat) :
  (j < n)%nat -> (T ≤ flr (view_addrs f n T) (f j))%nat.
Proof.
  induction n as [|k IH]; simpl; intros Hlt; [lia|].
  rewrite flr_join. destruct (decide (j = k)) as [->|Hne].
  - rewrite flr_byte_eq. lia.
  - specialize (IH ltac:(lia)). lia.
Qed.

Section release.
  Context `{!weakViewG Σ}.

  (** BUILD: what a release store's post-state authority yields. *)
  Lemma ctx_addrs_get (ξ : CtxId) (V : view) (f : nat -> Z) (n T : nat) :
    (∀ j : nat, (j < n)%nat -> (T ≤ flr V (f j))%nat) ->
    ctx_auth ξ V -∗ ctx_view_lb ξ (view_addrs f n T).
  Proof.
    iIntros (Hj) "Ha".
    iApply (ctx_view_lb_get with "Ha"). by apply view_addrs_le.
  Qed.

  (** SPEND: what an acquirer recovers, against ITS OWN authority.  The
      point of the round trip is that the two authorities may be at
      different views and even at different harts -- the token is the same
      proposition on both sides, which [ctx_view_lb_valid] then reads
      against whichever authority is present. *)
  Lemma ctx_addrs_valid (ξ : CtxId) (V : view) (f : nat -> Z) (n T : nat) :
    ctx_auth ξ V -∗ ctx_view_lb ξ (view_addrs f n T) -∗
    ⌜∀ j : nat, (j < n)%nat -> (T ≤ flr V (f j))%nat⌝.
  Proof.
    iIntros "Ha Hlb".
    iDestruct (ctx_view_lb_valid with "Ha Hlb") as %Hle.
    iPureIntro. intros j Hj.
    etrans; [apply (view_addrs_ge f n T j Hj)|apply Hle].
  Qed.

End release.

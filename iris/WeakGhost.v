(** * WeakGhost.v — the weak-memory base logic's ghost state (M1c)

    The Iris side of [WeakLang]: the three PER-ERA ghost families of the
    design doc's Decision 5 base layer, the state interpretation over
    [WeakLang.wgstate], and the [irisGS] instance for [weak_riscv_lang].

    WHAT IS REUSED FROM THE EXISTING TREE, VERBATIM.  The base logic runs at
    [Context {!riscvGS Σ, !weakGS Σ}]: every REGISTER assertion
    ([RiscvPtsto.reg_pointsto] / [reg_pointsto_at] / [reg_interp] /
    [gregs_interp]) and every DEVICE assertion ([uart_frag] / [plic_frag] /
    [virtio_frag] / [dev_interp]) is the tree's, unchanged in statement and
    in meaning — the weak machine's register and device components are
    literally [RiscvLang]'s.  [riscvGS]'s [gen_heap] memory field simply goes
    unused: the byte memory is now the log + the per-byte latest-write map
    below.  (So is its whole crash/power apparatus — see the SIMPLIFICATIONS
    note.)

    THE THREE NEW FAMILIES (design doc, Decision 5):

      - [weak_log_name] : a MONO-LIST over [wmsg].  [wlog_auth] rides in the
        state interpretation at [wglog g]; [wlog_lb] is the persistent
        "the log extends this" snapshot.  Append-only holds in every
        [wprim_step] arm except PowerOn (M1b's SEAM FACT (1)), which is why
        this is a per-era resource.
      - [weak_lat_name] : a [ghost_map Z (nat * bv 8)] — the PER-BYTE
        LATEST-WRITE map.  [a ↪[γlat]{dq} (t, v)] is the base points-to:
        "timestamp [t] is the latest write to byte [a], and it wrote [v]".
        The state interpretation ties every entry to the real log
        ([wlat_agree] below, i.e. [WeakMem.latest] plus the value).  M2's
        [↦ₘ] is built on top of this, at [Arch.pa] through [pa_z].
      - [weak_ws_name] : one gname PER HART, carrying a [ghost_var wstate] in
        the standard halves pattern — [wws_auth] in the state
        interpretation, [hart_ws] with the client.  DEVIATION from the M1c
        brief, which asked for a [ghost_map CPU wstate]: a single map
        authority cannot be FOCUSED on one hart the way [gregs_interp_acc]
        focuses one hart's registers (the lifting rule would have to expose
        the whole map, or take the client's element, to say that the other
        harts' cells did not move), whereas the halves pattern makes the
        per-hart framing one [big_sepS_delete] — exactly how [gregs_interp]
        and the per-hart [era_strans_name]/[era_sie_name] families already
        work in this tree.  The leaf-facing [hart_ws c ws] is exclusive and
        agreement-checkable, which is all M2 needs.

    SIMPLIFICATIONS, all deliberate and all M1c-local (see the project
    worklist):

      - SINGLE ERA.  The state interpretation pins [wgpow g = true] and
        [wggen g = 0] ([wgen_pin]) instead of carrying the generation
        counter, the started counter, the era registry and the FS tie of
        [RiscvPtsto.power_interp].  The power thread is correspondingly
        absent from the adequacy pool ([WeakAdequacy]), exactly as
        [riscv_system_adequacy] predates the power layer.  The era
        indirection slots in HERE, at [weak_state_interp], in the shape
        [power_interp] already has: [⌜wgen_pin g⌝] becomes
        [gen_auth (wggen g) ∗ start_auth … ∗ ∃ R, registry … ∗ (if wgpow g
        then ∃ E, ⌜R !! wggen g = Some E⌝ ∗ <the five conjuncts below at E>
        else True)], and the three names above move into a per-era record.
      - NO vProp.  This is the base logic only; views are explicit.  M2 is
        where [monPred] and the [⊒V] surface arrive.
*)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakViewMono.
Require Import WeakView.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The classes *)

(** The log's algebra.  Only the ALGEBRA-level [mono_list] exists in this
    Iris (there is no [base_logic.lib.mono_list]), so the [own] wrappers are
    spelled out — the same shape [FsCrash.fs_hist_auth] uses. *)
Notation wlogR := (mono_listR (leibnizO wmsg)).

(** THE C/D/S STATE of a byte (the φ-upgrade's three-state protocol; see
    [claude-notes/design/weak-memory-phi-upgrade.md] §1).  It rides in a
    SECOND ghost map, keyed by the same [Z] addresses as the latest-write map
    and carrying NO value — which is exactly what lets the S state be entered
    by DISCARDING (a persistent witness that pins no value, so a sync byte
    stays writable) while the C and D states keep a full-fraction element that
    a store must consume.

      - [WClean]   — every [WCplain] message on the byte is PUBLISHED (some
                     later message of the same agent is [WCrel]).  This is the
                     state [wlat_pointsto] — hence [↦w] at every fraction —
                     carries, so nothing about the existing surface changes.
      - [WDirty c] — the byte's UNPUBLISHED [WCplain] messages are all hart
                     [c]'s.  Exclusive (full fraction only): a fraction split
                     would let two harts each believe they are the only dirty
                     author.
      - [WSync]    — the byte is permanently racy-readable and NO [WCplain]
                     message ever writes it.  Absorbing, entered once at boot
                     by [sync_mint], and PERSISTENT — which is what makes it
                     incompatible with the full-fraction element a [WCplain]
                     store needs, so "a sync byte is never plain-written" is
                     enforced by the dfrac algebra rather than by a side
                     condition every store site would have to thread. *)
Inductive wcds := WClean | WDirty (c : CPU) | WSync.

Global Instance wcds_eq_dec : EqDecision wcds.
Proof. solve_decision. Defined.

Class weakGpreS (Σ : gFunctors) := WeakGpreS {
  weak_pre_logG :: inG Σ wlogR;
  weak_pre_latG :: ghost_mapG Σ Z (nat * bv 8);
  weak_pre_cdsG :: ghost_mapG Σ Z wcds;
  weak_pre_wsG :: ghost_varG Σ wstate;
  (* the max-fun authority [WeakCtx]'s objective layer is built on
     ([ctx_auth] / [ctx_view_lb] / [cobj]).  It used to be here as the
     MONOTONE SHADOW of [weak_pre_wsG], for the deleted [weak_view_name];
     the shadow is gone, the algebra stayed and found a better consumer. *)
  weak_pre_viewG :: weakViewG Σ;
}.

Definition weakΣ : gFunctors :=
  #[ GFunctor wlogR; ghost_mapΣ Z (nat * bv 8); ghost_mapΣ Z wcds;
     ghost_varΣ wstate; weakViewΣ ].

Global Instance subG_weakGpreS Σ : subG weakΣ Σ -> weakGpreS Σ.
Proof. intros H. split; try (revert H; solve_inG). Qed.

Class weakGS (Σ : gFunctors) := WeakGS {
  weak_preGS :: weakGpreS Σ;
  weak_log_name : gname;
  weak_lat_name : gname;
  (* the C/D/S state map (φ-upgrade §1); same keys as [weak_lat_name] *)
  weak_cds_name : gname;
  (* PER HART, like [era_reg_name] (see the header's DEVIATION note) *)
  weak_ws_name : CPU -> gname;
  (* THERE WAS A FIFTH FIELD, [weak_view_name : CPU -> wview_names] — a
     per-hart monotone shadow of [weak_ws_name], so that a caller could
     read a FLOOR off the hart's view without naming the exact [wstate].
     It is deleted (2026-08-11).  The hart-indexed view discipline it
     served was replaced wholesale by [WeakCtx]'s CONTEXT-indexed one
     ([ctx_auth] / [ctx_view_lb] / [cobj] / [wrunning]), and the one
     surviving consumer, [WeakCtx.hart_view_to_run], was already
     discarding the shadow half with a [_]. *)
}.

(* ====================================================================== *)
(** ** 2. The per-byte latest-write picture, as a pure predicate *)

(** "[t] is the latest write to byte [a] in [log], and it wrote [v]".  This
    is [WeakMem.latest] with the value pinned; it is what one [γlat] element
    means, and what the state interpretation ties every element to. *)
Definition latest_val (img : image) (log : list wmsg) (a : Z) (t : nat)
    (v : bv 8) : Prop :=
  log_byte img log t a = Some v /\ ¬ writes_in log a t (length log).

Lemma latest_val_latest img log a t v :
  latest_val img log a t v -> latest img log a t.
Proof. intros [Hv Hn]. split; [by exists v|exact Hn]. Qed.

Lemma latest_val_ts img log a t v :
  latest_val img log a t v -> latest_ts log a = t.
Proof.
  intros H. exact (latest_ts_eq img log a t (latest_val_latest img log a t v H)).
Qed.

(** The value is determined: two elements for the same byte agree. *)
Lemma latest_val_agree img log a t1 v1 t2 v2 :
  latest_val img log a t1 v1 -> latest_val img log a t2 v2 -> t1 = t2 /\ v1 = v2.
Proof.
  intros H1 H2.
  assert (t1 = t2) as Ht.
  { apply (latest_unique img log a);
      [ exact (latest_val_latest img log a t1 v1 H1)
      | exact (latest_val_latest img log a t2 v2 H2) ]. }
  subst t2. split; [reflexivity|].
  destruct H1 as [Hv1 _]. destruct H2 as [Hv2 _]. rewrite Hv1 in Hv2. by simplify_eq.
Qed.

(** THE FRAMING FACT the memory arms of M2 live on: an element survives an
    append that does not write its byte.  [writes_in log a (length log)
    (length (log ++ ms))] is exactly "one of the NEW messages writes [a]",
    stated in [WeakMem]'s own vocabulary. *)
Lemma latest_val_app img log ms a t v :
  latest_val img log a t v ->
  ¬ writes_in (log ++ ms) a (length log) (length (log ++ ms)) ->
  latest_val img (log ++ ms) a t v.
Proof.
  intros [Hv Hn] Hnew.
  assert (Hle : (t ≤ length log)%nat)
    by (apply (log_byte_bounded img log t a); by exists v).
  split; [by rewrite log_byte_app|].
  intros (t' & Hlo & Hhi & Hw).
  destruct (decide (t' ≤ length log)%nat) as [Hle'|Hgt].
  - apply Hn. apply (writes_in_app_inv log ms a t (length log) (Nat.le_refl _)).
    exists t'. split_and!; [done|done|exact Hw].
  - apply Hnew. exists t'. split_and!; [lia|done|exact Hw].
Qed.

(** THE BACKWARD READING of [latest_val]'s second conjunct: EVERY message
    that writes byte [a] sits at or below the byte's latest-write timestamp.
    This is what turns a bound on the ELEMENT's timestamp into a bound on the
    whole write history of the byte, and it is the pure heart of the
    lazy-upgrade arm (§3b'' below): a floor that covers [t] covers every
    message that ever wrote [a]. *)
Lemma latest_val_plain_le img log a t v p m :
  latest_val img log a t v -> log !! p = Some m -> is_Some (msg_byte m a) ->
  (S p <= t)%nat.
Proof.
  intros [_ Hn] Hp [b Hb].
  destruct (decide (S p <= t)%nat) as [?|Hgt]; [done|exfalso].
  apply Hn. exists (S p). apply lookup_lt_Some in Hp as Hlen.
  split_and!; [lia|lia|]. exists m. rewrite Nat.sub_succ Nat.sub_0_r.
  split; [exact Hp|by exists b].
Qed.

(** ... and the converse reading of that premise, for the arm that must
    IDENTIFY the offending message: a write in the new window comes from one
    of the appended messages. *)
Lemma writes_in_app_new log ms a :
  writes_in (log ++ ms) a (length log) (length (log ++ ms)) ->
  exists m, m ∈ ms /\ is_Some (msg_byte m a).
Proof.
  intros (t & Hlo & _ & m & Hm & Hs). exists m. split; [|exact Hs].
  assert (Hge : (length log ≤ t - 1)%nat) by lia.
  rewrite (lookup_app_r log ms (t - 1)%nat Hge) in Hm.
  by eapply elem_of_list_lookup_2.
Qed.

Lemma not_writes_in_app_new log ms a :
  (forall m, m ∈ ms -> msg_byte m a = None) ->
  ¬ writes_in (log ++ ms) a (length log) (length (log ++ ms)).
Proof.
  intros Hno Hw. apply writes_in_app_new in Hw as (m & Hm & [v Hv]).
  rewrite (Hno m Hm) in Hv. discriminate.
Qed.

(** The state interpretation's tie: EVERY element of the [γlat] map is
    accurate at the current image and log.  Deliberately an agreement, not a
    domain equation — a byte nobody owns simply has no element. *)
Definition wlat_agree (img : image) (log : list wmsg)
    (m : gmap Z (nat * bv 8)) : Prop :=
  forall a tv, m !! a = Some tv -> latest_val img log a tv.1 tv.2.

Lemma wlat_agree_app img log ms m :
  wlat_agree img log m ->
  (forall a, is_Some (m !! a) ->
     ¬ writes_in (log ++ ms) a (length log) (length (log ++ ms))) ->
  wlat_agree img (log ++ ms) m.
Proof.
  intros Hag Hno a tv Ha. apply latest_val_app; [by apply Hag|].
  apply Hno. by exists tv.
Qed.

Lemma wlat_agree_insert img log m a t v :
  wlat_agree img log m -> latest_val img log a t v ->
  wlat_agree img log (<[a := (t, v)]> m).
Proof.
  intros Hag Hl a' tv Ha'.
  destruct (decide (a' = a)) as [->|Hne].
  - rewrite lookup_insert in Ha'. by simplify_eq.
  - rewrite lookup_insert_ne // in Ha'. by apply Hag.
Qed.

(** THE STORE FRAMING FACT (added at M2a, consumed by [WeakVProp]'s store
    rule).  Appending a message that writes EXACTLY the byte [a] keeps the
    whole map accurate once [a]'s element is retargeted at the new top
    timestamp: [a]'s new element is the fresh message (nothing is above it),
    and every OTHER element survives by [latest_val_app] because the message
    does not write its byte. *)
Lemma wlat_agree_store img log m a v' mm :
  msg_byte m a = Some v' ->
  (forall a', a' <> a -> msg_byte m a' = None) ->
  wlat_agree img log mm ->
  wlat_agree img (log ++ [m]) (<[a := (S (length log), v')]> mm).
Proof.
  intros Hma Hother Hag a' tv Ha'.
  destruct (decide (a' = a)) as [->|Hne].
  - rewrite lookup_insert in Ha'. simplify_eq. simpl. split.
    + rewrite log_byte_S (lookup_app_r log [m] (length log) (Nat.le_refl _))
              Nat.sub_diag /=. exact Hma.
    + rewrite length_app /=. intros (t & Hlo & Hhi & _). lia.
  - rewrite lookup_insert_ne // in Ha'.
    apply latest_val_app; [by apply Hag|].
    apply not_writes_in_app_new. intros m0 Hm0.
    apply elem_of_list_singleton in Hm0 as ->. by apply Hother.
Qed.

(** The INITIAL map of an era: one element per byte of the era-initial
    image, at timestamp 0.  Keyed by [Z] through [pa_z]; injectivity of
    [pa_z] is what makes the key translation lossless. *)
Global Instance pa_z_inj : Inj (=) (=) pa_z.
Proof.
  intros a b Heq. rewrite -(z_pa_pa_z a) -(z_pa_pa_z b) Heq //.
Qed.

Definition wlat_init (img : gmap Arch.pa (bv 8)) : gmap Z (nat * bv 8) :=
  list_to_map ((fun ab : Arch.pa * bv 8 => (pa_z ab.1, (0%nat, ab.2)))
                 <$> map_to_list img).

Lemma wlat_init_keys (img : gmap Arch.pa (bv 8)) :
  ((fun ab : Arch.pa * bv 8 => (pa_z ab.1, (0%nat, ab.2)))
     <$> map_to_list img).*1 = pa_z <$> (map_to_list img).*1.
Proof.
  induction (map_to_list img) as [|[a b] l IH]; [reflexivity|].
  rewrite !fmap_cons /=. by rewrite IH.
Qed.

Lemma wlat_init_nodup (img : gmap Arch.pa (bv 8)) :
  NoDup ((fun ab : Arch.pa * bv 8 => (pa_z ab.1, (0%nat, ab.2)))
           <$> map_to_list img).*1.
Proof.
  rewrite wlat_init_keys.
  apply (NoDup_fmap_2 pa_z). apply NoDup_fst_map_to_list.
Qed.

Lemma wlat_init_lookup (img : gmap Arch.pa (bv 8)) z tv :
  wlat_init img !! z = Some tv ->
  exists a b, z = pa_z a /\ img !! a = Some b /\ tv = (0%nat, b).
Proof.
  intros Hlk. rewrite /wlat_init in Hlk.
  apply elem_of_list_to_map_2, elem_of_list_fmap in Hlk as ([a b] & Heq & Hin).
  apply elem_of_map_to_list in Hin. simplify_eq. by exists a, b.
Qed.

(** The fresh era's map is accurate: nothing has been written, so every byte
    of the boot image is its own latest write, at timestamp 0. *)
Lemma wlat_init_agree (img : gmap Arch.pa (bv 8)) :
  wlat_agree (img_z img) [] (wlat_init img).
Proof.
  intros z tv Hlk.
  apply wlat_init_lookup in Hlk as (a & b & -> & Hab & ->).
  split; [by rewrite log_byte_0 img_z_lookup|].
  intros (t & Hlo & Hhi & _). simpl in Hhi. lia.
Qed.

(** ... and the big-op the initial-resource bundle is stated with: the
    [Z]-keyed elements ARE the [Arch.pa]-keyed image bytes. *)
Lemma big_sepM_wlat_init {PROP : bi} (Φ : Z -> nat * bv 8 -> PROP)
    (img : gmap Arch.pa (bv 8)) :
  ([∗ map] z ↦ tv ∈ wlat_init img, Φ z tv)
  ⊣⊢ ([∗ map] a ↦ b ∈ img, Φ (pa_z a) (0%nat, b)).
Proof.
  rewrite /wlat_init.
  rewrite (big_sepM_list_to_map Φ _ (wlat_init_nodup img)).
  rewrite big_sepL_fmap. by rewrite big_sepM_map_to_list.
Qed.

(* ====================================================================== *)
(** ** 2b. The C/D/S invariant, PURELY over the log

    THE ONE DESIGN DELTA that matters (design file §1 asked for the
    publication test to read the AUTHOR's [w_pub], which would have forced
    the whole [wstate] family into [wlat_interp] and hence into every one of
    the 140-odd leaf statements that mention it).  It is not needed:
    [WeakMem.store_post] raises the storing agent's [w_pub] to the store's
    OWN timestamp whenever the store is release-class, and [w_pub] only ever
    grows ([ws_le]).  So

        "some message of agent [tid] at a log position [≥ p] is [WCrel]"

    IMPLIES "position [p] is published by [tid]", and it is a predicate of the
    LOG ALONE.  Everything below is stated with it, so [wlat_interp] keeps its
    arity, the invariant is preserved by purely local reasoning at each store,
    and the machine-level bridge to [w_pub] ([wpub_of_rel_store] in
    [WeakStore]) is a separate, one-line fact that the φ export will use.

    SECOND DELTA: the DMA/boot agents.  [WeakLang.wmsgs_of_map] stamps the
    disk's messages [wm_tid = Some n_disk] and [wm_ak = WCplain] (the DMA-tid
    unification, seam 1a — the disk is an ORDINARY agent, one index past the
    harts), and the disk never issues a [WCrel] message, so a disk [WCplain]
    message can never be published.  Clean-purity therefore EXEMPTS every
    NON-HART author ([¬ tid_is_hart]): it constrains the messages of harts,
    which is what φ's bad-edge shape (a cross-hart read of an unpublished
    owned store) is about.  Layer 1's [WeakRobustMain.bad] carries the same
    conjunct from the other side, so the two align syntactically. *)

(** [p] writes byte [a] with an owned-store ([WCplain]) message [m]. *)
Definition wplain_at (log : list wmsg) (a : Z) (p : nat) (m : wmsg) : Prop :=
  log !! p = Some m /\ is_Some (msg_byte m a) /\ wm_ak m = WCplain.

(** [p] is PUBLISHED by agent [tid]: a later message of the same agent is a
    release-class store, which raised that agent's [w_pub] past [p].  THE
    DEFINITION NOW LIVES IN [WeakMem] ([wpublished] / [wpublished_app]) so
    that Layer 1's [WeakRobustMain.pub_of] is the very same predicate — the
    publication-alignment item of the lift plan.  Nothing else changed. *)

(** *** THE PUBLICATION FLOOR, PURELY (φ-upgrade §1.5, the framing pattern)

    [wpub_upto log tid n] — "agent [tid] has published EVERY position below
    [n]".  ONE release message of [tid] at index [q] with [n ≤ S q] does it,
    because [wpublished log tid p] only asks for a later release of the same
    agent; so this is [wpublished] uniformly over a whole prefix.

    It is exactly what a RELEASE STORE establishes about its own backlog at
    the moment it appends: the message's position IS the log's fresh top, so
    it covers every earlier position without naming any of them.  That is why
    a migration handoff can mint publication coverage of the parking hart's
    WHOLE view in one step ([WeakVProp.pub_covers_view]) — the ghost token a
    yield returns. *)
Definition wpub_upto (log : list wmsg) (tid : option agent) (n : nat) : Prop :=
  exists (q : nat) (mq : wmsg),
    (n <= S q)%nat /\ log !! q = Some mq /\ wm_tid mq = tid /\ wm_ak mq = WCrel.

Lemma wpub_upto_published log tid n p :
  wpub_upto log tid n -> (p < n)%nat -> wpublished log tid p.
Proof.
  intros (q & mq & Hn & Hq & Ht & Hk) Hp. exists q, mq. split_and!; try done. lia.
Qed.

(** Coverage cannot outrun the log: the release that establishes it is IN the
    log.  This is what bounds the migration invariant's map entries. *)
Lemma wpub_upto_len log tid n : wpub_upto log tid n -> (n <= length log)%nat.
Proof.
  intros (q & mq & Hn & Hq & _). apply lookup_lt_Some in Hq. lia.
Qed.

Lemma wpub_upto_mono log tid n n' :
  (n' <= n)%nat -> wpub_upto log tid n -> wpub_upto log tid n'.
Proof.
  intros Hle (q & mq & Hn & Hq & Ht & Hk). exists q, mq. split_and!; try done. lia.
Qed.

(** The token is a fact about a PREFIX, and it survives to the whole log —
    which is what makes the [wlog_lb]-carried spelling of the token sound
    across arbitrarily many later steps of any hart. *)
Lemma wpub_upto_prefix l log tid n :
  l `prefix_of` log -> wpub_upto l tid n -> wpub_upto log tid n.
Proof.
  intros [ms ->] (q & mq & Hn & Hq & Ht & Hk). exists q, mq. split_and!; try done.
  rewrite lookup_app_l //. by eapply lookup_lt_Some.
Qed.

Lemma wpub_upto_app log ms tid n :
  wpub_upto log tid n -> wpub_upto (log ++ ms) tid n.
Proof. apply wpub_upto_prefix. by apply prefix_app_r. Qed.

(** ... AND THE CONVERSE ACROSS ONE MESSAGE THAT CANNOT BE THE PUBLISHER
    (φ-upgrade §1.6).  A leaf reads the publication floor of a FOREIGN hart
    off the log authority it holds, and the authority it holds at a STORE
    site is the one at the POST-log — one message ahead of the [wlat_interp]
    the retarget must re-establish.  The gap closes for free: the appended
    message is the storing hart's own, so it is not the foreign hart's
    release, and coverage in the longer log was already coverage in the
    shorter one. *)
Lemma wpub_upto_unsnoc log mnew tid n :
  ¬ (wm_tid mnew = tid /\ wm_ak mnew = WCrel) ->
  wpub_upto (log ++ [mnew]) tid n -> wpub_upto log tid n.
Proof.
  intros Hne (q & mq & Hn & Hq & Ht & Hk).
  apply lookup_app_Some in Hq as [Hq|[Hge Hq]]; [by exists q, mq|].
  exfalso. destruct (q - length log)%nat as [|j] eqn:Hj; simpl in Hq;
    [|by rewrite lookup_nil in Hq]. simplify_eq. by apply Hne.
Qed.

(** THE TRANSFER CONDITION the owned leaves quantify over: "the messages the
    log authority is ahead of the interpretation by publish nothing on behalf
    of any hart other than [c]".  Two constructors cover every site — a load
    (the logs coincide) and a store (the extra message is [c]'s own). *)
Definition pub_transfer (logA log : list wmsg) (c : CPU) : Prop :=
  forall (c' : CPU) (n : nat), c' <> c ->
    wpub_upto logA (Some (fin_to_nat c')) n ->
    wpub_upto log (Some (fin_to_nat c')) n.

Lemma pub_transfer_refl log c : pub_transfer log log c.
Proof. by intros c' n _. Qed.

Lemma pub_transfer_snoc log mnew (c : CPU) :
  wm_tid mnew = Some (fin_to_nat c) -> pub_transfer (log ++ [mnew]) log c.
Proof.
  intros Htid c' n Hne. apply wpub_upto_unsnoc. intros [Ht _].
  apply Hne, (inj fin_to_nat). rewrite Htid in Ht. by injection Ht.
Qed.

(** THE MINT, purely: a release-class message appended at the top publishes
    every position of the log it was appended to. *)
Lemma wpub_upto_rel log (mrel : wmsg) tid :
  wm_tid mrel = tid -> wm_ak mrel = WCrel ->
  wpub_upto (log ++ [mrel]) tid (S (length log)).
Proof.
  intros Ht Hk. exists (length log), mrel. split_and!; try done.
  rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag.
Qed.

Definition wcds_clean (log : list wmsg) (a : Z) : Prop :=
  forall p m, wplain_at log a p m ->
    ¬ tid_is_hart (wm_tid m) \/ wpublished log (wm_tid m) p.

Definition wcds_dirty (log : list wmsg) (a : Z) (c : CPU) : Prop :=
  forall p m, wplain_at log a p m ->
    ¬ tid_is_hart (wm_tid m) \/ wpublished log (wm_tid m) p \/
    wm_tid m = Some (fin_to_nat c).

Definition wcds_sync (log : list wmsg) (a : Z) : Prop :=
  forall p m, ¬ wplain_at log a p m.

Definition wcds_ok (log : list wmsg) (a : Z) (s : wcds) : Prop :=
  match s with
  | WClean => wcds_clean log a
  | WDirty c => wcds_dirty log a c
  | WSync => wcds_sync log a
  end.

Lemma wcds_clean_dirty log a c : wcds_clean log a -> wcds_dirty log a c.
Proof. intros H p m Hp. destruct (H p m Hp); auto. Qed.

(** THE FRAMING FACT: a byte the appended messages do not write keeps its
    state, whatever it is.  ([wpublished] only gets easier as the log grows,
    and no new [wplain_at] obligation appears.) *)
Lemma wcds_ok_app log ms a s :
  (forall m, m ∈ ms -> msg_byte m a = None) ->
  wcds_ok log a s -> wcds_ok (log ++ ms) a s.
Proof.
  intros Hno.
  assert (Hback : forall p m, wplain_at (log ++ ms) a p m -> wplain_at log a p m).
  { intros p m (Hp & Hs & Hk).
    apply lookup_app_Some in Hp as [Hp|[_ Hp]]; [by split_and!|].
    exfalso. apply elem_of_list_lookup_2, Hno in Hp. rewrite Hp in Hs.
    by destruct Hs. }
  destruct s as [|c|]; simpl.
  - intros Hcl p m Hp. destruct (Hcl p m (Hback p m Hp)) as [?|?];
      [by left|right; by apply wpublished_app].
  - intros Hdi p m Hp. destruct (Hdi p m (Hback p m Hp)) as [?|[?|?]];
      [by left|right; left; by apply wpublished_app|by right; right].
  - intros Hsy p m Hp. exact (Hsy p m (Hback p m Hp)).
Qed.

(** ... and the STORE step at the byte the message writes.  The state moves
    by [wcds_own_step]: an owned ([WCplain]) store dirties, a release
    ([WCrel]) store CLEANS — it publishes every earlier own message of the
    same hart, which is exactly the D→C flip — and an exclusive ([WCexcl])
    store leaves the state alone. *)
Definition wcds_own_step (c : CPU) (k : wm_class) (s : wcds) : wcds :=
  match k with
  | WCplain => WDirty c
  | WCrel => WClean
  | WCexcl => s
  end.

Lemma wcds_ok_store_own log mnew a c s :
  wm_tid mnew = Some (fin_to_nat c) ->
  (s = WClean \/ s = WDirty c) ->
  wcds_ok log a s ->
  wcds_ok (log ++ [mnew]) a (wcds_own_step c (wm_ak mnew) s).
Proof.
  intros Htid Hs Hok.
  (* the old obligations, transported *)
  assert (Hdi : wcds_dirty log a c).
  { destruct Hs as [->| ->]; [by apply wcds_clean_dirty|exact Hok]. }
  assert (Hback : forall p m, wplain_at (log ++ [mnew]) a p m ->
                    wplain_at log a p m \/ (p = length log /\ m = mnew)).
  { intros p m (Hp & Hsm & Hk).
    apply lookup_app_Some in Hp as [Hp|[Hge Hp]]; [left; by split_and!|].
    right. destruct (p - length log)%nat as [|n] eqn:Hn; simpl in Hp;
      [|by rewrite lookup_nil in Hp]. simplify_eq. split; [lia|done]. }
  (* the release message publishes every earlier own message of [c] *)
  assert (Hpub : wm_ak mnew = WCrel ->
            forall p, (p < length log)%nat ->
              wpublished (log ++ [mnew]) (Some (fin_to_nat c)) p).
  { intros Hk p Hp. exists (length log), mnew. split_and!; try done; [lia|].
    rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag. }
  destruct (wm_ak mnew) as [| |] eqn:Hk; simpl.
  - (* WCplain: dirty by [c] *)
    intros p m Hp. destruct (Hback p m Hp) as [Hold|[-> ->]].
    + destruct (Hdi p m Hold) as [?|[?|?]];
        [by left|right; left; by apply wpublished_app|by right; right].
    + right; right. exact Htid.
  - (* WCrel: clean — the new message publishes [c]'s whole backlog *)
    intros p m Hp. destruct (Hback p m Hp) as [Hold|[-> ->]];
      [|by destruct Hp as (_ & _ & Hc); rewrite Hk in Hc].
    destruct (Hdi p m Hold) as [Hn|[Hp'|Hc]];
      [by left|right; by apply wpublished_app|].
    right. rewrite Hc. apply Hpub; [done|].
    destruct Hold as (Hlk & _). by eapply lookup_lt_Some.
  - (* WCexcl: the state is unchanged, and the new message is not plain *)
    destruct Hs as [-> | ->]; simpl in Hok |- *.
    + intros p m Hp. destruct (Hback p m Hp) as [Hold|[-> ->]];
        [|by destruct Hp as (_ & _ & Hc); rewrite Hk in Hc].
      destruct (Hok p m Hold) as [?|?];
        [by left|right; by apply wpublished_app].
    + intros p m Hp. destruct (Hback p m Hp) as [Hold|[-> ->]];
        [|by destruct Hp as (_ & _ & Hc); rewrite Hk in Hc].
      destruct (Hok p m Hold) as [?|[?|?]];
        [by left|right; left; by apply wpublished_app|by right; right].
Qed.

(** THE NON-PLAIN STORE: a message that is not an owned store adds no
    obligation to ANY state, so every state survives it — including [WSync]
    (the "a sync byte is never plain-written" clause) and [WClean] (which is
    why an AMO or a release keeps a shared/invariant-held bundle clean). *)
Lemma wcds_ok_store_nonplain log mnew a s :
  wm_ak mnew ≠ WCplain -> wcds_ok log a s -> wcds_ok (log ++ [mnew]) a s.
Proof.
  intros Hk Hok.
  assert (Hback : forall p m, wplain_at (log ++ [mnew]) a p m ->
                    wplain_at log a p m).
  { intros p m (Hp & Hs & Hkm).
    apply lookup_app_Some in Hp as [Hp|[_ Hp]]; [by split_and!|].
    exfalso. destruct (p - length log)%nat as [|n]; simpl in Hp;
      [|by rewrite lookup_nil in Hp]. simplify_eq; by apply Hk. }
  destruct s as [|c|]; simpl in Hok |- *.
  - intros p m Hp. destruct (Hok p m (Hback p m Hp)) as [?|?];
      [by left|right; by apply wpublished_app].
  - intros p m Hp. destruct (Hok p m (Hback p m Hp)) as [?|[?|?]];
      [by left|right; left; by apply wpublished_app|by right; right].
  - intros p m Hp. exact (Hok p m (Hback p m Hp)).
Qed.

Lemma wcds_ok_store_sync log mnew a :
  wm_ak mnew ≠ WCplain ->
  wcds_sync log a -> wcds_sync (log ++ [mnew]) a.
Proof. apply (wcds_ok_store_nonplain log mnew a WSync). Qed.

(** THE FLIP, purely.  A byte that is dirty by [c] is CLEAN as soon as [c]'s
    release store is the log's LAST message: that message publishes every
    earlier position, hence every one of [c]'s outstanding own stores.  This
    is what a release site applies to the bytes of its deposit, and it is
    stated at the POST-state so that the store's own window and the deposit's
    other bytes are flipped by one and the same lemma. *)
Lemma wcds_dirty_flip log a c q mq :
  log !! q = Some mq -> wm_tid mq = Some (fin_to_nat c) -> wm_ak mq = WCrel ->
  (length log <= S q)%nat ->
  wcds_dirty log a c -> wcds_clean log a.
Proof.
  intros Hq Htid Hk Hlen Hdi p m Hp.
  destruct (Hdi p m Hp) as [?|[?|Hc]]; [by left|by right|].
  right. rewrite Hc. exists q, mq. split_and!; try done.
  destruct Hp as (Hlk & _). apply lookup_lt_Some in Hlk. lia.
Qed.

(** THE LAZY UPGRADE, purely (φ-upgrade §1.5).  The flip above needs the
    releasing hart's message to be the log's LAST, which is what a release
    SITE has; a hart that PARKED and resumed elsewhere has no such thing —
    arbitrarily many messages of arbitrarily many harts sit between its
    migration handoff and the byte's first use on the new CPU.

    What survives that gap is a FLOOR: hart [c] published every position
    below [n], and the byte's whole write history is at or below its own
    latest-write timestamp [t] ([latest_val_plain_le]).  So [t ≤ n] flips it,
    no matter how long ago and no matter what has happened since.  This is
    the pure content of the acceptance arm. *)
Lemma wcds_dirty_flip_pub img log a (c : CPU) (t n : nat) (v : bv 8) :
  latest_val img log a t v -> (t <= n)%nat ->
  wpub_upto log (Some (fin_to_nat c)) n ->
  wcds_dirty log a c -> wcds_clean log a.
Proof.
  intros Hlat Htn Hpub Hdi p m Hp.
  destruct (Hdi p m Hp) as [Hnone|[Hp'|Hc]]; [by left|by right|].
  right. rewrite Hc. apply (wpub_upto_published log _ n p Hpub).
  destruct Hp as (Hlk & Hs & _).
  pose proof (latest_val_plain_le img log a t v p m Hlat Hlk Hs). lia.
Qed.

(** The map-level tie, the twin of [wlat_agree]. *)
Definition wcds_agree (log : list wmsg) (m : gmap Z wcds) : Prop :=
  forall a s, m !! a = Some s -> wcds_ok log a s.

Lemma wcds_agree_app log ms m :
  (forall a, is_Some (m !! a) -> forall mg, mg ∈ ms -> msg_byte mg a = None) ->
  wcds_agree log m -> wcds_agree (log ++ ms) m.
Proof.
  intros Hno Hag a s Ha. apply wcds_ok_app; [|by apply Hag].
  intros mg Hmg. apply (Hno a (mk_is_Some _ _ Ha) mg Hmg).
Qed.

Lemma wcds_agree_insert log m a s :
  wcds_agree log m -> wcds_ok log a s -> wcds_agree log (<[a := s]> m).
Proof.
  intros Hag Hok a' s' Ha'.
  destruct (decide (a' = a)) as [->|Hne].
  - rewrite lookup_insert in Ha'. by simplify_eq.
  - rewrite lookup_insert_ne // in Ha'. by apply Hag.
Qed.

(** The whole map survives a non-plain store: no state gains an obligation. *)
Lemma wcds_agree_nonplain log mnew mc :
  wm_ak mnew ≠ WCplain -> wcds_agree log mc -> wcds_agree (log ++ [mnew]) mc.
Proof. intros Hk Hag a s Ha. by apply wcds_ok_store_nonplain; [|apply Hag]. Qed.

(** The initial state map: every byte of the era-initial image is CLEAN (the
    log is empty, so there is nothing to publish). *)
Definition wcds_init (img : gmap Arch.pa (bv 8)) : gmap Z wcds :=
  (fun _ : nat * bv 8 => WClean) <$> wlat_init img.

Lemma wcds_init_agree (img : gmap Arch.pa (bv 8)) :
  wcds_agree [] (wcds_init img).
Proof.
  intros a s Ha. rewrite /wcds_init lookup_fmap in Ha.
  destruct (wlat_init img !! a) as [tv|]; simplify_eq/=.
  intros p m (Hp & _). by rewrite lookup_nil in Hp.
Qed.

Lemma big_sepM_wcds_init {PROP : bi} (Φ : Z -> wcds -> PROP)
    (img : gmap Arch.pa (bv 8)) :
  ([∗ map] z ↦ s ∈ wcds_init img, Φ z s)
  ⊣⊢ ([∗ map] a ↦ b ∈ img, Φ (pa_z a) WClean).
Proof.
  rewrite /wcds_init big_sepM_fmap.
  apply (big_sepM_wlat_init (fun z _ => Φ z WClean)).
Qed.

(* ====================================================================== *)
(** ** 1. The predicate

    Three spellings of the same thing, in the three altitudes the
    preservation proof works at:

      - [nv_byte log c' a n] — ONE hart's floor at ONE byte.  Every arm of
        the preservation argument is a fact about one byte, because that is
        the granularity at which the C/D/S state lives.
      - [nv_hart log c' ws] — one hart, all bytes: [nv_byte] at its own
        [coh].  This is the shape a per-hart (focused) interpretation would
        carry, the twin of [WeakMem.ws_bounded]'s per-hart conjunct.
      - [no_violation log wsf] — the GLOBAL statement, and the one the
        adequacy export is to produce.  Spelled exactly as the deliverable
        asks, i.e. with the message quantified first and the foreign hart
        last, so that the reading matches [WeakRobust.violation] term for
        term. *)

Definition nv_byte (log : list wmsg) (c' : CPU) (a : Z) (n : nat) : Prop :=
  forall (p : nat) (m : wmsg) (c : CPU),
    log !! p = Some m -> wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain -> ¬ wpublished log (wm_tid m) p ->
    is_Some (msg_byte m a) -> c' <> c -> (n < S p)%nat.

Definition nv_hart (log : list wmsg) (c' : CPU) (ws : wstate) : Prop :=
  forall a : Z, nv_byte log c' a (coh ws a).

Definition no_violation (log : list wmsg) (wsf : CPU -> wstate) : Prop :=
  forall (p : nat) (m : wmsg) (c : CPU) (a : Z),
    log !! p = Some m -> wm_tid m = Some (fin_to_nat c) ->
    wm_ak m = WCplain -> ¬ wpublished log (wm_tid m) p ->
    is_Some (msg_byte m a) ->
    forall c' : CPU, c' <> c -> (coh (wsf c') a < S p)%nat.

(** The global statement IS the per-hart one at every hart — the two are
    the same quantifier prefix, reassociated.  Both directions are used:
    [_hart] when a rule focuses one hart, [_intro] when it reassembles. *)
Lemma no_violation_hart log wsf c' :
  no_violation log wsf -> nv_hart log c' (wsf c').
Proof. intros H a p m c Hp Ht Hk Hnp Hs Hne. exact (H p m c a Hp Ht Hk Hnp Hs c' Hne). Qed.

Lemma no_violation_intro log wsf :
  (forall c' : CPU, nv_hart log c' (wsf c')) -> no_violation log wsf.
Proof. intros H p m c a Hp Ht Hk Hnp Hs c' Hne. exact (H c' a p m c Hp Ht Hk Hnp Hs Hne). Qed.

(** The empty log violates nothing — [WeakRobust.violation_init]'s twin,
    and the conjunct's boot case. *)
Lemma no_violation_nil wsf : no_violation [] wsf.
Proof. intros p m c a Hp. by rewrite lookup_nil in Hp. Qed.

Lemma nv_hart_nil c' ws : nv_hart [] c' ws.
Proof. intros a p m c Hp. by rewrite lookup_nil in Hp. Qed.

(** Lowering a floor keeps it safe. *)
Lemma nv_byte_mono log c' a n n' :
  nv_byte log c' a n -> (n' <= n)%nat -> nv_byte log c' a n'.
Proof. intros H Hle p m c Hp Ht Hk Hnp Hs Hne. pose proof (H p m c Hp Ht Hk Hnp Hs Hne). lia. Qed.

(* ====================================================================== *)
(** ** 2. The induction algebra

    Everything the per-rule preservation argument needs that is NOT about
    resources.  The resource-backed arm — a load's raising of [coh] at a
    byte it read — is §3. *)

(** *** 2a. APPENDS.  The obligation only ever gets WEAKER along an append:
    publication is monotone ([WeakGhost.wpublished_app]), so a message that
    is unpublished in the LONGER log was unpublished in the shorter one and
    the old obligation applies verbatim.  What is new is the messages the
    append itself added, and there the floor is below them by
    [WeakMem.ws_bounded]. *)
Lemma nv_byte_app log ms c' a n :
  nv_byte log c' a n -> (n <= length log)%nat -> nv_byte (log ++ ms) c' a n.
Proof.
  intros H Hn p m c Hp Ht Hk Hnp Hs Hne.
  apply lookup_app_Some in Hp as [Hp|[Hge _]].
  - assert (Hnp' : ¬ wpublished log (wm_tid m) p)
      by (intros Hpub; apply Hnp; by apply wpublished_app).
    exact (H p m c Hp Ht Hk Hnp' Hs Hne).
  - lia.
Qed.

Lemma nv_hart_app log ms c' ws :
  nv_hart log c' ws -> ws_bounded ws (length log) -> nv_hart (log ++ ms) c' ws.
Proof.
  intros H (_ & _ & _ & _ & _ & _ & Hcoh & _) a.
  apply (nv_byte_app log ms c' a _ (H a) (Hcoh a)).
Qed.

(** ... and the STEPPING hart's own append, where the floor bound is not
    available (the hart's own [coh] has just been raised to the fresh top)
    and is not needed: every message a hart appends carries ITS OWN tid, so
    the new obligations quantify over [c' ≠ c'] and are vacuous.  This is
    what makes a store free for its own author. *)
Lemma nv_byte_app_own log ms c a n :
  nv_byte log c a n ->
  (forall m, m ∈ ms -> wm_tid m = Some (fin_to_nat c)) ->
  nv_byte (log ++ ms) c a n.
Proof.
  intros H Hown p m c0 Hp Ht Hk Hnp Hs Hne.
  apply lookup_app_Some in Hp as [Hp|[_ Hp]].
  - assert (Hnp' : ¬ wpublished log (wm_tid m) p)
      by (intros Hpub; apply Hnp; by apply wpublished_app).
    exact (H p m c0 Hp Ht Hk Hnp' Hs Hne).
  - exfalso. apply Hne. apply elem_of_list_lookup_2, Hown in Hp.
    rewrite Hp in Ht. by simplify_eq.
Qed.

Lemma nv_hart_app_own log ms c ws :
  nv_hart log c ws ->
  (forall m, m ∈ ms -> wm_tid m = Some (fin_to_nat c)) ->
  nv_hart (log ++ ms) c ws.
Proof. intros H Hown a. exact (nv_byte_app_own log ms c a _ (H a) Hown). Qed.

(** *** 2b. THE FLOOR MOVE.  A hart's [coh] only rises, and only at the
    bytes its step touched; so the whole per-step obligation is "every byte
    whose floor moved is one at which no foreign unpublished [WCplain]
    message lives", which §3 reads off the mover's own C/D/S fragment. *)
Lemma nv_hart_coh_step log c ws ws' :
  nv_hart log c ws ->
  (forall a : Z, (coh ws a < coh ws' a)%nat -> nv_byte log c a (coh ws' a)) ->
  nv_hart log c ws'.
Proof.
  intros H Hmv a. destruct (decide (coh ws a < coh ws' a)%nat) as [Hlt|Hge].
  - exact (Hmv a Hlt).
  - apply (nv_byte_mono log c a (coh ws a)); [exact (H a)|lia].
Qed.

(** *** 2c. THE REASSEMBLY, in the shape [WeakExec.wp_wrun_step] closes the
    global interpretation at: ONE hart stepped (its cell moved, its
    messages were appended), every other hart's cell is untouched and its
    floors are below the OLD log's top.  This is the exact twin of the
    [ws_bounded] reassembly ([Hbnd2] there) and is meant to be applied the
    same way. *)
Lemma no_violation_step (log ms : list wmsg) (wsf wsf' : CPU -> wstate)
    (c : CPU) :
  no_violation log wsf ->
  (forall c0 : CPU, ws_bounded (wsf c0) (length log)) ->
  (forall m, m ∈ ms -> wm_tid m = Some (fin_to_nat c)) ->
  (forall c0 : CPU, c0 <> c -> wsf' c0 = wsf c0) ->
  nv_hart (log ++ ms) c (wsf' c) ->
  no_violation (log ++ ms) wsf'.
Proof.
  intros Hnv Hbnd Hown Hfr Hc. apply no_violation_intro. intros c0.
  destruct (decide (c0 = c)) as [->|Hne]; [exact Hc|].
  rewrite (Hfr c0 Hne).
  apply (nv_hart_app log ms c0 (wsf c0) (no_violation_hart log wsf c0 Hnv)
           (Hbnd c0)).
Qed.

(** The DEVICE/DMA arm.  [WeakLang.wmsgs_of_map] stamps [wm_tid = Some
    n_disk], which is NOT a hart ([WeakLang.n_disk_not_hart]), so a disk
    append adds no obligation at all and no hart's floor moves: the conjunct
    survives by [nv_hart_app] alone.  (The DMA messages are [WCplain] but
    the disk is not a hart — the surgery's Delta 2, re-keyed by the DMA-tid
    unification.  The lemma itself never inspects [ms]: [nv_hart]'s message
    quantifier is already restricted to hart authors.) *)
Lemma no_violation_dma (log ms : list wmsg) (wsf : CPU -> wstate) :
  no_violation log wsf ->
  (forall c0 : CPU, ws_bounded (wsf c0) (length log)) ->
  no_violation (log ++ ms) wsf.
Proof.
  intros Hnv Hbnd. apply no_violation_intro. intros c0.
  apply (nv_hart_app log ms c0 (wsf c0) (no_violation_hart log wsf c0 Hnv)
           (Hbnd c0)).
Qed.

(* ====================================================================== *)
(** ** 3. THE THREE DISCHARGE ARMS, off the C/D/S invariants

    The whole point of the surgery: at a byte whose state a load's own
    fragment pins, the obligation is VACUOUS — there is no foreign
    unpublished [WCplain] message there to be observed — so the floor may
    move as far as the step likes.

      - CLEAN  ([wcds_clean], what every [wlat_pointsto] carries at every
        fraction): every [WCplain] writer of the byte is published.
      - DIRTY BY ME ([wcds_dirty _ c], the [↦wo] path at [q = 1]): the
        unpublished [WCplain] writers are all mine, and the obligation
        quantifies over authors OTHER than the floor's owner.
      - SYNC ([wcds_sync], the racy window): no [WCplain] writer at all. *)

Lemma nv_byte_clean log c' a n : wcds_clean log a -> nv_byte log c' a n.
Proof.
  intros Hcl p m c Hp Ht Hk Hnp Hs _.
  destruct (Hcl p m (conj Hp (conj Hs Hk))) as [Hn|Hpub].
  - destruct Hn. rewrite Ht. apply tid_is_hart_cpu_intro.
  - by destruct (Hnp Hpub).
Qed.

Lemma nv_byte_dirty log c a n : wcds_dirty log a c -> nv_byte log c a n.
Proof.
  intros Hdi p m c0 Hp Ht Hk Hnp Hs Hne.
  destruct (Hdi p m (conj Hp (conj Hs Hk))) as [Hn|[Hpub|Hc]].
  - destruct Hn. rewrite Ht. apply tid_is_hart_cpu_intro.
  - by destruct (Hnp Hpub).
  - exfalso. apply Hne. rewrite Ht in Hc. by simplify_eq.
Qed.

Lemma nv_byte_sync log c' a n : wcds_sync log a -> nv_byte log c' a n.
Proof. intros Hsy p m c Hp Ht Hk Hnp Hs _. by destruct (Hsy p m (conj Hp (conj Hs Hk))). Qed.

(** The uniform reading: any state a hart may legitimately PRESENT for a
    byte — clean at any fraction, dirty by itself, or sync — discharges the
    obligation at that byte.  [WeakGhost.wown_st] is exactly the first two,
    which is why the owned store/load surface needs no case split. *)
Lemma nv_byte_ok log c a n s :
  wcds_ok log a s -> (s = WClean \/ s = WDirty c \/ s = WSync) ->
  nv_byte log c a n.
Proof.
  intros Hok Hs. destruct Hs as [Hs|[Hs|Hs]]; subst s; simpl in Hok.
  - by apply nv_byte_clean.
  - by apply nv_byte_dirty.
  - by apply nv_byte_sync.
Qed.

(** THE FETCH ARM, and the reason the ~50 register-only leaves pay nothing:
    a byte NO message of the log ever writes carries no obligation at all,
    whatever the floor.  Kernel text is exactly that ([WeakFunnel]'s
    [winstr_unwritten]: [latest_ts = 0] this era), and the fetch is the only
    memory access a register-only instruction makes. *)
Lemma nv_byte_unwritten (log : list wmsg) (c : CPU) (a : Z) (n : nat) :
  latest_ts log a = 0%nat -> nv_byte log c a n.
Proof.
  intros Hlt p m c0 Hp _ _ _ [b Hb] _. exfalso.
  apply (latest_ts_top log a). rewrite Hlt.
  apply (writes_in_log_byte (fun _ => None)). exists (S p).
  apply lookup_lt_Some in Hp as Hlen. split_and!; [lia|lia|].
  exists b. rewrite log_byte_S Hp /=. exact Hb.
Qed.

(** THE BYTE-LEVEL SUMMARY a resource-holder exports.  "Byte [a] carries no
    foreign unpublished [WCplain] message, for ANY hart at ANY floor" — which
    is exactly what a clean fragment, a sync witness, or an unwritten byte
    gives, and exactly what a reassembly site needs per touched byte.  It is
    PURE, so it survives the closing of the invariant the fragment came from
    (the walk's leaf slot is minted this way: the element goes back into
    [WeakKpt]'s invariant, the fact stays). *)
Definition nv_free (log : list wmsg) (a : Z) : Prop :=
  forall (c : CPU) (n : nat), nv_byte log c a n.

(** ... and its HART-INDEXED form, which is what a leaf actually needs (the
    floor whose move it must justify is its own).  Weaker than [nv_free] —
    an OWNED byte is [nv_ok] for its owner but not [nv_free] — and that gap
    is exactly the [WDirty] arm. *)
Definition nv_ok (log : list wmsg) (c : CPU) (a : Z) : Prop :=
  forall n : nat, nv_byte log c a n.

Lemma nv_ok_of_free log c a : nv_free log a -> nv_ok log c a.
Proof. intros H n. apply H. Qed.

Lemma nv_ok_clean log c a : wcds_clean log a -> nv_ok log c a.
Proof. intros H n. by apply nv_byte_clean. Qed.

Lemma nv_ok_dirty log c a : wcds_dirty log a c -> nv_ok log c a.
Proof. intros H n. by apply nv_byte_dirty. Qed.

Lemma nv_ok_sync log c a : wcds_sync log a -> nv_ok log c a.
Proof. intros H n. by apply nv_byte_sync. Qed.

Lemma nv_ok_unwritten log c a : latest_ts log a = 0%nat -> nv_ok log c a.
Proof. intros H n. by apply nv_byte_unwritten. Qed.

Lemma nv_byte_of_ok log c a n : nv_ok log c a -> nv_byte log c a n.
Proof. intros H. apply H. Qed.

Lemma nv_free_clean log a : wcds_clean log a -> nv_free log a.
Proof. intros H c n. by apply nv_byte_clean. Qed.

Lemma nv_free_sync log a : wcds_sync log a -> nv_free log a.
Proof. intros H c n. by apply nv_byte_sync. Qed.

Lemma nv_free_unwritten log a : latest_ts log a = 0%nat -> nv_free log a.
Proof. intros H c n. by apply nv_byte_unwritten. Qed.

Lemma nv_byte_of_free log c a n : nv_free log a -> nv_byte log c a n.
Proof. intros H. apply H. Qed.

(** THE φ PAYMENT OF THE LAZY-UPGRADE ARM (φ-upgrade §1.5).  A byte that is
    still [WDirty c] in the ghost map but whose whole write history [c] has
    PUBLISHED carries no obligation to ANY hart at ANY floor — [no_violation]
    only ever constrains UNPUBLISHED owned stores, and there are none here.

    So the arm does not have to flip the state element first in order to pay:
    the publication evidence pays directly, which is what lets a leaf state
    its [nv_ok] obligation before its ghost section runs.  (After the flip it
    is the ordinary [nv_free_clean], of course — the two agree.) *)
Lemma nv_free_published img log a (c : CPU) (t n : nat) (v : bv 8) :
  latest_val img log a t v -> (t <= n)%nat ->
  wpub_upto log (Some (fin_to_nat c)) n ->
  wcds_dirty log a c -> nv_free log a.
Proof.
  intros Hlat Htn Hpub Hdi. apply nv_free_clean.
  exact (wcds_dirty_flip_pub img log a c t n v Hlat Htn Hpub Hdi).
Qed.

Lemma nv_byte_published img log (c' : CPU) a (m : nat) (c : CPU) (t n : nat)
    (v : bv 8) :
  latest_val img log a t v -> (t <= n)%nat ->
  wpub_upto log (Some (fin_to_nat c)) n ->
  wcds_dirty log a c -> nv_byte log c' a m.
Proof.
  intros Hlat Htn Hpub Hdi.
  exact (nv_free_published img log a c t n v Hlat Htn Hpub Hdi c' m).
Qed.

Lemma nv_ok_published img log (c' : CPU) a (c : CPU) (t n : nat) (v : bv 8) :
  latest_val img log a t v -> (t <= n)%nat ->
  wpub_upto log (Some (fin_to_nat c)) n ->
  wcds_dirty log a c -> nv_ok log c' a.
Proof.
  intros Hlat Htn Hpub Hdi. apply nv_ok_of_free.
  exact (nv_free_published img log a c t n v Hlat Htn Hpub Hdi).
Qed.

(* ====================================================================== *)
(** ** 3. The resources *)

(* ====================================================================== *)
(** ** 0'. THE EXECUTION CONTEXT'S NAME (φ-upgrade §1.6)

    [WeakCtx]'s [CtxId] lives HERE, not there, because the OWNED POINTS-TO is
    indexed by it ([WeakVProp.wpt_own]) and [WeakVProp] sits below [WeakCtx].
    That is the whole reason for the move: Stage 1.6 makes the migration
    upgrade invisible by putting the context's write breadcrumb INSIDE the
    points-to, so the type of contexts has to be visible at the points-to's
    altitude.

    TWO ghost names rather than one.  [ctx_vn] is [WeakCtx]'s view authority
    (an [authR cohUR], the context's [flr] summary); [ctx_wn] is the per-hart
    write watermark this file's §3a'' builds ([authR ctxwrUR]).  They are
    separate [own]s under separate names because Iris allocates a name per
    algebra; pairing them in a record keeps a context ONE value, so nothing
    downstream of [WeakCtx] can tell the difference — [CtxId] stays an opaque
    parameter exactly as its header demands. *)
Record CtxId := CtxNames { ctx_vn : gname; ctx_wn : gname }.

Section resources.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (* ---------------------------------------------------------------- *)
  (** *** 3a. the global write log (mono-list) *)

  Definition wlog_auth (l : list wmsg) : iProp Σ :=
    own weak_log_name (●ML (l : list (leibnizO wmsg))).
  Definition wlog_lb (l : list wmsg) : iProp Σ :=
    own weak_log_name (◯ML (l : list (leibnizO wmsg))).

  Global Instance wlog_lb_persistent l : Persistent (wlog_lb l).
  Proof. rewrite /wlog_lb. apply _. Qed.

  Lemma wlog_snapshot l : wlog_auth l -∗ wlog_auth l ∗ wlog_lb l.
  Proof.
    rewrite /wlog_auth /wlog_lb -own_op -mono_list_auth_lb_op. iIntros "$".
  Qed.

  Lemma wlog_valid l l' : wlog_auth l -∗ wlog_lb l' -∗ ⌜l' `prefix_of` l⌝.
  Proof.
    rewrite /wlog_auth /wlog_lb. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  Lemma wlog_update l ms : wlog_auth l ==∗ wlog_auth (l ++ ms).
  Proof.
    rewrite /wlog_auth. iIntros "Ha". iApply (own_update with "Ha").
    apply mono_list_update. by apply prefix_app_r.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3a'. THE PUBLICATION-FLOOR TOKEN (φ-upgrade §1.5)

      [pub_floor c n] — "hart [c] has published everything at or below [n]",
      as a PERSISTENT resource.

      SPELLING, and why it is not the [WeakViewMono] [w_pub] mono_nat.  The
      semantics wanted is a lower bound on the publication watermark, and
      [WeakViewMono.ws_scal_lb]'s sixth component is exactly that shape — but
      (a) its AUTHORITY is not threaded anywhere (the [weak_view_name] field
      was deleted when [WeakCtx]'s context-indexed discipline landed, see §1's
      class comment), and (b) even with the authority back, the arm needs the
      CONVERSE of [WeakViolation.wpublished_w_pub] — "[w_pub ≥ S p] implies
      [p] is published" — which is not an available machine invariant and
      would have to be added to the state interpretation.  The LOG is already
      a mono-list with a persistent lower bound, and publication is a LOG
      predicate ([wpublished]), so the token is spelled there: a snapshot of a
      prefix in which [c] has already released.  Nothing new is wired, and the
      arm reads the fact it actually needs off it directly.  The [w_pub]
      reading is still recoverable — [WeakViolation.wpub_upto_w_pub] is the
      one-line bridge — it is simply not the load-bearing spelling. *)
  (** The HART-INDEX-KEYED spelling is the primitive one: [WeakCtx]'s
      migration invariant is a map over hart indices, so the entry it stores
      has to be statable at a bare [nat]. *)
  Definition pub_floorn (k n : nat) : iProp Σ :=
    (∃ l : list wmsg, wlog_lb l ∗ ⌜wpub_upto l (Some k) n⌝)%I.

  Definition pub_floor (c : CPU) (n : nat) : iProp Σ :=
    pub_floorn (fin_to_nat c) n.

  Global Instance pub_floorn_persistent k n : Persistent (pub_floorn k n).
  Proof. rewrite /pub_floorn. apply _. Qed.
  Global Instance pub_floorn_timeless k n : Timeless (pub_floorn k n).
  Proof. rewrite /pub_floorn /wlog_lb. apply _. Qed.
  Global Instance pub_floor_persistent c n : Persistent (pub_floor c n).
  Proof. rewrite /pub_floor. apply _. Qed.
  Global Instance pub_floor_timeless c n : Timeless (pub_floor c n).
  Proof. rewrite /pub_floor. apply _. Qed.

  (** AGREEMENT: what the token says about the CURRENT log.  One
      [wlog_valid] plus the prefix-monotonicity of [wpub_upto]. *)
  Lemma pub_floor_agree log c n :
    wlog_auth log -∗ pub_floor c n -∗ ⌜wpub_upto log (Some (fin_to_nat c)) n⌝.
  Proof.
    iIntros "Ha [%l [Hlb %Hp]]".
    iDestruct (wlog_valid with "Ha Hlb") as %Hpre.
    iPureIntro. exact (wpub_upto_prefix l log _ n Hpre Hp).
  Qed.

  (** MINTING, at the RELEASE/HANDOFF STORE's own ghost section: the message
      the step appended is [c]'s and release-class, and it sits at the log's
      fresh top — so it covers EVERY prior position at once.  This is the only
      site that mints, and it needs nothing but the log authority the store
      leaf already updates. *)
  Lemma pub_floor_mint (log : list wmsg) (mrel : wmsg) (c : CPU) :
    wm_tid mrel = Some (fin_to_nat c) -> wm_ak mrel = WCrel ->
    wlog_auth (log ++ [mrel]) -∗
    wlog_auth (log ++ [mrel]) ∗ pub_floor c (S (length log)).
  Proof.
    intros Ht Hk. iIntros "Ha".
    iDestruct (wlog_snapshot with "Ha") as "[$ #Hlb]".
    iExists (log ++ [mrel])%list. iFrame "Hlb". iPureIntro.
    by apply wpub_upto_rel.
  Qed.

  (** A floor may always be LOWERED. *)
  Lemma pub_floor_le c n n' : (n' <= n)%nat -> pub_floor c n -∗ pub_floor c n'.
  Proof.
    iIntros (Hle) "[%l [Hlb %Hp]]". iExists l. iFrame "Hlb". iPureIntro.
    by eapply wpub_upto_mono.
  Qed.

  (** THE VIEW-INDEXED FLOOR (φ-upgrade §1.5).  "Hart [c] has published
      everything the view [V] can see."  Stated over a VIEW rather than a
      position because that is the shape an owned points-to already carries:
      its receipt [⊒(view_byte a t)] read at any index [V] IS [t ≤ flr V a],
      so a token about [V] discharges the timestamp side condition by
      construction and no leaf ever has to name a timestamp. *)
  Definition pub_covers_view (c : CPU) (V : view) : iProp Σ :=
    (∃ n : nat, pub_floor c n ∗ ⌜V ⊑ view_scl n⌝)%I.

  Global Instance pub_covers_view_persistent c V :
    Persistent (pub_covers_view c V).
  Proof. rewrite /pub_covers_view. apply _. Qed.
  Global Instance pub_covers_view_timeless c V :
    Timeless (pub_covers_view c V).
  Proof. rewrite /pub_covers_view. apply _. Qed.

  Lemma pub_covers_view_intro c V n :
    V ⊑ view_scl n -> pub_floor c n -∗ pub_covers_view c V.
  Proof. iIntros (Hle) "H". iExists n. by iFrame "H". Qed.

  Lemma pub_covers_view_mono c V V' :
    V' ⊑ V -> pub_covers_view c V -∗ pub_covers_view c V'.
  Proof.
    iIntros (Hle) "[%n [H %Hn]]". iExists n. iFrame "H". iPureIntro.
    by etrans.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3a''. THE CONTEXT'S WRITE BREADCRUMB, AND THE MIGRATION INVARIANT
      (φ-upgrade §1.6 — what makes the lazy upgrade INVISIBLE)

      Stage 1.5 left the upgrade as a lemma the CALLER applied at the first
      touch of a dirty byte after a migration.  That is unacceptable
      ergonomics: an access site's script must not depend on whether the
      thread has been rescheduled since it last wrote the byte.  The fix is to
      move the evidence INTO the resource and the case split INTO the leaf,
      and the evidence is this pair:

        [ctx_wrote ξ c V]  — PERSISTENT.  "context [ξ] wrote, through hart
                             [c], at or below [V]."  Minted by the owned store
                             leaf, carried by [WeakVProp.wpt_own]'s dirty
                             disjunct, and never mentioned by a caller.
        [ctx_migr ξ c]     — the SCHEDULER-SIDE authority, riding in
                             [WeakCtx.wrunning]: "[ξ] is running on hart [c],
                             and every OTHER hart it has ever written through
                             has published what it wrote."

      Their product is the whole of Stage 1.6: given a breadcrumb for a hart
      that is not the current one, the invariant hands back
      [pub_covers_view], which is exactly Stage 1.5's evidence — now produced
      inside the leaf rather than by the caller.

      THE ALGEBRA IS A MAX PER HART.  The breadcrumb has to be persistent
      (points-to facts are duplicated, framed and re-proved freely) and has to
      survive the context writing more, so it is a LOWER bound on a monotone
      quantity: the highest position [ξ] has written through [c].  A
      [gmap nat max_nat] auth gives that in one [own], with the fragment
      core-id hence persistent for free.

      WHY THE LIVE HART IS AN EXCEPTION AND NOT A HOLE.  The entry for the
      hart [ξ] is running on is deliberately NOT covered — those writes are
      the thread's own outstanding dirty bytes, and the leaf never needs
      coverage for them (it takes the ordinary own-dirty path instead).  What
      every entry carries instead is the POSITION BOUND [wlog_ts_ok], which is
      what lets the PARK discharge the exception: a release at the log's fresh
      top publishes every position at or below the log's length, so it covers
      the live entry without knowing which bytes, or how many, the thread
      dirtied. *)

  (** "position [n] is IN the log" — the bound a store's own fresh top
      satisfies (its message is the log's last, so [n] is the post-log's
      length), and the one the park spends against the floor its release
      mints (which is that same number). *)
  Definition wlog_ts_ok (n : nat) : iProp Σ :=
    (∃ l : list wmsg, wlog_lb l ∗ ⌜(n <= length l)%nat⌝)%I.

  Global Instance wlog_ts_ok_persistent n : Persistent (wlog_ts_ok n).
  Proof. rewrite /wlog_ts_ok. apply _. Qed.
  Global Instance wlog_ts_ok_timeless n : Timeless (wlog_ts_ok n).
  Proof. rewrite /wlog_ts_ok /wlog_lb. apply _. Qed.

  Lemma wlog_ts_ok_get (log : list wmsg) (n : nat) :
    (n <= length log)%nat -> wlog_auth log -∗ wlog_auth log ∗ wlog_ts_ok n.
  Proof.
    iIntros (Hn) "Ha". iDestruct (wlog_snapshot with "Ha") as "[$ #Hlb]".
    iExists log. by iFrame "Hlb".
  Qed.

  Lemma wlog_ts_ok_bound (log : list wmsg) (n : nat) :
    wlog_auth log -∗ wlog_ts_ok n -∗ ⌜(n <= length log)%nat⌝.
  Proof.
    iIntros "Ha [%l [Hlb %Hn]]".
    iDestruct (wlog_valid with "Ha Hlb") as %Hpre.
    iPureIntro. apply prefix_length in Hpre. lia.
  Qed.

  (** ... and a published floor is bounded too, so EVERY entry of the map is
      (this is what makes the park's discharge uniform). *)
  Lemma pub_floorn_bound (log : list wmsg) (k n : nat) :
    wlog_auth log -∗ pub_floorn k n -∗ ⌜(n <= length log)%nat⌝.
  Proof.
    iIntros "Ha [%l [Hlb %Hp]]".
    iDestruct (wlog_valid with "Ha Hlb") as %Hpre.
    iPureIntro. apply prefix_length in Hpre.
    pose proof (wpub_upto_len l _ n Hp). lia.
  Qed.

  (** The map, as an element of the algebra.  Spelled through a named
      coercion rather than an inline [fmap] so that the [gmap] functor is
      pinned by the result type. *)
  Definition ctxwr_of (m : gmap nat nat) : gmap nat max_nat :=
    (fun n : nat => MaxNat n) <$> m.

  Definition ctx_wr_auth (ξ : CtxId) (m : gmap nat nat) : iProp Σ :=
    own (ctx_wn ξ) (● (ctxwr_of m)).

  Definition ctx_wrote_pos (ξ : CtxId) (c : CPU) (t : nat) : iProp Σ :=
    own (ctx_wn ξ) (◯ {[ fin_to_nat c := MaxNat t ]}).

  Global Instance ctx_wrote_pos_persistent ξ c t :
    Persistent (ctx_wrote_pos ξ c t).
  Proof. rewrite /ctx_wrote_pos. apply _. Qed.
  Global Instance ctx_wrote_pos_timeless ξ c t :
    Timeless (ctx_wrote_pos ξ c t).
  Proof. rewrite /ctx_wrote_pos. apply _. Qed.

  (** The VIEW-indexed breadcrumb, for the same reason [pub_covers_view] is
      view-indexed: the points-to's own receipt is a view, so nothing has to
      name a timestamp. *)
  Definition ctx_wrote (ξ : CtxId) (c : CPU) (V : view) : iProp Σ :=
    (∃ t : nat, ctx_wrote_pos ξ c t ∗ ⌜V ⊑ view_scl t⌝)%I.

  Global Instance ctx_wrote_persistent ξ c V : Persistent (ctx_wrote ξ c V).
  Proof. rewrite /ctx_wrote. apply _. Qed.
  Global Instance ctx_wrote_timeless ξ c V : Timeless (ctx_wrote ξ c V).
  Proof. rewrite /ctx_wrote. apply _. Qed.

  Lemma ctx_wrote_intro ξ c t :
    ctx_wrote_pos ξ c t -∗ ctx_wrote ξ c (view_scl t).
  Proof. iIntros "H". iExists t. by iFrame "H". Qed.

  Lemma ctx_wrote_byte ξ c a t :
    ctx_wrote_pos ξ c t -∗ ctx_wrote ξ c (view_byte a t).
  Proof.
    iIntros "H". iExists t. iFrame "H". iPureIntro. intros a'.
    rewrite flr_scl_eq. destruct (decide (a' = a)) as [->|Hne].
    - rewrite flr_byte_eq. lia.
    - rewrite flr_byte_ne //. lia.
  Qed.

  Lemma ctx_wrote_mono ξ c V V' :
    V' ⊑ V -> ctx_wrote ξ c V -∗ ctx_wrote ξ c V'.
  Proof.
    iIntros (Hle) "[%t [H %Ht]]". iExists t. iFrame "H". iPureIntro.
    by etrans.
  Qed.

  (** THE INVARIANT, as a resource: the authority plus, per hart, either "this
      is the hart I am running on" or full publication coverage — and, either
      way, the position bound. *)
  Definition ctx_migr (ξ : CtxId) (c : CPU) : iProp Σ :=
    (∃ m : gmap nat nat, ctx_wr_auth ξ m ∗
       [∗ map] k ↦ n ∈ m,
         wlog_ts_ok n ∗ (⌜k = fin_to_nat c⌝ ∨ pub_floorn k n))%I.

  (** THE PARKED FORM: EVERY entry covered, no live hart named.  This is what
      the migration handoff produces and what the resume consumes — and the
      reason the resume needs no memory evidence: an all-covered map satisfies
      the invariant at WHATEVER hart the scheduler picks. *)
  Definition ctx_migr_all (ξ : CtxId) : iProp Σ :=
    (∃ m : gmap nat nat, ctx_wr_auth ξ m ∗
       [∗ map] k ↦ n ∈ m, wlog_ts_ok n ∗ pub_floorn k n)%I.

  Lemma ctx_migr_all_run ξ (c : CPU) : ctx_migr_all ξ -∗ ctx_migr ξ c.
  Proof.
    iIntros "[%m [Ha #Hall]]". iExists m. iFrame "Ha".
    iApply (big_sepM_impl with "Hall"). iIntros "!>" (k n _) "[$ #Hp]".
    by iRight.
  Qed.

  Lemma ctx_wr_alloc : ⊢ |==> ∃ γ : gname, own γ (● (∅ : ctxwrUR)).
  Proof.
    iMod (own_alloc (● (∅ : ctxwrUR))) as (γ) "H".
    { by apply auth_auth_valid. }
    by iExists γ.
  Qed.

  Lemma ctx_migr_empty ξ c : own (ctx_wn ξ) (● (∅ : ctxwrUR)) -∗ ctx_migr ξ c.
  Proof.
    iIntros "H". iExists ∅. rewrite /ctx_wr_auth /ctxwr_of fmap_empty. iFrame "H".
    by rewrite big_sepM_empty.
  Qed.

  (** SPENDING A BREADCRUMB — the whole point of the stage.  A points-to whose
      dirty author is a hart the context is NOT running on yields Stage 1.5's
      publication evidence, with no caller involvement whatsoever. *)
  Lemma ctx_migr_pub ξ (c c' : CPU) (V : view) :
    c' <> c ->
    ctx_migr ξ c -∗ ctx_wrote ξ c' V -∗ pub_covers_view c' V.
  Proof.
    iIntros (Hne) "[%m [Ha #Hall]] [%t [Hf %Ht]]".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    assert (Hm : exists n, m !! fin_to_nat c' = Some n /\ (t <= n)%nat).
    { apply auth_both_valid_discrete in Hv as [Hincl _].
      apply singleton_included_l in Hincl as (y & Hy & Hle).
      rewrite /ctxwr_of lookup_fmap in Hy.
      destruct (m !! fin_to_nat c') as [n|] eqn:Hn; [|by inversion Hy].
      exists n. split; [done|]. simpl in Hy.
      apply (inj Some) in Hy. rewrite -Hy in Hle.
      apply Some_included_total, max_nat_included in Hle. exact Hle. }
    destruct Hm as (n & Hn & Htn).
    iDestruct (big_sepM_lookup _ _ _ _ Hn with "Hall") as "[_ [%Hk|Hpf]]".
    { exfalso. apply Hne. by apply (inj fin_to_nat). }
    iApply (pub_covers_view_intro c' V n); [|iExact "Hpf"].
    etrans; [exact Ht|]. intros a. rewrite !flr_scl_eq. exact Htn.
  Qed.

  (** The algebraic step behind the mint: raising one key of the map IS
      op-ing the singleton in. *)
  Lemma ctxwr_fmap_op (m : gmap nat nat) (k t : nat) :
    ctxwr_of (<[k := Nat.max t (default 0%nat (m !! k))]> m)
    ≡ ({[k := MaxNat t]} : ctxwrUR) ⋅ ctxwr_of m.
  Proof.
    intros i. rewrite /ctxwr_of lookup_op !lookup_fmap.
    destruct (decide (i = k)) as [->|Hne].
    - rewrite lookup_insert lookup_singleton /=.
      destruct (m !! k) as [n|]; simpl.
      + rewrite -Some_op max_nat_op //.
      + rewrite Nat.max_0_r. by rewrite right_id.
    - rewrite lookup_insert_ne // lookup_singleton_ne //.
      by destruct (m !! i).
  Qed.

  (** MINTING, at the owned store leaf: the store's own message sits at the
      log's fresh top, so the position bound is the log's length and nothing
      else — no view arithmetic, no knowledge of any other byte. *)
  Lemma ctx_migr_mint ξ (c : CPU) (log : list wmsg) (t : nat) :
    (t <= length log)%nat ->
    wlog_auth log -∗ ctx_migr ξ c ==∗
    wlog_auth log ∗ ctx_migr ξ c ∗ ctx_wrote_pos ξ c t.
  Proof.
    iIntros (Ht) "Hlog [%m [Ha #Hall]]".
    set (k := fin_to_nat c).
    set (n' := Nat.max t (default 0%nat (m !! k))).
    (* the old entry is bounded too, so the raised one still is *)
    iAssert (⌜(n' <= length log)%nat⌝)%I as %Hn'.
    { rewrite /n'. destruct (m !! k) as [n|] eqn:Hn; simpl; [|by iPureIntro; lia].
      iDestruct (big_sepM_lookup _ _ _ _ Hn with "Hall") as "[Hts _]".
      iDestruct (wlog_ts_ok_bound with "Hlog Hts") as %Hb.
      iPureIntro. lia. }
    iDestruct (wlog_ts_ok_get log n' Hn' with "Hlog") as "[Hlog #Hts']".
    iMod (own_update _ _ (● (ctxwr_of (<[k := n']> m))
                          ⋅ ◯ ({[k := MaxNat t]} : ctxwrUR)) with "Ha")
      as "[Ha #Hf]".
    { apply auth_update_alloc.
      rewrite local_update_unital_discrete => z _ Heq. split.
      - intros i. rewrite /ctxwr_of lookup_fmap. by destruct (_ !! i).
      - rewrite left_id in Heq. rewrite /n' ctxwr_fmap_op -Heq //. }
    iModIntro. iFrame "Hlog Hf". iExists (<[k := n']> m). iFrame "Ha".
    iApply big_sepM_insert_2; [|iExact "Hall"]. iFrame "Hts'". by iLeft.
  Qed.

  (** THE PARK.  The migration handoff's release publishes every position at
      or below the log's length, and every entry of the map is at or below
      that — so the live-hart exception disappears, every entry becomes
      covered, and the invariant re-forms at WHATEVER hart the context is
      about to resume on.  That last quantifier is why the resume side needs
      no memory evidence at all. *)
  Lemma ctx_migr_park ξ (c : CPU) (log : list wmsg) (N : nat) :
    (length log <= N)%nat ->
    wlog_auth log -∗ pub_floor c N -∗ ctx_migr ξ c -∗
    wlog_auth log ∗ ctx_migr_all ξ.
  Proof.
    iIntros (HN) "Hlog #Hpf [%m [Ha #Hall]]".
    iAssert (⌜forall k n, m !! k = Some n -> (n <= length log)%nat⌝)%I
      as %Hbnd.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_forall. iIntros (n).
      rewrite bi.pure_impl. iIntros (Hkn).
      iDestruct (big_sepM_lookup _ _ _ _ Hkn with "Hall") as "[Hts _]".
      by iApply (wlog_ts_ok_bound with "Hlog Hts"). }
    iFrame "Hlog". iExists m. iFrame "Ha".
    iApply (big_sepM_impl with "Hall"). iIntros "!>" (k n Hkn) "[$ [%Hk|#Hp]]".
    - subst k. rewrite /pub_floor.
      iApply (pub_floor_le c N n); [apply Hbnd in Hkn; lia|].
      iExact "Hpf".
    - iExact "Hp".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3b. the per-byte latest-write map (the BASE points-to) *)

  (** THE VALUE ELEMENT — what [wlat_pointsto] used to BE, verbatim.  It is
      now one half of the points-to; the other half is the C/D/S state. *)
  Definition wlat_elem (a : Z) (dq : dfrac) (t : nat) (v : bv 8) : iProp Σ :=
    ghost_map_elem weak_lat_name a dq (t, v).

  (** THE STATE ELEMENTS. *)
  Definition wcds_el (a : Z) (dq : dfrac) (s : wcds) : iProp Σ :=
    ghost_map_elem weak_cds_name a dq s.

  Definition wclean (a : Z) (dq : dfrac) : iProp Σ := wcds_el a dq WClean.
  Definition wdirty (c : CPU) (a : Z) : iProp Σ :=
    wcds_el a (DfracOwn 1) (WDirty c).

  (** The PERSISTENT sync witness.  It pins no value, so a sync byte stays
      writable; and it is [DfracDiscarded], so it is INCOMPATIBLE with the
      full-fraction state element every owned store consumes — which is
      exactly the "a sync byte is never plain-written" side condition, paid
      for by the algebra rather than by a premise on every store. *)
  Definition sync_byte (a : Z) : iProp Σ := wcds_el a DfracDiscarded WSync.

  Global Instance sync_byte_persistent a : Persistent (sync_byte a).
  Proof. rewrite /sync_byte /wcds_el. apply _. Qed.

  (** A WHOLE ACCESS WINDOW is sync — the shape the racy load rules take as
      a premise (φ-upgrade, deliverable A).  Persistent, so threading it
      costs a caller nothing but the obligation to have minted it. *)
  Definition sync_win (a : Arch.pa) (n : N) : iProp Σ :=
    ([∗ list] j ∈ seq 0 (N.to_nat n), sync_byte (acc_addr a j))%I.

  Global Instance sync_win_persistent a n : Persistent (sync_win a n).
  Proof. rewrite /sync_win. apply _. Qed.

  Lemma sync_win_byte (a : Arch.pa) (n : N) (j : nat) :
    (j < N.to_nat n)%nat -> sync_win a n -∗ sync_byte (acc_addr a j).
  Proof.
    intros Hj. rewrite /sync_win.
    iIntros "H". iApply (big_sepL_lookup _ _ j j with "H").
    by rewrite lookup_seq_lt.
  Qed.

  (** The four-byte constructor, which is the only width any racy site in
      this tree uses (the [started] flag). *)
  Lemma sync_win4 (a : Arch.pa) :
    sync_byte (acc_addr a 0) -∗ sync_byte (acc_addr a 1) -∗
    sync_byte (acc_addr a 2) -∗ sync_byte (acc_addr a 3) -∗ sync_win a 4.
  Proof.
    iIntros "#H0 #H1 #H2 #H3". rewrite /sync_win /=. iFrame "H0 H1 H2 H3".
  Qed.
  Global Instance wcds_el_timeless a dq s : Timeless (wcds_el a dq s).
  Proof. rewrite /wcds_el. apply _. Qed.

  (** THE OWNED STATE: clean, or dirty by THIS hart.  The [∃] is what makes
      the surface absorb both, so that a store's postcondition needs no case
      split at any call site. *)
  Definition wown_st (c : CPU) (a : Z) : iProp Σ :=
    (∃ s : wcds, wcds_el a (DfracOwn 1) s ∗ ⌜s = WClean \/ s = WDirty c⌝)%I.

  Global Instance wown_st_timeless c a : Timeless (wown_st c a).
  Proof. rewrite /wown_st. apply _. Qed.

  Lemma wclean_own_st c a : wclean a (DfracOwn 1) -∗ wown_st c a.
  Proof. iIntros "H". iExists WClean. iFrame "H". by iLeft. Qed.

  Lemma wdirty_own_st c a : wdirty c a -∗ wown_st c a.
  Proof. iIntros "H". iExists (WDirty c). iFrame "H". by iRight. Qed.

  (** A full-fraction state element and a sync witness cannot coexist. *)
  Lemma wcds_el_sync_excl a s : wcds_el a (DfracOwn 1) s -∗ sync_byte a -∗ False.
  Proof.
    rewrite /wcds_el /sync_byte. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[? _].
  Qed.

  (** THE BASE POINTS-TO: the value element PLUS the clean state, at the same
      fraction.  Every existing statement that mentions [wlat_pointsto] keeps
      its exact meaning — including the [DfracDiscarded] read-only form, which
      is clean forever and blocks stores. *)
  Definition wlat_pointsto (a : Z) (dq : dfrac) (t : nat) (v : bv 8) : iProp Σ :=
    (wlat_elem a dq t v ∗ wclean a dq)%I.

  Lemma wlat_pointsto_elem a dq t v : wlat_pointsto a dq t v -∗ wlat_elem a dq t v.
  Proof. by iIntros "[$ _]". Qed.

  Definition wlat_interp (img : _) (log : list wmsg) : iProp Σ :=
    (∃ m mc, ghost_map_auth weak_lat_name 1 m ∗ ⌜wlat_agree (img_z img) log m⌝ ∗
             ghost_map_auth weak_cds_name 1 mc ∗ ⌜wcds_agree log mc⌝)%I.

  (** THE READ BRIDGE: my element IS the latest write.  This is what an M2
      load leaf turns into "every admissible timestamp returns [v]".  Stated
      over the bare value element, so that the OWNED (possibly dirty) form
      reads through it too. *)
  Lemma wlat_lookup_elem img log a dq t v :
    wlat_interp img log -∗ wlat_elem a dq t v -∗
    ⌜latest_val (img_z img) log a t v⌝.
  Proof.
    iIntros "Hi He". iDestruct "Hi" as (m mc) "(Hauth & %Hag & _ & _)".
    iDestruct (ghost_map_lookup with "Hauth He") as %Hlk.
    iPureIntro. exact (Hag a (t, v) Hlk).
  Qed.

  Lemma wlat_lookup img log a dq t v :
    wlat_interp img log -∗ wlat_pointsto a dq t v -∗
    ⌜latest_val (img_z img) log a t v⌝.
  Proof.
    iIntros "Hi [He _]". by iApply (wlat_lookup_elem with "Hi He").
  Qed.

  (** The C/D/S lookup: an owned state element is accurate at the log. *)
  Lemma wcds_lookup img log a dq s :
    wlat_interp img log -∗ wcds_el a dq s -∗ ⌜wcds_ok log a s⌝.
  Proof.
    iIntros "Hi He". iDestruct "Hi" as (m mc) "(_ & _ & Hauth & %Hag)".
    iDestruct (ghost_map_lookup with "Hauth He") as %Hlk.
    iPureIntro. exact (Hag a s Hlk).
  Qed.

  Lemma wown_st_lookup (c : CPU) a mc :
    ghost_map_auth weak_cds_name 1 mc -∗ wown_st c a -∗
    ⌜exists s, mc !! a = Some s /\ (s = WClean \/ s = WDirty c)⌝.
  Proof.
    iIntros "Ha Hs". iDestruct "Hs" as (s) "[Hel %Hs]".
    iDestruct (ghost_map_lookup with "Ha Hel") as %Hlk.
    iPureIntro. by exists s.
  Qed.

  (** SYNC-PURITY, at the surface: a sync byte carries no owned store. *)
  Lemma sync_byte_no_plain img log a :
    wlat_interp img log -∗ sync_byte a -∗ ⌜wcds_sync log a⌝.
  Proof. iIntros "Hi #Hs". by iApply (wcds_lookup with "Hi Hs"). Qed.

  (** The ghost readings of the three arms.  Each is one [wcds_lookup]. *)
  Lemma nv_byte_of_clean img log c a dq n :
    wlat_interp img log -∗ wclean a dq -∗ ⌜nv_byte log c a n⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. by apply nv_byte_clean.
  Qed.

  Lemma nv_byte_of_pointsto img log c a dq t v n :
    wlat_interp img log -∗ wlat_pointsto a dq t v -∗ ⌜nv_byte log c a n⌝.
  Proof.
    iIntros "Hi [_ He]". by iApply (nv_byte_of_clean with "Hi He").
  Qed.

  Lemma nv_byte_of_own_st img log c a n :
    wlat_interp img log -∗ wown_st c a -∗ ⌜nv_byte log c a n⌝.
  Proof.
    iIntros "Hi He". iDestruct "He" as (s) "[Hel %Hs]".
    iDestruct (wcds_lookup with "Hi Hel") as %Hok.
    iPureIntro. apply (nv_byte_ok log c a n s Hok). destruct Hs; auto.
  Qed.

  Lemma nv_byte_of_sync img log c a n :
    wlat_interp img log -∗ sync_byte a -∗ ⌜nv_byte log c a n⌝.
  Proof.
    iIntros "Hi #He". iDestruct (sync_byte_no_plain with "Hi He") as %Hsy.
    iPureIntro. by apply nv_byte_sync.
  Qed.

  (** The [nv_free] forms — what a site EXPORTS when it is about to give the
      fragment back (the pure fact outlives the element). *)
  Lemma nv_free_of_clean img log a dq :
    wlat_interp img log -∗ wclean a dq -∗ ⌜nv_free log a⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. by apply nv_free_clean.
  Qed.

  Lemma nv_free_of_pointsto img log a dq t v :
    wlat_interp img log -∗ wlat_pointsto a dq t v -∗ ⌜nv_free log a⌝.
  Proof. iIntros "Hi [_ He]". by iApply (nv_free_of_clean with "Hi He"). Qed.

  Lemma nv_free_of_sync img log a :
    wlat_interp img log -∗ sync_byte a -∗ ⌜nv_free log a⌝.
  Proof.
    iIntros "Hi #He". iDestruct (sync_byte_no_plain with "Hi He") as %Hsy.
    iPureIntro. by apply nv_free_sync.
  Qed.

  (** The hart-indexed readings.  [wown_st] — what a plain store consumes and
      produces — pays through the [WDirty] arm. *)
  Lemma nv_ok_of_own_st img log c a :
    wlat_interp img log -∗ wown_st c a -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hi He". iDestruct "He" as (s) "[Hel %Hs]".
    iDestruct (wcds_lookup with "Hi Hel") as %Hok.
    iPureIntro. intros n. apply (nv_byte_ok log c a n s Hok).
    destruct Hs; auto.
  Qed.

  Lemma nv_ok_of_pointsto img log c a dq t v :
    wlat_interp img log -∗ wlat_pointsto a dq t v -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hi He". iDestruct (nv_free_of_pointsto with "Hi He") as %H.
    iPureIntro. by apply nv_ok_of_free.
  Qed.

  Lemma nv_ok_of_sync img log c a :
    wlat_interp img log -∗ sync_byte a -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hi #He". iDestruct (nv_free_of_sync with "Hi He") as %H.
    iPureIntro. by apply nv_ok_of_free.
  Qed.


  (** The accessor M2's store leaf uses: take the authority out, update the
      elements of the bytes the store wrote, put it back at the new log. *)
  Lemma wlat_interp_acc img log :
    wlat_interp img log -∗
    ∃ m mc, ghost_map_auth weak_lat_name 1 m ∗ ⌜wlat_agree (img_z img) log m⌝ ∗
            ghost_map_auth weak_cds_name 1 mc ∗ ⌜wcds_agree log mc⌝ ∗
      (∀ m' mc' log', ghost_map_auth weak_lat_name 1 m' -∗
         ⌜wlat_agree (img_z img) log' m'⌝ -∗
         ghost_map_auth weak_cds_name 1 mc' -∗
         ⌜wcds_agree log' mc'⌝ -∗ wlat_interp img log').
  Proof.
    iIntros "Hi". iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    iExists m, mc. iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iSplitR; [iPureIntro; exact Hagc|].
    iIntros (m' mc' log') "Hauth' %Hag' Hc' %Hagc'".
    iExists m', mc'. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3b'. THE D→C FLIP and the S mint

      [wlat_flip] is the ghost half of a RELEASE: once the releasing hart's
      [WCrel] message is the log's last, every byte that hart had dirtied is
      clean — its whole own-store backlog is published.  Note the byte need
      NOT be the one the release wrote: this is what lets a release site flip
      a whole DEPOSIT clean before it egresses. *)
  Lemma wlat_flip img log (mrel : wmsg) (c : CPU) (a : Z) :
    wm_tid mrel = Some (fin_to_nat c) -> wm_ak mrel = WCrel ->
    wlat_interp img (log ++ [mrel]) -∗ wown_st c a ==∗
    wlat_interp img (log ++ [mrel]) ∗ wclean a (DfracOwn 1).
  Proof.
    intros Htid Hk. iIntros "Hi Hs".
    iDestruct "Hs" as (s) "[Hel %Hs]".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    iDestruct (ghost_map_lookup with "Hc Hel") as %Hlk.
    iMod (ghost_map_update WClean with "Hc Hel") as "[Hc Hel]".
    iModIntro. iFrame "Hel". iExists m, (<[a := WClean]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|]. simpl.
    destruct Hs as [-> | ->]; [exact (Hagc a WClean Hlk)|].
    apply (wcds_dirty_flip _ _ c (length log) mrel).
    - rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag.
    - exact Htid.
    - exact Hk.
    - rewrite length_app /=. lia.
    - exact (Hagc a (WDirty c) Hlk).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3b''. THE LAZY UPGRADE — the D→C flip a MIGRATED thread does

      [wlat_flip] is the flip at a release SITE: it needs the releasing hart's
      [WCrel] message to be the log's last, which only that one step has.  A
      thread that parked on hart [c] and resumed on another CPU is arbitrarily
      many messages downstream of its own handoff, so it cannot use it.

      What it uses instead is the FLOOR: [pub_floor c n] says [c] published
      everything below [n], and the element's timestamp [t ≤ n] says the
      byte's whole write history is inside that.  The state element is
      retargeted [WDirty c → WClean] with no premise about the current top at
      all — which is precisely what makes the ownership fact FRAME around the
      yield instead of appearing in its specification.

      Note what it does NOT need: the flipping hart's identity.  The evidence
      is about [c], the author; whoever holds the element may spend it. *)
  Lemma nv_free_of_own_pure img log (c : CPU) (a : Z) (t n : nat) (v : bv 8) :
    (t <= n)%nat -> wpub_upto log (Some (fin_to_nat c)) n ->
    wlat_interp img log -∗
    wlat_elem a (DfracOwn 1) t v -∗ wown_st c a -∗ ⌜nv_free log a⌝.
  Proof.
    intros Htn Hpub. iIntros "Hi Hel Hs".
    iDestruct (wlat_lookup_elem with "Hi Hel") as %Hlat.
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct (wcds_lookup with "Hi Hsel") as %Hok.
    iPureIntro. destruct Hs as [-> | ->]; simpl in Hok.
    - by apply nv_free_clean.
    - exact (nv_free_published (img_z img) log a c t n v Hlat Htn Hpub Hok).
  Qed.

  Lemma nv_free_of_own_pub img log (c : CPU) (a : Z) (t n : nat) (v : bv 8) :
    (t <= n)%nat ->
    wlog_auth log -∗ pub_floor c n -∗ wlat_interp img log -∗
    wlat_elem a (DfracOwn 1) t v -∗ wown_st c a -∗ ⌜nv_free log a⌝.
  Proof.
    intros Htn. iIntros "Hlog #Hpf Hi Hel Hs".
    iDestruct (pub_floor_agree with "Hlog Hpf") as %Hpub.
    iDestruct (wlat_lookup_elem with "Hi Hel") as %Hlat.
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct (wcds_lookup with "Hi Hsel") as %Hok.
    iPureIntro. destruct Hs as [-> | ->]; simpl in Hok.
    - by apply nv_free_clean.
    - exact (nv_free_published (img_z img) log a c t n v Hlat Htn Hpub Hok).
  Qed.

  Lemma wlat_flip_pure img log (c : CPU) (a : Z) (t n : nat) (v : bv 8) :
    (t <= n)%nat -> wpub_upto log (Some (fin_to_nat c)) n ->
    wlat_interp img log -∗ wlat_elem a (DfracOwn 1) t v -∗ wown_st c a ==∗
    wlat_interp img log ∗
    wlat_elem a (DfracOwn 1) t v ∗ wclean a (DfracOwn 1).
  Proof.
    intros Htn Hpub. iIntros "Hi Hel Hs".
    iDestruct (wlat_lookup_elem with "Hi Hel") as %Hlat.
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct (wcds_lookup with "Hi Hsel") as %Hok.
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wcds_el.
    iMod (ghost_map_update WClean with "Hc Hsel") as "[Hc Hsel]".
    iModIntro. iFrame "Hel Hsel".
    iExists mm, (<[a := WClean]> mc). iFrame "Hauth Hc".
    iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|]. simpl.
    destruct Hs as [-> | ->]; simpl in Hok; [exact Hok|].
    exact (wcds_dirty_flip_pub (img_z img) log a c t n v Hlat Htn Hpub Hok).
  Qed.

  Lemma wlat_flip_pub img log (c : CPU) (a : Z) (t n : nat) (v : bv 8) :
    (t <= n)%nat ->
    wlog_auth log -∗ pub_floor c n -∗
    wlat_interp img log -∗ wlat_elem a (DfracOwn 1) t v -∗ wown_st c a ==∗
    wlog_auth log ∗ wlat_interp img log ∗
    wlat_elem a (DfracOwn 1) t v ∗ wclean a (DfracOwn 1).
  Proof.
    intros Htn. iIntros "Hlog #Hpf Hi Hel Hs".
    iDestruct (pub_floor_agree with "Hlog Hpf") as %Hpub.
    iDestruct (wlat_lookup_elem with "Hi Hel") as %Hlat.
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct (wcds_lookup with "Hi Hsel") as %Hok.
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wcds_el.
    iMod (ghost_map_update WClean with "Hc Hsel") as "[Hc Hsel]".
    iModIntro. iFrame "Hlog Hel Hsel".
    iExists mm, (<[a := WClean]> mc). iFrame "Hauth Hc".
    iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|]. simpl.
    destruct Hs as [-> | ->]; simpl in Hok; [exact Hok|].
    exact (wcds_dirty_flip_pub (img_z img) log a c t n v Hlat Htn Hpub Hok).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3b'''. THE CONTEXT-INDEXED OWNED STATE (φ-upgrade §1.6)

      [wown_st c a] says "clean, or dirty by hart [c]", and that is a fact
      about SILICON: it stops being true of the same byte the moment the
      thread is rescheduled.  [wown_ctx ξ a t] is its context-indexed
      successor and the payload of [WeakVProp.wpt_own]:

        clean            — no breadcrumb needed, and no hart is named;
        dirty by [c]     — plus [ctx_wrote ξ c (view_byte a t)], the
                           persistent receipt the store leaf minted.

      NOTHING HERE NAMES THE RUNNING HART.  That is the entire point: the
      assertion is invariant under migration, so it frames across a yield with
      nothing to prove, and the case analysis "is the author the hart I am on
      now?" happens INSIDE the leaf, below the caller's script.

      [wown_ctx_retarget] IS that case analysis.  Given the scheduler's
      migration invariant it hands back an ordinary [wown_st c a] at the
      CURRENT hart — flipping a foreign author's dirty byte clean out of the
      publication coverage the invariant supplies, exactly as Stage 1.5's
      caller-applied [wpt_own_upgrade] did, and otherwise doing nothing at
      all.  Every owned rule is stated over [wown_ctx] and opens with this. *)

  Definition wcds_ob (b : option CPU) : wcds :=
    match b with None => WClean | Some c => WDirty c end.

  Definition ctx_bc (ξ : CtxId) (b : option CPU) (a : Z) (t : nat) : iProp Σ :=
    match b with
    | None => emp
    | Some c => ctx_wrote ξ c (view_byte a t)
    end%I.

  Global Instance ctx_bc_persistent ξ b a t : Persistent (ctx_bc ξ b a t).
  Proof. destruct b; apply _. Qed.

  Definition wown_ctx (ξ : CtxId) (a : Z) (t : nat) : iProp Σ :=
    (∃ b : option CPU, wcds_el a (DfracOwn 1) (wcds_ob b) ∗ ctx_bc ξ b a t)%I.

  Global Instance wown_ctx_timeless ξ a t : Timeless (wown_ctx ξ a t).
  Proof. rewrite /wown_ctx /ctx_bc. apply _. Qed.

  Lemma wown_ctx_of_clean ξ a t :
    wclean a (DfracOwn 1) -∗ wown_ctx ξ a t.
  Proof. iIntros "H". iExists None. by iFrame "H". Qed.

  Lemma wown_ctx_of_dirty ξ (c : CPU) a t :
    wdirty c a -∗ ctx_wrote ξ c (view_byte a t) -∗ wown_ctx ξ a t.
  Proof. iIntros "H #Hw". iExists (Some c). by iFrame "H Hw". Qed.

  (** ... and the form the store rule rebuilds through: an [wown_st] at the
      CURRENT hart plus that hart's fresh breadcrumb is a [wown_ctx].  (The
      breadcrumb is minted unconditionally at a store, because the resulting
      state is [WDirty c] for a plain message and the caller must not have to
      know the message's class.) *)
  Lemma wown_ctx_of_own_st ξ (c : CPU) a t :
    wown_st c a -∗ ctx_wrote ξ c (view_byte a t) -∗ wown_ctx ξ a t.
  Proof.
    iIntros "[%s [Hel %Hs]] #Hw".
    destruct Hs as [-> | ->].
    - iExists None. by iFrame "Hel".
    - iExists (Some c). by iFrame "Hel Hw".
  Qed.

  (** THE RETARGET — the leaf-internal upgrade.  [logA] is the log the CALLER
      holds the authority at, which at a store site is ONE MESSAGE AHEAD of
      the interpretation's; [pub_transfer] is the (trivially discharged)
      statement that the extra message publishes nothing on a foreign hart's
      behalf. *)
  Lemma wown_ctx_retarget ξ (c : CPU) (a : Z) (t : nat) (v : bv 8)
      img (log logA : list wmsg) :
    pub_transfer logA log c ->
    wlog_auth logA -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    wlat_elem a (DfracOwn 1) t v -∗ wown_ctx ξ a t ==∗
    wlog_auth logA ∗ ctx_migr ξ c ∗ wlat_interp img log ∗
    wlat_elem a (DfracOwn 1) t v ∗ wown_st c a.
  Proof.
    intros Htr. iIntros "Hlog Hmg Hi Hel [%b [Hst #Hbc]]".
    destruct b as [c'|]; simpl.
    - destruct (decide (c' = c)) as [->|Hne].
      { iModIntro. iFrame "Hlog Hmg Hi Hel".
        by iApply (wdirty_own_st with "Hst"). }
      (* THE FOREIGN-AUTHOR ARM: the invariant supplies the coverage *)
      iDestruct (ctx_migr_pub ξ c c' (view_byte a t) Hne with "Hmg Hbc")
        as "#[%n [Hpf %Hn]]".
      iDestruct (pub_floor_agree with "Hlog Hpf") as %HpubA.
      assert (Htn : (t <= n)%nat).
      { specialize (Hn a). by rewrite flr_byte_eq flr_scl_eq in Hn. }
      iMod (wlat_flip_pure img log c' a t n v Htn (Htr c' n Hne HpubA)
              with "Hi Hel [Hst]") as "(Hi & Hel & Hcl)".
      { by iApply (wdirty_own_st with "Hst"). }
      iModIntro. iFrame "Hlog Hmg Hi Hel".
      by iApply (wclean_own_st with "Hcl").
    - iModIntro. iFrame "Hlog Hmg Hi Hel".
      by iApply (wclean_own_st with "Hst").
  Qed.

  (** THE φ PAYMENT OF THE SAME CASE SPLIT, with no ghost step: an owned byte
      pays [nv_ok] at the running hart whichever arm it is in — clean and
      own-dirty through [nv_ok_of_own_st]'s reasoning, foreign-dirty because a
      PUBLISHED owned store is not a violation to anybody
      ([nv_free_published]).  A leaf states this where it holds its
      resources, and it is the SAME lemma before and after a migration. *)
  Lemma nv_ok_of_wown_ctx ξ (c : CPU) (a : Z) (t : nat) (v : bv 8)
      img (log logA : list wmsg) :
    pub_transfer logA log c ->
    wlog_auth logA -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    wlat_elem a (DfracOwn 1) t v -∗ wown_ctx ξ a t -∗ ⌜nv_ok log c a⌝.
  Proof.
    intros Htr. iIntros "Hlog Hmg Hi Hel [%b [Hst #Hbc]]".
    destruct b as [c'|]; simpl.
    - destruct (decide (c' = c)) as [->|Hne].
      { iApply (nv_ok_of_own_st with "Hi [Hst]").
        by iApply (wdirty_own_st with "Hst"). }
      iDestruct (ctx_migr_pub ξ c c' (view_byte a t) Hne with "Hmg Hbc")
        as "#[%n [Hpf %Hn]]".
      iDestruct (pub_floor_agree with "Hlog Hpf") as %HpubA.
      assert (Htn : (t <= n)%nat).
      { specialize (Hn a). by rewrite flr_byte_eq flr_scl_eq in Hn. }
      iDestruct (nv_free_of_own_pure img log c' a t n v Htn
                   (Htr c' n Hne HpubA) with "Hi Hel [Hst]") as %Hfree.
      { by iApply (wdirty_own_st with "Hst"). }
      iPureIntro. by apply nv_ok_of_free.
    - iApply (nv_ok_of_own_st with "Hi [Hst]").
      by iApply (wclean_own_st with "Hst").
  Qed.

  (** THE S MINT.  A byte with no owned store in the log — at boot, every
      byte — may be turned sync once and for all, consuming its state element
      and yielding the persistent witness. *)
  Lemma sync_mint img log a s :
    wcds_sync log a ->
    wlat_interp img log -∗ wcds_el a (DfracOwn 1) s ==∗
    wlat_interp img log ∗ sync_byte a.
  Proof.
    intros Hsy. iIntros "Hi Hel".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    iMod (ghost_map_update WSync with "Hc Hel") as "[Hc Hel]".
    iMod (ghost_map_elem_persist with "Hel") as "#Hel".
    iModIntro. iFrame "Hel". iExists m, (<[a := WSync]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. by apply wcds_agree_insert.
  Qed.

  (** At boot the log is empty, so the premise is free. *)
  Lemma sync_mint_nil img a s :
    wlat_interp img [] -∗ wcds_el a (DfracOwn 1) s ==∗
    wlat_interp img [] ∗ sync_byte a.
  Proof.
    apply sync_mint. intros p m (Hp & _). by rewrite lookup_nil in Hp.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c. the per-hart weak state *)

  Definition wws_auth (c : CPU) (ws : wstate) : iProp Σ :=
    ghost_var (weak_ws_name c) (1/2) ws.
  Definition hart_ws (c : CPU) (ws : wstate) : iProp Σ :=
    ghost_var (weak_ws_name c) (1/2) ws.

  Lemma hart_ws_agree c ws ws' : wws_auth c ws -∗ hart_ws c ws' -∗ ⌜ws' = ws⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.

  Lemma hart_ws_update c ws ws' ws'' :
    wws_auth c ws -∗ hart_ws c ws' ==∗ wws_auth c ws'' ∗ hart_ws c ws''.
  Proof. iApply ghost_var_update_halves. Qed.

  Definition wws_interp (f : CPU -> wstate) : iProp Σ :=
    ([∗ set] c ∈ (fin_to_set CPU : gset CPU), wws_auth c (f c))%I.

  (** Focus one hart's cell, with the handle to put an updated one back —
      the [wstate] twin of [RiscvPtsto.gregs_interp_acc], and the reason the
      family is per-hart. *)
  Lemma wws_interp_acc `{CpuId} (f : CPU -> wstate) :
    wws_interp f ⊢ wws_auth cpu_id (f cpu_id) ∗
      (∀ ws', wws_auth cpu_id ws' -∗ wws_interp (<[cpu_id := ws']> f)).
  Proof.
    rewrite /wws_interp. iIntros "H".
    iDestruct (big_sepS_delete _ _ cpu_id with "H") as "[Hcur Hrest]";
      [apply elem_of_fin_to_set|].
    iFrame "Hcur". iIntros (ws') "Hws'".
    iApply (big_sepS_delete _ _ cpu_id); [apply elem_of_fin_to_set|].
    rewrite gws_insert_eq. iFrame "Hws'".
    iApply (big_sepS_mono with "Hrest").
    intros c Hc. apply elem_of_difference in Hc as [_ Hne].
    rewrite gws_insert_ne; [done|].
    intros ->. apply Hne, elem_of_singleton. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c'. THE CLIENT TOKEN: [hart_ws] with its value hidden.

      What boot hands each hart and what [WeakCtx.hart_view_to_run] turns
      into a [wrunning ξ].  Its value is not nameable from outside, which
      is the point: naming it is what forced the [ws]/[ws']/[ws_le] residue
      on every caller.

      IT USED TO CARRY A SECOND CONJUNCT, [ws_auth (weak_view_name c) ws] —
      a monotone shadow of the exact cell, so that a caller could snapshot
      a FLOOR ([hart_view_lb]) without naming the [wstate].  That whole
      discipline is superseded: floors are read at the CONTEXT index now
      ([WeakCtx.ctx_view_lb_get]), the hart-indexed objective layer is
      gone, and the bridge lemma was already dropping the shadow half.  So
      the field, the conjunct, and [hart_view_intro]/[_open]/[_close]/[_lb]
      (which had no callers left) are all deleted. *)
  Definition hart_view (c : CPU) : iProp Σ :=
    (∃ ws : wstate, hart_ws c ws)%I.

  Lemma hart_view_intro c ws : hart_ws c ws -∗ hart_view c.
  Proof. iIntros "H". by iExists ws. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3d. the state interpretations *)

  (** THE SINGLE-ERA PIN (see the header): the machine is powered on and
      running generation 0.  This is the seam where the generation counter /
      registry / era existential of [RiscvPtsto.power_interp] slot in. *)
  Definition wgen_pin (g : wgstate) : Prop :=
    wgpow g = true /\ wggen g = 0%nat.

  (** The GLOBAL state interpretation.  The register/device/log/latest
      conjuncts are the existing tree's, verbatim in shape
      ([RiscvPtsto.era_interp] minus its [gen_heap_interp] and its disk-image
      auth); the rest are the weak-memory ones.

      THE SECOND CONJUNCT is the M2b machine invariant: every view EVERY hart
      holds is a real timestamp of the current log ([WeakMem.ws_bounded]).
      Its POSITION matters — the three device rules of [WeakExec] destruct
      only the FIRST conjunct and pass the rest along as one hypothesis, so
      keeping it second leaves them compiling unchanged.  It is preserved
      across a hart step by [WeakInterp.wrun_ws_bounded] for the stepping
      hart, and by [WeakMem.ws_bounded_mono] + [WeakInterp.wrun_log_app] for
      every other hart. *)
  Definition weak_state_interp (g : wgstate) : iProp Σ :=
    (⌜wgen_pin g⌝ ∗
     ⌜∀ c : CPU, ws_bounded (wgws g c) (length (wglog g))⌝ ∗
     (* THE φ CONJUNCT (violation-freedom).  Position: AFTER [ws_bounded],
        for the same reason [ws_bounded] is second — the three device rules
        of [WeakExec] destruct only the FIRST conjunct and pass the rest
        along as one hypothesis, so anything added here leaves them
        compiling unchanged.  Preserved across a hart step by
        [no_violation_step] (the stepping hart's own messages carry its own
        tid, [WeakInterp.wrun_log_tid]; every other hart's floors are below
        the OLD log's top, [ws_bounded]); across a DMA append by
        [no_violation_dma]. *)
     ⌜no_violation (wglog g) (wgws g)⌝ ∗
     ⌜wlog_wf (wglog g)⌝ ∗
     gregs_interp (wgregs g) ∗
     dev_interp (wgdev g) ∗
     wlog_auth (wglog g) ∗
     wlat_interp (wgimg g) (wglog g) ∗
     wws_interp (wgws g))%I.

  (** ... and ONE HART's view of it, which is what the lifting rule hands to
      its caller: [RiscvPtsto.mstate_interp] with the memory conjunct
      replaced by the log + latest-write pair, plus this hart's weak-state
      cell.  Everything in it is about [σ] alone — including the FIRST
      conjunct, this hart's instance of the M2b view-bound invariant, which
      the lifting rule hands out and takes back at the successor state. *)
  Definition wmstate_interp `{CpuId} (σ : wmstate) : iProp Σ :=
    (⌜ws_bounded σ.(wm_ws) (length σ.(wm_log))⌝ ∗
     (* this hart's instance of the φ conjunct — the twin of the [ws_bounded]
        conjunct above, handed out and taken back at the successor.  It is
        the ONE conjunct a leaf cannot get from the machine: it is paid, per
        byte the step touches, out of the leaf's own C/D/S evidence. *)
     ⌜nv_hart σ.(wm_log) cpu_id σ.(wm_ws)⌝ ∗
     ⌜wlog_wf σ.(wm_log)⌝ ∗
     reg_interp σ.(wm_regs) ∗
     dev_interp σ.(wm_dev) ∗
     wlog_auth σ.(wm_log) ∗
     wlat_interp σ.(wm_img) σ.(wm_log) ∗
     wws_auth cpu_id σ.(wm_ws))%I.

  (** THE φ EXPORT (deliverable D).  A trivial projection now that the
      conjunct is in — and the whole point of the upgrade: whatever the
      Iris proof was for, the state interpretation of ANY reachable
      configuration certifies that no hart's coherence floor has reached a
      foreign agent's unpublished owned store. *)
  Lemma weak_state_interp_export (g : wgstate) :
    weak_state_interp g ⊢ ⌜no_violation (wglog g) (wgws g)⌝.
  Proof. iIntros "(_ & _ & $ & _)". Qed.

End resources.

(* ====================================================================== *)
(** ** 4. The [irisGS] instance

    [state_interp] ignores its step/observation/fork counters exactly as
    [riscv_irisGS] does, and [num_laters_per_step] is 0, so the leaf-facing
    fupd/mask discipline of the SC tree carries over verbatim.

    NOTE (single era): unlike [riscv_irisGS], which is defined over the
    FIXED layer alone so that threads of different generations share one WP
    connective, this instance takes the whole [riscvGS] — the ambient era's
    register and device names appear in [weak_state_interp].  With one era
    that is exactly the same thing; the era existential is what makes the
    difference, and it slots in at [weak_state_interp] (header). *)
Global Program Instance weak_irisGS `{!riscvGS Σ, !weakGS Σ}
    : irisGS weak_riscv_lang Σ := {
  iris_invGS := riscvF_invGS;
  state_interp g _ _ _ := weak_state_interp g;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* ====================================================================== *)
(** ** 5. The Φ-free weak WP

    The weak twin of [RiscvPtsto.wp_triv]: [to_val] is unconditionally
    [None] for every [expr weak_riscv_lang] (the language reuses
    [RiscvLang.mval := Empty_set]), so a WP never inspects its
    postcondition and any two postconditions give provably equivalent WPs.
    [wwp_triv] pins the postcondition to the canonical [True]; the
    notations below drop the [{{ Φ }}] clause, which SC's new [WP e @ E]
    notation (RiscvPtsto) made unparseable in any importing file anyway.

    THE NOTATION IS [WWP], NOT [WP], DELIBERATELY.  [expr weak_riscv_lang]
    and [expr riscv_lang] are both [mexpr] up to conversion, and the weak
    files have [riscvGS] (hence SC's [irisGS riscv_lang]) in scope — so if
    the weak notation reused the [WP] syntax, whichever notation was
    imported LAST would win silently ([-notation-overridden] is on
    project-wide), and a weak statement could elaborate at the WRONG
    LANGUAGE and still compile.  A distinct token makes the language
    visible at every use site, and matches the tree's [wwp_*] naming;
    the [(Loop : expr weak_riscv_lang)] annotations become redundant
    ([wwp_triv]'s argument type pins the language) and are dropped. *)

Lemma wwp_post_irrel `{!riscvGS Σ, !weakGS Σ} s E (e : expr weak_riscv_lang)
    (Φ1 Φ2 : val weak_riscv_lang -> iProp Σ) :
  wp s E e Φ1 ⊢ wp s E e Φ2.
Proof.
  (* [wp_mono]'s [irisGS] instance must be PINNED: TC search may otherwise
     resolve it at [riscv_lang] (both languages' [expr] convert to [mexpr])
     and the conclusion then fails to unify with the weak-instance goal. *)
  iApply (wp_mono (Λ := weak_riscv_lang)). iIntros ([]).
Qed.

Definition wwp_triv `{!riscvGS Σ, !weakGS Σ}
    (E : coPset) (e : expr weak_riscv_lang) : iProp Σ :=
  wp NotStuck E e (fun _ => True%I).

Lemma wwp_triv_eq `{!riscvGS Σ, !weakGS Σ} E (e : expr weak_riscv_lang) Φ :
  wwp_triv E e ⊣⊢ wp NotStuck E e Φ.
Proof. rewrite /wwp_triv. iSplit; iApply wwp_post_irrel. Qed.

Notation "'WWP' e @ E" := (wwp_triv E e%E) (at level 20, e at level 20) : bi_scope.
Notation "'WWP' e" := (wwp_triv ⊤ e%E) (at level 20, e at level 20) : bi_scope.

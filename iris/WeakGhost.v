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
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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

(** THE READ-RECORD ALGEBRA (T2-0′ / F3″).  A protected LOAD leaves a
    persistent RECORD "byte [a] was read, as a byte of this lock's payload,
    at log position [p]" — a monotone list of [(a, p)] pairs, one ghost per
    registered lock.  It is what lets the kill know that the read whose value
    it is chasing happened INSIDE the protected window ([r0 ≤ p]); nothing
    else about a load is exported.

    It is a SEPARATE class rather than a field of [weakGpreS]: the record
    ghost is allocated per lock, by the lock library, and no rule of the
    memory model mentions it — so making it a [weakGS] field would put it in
    the ~50-site state-interpretation reassembly for nothing.  It composes
    exactly as [lockG] does. *)
Notation wprecR := (mono_listR (leibnizO (Z * nat))).

Class wprotG (Σ : gFunctors) := WprotG { wprot_recG :: inG Σ wprecR }.
Definition wprotΣ : gFunctors := #[ GFunctor wprecR ].
Global Instance subG_wprotG Σ : subG wprotΣ Σ -> wprotG Σ.
Proof. solve_inG. Qed.

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
                     condition every store site would have to thread.
      - [WLock base n0] — THE FOURTH STATE (tier-2 T2-0, see
                     [claude-notes/design/weak-memory-tier2-s6.md] §4/§6b):
                     the byte belongs to the REGISTERED LOCK WORD at 4-byte
                     base [base], registered when the log had length [n0].
                     It is a REFINEMENT of [WClean] (see [wcds_lock]): the
                     clean obligation, PLUS the lock word's VALUE PROTOCOL on
                     the post-registration suffix ([wlp_at]).  Exclusive (full
                     fraction), and the only writers are the acquire/release
                     leaves, which alone hold the fragment (it lives inside
                     [WeakLock.wlock_inv]).

                     WHY THE SUFFIX.  A lock word is initialized by
                     [initlock]'s PLAIN store (class [WCplain]) BEFORE it is
                     registered, so an unsuffixed protocol is simply false;
                     [n0] is the length of the log at registration and the
                     protocol quantifies over positions [n0 ≤ p] only.

                     THE HOLDER [h] (T2-0′ / F3′, route-b §4d.3′).  The
                     third index is the lock's CURRENT HOLDER as the pure
                     FOLD [wlp_alt] computes it from the post-registration
                     messages: [None] free, [Some t] held by agent [t].  The
                     fold is what turns the SHAPE protocol ([wlp_at]) into the
                     PAIRING protocol the kill needs — "only the holder
                     releases" — and it is enforced by the three write rules
                     ([wcds_ok_store_lock_acq]/[_fail]/[_rel]), each of which
                     ties the message's AUTHOR to the state.  The tie to the
                     lock's ghost ([WeakLock.wlock_inv]: [h = tid_of st]) is
                     what makes those rules discharge locally at the two
                     leaves.

                     WHY THE CLEAN CONJUNCT.  Everything that holds the lock
                     word's bundle must still pay φ's per-byte obligation
                     ([nv_ok]), and the suffix protocol alone says nothing
                     about the pre-registration history — where [initlock]'s
                     plain store sits.  Registration therefore CONSUMES a
                     clean state and carries it along; every protocol store is
                     non-plain, so clean is preserved for free.

      - [WProt γ base n0 r0 d] — THE FIFTH STATE (tier-2 T2-0′ / F3″, see
                     [claude-notes/design/weak-memory-route-b.md] §4d.3′):
                     the byte is in the PAYLOAD (footprint) of the lock word
                     at [base], whose ghost is [γ] and whose registration
                     point is [n0], and it is PROTECTED from log position
                     [r0] on ([n0 ≤ r0]; the lock library registers both at
                     once, so [r0 = n0] there).  The obligation
                     ([wcds_prot]) is φ's, PLUS the protection clause
                     [wprot_at]: every [WCplain] message at or after [r0]
                     that writes the byte is authored by the lock's HOLDER at
                     that position — the holder being F3′'s fold
                     [wlp_holder_at] evaluated on the lock word's own byte
                     [base] at [n0].  This is `(P)` of route-b §4d.1 F6, and
                     it is what the CS-chained arm of the cycle kill
                     consumes.

                     THE φ HALF AND WHY [d] IS THERE.  A protected byte is
                     NOT unconditionally clean: the holder's own plain
                     stores inside its critical section are owned and
                     UNPUBLISHED until it releases, which is exactly the C→D
                     move of the three-state protocol.  So the state carries
                     the dirty author [d : option CPU] and its φ conjunct is
                     [wcds_ob_ok] — [WClean]'s obligation at [None],
                     [WDirty c]'s at [Some c].  The protected store rule
                     ([wcds_ok_store_prot]) takes [d = None ∨ d = Some c]
                     exactly as the owned store rule takes [WClean ∨ WDirty
                     c], and the D→C flip at the release is
                     [wcds_prot_flip], the twin of [wcds_dirty_flip].  ([γ]
                     is IDENTIFICATION ONLY — no clause of [wcds_prot]
                     mentions it; it is what lets a client's [locked γ c] and
                     the byte's state name the same lock.)

                     ENFORCEMENT.  The generic PLAIN store rule
                     ([wcds_ok_store_own]) demands [s = WClean ∨ s = WDirty
                     c], so it refuses a [WProt] byte outright — the same
                     disequality every generic store site already reads off
                     the [wclean]/[wown_st]/[sync_byte] fragment it holds,
                     no new premise threaded anywhere.  ([is_wprot] is the
                     boolean form, for a site that wants to say it.)  The
                     NON-plain rule ([wcds_ok_store_nonplain]) is TRUE at
                     [WProt] and stays available: [wprot_at] speaks of plain
                     messages only, and no site can reach the byte without
                     the exclusive fragment anyway. *)
Inductive wcds :=
  | WClean
  | WDirty (c : CPU)
  | WSync
  | WLock (base : Z) (n0 : nat) (h : option nat)
  | WProt (γ : gname) (base : Z) (n0 r0 : nat) (d : option CPU).

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

(* ---------------------------------------------------------------------- *)
(** *** THE LOCK WORD'S VALUE PROTOCOL (tier-2 T2-0 / S6 §4, §6b)

    The one fact about the kernel's lock words that is NOT machine-derivable
    (nothing stops a program from plain-storing 5 to a lock word; xv6 just
    does not) and that tier 2's case #5 needs in order to make the two
    critical-section windows gmo-exclusive: writes to a registered lock word
    ALTERNATE acquire-RMW / release.  It rides the C/D/S protocol as its
    fourth per-byte state, so the enforcement is the write rule of the state
    and the export is one read of the same auth map [no_violation] is read
    from. *)

(** The four zero bytes a release stores. *)
Definition wlock_zero4 : list (bv 8) := replicate 4 (Z_to_bv 8 0).

Lemma wlock_zero4_eq :
  wlock_zero4 = [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof. reflexivity. Qed.

(** [wlock_shaped m] — the message is ACQUIRE-SHAPED or RELEASE-SHAPED:

      - four bytes wide (a lock word is an [int]);
      - never an owned plain store ([WCplain]);
      - and EITHER exclusive (the acquire's [amoswap] write half, whose read
        half reads the latest write — [ak_latest]) OR a write of the ZERO
        word (the release).

    Read it contrapositively, which is the form S6 §3's case #5 consumes: a
    message that writes a NONZERO value to a registered lock word is
    [WCexcl], i.e. the write half of an RMW, so [excl_ok] orders it; every
    other message on the word writes 0 and is at least release-class, so it
    PUBLISHES.  Hence an acquire's read of 0 names its co-predecessor
    release.

    DELIBERATE WEAKENING vs. the T2-0 spec's "[WCrel] ∧ zero" release arm:
    the release leaf's own effect ([WeakInstr.wQ_store_w]) leaves the
    message's class EXISTENTIAL and derives only [≠ WCplain] from the
    hart's [w_relp] flag — pinning [WCrel] there would need [ak_latest =
    false], which no leaf at this altitude carries.  The arm admitted by the
    weakening ([WCexcl] writing zero — an [amoswap] that swaps in 0) is
    STRICTLY more ordered than a release, so nothing downstream loses. *)
Definition wlock_shaped (m : wmsg) : Prop :=
  length (wm_data m) = 4%nat /\ wm_ak m <> WCplain /\
  (wm_ak m = WCexcl \/ wm_data m = wlock_zero4).

(** THE EXPORTED PURE FACT, per byte: [a] is a byte of the lock word at
    [base], and every message of the log AT OR AFTER the registration point
    [n0] that writes [a] is a message of the whole word, acquire- or
    release-shaped. *)
Definition wlp_at (log : list wmsg) (a base : Z) (n0 : nat) : Prop :=
  (base <= a < base + 4)%Z /\
  forall p m, log !! p = Some m -> (n0 <= p)%nat -> is_Some (msg_byte m a) ->
    wm_pa m = base /\ wlock_shaped m.

(* ---------------------------------------------------------------------- *)
(** *** THE ALTERNATION FOLD (tier-2 T2-0' / F3', route-b sect 4d.3')

    [wlp_at] pins the SHAPES of the messages on a registered lock word; what
    the kill needs on top is the PAIRING — "only the holder releases".  That
    is a fact about the SEQUENCE of those messages, and it is a pure FOLD:
    replay the post-registration messages of the word, carrying the current
    holder [h : option nat] ([None] = free, [Some t] = held by agent [t]).

      - a ZERO-DATA message (the release) requires the fold to be held by its
        own author and leaves it free;
      - an EXCLUSIVE NONZERO message is an [amoswap] write half: from FREE it
        is a SUCCESSFUL ACQUIRE and installs its author as the holder; from
        HELD it is a FAILED SWAP and changes nothing (the log records no read
        value, so the fold cannot tell a failed swap from anything else — and
        need not);
      - anything else does not occur on a [wlock_shaped] word and fails the
        fold outright.

    The zero-data test comes FIRST because [wlock_shaped] deliberately admits
    an exclusive write of the zero word (an [amoswap] swapping in 0), which
    is a release. *)

(** Does [m] write byte [a]?  As a boolean, so that it may be matched on
    inside the fold. *)
Definition mwrites (a : Z) (m : wmsg) : bool :=
  match msg_byte m a with Some _ => true | None => false end.

Lemma mwrites_true a m : mwrites a m = true <-> is_Some (msg_byte m a).
Proof.
  rewrite /mwrites. destruct (msg_byte m a) as [b|].
  - split; [intros _; by eexists|done].
  - split; [done|intros [b Hb]; done].
Qed.

Lemma mwrites_false a m : mwrites a m = false <-> msg_byte m a = None.
Proof.
  rewrite /mwrites. destruct (msg_byte m a) as [b|]; [|done].
  split; [done|intros [=]].
Qed.

Definition alt_step (h : option nat) (m : wmsg) : option (option nat) :=
  if bool_decide (wm_data m = wlock_zero4)
  then match h with
       | Some t => if bool_decide (wm_tid m = Some t) then Some None else None
       | None => None
       end
  else if bool_decide (wm_ak m = WCexcl)
       then match h with
            | None => match wm_tid m with
                      | Some t => Some (Some t)
                      | None => None
                      end
            | Some _ => Some h
            end
       else None.

(** THE THREE STEPS, as the leaves use them. *)
Lemma alt_step_rel m t :
  wm_data m = wlock_zero4 -> wm_tid m = Some t ->
  alt_step (Some t) m = Some None.
Proof.
  intros Hd Ht. rewrite /alt_step (bool_decide_eq_true_2 _ Hd).
  by rewrite (bool_decide_eq_true_2 _ Ht).
Qed.

Lemma alt_step_acq m t :
  wm_data m <> wlock_zero4 -> wm_ak m = WCexcl -> wm_tid m = Some t ->
  alt_step None m = Some (Some t).
Proof.
  intros Hd Hk Ht. rewrite /alt_step (bool_decide_eq_false_2 _ Hd).
  by rewrite (bool_decide_eq_true_2 _ Hk) Ht.
Qed.

Lemma alt_step_fail m t :
  wm_data m <> wlock_zero4 -> wm_ak m = WCexcl ->
  alt_step (Some t) m = Some (Some t).
Proof.
  intros Hd Hk. rewrite /alt_step (bool_decide_eq_false_2 _ Hd).
  by rewrite (bool_decide_eq_true_2 _ Hk).
Qed.

(** ... and their INVERSIONS, which is what the kill lemmas read. *)
Lemma alt_step_zero h m h' :
  wm_data m = wlock_zero4 -> alt_step h m = Some h' ->
  h' = None /\ h <> None /\ wm_tid m = h.
Proof.
  intros Hd. rewrite /alt_step (bool_decide_eq_true_2 _ Hd).
  destruct h as [t|]; [|discriminate].
  case_bool_decide as Ht; [|discriminate]. intros [= <-].
  split_and!; [done|done|exact Ht].
Qed.

Lemma alt_step_nonzero h m h' :
  wm_data m <> wlock_zero4 -> alt_step h m = Some h' ->
  wm_ak m = WCexcl /\ h' <> None /\
  (h = None -> h' = wm_tid m) /\ (h <> None -> h' = h).
Proof.
  intros Hd. rewrite /alt_step (bool_decide_eq_false_2 _ Hd).
  case_bool_decide as Hk; [|discriminate].
  destruct h as [t|].
  - intros [= <-]. split_and!; [done|done|intros [=]|done].
  - destruct (wm_tid m) as [t|] eqn:Ht; [|discriminate].
    intros [= <-]. split_and!;
      [done|done|done|intros Hne; exfalso; by apply Hne].
Qed.

Fixpoint alt_fold (a : Z) (h : option nat) (ms : list wmsg)
    : option (option nat) :=
  match ms with
  | [] => Some h
  | m :: ms' =>
      if mwrites a m
      then match alt_step h m with
           | Some h' => alt_fold a h' ms'
           | None => None
           end
      else alt_fold a h ms'
  end.

Lemma alt_fold_app a h ms1 ms2 :
  alt_fold a h (ms1 ++ ms2)
  = match alt_fold a h ms1 with
    | Some h' => alt_fold a h' ms2
    | None => None
    end.
Proof.
  revert h. induction ms1 as [|m ms1 IH]; intros h; [done|]. simpl.
  destruct (mwrites a m); [|by apply IH].
  destruct (alt_step h m) as [h'|]; [by apply IH|done].
Qed.

Lemma alt_fold_quiet a h ms :
  (forall m, m ∈ ms -> msg_byte m a = None) -> alt_fold a h ms = Some h.
Proof.
  induction ms as [|m ms IH]; [done|]. intros Hno. simpl.
  rewrite (proj2 (mwrites_false a m) (Hno m (elem_of_list_here _ _))).
  apply IH. intros m' Hm'. by apply Hno, elem_of_list_further.
Qed.

(** THE FOLD AT A POSITION: replay the messages of the log in the window
    [[n0, p)] that write [a].  [wlp_holder_at log a n0 p = Some h] says the
    word is held by [h] just BEFORE position [p]; [None] says the sequence is
    not a legal alternation at all. *)
Definition wlp_holder_at (log : list wmsg) (a : Z) (n0 p : nat)
    : option (option nat) :=
  alt_fold a None (drop n0 (take p log)).

(** THE EXPORTED FACT: the whole post-registration suffix folds, and ends at
    holder [h].  ([n0] is at or below the log's length — registration happens
    at the current top and the log only grows — which is what makes the fold
    extend one message at a time.) *)
Definition wlp_alt (log : list wmsg) (a : Z) (n0 : nat) (h : option nat)
    : Prop :=
  (n0 <= length log)%nat /\ wlp_holder_at log a n0 (length log) = Some h.

Lemma wlp_holder_small log a n0 p :
  (p <= n0)%nat -> wlp_holder_at log a n0 p = Some None.
Proof.
  intros Hp. rewrite /wlp_holder_at drop_ge; [done|].
  rewrite length_take. lia.
Qed.

Lemma wlp_holder_big log a n0 p :
  (length log <= p)%nat ->
  wlp_holder_at log a n0 p = wlp_holder_at log a n0 (length log).
Proof. intros Hp. rewrite /wlp_holder_at !take_ge //. Qed.

Lemma wlp_holder_step log a n0 p m :
  (n0 <= p)%nat -> log !! p = Some m ->
  wlp_holder_at log a n0 (S p)
  = match wlp_holder_at log a n0 p with
    | None => None
    | Some h => if mwrites a m then alt_step h m else Some h
    end.
Proof.
  intros Hn0 Hp. pose proof (lookup_lt_Some _ _ _ Hp) as Hlt.
  rewrite /wlp_holder_at (take_S_r _ _ m Hp).
  rewrite drop_app_le; [|rewrite length_take; lia].
  rewrite alt_fold_app.
  destruct (alt_fold a None (drop n0 (take p log))) as [h|]; [|done].
  simpl. destruct (mwrites a m); [|done]. by destruct (alt_step h m).
Qed.

Lemma wlp_holder_none_mono log a n0 p q :
  (p <= q)%nat -> wlp_holder_at log a n0 p = None ->
  wlp_holder_at log a n0 q = None.
Proof.
  induction q as [|q IH]; intros Hpq Hp.
  - assert (p = 0%nat) as -> by lia. exact Hp.
  - destruct (decide (p = S q)) as [->|Hne]; [exact Hp|].
    assert (Hq : wlp_holder_at log a n0 q = None) by (apply IH; [lia|done]).
    destruct (decide (q < n0)%nat) as [Hlt|Hge].
    { rewrite (wlp_holder_small log a n0 q ltac:(lia)) in Hq. discriminate. }
    destruct (log !! q) as [m|] eqn:Hm.
    + rewrite (wlp_holder_step log a n0 q m ltac:(lia) Hm) Hq //.
    + apply lookup_ge_None in Hm.
      rewrite (wlp_holder_big log a n0 (S q) ltac:(lia))
              -(wlp_holder_big log a n0 q ltac:(lia)) //.
Qed.

Lemma wlp_holder_is_Some log a n0 p q h :
  (p <= q)%nat -> wlp_holder_at log a n0 q = Some h ->
  exists h', wlp_holder_at log a n0 p = Some h'.
Proof.
  intros Hpq Hq. destruct (wlp_holder_at log a n0 p) as [h'|] eqn:Hp;
    [by exists h'|].
  rewrite (wlp_holder_none_mono log a n0 p q Hpq Hp) in Hq. discriminate.
Qed.

(** The fold does not move across a stretch that does not write [a]. *)
Lemma wlp_holder_quiet log a n0 p q :
  (p <= q)%nat ->
  (forall r mr, (p <= r < q)%nat -> log !! r = Some mr -> msg_byte mr a = None) ->
  wlp_holder_at log a n0 q = wlp_holder_at log a n0 p.
Proof.
  induction q as [|q IH]; intros Hpq Hq.
  - assert (p = 0%nat) as -> by lia. done.
  - destruct (decide (p = S q)) as [->|Hne]; [done|].
    rewrite -(IH ltac:(lia) ltac:(intros r mr Hr; apply Hq; lia)).
    destruct (decide (q < n0)%nat) as [Hlt|Hge].
    { rewrite (wlp_holder_small log a n0 (S q) ltac:(lia))
              (wlp_holder_small log a n0 q ltac:(lia)) //. }
    destruct (log !! q) as [m|] eqn:Hm.
    + rewrite (wlp_holder_step log a n0 q m ltac:(lia) Hm).
      rewrite (proj2 (mwrites_false a m) (Hq q m ltac:(lia) Hm)).
      by destruct (wlp_holder_at log a n0 q).
    + apply lookup_ge_None in Hm.
      rewrite (wlp_holder_big log a n0 (S q) ltac:(lia))
              -(wlp_holder_big log a n0 q ltac:(lia)) //.
Qed.

(** ... and it does not move across a stretch of FAILED SWAPS: while the word
    is held and nobody writes zero to it, the holder stays. *)
Lemma wlp_holder_hold log a n0 p q hv h2 :
  (p <= q)%nat ->
  wlp_holder_at log a n0 p = Some (Some hv) ->
  wlp_holder_at log a n0 q = Some h2 ->
  (forall r mr, (p <= r < q)%nat -> log !! r = Some mr ->
     is_Some (msg_byte mr a) -> wm_data mr <> wlock_zero4) ->
  h2 = Some hv.
Proof.
  revert h2. induction q as [|q IH]; intros h2 Hpq Hp Hq Hnz.
  - assert (p = 0%nat) as -> by lia. rewrite Hp in Hq. by simplify_eq.
  - destruct (decide (p = S q)) as [->|Hne].
    { rewrite Hp in Hq. by simplify_eq. }
    assert (Hpq' : (p <= q)%nat) by lia.
    destruct (wlp_holder_is_Some log a n0 q (S q) h2 ltac:(lia) Hq)
      as [h1 Hq1].
    assert (Hh1 : h1 = Some hv)
      by (apply (IH h1 Hpq' Hp Hq1); intros r mr Hr; apply Hnz; lia).
    subst h1.
    (* the window is above the registration point: [p] is, and [p <= q] *)
    assert (Hn0 : (n0 <= q)%nat).
    { destruct (decide (n0 <= q)%nat) as [?|Hgt]; [done|exfalso].
      rewrite (wlp_holder_small log a n0 p ltac:(lia)) in Hp. by simplify_eq. }
    destruct (log !! q) as [m|] eqn:Hm.
    + rewrite (wlp_holder_step log a n0 q m Hn0 Hm) Hq1 in Hq.
      destruct (mwrites a m) eqn:Hw; [|by simplify_eq].
      destruct (alt_step_nonzero (Some hv) m h2 
                  (Hnz q m ltac:(lia) Hm (proj1 (mwrites_true a m) Hw)) Hq)
        as (_ & _ & _ & Hkeep).
      by apply Hkeep.
    + apply lookup_ge_None in Hm.
      rewrite (wlp_holder_big log a n0 (S q) ltac:(lia))
              -(wlp_holder_big log a n0 q ltac:(lia)) Hq1 in Hq.
      by simplify_eq.
Qed.

(** A bounded search for the FIRST position of a window at which a decidable
    property of the message holds. *)
Lemma msg_search (f : wmsg -> bool) (log : list wmsg) (s0 e : nat) :
  (forall r mr, (s0 <= r < e)%nat -> log !! r = Some mr -> f mr = false)
  \/ (exists r mr, (s0 <= r < e)%nat /\ log !! r = Some mr /\ f mr = true /\
        forall r' mr', (s0 <= r' < r)%nat -> log !! r' = Some mr' ->
          f mr' = false).
Proof.
  induction e as [|e IH].
  - left. intros r mr Hr. exfalso. lia.
  - destruct IH as [Hno|(r & mr & Hr & Hlk & Hf & Hfirst)].
    + destruct (log !! e) as [m|] eqn:Hm.
      * destruct (f m) eqn:Hf.
        -- destruct (decide (s0 <= e)%nat) as [Hle|Hgt].
           ++ right. exists e, m. split_and!; [lia|lia|done|done|].
              intros r' mr' Hr'. apply Hno. lia.
           ++ left. intros r mr Hr. exfalso. lia.
        -- left. intros r mr Hr Hlk.
           destruct (decide (r = e)) as [->|Hne];
             [rewrite Hm in Hlk; by simplify_eq|apply (Hno r mr); [lia|done]].
      * left. intros r mr Hr Hlk.
        destruct (decide (r = e)) as [->|Hne];
          [rewrite Hm in Hlk; by simplify_eq|apply (Hno r mr); [lia|done]].
    + right. exists r, mr. split_and!; [lia|lia|done|done|done].
Qed.

(** THE FRAMING FACT for the fold: messages that do not write [a] do not
    move it. *)
Lemma wlp_alt_app log ms a n0 h :
  (forall m, m ∈ ms -> msg_byte m a = None) ->
  wlp_alt log a n0 h -> wlp_alt (log ++ ms) a n0 h.
Proof.
  intros Hno [Hlen Hf]. split; [rewrite length_app; lia|].
  rewrite /wlp_holder_at take_ge; [|lia].
  rewrite drop_app_le; [|lia]. rewrite alt_fold_app.
  rewrite /wlp_holder_at take_ge in Hf; [|lia]. rewrite Hf.
  by apply alt_fold_quiet.
Qed.

(** ... and THE STEP: one message on the word moves it by [alt_step]. *)
Lemma wlp_alt_store log mnew a n0 h h' :
  wlp_alt log a n0 h -> is_Some (msg_byte mnew a) ->
  alt_step h mnew = Some h' -> wlp_alt (log ++ [mnew]) a n0 h'.
Proof.
  intros [Hlen Hf] Hw Hst. split; [rewrite length_app /=; lia|].
  rewrite /wlp_holder_at take_ge; [|rewrite length_app /=; lia].
  rewrite drop_app_le; [|lia]. rewrite alt_fold_app.
  rewrite /wlp_holder_at take_ge in Hf; [|lia]. rewrite Hf /=.
  by rewrite (proj2 (mwrites_true a mnew) Hw) Hst.
Qed.

(** The registration point's own value: at [n0 = length log] the window is
    empty, so the word is FREE. *)
Lemma wlp_alt_register log a : wlp_alt log a (length log) None.
Proof. split; [lia|by apply wlp_holder_small]. Qed.

(* ---------------------------------------------------------------------- *)
(** *** WHAT THE FOLD SAYS ABOUT THE WORD'S VALUE, AND THE TWO KILL LEMMAS

    These three are the reason the export exists (route-b sect 4d.3'): the
    graph-side [cs_kill] consumes them at the certifying configuration. *)

(** LOCALITY FACT (i): the fold's state is the word's CURRENT VALUE, read the
    way [WeakStore.wlat4L_flat_gen] reads it — off the LATEST message writing
    the byte.  The word is free exactly when that message wrote zero.  (There
    is no third case: the fold's own success rules out a zero-data message on
    a free word, and a nonzero one always leaves the word held.) *)
Lemma wlp_alt_value log a n0 h p m :
  wlp_alt log a n0 h -> (n0 <= p)%nat ->
  log !! p = Some m -> is_Some (msg_byte m a) ->
  (forall q mq, (p < q)%nat -> log !! q = Some mq -> msg_byte mq a = None) ->
  (h = None <-> wm_data m = wlock_zero4).
Proof.
  intros [Hlen Hf] Hn0 Hp Hw Hlast.
  pose proof (lookup_lt_Some _ _ _ Hp) as Hlt.
  assert (Hsp : wlp_holder_at log a n0 (S p) = Some h).
  { rewrite -Hf. symmetry.
    apply (wlp_holder_quiet log a n0 (S p) (length log)); [lia|].
    intros r mr Hr. apply Hlast. lia. }
  destruct (wlp_holder_is_Some log a n0 p (S p) h ltac:(lia) Hsp) as [hp Hhp].
  rewrite (wlp_holder_step log a n0 p m Hn0 Hp) Hhp
          (proj2 (mwrites_true a m) Hw) in Hsp.
  split.
  - intros ->. destruct (decide (wm_data m = wlock_zero4)) as [?|Hne]; [done|].
    destruct (alt_step_nonzero hp m None Hne Hsp) as (_ & Hnn & _). done.
  - intros Hd. by destruct (alt_step_zero hp m h Hd Hsp) as (-> & _ & _).
Qed.

(** KILL LEMMA 1 — TWO ACQUIRES ARE SEPARATED BY THE FIRST ONE'S RELEASE.
    [p] is a successful acquire (the fold is FREE just before it, and the
    message is not a release) by agent [i]; the word is FREE again just
    before [q].  Then [i] released in between — which is exactly the
    "critical sections do not overlap" premise [cs_kill] carries.  (The
    two harts need not be distinct: the statement holds for [i = j] too, so
    the distinctness hypothesis of the design note is not taken.) *)
Lemma wlp_alt_two_acq log a n0 p q mp i :
  (n0 <= p)%nat -> (p < q)%nat ->
  log !! p = Some mp -> is_Some (msg_byte mp a) ->
  wm_data mp <> wlock_zero4 -> wm_tid mp = Some i ->
  wlp_holder_at log a n0 p = Some None ->
  wlp_holder_at log a n0 q = Some None ->
  exists r mr, (p < r < q)%nat /\ log !! r = Some mr /\
               is_Some (msg_byte mr a) /\ wm_data mr = wlock_zero4 /\
               wm_tid mr = Some i.
Proof.
  intros Hn0 Hpq Hp Hw Hnz Hti Hfp Hfq.
  (* the acquire installs [i] *)
  destruct (wlp_holder_is_Some log a n0 (S p) q None ltac:(lia) Hfq)
    as [h1 Hsp].
  assert (Hst : alt_step None mp = Some h1).
  { rewrite -Hsp (wlp_holder_step log a n0 p mp Hn0 Hp) Hfp
            (proj2 (mwrites_true a mp) Hw) //. }
  destruct (alt_step_nonzero None mp h1 Hnz Hst) as (_ & _ & Hfree & _).
  rewrite (Hfree eq_refl) Hti in Hsp.
  (* the first release after it *)
  destruct (msg_search
              (fun m => mwrites a m && bool_decide (wm_data m = wlock_zero4))
              log (S p) q) as [Hnone|(r & mr & Hr & Hlk & Hf & Hfirst)].
  - exfalso.
    assert (Hcontra : (None : option nat) = Some i).
    { apply (wlp_holder_hold log a n0 (S p) q i None ltac:(lia) Hsp Hfq).
      intros s ms Hs Hls Hws Hzs.
      specialize (Hnone s ms Hs Hls).
      rewrite (proj2 (mwrites_true a ms) Hws) (bool_decide_eq_true_2 _ Hzs)
        in Hnone. done. }
    done.
  - apply andb_prop in Hf as [Hf1 Hf2].
    apply mwrites_true in Hf1. apply bool_decide_eq_true in Hf2.
    exists r, mr. split_and!; [lia|lia|done|done|done|].
    (* the holder is still [i] at [r] *)
    destruct (wlp_holder_is_Some log a n0 r q None ltac:(lia) Hfq) as [hr Hhr].
    assert (Hhr' : hr = Some i).
    { apply (wlp_holder_hold log a n0 (S p) r i hr ltac:(lia) Hsp Hhr).
      intros s ms Hs Hls Hws Hzs.
      specialize (Hfirst s ms ltac:(lia) Hls).
      rewrite (proj2 (mwrites_true a ms) Hws) (bool_decide_eq_true_2 _ Hzs)
        in Hfirst. done. }
    subst hr.
    destruct (wlp_holder_is_Some log a n0 (S r) q None ltac:(lia) Hfq)
      as [h2 Hsr].
    rewrite (wlp_holder_step log a n0 r mr ltac:(lia) Hlk) Hhr
            (proj2 (mwrites_true a mr) Hf1) in Hsr.
    by destruct (alt_step_zero (Some i) mr h2 Hf2 Hsr) as (_ & _ & <-).
Qed.

(** KILL LEMMA 2 — THE CURRENT HOLDER'S CRITICAL SECTION IS STILL OPEN.
    If the word ends HELD, then its holder's LAST acquire — the position [p]
    at which the fold was free and after which no later message finds it free
    again — has no release after it at all.  ([cs_kill] uses this at the
    certifying configuration for the hart that is inside the section.) *)
Lemma wlp_alt_open log a n0 i p mp :
  wlp_alt log a n0 (Some i) ->
  (n0 <= p)%nat -> log !! p = Some mp -> is_Some (msg_byte mp a) ->
  wlp_holder_at log a n0 p = Some None ->
  (forall r mr, (p < r)%nat -> log !! r = Some mr -> is_Some (msg_byte mr a) ->
     wlp_holder_at log a n0 r <> Some None) ->
  forall r mr, (p < r)%nat -> log !! r = Some mr -> is_Some (msg_byte mr a) ->
     wm_data mr <> wlock_zero4.
Proof.
  intros [Hlen Hf] Hn0 Hp Hw Hfp Hlast r mr Hr Hlk Hwr Hzero.
  pose proof (lookup_lt_Some _ _ _ Hlk) as Hrlt.
  (* the release frees the word at [S r] *)
  destruct (wlp_holder_is_Some log a n0 r (length log) (Some i)
              ltac:(lia) Hf) as [hr Hhr].
  destruct (wlp_holder_is_Some log a n0 (S r) (length log) (Some i)
              ltac:(lia) Hf) as [h2 Hsr].
  assert (Hst : alt_step hr mr = Some h2).
  { rewrite -Hsr (wlp_holder_step log a n0 r mr ltac:(lia) Hlk) Hhr
            (proj2 (mwrites_true a mr) Hwr) //. }
  destruct (alt_step_zero hr mr h2 Hzero Hst) as (-> & _ & _).
  (* ... and the word can only be held again by a LATER successful acquire,
     which the "last acquire" hypothesis forbids *)
  destruct (msg_search (mwrites a) log (S r) (length log))
    as [Hnone|(s & ms & Hs & Hls & Hfs & Hfirst)].
  - rewrite (wlp_holder_quiet log a n0 (S r) (length log) ltac:(lia)
               ltac:(intros s2 ms2 Hs2 Hls2;
                     exact (proj1 (mwrites_false a ms2)
                              (Hnone s2 ms2 Hs2 Hls2))))
      in Hf.
    rewrite Hsr in Hf. by simplify_eq.
  - apply (Hlast s ms ltac:(lia) Hls (proj1 (mwrites_true a ms) Hfs)).
    rewrite (wlp_holder_quiet log a n0 (S r) s ltac:(lia)
               ltac:(intros s' ms' Hs' Hls';
                     exact (proj1 (mwrites_false a ms')
                              (Hfirst s' ms' Hs' Hls')))).
    exact Hsr.
Qed.

(** ... and the state's own obligation: the protocol ON TOP OF clean (see the
    [WLock] note at the head of the file), the alternation included. *)
Definition wcds_lock (log : list wmsg) (a base : Z) (n0 : nat)
    (h : option nat) : Prop :=
  wcds_clean log a /\ wlp_at log a base n0 /\ wlp_alt log a n0 h.

(* ---------------------------------------------------------------------- *)
(** *** THE PROTECTED-BYTE FOOTPRINT (tier-2 T2-0′ / F3″, route-b §4d.3′)

    The lock word's own protocol ([wlp_at] / [wlp_alt]) says who holds the
    lock at every position.  THE FOOTPRINT says what that buys: a byte
    declared to be in the lock's payload may be plain-written only by the
    hart the fold names as the holder.  That is the one fact the CS-chained
    arm of route B's cycle kill cannot read off the emission — "the message
    this critical-section read observed was written INSIDE its writer's
    critical section of the SAME lock" — and it is a pure predicate of the
    log, so the state interpretation exports it at every reachable
    configuration.

    [n0] is the LOCK WORD's registration point (the fold's origin, F3′), [r0]
    the BYTE's: the protection clause is quantified over [r0 ≤ p], leaving
    the byte's pre-registration history — [initlock]'s plain store, the
    allocator's zeroing — entirely unconstrained, exactly as [wlp_at]'s
    suffix does for the word. *)

(** The fold does not see an append below its cut point. *)
Lemma wlp_holder_app log ms a n0 p :
  (p <= length log)%nat ->
  wlp_holder_at (log ++ ms) a n0 p = wlp_holder_at log a n0 p.
Proof. intros Hp. rewrite /wlp_holder_at take_app_le //. Qed.

(** The φ obligation, indexed by the DIRTY AUTHOR: [None] is [WClean]'s,
    [Some c] is [WDirty c]'s.  (The state-level twin of [wcds_ob], which the
    context-indexed owned surface already uses; kept pure and separate so
    that [wcds_ok] does not have to call itself.) *)
Definition wcds_ob (b : option CPU) : wcds :=
  match b with None => WClean | Some c => WDirty c end.

Definition wcds_ob_ok (log : list wmsg) (a : Z) (d : option CPU) : Prop :=
  match d with
  | None => wcds_clean log a
  | Some c => wcds_dirty log a c
  end.

(** THE PROTECTION CLAUSE, per byte: every owned store at or after [r0] that
    reaches the byte is the lock's holder's.  [wm_tid m] is an [option agent]
    and the fold's value is an [option (option nat)], so the equation reads
    "the fold is DEFINED at [p] and names exactly this message's author". *)
Definition wprot_at (log : list wmsg) (a base : Z) (n0 r0 : nat) : Prop :=
  (n0 <= r0)%nat /\
  forall p m, log !! p = Some m -> (r0 <= p)%nat -> is_Some (msg_byte m a) ->
    wm_ak m = WCplain -> wlp_holder_at log base n0 p = Some (wm_tid m).

(** ... and the state's own obligation: φ's, at the dirty author the state
    carries, PLUS the protection clause. *)
Definition wcds_prot (log : list wmsg) (a base : Z) (n0 r0 : nat)
    (d : option CPU) : Prop :=
  wcds_ob_ok log a d /\ wprot_at log a base n0 r0.

Definition wcds_ok (log : list wmsg) (a : Z) (s : wcds) : Prop :=
  match s with
  | WClean => wcds_clean log a
  | WDirty c => wcds_dirty log a c
  | WSync => wcds_sync log a
  | WLock base n0 h => wcds_lock log a base n0 h
  | WProt _ base n0 r0 d => wcds_prot log a base n0 r0 d
  end.

Lemma wcds_ok_ob log a d : wcds_ok log a (wcds_ob d) <-> wcds_ob_ok log a d.
Proof. by destruct d. Qed.

(** The state a NON-PROTOCOL store may be taken at.  A [WLock] byte is
    exactly the one that may not (its write rule is [wcds_ok_store_lock]),
    and this boolean is what every generic store site now threads. *)
Definition is_wlock (s : wcds) : bool :=
  match s with WLock _ _ _ => true | _ => false end.

(** ... and the FIFTH state's boolean, for a site that wants to name it.  It
    is NOT threaded through the non-plain store rule (which is true at
    [WProt]); the PLAIN rule refuses the state by its [WClean ∨ WDirty c]
    premise, which is where the enforcement lives. *)
Definition is_wprot (s : wcds) : bool :=
  match s with WProt _ _ _ _ _ => true | _ => false end.

Lemma wcds_prot_ob log a γ base n0 r0 d :
  wcds_ok log a (WProt γ base n0 r0 d) -> wcds_ob_ok log a d.
Proof. by intros [? _]. Qed.

Lemma wcds_prot_wprot log a γ base n0 r0 d :
  wcds_ok log a (WProt γ base n0 r0 d) -> wprot_at log a base n0 r0.
Proof. by intros [_ ?]. Qed.

Lemma wcds_lock_clean log a base n0 h :
  wcds_ok log a (WLock base n0 h) -> wcds_clean log a.
Proof. by intros [? _]. Qed.

Lemma wcds_lock_wlp log a base n0 h :
  wcds_ok log a (WLock base n0 h) -> wlp_at log a base n0.
Proof. by intros [_ [? _]]. Qed.

Lemma wcds_lock_alt log a base n0 h :
  wcds_ok log a (WLock base n0 h) -> wlp_alt log a n0 h.
Proof. by intros [_ [_ ?]]. Qed.

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
  assert (Hcln : wcds_clean log a -> wcds_clean (log ++ ms) a).
  { intros Hcl p m Hp. destruct (Hcl p m (Hback p m Hp)) as [?|?];
      [by left|right; by apply wpublished_app]. }
  assert (Hdrt : forall c, wcds_dirty log a c -> wcds_dirty (log ++ ms) a c).
  { intros c Hdi p m Hp. destruct (Hdi p m (Hback p m Hp)) as [?|[?|?]];
      [by left|right; left; by apply wpublished_app|by right; right]. }
  destruct s as [ | c | | base n0 h | γ base n0 r0 d ]; simpl.
  - exact Hcln.
  - exact (Hdrt c).
  - intros Hsy p m Hp. exact (Hsy p m (Hback p m Hp)).
  - intros [Hcl [[Hrng Hlp] Halt]]. split; [by apply Hcln|].
    split; [|by apply wlp_alt_app]. split; [exact Hrng|].
    intros p m Hp Hn0 Hs.
    apply lookup_app_Some in Hp as [Hp|[_ Hp]]; [by apply (Hlp p m)|].
    exfalso. apply elem_of_list_lookup_2, Hno in Hp.
    rewrite Hp in Hs. by destruct Hs.
  - (* the FIFTH arm: φ's half frames as its own state does, and the
       protection clause is about messages of the OLD log only — the append
       writes none of the byte, and the fold below a cut point does not see
       an append ([wlp_holder_app]). *)
    intros [Hob [Hle Hpr]]. split.
    { destruct d as [c|]; simpl in Hob |- *; [by apply Hdrt|by apply Hcln]. }
    split; [exact Hle|]. intros p m Hp Hr0 Hs Hk.
    apply lookup_app_Some in Hp as [Hp|[_ Hp]]; last first.
    { exfalso. apply elem_of_list_lookup_2, Hno in Hp.
      rewrite Hp in Hs. by destruct Hs. }
    rewrite (wlp_holder_app log ms base n0 p
               ltac:(pose proof (lookup_lt_Some _ _ _ Hp); lia)).
    exact (Hpr p m Hp Hr0 Hs Hk).
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
    obligation to a C/D/S state, so those three survive it — including
    [WSync] (the "a sync byte is never plain-written" clause) and [WClean]
    (which is why an AMO or a release keeps a shared/invariant-held bundle
    clean).

    IT IS FALSE AT [WLock] (T2-0): a non-protocol exclusive store to a lock
    byte — an [amoswap] swapping in 5 — is non-plain and yet breaks the
    value protocol outright.  Hence the [is_wlock] premise; a lock byte's
    write rule is [wcds_ok_store_lock] below, and every generic store site
    supplies the disequality off the fragment it already holds (a [wclean],
    a [wown_st], or a [sync_byte] — none of which is [WLock]). *)
Lemma wcds_ok_store_nonplain log mnew a s :
  wm_ak mnew ≠ WCplain -> is_wlock s = false ->
  wcds_ok log a s -> wcds_ok (log ++ [mnew]) a s.
Proof.
  intros Hk Hnl Hok.
  assert (Hback : forall p m, wplain_at (log ++ [mnew]) a p m ->
                    wplain_at log a p m).
  { intros p m (Hp & Hs & Hkm).
    apply lookup_app_Some in Hp as [Hp|[_ Hp]]; [by split_and!|].
    exfalso. destruct (p - length log)%nat as [|n]; simpl in Hp;
      [|by rewrite lookup_nil in Hp]. simplify_eq; by apply Hk. }
  assert (Hcln : wcds_clean log a -> wcds_clean (log ++ [mnew]) a).
  { intros Hc p m Hp. destruct (Hc p m (Hback p m Hp)) as [?|?];
      [by left|right; by apply wpublished_app]. }
  assert (Hdrt : forall c, wcds_dirty log a c -> wcds_dirty (log ++ [mnew]) a c).
  { intros c Hd p m Hp. destruct (Hd p m (Hback p m Hp)) as [?|[?|?]];
      [by left|right; left; by apply wpublished_app|by right; right]. }
  destruct s as [ | c | | base n0 h | γ base n0 r0 d ]; simpl in Hok |- *.
  - exact (Hcln Hok).
  - exact (Hdrt c Hok).
  - intros p m Hp. exact (Hok p m (Hback p m Hp)).
  - simpl in Hnl. discriminate.
  - (* TRUE at [WProt]: [wprot_at] constrains PLAIN messages only, and the
       appended one is not plain, so the new position's obligation is
       vacuous. *)
    destruct Hok as [Hob [Hle Hpr]]. split.
    { destruct d as [c|]; simpl in Hob |- *; [by apply Hdrt|by apply Hcln]. }
    split; [exact Hle|]. intros p m Hp Hr0 Hs Hkm.
    apply lookup_app_Some in Hp as [Hp|[Hge Hp]]; last first.
    { exfalso. destruct (p - length log)%nat as [|n]; simpl in Hp;
        [|by rewrite lookup_nil in Hp]. by (simplify_eq; apply Hk). }
    rewrite (wlp_holder_app log [mnew] base n0 p
               ltac:(pose proof (lookup_lt_Some _ _ _ Hp); lia)).
    exact (Hpr p m Hp Hr0 Hs Hkm).
Qed.

Lemma wcds_ok_store_clean log mnew a :
  wm_ak mnew ≠ WCplain ->
  wcds_clean log a -> wcds_clean (log ++ [mnew]) a.
Proof. intros Hk. exact (wcds_ok_store_nonplain log mnew a WClean Hk eq_refl). Qed.

Lemma wcds_ok_store_sync log mnew a :
  wm_ak mnew ≠ WCplain ->
  wcds_sync log a -> wcds_sync (log ++ [mnew]) a.
Proof. intros Hk. exact (wcds_ok_store_nonplain log mnew a WSync Hk eq_refl). Qed.

(** A whole-word message writes EVERY byte of the word — which is why the
    protocol store below always moves the fold. *)
Lemma wlock_shaped_writes m a base :
  wm_pa m = base -> wlock_shaped m -> (base <= a < base + 4)%Z ->
  is_Some (msg_byte m a).
Proof.
  intros Hpa [Hlen _] Hrng. rewrite /msg_byte Hpa bool_decide_eq_true_2;
    [|lia].
  apply lookup_lt_is_Some_2. rewrite Hlen. lia.
Qed.

(** THE PROTOCOL STORE — the [WLock] write rule, covering BOTH the acquire's
    exclusive write and the release's zero store in one lemma: a message of
    the whole word, acquire- or release-shaped, keeps the state, MOVING the
    holder by [alt_step].  The three named instances below are the shapes the
    two leaves discharge. *)
Lemma wcds_ok_store_lock log mnew a base n0 h h' :
  wm_pa mnew = base -> wlock_shaped mnew -> alt_step h mnew = Some h' ->
  wcds_ok log a (WLock base n0 h) ->
  wcds_ok (log ++ [mnew]) a (WLock base n0 h').
Proof.
  intros Hpa Hsh Hst [Hcl [[Hrng Hlp] Halt]].
  assert (Hk : wm_ak mnew <> WCplain) by (destruct Hsh as (_ & ? & _); done).
  split; [by apply wcds_ok_store_clean|].
  split; [|apply (wlp_alt_store log mnew a n0 h h' Halt
                    (wlock_shaped_writes mnew a base Hpa Hsh Hrng) Hst)].
  split; [exact Hrng|].
  intros p m Hp Hn0 Hs.
  apply lookup_app_Some in Hp as [Hp|[Hge Hp]]; [by apply (Hlp p m)|].
  destruct (p - length log)%nat as [|n]; simpl in Hp;
    [|by rewrite lookup_nil in Hp].
  simplify_eq. by split.
Qed.

(** THE SUCCESSFUL ACQUIRE: an exclusive nonzero write on a FREE word
    installs its author. *)
Lemma wcds_ok_store_lock_acq log mnew a base n0 t :
  wm_pa mnew = base -> wlock_shaped mnew ->
  wm_data mnew <> wlock_zero4 -> wm_ak mnew = WCexcl -> wm_tid mnew = Some t ->
  wcds_ok log a (WLock base n0 None) ->
  wcds_ok (log ++ [mnew]) a (WLock base n0 (Some t)).
Proof.
  intros Hpa Hsh Hd Hk Ht.
  apply (wcds_ok_store_lock log mnew a base n0 None (Some t) Hpa Hsh).
  by apply alt_step_acq.
Qed.

(** THE FAILED SWAP: the same message on a HELD word leaves the holder
    alone (the log records no read value; the fold does not need one). *)
Lemma wcds_ok_store_lock_fail log mnew a base n0 t :
  wm_pa mnew = base -> wlock_shaped mnew ->
  wm_data mnew <> wlock_zero4 -> wm_ak mnew = WCexcl ->
  wcds_ok log a (WLock base n0 (Some t)) ->
  wcds_ok (log ++ [mnew]) a (WLock base n0 (Some t)).
Proof.
  intros Hpa Hsh Hd Hk.
  apply (wcds_ok_store_lock log mnew a base n0 (Some t) (Some t) Hpa Hsh).
  by apply alt_step_fail.
Qed.

(** THE RELEASE: a zero write frees the word — and ONLY THE HOLDER MAY DO
    IT.  This is the arm the whole export exists for. *)
Lemma wcds_ok_store_lock_rel log mnew a base n0 t :
  wm_pa mnew = base -> wlock_shaped mnew ->
  wm_data mnew = wlock_zero4 -> wm_tid mnew = Some t ->
  wcds_ok log a (WLock base n0 (Some t)) ->
  wcds_ok (log ++ [mnew]) a (WLock base n0 None).
Proof.
  intros Hpa Hsh Hd Ht.
  apply (wcds_ok_store_lock log mnew a base n0 (Some t) None Hpa Hsh).
  by apply alt_step_rel.
Qed.

(** THE REGISTRATION, purely.  At the log's own length the suffix obligation
    is VACUOUS — nothing is said about the byte's history, which is what makes
    registration legal AFTER [initlock]'s plain store — and the fold starts
    FREE, which is the word's value there. *)
Lemma wcds_ok_register log a base :
  (base <= a < base + 4)%Z ->
  wcds_clean log a ->
  wcds_ok log a (WLock base (length log) None).
Proof.
  intros Hrng Hcl. split; [exact Hcl|].
  split; [|apply wlp_alt_register]. split; [exact Hrng|].
  intros p m Hp Hn0 _. exfalso. apply lookup_lt_Some in Hp. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** THE PROTECTED-BYTE RULES (T2-0′ / F3″)

    Four rules, in the same shapes the [WLock] arm has: REGISTER (a clean
    byte joins the footprint), STORE (the holder's owned store), FLIP (the
    release publishes the holder's backlog, D→C) and DEREGISTER (the byte
    leaves the footprint with its φ obligation intact). *)

(** THE REGISTRATION.  At the log's own length the protection clause is
    VACUOUS — nothing about the byte's history is required, which is what
    makes registration legal after [initlock] and after the allocator's
    zeroing — and the byte starts with no outstanding owned store, i.e. at
    the state its clean fragment already certifies. *)
Lemma wcds_ok_register_prot log a base n0 :
  (n0 <= length log)%nat ->
  wcds_clean log a ->
  wcds_prot log a base n0 (length log) None.
Proof.
  intros Hn0 Hcl. split; [exact Hcl|]. split; [exact Hn0|].
  intros p m Hp Hr0 _ _. exfalso. apply lookup_lt_Some in Hp. lia.
Qed.

(** THE PROTECTED STORE — the rule the whole export exists to enforce: an
    owned ([WCplain]) message may reach a footprint byte only if its author
    is the lock's HOLDER at the log's top, which is where the appended
    message sits.  The [d = None ∨ d = Some c] premise is φ's, verbatim from
    [wcds_ok_store_own]: a second hart's outstanding owned store would be
    lost by the retarget, and the protocol forbids one anyway (it would have
    been made by a previous holder, who published it at its release —
    [wcds_prot_flip]). *)
Lemma wcds_ok_store_prot log mnew a base n0 r0 d (c : CPU) :
  wm_ak mnew = WCplain -> wm_tid mnew = Some (fin_to_nat c) ->
  (d = None \/ d = Some c) ->
  wlp_holder_at log base n0 (length log) = Some (Some (fin_to_nat c)) ->
  wcds_prot log a base n0 r0 d ->
  wcds_prot (log ++ [mnew]) a base n0 r0 (Some c).
Proof.
  intros Hk Htid Hd Hhold [Hob [Hle Hpr]]. split.
  - (* φ: the owned-store step of the three-state protocol, at [d]'s state *)
    assert (Hs : wcds_ok log a (wcds_ob d) /\
                 (wcds_ob d = WClean \/ wcds_ob d = WDirty c)).
    { destruct Hd as [-> | ->]; simpl; (split; [exact Hob|]);
        [by left|by right]. }
    destruct Hs as [Hok Hor].
    pose proof (wcds_ok_store_own log mnew a c _ Htid Hor Hok) as Hstep.
    by rewrite /wcds_own_step Hk in Hstep.
  - split; [exact Hle|]. intros p m Hp Hr0 Hsm Hkm.
    apply lookup_app_Some in Hp as [Hp|[Hge Hp]].
    + rewrite (wlp_holder_app log [mnew] base n0 p
                 ltac:(pose proof (lookup_lt_Some _ _ _ Hp); lia)).
      exact (Hpr p m Hp Hr0 Hsm Hkm).
    + destruct (p - length log)%nat as [|n] eqn:Hn; simpl in Hp;
        [|by rewrite lookup_nil in Hp].
      assert (p = length log) as -> by lia. injection Hp as <-.
      rewrite (wlp_holder_app log [mnew] base n0 (length log) ltac:(lia)).
      by rewrite Hhold Htid.
Qed.

(** THE DEREGISTRATION: the byte leaves the footprint carrying exactly the
    φ obligation its dirty author names — [WClean]'s when the lock is free
    (which is when a client may hand the payload back), [WDirty c]'s
    otherwise.  Purely a projection; the fractions and the lock's freedom are
    the Iris-level side conditions. *)
Lemma wcds_ok_deregister_prot log a base n0 r0 d :
  wcds_prot log a base n0 r0 d -> wcds_ok log a (wcds_ob d).
Proof. intros [Hob _]. by destruct d. Qed.

(* ---------------------------------------------------------------------- *)
(** *** THE KILL LEMMA (route-b §4d.3′, "what the kill consumes")

    The footprint's export, read backwards.  A plain message writing a
    protected byte at [p ≥ r0] is the holder's; unfolding the fold that says
    so gives the holder's SUCCESSFUL ACQUIRE — the last position at which the
    word was free — together with the fact that NO release of the word (no
    zero write at all) lies between it and [p].  That pair is precisely the
    CS-coverage hypothesis [WeakRvwmoLock.cs_kill] carries, now
    machine-grounded rather than assumed. *)

(** The fold's own inversion: a held word was acquired, and has not been
    released since. *)
Lemma wlp_holder_acq_exists log a n0 p j :
  wlp_holder_at log a n0 p = Some (Some j) ->
  exists q mq, (n0 <= q < p)%nat /\ log !! q = Some mq /\
    is_Some (msg_byte mq a) /\ wm_data mq <> wlock_zero4 /\
    wm_tid mq = Some j /\ wlp_holder_at log a n0 q = Some None /\
    (forall r mr, (q < r < p)%nat -> log !! r = Some mr ->
       is_Some (msg_byte mr a) -> wm_data mr <> wlock_zero4).
Proof.
  induction p as [|p IH]; intros Hp.
  { rewrite (wlp_holder_small log a n0 0 ltac:(lia)) in Hp. discriminate. }
  destruct (decide (S p <= n0)%nat) as [Hle|Hgt].
  { rewrite (wlp_holder_small log a n0 (S p) Hle) in Hp. discriminate. }
  destruct (log !! p) as [m|] eqn:Hm; last first.
  { (* past the end of the log: the fold has not moved *)
    apply lookup_ge_None in Hm.
    rewrite (wlp_holder_big log a n0 (S p) ltac:(lia))
            -(wlp_holder_big log a n0 p ltac:(lia)) in Hp.
    destruct (IH Hp) as (q & mq & [Hq1 Hq2] & Hlk & Hw & Hnz & Ht & Hfree & Hno).
    exists q, mq. split_and!;
      [lia|lia|exact Hlk|exact Hw|exact Hnz|exact Ht|exact Hfree|].
    intros r mr Hr Hlr Hwr. destruct (decide (r < p)%nat) as [Hlt|Hge];
      [exact (Hno r mr ltac:(lia) Hlr Hwr)|].
    exfalso. apply lookup_lt_Some in Hlr. lia. }
  destruct (decide (n0 <= p)%nat) as [Hn0p|Hn0p]; [|lia].
  rewrite (wlp_holder_step log a n0 p m Hn0p Hm) in Hp.
  destruct (wlp_holder_at log a n0 p) as [h|] eqn:Hh; [|discriminate].
  destruct (mwrites a m) eqn:Hwm; last first.
  { (* the message does not touch the word *)
    destruct (IH Hp) as (q & mq & [Hq1 Hq2] & Hlk & Hw & Hnz & Ht & Hfree & Hno).
    exists q, mq. split_and!;
      [lia|lia|exact Hlk|exact Hw|exact Hnz|exact Ht|exact Hfree|].
    intros r mr Hr Hlr Hwr. destruct (decide (r < p)%nat) as [Hlt|Hge];
      [exact (Hno r mr ltac:(lia) Hlr Hwr)|].
    assert (r = p) as -> by lia. rewrite Hm in Hlr. injection Hlr as <-.
    exfalso. rewrite (proj1 (mwrites_false a m) ltac:(done)) in Hwr.
    by destruct Hwr. }
  apply mwrites_true in Hwm.
  destruct (decide (wm_data m = wlock_zero4)) as [Hz|Hnz].
  { exfalso. by destruct (alt_step_zero h m (Some j) Hz Hp) as (? & _ & _). }
  destruct (alt_step_nonzero h m (Some j) Hnz Hp)
    as (_ & _ & Hfromfree & Hfromheld).
  destruct h as [t|].
  - (* a FAILED swap: the holder was already [j], so the acquire is earlier *)
    assert (Some t = Some j) as [= <-] by (symmetry; apply Hfromheld; done).
    destruct (IH eq_refl)
      as (q & mq & [Hq1 Hq2] & Hlk & Hw & Hnzq & Ht & Hfree & Hno).
    exists q, mq. split_and!;
      [lia|lia|exact Hlk|exact Hw|exact Hnzq|exact Ht|exact Hfree|].
    intros r mr Hr Hlr Hwr. destruct (decide (r < p)%nat) as [Hlt|Hge];
      [exact (Hno r mr ltac:(lia) Hlr Hwr)|].
    assert (r = p) as -> by lia. rewrite Hm in Hlr. by injection Hlr as <-.
  - (* a SUCCESSFUL acquire: [p] is the position we were looking for *)
    exists p, m. split_and!;
      [lia|lia|exact Hm|exact Hwm|exact Hnz| |exact Hh|].
    + by rewrite -(Hfromfree eq_refl).
    + intros r mr Hr. lia.
Qed.

(** THE EXPORTED CONSUMPTION.  [(P)] of route-b §4d.1 F6: the plain writer of
    a protected byte holds the lock, its acquire is identified, and its
    critical section is still open at the write. *)
Lemma wprot_writer_holds log a base n0 r0 p m j :
  wprot_at log a base n0 r0 ->
  log !! p = Some m -> (r0 <= p)%nat -> is_Some (msg_byte m a) ->
  wm_ak m = WCplain -> wm_tid m = Some j ->
  wlp_holder_at log base n0 p = Some (Some j).
Proof.
  intros [_ Hpr] Hp Hr0 Hs Hk Ht.
  rewrite (Hpr p m Hp Hr0 Hs Hk) Ht //.
Qed.

Lemma wprot_writer_cs log a base n0 r0 p m j :
  wprot_at log a base n0 r0 ->
  log !! p = Some m -> (r0 <= p)%nat -> is_Some (msg_byte m a) ->
  wm_ak m = WCplain -> wm_tid m = Some j ->
  exists q mq, (n0 <= q < p)%nat /\ log !! q = Some mq /\
    is_Some (msg_byte mq base) /\ wm_data mq <> wlock_zero4 /\
    wm_tid mq = Some j /\ wlp_holder_at log base n0 q = Some None /\
    (forall r mr, (q < r < p)%nat -> log !! r = Some mr ->
       is_Some (msg_byte mr base) -> wm_data mr <> wlock_zero4).
Proof.
  intros Hpr Hp Hr0 Hs Hk Ht.
  apply wlp_holder_acq_exists.
  exact (wprot_writer_holds log a base n0 r0 p m j Hpr Hp Hr0 Hs Hk Ht).
Qed.

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

(** THE D→C FLIP, [wcds_dirty_flip]'s twin: once the holder's release
    message is the log's LAST, its whole owned backlog is published, so every
    byte of the footprint returns to the "no outstanding store" state.  This
    is what a release site applies to the whole footprint before it gives the
    lock back — the protected twin of the deposit flip. *)
Lemma wcds_prot_flip log a base n0 r0 (c : CPU) q mq :
  log !! q = Some mq -> wm_tid mq = Some (fin_to_nat c) -> wm_ak mq = WCrel ->
  (length log <= S q)%nat ->
  wcds_prot log a base n0 r0 (Some c) -> wcds_prot log a base n0 r0 None.
Proof.
  intros Hq Htid Hk Hlen [Hob Hpr]. split; [|exact Hpr].
  exact (wcds_dirty_flip log a c q mq Hq Htid Hk Hlen Hob).
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

(** The whole map survives a non-plain store PROVIDED the message's own
    window carries no [WLock] byte (T2-0).  Outside the window nothing is
    written and every state frames ([wcds_ok_app]); inside it, the store site
    reads the disequality off the fragments it is already holding.  [zs] is
    the window — the same list [wcds_agree_winsl] takes. *)
Lemma wcds_agree_nonplain_win log mnew mc (zs : list Z) :
  wm_ak mnew ≠ WCplain ->
  (forall z, msg_byte mnew z <> None -> z ∈ zs) ->
  (forall z s, z ∈ zs -> mc !! z = Some s -> is_wlock s = false) ->
  wcds_agree log mc -> wcds_agree (log ++ [mnew]) mc.
Proof.
  intros Hk Hcov Hnl Hag a s Ha.
  destruct (decide (msg_byte mnew a = None)) as [Hnone|Hsome].
  - apply wcds_ok_app; [|by apply Hag].
    intros m0 Hm0. by apply elem_of_list_singleton in Hm0 as ->.
  - apply wcds_ok_store_nonplain; [done| |by apply Hag].
    exact (Hnl a s (Hcov a Hsome) Ha).
Qed.

(** The SINGLE-BYTE instance, which is the shape [WeakVProp]'s one-byte store
    rule has: the message writes only [a], and the caller's own fragment pins
    [a]'s state. *)
Lemma wcds_agree_nonplain1 log mnew mc (a : Z) (s0 : wcds) :
  wm_ak mnew ≠ WCplain -> is_wlock s0 = false ->
  (forall a', a' <> a -> msg_byte mnew a' = None) ->
  mc !! a = Some s0 ->
  wcds_agree log mc -> wcds_agree (log ++ [mnew]) mc.
Proof.
  intros Hk Hnl Hother Ha Hag.
  apply (wcds_agree_nonplain_win _ _ _ [a]); [exact Hk| | |exact Hag].
  - intros z Hz. destruct (decide (z = a)) as [->|Hne];
      [by apply elem_of_list_here|by destruct Hz; apply Hother].
  - intros z s Hz Hs. apply elem_of_list_singleton in Hz as ->.
    rewrite Ha in Hs. by simplify_eq.
Qed.

(** ... and its PROTOCOL twin: the whole map survives an acquire-/release-
    shaped store to a registered lock word, the window's bytes being exactly
    the ones the storing site holds [WLock] fragments for. *)
Lemma wcds_agree_store_lock log mnew mc mc' (zs : list Z) (base : Z)
    (n0 : nat) (h h' : option nat) :
  wm_pa mnew = base -> wlock_shaped mnew -> alt_step h mnew = Some h' ->
  (forall z, msg_byte mnew z <> None -> z ∈ zs) ->
  (forall z, z ∈ zs -> mc !! z = Some (WLock base n0 h)) ->
  (forall z, z ∈ zs -> mc' !! z = Some (WLock base n0 h')) ->
  (forall z, z ∉ zs -> mc' !! z = mc !! z) ->
  wcds_agree log mc -> wcds_agree (log ++ [mnew]) mc'.
Proof.
  intros Hpa Hsh Hst Hcov Hin Hin' Hout Hag a s Ha.
  destruct (decide (a ∈ zs)) as [Hz|Hz].
  - rewrite (Hin' a Hz) in Ha. injection Ha as <-.
    apply (wcds_ok_store_lock log mnew a base n0 h h' Hpa Hsh Hst).
    by apply Hag, Hin.
  - rewrite (Hout a Hz) in Ha.
    apply wcds_ok_app; [|by apply Hag].
    intros m0 Hm0. apply elem_of_list_singleton in Hm0 as ->.
    destruct (msg_byte mnew a) as [b|] eqn:Hb; [|done].
    exfalso. apply Hz, Hcov. by rewrite Hb.
Qed.

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

(** THE FOURTH ARM (T2-0), and the reason [WLock] carries the clean
    conjunct: a registered lock byte pays φ's obligation exactly as a clean
    one does, so the acquire/release leaves keep paying it off the very
    bundle they hand back. *)
Lemma nv_byte_lock log c' a n base n0 h :
  wcds_lock log a base n0 h -> nv_byte log c' a n.
Proof. intros [Hcl _]. by apply nv_byte_clean. Qed.

(** φ'S FIFTH ARM: a protected byte pays the violation-freedom obligation
    exactly as the C/D state its dirty author names does — which is what lets
    a protected store leaf discharge [nv_ok] off the very fragment it hands
    back. *)
Lemma nv_byte_prot log (c : CPU) a n base n0 r0 d :
  wcds_prot log a base n0 r0 d -> (d = None \/ d = Some c) ->
  nv_byte log c a n.
Proof.
  intros [Hob _] Hd. destruct Hd as [-> | ->]; simpl in Hob.
  - by apply nv_byte_clean.
  - by apply nv_byte_dirty.
Qed.

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

Lemma nv_ok_lock log c a base n0 h : wcds_lock log a base n0 h -> nv_ok log c a.
Proof. intros [H _] n. by apply nv_byte_clean. Qed.

Lemma nv_free_lock log a base n0 h : wcds_lock log a base n0 h -> nv_free log a.
Proof. intros [H _] c n. by apply nv_byte_clean. Qed.

Lemma nv_free_prot log a base n0 r0 :
  wcds_prot log a base n0 r0 None -> nv_free log a.
Proof. intros [Hob _] c n. by apply nv_byte_clean. Qed.

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
  (** THE LOCK-BYTE FRAGMENT (T2-0).  Exclusive, like [wdirty]: a byte of the
      registered lock word at [base], registered at log length [n0].  It is
      NOT persistent and NOT split — the whole point is that only its holder
      may write the byte, and its holder is [WeakLock.wlock_inv].  There is
      therefore no separate "registration witness" resource: the fragment
      inside the lock invariant IS the witness, and the export
      ([wlp_at_of_lock]) reads the pure protocol off it against the auth. *)
  Definition wlock_st (a : Z) (base : Z) (n0 : nat) (h : option nat)
      : iProp Σ :=
    wcds_el a (DfracOwn 1) (WLock base n0 h).

  Global Instance wcds_el_timeless a dq s : Timeless (wcds_el a dq s).
  Proof. rewrite /wcds_el. apply _. Qed.

  Global Instance wlock_st_timeless a base n0 h :
    Timeless (wlock_st a base n0 h).
  Proof. rewrite /wlock_st. apply _. Qed.

  Lemma wlock_st_lookup a base n0 h mc :
    ghost_map_auth weak_cds_name 1 mc -∗ wlock_st a base n0 h -∗
    ⌜mc !! a = Some (WLock base n0 h)⌝.
  Proof.
    iIntros "Ha Hel". rewrite /wlock_st /wcds_el.
    by iDestruct (ghost_map_lookup with "Ha Hel") as %Hlk.
  Qed.

  (** A lock byte is not a clean/owned/sync one: the fragments are
      incompatible, which is what makes the C/D/S store rules and the
      protocol rule mutually exclusive. *)
  Lemma wlock_st_clean_excl a base n0 h dq :
    wlock_st a base n0 h -∗ wclean a dq -∗ False.
  Proof.
    rewrite /wlock_st /wclean /wcds_el. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Hq. by inversion Hq.
  Qed.

  (** THE PROTECTED-BYTE FRAGMENT (T2-0′ / F3″).  Exclusive, like
      [wlock_st]: it is the byte's registration witness AND the carrier of
      the dirty author [d], and only its holder — the lock's payload owner —
      may write the byte.  It is incompatible with [wclean] / [wown_st] /
      [sync_byte] by the ghost map, which is where the plain store rule's
      refusal is paid for. *)
  Definition wprot_st (a : Z) (γ : gname) (base : Z) (n0 r0 : nat)
      (d : option CPU) : iProp Σ :=
    wcds_el a (DfracOwn 1) (WProt γ base n0 r0 d).

  Global Instance wprot_st_timeless a γ base n0 r0 d :
    Timeless (wprot_st a γ base n0 r0 d).
  Proof. rewrite /wprot_st. apply _. Qed.

  Lemma wprot_st_lookup a γ base n0 r0 d mc :
    ghost_map_auth weak_cds_name 1 mc -∗ wprot_st a γ base n0 r0 d -∗
    ⌜mc !! a = Some (WProt γ base n0 r0 d)⌝.
  Proof.
    iIntros "Ha Hel". rewrite /wprot_st /wcds_el.
    by iDestruct (ghost_map_lookup with "Ha Hel") as %Hlk.
  Qed.

  Lemma wprot_st_clean_excl a γ base n0 r0 d dq :
    wprot_st a γ base n0 r0 d -∗ wclean a dq -∗ False.
  Proof.
    rewrite /wprot_st /wclean /wcds_el. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Hq. by inversion Hq.
  Qed.

  Lemma wprot_st_lock_excl a γ base n0 r0 d base' n0' h :
    wprot_st a γ base n0 r0 d -∗ wlock_st a base' n0' h -∗ False.
  Proof.
    rewrite /wprot_st /wlock_st /wcds_el. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Hq. by inversion Hq.
  Qed.

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

  Lemma wprot_st_own_excl (c : CPU) a γ base n0 r0 d :
    wprot_st a γ base n0 r0 d -∗ wown_st c a -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct "H2" as (s) "[Hel %Hs]".
    rewrite /wprot_st /wcds_el.
    iDestruct (ghost_map_elem_agree with "H1 Hel") as %Hq.
    destruct Hs as [-> | ->]; by inversion Hq.
  Qed.

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

  (* ---------------------------------------------------------------- *)
  (** *** 3b'. THE LOCK-PROTOCOL EXPORT (T2-0 / S6 §4)

      THE ONE THING T2-0 OWES: the pure per-state fact that every message
      overlapping a registered lock word is acquire- or release-shaped, read
      off the very auth map that carries the C/D/S states — i.e. by exactly
      the move φ's [no_violation] export makes ([wcds_lookup] +
      [wcds_agree]).  Nothing else is needed: the FRAGMENT is the
      registration witness (it lives inside [WeakLock.wlock_inv], the only
      writer of the word), and the interp tie [wcds_agree] covers the new arm
      automatically. *)
  Lemma wlp_at_of_lock img log a base n0 h :
    wlat_interp img log -∗ wlock_st a base n0 h -∗ ⌜wlp_at log a base n0⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. exact (wcds_lock_wlp log a base n0 h Hok).
  Qed.

  (** ... and its T2-0′ twin: the ALTERNATION, off the same fragment. *)
  Lemma wlp_alt_of_lock img log a base n0 h :
    wlat_interp img log -∗ wlock_st a base n0 h -∗ ⌜wlp_alt log a n0 h⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. exact (wcds_lock_alt log a base n0 h Hok).
  Qed.

  Lemma nv_free_of_lock img log a base n0 h :
    wlat_interp img log -∗ wlock_st a base n0 h -∗ ⌜nv_free log a⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. by apply (nv_free_lock log a base n0 h).
  Qed.

  Lemma nv_ok_of_lock img log c a base n0 h :
    wlat_interp img log -∗ wlock_st a base n0 h -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hi He". iDestruct (nv_free_of_lock with "Hi He") as %H.
    iPureIntro. by apply nv_ok_of_free.
  Qed.

  (** THE REGISTRATION.  A clean byte inside the word's range becomes a lock
      byte, at [n0 = length log] — where the protocol's suffix obligation is
      vacuous, so NOTHING about the byte's history is required (which is what
      makes it legal after [initlock]'s plain store).  The clean state the
      caller gives up is the conjunct [WLock] carries forward. *)
  Lemma wlock_register img log a base :
    (base <= a < base + 4)%Z ->
    wlat_interp img log -∗ wclean a (DfracOwn 1) ==∗
    wlat_interp img log ∗ wlock_st a base (length log) None.
  Proof.
    intros Hrng. iIntros "Hi Hel".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wclean /wcds_el.
    iDestruct (ghost_map_lookup with "Hc Hel") as %Hlk.
    iMod (ghost_map_update (WLock base (length log) None) with "Hc Hel")
      as "[Hc Hel]".
    iModIntro. iFrame "Hel".
    iExists m, (<[a := WLock base (length log) None]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|].
    apply wcds_ok_register; [exact Hrng|exact (Hagc a WClean Hlk)].
  Qed.

  (** *** THE PROTECTED-BYTE OPERATIONS (T2-0′ / F3″)

      Registration, the owned store, the release flip and deregistration —
      the ghost halves of the four pure rules.  Each is one ghost-map update
      against the C/D/S auth, exactly like the [WLock] ones. *)

  (** REGISTRATION: a clean byte joins the footprint of the lock registered
      at [base] with ghost [γ] and registration point [n0], protected from
      the CURRENT log length on — where the protection clause is vacuous, so
      nothing about the byte's history is required. *)
  Lemma wprot_register img log a γ base (n0 : nat) :
    (n0 <= length log)%nat ->
    wlat_interp img log -∗ wclean a (DfracOwn 1) ==∗
    wlat_interp img log ∗ wprot_st a γ base n0 (length log) None.
  Proof.
    intros Hn0. iIntros "Hi Hel".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wclean /wcds_el.
    iDestruct (ghost_map_lookup with "Hc Hel") as %Hlk.
    iMod (ghost_map_update (WProt γ base n0 (length log) None) with "Hc Hel")
      as "[Hc Hel]".
    iModIntro. iFrame "Hel".
    iExists m, (<[a := WProt γ base n0 (length log) None]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|].
    apply wcds_ok_register_prot; [exact Hn0|exact (Hagc a WClean Hlk)].
  Qed.

  (** DEREGISTRATION: the byte leaves the footprint carrying the C/D state
      its dirty author names.  Stated at [d = None] — the shape a client has
      when the lock is free, which is the only moment the payload may be
      dismantled — so what comes back is an ordinary clean fragment. *)
  Lemma wprot_deregister img log a γ base n0 r0 :
    wlat_interp img log -∗ wprot_st a γ base n0 r0 None ==∗
    wlat_interp img log ∗ wclean a (DfracOwn 1).
  Proof.
    iIntros "Hi Hel".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wprot_st /wclean /wcds_el.
    iDestruct (ghost_map_lookup with "Hc Hel") as %Hlk.
    iMod (ghost_map_update WClean with "Hc Hel") as "[Hc Hel]".
    iModIntro. iFrame "Hel". iExists m, (<[a := WClean]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|].
    exact (wcds_ok_deregister_prot log a base n0 r0 None
             (Hagc a _ Hlk)).
  Qed.

  (** THE D→C FLIP at a release site, [wlat_flip]'s twin: the releasing
      hart's [WCrel] message is the log's LAST, so its whole owned backlog is
      published and every footprint byte returns to [d = None]. *)
  Lemma wprot_flip img log (mrel : wmsg) (c : CPU) a γ base n0 r0 :
    wm_tid mrel = Some (fin_to_nat c) -> wm_ak mrel = WCrel ->
    wlat_interp img (log ++ [mrel]) -∗ wprot_st a γ base n0 r0 (Some c) ==∗
    wlat_interp img (log ++ [mrel]) ∗ wprot_st a γ base n0 r0 None.
  Proof.
    intros Htid Hk. iIntros "Hi Hel".
    iDestruct "Hi" as (m mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wprot_st /wcds_el.
    iDestruct (ghost_map_lookup with "Hc Hel") as %Hlk.
    iMod (ghost_map_update (WProt γ base n0 r0 None) with "Hc Hel")
      as "[Hc Hel]".
    iModIntro. iFrame "Hel".
    iExists m, (<[a := WProt γ base n0 r0 None]> mc).
    iFrame "Hauth Hc". iSplitR; [iPureIntro; exact Hag|].
    iPureIntro. apply wcds_agree_insert; [exact Hagc|].
    apply (wcds_prot_flip _ _ _ _ _ c (length log) mrel).
    - rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag.
    - exact Htid.
    - exact Hk.
    - rewrite length_app /=. lia.
    - exact (Hagc a _ Hlk).
  Qed.

  (** THE PROTECTED STORE, at the ghost altitude: the byte's VALUE element is
      retargeted at the message the step appended and its state moves to
      "dirty by the storing hart".  The holder premise is the whole content
      of the rule — the message's author must be the hart the lock word's
      fold names at the log's top — and the client discharges it from the
      lock invariant plus its [locked] token. *)
  Lemma wprot_store img log (mnew : wmsg) a γ base n0 r0 d (c : CPU)
      (t : nat) (w b : bv 8) :
    wm_ak mnew = WCplain -> wm_tid mnew = Some (fin_to_nat c) ->
    (d = None \/ d = Some c) ->
    wlp_holder_at log base n0 (length log) = Some (Some (fin_to_nat c)) ->
    msg_byte mnew a = Some b ->
    (forall a', a' <> a -> msg_byte mnew a' = None) ->
    wlat_interp img log -∗ wlat_elem a (DfracOwn 1) t w -∗
    wprot_st a γ base n0 r0 d ==∗
    wlat_interp img (log ++ [mnew]) ∗
    wlat_elem a (DfracOwn 1) (S (length log)) b ∗
    wprot_st a γ base n0 r0 (Some c).
  Proof.
    intros Hk Htid Hd Hhold Hma Hother. iIntros "Hi He Hs".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wlat_elem /wprot_st /wcds_el.
    iDestruct (ghost_map_lookup with "Hc Hs") as %Hlk.
    iMod (ghost_map_update (S (length log), b) with "Hauth He")
      as "[Hauth He]".
    iMod (ghost_map_update (WProt γ base n0 r0 (Some c)) with "Hc Hs")
      as "[Hc Hs]".
    iModIntro. iFrame "He Hs".
    iExists (<[a := (S (length log), b)]> mm),
            (<[a := WProt γ base n0 r0 (Some c)]> mc).
    iFrame "Hauth Hc". iSplitR.
    { iPureIntro. by apply wlat_agree_store. }
    iPureIntro. intros a' s' Ha'.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Ha'. injection Ha' as <-.
      exact (wcds_ok_store_prot log mnew a base n0 r0 d c Hk Htid Hd Hhold
               (Hagc a _ Hlk)).
    - rewrite lookup_insert_ne // in Ha'.
      apply wcds_ok_app; [|by apply Hagc].
      intros m0 Hm0. apply elem_of_list_singleton in Hm0 as ->.
      by apply Hother.
  Qed.

  (** THE READINGS off the fragment: the protection clause itself (the
      export), and φ's obligation (what a protected leaf pays with). *)
  Lemma wprot_at_of_prot img log a γ base n0 r0 d :
    wlat_interp img log -∗ wprot_st a γ base n0 r0 d -∗
    ⌜wprot_at log a base n0 r0⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. exact (wcds_prot_wprot log a γ base n0 r0 d Hok).
  Qed.

  Lemma nv_byte_of_prot img log (c : CPU) a γ base n0 r0 d n :
    (d = None \/ d = Some c) ->
    wlat_interp img log -∗ wprot_st a γ base n0 r0 d -∗ ⌜nv_byte log c a n⌝.
  Proof.
    intros Hd. iIntros "Hi He".
    iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. exact (nv_byte_prot log c a n base n0 r0 d Hok Hd).
  Qed.

  Lemma nv_free_of_prot img log a γ base n0 r0 :
    wlat_interp img log -∗ wprot_st a γ base n0 r0 None -∗ ⌜nv_free log a⌝.
  Proof.
    iIntros "Hi He". iDestruct (wcds_lookup with "Hi He") as %Hok.
    iPureIntro. exact (nv_free_prot log a base n0 r0 Hok).
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

  (* ---------------------------------------------------------------- *)
  (** *** 3d. T2-0's EXPORT AND ITS REGISTRATION SEAM

      [weak_state_interp_export]'s sibling.  The lock word's value protocol
      is NOT a pure conjunct of the state interpretation the way
      [no_violation] is — it is a fact about the bytes a client has
      REGISTERED, so it is read off the C/D/S auth against the client's own
      [WLock] fragment.  That fragment is exclusive and lives inside the
      lock's namespace invariant ([WeakLock.wlock_inv]), so what crosses to
      the adequacy seam is [wlock_regd]: the PERSISTENT invariant assertion
      plus an accessor saying its body contains byte [a]'s fragment (at some
      registration point) and takes it back.

      THE SEAM DECISION (T2-0 report): no persistent per-byte registration
      witness is minted.  A [DfracDiscarded] copy of the state fragment is
      not an option — ghost-map fragments at different fractions must AGREE
      on the value, and the value here carries [n0]; and a discarded copy
      would make the byte unwritable, which is exactly what the acquire and
      release must do.  A separate registry ghost was rejected as out of
      scope (it re-opens the ~50-site [weak_state_interp] reassembly the
      φ-upgrade paid for).  The fragment inside the invariant IS the
      witness, and [wlock_regd] is the shape in which it travels. *)

  Definition wlock_regd (N : namespace) (a base : Z) : iProp Σ :=
    (∃ I : iProp Σ,
       inv N I ∗
       □ (I -∗ ∃ (n0 : nat) (h : option nat),
            wlock_st a base n0 h ∗ (wlock_st a base n0 h -∗ I)))%I.

  Global Instance wlock_regd_persistent N a base :
    Persistent (wlock_regd N a base).
  Proof. rewrite /wlock_regd. apply _. Qed.

  Lemma weak_state_interp_lat (g : wgstate) :
    weak_state_interp g -∗ wlat_interp (wgimg g) (wglog g).
  Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & $ & _)". Qed.

  (** THE PER-STATE EXPORT, off a fragment in hand. *)
  Lemma weak_state_interp_lockproto (g : wgstate) (a base : Z) (n0 : nat)
      (h : option nat) :
    weak_state_interp g -∗ wlock_st a base n0 h -∗
    ⌜wlp_at (wglog g) a base n0⌝.
  Proof.
    iIntros "Hi He". iDestruct (weak_state_interp_lat with "Hi") as "Hlat".
    by iApply (wlp_at_of_lock with "Hlat He").
  Qed.

  (** ... and THROUGH THE SEAM, in one fancy update at a mask containing the
      lock's namespace — which is the form the adequacy wrapper consumes
      (the continuation of [wp_strong_adequacy] runs at ⊤). *)
  Lemma wlock_regd_export_alt (N : namespace) (E : coPset) (g : wgstate)
      (a base : Z) :
    ↑N ⊆ E ->
    weak_state_interp g -∗ wlock_regd N a base ={E}=∗
    ⌜exists (n0 : nat) (h : option nat),
       wlp_at (wglog g) a base n0 /\ wlp_alt (wglog g) a n0 h⌝.
  Proof.
    intros HN. iIntros "Hsi #Hreg".
    iDestruct (weak_state_interp_lat with "Hsi") as "Hlat".
    iDestruct "Hreg" as (I) "[#Hinv #Hacc]".
    iInv "Hinv" as "HI" "Hclose".
    iAssert (▷ (∃ (n0 : nat) (h : option nat),
                  wlock_st a base n0 h ∗ (wlock_st a base n0 h -∗ I)))%I
      with "[HI]" as "HQ".
    { iNext. by iApply "Hacc". }
    rewrite bi.later_exist. iDestruct "HQ" as (n0) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (h) "HQ".
    rewrite bi.later_sep. iDestruct "HQ" as "[>Hst Hback]".
    iDestruct (wlp_at_of_lock with "Hlat Hst") as %Hlp.
    iDestruct (wlp_alt_of_lock with "Hlat Hst") as %Halt.
    iMod ("Hclose" with "[Hst Hback]") as "_".
    { iNext. by iApply "Hback". }
    iModIntro. iPureIntro. by exists n0, h.
  Qed.

  Lemma wlock_regd_export (N : namespace) (E : coPset) (g : wgstate)
      (a base : Z) :
    ↑N ⊆ E ->
    weak_state_interp g -∗ wlock_regd N a base ={E}=∗
    ⌜exists n0 : nat, wlp_at (wglog g) a base n0⌝.
  Proof.
    intros HN. iIntros "Hsi #Hreg".
    iMod (wlock_regd_export_alt N E g a base HN with "Hsi Hreg")
      as %(n0 & h & Hlp & _).
    iModIntro. iPureIntro. by exists n0.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3d′. F3″'s EXPORT AND ITS SEAM — THE PROTECTED-BYTE FOOTPRINT

      [wlock_regd]'s twin, one level up: the byte of interest is a PAYLOAD
      byte, and what travels to the adequacy seam is an invariant whose body
      holds BOTH its [WProt] fragment AND the lock word's own [WLock]
      fragment — the two AT THE SAME REGISTRATION POINT [n0].

      WHY BOTH FRAGMENTS, AND WHY ONE INVARIANT.  [wprot_at]'s content is a
      statement about the fold [wlp_holder_at log base n0 ·], so it is only
      as good as the [n0] it is stated at: the kill has to read the
      footprint's protection and the word's alternation ON THE SAME FOLD.
      Nothing relates two independently-quantified registration points, so
      the tie must be a RESOURCE fact, and the only place a resource fact can
      be persistent is inside an invariant.  [WeakLock.wplock_body] is that
      invariant — the lock's own, with the footprint's fragments moved in —
      and [WeakLock.wplock_inv_regd] is what produces this seam from it. *)

  Definition wprot_regd (N : namespace) (a base : Z) : iProp Σ :=
    (∃ I : iProp Σ,
       inv N I ∗
       □ (I -∗ ∃ (γ : gname) (n0 r0 : nat) (d : option CPU) (h : option nat),
            wprot_st a γ base n0 r0 d ∗ wlock_st base base n0 h ∗
            (wprot_st a γ base n0 r0 d -∗ wlock_st base base n0 h -∗ I)))%I.

  Global Instance wprot_regd_persistent N a base :
    Persistent (wprot_regd N a base).
  Proof. rewrite /wprot_regd. apply _. Qed.

  (** THE PER-STATE EXPORT, off the fragments in hand. *)
  Lemma weak_state_interp_prot (g : wgstate) (a base : Z) (γ : gname)
      (n0 r0 : nat) (d : option CPU) :
    weak_state_interp g -∗ wprot_st a γ base n0 r0 d -∗
    ⌜wprot_at (wglog g) a base n0 r0⌝.
  Proof.
    iIntros "Hi He". iDestruct (weak_state_interp_lat with "Hi") as "Hlat".
    by iApply (wprot_at_of_prot with "Hlat He").
  Qed.

  (** ... and THROUGH THE SEAM, in one fancy update at a mask containing the
      lock's namespace — the form the adequacy wrapper consumes.  All three
      conclusions share the registration point [n0]: the byte is protected
      from [r0] on, and the word it is protected by carries the shape and the
      alternation protocols from [n0] on. *)
  Lemma wprot_regd_export (N : namespace) (E : coPset) (g : wgstate)
      (a base : Z) :
    ↑N ⊆ E ->
    weak_state_interp g -∗ wprot_regd N a base ={E}=∗
    ⌜exists (γ : gname) (n0 r0 : nat) (h : option nat),
       wprot_at (wglog g) a base n0 r0 /\
       wlp_at (wglog g) base base n0 /\ wlp_alt (wglog g) base n0 h⌝.
  Proof.
    intros HN. iIntros "Hsi #Hreg".
    iDestruct (weak_state_interp_lat with "Hsi") as "Hlat".
    iDestruct "Hreg" as (I) "[#Hinv #Hacc]".
    iInv "Hinv" as "HI" "Hclose".
    iAssert (▷ (∃ (γ : gname) (n0 r0 : nat) (d : option CPU) (h : option nat),
                  wprot_st a γ base n0 r0 d ∗ wlock_st base base n0 h ∗
                  (wprot_st a γ base n0 r0 d -∗
                     wlock_st base base n0 h -∗ I)))%I
      with "[HI]" as "HQ".
    { iNext. by iApply "Hacc". }
    rewrite bi.later_exist. iDestruct "HQ" as (γ) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (n0) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (r0) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (d) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (h) "HQ".
    rewrite !bi.later_sep. iDestruct "HQ" as "(>Hpr & >Hlk & Hback)".
    iDestruct (wprot_at_of_prot with "Hlat Hpr") as %Hpa.
    iDestruct (wlp_at_of_lock with "Hlat Hlk") as %Hlp.
    iDestruct (wlp_alt_of_lock with "Hlat Hlk") as %Halt.
    iMod ("Hclose" with "[Hpr Hlk Hback]") as "_".
    { iNext. iApply ("Hback" with "Hpr Hlk"). }
    iModIntro. iPureIntro. by exists γ, n0, r0, h.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3d″. THE READ RECORDS

      The protected LOAD rule is the ordinary load plus a persistent record.
      The ghost is one monotone list of [(byte, log position)] pairs per
      registered lock; the mint's side condition — the position is at or
      after the footprint's registration point — is the invariant the auth
      carries, so a recorded read cannot be fabricated below [r0].  [(a, p)]
      is all the kill needs: with the footprint export at the same [r0] it
      says the byte WAS protected when the read happened. *)

  Context `{!wprotG Σ}.

  Definition prot_recs (γr : gname) (L : list (Z * nat)) : iProp Σ :=
    own γr (●ML (L : list (leibnizO (Z * nat)))).

  Definition prot_read (γr : gname) (a : Z) (p : nat) : iProp Σ :=
    (∃ L : list (Z * nat),
       own γr (◯ML (L : list (leibnizO (Z * nat)))) ∗ ⌜(a, p) ∈ L⌝)%I.

  Global Instance prot_read_persistent γr a p : Persistent (prot_read γr a p).
  Proof. rewrite /prot_read. apply _. Qed.

  Global Instance prot_recs_timeless γr L : Timeless (prot_recs γr L).
  Proof. rewrite /prot_recs. apply _. Qed.

  (** The list's own well-formedness, carried next to the auth: every record
      sits at or after the footprint's registration point. *)
  Definition prot_recs_ok (r0 : nat) (L : list (Z * nat)) : Prop :=
    forall ap, ap ∈ L -> (r0 <= ap.2)%nat.

  Lemma prot_recs_alloc : ⊢ |==> ∃ γr, prot_recs γr [].
  Proof.
    iMod (own_alloc (●ML ([] : list (leibnizO (Z * nat))))) as (γr) "H".
    { by apply mono_list_auth_valid. }
    iModIntro. by iExists γr.
  Qed.

  (** THE MINT, at a load site: append the record and keep a persistent copy
      of it. *)
  Lemma prot_recs_append γr L a p :
    prot_recs γr L ==∗ prot_recs γr (L ++ [(a, p)]) ∗ prot_read γr a p.
  Proof.
    iIntros "Ha".
    iAssert (|==> prot_recs γr (L ++ [(a, p)]))%I with "[Ha]" as ">Ha".
    { rewrite /prot_recs. iApply (own_update with "Ha").
      apply mono_list_update. by apply prefix_app_r. }
    iAssert (prot_recs γr (L ++ [(a, p)]) ∗
             own γr (◯ML ((L ++ [(a, p)]) : list (leibnizO (Z * nat)))))%I
      with "[Ha]" as "[$ #Hlb]".
    { rewrite /prot_recs -own_op -mono_list_auth_lb_op. iExact "Ha". }
    iModIntro. iExists ((L ++ [(a, p)])%list). iFrame "Hlb". iPureIntro.
    apply elem_of_app. right. by apply elem_of_list_singleton.
  Qed.

  Lemma prot_read_agree γr L a p :
    prot_recs γr L -∗ prot_read γr a p -∗ ⌜(a, p) ∈ L⌝.
  Proof.
    rewrite /prot_recs /prot_read. iIntros "Ha (%L' & Hf & %Hin)".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    apply mono_list_both_valid_L in Hv.
    iPureIntro. by eapply elem_of_prefix.
  Qed.

  (** THE SEAM, [wprot_regd] plus the record authority: one invariant holds
      the byte's [WProt] fragment, the lock word's [WLock] fragment and the
      record list, so the export can state the position bound at THE SAME
      [r0] the protection is stated at. *)
  Definition wprot_rd_regd (N : namespace) (γr : gname) (a base : Z)
      : iProp Σ :=
    (∃ I : iProp Σ,
       inv N I ∗
       □ (I -∗ ∃ (γ : gname) (n0 r0 : nat) (d : option CPU) (h : option nat)
                  (L : list (Z * nat)),
            wprot_st a γ base n0 r0 d ∗ wlock_st base base n0 h ∗
            prot_recs γr L ∗ ⌜prot_recs_ok r0 L⌝ ∗
            (wprot_st a γ base n0 r0 d -∗ wlock_st base base n0 h -∗
               prot_recs γr L -∗ I)))%I.

  Global Instance wprot_rd_regd_persistent N γr a base :
    Persistent (wprot_rd_regd N γr a base).
  Proof. rewrite /wprot_rd_regd. apply _. Qed.

  Lemma wprot_rd_regd_export (N : namespace) (E : coPset) (g : wgstate)
      (γr : gname) (a base : Z) (p : nat) :
    ↑N ⊆ E ->
    weak_state_interp g -∗ wprot_rd_regd N γr a base -∗ prot_read γr a p ={E}=∗
    ⌜exists (γ : gname) (n0 r0 : nat) (h : option nat),
       (r0 <= p)%nat /\ wprot_at (wglog g) a base n0 r0 /\
       wlp_at (wglog g) base base n0 /\ wlp_alt (wglog g) base n0 h⌝.
  Proof.
    intros HN. iIntros "Hsi #Hreg #Hrd".
    iDestruct (weak_state_interp_lat with "Hsi") as "Hlat".
    iDestruct "Hreg" as (I) "[#Hinv #Hacc]".
    iInv "Hinv" as "HI" "Hclose".
    iAssert (▷ (∃ (γ : gname) (n0 r0 : nat) (d : option CPU) (h : option nat)
                  (L : list (Z * nat)),
                  wprot_st a γ base n0 r0 d ∗ wlock_st base base n0 h ∗
                  prot_recs γr L ∗ ⌜prot_recs_ok r0 L⌝ ∗
                  (wprot_st a γ base n0 r0 d -∗ wlock_st base base n0 h -∗
                     prot_recs γr L -∗ I)))%I
      with "[HI]" as "HQ".
    { iNext. by iApply "Hacc". }
    rewrite bi.later_exist. iDestruct "HQ" as (γ) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (n0) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (r0) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (d) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (h) "HQ".
    rewrite bi.later_exist. iDestruct "HQ" as (L) "HQ".
    rewrite !bi.later_sep.
    iDestruct "HQ" as "(>Hpr & >Hlk & >Hrecs & >%Hok & Hback)".
    iDestruct (wprot_at_of_prot with "Hlat Hpr") as %Hpa.
    iDestruct (wlp_at_of_lock with "Hlat Hlk") as %Hlp.
    iDestruct (wlp_alt_of_lock with "Hlat Hlk") as %Halt.
    iDestruct (prot_read_agree with "Hrecs Hrd") as %Hin.
    iMod ("Hclose" with "[Hpr Hlk Hrecs Hback]") as "_".
    { iNext. iApply ("Hback" with "Hpr Hlk Hrecs"). }
    iModIntro. iPureIntro. exists γ, n0, r0, h.
    split_and!; [exact (Hok (a, p) Hin)|exact Hpa|exact Hlp|exact Halt].
  Qed.

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

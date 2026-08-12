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
    disk's messages [wm_tid = None] and [wm_ak = WCplain], and no [WCrel]
    message ever carries [wm_tid = None], so an agent-less [WCplain] message
    can never be published.  Clean-purity therefore EXEMPTS [wm_tid = None]:
    it constrains the messages of real agents, which is what φ's bad-edge
    shape (a cross-hart read of an unpublished owned store) is about. *)

(** [p] writes byte [a] with an owned-store ([WCplain]) message [m]. *)
Definition wplain_at (log : list wmsg) (a : Z) (p : nat) (m : wmsg) : Prop :=
  log !! p = Some m /\ is_Some (msg_byte m a) /\ wm_ak m = WCplain.

(** [p] is PUBLISHED by agent [tid]: a later message of the same agent is a
    release-class store, which raised that agent's [w_pub] past [p]. *)
Definition wpublished (log : list wmsg) (tid : option agent) (p : nat) : Prop :=
  exists (q : nat) (mq : wmsg),
    (p <= q)%nat /\ log !! q = Some mq /\ wm_tid mq = tid /\ wm_ak mq = WCrel.

Lemma wpublished_app log ms tid p :
  wpublished log tid p -> wpublished (log ++ ms) tid p.
Proof.
  intros (q & mq & Hle & Hq & Ht & Hk). exists q, mq. split_and!; try done.
  rewrite lookup_app_l //. by eapply lookup_lt_Some.
Qed.

Definition wcds_clean (log : list wmsg) (a : Z) : Prop :=
  forall p m, wplain_at log a p m ->
    wm_tid m = None \/ wpublished log (wm_tid m) p.

Definition wcds_dirty (log : list wmsg) (a : Z) (c : CPU) : Prop :=
  forall p m, wplain_at log a p m ->
    wm_tid m = None \/ wpublished log (wm_tid m) p \/
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
(** ** 3. The resources *)

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
     ⌜wlog_wf σ.(wm_log)⌝ ∗
     reg_interp σ.(wm_regs) ∗
     dev_interp σ.(wm_dev) ∗
     wlog_auth σ.(wm_log) ∗
     wlat_interp σ.(wm_img) σ.(wm_log) ∗
     wws_auth cpu_id σ.(wm_ws))%I.

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

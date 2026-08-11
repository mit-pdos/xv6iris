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

Class weakGpreS (Σ : gFunctors) := WeakGpreS {
  weak_pre_logG :: inG Σ wlogR;
  weak_pre_latG :: ghost_mapG Σ Z (nat * bv 8);
  weak_pre_wsG :: ghost_varG Σ wstate;
  (* the MONOTONE SHADOW of [weak_pre_wsG] — see [weak_view_name] below *)
  weak_pre_viewG :: weakViewG Σ;
}.

Definition weakΣ : gFunctors :=
  #[ GFunctor wlogR; ghost_mapΣ Z (nat * bv 8); ghost_varΣ wstate;
     weakViewΣ ].

Global Instance subG_weakGpreS Σ : subG weakΣ Σ -> weakGpreS Σ.
Proof. intros H. split; try (revert H; solve_inG). Qed.

Class weakGS (Σ : gFunctors) := WeakGS {
  weak_preGS :: weakGpreS Σ;
  weak_log_name : gname;
  weak_lat_name : gname;
  (* PER HART, like [era_reg_name] (see the header's DEVIATION note) *)
  weak_ws_name : CPU -> gname;
  (* PER HART, and the MONOTONE SHADOW of the one above: [weak_ws_name]'s
     [ghost_var] is exact-valued, which is why a leaf can only step it by
     naming both states, and hence why every caller above a leaf had to
     name them too.  [weak_view_name] carries the same [wstate] in a
     [mono_nat]/max-fun authority, where "it only grows" is free.  Both are
     client-side halves of ONE fact, kept in step by [hart_view] below; the
     state interpretation is untouched by this field. *)
  weak_view_name : CPU -> wview_names;
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

  Definition wlat_pointsto (a : Z) (dq : dfrac) (t : nat) (v : bv 8) : iProp Σ :=
    ghost_map_elem weak_lat_name a dq (t, v).

  Definition wlat_interp (img : _) (log : list wmsg) : iProp Σ :=
    (∃ m, ghost_map_auth weak_lat_name 1 m ∗ ⌜wlat_agree (img_z img) log m⌝)%I.

  (** THE READ BRIDGE: my element IS the latest write.  This is what an M2
      load leaf turns into "every admissible timestamp returns [v]". *)
  Lemma wlat_lookup img log a dq t v :
    wlat_interp img log -∗ wlat_pointsto a dq t v -∗
    ⌜latest_val (img_z img) log a t v⌝.
  Proof.
    iIntros "Hi He". iDestruct "Hi" as (m) "[Hauth %Hag]".
    iDestruct (ghost_map_lookup with "Hauth He") as %Hlk.
    iPureIntro. exact (Hag a (t, v) Hlk).
  Qed.

  (** The accessor M2's store leaf uses: take the authority out, update the
      elements of the bytes the store wrote, put it back at the new log. *)
  Lemma wlat_interp_acc img log :
    wlat_interp img log -∗
    ∃ m, ghost_map_auth weak_lat_name 1 m ∗ ⌜wlat_agree (img_z img) log m⌝ ∗
      (∀ m' log', ghost_map_auth weak_lat_name 1 m' -∗
         ⌜wlat_agree (img_z img) log' m'⌝ -∗ wlat_interp img log').
  Proof.
    iIntros "Hi". iDestruct "Hi" as (m) "[Hauth %Hag]".
    iExists m. iFrame "Hauth". iSplitR; [iPureIntro; exact Hag|].
    iIntros (m' log') "Hauth' %Hag'". iExists m'. by iFrame "Hauth'".
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

      This is what everything above a leaf threads, and the reason it can
      be threaded is the pairing: inside the existential the exact
      [hart_ws] value and the monotone authority's value are THE SAME
      [wstate], so a floor read off the authority is a floor on the real
      hart view.  Outside, neither value is nameable — which is the whole
      point, since naming them is what forced the [ws]/[ws']/[ws_le]
      residue on every caller.

      Note what is NOT here: [weak_view_name]'s authority never appears in
      the state interpretation.  It is a purely client-side shadow, kept
      honest by [hart_view_step] below being the only way to move it. *)
  Definition hart_view (c : CPU) : iProp Σ :=
    (∃ ws : wstate, hart_ws c ws ∗ ws_auth (weak_view_name c) ws)%I.

  Lemma hart_view_intro c ws :
    hart_ws c ws -∗ ws_auth (weak_view_name c) ws -∗ hart_view c.
  Proof. iIntros "H1 H2". iExists ws. iFrame. Qed.

  (** THE CONVERSION EVERY LEAF WRAPPER USES.  Open the token at some
      unknown [ws], run the underlying leaf (which does name both states),
      and close it at [ws'] — the [ws_le] the leaf hands back is exactly
      what [ws_update] needs, so it is consumed here and never reaches the
      caller. *)
  Lemma hart_view_open c :
    hart_view c -∗ ∃ ws, hart_ws c ws ∗ ws_auth (weak_view_name c) ws.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma hart_view_close c ws ws' :
    ws_le ws ws' ->
    ws_auth (weak_view_name c) ws -∗ hart_ws c ws' ==∗ hart_view c.
  Proof.
    iIntros (Hle) "Hauth Hws".
    iMod (ws_update _ _ ws' with "Hauth") as "Hauth"; [exact Hle|].
    iModIntro. iExists ws'. iFrame.
  Qed.

  (** Snapshotting a floor: the only thing a caller can learn from the
      token, and being persistent it never has to be given back.  Code that
      does NOT care about views — every lock-disciplined function — never
      calls this. *)
  Lemma hart_view_lb c :
    hart_view c -∗ ∃ ws, hart_view c ∗ ws_lb (weak_view_name c) ws.
  Proof.
    iIntros "[%ws [Hws Hauth]]".
    iDestruct (ws_lb_get with "Hauth") as "#Hlb".
    iExists ws. iFrame "Hlb". iExists ws. iFrame.
  Qed.

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

(** * WeakViolation.v — φ: violation-freedom as a pure predicate, and the
      [w_pub] bridge (φ-upgrade, deliverable B)

    The payoff side of the C/D/S points-to surgery
    ([claude-notes/design/weak-memory-phi-upgrade.md] §1/§1b): the pure
    predicate the state interpretation is meant to carry, its three
    discharge lemmas off the C/D/S invariants, the induction algebra a
    step's reassembly needs, and the one machine fact the φ EXPORT owes
    Layer 1 (the tie between [WeakGhost.wpublished] — a predicate of the
    LOG — and the author's [WeakMem.w_pub] watermark, which is what
    [WeakRobustMain.pub_of] reads).

    STATEMENT ALIGNMENT (checked by hand against [WeakRobust.violation]
    and [WeakRobustMain.pub_of], which this file deliberately does NOT
    import — Layer 1 is Iris-free and stays that way):

      [WeakRobust.violation cls pub c] is
        ∃ p m i j a, pc_log c !! p = Some m ∧ wm_tid m = Some i ∧
          cls m = SCowned ∧ ¬ pub c (S p) ∧ j ≠ i ∧
          is_Some (msg_byte m a) ∧ (S p ≤ obs_flr c j a)%nat

      [no_violation log wsf] below is its negation with
        · [cls m = SCowned]        ↦ [wm_ak m = WCplain]
          (exactly [WeakRobustMain.cls_of]'s first arm),
        · [pub c (S p)]            ↦ [wpublished log (wm_tid m) p]
          (§4 below bridges the two),
        · [obs_flr c j a]          ↦ [coh (wsf c') a]
          ([obs_flr] IS the agent's [coh], [WeakRobust]'s header),
        · the agents [i]/[j]       ↦ [CPU]s.
    THE DELIBERATE GAP is the agent quantifier: [no_violation] constrains
    only messages whose [wm_tid] is a HART.  That is the surgery's Delta 2
    ([wm_tid = None] — the DMA/boot agent — is exempted from the C/D/S
    invariants and can never be published), and it is why Layer 1's [bad]
    predicate must carry "the message's tid is a hart"; the design file's
    DMA-tid unification (seam 1c/d) closes the gap from the other side.

    NO IRIS BELOW §3.  §§1–2 are [Prop]s over [WeakMem]'s vocabulary; §3
    is the two-line bridge from the C/D/S ghost elements. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

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

(** The DEVICE/DMA arm.  [WeakLang.wmsgs_of_map] stamps [wm_tid = None],
    so a disk append adds no obligation at all, and no hart's floor moves:
    the conjunct survives by [nv_hart_app] alone.  (The DMA messages are
    [WCplain] but agent-less — the surgery's Delta 2.) *)
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
  - rewrite Ht in Hn. discriminate.
  - by destruct (Hnp Hpub).
Qed.

Lemma nv_byte_dirty log c a n : wcds_dirty log a c -> nv_byte log c a n.
Proof.
  intros Hdi p m c0 Hp Ht Hk Hnp Hs Hne.
  destruct (Hdi p m (conj Hp (conj Hs Hk))) as [Hn|[Hpub|Hc]].
  - rewrite Ht in Hn. discriminate.
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

Section resources.
  Context `{!riscvGS Σ, !weakGS Σ}.

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

End resources.

(* ====================================================================== *)
(** ** 4. THE [w_pub] BRIDGE — the machine fact the φ export owes Layer 1

    [WeakGhost.wpublished] is a predicate of the LOG ("some later message of
    the same agent is [WCrel]"), which is what let the C/D/S invariant keep
    [wlat_interp]'s arity (φ-upgrade §1b, delta 1).  Layer 1's
    [WeakRobustMain.pub_of] instead reads the AUTHOR's inert [w_pub]
    watermark: [pub_of c (S p)] is [∃ …, pc_ags c !! i = Some ag ∧
    (S p ≤ w_pub (pa_ws ag))%nat].  The two are tied by [wpub_covers]
    below, which is exactly "the author's watermark has caught up with every
    [WCrel] message of its own that the log contains".

    WHY THAT IS THE HONEST PREMISE.  It is NOT a conjunct of any state
    interpretation today, so it cannot be assumed; and it is not derivable
    from [ws_bounded] (which bounds [w_pub] from ABOVE, the wrong
    direction).  It IS a machine invariant — §4b proves the three
    preservation steps — of the same character as [ws_bounded], i.e.
    resource-free and provable by a [wrun]-level induction; the design note
    calls it "the hart's wstate is the fold of its own log messages", and
    [wpub_covers] is that statement's [w_pub] projection.

    THE ONE CAVEAT, and it is real: a ZERO-WIDTH release-class write.
    [WeakMem.store_post_run] folds per BYTE, so a width-0 store appends a
    [WCrel] message (its class comes from [WeakInterp.wm_class_of], which
    does not look at the width) while raising nothing.  [wpublished] would
    then hold with no [w_pub] behind it.  [WeakEff]'s header records that
    the interface admits zero-width accesses and that the generated model
    emits none; §4b's store step therefore carries [(0 < N.to_nat n)%nat]
    explicitly rather than hiding the assumption. *)

Definition wpub_covers (log : list wmsg) (i : agent) (ws : wstate) : Prop :=
  forall (q : nat) (mq : wmsg),
    log !! q = Some mq -> wm_tid mq = Some i -> wm_ak mq = WCrel ->
    (S q <= w_pub ws)%nat.

(** THE BRIDGE.  One line, as advertised. *)
Lemma wpublished_w_pub (log : list wmsg) (i : agent) (ws : wstate) (p : nat) :
  wpub_covers log i ws -> wpublished log (Some i) p -> (S p <= w_pub ws)%nat.
Proof.
  intros Hcov (q & mq & Hle & Hq & Ht & Hk). pose proof (Hcov q mq Hq Ht Hk). lia.
Qed.

(** The φ-export shape, at the hart index the state interpretation uses. *)
Lemma wpublished_w_pub_cpu (log : list wmsg) (c : CPU) (ws : wstate) (p : nat) :
  wpub_covers log (fin_to_nat c) ws ->
  wpublished log (Some (fin_to_nat c)) p -> (S p <= w_pub ws)%nat.
Proof. apply wpublished_w_pub. Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4b. [wpub_covers] IS an invariant — the three preservation steps *)

Lemma wpub_covers_nil i ws : wpub_covers [] i ws.
Proof. intros q mq Hq. by rewrite lookup_nil in Hq. Qed.

Lemma wpub_covers_mono log i ws ws' :
  wpub_covers log i ws -> (w_pub ws <= w_pub ws')%nat -> wpub_covers log i ws'.
Proof. intros H Hle q mq Hq Ht Hk. pose proof (H q mq Hq Ht Hk). lia. Qed.

(** A FOREIGN append (another hart's messages, or the disk's) adds no
    obligation to this agent's watermark. *)
Lemma wpub_covers_app_foreign log ms i ws :
  wpub_covers log i ws -> (forall m, m ∈ ms -> wm_tid m <> Some i) ->
  wpub_covers (log ++ ms) i ws.
Proof.
  intros H Hfor q mq Hq Ht Hk.
  apply lookup_app_Some in Hq as [Hq|[_ Hq]]; [exact (H q mq Hq Ht Hk)|].
  exfalso. apply elem_of_list_lookup_2, Hfor in Hq. by apply Hq.
Qed.

(** A READ moves neither the log nor [w_pub]. *)
Lemma w_pub_load_post_at ws aq vpre a t : w_pub (load_post_at ws aq vpre a t) = w_pub ws.
Proof. reflexivity. Qed.

Lemma w_pub_foldl_load (aq : bool) (v : nat) ats :
  forall w, w_pub (foldl (fun w at_ => load_post_at w aq v at_.1 at_.2) w ats)
            = w_pub w.
Proof. induction ats as [|at_ ats IH]; intros w; [reflexivity|by rewrite /= IH]. Qed.

Lemma w_pub_load_post_bytes ws aq ats : w_pub (load_post_bytes ws aq ats) = w_pub ws.
Proof. apply w_pub_foldl_load. Qed.

Lemma wpub_covers_read (s : wmstate) (i : agent) ak pa ts :
  wpub_covers (wm_log s) i (wm_ws s) ->
  wpub_covers (wm_log (wread_post s ak pa ts)) i (wm_ws (wread_post s ak pa ts)).
Proof.
  intros H. rewrite wread_post_log. eapply wpub_covers_mono; [exact H|].
  rewrite /wread_post. destruct (ak_coh ak); [reflexivity|].
  rewrite /wset_ws /= /load_post_run w_pub_load_post_bytes. reflexivity.
Qed.

(** A BARRIER moves neither. *)
Lemma wpub_covers_bar (log : list wmsg) (i : agent) ws b :
  wpub_covers log i ws -> wpub_covers log i (barrier_post ws b).
Proof.
  intros H. eapply wpub_covers_mono; [exact H|].
  rewrite /barrier_post. by destruct b.
Qed.

(** THE STORE STEP, the only one with content.  A store folds
    [WeakMem.store_post] over the access's bytes at the fresh top
    [S (length log)]; if the message's class is [WCrel] then
    [WeakInterp.wm_class_of] says the release-pending flag or the [.rl] bit
    is set, which is exactly [store_post]'s raise condition — so the FIRST
    byte lifts [w_pub] to the message's own timestamp and no later byte can
    lower it. *)
Lemma w_pub_store_post ws rl a t :
  (w_pub ws <= w_pub (store_post ws rl a t))%nat.
Proof. rewrite /store_post /=. destruct (w_relp ws || rl)%bool; lia. Qed.

Lemma w_pub_store_post_raise ws rl a t :
  (w_relp ws || rl)%bool = true -> (t <= w_pub (store_post ws rl a t))%nat.
Proof. intros Hr. rewrite /store_post /= Hr. lia. Qed.

Lemma w_pub_foldl_store_mono (rl : bool) as_ (t : nat) :
  forall w, (w_pub w <= w_pub (foldl (fun w a => store_post w rl a t) w as_))%nat.
Proof.
  induction as_ as [|a as_ IH]; intros w; [reflexivity|].
  simpl. etrans; [apply (w_pub_store_post w rl a t)|apply IH].
Qed.

Lemma w_pub_store_post_bytes_mono ws rl as_ t :
  (w_pub ws <= w_pub (store_post_bytes ws rl as_ t))%nat.
Proof. apply w_pub_foldl_store_mono. Qed.

Lemma w_pub_store_post_bytes_raise ws rl as_ t a0 as0 :
  as_ = a0 :: as0 -> (w_relp ws || rl)%bool = true ->
  (t <= w_pub (store_post_bytes ws rl as_ t))%nat.
Proof.
  intros -> Hr. rewrite /store_post_bytes /=.
  etrans; [exact (w_pub_store_post_raise ws rl a0 t Hr)|].
  apply (w_pub_store_post_bytes_mono (store_post ws rl a0 t) rl as0 t).
Qed.

Lemma w_pub_store_post_run_raise ws rl base n t :
  (0 < n)%nat -> (w_relp ws || rl)%bool = true ->
  (t <= w_pub (store_post_run ws rl base n t))%nat.
Proof.
  intros Hn Hr. rewrite /store_post_run.
  destruct n as [|n]; [lia|].
  apply (w_pub_store_post_bytes_raise ws rl _ t (base + Z.of_nat 0)
           (map (fun j : nat => base + Z.of_nat j) (seq 1 n)));
    [reflexivity|exact Hr].
Qed.

Lemma w_pub_store_post_run_mono ws rl base n t :
  (w_pub ws <= w_pub (store_post_run ws rl base n t))%nat.
Proof. apply w_pub_store_post_bytes_mono. Qed.

Lemma wpub_covers_write (tid : option nat) (i : agent) (s : wmstate)
    ak pa (n : N) (v : bv (8 * n)) :
  tid = Some i ->
  (0 < N.to_nat n)%nat ->
  wpub_covers (wm_log s) i (wm_ws s) ->
  wpub_covers (wm_log (wwrite_post tid s ak pa n v)) i
              (wm_ws (wwrite_post tid s ak pa n v)).
Proof.
  intros -> Hn H q mq Hq Ht Hk.
  rewrite wwrite_post_log in Hq. rewrite /wwrite_post /=.
  apply lookup_app_Some in Hq as [Hq|[Hge Hq]].
  - etrans; [exact (H q mq Hq Ht Hk)|]. apply w_pub_store_post_run_mono.
  - (* the fresh message: its class is [WCrel], so the store published *)
    destruct (q - length (wm_log s))%nat as [|k] eqn:Hk2; simpl in Hq;
      [|by rewrite lookup_nil in Hq].
    injection Hq as <-. rewrite /wwrite_msg /= in Hk.
    assert (Hq' : q = length (wm_log s)) by lia. subst q.
    apply w_pub_store_post_run_raise; [exact Hn|].
    rewrite /wm_class_of in Hk. destruct (ak_latest ak); [discriminate|].
    by destruct (w_relp (wm_ws s) || ak_sync ak)%bool.
Qed.

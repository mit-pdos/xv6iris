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

    WHERE THE PREDICATE LIVES.  §§1–3 (the predicate, its induction algebra
    and the three C/D/S discharge arms) MOVED INTO [WeakGhost] when the
    conjunct landed: [weak_state_interp] / [wmstate_interp] are defined there
    and now carry it, and [WeakGhost] is upstream of this file.  What is left
    here is §4, the [w_pub] bridge — the one machine fact the φ EXPORT owes
    Layer 1, which nothing in the Iris tower consumes. *)
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

(** THE SAME BRIDGE FOR THE PUBLICATION-FLOOR TOKEN (φ-upgrade §1.5).
    [WeakGhost.pub_floor c n] is spelled over the LOG (a [wlog_lb] snapshot in
    which [c] has already released) rather than as a [WeakViewMono] [w_pub]
    lower bound — see [WeakGhost]'s §3a' for why (the [w_pub] authority is not
    threaded, and the arm would need the CONVERSE of [wpublished_w_pub], which
    is not a machine invariant).  This records that nothing is LOST by that
    choice: under the same honest premise the two readings coincide, so a
    ported spec may state the token either way. *)
Lemma wpub_upto_w_pub (log : list wmsg) (i : agent) (ws : wstate) (n : nat) :
  wpub_covers log i ws -> wpub_upto log (Some i) n -> (n <= w_pub ws)%nat.
Proof.
  intros Hcov (q & mq & Hle & Hq & Ht & Hk).
  pose proof (Hcov q mq Hq Ht Hk). lia.
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

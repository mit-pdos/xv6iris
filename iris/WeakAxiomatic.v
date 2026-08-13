(** * WeakAxiomatic.v — the axiomatic characterization of the promise-free machine

    W4 of the M6 robustness effort ([claude-notes/projects/weak-memory-m6.md]):
    the conjectured characterization

        promise-free machine  ≡  RVWMO ∧ acyclic(po ∪ rf) ∧ (po ∩ W×W) ⊆ gmo

    ([claude-notes/design/weak-memory-m6-robustness.md] §6).  THIS FILE IS
    SLICE 1: the event vocabulary, the axioms as definitions, and the SOUNDNESS
    direction (every promise-free machine execution induces an axiomatic
    execution satisfying the axioms).  Completeness — axiomatically-consistent
    implies machine-reachable — is slice 2 and appears here only as a commented
    conjecture at the very bottom.

    SCOPE (W4's own scope decision): the axiomatic side is "RVWMO minus
    ppo 9–13".  Syntactic address/data/control dependencies are NOT modelled,
    matching design Decision 3 (the machine tracks no register views).

    DELIBERATELY DEPENDENCY-FREE, like [WeakMem.v]: this file imports stdpp and
    [WeakMem] and nothing else.  No Iris, no Sail.

    ------------------------------------------------------------------------
    WHY THERE IS A MACHINE DEFINITION IN THIS FILE AT ALL

    [WeakMem.v] defines the memory model's STEP FUNCTIONS ([load_post_run],
    [store_post_run], [fence_post]) and their side conditions ([readable],
    [latest]) but no whole-machine step relation: the tree's two consumers each
    build their own ([WeakLitmus.lstep] over a toy instruction language,
    [WeakInterp.wrun] over Sail).  An axiomatic characterization needs a notion
    of "execution", so this file supplies the minimal one: an EVENT-LABELLED
    transition system whose labels are exactly the memory-model-visible effects
    and whose steps are exactly [WeakMem]'s rules.  Both existing consumers
    project onto it (the projection is not proved here — see the report's
    friction list).

    Every modelling choice is flagged with `MODELLING CHOICE` in a comment. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The label alphabet

    MODELLING CHOICE (events).  ONE MACHINE STEP = ONE EVENT.  An event is a
    whole (possibly multi-byte) access, not a byte; byte structure is carried
    INSIDE the label as the per-byte timestamp list, and the relations that
    need byte granularity ([rf], [co], [fr], per-byte coherence) are indexed by
    a byte address.  Rationale: [po] and the fence rules are per-STEP in the
    machine ([load_post_run] folds one pre-view over all bytes of one access),
    so splitting an access into per-byte events would have to re-invent a
    within-access order that the machine does not have.

    MODELLING CHOICE (byte addressing).  Byte [j] of an access based at [base]
    lives at [base + j] — the same additive seam [WeakMem.load_post_run] and
    [WeakInterp.acc_addr] use. *)

Definition acc_addr (base : Z) (j : nat) : Z := base + Z.of_nat j.

Lemma acc_addr_inj base j j' : acc_addr base j = acc_addr base j' → j = j'.
Proof. rewrite /acc_addr. lia. Qed.

(** MODELLING CHOICE (the alphabet).  Four labels, mirroring the four arms of
    the design doc's step rules (Decision 2):

    - [LLoad aq base ts vs]   — a load of [|ts|] bytes at [base..], byte [j]
      reading timestamp [ts !! j] and obtaining value [vs !! j];
    - [LStore rl base vs k]   — a store appending ONE message of class [k];
    - [LFence pr pw sr sw]    — FENCE pred,succ with the four kind bits;
    - [LRmw aq rl base ts rvs wvs k] — an AMO: read half + write half in ONE
      step (the design doc's AMO paragraph), with the read half constrained to
      the globally-latest message per byte.

    THE CLASS FIELD [k : wm_class] (M6 D-M6-6) is INERT — no rule and no
    relation of the axiomatic model inspects it.  It is on the LABEL rather
    than computed from the state because [WeakAxiomatic2]'s replay makes the
    post-state (and hence the appended message) a FUNCTION of the label
    ([mnext], [es_msg]); the machines that project into [exec]
    ([WeakInterp] via [WeakInterpProj], [WeakLitmus] via [WeakLitmusProj],
    [WeakPromise] via [WeakPromiseBridge]) each supply the class their own
    append used, which is what keeps the projected logs literally equal.

    What is deliberately NOT in the alphabet: LR/SC (the kernel uses none —
    design Decision 2), the [ak_coh] "coherent read" arm of [WeakInterp]
    (dead for rv64d — design Decision 6: fetch and page-table walks are plain
    weak loads, hence [LLoad]), and any dependency/register information
    (Decision 3, and W4's scope decision). *)
Inductive lbl :=
| LLoad (aq : bool) (base : Z) (ts : list nat) (vs : list (bv 8))
| LStore (rl : bool) (base : Z) (vs : list (bv 8)) (k : wm_class)
| LFence (pr pw sr sw : bool)
| LRmw (aq rl : bool) (base : Z) (ts : list nat) (rvs wvs : list (bv 8))
       (k : wm_class).

(** MODELLING CHOICE (agents).  A step names its agent; harts and the disk
    agent are the same kind of thing (decision D-M6-4: "devices = the simple
    disk agent, uniformly", one more agent of the same LTS).  Consequently
    every message this machine appends carries [wm_tid = Some i]; the
    [wm_tid = None] slot is used by NO step here — such writes belong to the
    era-initial image instead.  SINCE THE DMA-TID UNIFICATION (seam 1a of
    [claude-notes/completed/weak-memory-lift.md]) the operational machine
    agrees: [WeakLang.wmsgs_of_map] stamps [Some WeakLang.n_disk], so
    [wm_tid = None] is now unreachable on BOTH sides and the modelling
    choice above costs nothing at the seam. *)
Record estep := EStep { es_ag : agent; es_lb : lbl }.

Record mstate := MSt {
  ms_img : image;
  ms_log : list wmsg;
  ms_ws  : agent → wstate;
}.

Definition upd_ws (f : agent → wstate) (i : agent) (w : wstate) : agent → wstate :=
  λ j, if bool_decide (j = i) then w else f j.

Lemma upd_ws_eq f i w : upd_ws f i w i = w.
Proof. rewrite /upd_ws bool_decide_eq_true_2 //. Qed.

Lemma upd_ws_ne f i w j : j ≠ i → upd_ws f i w j = f j.
Proof. intros ?. rewrite /upd_ws bool_decide_eq_false_2 //. Qed.

(* ------------------------------------------------------------------ *)
(** ** The step relation *)

(** One byte of a load: it returns [v] from timestamp [t], and [t] is
    admissible at the load's pre-view. *)
Definition byte_rd (img : image) (log : list wmsg) (ws : wstate) (aq : bool)
    (a : Z) (t : nat) (v : bv 8) : Prop :=
  log_byte img log t a = Some v ∧ readable img log ws (load_vpre ws aq) a t.

Definition rd_ok (img : image) (log : list wmsg) (ws : wstate) (aq : bool)
    (base : Z) (ts : list nat) (vs : list (bv 8)) : Prop :=
  length vs = length ts ∧
  ∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
    byte_rd img log ws aq (acc_addr base j) t v.

(** The AMO's atomicity side condition: every byte of the read half takes the
    globally-latest message ([WeakMem.latest], which pins it uniquely). *)
Definition rmw_latest (img : image) (log : list wmsg) (base : Z) (ts : list nat)
    : Prop :=
  ∀ (j : nat) t, ts !! j = Some t → latest img log (acc_addr base j) t.

Inductive mstep (σ : mstate) (i : agent) : lbl → mstate → Prop :=
| MStepLoad aq base ts vs :
    rd_ok (ms_img σ) (ms_log σ) (ms_ws σ i) aq base ts vs →
    mstep σ i (LLoad aq base ts vs)
      (MSt (ms_img σ) (ms_log σ)
         (upd_ws (ms_ws σ) i (load_post_run (ms_ws σ i) aq base ts)))
| MStepStore rl base vs k :
    vs ≠ [] →
    mstep σ i (LStore rl base vs k)
      (MSt (ms_img σ) (ms_log σ ++ [WMsg base vs (Some i) k])
         (upd_ws (ms_ws σ) i
            (store_post_run (ms_ws σ i) rl base (length vs)
               (S (length (ms_log σ))))))
| MStepFence pr pw sr sw :
    mstep σ i (LFence pr pw sr sw)
      (MSt (ms_img σ) (ms_log σ)
         (upd_ws (ms_ws σ) i (fence_post (ms_ws σ i) pr pw sr sw)))
| MStepRmw aq rl base ts rvs wvs k :
    wvs ≠ [] → length wvs = length ts →
    rd_ok (ms_img σ) (ms_log σ) (ms_ws σ i) aq base ts rvs →
    rmw_latest (ms_img σ) (ms_log σ) base ts →
    mstep σ i (LRmw aq rl base ts rvs wvs k)
      (MSt (ms_img σ) (ms_log σ ++ [WMsg base wvs (Some i) k])
         (upd_ws (ms_ws σ) i
            (store_post_run (load_post_run (ms_ws σ i) aq base ts) rl base
               (length wvs) (S (length (ms_log σ)))))).

(** Label classification. *)
Definition lb_is_w (l : lbl) : bool :=
  match l with LStore _ _ _ _ | LRmw _ _ _ _ _ _ _ => true | _ => false end.
Definition lb_is_r (l : lbl) : bool :=
  match l with LLoad _ _ _ _ | LRmw _ _ _ _ _ _ _ => true | _ => false end.
Definition lb_aq (l : lbl) : bool :=
  match l with LLoad aq _ _ _ => aq | LRmw aq _ _ _ _ _ _ => aq | _ => false end.

(** The INERT class the label's write half publishes (see the alphabet
    comment); [WCplain] on the non-writing labels, where it is never read. *)
Definition lb_cls (l : lbl) : wm_class :=
  match l with LStore _ _ _ k => k | LRmw _ _ _ _ _ _ k => k | _ => WCplain end.

(** The read footprint: base, per-byte timestamps, per-byte values. *)
Definition lb_rd (l : lbl) : option (Z * list nat * list (bv 8)) :=
  match l with
  | LLoad _ base ts vs => Some (base, ts, vs)
  | LRmw _ _ base ts rvs _ _ => Some (base, ts, rvs)
  | _ => None
  end.

(** The write footprint: base and the bytes written. *)
Definition lb_wr (l : lbl) : option (Z * list (bv 8)) :=
  match l with
  | LStore _ base vs _ => Some (base, vs)
  | LRmw _ _ base _ _ wvs _ => Some (base, wvs)
  | _ => None
  end.

Lemma lb_is_w_wr l : lb_is_w l = true → ∃ base vs, lb_wr l = Some (base, vs).
Proof. destruct l; try done; intros _; eauto. Qed.

Lemma lb_is_r_rd l :
  lb_is_r l = true → ∃ base ts vs, lb_rd l = Some (base, ts, vs).
Proof. destruct l; try done; intros _; eauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** Per-step facts *)

Lemma mstep_img σ i l σ' : mstep σ i l σ' → ms_img σ' = ms_img σ.
Proof. by inversion 1. Qed.

Lemma mstep_log_nw σ i l σ' :
  mstep σ i l σ' → lb_is_w l = false → ms_log σ' = ms_log σ.
Proof. by inversion 1. Qed.

Lemma mstep_log_w σ i l σ' :
  mstep σ i l σ' → lb_is_w l = true →
  ∃ base vs, lb_wr l = Some (base, vs) ∧ vs ≠ [] ∧
             ms_log σ' = ms_log σ ++ [WMsg base vs (Some i) (lb_cls l)].
Proof. inversion 1; try done; intros _; eauto. Qed.

Lemma mstep_log_prefix σ i l σ' : mstep σ i l σ' → ms_log σ `prefix_of` ms_log σ'.
Proof.
  intros Hs. destruct (lb_is_w l) eqn:Hw.
  - destruct (mstep_log_w _ _ _ _ Hs Hw) as (base & vs & _ & _ & ->).
    by apply prefix_app_r.
  - rewrite (mstep_log_nw _ _ _ _ Hs Hw) //.
Qed.

Lemma mstep_ws_ne σ i l σ' j : mstep σ i l σ' → j ≠ i → ms_ws σ' j = ms_ws σ j.
Proof. intros Hs Hne. inversion Hs; simpl; by rewrite upd_ws_ne. Qed.

Lemma mstep_ws_le σ i l σ' j : mstep σ i l σ' → ws_le (ms_ws σ j) (ms_ws σ' j).
Proof.
  intros Hs. destruct (decide (j = i)) as [->|Hne];
    [|rewrite (mstep_ws_ne _ _ _ _ _ Hs Hne); reflexivity].
  inversion Hs; simpl; rewrite upd_ws_eq.
  - apply load_post_run_le.
  - apply store_post_run_le.
  - apply fence_post_le.
  - etrans; [apply load_post_run_le|apply store_post_run_le].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Executions

    MODELLING CHOICE (executions).  An execution is a list of STATES together
    with a list of STEPS, related pointwise, rather than an [rtc]-style
    reachability proof.  Rationale: the event identity we need is "position in
    the run" (the axiomatic proofs all embed relations into execution order),
    and with an explicit state list every event's pre- and post-state is a
    lookup rather than an induction. *)

Record exec := Exec { ex_st : list mstate; ex_tr : list estep }.

(** MODELLING CHOICE (the era-initial image).  Timestamp 0 is the image, as in
    [WeakMem.log_byte]; the initial LOG IS REQUIRED TO BE EMPTY.  At the event
    level timestamp 0 is reified as a single VIRTUAL INIT WRITE EVENT
    [ev_init], which writes exactly the bytes the image defines and is
    [gmo]-below every other write.  Requiring the log empty is what makes
    "every timestamp above 0 has a unique writer event in this run" true, and
    it is what the machine does anyway (design Decision 6: a PowerOn resets
    [glog] to empty over the boot image).

    The initial per-agent states are [ws_init] (all views 0, empty forward
    bank): the forward-bank invariant [exec_fwd_tid] below needs it. *)
Definition exec_wf (E : exec) : Prop :=
  length (ex_st E) = S (length (ex_tr E)) ∧
  (∀ σ0, ex_st E !! 0%nat = Some σ0 → ms_log σ0 = [] ∧ ∀ i, ms_ws σ0 i = ws_init) ∧
  (∀ k s σ σ', ex_tr E !! k = Some s → ex_st E !! k = Some σ →
               ex_st E !! S k = Some σ' → mstep σ (es_ag s) (es_lb s) σ').

(** Total accessors.  [stt E k] is junk outside the run; every lemma that uses
    it carries the [k ≤ length (ex_tr E)] guard. *)
Definition ms_junk : mstate := MSt (λ _, None) [] (λ _, ws_init).
Definition stt (E : exec) (k : nat) : mstate := default ms_junk (ex_st E !! k).
Definition elog (E : exec) (k : nat) : list wmsg := ms_log (stt E k).
Definition eimg (E : exec) (k : nat) : image := ms_img (stt E k).
Definition ews (E : exec) (k : nat) (i : agent) : wstate := ms_ws (stt E k) i.

Lemma stt_lookup E k σ : ex_st E !! k = Some σ → stt E k = σ.
Proof. rewrite /stt => -> //. Qed.

Lemma exec_st_len E k : exec_wf E → (k ≤ length (ex_tr E))%nat → is_Some (ex_st E !! k).
Proof.
  intros (Hlen & _ & _) Hk. apply lookup_lt_is_Some_2. lia.
Qed.

(** The one lemma that unpacks [exec_wf]'s step clause at the total
    accessors. *)
Lemma exec_step_at E k s :
  exec_wf E → ex_tr E !! k = Some s →
  mstep (stt E k) (es_ag s) (es_lb s) (stt E (S k)).
Proof.
  intros Hwf Hs. pose proof (lookup_lt_Some _ _ _ Hs) as Hlt.
  destruct Hwf as (Hlen & _ & Hstep).
  destruct (lookup_lt_is_Some_2 (ex_st E) k ltac:(lia)) as [σ Hσ].
  destruct (lookup_lt_is_Some_2 (ex_st E) (S k) ltac:(lia)) as [σ' Hσ'].
  rewrite (stt_lookup _ _ _ Hσ) (stt_lookup _ _ _ Hσ').
  by eapply Hstep.
Qed.

Lemma exec_tr_lookup E k : (k < length (ex_tr E))%nat → is_Some (ex_tr E !! k).
Proof. apply lookup_lt_is_Some_2. Qed.

(** Structural monotonicity along a run. *)
Lemma exec_log_prefix E k k' :
  exec_wf E → (k ≤ k')%nat → (k' ≤ length (ex_tr E))%nat →
  elog E k `prefix_of` elog E k'.
Proof.
  intros Hwf Hle Hk'. induction k' as [|k' IH].
  { assert (k = 0%nat) as -> by lia. reflexivity. }
  destruct (decide (k = S k')) as [->|Hne]; [reflexivity|].
  etrans; [apply IH; lia|].
  destruct (exec_tr_lookup E k' ltac:(lia)) as [s Hs].
  apply (mstep_log_prefix _ _ _ _ (exec_step_at E k' s Hwf Hs)).
Qed.

Lemma exec_log_len_le E k k' :
  exec_wf E → (k ≤ k')%nat → (k' ≤ length (ex_tr E))%nat →
  (length (elog E k) ≤ length (elog E k'))%nat.
Proof.
  intros. apply prefix_length. by apply exec_log_prefix.
Qed.

Lemma exec_ws_le E k k' i :
  exec_wf E → (k ≤ k')%nat → (k' ≤ length (ex_tr E))%nat →
  ws_le (ews E k i) (ews E k' i).
Proof.
  intros Hwf Hle Hk'. induction k' as [|k' IH].
  { assert (k = 0%nat) as -> by lia. reflexivity. }
  destruct (decide (k = S k')) as [->|Hne]; [reflexivity|].
  etrans; [apply IH; lia|].
  destruct (exec_tr_lookup E k' ltac:(lia)) as [s Hs].
  apply (mstep_ws_le _ _ _ _ i (exec_step_at E k' s Hwf Hs)).
Qed.

Lemma exec_img_const E k :
  exec_wf E → (k ≤ length (ex_tr E))%nat → eimg E k = eimg E 0%nat.
Proof.
  intros Hwf Hk. induction k as [|k IH]; [done|].
  rewrite -IH; [lia|].
  destruct (exec_tr_lookup E k ltac:(lia)) as [s Hs].
  apply (mstep_img _ _ _ _ (exec_step_at E k s Hwf Hs)).
Qed.

(** The whole run's image and final log — the memory the axiomatic execution
    is stated over. *)
Definition ex_img (E : exec) : image := eimg E 0%nat.
Definition ex_log (E : exec) : list wmsg := elog E (length (ex_tr E)).

Lemma ex_log_prefix E k :
  exec_wf E → (k ≤ length (ex_tr E))%nat → elog E k `prefix_of` ex_log E.
Proof. intros. by apply exec_log_prefix. Qed.

(** A byte value read at step [k] is still there at the end of the run: the log
    is append-only. *)
Lemma log_byte_final E k t a :
  exec_wf E → (k ≤ length (ex_tr E))%nat → (t ≤ length (elog E k))%nat →
  log_byte (ex_img E) (ex_log E) t a = log_byte (eimg E k) (elog E k) t a.
Proof.
  intros Hwf Hk Ht. rewrite (exec_img_const E k Hwf Hk) -/(ex_img E).
  destruct (ex_log_prefix E k Hwf Hk) as [l ->].
  by rewrite log_byte_app.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Events

    MODELLING CHOICE (event identity).  An event is either the VIRTUAL INIT
    WRITE [ev_init] — timestamp 0, i.e. the era-initial image, reified as one
    write event that writes exactly the bytes the image defines — or the step
    at position [k] of the run, [ev_at k].  Event identity is therefore
    "position in the run", which is what makes the soundness proofs
    embeddings into execution order.

    [ev_ix] is the corresponding total order on events (init first).
    [ev_ts] is the event's GLOBAL-MEMORY-ORDER position, meaningful for write
    events only: the timestamp the message it appended occupies. *)
Inductive ev := ev_init | ev_at (k : nat).

Global Instance ev_eq_dec : EqDecision ev.
Proof. solve_decision. Defined.

Definition ev_ix (e : ev) : nat := match e with ev_init => 0%nat | ev_at k => S k end.
Definition ev_ts (E : exec) (e : ev) : nat :=
  match e with ev_init => 0%nat | ev_at k => S (length (elog E k)) end.

Lemma ev_ts_at E k : ev_ts E (ev_at k) = S (length (elog E k)).
Proof. done. Qed.

Definition is_W (E : exec) (e : ev) : Prop :=
  match e with
  | ev_init => True
  | ev_at k => ∃ s, ex_tr E !! k = Some s ∧ lb_is_w (es_lb s) = true
  end.

Definition is_R (E : exec) (e : ev) : Prop :=
  ∃ k s, e = ev_at k ∧ ex_tr E !! k = Some s ∧ lb_is_r (es_lb s) = true.

Lemma is_W_lt E k : is_W E (ev_at k) → (k < length (ex_tr E))%nat.
Proof. intros (s & Hs & _). by eapply lookup_lt_Some. Qed.

Lemma lb_wr_is_w l x : lb_wr l = Some x → lb_is_w l = true.
Proof. by destruct l. Qed.

Lemma lb_rd_is_r l x : lb_rd l = Some x → lb_is_r l = true.
Proof. by destruct l. Qed.

(** The bytes an event writes, read off the FINAL log at the event's
    timestamp.  For [ev_init] this is exactly the image's domain. *)
Definition ev_writes (E : exec) (e : ev) (a : Z) : Prop :=
  is_Some (log_byte (ex_img E) (ex_log E) (ev_ts E e) a).

Lemma ev_writes_init E a : ev_writes E ev_init a ↔ is_Some (ex_img E a).
Proof. rewrite /ev_writes /=. done. Qed.

(** Initial state facts. *)
Lemma exec_st0 E : exec_wf E → ∃ σ0, ex_st E !! 0%nat = Some σ0.
Proof. intros Hwf. apply exec_st_len; [done|lia]. Qed.

Lemma exec_log_init E : exec_wf E → elog E 0%nat = [].
Proof.
  intros Hwf. destruct (exec_st0 E Hwf) as [σ0 H0].
  destruct Hwf as (_ & Hinit & _). rewrite /elog (stt_lookup _ _ _ H0).
  by destruct (Hinit σ0 H0) as [? _].
Qed.

Lemma exec_ws_init E i : exec_wf E → ews E 0%nat i = ws_init.
Proof.
  intros Hwf. destruct (exec_st0 E Hwf) as [σ0 H0].
  destruct Hwf as (_ & Hinit & _). rewrite /ews (stt_lookup _ _ _ H0).
  by destruct (Hinit σ0 H0) as [_ ?].
Qed.

(** The message a write step appends, located in the final log. *)
Lemma exec_msg_at E k s base vs :
  exec_wf E → ex_tr E !! k = Some s → lb_wr (es_lb s) = Some (base, vs) →
  ex_log E !! length (elog E k)
  = Some (WMsg base vs (Some (es_ag s)) (lb_cls (es_lb s))).
Proof.
  intros Hwf Hs Hwr. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  destruct (mstep_log_w _ _ _ _ Hstep (lb_wr_is_w _ _ Hwr))
    as (base' & vs' & Hwr' & _ & Hlog).
  rewrite Hwr in Hwr'. simplify_eq.
  destruct (ex_log_prefix E (S k) Hwf ltac:(lia)) as [l Hl].
  rewrite Hl /elog Hlog -app_assoc.
  rewrite lookup_app_r; [lia|]. by rewrite Nat.sub_diag.
Qed.

Lemma ev_writes_at E k s base vs a :
  exec_wf E → ex_tr E !! k = Some s → lb_wr (es_lb s) = Some (base, vs) →
  ev_writes E (ev_at k) a ↔
  is_Some (msg_byte (WMsg base vs (Some (es_ag s)) (lb_cls (es_lb s))) a).
Proof.
  intros Hwf Hs Hwr. rewrite /ev_writes. cbn [ev_ts]. rewrite log_byte_S.
  by rewrite (exec_msg_at E k s base vs Hwf Hs Hwr).
Qed.

(** Write timestamps are strictly increasing in execution order — this is the
    fact that makes [gmo] a total order refining execution order on writes,
    and it is what [(po ∩ W×W) ⊆ gmo] comes down to. *)
Lemma ev_ts_next E k s :
  exec_wf E → ex_tr E !! k = Some s → lb_is_w (es_lb s) = true →
  length (elog E (S k)) = ev_ts E (ev_at k).
Proof.
  intros Hwf Hs Hw. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  destruct (mstep_log_w _ _ _ _ Hstep Hw) as (base & vs & _ & _ & Hlog).
  rewrite /elog Hlog length_app /=. rewrite /ev_ts /elog. lia.
Qed.

Lemma ev_ts_mono E k k' :
  exec_wf E → (k < k')%nat → is_W E (ev_at k) → is_W E (ev_at k') →
  (ev_ts E (ev_at k) < ev_ts E (ev_at k'))%nat.
Proof.
  intros Hwf Hlt (s & Hs & Hw) HW'.
  pose proof (is_W_lt E k' HW') as Hk'.
  rewrite -(ev_ts_next E k s Hwf Hs Hw).
  pose proof (exec_log_len_le E (S k) k' Hwf ltac:(lia) ltac:(lia)).
  rewrite /ev_ts. lia.
Qed.

(** Hence a write event is determined by its timestamp: [gmo] is injective. *)
Lemma ev_ts_inj E e1 e2 :
  exec_wf E → is_W E e1 → is_W E e2 → ev_ts E e1 = ev_ts E e2 → e1 = e2.
Proof.
  intros Hwf H1 H2 Hts. destruct e1 as [|k1], e2 as [|k2]; [done| | |].
  - rewrite /ev_ts in Hts. lia.
  - rewrite /ev_ts in Hts. lia.
  - destruct (decide (k1 = k2)) as [->|Hne]; [done|exfalso].
    destruct (decide (k1 < k2)%nat) as [Hlt|Hgt].
    + pose proof (ev_ts_mono E k1 k2 Hwf Hlt H1 H2). lia.
    + pose proof (ev_ts_mono E k2 k1 Hwf ltac:(lia) H2 H1). lia.
Qed.

(** Every non-zero timestamp present in the log at any point of the run is the
    timestamp of a unique earlier WRITE STEP.  This is what makes [rf] total:
    a read always has a source event. *)
Lemma ts_writer E k t :
  exec_wf E → (k ≤ length (ex_tr E))%nat → (0 < t)%nat →
  (t ≤ length (elog E k))%nat →
  ∃ k' s, (k' < k)%nat ∧ ex_tr E !! k' = Some s ∧ lb_is_w (es_lb s) = true ∧
          ev_ts E (ev_at k') = t.
Proof.
  intros Hwf. induction k as [|k IH]; intros Hk Ht Hlen.
  { rewrite (exec_log_init E Hwf) /= in Hlen. lia. }
  destruct (exec_tr_lookup E k ltac:(lia)) as [s Hs].
  destruct (lb_is_w (es_lb s)) eqn:Hw.
  - rewrite (ev_ts_next E k s Hwf Hs Hw) ev_ts_at in Hlen.
    destruct (decide (t = S (length (elog E k)))) as [->|Hne].
    + exists k, s. split_and!; [lia|done|done|by rewrite ev_ts_at].
    + destruct (IH ltac:(lia) Ht ltac:(lia)) as (k' & s' & ? & ? & ? & ?).
      exists k', s'. split_and!; [lia|done|done|done].
  - pose proof (exec_step_at E k s Hwf Hs) as Hstep.
    rewrite /elog (mstep_log_nw _ _ _ _ Hstep Hw) in Hlen.
    destruct (IH ltac:(lia) Ht Hlen) as (k' & s' & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done].
Qed.

(** Reading a step's side conditions back off the trace. *)
Lemma lb_rd_cases l base ts vs :
  lb_rd l = Some (base, ts, vs) →
  ∃ aq, lb_aq l = aq ∧
        (l = LLoad aq base ts vs ∨ ∃ rl wvs k, l = LRmw aq rl base ts vs wvs k).
Proof.
  destruct l; simpl; intros Hl; simplify_eq; eexists; (split; [reflexivity|]).
  - by left.
  - right. by do 3 eexists.
Qed.

Lemma exec_rd_ok E k s base ts vs :
  exec_wf E → ex_tr E !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  rd_ok (eimg E k) (elog E k) (ews E k (es_ag s)) (lb_aq (es_lb s)) base ts vs.
Proof.
  intros Hwf Hs Hrd. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite /eimg /elog /ews.
  destruct (lb_rd_cases _ _ _ _ Hrd) as (aq & Haq & [Hl|(rl & wvs & kc & Hl)]);
    rewrite Haq; rewrite Hl in Hstep; inversion Hstep; simplify_eq; done.
Qed.

Lemma exec_rmw_latest E k s aq rl base ts rvs wvs kc :
  exec_wf E → ex_tr E !! k = Some s → es_lb s = LRmw aq rl base ts rvs wvs kc →
  rmw_latest (eimg E k) (elog E k) base ts.
Proof.
  intros Hwf Hs Hl. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite Hl in Hstep. rewrite /eimg /elog. by inversion Hstep; simplify_eq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reads, and the per-byte reads-from

    MODELLING CHOICE (reads-from is PER BYTE).  [reads_at E k a t v] says step
    [k] read byte [a] at timestamp [t] obtaining [v]; [rf_b E a w r] then says
    the write event [w] is the one occupying that timestamp.  A multi-byte load
    has one rf edge per byte, all with the same reader event, exactly as
    RVWMO's load-value axiom is per byte. *)

Definition reads_at (E : exec) (k : nat) (a : Z) (t : nat) (v : bv 8) : Prop :=
  ∃ s base ts vs (j : nat),
    ex_tr E !! k = Some s ∧ lb_rd (es_lb s) = Some (base, ts, vs) ∧
    ts !! j = Some t ∧ vs !! j = Some v ∧ a = acc_addr base j.

Lemma reads_at_lt E k a t v : reads_at E k a t v → (k < length (ex_tr E))%nat.
Proof. intros (s & ? & ? & ? & ? & Hs & _). by eapply lookup_lt_Some. Qed.

Lemma reads_at_byte_rd E k a t v :
  exec_wf E → reads_at E k a t v →
  ∃ s, ex_tr E !! k = Some s ∧
       byte_rd (eimg E k) (elog E k) (ews E k (es_ag s)) (lb_aq (es_lb s)) a t v.
Proof.
  intros Hwf (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & ->).
  exists s. split; [done|].
  destruct (exec_rd_ok E k s base ts vs Hwf Hs Hrd) as [_ Hall].
  by apply Hall.
Qed.

Lemma reads_at_ts_le E k a t v :
  exec_wf E → reads_at E k a t v → (t ≤ length (elog E k))%nat.
Proof.
  intros Hwf Hr. destruct (reads_at_byte_rd E k a t v Hwf Hr) as (s & _ & [Hv _]).
  apply (log_byte_bounded (eimg E k) (elog E k) t a). by eexists.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The relations of an axiomatic execution *)

(** [e] writes byte [a] / reads byte [a] / accesses byte [a]. *)
Definition wr_b (E : exec) (a : Z) (e : ev) : Prop := is_W E e ∧ ev_writes E e a.
Definition rd_b (E : exec) (a : Z) (e : ev) : Prop :=
  ∃ k t v, e = ev_at k ∧ reads_at E k a t v.
Definition acc_b (E : exec) (a : Z) (e : ev) : Prop := wr_b E a e ∨ rd_b E a e.

(** PROGRAM ORDER: the per-agent step order.  [ev_init] is in no [po] edge —
    the initial image is not part of any agent's program. *)
Definition po (E : exec) (e1 e2 : ev) : Prop :=
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ (k1 < k2)%nat ∧
    ex_tr E !! k1 = Some s1 ∧ ex_tr E !! k2 = Some s2 ∧ es_ag s1 = es_ag s2.

(** READS-FROM, per byte and lifted to events. *)
Definition rf_b (E : exec) (a : Z) (w r : ev) : Prop :=
  wr_b E a w ∧ ∃ k t v, r = ev_at k ∧ reads_at E k a t v ∧ ev_ts E w = t.
Definition rf (E : exec) (w r : ev) : Prop := ∃ a, rf_b E a w r.

(** THE GLOBAL MEMORY ORDER ON WRITES: the log order.  This is the single
    total order multi-copy atomicity licenses (design Decision 1/2); reads are
    NOT placed in it — see the note on [ax_external] below. *)
Definition gmo (E : exec) (w1 w2 : ev) : Prop :=
  is_W E w1 ∧ is_W E w2 ∧ (ev_ts E w1 < ev_ts E w2)%nat.

(** COHERENCE ORDER: [gmo] restricted to the writes of one byte. *)
Definition co_b (E : exec) (a : Z) (w1 w2 : ev) : Prop :=
  wr_b E a w1 ∧ wr_b E a w2 ∧ (ev_ts E w1 < ev_ts E w2)%nat.
Definition co (E : exec) (w1 w2 : ev) : Prop := ∃ a, co_b E a w1 w2.

(** FROM-READ: [r] reads a write [co]-before [w].  The [r ≠ w] side condition
    is what fusing an RMW's two halves into one event costs: without it every
    RMW would carry an [fr] self-loop from its own read half to its own write
    half. *)
Definition fr_b (E : exec) (a : Z) (r w : ev) : Prop :=
  (∃ w0, rf_b E a w0 r ∧ co_b E a w0 w) ∧ r ≠ w.
Definition fr (E : exec) (r w : ev) : Prop := ∃ a, fr_b E a r w.

(** Same-byte program order. *)
Definition po_loc_b (E : exec) (a : Z) (e1 e2 : ev) : Prop :=
  po E e1 e2 ∧ acc_b E a e1 ∧ acc_b E a e2.

(** [is_rmw E e]: the event is a fused read-modify-write. *)
Definition is_rmw (E : exec) (e : ev) : Prop :=
  ∃ k s, e = ev_at k ∧ ex_tr E !! k = Some s ∧
         lb_is_r (es_lb s) = true ∧ lb_is_w (es_lb s) = true.

(* ------------------------------------------------------------------ *)
(** ** Acyclicity by a lexicographic measure

    Every soundness proof below is an embedding of a union of relations into a
    (timestamp, execution-position) lexicographic order. *)

Definition lexlt (p q : nat * nat) : Prop :=
  (p.1 < q.1)%nat ∨ (p.1 = q.1 ∧ (p.2 < q.2)%nat).

Lemma lexlt_trans p q r : lexlt p q → lexlt q r → lexlt p r.
Proof. rewrite /lexlt. intros [?|[??]] [?|[??]]; [left|left|left|right]; lia. Qed.

Lemma lexlt_irrefl p : ¬ lexlt p p.
Proof. rewrite /lexlt. intros [?|[??]]; lia. Qed.

Lemma tc_lexlt {A} (R : relation A) (f : A → nat * nat) :
  (∀ x y, R x y → lexlt (f x) (f y)) → ∀ x, ¬ tc R x x.
Proof.
  intros Hf x Hc.
  assert (Hall : ∀ y z, tc R y z → lexlt (f y) (f z)).
  { intros y z Hyz. induction Hyz as [y z Hr|y z u Hr _ IH];
      [by apply Hf|]. eapply lexlt_trans; [by apply Hf|exact IH]. }
  by apply (lexlt_irrefl (f x)), Hall.
Qed.

(** The scalar special case (measure in the first component only). *)
Lemma tc_nat_lt {A} (R : relation A) (f : A → nat) :
  (∀ x y, R x y → (f x < f y)%nat) → ∀ x, ¬ tc R x x.
Proof.
  intros Hf. apply (tc_lexlt R (λ x, (f x, 0%nat))).
  intros x y ?. left. simpl. by apply Hf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Well-formedness of [rf]: total, functional, value-correct *)

Lemma reads_at_log_final E k a t v :
  exec_wf E → reads_at E k a t v → log_byte (ex_img E) (ex_log E) t a = Some v.
Proof.
  intros Hwf Hr.
  pose proof (reads_at_lt E k a t v Hr) as Hk.
  pose proof (reads_at_ts_le E k a t v Hwf Hr) as Ht.
  rewrite (log_byte_final E k t a Hwf ltac:(lia) Ht).
  destruct (reads_at_byte_rd E k a t v Hwf Hr) as (s & _ & [Hv _]). exact Hv.
Qed.

(** Two reads of the SAME byte by the SAME step agree: the byte index is
    determined by the address ([acc_addr] is injective in the index). *)
Lemma reads_at_det E k a t v t' v' :
  reads_at E k a t v → reads_at E k a t' v' → t = t' ∧ v = v'.
Proof.
  intros (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha)
         (s' & base' & ts' & vs' & j' & Hs' & Hrd' & Hj' & Hv' & Ha').
  assert (Hss : s = s') by (rewrite Hs in Hs'; by simplify_eq).
  subst s'.
  assert (Hbb : base = base' ∧ ts = ts' ∧ vs = vs').
  { rewrite Hrd in Hrd'. by simplify_eq. }
  destruct Hbb as (<- & <- & <-).
  assert (j = j') as <-.
  { apply (acc_addr_inj base). rewrite -Ha -Ha' //. }
  rewrite Hj in Hj'. rewrite Hv in Hv'. by simplify_eq.
Qed.

Lemma rf_b_total E k a t v :
  exec_wf E → reads_at E k a t v → ∃ w, rf_b E a w (ev_at k).
Proof.
  intros Hwf Hr.
  pose proof (reads_at_lt E k a t v Hr) as Hk.
  pose proof (reads_at_log_final E k a t v Hwf Hr) as Hlog.
  destruct t as [|t'].
  - exists ev_init. split.
    + split; [done|]. rewrite /ev_writes. cbn [ev_ts]. rewrite Hlog. by eexists.
    + exists k, 0%nat, v. by split_and!.
  - destruct (ts_writer E k (S t') Hwf ltac:(lia) ltac:(lia)
                (reads_at_ts_le E k a (S t') v Hwf Hr))
      as (k' & s' & Hlt & Hs' & Hw' & Hts).
    exists (ev_at k'). split.
    + split; [by eexists|]. rewrite /ev_writes Hts Hlog. by eexists.
    + exists k, (S t'), v. by split_and!.
Qed.

(** [rf] is functional per byte: a timestamp determines its write event. *)
Lemma rf_b_functional E a w1 w2 r :
  exec_wf E → rf_b E a w1 r → rf_b E a w2 r → w1 = w2.
Proof.
  intros Hwf [[HW1 _] (k & t & v & -> & Hr & Hts1)] [[HW2 _] (k' & t' & v' & Hk & Hr' & Hts2)].
  assert (k' = k) as -> by (by simplify_eq).
  destruct (reads_at_det E k a t v t' v' Hr Hr') as [-> _].
  apply (ev_ts_inj E w1 w2 Hwf HW1 HW2). by rewrite Hts1 Hts2.
Qed.

Lemma rf_b_value E a w k t v :
  exec_wf E → reads_at E k a t v → rf_b E a w (ev_at k) →
  log_byte (ex_img E) (ex_log E) (ev_ts E w) a = Some v.
Proof.
  intros Hwf Hr [_ (k' & t' & v' & Hk & Hr' & Hts)].
  assert (k' = k) as -> by (by simplify_eq).
  destruct (reads_at_det E k a t v t' v' Hr Hr') as [-> ->].
  rewrite Hts. by apply (reads_at_log_final E k).
Qed.

(* ------------------------------------------------------------------ *)
(** ** [rf] and [po] both point forward in execution order *)

Lemma po_ix E e1 e2 : po E e1 e2 → (ev_ix e1 < ev_ix e2)%nat.
Proof. intros (k1 & k2 & ? & ? & -> & -> & ? & _). simpl. lia. Qed.

(** THE key structural fact behind [acyclic(po ∪ rf)]: a load can only read a
    message that is ALREADY IN THE LOG, so every [rf] edge points backwards in
    real time (design Decision 1's "no interleaving machine can represent
    load buffering" argument, mechanized). *)
Lemma rf_ix E w r : exec_wf E → rf E w r → (ev_ix w < ev_ix r)%nat.
Proof.
  intros Hwf (a & [[HW _] (k & t & v & -> & Hr & Hts)]).
  destruct w as [|k']; [simpl; lia|].
  pose proof (reads_at_lt E k a t v Hr) as Hk.
  pose proof (reads_at_ts_le E k a t v Hwf Hr) as Ht.
  pose proof (is_W_lt E k' HW) as Hk'.
  rewrite ev_ts_at in Hts.
  simpl. cut ((k' < k)%nat); [lia|].
  destruct (decide (k' < k)%nat) as [?|Hge]; [done|exfalso].
  pose proof (exec_log_len_le E k k' Hwf ltac:(lia) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Per-agent state along a run: the shape of each step's update *)

Lemma mstep_ws_load σ i aq base ts vs σ' :
  mstep σ i (LLoad aq base ts vs) σ' →
  ms_ws σ' i = load_post_run (ms_ws σ i) aq base ts.
Proof. inversion 1; simplify_eq; simpl; by rewrite upd_ws_eq. Qed.

Lemma mstep_ws_store σ i rl base vs k σ' :
  mstep σ i (LStore rl base vs k) σ' →
  ms_ws σ' i = store_post_run (ms_ws σ i) rl base (length vs)
                 (S (length (ms_log σ))).
Proof. inversion 1; simplify_eq; simpl; by rewrite upd_ws_eq. Qed.

Lemma mstep_ws_fence σ i pr pw sr sw σ' :
  mstep σ i (LFence pr pw sr sw) σ' →
  ms_ws σ' i = fence_post (ms_ws σ i) pr pw sr sw.
Proof. inversion 1; simplify_eq; simpl; by rewrite upd_ws_eq. Qed.

Lemma mstep_ws_rmw σ i aq rl base ts rvs wvs k σ' :
  mstep σ i (LRmw aq rl base ts rvs wvs k) σ' →
  ms_ws σ' i = store_post_run (load_post_run (ms_ws σ i) aq base ts) rl base
                 (length wvs) (S (length (ms_log σ))).
Proof. inversion 1; simplify_eq; simpl; by rewrite upd_ws_eq. Qed.

Lemma exec_ws_load E k s aq base ts vs :
  exec_wf E → ex_tr E !! k = Some s → es_lb s = LLoad aq base ts vs →
  ews E (S k) (es_ag s) = load_post_run (ews E k (es_ag s)) aq base ts.
Proof.
  intros Hwf Hs Hl. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite Hl in Hstep. exact (mstep_ws_load _ _ _ _ _ _ _ Hstep).
Qed.

Lemma exec_ws_store E k s rl base vs kc :
  exec_wf E → ex_tr E !! k = Some s → es_lb s = LStore rl base vs kc →
  ews E (S k) (es_ag s) =
    store_post_run (ews E k (es_ag s)) rl base (length vs) (ev_ts E (ev_at k)).
Proof.
  intros Hwf Hs Hl. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite Hl in Hstep. exact (mstep_ws_store _ _ _ _ _ _ _ Hstep).
Qed.

Lemma exec_ws_fence E k s pr pw sr sw :
  exec_wf E → ex_tr E !! k = Some s → es_lb s = LFence pr pw sr sw →
  ews E (S k) (es_ag s) = fence_post (ews E k (es_ag s)) pr pw sr sw.
Proof.
  intros Hwf Hs Hl. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite Hl in Hstep. exact (mstep_ws_fence _ _ _ _ _ _ _ Hstep).
Qed.

Lemma exec_ws_rmw E k s aq rl base ts rvs wvs kc :
  exec_wf E → ex_tr E !! k = Some s → es_lb s = LRmw aq rl base ts rvs wvs kc →
  ews E (S k) (es_ag s) =
    store_post_run (load_post_run (ews E k (es_ag s)) aq base ts) rl base
      (length wvs) (ev_ts E (ev_at k)).
Proof.
  intros Hwf Hs Hl. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  rewrite Hl in Hstep. exact (mstep_ws_rmw _ _ _ _ _ _ _ _ _ _ Hstep).
Qed.

(** A byte inside a message's range is byte [j] of it. *)
Lemma msg_byte_index base vs tid k a :
  is_Some (msg_byte (WMsg base vs tid k) a) →
  ∃ j : nat, (j < length vs)%nat ∧ a = acc_addr base j.
Proof.
  rewrite /msg_byte /=. case_bool_decide as Hle; [|by intros []].
  intros Hs. exists (Z.to_nat (a - base)). split.
  - by apply lookup_lt_is_Some_1 in Hs.
  - rewrite /acc_addr. lia.
Qed.

(** Values are stable along the run (the log is append-only). *)
Lemma log_byte_at E k k' t a :
  exec_wf E → (k ≤ k')%nat → (k' ≤ length (ex_tr E))%nat →
  (t ≤ length (elog E k))%nat →
  log_byte (eimg E k') (elog E k') t a = log_byte (eimg E k) (elog E k) t a.
Proof.
  intros Hwf Hle Hk' Ht.
  rewrite (exec_img_const E k' Hwf Hk') (exec_img_const E k Hwf ltac:(lia)).
  destruct (exec_log_prefix E k k' Hwf Hle Hk') as [l ->].
  by rewrite log_byte_app.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [touches]: the timestamp a step uses at a byte

    A step "touches byte [a] at timestamp [t]" if it reads [a] at [t] or writes
    [a] (whose timestamp is its own).  An RMW touches its bytes TWICE — at the
    read timestamp and at its write timestamp. *)
Definition touches (E : exec) (k : nat) (a : Z) (t : nat) : Prop :=
  (∃ v, reads_at E k a t v) ∨
  (is_W E (ev_at k) ∧ ev_writes E (ev_at k) a ∧ t = ev_ts E (ev_at k)).

(** THE COHERENCE INVARIANT: a step's own timestamps are below its agent's
    coherence floor for that byte immediately afterwards. *)
Lemma touches_coh E k s a t :
  exec_wf E → ex_tr E !! k = Some s → touches E k a t →
  (t ≤ coh (ews E (S k) (es_ag s)) a)%nat.
Proof.
  intros Hwf Hs Ht.
  destruct (es_lb s) as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc]
    eqn:Hl.
  - (* load *)
    destruct Ht as [[v Hr]|(HW & _ & _)]; last first.
    { destruct HW as (s' & Hs' & Hw). rewrite Hs in Hs'. simplify_eq.
      by rewrite Hl in Hw. }
    destruct Hr as (s' & base' & ts' & vs' & j & Hs' & Hrd & Hj & Hv & ->).
    assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
    rewrite Hl /= in Hrd. simplify_eq.
    rewrite (exec_ws_load E k s aq base' ts' vs' Hwf Hs Hl).
    by apply load_post_run_coh.
  - (* store *)
    destruct Ht as [[v Hr]|(HW & Hwr & ->)].
    { destruct Hr as (s' & ? & ? & ? & ? & Hs' & Hrd & _).
      assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
      by rewrite Hl /= in Hrd. }
    apply (ev_writes_at E k s base vs a Hwf Hs ltac:(by rewrite Hl)) in Hwr.
    destruct (msg_byte_index base vs (Some (es_ag s)) _ a Hwr) as (j & Hj & ->).
    rewrite (exec_ws_store E k s rl base vs _ Hwf Hs Hl).
    by apply store_post_run_coh.
  - (* fence *)
    destruct Ht as [[v Hr]|(HW & _ & _)].
    { destruct Hr as (s' & ? & ? & ? & ? & Hs' & Hrd & _).
      assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
      by rewrite Hl /= in Hrd. }
    destruct HW as (s' & Hs' & Hw). rewrite Hs in Hs'. simplify_eq.
    by rewrite Hl in Hw.
  - (* rmw *)
    rewrite (exec_ws_rmw E k s aq rl base ts rvs wvs _ Hwf Hs Hl).
    destruct Ht as [[v Hr]|(HW & Hwr & ->)].
    + destruct Hr as (s' & base' & ts' & vs' & j & Hs' & Hrd & Hj & Hv & ->).
      assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
      rewrite Hl /= in Hrd. simplify_eq.
      etrans; [by apply load_post_run_coh|].
      apply ws_le_coh, store_post_run_le.
    + apply (ev_writes_at E k s base wvs a Hwf Hs ltac:(by rewrite Hl)) in Hwr.
      destruct (msg_byte_index base wvs (Some (es_ag s)) _ a Hwr) as (j & Hj & ->).
      by apply store_post_run_coh.
Qed.

Lemma touches_coh_later E k k' s a t :
  exec_wf E → ex_tr E !! k = Some s → touches E k a t →
  (S k ≤ k')%nat → (k' ≤ length (ex_tr E))%nat →
  (t ≤ coh (ews E k' (es_ag s)) a)%nat.
Proof.
  intros Hwf Hs Ht Hle Hk'.
  etrans; [by eapply touches_coh|].
  by apply ws_le_coh, (exec_ws_le E (S k) k' (es_ag s)).
Qed.

(** A touched timestamp is a real timestamp of the log at every LATER point of
    the run, and it does write the byte there. *)
Lemma touches_log E k k' a t :
  exec_wf E → touches E k a t → (k < k')%nat → (k' ≤ length (ex_tr E))%nat →
  (t ≤ length (elog E k'))%nat ∧ is_Some (log_byte (eimg E k') (elog E k') t a).
Proof.
  intros Hwf Ht Hlt Hk'. destruct Ht as [[v Hr]|(HW & Hwr & ->)].
  - pose proof (reads_at_ts_le E k a t v Hwf Hr) as Hle.
    pose proof (exec_log_len_le E k k' Hwf ltac:(lia) Hk') as Hlen.
    split; [lia|].
    rewrite (log_byte_at E k k' t a Hwf ltac:(lia) Hk' Hle).
    destruct (reads_at_byte_rd E k a t v Hwf Hr) as (s & _ & [Hv _]).
    rewrite Hv. by eexists.
  - destruct HW as (s & Hs & Hw).
    pose proof (ev_ts_next E k s Hwf Hs Hw) as Hnext.
    pose proof (exec_log_len_le E (S k) k' Hwf ltac:(lia) Hk') as Hlen.
    assert (Ht : (ev_ts E (ev_at k) ≤ length (elog E k'))%nat) by lia.
    split; [exact Ht|].
    rewrite -(log_byte_at E k' (length (ex_tr E)) (ev_ts E (ev_at k)) a
                Hwf Hk' ltac:(lia) Ht).
    exact Hwr.
Qed.

(** THE PER-BYTE MONOTONICITY OF PROGRAM ORDER.  Two accesses to the same byte
    by the same agent use non-decreasing timestamps: the earlier one raised the
    agent's coherence floor, and [readable] forbids reading below it. *)
Lemma touches_mono E k1 k2 s1 s2 a t1 t2 :
  exec_wf E → (k1 < k2)%nat →
  ex_tr E !! k1 = Some s1 → ex_tr E !! k2 = Some s2 → es_ag s1 = es_ag s2 →
  touches E k1 a t1 → touches E k2 a t2 → (t1 ≤ t2)%nat.
Proof.
  intros Hwf Hlt Hs1 Hs2 Hag Ht1 Ht2.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  destruct (touches_log E k1 k2 a t1 Hwf Ht1 Hlt ltac:(lia)) as [Ht1len Ht1some].
  destruct Ht2 as [[v2 Hr2]|(HW2 & Hwr2 & ->)]; last first.
  { rewrite ev_ts_at. lia. }
  destruct (reads_at_byte_rd E k2 a t2 v2 Hwf Hr2) as (s & Hs & [_ Hread]).
  assert (s = s2) as -> by (rewrite Hs in Hs2; by simplify_eq).
  destruct (decide (t1 ≤ t2)%nat) as [?|Hgt]; [done|exfalso].
  destruct Hread as [_ Hnw]. apply Hnw.
  apply (writes_in_log_byte (eimg E k2)). exists t1.
  pose proof (touches_coh_later E k1 k2 s1 a t1 Hwf Hs1 Ht1 ltac:(lia) ltac:(lia))
    as Hcoh.
  rewrite Hag in Hcoh. split_and!; [lia|lia|exact Ht1some].
Qed.

(** An RMW's read half is the globally latest write to that byte at its own
    step — the atomicity constraint, read off the trace. *)
Lemma lb_rw_rmw l :
  lb_is_w l = true → lb_is_r l = true →
  ∃ aq rl base ts rvs wvs k, l = LRmw aq rl base ts rvs wvs k.
Proof. destruct l; try done. intros _ _. by do 7 eexists. Qed.

Lemma rmw_read_latest E kr a t v :
  exec_wf E → reads_at E kr a t v → is_W E (ev_at kr) →
  latest (eimg E kr) (elog E kr) a t.
Proof.
  intros Hwf Hr HW.
  destruct Hr as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & ->).
  destruct HW as (s' & Hs' & Hw).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct (lb_rw_rmw (es_lb s) Hw (lb_rd_is_r _ _ Hrd))
    as (aq & rl & base' & ts' & rvs' & wvs' & kc & Hl).
  pose proof (exec_rmw_latest E kr s aq rl base' ts' rvs' wvs' _ Hwf Hs Hl) as Hlat.
  rewrite Hl /= in Hrd. simplify_eq. by apply (Hlat j).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The per-byte timestamp of an event: the coherence measure *)

Definition is_Wb (E : exec) (e : ev) : bool :=
  match e with
  | ev_init => true
  | ev_at k => match ex_tr E !! k with Some s => lb_is_w (es_lb s) | None => false end
  end.

Definition writesb (E : exec) (a : Z) (e : ev) : bool :=
  is_Wb E e &&
  match log_byte (ex_img E) (ex_log E) (ev_ts E e) a with
  | Some _ => true | None => false end.

Definition lb_rd_ts (l : lbl) (a : Z) : option nat :=
  match lb_rd l with
  | Some (base, ts, _) =>
      if bool_decide (base ≤ a) then ts !! Z.to_nat (a - base) else None
  | None => None
  end.

(** [ets E a e] — the timestamp event [e] occupies at byte [a]: its own write
    timestamp if it writes [a] (this is the arm an RMW takes), else the
    timestamp it read there. *)
Definition ets (E : exec) (a : Z) (e : ev) : nat :=
  if writesb E a e then ev_ts E e
  else match e with
       | ev_init => 0%nat
       | ev_at k =>
           match ex_tr E !! k with
           | Some s => default 0%nat (lb_rd_ts (es_lb s) a)
           | None => 0%nat
           end
       end.

Lemma writesb_spec E a e : writesb E a e = true ↔ wr_b E a e.
Proof.
  rewrite /writesb /wr_b /ev_writes andb_true_iff. split.
  - intros [HW Hlog]. split.
    + destruct e as [|k]; [done|]. simpl in HW.
      destruct (ex_tr E !! k) as [s|] eqn:Hs; [by eexists|done].
    + destruct (log_byte _ _ _ _); [by eexists|done].
  - intros [HW [v Hv]]. split.
    + destruct e as [|k]; [done|]. destruct HW as (s & Hs & Hw). by rewrite /= Hs.
    + by rewrite Hv.
Qed.

Lemma writesb_false E a e : ¬ wr_b E a e → writesb E a e = false.
Proof.
  intros Hn. destruct (writesb E a e) eqn:Hb; [|done].
  by destruct Hn; apply writesb_spec.
Qed.

Lemma ets_wr E a e : wr_b E a e → ets E a e = ev_ts E e.
Proof. intros H. rewrite /ets (proj2 (writesb_spec E a e) H) //. Qed.

Lemma reads_at_lb_rd_ts E k s a t v :
  ex_tr E !! k = Some s → reads_at E k a t v → lb_rd_ts (es_lb s) a = Some t.
Proof.
  intros Hs (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & ->).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  rewrite /lb_rd_ts Hrd bool_decide_eq_true_2; [rewrite /acc_addr; lia|].
  by replace (Z.to_nat (acc_addr base j - base)) with j by (rewrite /acc_addr; lia).
Qed.

Lemma ets_rd E a k t v :
  ¬ wr_b E a (ev_at k) → reads_at E k a t v → ets E a (ev_at k) = t.
Proof.
  intros Hn Hr. rewrite /ets (writesb_false E a _ Hn).
  destruct Hr as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
  rewrite Hs (reads_at_lb_rd_ts E k s a t v Hs) //.
  by exists s, base, ts, vs, j.
Qed.

(** Whatever [ets] picks, the step really does touch the byte at it. *)
Lemma acc_touches E a k : acc_b E a (ev_at k) → touches E k a (ets E a (ev_at k)).
Proof.
  intros Hacc. destruct (writesb E a (ev_at k)) eqn:Hb.
  - apply writesb_spec in Hb as Hw.
    right. rewrite (ets_wr E a _ Hw). destruct Hw as [? ?]. by split_and!.
  - assert (Hn : ¬ wr_b E a (ev_at k)).
    { intros Hw. by rewrite (proj2 (writesb_spec E a _) Hw) in Hb. }
    destruct Hacc as [Hw|(k' & t & v & Hk & Hr)]; [by exfalso; apply Hn|].
    simplify_eq. left. exists v. by rewrite (ets_rd E a k' t v Hn Hr).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Per-byte coherence (SC-per-location)

    This is the RVWMO content of ppo rules 1–3 plus the load-value axiom's
    coherence half, in the standard cat-model form: for each BYTE, the union
    [po-loc ∪ rf ∪ co ∪ fr] is acyclic. *)

Definition coh_rel (E : exec) (a : Z) : relation ev := λ e1 e2,
  po_loc_b E a e1 e2 ∨ rf_b E a e1 e2 ∨ co_b E a e1 e2 ∨ fr_b E a e1 e2.

Lemma coh_rel_lexlt E a e1 e2 :
  exec_wf E → coh_rel E a e1 e2 →
  lexlt (ets E a e1, ev_ix e1) (ets E a e2, ev_ix e2).
Proof.
  intros Hwf [Hpl|[Hrf|[Hco|Hfr]]].
  - (* po-loc: non-decreasing timestamp, increasing position *)
    destruct Hpl as ((k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag)
                     & Hacc1 & Hacc2).
    pose proof (touches_mono E k1 k2 s1 s2 a _ _ Hwf Hlt Hs1 Hs2 Hag
                  (acc_touches E a k1 Hacc1) (acc_touches E a k2 Hacc2)) as Hle.
    rewrite /lexlt /=.
    destruct (decide (ets E a (ev_at k1) = ets E a (ev_at k2))) as [Heq|Hne];
      [right; split; [exact Heq|lia]|left; lia].
  - (* rf: the reader sits at the write's own timestamp (or above it, if the
       reader is itself an RMW writing that byte) *)
    destruct Hrf as (Hw & k & t & v & -> & Hr & Hts).
    rewrite (ets_wr E a e1 Hw) Hts.
    destruct (writesb E a (ev_at k)) eqn:Hb.
    + apply writesb_spec in Hb as Hw2.
      rewrite (ets_wr E a _ Hw2) ev_ts_at. left; simpl.
      pose proof (reads_at_ts_le E k a t v Hwf Hr). lia.
    + assert (Hn : ¬ wr_b E a (ev_at k)).
      { intros Hx. by rewrite (proj2 (writesb_spec E a _) Hx) in Hb. }
      rewrite (ets_rd E a k t v Hn Hr). right; split; [done|].
      apply (rf_ix E e1 (ev_at k) Hwf). exists a. split; [exact Hw|].
      by exists k, t, v.
  - (* co: strictly increasing timestamp *)
    destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite (ets_wr E a e1 Hw1) (ets_wr E a e2 Hw2). by left.
  - (* fr: the reader is strictly below every co-later write *)
    destruct Hfr as ((w0 & Hrf & Hco) & Hne).
    pose proof Hco as (Hw0 & Hw2 & Hlt).
    rewrite (ets_wr E a e2 Hw2).
    destruct Hrf as (_ & kr & t0 & v0 & -> & Hr & Hts0).
    destruct (writesb E a (ev_at kr)) eqn:Hb; last first.
    { assert (Hn : ¬ wr_b E a (ev_at kr)).
      { intros Hx. by rewrite (proj2 (writesb_spec E a _) Hx) in Hb. }
      rewrite (ets_rd E a kr t0 v0 Hn Hr). left; simpl. lia. }
    apply writesb_spec in Hb as Hwr.
    rewrite (ets_wr E a _ Hwr). left; cbn [fst snd].
    destruct (decide (ev_ts E e2 < ev_ts E (ev_at kr))%nat) as [Hgt|Hge]; last first.
    { destruct (decide (ev_ts E e2 = ev_ts E (ev_at kr))) as [Heq|?]; [|lia].
      destruct (ev_ts_inj E e2 (ev_at kr) Hwf (proj1 Hw2) (proj1 Hwr) Heq).
      done. }
    (* the RMW's read half was globally latest, so nothing can sit between *)
    exfalso.
    pose proof (rmw_read_latest E kr a t0 v0 Hwf Hr (proj1 Hwr)) as [_ Hlat].
    pose proof (reads_at_lt E kr a t0 v0 Hr) as Hkr.
    apply Hlat. apply (writes_in_log_byte (eimg E kr)). exists (ev_ts E e2).
    rewrite ev_ts_at in Hgt.
    split_and!; [lia|lia|].
    rewrite -(log_byte_final E kr (ev_ts E e2) a Hwf ltac:(lia) ltac:(lia)).
    exact (proj2 Hw2).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The preserved-program-order fragment the machine keeps

    RVWMO's ppo rules, mapped onto this model:

    - rules 1–3 (overlapping addresses)     -> [po_loc_b], via [ax_coherence];
    - rule 4 (FENCE pred,succ)              -> [fence_between] below;
    - rule 5 (acquire annotation on [a])    -> [acq_po] below;
    - rule 6 (release annotation on [b])    -> NOT ENFORCED by this machine
      (design Decision 2: [.rl] only feeds [w_vRel], which is inert for stores
      in a promise-free machine).  Recorded as a friction point, not modelled;
      the kernel image contains no release store;
    - rule 7 (RCsc pairs), rule 8 (LR/SC)   -> vacuous: no RCsc annotation and
      no LR/SC in the modelled alphabet;
    - rules 9–13 (syntactic dependencies)   -> OUT OF SCOPE by W4's own scope
      decision (design Decision 3: no register views). *)

Definition fence_between (E : exec) (k1 k2 : nat) (pr pw sr sw : bool) : Prop :=
  ∃ kf sf s1 s2, (k1 < kf)%nat ∧ (kf < k2)%nat ∧
    ex_tr E !! k1 = Some s1 ∧ ex_tr E !! kf = Some sf ∧ ex_tr E !! k2 = Some s2 ∧
    es_ag s1 = es_ag sf ∧ es_ag sf = es_ag s2 ∧ es_lb sf = LFence pr pw sr sw.

Definition acq_po (E : exec) (e1 e2 : ev) : Prop :=
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ (k1 < k2)%nat ∧
    ex_tr E !! k1 = Some s1 ∧ ex_tr E !! k2 = Some s2 ∧ es_ag s1 = es_ag s2 ∧
    lb_is_r (es_lb s1) = true ∧ lb_aq (es_lb s1) = true.

(** Ordering edges INTO A READ, by which predecessor bit justifies them. *)
Definition ord_pw (E : exec) (e1 e2 : ev) : Prop :=
  ∃ k1 k2 pr sw, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧
                 fence_between E k1 k2 pr true true sw.
Definition ord_pr (E : exec) (e1 e2 : ev) : Prop :=
  (∃ k1 k2 pw sw, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧
                  fence_between E k1 k2 true pw true sw)
  ∨ acq_po E e1 e2.

(** PUBLICATIONS: the timestamps an event makes visible to its agent's future.
    A write publishes its own timestamp ([w_vwOld]); an ACQUIRE read publishes
    the timestamp it read ([w_vrOld] / [w_vrNew], and forwarding is disabled
    for acquires so the published view IS the timestamp).

    A PLAIN read publishes its timestamp too, but only when it was not
    FORWARDED from the agent's own store — [WeakMem.fwd_view] replaces the
    timestamp by the weaker banked view in that case.  The side condition is
    stated axiomatically as "the rf edge is EXTERNAL" ([ext_w]), which is
    exactly why [rfi] is excluded from [obs] in the Arm-A/RVWMO cat models. *)
Definition pub_w (E : exec) (e : ev) (t : nat) : Prop :=
  is_W E e ∧ (∃ k, e = ev_at k) ∧ t = ev_ts E e.

Definition ext_w (E : exec) (w : ev) (i : agent) : Prop :=
  match w with
  | ev_init => True
  | ev_at k => ∃ s, ex_tr E !! k = Some s ∧ es_ag s ≠ i
  end.

Definition pub_r (E : exec) (e : ev) (t : nat) : Prop :=
  ∃ k s a v, e = ev_at k ∧ ex_tr E !! k = Some s ∧ reads_at E k a t v ∧
             (lb_aq (es_lb s) = true ∨
              ∃ w, rf_b E a w (ev_at k) ∧ ext_w E w (es_ag s)).

(* ------------------------------------------------------------------ *)
(** ** The operational content: publications reach the reader's pre-view *)

Lemma load_post_run_vrOld_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vrOld (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. apply (load_post_run_vrOld' ws true base ts j t Ht).
  apply fwd_view_aq.
Qed.

(** A write's own timestamp is under its agent's [w_vwOld] straight after. *)
Lemma pub_w_vwOld E k s :
  exec_wf E → ex_tr E !! k = Some s → lb_is_w (es_lb s) = true →
  (ev_ts E (ev_at k) ≤ w_vwOld (ews E (S k) (es_ag s)))%nat.
Proof.
  intros Hwf Hs Hw. pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  destruct (mstep_log_w _ _ _ _ Hstep Hw) as (base & vs & Hwr & Hne & _).
  destruct (es_lb s) as [aq0 b0 t0 v0|rl b0 v0 kc|p1 p2 p3 p4|aq0 rl b0 t0 rv0 wv0 kc]
    eqn:Hl; [by simplify_eq/=| |by simplify_eq/=|].
  - rewrite (exec_ws_store E k s rl b0 v0 _ Hwf Hs Hl).
    apply store_post_run_vwOld.
    assert (v0 ≠ []) as Hne0 by (simpl in Hwr; by simplify_eq).
    destruct v0; [done|simpl; lia].
  - rewrite (exec_ws_rmw E k s aq0 rl b0 t0 rv0 wv0 _ Hwf Hs Hl).
    apply store_post_run_vwOld.
    assert (wv0 ≠ []) as Hne0 by (simpl in Hwr; by simplify_eq).
    destruct wv0; [done|simpl; lia].
Qed.

(** *** The forward-bank invariant

    A bank entry's timestamp is always one of THIS agent's own writes.  This is
    what turns "the rf edge is external" into "the read was not forwarded", and
    hence into a [w_vrOld] publication for a PLAIN read. *)

Definition fwd_ok (E : exec) (k : nat) (i : agent) : Prop :=
  ∀ a tf vf, w_fwd (ews E k i) !! a = Some (tf, vf) →
    ∃ k' s', (k' < k)%nat ∧ ex_tr E !! k' = Some s' ∧ es_ag s' = i ∧
             lb_is_w (es_lb s') = true ∧ ev_ts E (ev_at k') = tf.

Lemma exec_fwd_ok E k i :
  exec_wf E → (k ≤ length (ex_tr E))%nat → fwd_ok E k i.
Proof.
  intros Hwf. induction k as [|k IH]; intros Hk a tf vf Hlk.
  { by rewrite (exec_ws_init E i Hwf) /ws_init /= lookup_empty in Hlk. }
  destruct (exec_tr_lookup E k ltac:(lia)) as [s Hs].
  destruct (decide (es_ag s = i)) as [Hag|Hne]; last first.
  { pose proof (exec_step_at E k s Hwf Hs) as Hstep.
    rewrite /ews (mstep_ws_ne _ _ _ _ i Hstep ltac:(congruence)) in Hlk.
    destruct (IH ltac:(lia) a tf vf Hlk) as (k' & s' & ? & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done|done]. }
  subst i.
  destruct (es_lb s) as [aq0 b0 t0 v0|rl b0 v0 kc|p1 p2 p3 p4|aq0 rl b0 t0 rv0 wv0 kc]
    eqn:Hl.
  - rewrite (exec_ws_load E k s aq0 b0 t0 v0 Hwf Hs Hl)
            load_post_run_fwd in Hlk.
    destruct (IH ltac:(lia) a tf vf Hlk) as (k' & s' & ? & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done|done].
  - rewrite (exec_ws_store E k s rl b0 v0 _ Hwf Hs Hl) in Hlk.
    apply store_post_run_fwd_inv in Hlk as [->|Hlk].
    + exists k, s. split_and!; [lia|done|done|by rewrite Hl|done].
    + destruct (IH ltac:(lia) a tf vf Hlk) as (k' & s' & ? & ? & ? & ? & ?).
      exists k', s'. split_and!; [lia|done|done|done|done].
  - rewrite (exec_ws_fence E k s p1 p2 p3 p4 Hwf Hs Hl)
            fence_post_fwd in Hlk.
    destruct (IH ltac:(lia) a tf vf Hlk) as (k' & s' & ? & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done|done].
  - rewrite (exec_ws_rmw E k s aq0 rl b0 t0 rv0 wv0 _ Hwf Hs Hl) in Hlk.
    apply store_post_run_fwd_inv in Hlk as [->|Hlk].
    + exists k, s. split_and!; [lia|done|done|by rewrite Hl|done].
    + rewrite load_post_run_fwd in Hlk.
      destruct (IH ltac:(lia) a tf vf Hlk) as (k' & s' & ? & ? & ? & ? & ?).
      exists k', s'. split_and!; [lia|done|done|done|done].
Qed.

(** An acquire read, or a plain read whose rf edge is EXTERNAL, is not
    forwarded — so the view it contributes IS its timestamp. *)
Lemma pub_r_fwd_view E k s a t v :
  exec_wf E → ex_tr E !! k = Some s → reads_at E k a t v →
  (lb_aq (es_lb s) = true ∨ ∃ w, rf_b E a w (ev_at k) ∧ ext_w E w (es_ag s)) →
  fwd_view (ews E k (es_ag s)) (lb_aq (es_lb s)) a t = t.
Proof.
  intros Hwf Hs Hr Hside.
  destruct (lb_aq (es_lb s)) eqn:Haq; [apply fwd_view_aq|].
  destruct Hside as [?|(w & Hrf & Hext)]; [done|].
  destruct (w_fwd (ews E k (es_ag s)) !! a) as [[tf vf]|] eqn:Hf;
    [|by apply fwd_view_miss].
  rewrite /fwd_view Hf. case_bool_decide as Ht; [|done]. exfalso. subst t.
  pose proof (reads_at_lt E k a tf v Hr) as Hk.
  destruct (exec_fwd_ok E k (es_ag s) Hwf ltac:(lia) a tf vf Hf)
    as (k' & s' & Hlt & Hs' & Hag' & Hw' & Hts').
  destruct Hrf as (Hwb & k'' & t'' & v'' & Hk'' & Hr'' & Hts'').
  assert (k'' = k) as -> by (by simplify_eq).
  destruct (reads_at_det E k a tf v t'' v'' Hr Hr'') as [-> _].
  assert (w = ev_at k') as ->.
  { apply (ev_ts_inj E w (ev_at k') Hwf (proj1 Hwb) ltac:(by eexists)).
    by rewrite Hts'' Hts'. }
  destruct Hext as (s'' & Hs'' & Hne).
  rewrite Hs' in Hs''. by simplify_eq.
Qed.

(** ... hence its timestamp lands under [w_vrOld]; an ACQUIRE read additionally
    raises [w_vrNew] with no fence at all. *)
Lemma pub_r_vrOld E k s t :
  exec_wf E → ex_tr E !! k = Some s → pub_r E (ev_at k) t →
  (t ≤ w_vrOld (ews E (S k) (es_ag s)))%nat.
Proof.
  intros Hwf Hs (k0 & s0 & a & v & Hk0 & Hs0 & Hr & Hside).
  assert (k0 = k) as -> by (by simplify_eq).
  assert (s0 = s) as -> by (rewrite Hs in Hs0; by simplify_eq).
  pose proof (pub_r_fwd_view E k s a t v Hwf Hs Hr Hside) as Hfv.
  destruct Hr as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & Ha).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  rewrite Ha in Hfv.
  destruct (lb_rd_cases _ _ _ _ Hrd) as (aq & Haq' & [Hl|(rl & wvs & kc & Hl)]);
    rewrite Haq' in Hfv.
  - rewrite (exec_ws_load E k s aq base ts vs Hwf Hs Hl).
    by apply (load_post_run_vrOld' _ _ _ _ j t Hj).
  - rewrite (exec_ws_rmw E k s aq rl base ts vs wvs _ Hwf Hs Hl).
    etrans; [apply (load_post_run_vrOld' (ews E k (es_ag s)) aq base ts j t Hj Hfv)|].
    apply ws_le_vrOld, store_post_run_le.
Qed.

Lemma pub_r_vrNew_aq E k s t :
  exec_wf E → ex_tr E !! k = Some s → pub_r E (ev_at k) t →
  lb_aq (es_lb s) = true → (t ≤ w_vrNew (ews E (S k) (es_ag s)))%nat.
Proof.
  intros Hwf Hs (k0 & s0 & a & v & Hk0 & Hs0 & Hr & _) Haq.
  assert (k0 = k) as -> by (by simplify_eq).
  assert (s0 = s) as -> by (rewrite Hs in Hs0; by simplify_eq).
  destruct Hr as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & Ha).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct (lb_rd_cases _ _ _ _ Hrd) as (aq & Haq' & [Hl|(rl & wvs & kc & Hl)]);
    rewrite Haq in Haq'; subst aq.
  - rewrite (exec_ws_load E k s true base ts vs Hwf Hs Hl).
    by apply (load_post_run_vrNew_aq _ _ _ j).
  - rewrite (exec_ws_rmw E k s true rl base ts vs wvs _ Hwf Hs Hl).
    etrans; [apply (load_post_run_vrNew_aq (ews E k (es_ag s)) base ts j t Hj)|].
    apply ws_le_vrNew, store_post_run_le.
Qed.

Lemma ord_lt E e1 k2 :
  ord_pw E e1 (ev_at k2) ∨ ord_pr E e1 (ev_at k2) →
  ∃ k1, e1 = ev_at k1 ∧ (k1 < k2)%nat.
Proof.
  intros [(k1 & k2' & ? & ? & -> & Hk & (kf & ? & ? & ? & ? & ? & _))
         |[(k1 & k2' & ? & ? & -> & Hk & (kf & ? & ? & ? & ? & ? & _))
          |(k1 & k2' & ? & ? & -> & Hk & ? & ? & ? & ? & ? & _)]];
    exists k1; (split; [done|]); simplify_eq; lia.
Qed.

Lemma pub_w_le_log E k1 k2 t :
  exec_wf E → pub_w E (ev_at k1) t → (k1 < k2)%nat →
  (k2 ≤ length (ex_tr E))%nat → (t ≤ length (elog E k2))%nat.
Proof.
  intros Hwf (HW & _ & ->) Hlt Hk2. destruct HW as (s & Hs & Hw).
  rewrite -(ev_ts_next E k1 s Hwf Hs Hw).
  apply (exec_log_len_le E (S k1) k2 Hwf ltac:(lia) Hk2).
Qed.

Lemma pub_r_le_log E k1 k2 t :
  exec_wf E → pub_r E (ev_at k1) t → (k1 < k2)%nat →
  (k2 ≤ length (ex_tr E))%nat → (t ≤ length (elog E k2))%nat.
Proof.
  intros Hwf (k & s & a & v & Hk & Hs & Hr & _) Hlt Hk2.
  assert (k = k1) as -> by (by simplify_eq).
  etrans; [by eapply reads_at_ts_le|].
  apply (exec_log_len_le E k1 k2 Hwf ltac:(lia) Hk2).
Qed.

(** THE FENCE/ACQUIRE LEMMA: an ordering edge delivers the source's published
    timestamp into the target read's PRE-VIEW. *)
Lemma ord_vrNew E e1 t k2 s2 :
  exec_wf E → ex_tr E !! k2 = Some s2 →
  ((ord_pw E e1 (ev_at k2) ∧ pub_w E e1 t) ∨
   (ord_pr E e1 (ev_at k2) ∧ pub_r E e1 t)) →
  (t ≤ w_vrNew (ews E k2 (es_ag s2)))%nat.
Proof.
  intros Hwf Hs2 Hcase.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  destruct Hcase as [[Hord Hpub]|[[Hord|Hord] Hpub]].
  - (* pred-W fence, write publication *)
    destruct Hord as (k1 & k2' & pr & sw & -> & Hk &
                      (kf & sf & s1 & s2'' & Hlt1 & Hlt2 & Hs1 & Hsf & Hs2'' &
                       Hag1 & Hag2 & Hlf)).
    assert (k2' = k2) as -> by (by simplify_eq).
    assert (s2'' = s2) as -> by (rewrite Hs2 in Hs2''; by simplify_eq).
    destruct Hpub as (HW & _ & ->).
    destruct HW as (s1' & Hs1' & Hw1).
    assert (s1' = s1) as -> by (rewrite Hs1 in Hs1'; by simplify_eq).
    assert (Hkf : (ev_ts E (ev_at k1) ≤ w_vwOld (ews E kf (es_ag sf)))%nat).
    { rewrite -Hag1. etrans; [exact (pub_w_vwOld E k1 s1 Hwf Hs1 Hw1)|].
      apply ws_le_vwOld,
        (exec_ws_le E (S k1) kf (es_ag s1) Hwf ltac:(lia) ltac:(lia)). }
    rewrite -Hag2. etrans; [|apply ws_le_vrNew,
      (exec_ws_le E (S kf) k2 (es_ag sf) Hwf ltac:(lia) ltac:(lia))].
    rewrite (exec_ws_fence E kf sf pr true true sw Hwf Hsf Hlf).
    etrans; [exact Hkf|]. apply fence_post_vrNew_w.
  - (* pred-R fence, acquire-read publication *)
    destruct Hord as (k1 & k2' & pw & sw & -> & Hk &
                      (kf & sf & s1 & s2'' & Hlt1 & Hlt2 & Hs1 & Hsf & Hs2'' &
                       Hag1 & Hag2 & Hlf)).
    assert (k2' = k2) as -> by (by simplify_eq).
    assert (s2'' = s2) as -> by (rewrite Hs2 in Hs2''; by simplify_eq).
    assert (Hkf : (t ≤ w_vrOld (ews E kf (es_ag sf)))%nat).
    { rewrite -Hag1.
      etrans; [exact (pub_r_vrOld E k1 s1 t Hwf Hs1 Hpub)|].
      apply ws_le_vrOld,
        (exec_ws_le E (S k1) kf (es_ag s1) Hwf ltac:(lia) ltac:(lia)). }
    rewrite -Hag2. etrans; [|apply ws_le_vrNew,
      (exec_ws_le E (S kf) k2 (es_ag sf) Hwf ltac:(lia) ltac:(lia))].
    rewrite (exec_ws_fence E kf sf true pw true sw Hwf Hsf Hlf).
    etrans; [exact Hkf|]. apply fence_post_vrNew_r.
  - (* acquire read, no fence needed *)
    destruct Hord as (k1 & k2' & s1 & s2'' & -> & Hk & Hlt & Hs1 & Hs2'' &
                      Hag & Hisr & Haq1).
    assert (k2' = k2) as -> by (by simplify_eq).
    assert (s2'' = s2) as -> by (rewrite Hs2 in Hs2''; by simplify_eq).
    rewrite -Hag.
    etrans; [exact (pub_r_vrNew_aq E k1 s1 t Hwf Hs1 Hpub Haq1)|].
    apply ws_le_vrNew,
      (exec_ws_le E (S k1) k2 (es_ag s1) Hwf ltac:(lia) ltac:(lia)).
Qed.

(** ... and a timestamp in the reader's pre-view cannot be shadowed by a write
    the reader then fails to see. *)
Lemma no_stale E k2 s2 a t t0 v0 w :
  exec_wf E → ex_tr E !! k2 = Some s2 → reads_at E k2 a t0 v0 →
  (t ≤ w_vrNew (ews E k2 (es_ag s2)))%nat → (t ≤ length (elog E k2))%nat →
  wr_b E a w → (t0 < ev_ts E w)%nat → (t < ev_ts E w)%nat.
Proof.
  intros Hwf Hs2 Hr Hv Hlen Hw Hgt.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  destruct (decide (t < ev_ts E w)%nat) as [?|Hle]; [done|exfalso].
  destruct (reads_at_byte_rd E k2 a t0 v0 Hwf Hr) as (s & Hs & [_ [_ Hnw]]).
  assert (s = s2) as -> by (rewrite Hs in Hs2; by simplify_eq).
  pose proof (load_vpre_vrNew (ews E k2 (es_ag s2)) (lb_aq (es_lb s2))) as Hvp.
  apply Hnw. apply (writes_in_log_byte (eimg E k2)). exists (ev_ts E w).
  split_and!; [lia|lia|].
  rewrite -(log_byte_final E k2 (ev_ts E w) a Hwf ltac:(lia) ltac:(lia)).
  exact (proj2 Hw).
Qed.

(* ================================================================== *)
(** * THE AXIOMS

    An axiomatic execution is the tuple (events, [po], [rf], [gmo]) derived
    above.  These are the axioms it satisfies.  The first three are
    well-formedness of [rf]; then come RVWMO's coherence and atomicity axioms
    and the preserved-program-order fragment; the last two are the
    PROMISE-FREE STRENGTHENINGS the characterization is about. *)

(** rf is total, functional and value-correct, per byte. *)
Definition ax_rf_total (E : exec) : Prop :=
  ∀ k a t v, reads_at E k a t v → ∃ w, rf_b E a w (ev_at k).
Definition ax_rf_functional (E : exec) : Prop :=
  ∀ a w1 w2 r, rf_b E a w1 r → rf_b E a w2 r → w1 = w2.
Definition ax_rf_value (E : exec) : Prop :=
  ∀ k a w t v, reads_at E k a t v → rf_b E a w (ev_at k) →
    log_byte (ex_img E) (ex_log E) (ev_ts E w) a = Some v.

(** RVWMO coherence (ppo rules 1–3 + the load-value axiom's coherence half),
    per byte: SC-per-location. *)
Definition ax_coherence (E : exec) : Prop := ∀ a e, ¬ tc (coh_rel E a) e e.

(** RVWMO's ATOMICITY axiom: no write of the same byte falls between an RMW's
    read half and its write half in [gmo]. *)
Definition ax_atomicity (E : exec) : Prop :=
  ∀ kr a w0 w, is_W E (ev_at kr) → rf_b E a w0 (ev_at kr) → wr_b E a w →
    (ev_ts E w0 < ev_ts E w)%nat → ¬ (ev_ts E w < ev_ts E (ev_at kr))%nat.

(** THE PPO FRAGMENT THE MACHINE KEEPS, in "no stale read across an ordering
    edge" form: if [e1] is ordered before the read [e2] (by a FENCE whose
    pred/succ bits cover them, or because [e1] is an acquire), and [e2] has an
    [fr] edge to a write [w] of the byte it read, then [w] is [gmo]-ABOVE the
    timestamp [e1] published.

    In cat terms this is the irreflexivity of the short [ob] cycles
    [co? ; ord ; fr] (write source) and [rf ; ord ; fr ; co?] (acquire-read
    source); full [ob]-acyclicity is the slice-2 conjecture at the bottom of
    this file. *)
Definition ax_ord (E : exec) : Prop :=
  ∀ e1 k2 s2 a w t,
    ex_tr E !! k2 = Some s2 →
    ((ord_pw E e1 (ev_at k2) ∧ pub_w E e1 t) ∨
     (ord_pr E e1 (ev_at k2) ∧ pub_r E e1 t)) →
    fr_b E a (ev_at k2) w →
    (t < ev_ts E w)%nat.

(** THE TWO PROMISE-FREE STRENGTHENINGS (design doc, Decision 1). *)
Definition ax_no_thin_air (E : exec) : Prop :=
  ∀ e, ¬ tc (λ x y, po E x y ∨ rf E x y) e e.
Definition ax_po_ww_gmo (E : exec) : Prop :=
  ∀ e1 e2, po E e1 e2 → is_W E e1 → is_W E e2 → gmo E e1 e2.

(* ================================================================== *)
(** * SOUNDNESS: every promise-free execution satisfies the axioms *)

Theorem sound_rf_total E : exec_wf E → ax_rf_total E.
Proof. intros Hwf k a t v Hr. by eapply rf_b_total. Qed.

Theorem sound_rf_functional E : exec_wf E → ax_rf_functional E.
Proof. intros Hwf a w1 w2 r H1 H2. by eapply rf_b_functional. Qed.

Theorem sound_rf_value E : exec_wf E → ax_rf_value E.
Proof. intros Hwf k a w t v Hr Hrf. by eapply rf_b_value. Qed.

(** ACYCLICITY OF [po ∪ rf] — the promise-free machine's defining property.
    Both kinds of edge point forward in execution order: [po] by definition,
    and [rf] because a load can only read a message already in the log.  So
    load buffering is impossible (design Decision 1). *)
Theorem sound_no_thin_air E : exec_wf E → ax_no_thin_air E.
Proof.
  intros Hwf. rewrite /ax_no_thin_air. apply (tc_nat_lt _ ev_ix).
  intros x y [Hpo|Hrf]; [by apply (po_ix E)|by apply (rf_ix E _ _ Hwf)].
Qed.

(** [(po ∩ W×W) ⊆ gmo] — stores append at the end of the log, so one agent's
    writes enter the global order in program order. *)
Theorem sound_po_ww_gmo E : exec_wf E → ax_po_ww_gmo E.
Proof.
  intros Hwf e1 e2 (k1 & k2 & s1 & s2 & -> & -> & Hlt & _) HW1 HW2.
  split_and!; [done|done|]. by apply ev_ts_mono.
Qed.

Theorem sound_coherence E : exec_wf E → ax_coherence E.
Proof.
  intros Hwf a. apply (tc_lexlt _ (λ e, (ets E a e, ev_ix e))).
  intros x y Hxy. by apply coh_rel_lexlt.
Qed.

Theorem sound_atomicity E : exec_wf E → ax_atomicity E.
Proof.
  intros Hwf kr a w0 w HW (_ & k & t0 & v0 & Hk & Hr & Hts0) Hw Hgt Hlt.
  assert (k = kr) as -> by (by simplify_eq).
  pose proof (rmw_read_latest E kr a t0 v0 Hwf Hr HW) as [_ Hlat].
  pose proof (reads_at_lt E kr a t0 v0 Hr) as Hkr.
  rewrite ev_ts_at in Hlt.
  apply Hlat. apply (writes_in_log_byte (eimg E kr)). exists (ev_ts E w).
  split_and!; [lia|lia|].
  rewrite -(log_byte_final E kr (ev_ts E w) a Hwf ltac:(lia) ltac:(lia)).
  exact (proj2 Hw).
Qed.

Theorem sound_ord E : exec_wf E → ax_ord E.
Proof.
  intros Hwf e1 k2 s2 a w t Hs2 Hcase Hfr.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  destruct Hfr as ((w0 & (_ & k & t0 & v0 & Hk0 & Hr & Hts0) & (_ & Hw & Hgt)) & _).
  assert (k = k2) as -> by (by simplify_eq).
  destruct (ord_lt E e1 k2 ltac:(by destruct Hcase as [[? ?]|[? ?]]; auto))
    as (k1 & -> & Hlt).
  eapply (no_stale E k2 s2 a t t0 v0 w Hwf Hs2 Hr).
  - by eapply ord_vrNew.
  - destruct Hcase as [[_ Hp]|[_ Hp]];
      [ exact (pub_w_le_log E k1 k2 t Hwf Hp Hlt ltac:(lia))
      | exact (pub_r_le_log E k1 k2 t Hwf Hp Hlt ltac:(lia)) ].
  - exact Hw.
  - lia.
Qed.

(** THE SLICE-1 SOUNDNESS THEOREM. *)
Definition axiomatic_ok (E : exec) : Prop :=
  ax_rf_total E ∧ ax_rf_functional E ∧ ax_rf_value E ∧
  ax_coherence E ∧ ax_atomicity E ∧ ax_ord E ∧
  ax_no_thin_air E ∧ ax_po_ww_gmo E.

Theorem promise_free_sound E : exec_wf E → axiomatic_ok E.
Proof.
  intros Hwf. split_and!.
  - by apply sound_rf_total.
  - by apply sound_rf_functional.
  - by apply sound_rf_value.
  - by apply sound_coherence.
  - by apply sound_atomicity.
  - by apply sound_ord.
  - by apply sound_no_thin_air.
  - by apply sound_po_ww_gmo.
Qed.

(* ================================================================== *)
(** * Execution constructors (and the non-vacuity guard)

    [exec_wf] is inhabited and closed under appending any machine step, so
    [promise_free_sound] is not vacuous.  These are also how a consumer builds
    an [exec] from its own machine's run. *)

Lemma exec_nil σ0 :
  ms_log σ0 = [] → (∀ i, ms_ws σ0 i = ws_init) → exec_wf (Exec [σ0] []).
Proof.
  intros Hlog Hws. split_and!.
  - done.
  - intros σ Hσ. simpl in Hσ. by simplify_eq.
  - intros k s ?? Hs. by rewrite /= lookup_nil in Hs.
Qed.

Lemma exec_snoc E s σ' :
  exec_wf E → mstep (stt E (length (ex_tr E))) (es_ag s) (es_lb s) σ' →
  exec_wf (Exec (ex_st E ++ [σ']) (ex_tr E ++ [s])).
Proof.
  intros (Hlen & Hinit & Hstep) Hnew. split_and!.
  - simpl. rewrite !length_app /=. lia.
  - intros σ Hσ. simpl in Hσ. rewrite lookup_app_l in Hσ; [lia|].
    by apply Hinit.
  - intros k s0 σ σ'' Hs0 Hσ Hσ''. simpl in Hs0, Hσ, Hσ''.
    destruct (decide (k < length (ex_tr E))%nat) as [Hlt|Hge].
    + rewrite lookup_app_l in Hs0; [lia|].
      rewrite lookup_app_l in Hσ; [lia|].
      rewrite lookup_app_l in Hσ''; [lia|].
      by eapply Hstep.
    + assert (k = length (ex_tr E)) as ->.
      { apply lookup_lt_Some in Hs0. rewrite length_app /= in Hs0. lia. }
      rewrite lookup_app_r in Hs0; [lia|].
      rewrite Nat.sub_diag /= in Hs0. simplify_eq.
      rewrite lookup_app_l in Hσ; [lia|].
      rewrite (stt_lookup E _ _ Hσ) in Hnew.
      rewrite lookup_app_r in Hσ''; [lia|].
      replace (S (length (ex_tr E)) - length (ex_st E))%nat with 0%nat
        in Hσ'' by lia.
      simpl in Hσ''. by simplify_eq.
Qed.

(* ================================================================== *)
(** * WHAT SLICE 1 DOES NOT DO — the slice-2 obligations

    Both statements below are written out as Rocq-shaped comments rather than
    as [Axiom]s so that nothing in this file is assumed.

    ------------------------------------------------------------------
    (1) COMPLETENESS — TODO SLICE 2.

    The other half of the characterization
    ([design/weak-memory-m6-robustness.md] §6): an axiomatically-consistent
    candidate execution is realized by the machine.  The candidate has to be
    given as data, since [exec] is the machine side; the intended statement is

<<
      Record cand := Cand {
        cd_img : image;                     (* the era-initial image *)
        cd_tr  : list estep;                (* the agents' programs, in some
                                               interleaving *)
      }.

      Conjecture promise_free_complete : forall (c : cand),
        (* the labels are internally consistent: each read's value is the one
           its rf source wrote, rf is per-byte total and functional, ... *)
        cand_wf c ->
        (* ... and the candidate satisfies every axiom of [axiomatic_ok],
           stated over the candidate's own po/rf/gmo ... *)
        cand_axiomatic_ok c ->
        (* ... then there is a machine execution with exactly these steps. *)
        exists E, exec_wf E /\ ex_tr E = cd_tr c /\ ex_img E = cd_img c.
>>

    The proof obligation is the usual one for a view machine: replay the
    candidate in [gmo] order and show each read's [readable] side condition
    holds, the per-byte coherence axiom being exactly what makes the reader's
    floor admit its rf source.  The [(po ∩ W×W) ⊆ gmo] axiom is what lets the
    replay APPEND each write at the log's top (rather than needing a promise),
    and [acyclic(po ∪ rf)] is what makes the interleaving exist at all.

    ------------------------------------------------------------------
    (2) FULL [ob]-ACYCLICITY — TODO SLICE 2.

    [ax_ord] above states the ppo content in LOCAL form (an ordering edge
    forbids one specific stale read).  The global form is the Arm-A/herd-style
    external axiom

<<
      Definition ppo (E : exec) : relation ev := ...  (* fence_between + acq_po
                                                          + po_loc_b *)
      Definition ob (E : exec) : relation ev := λ x y,
        ppo E x y ∨ rfe E x y ∨ co E x y ∨ fr E x y.
      Conjecture ax_external : forall E, exec_wf E -> forall e, ~ tc (ob E) e e.
>>

    This is NOT provable by the measure arguments used above and is the real
    work of the characterization: [fr] edges point BACKWARDS in execution order
    (a load may read a stale value long after the shadowing write executed), so
    no embedding into execution order or into a single per-byte timestamp can
    work.  Proving it means constructing the RVWMO global memory order — i.e.
    choosing a position for every READ — which is the same construction
    completeness needs, and is why the two belong in one slice.

    ------------------------------------------------------------------
    (3) KNOWN GAPS IN [ax_ord] (see the slice-1 report):

    - an INTERNAL rf edge (the read is forwarded from the agent's own
      po-earlier store) publishes only the weaker banked view, so [pub_r]
      excludes it — as [obs]'s exclusion of [rfi] does in the cat models.
      What the machine actually guarantees there is the STORE's fence floor
      [w_vwNew] at store time (design Decision 3, "the weakest sound view"),
      which is a strictly weaker publication and is not stated here;
    - RVWMO ppo rule 6 (release annotation on the SUCCESSOR) is not modelled,
      because the promise-free machine does not enforce it: [.rl] only feeds
      [w_vRel].  Vacuous for this kernel (the image contains no release store)
      but it is a place where this machine is WEAKER than RVWMO, which is the
      direction that needs an argument. *)

(* ------------------------------------------------------------------ *)
(** ** The machine invariant along a run, and the event pre-view

    (Lifted here from [WeakAxiomatic2] by the W4 batch: [rd_ok] and [exec]
    are defined in THIS file, so this is their home; slice 2 proved them
    against a frozen [.vo].)

    [WeakMem.ws_bounded] instantiated at the execution's own log, and
    [evpre] — the [load_vpre] a step ran at, as a total function of the
    event. *)

(** The [Forall] shape [load_post_run_bounded] wants, from an [rd_ok]. *)
Lemma rd_ok_ts_bounded img log ws aq base ts vs :
  rd_ok img log ws aq base ts vs →
  Forall (λ t, (t ≤ length log)%nat) ts.
Proof.
  intros [Hlen Hall]. apply Forall_lookup_2. intros j t Hj.
  destruct (lookup_lt_is_Some_2 vs j) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  destruct (Hall j t v Hj Hv) as [Hb _].
  eapply log_byte_bounded. by eexists.
Qed.

(* ================================================================== *)
(** * 2. The machine invariant along a run: every view is a real timestamp

    [WeakMem.ws_bounded] instantiated at the execution's own log.  Slice 1
    never needed it (its measures were all timestamps read off the trace);
    slice 2 does, because the read's position [opos] contains [load_vpre],
    and "the position of a read is below the log" is what makes a later write
    strictly above it. *)

Lemma exec_ws_bounded E k i :
  exec_wf E → (k ≤ length (ex_tr E))%nat →
  ws_bounded (ews E k i) (length (elog E k)).
Proof.
  intros Hwf. induction k as [|k IH]; intros Hk.
  { rewrite (exec_ws_init E i Hwf). apply ws_bounded_init. }
  destruct (exec_tr_lookup E k ltac:(lia)) as [s Hs].
  pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  pose proof (IH ltac:(lia)) as Hb.
  pose proof (exec_log_len_le E k (S k) Hwf ltac:(lia) ltac:(lia)) as Hlen.
  destruct (decide (i = es_ag s)) as [->|Hne]; last first.
  { rewrite /ews (mstep_ws_ne _ _ _ _ i Hstep Hne).
    eapply ws_bounded_mono; [exact Hb|exact Hlen]. }
  destruct (es_lb s) as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc]
    eqn:Hl.
  - (* load *)
    rewrite (exec_ws_load E k s aq base ts vs Hwf Hs Hl).
    pose proof (exec_rd_ok E k s base ts vs Hwf Hs ltac:(by rewrite Hl)) as Hrd.
    eapply ws_bounded_mono; [|exact Hlen].
    apply load_post_run_bounded; [exact Hb|].
    by eapply rd_ok_ts_bounded.
  - (* store *)
    rewrite (exec_ws_store E k s rl base vs _ Hwf Hs Hl).
    assert (Hts : ev_ts E (ev_at k) = length (elog E (S k))).
    { symmetry. by apply (ev_ts_next E k s Hwf Hs); rewrite Hl. }
    apply (store_post_run_bounded _ _ _ _ _ (length (elog E k)));
      [exact Hb|rewrite Hts; lia|exact Hlen].
  - (* fence *)
    rewrite (exec_ws_fence E k s pr pw sr sw Hwf Hs Hl).
    eapply ws_bounded_mono; [|exact Hlen]. by apply fence_post_bounded.
  - (* rmw *)
    rewrite (exec_ws_rmw E k s aq rl base ts rvs wvs _ Hwf Hs Hl).
    pose proof (exec_rd_ok E k s base ts rvs Hwf Hs ltac:(by rewrite Hl)) as Hrd.
    assert (Hts : ev_ts E (ev_at k) = length (elog E (S k))).
    { symmetry. by apply (ev_ts_next E k s Hwf Hs); rewrite Hl. }
    apply (store_post_run_bounded _ _ _ _ _ (length (elog E k)));
      [|rewrite Hts; lia|exact Hlen].
    apply load_post_run_bounded; [exact Hb|].
    by eapply rd_ok_ts_bounded.
Qed.

(* ================================================================== *)
(** * 3. [evpre]: the load pre-view an event ran at

    A total function on events (junk off the run, like slice 1's [stt]).  For
    a read event it is exactly the [load_vpre] its [readable] side conditions
    were checked against. *)

Definition evpre (E : exec) (e : ev) : nat :=
  match e with
  | ev_init => 0%nat
  | ev_at k =>
      match ex_tr E !! k with
      | Some s => load_vpre (ews E k (es_ag s)) (lb_aq (es_lb s))
      | None => 0%nat
      end
  end.

Lemma evpre_at E k s :
  ex_tr E !! k = Some s →
  evpre E (ev_at k) = load_vpre (ews E k (es_ag s)) (lb_aq (es_lb s)).
Proof. by move=> /= ->. Qed.

(** Bounded, like every other view. *)
Lemma evpre_le_log E k :
  exec_wf E → (k ≤ length (ex_tr E))%nat →
  (evpre E (ev_at k) ≤ length (elog E k))%nat.
Proof.
  intros Hwf Hk. rewrite /evpre. destruct (ex_tr E !! k) as [s|] eqn:Hs; [|lia].
  apply load_vpre_bounded. by apply exec_ws_bounded.
Qed.

(** A READ's pre-view is under the agent's [w_vrNew] IMMEDIATELY AFTER the
    step.  For a plain read this is trivial ([load_vpre] IS [w_vrNew] there);
    for an ACQUIRE it is the content of [load_post_at]'s [aq] arm, and it is
    what makes the pre-view monotone along an agent's program even though
    [load_vpre] joins the (non-monotone-looking) [w_vRel]. *)
Lemma evpre_le_vrNew_post E k s a t v :
  exec_wf E → ex_tr E !! k = Some s → reads_at E k a t v →
  (evpre E (ev_at k) ≤ w_vrNew (ews E (S k) (es_ag s)))%nat.
Proof.
  intros Hwf Hs Hr. rewrite (evpre_at E k s Hs).
  destruct Hr as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & Ha).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct (lb_aq (es_lb s)) eqn:Haq; last first.
  { rewrite /load_vpre /= Nat.max_0_r.
    apply ws_le_vrNew, (exec_ws_le E k (S k) (es_ag s) Hwf ltac:(lia)).
    pose proof (lookup_lt_Some _ _ _ Hs). lia. }
  destruct (lb_rd_cases _ _ _ _ Hrd) as (aq & Haq' & [Hl|(rl & wvs & kc & Hl)]);
    rewrite Haq in Haq'; subst aq.
  - rewrite (exec_ws_load E k s true base ts vs Hwf Hs Hl).
    by apply (load_post_run_vrNew_aq_vpre _ _ _ j t).
  - rewrite (exec_ws_rmw E k s true rl base ts vs wvs _ Hwf Hs Hl).
    etrans; [by apply (load_post_run_vrNew_aq_vpre _ base ts j t)|].
    apply ws_le_vrNew, store_post_run_le.
Qed.

(** ... hence the pre-view is monotone along one agent's program order. *)
Lemma evpre_mono E k1 k2 s1 s2 a t v :
  exec_wf E → (k1 < k2)%nat →
  ex_tr E !! k1 = Some s1 → ex_tr E !! k2 = Some s2 → es_ag s1 = es_ag s2 →
  reads_at E k1 a t v →
  (evpre E (ev_at k1) ≤ evpre E (ev_at k2))%nat.
Proof.
  intros Hwf Hlt Hs1 Hs2 Hag Hr.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  etrans; [by eapply evpre_le_vrNew_post|].
  rewrite (evpre_at E k2 s2 Hs2) -Hag.
  etrans; [apply ws_le_vrNew,
    (exec_ws_le E (S k1) k2 (es_ag s1) Hwf ltac:(lia) ltac:(lia))|].
  rewrite Hag. apply load_vpre_vrNew.
Qed.

(** The other half of the same fact: a publication delivered into the target's
    [w_vrNew] is under the target's pre-view. *)
Lemma vrNew_le_evpre E k s :
  ex_tr E !! k = Some s →
  (w_vrNew (ews E k (es_ag s)) ≤ evpre E (ev_at k))%nat.
Proof. intros Hs. rewrite (evpre_at E k s Hs). apply load_vpre_vrNew. Qed.

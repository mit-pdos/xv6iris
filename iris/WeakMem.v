(** * WeakMem.v — the promise-free view machine (M0 model spike)

    This is the M0 spike of the RVWMO model described in
    [claude-notes/design/weak-memory.md]: the Promising-RISC-V machine shape
    with the promise machinery deliberately omitted (every store appends at the
    end of the global log), and with syntactic dependency tracking (ppo 9–13)
    dropped.

    DELIBERATELY DEPENDENCY-FREE.  This file imports only stdpp: no Iris, no
    Sail.  The machine types are abstracted for the spike —

      - addresses are [Z]       (the real machine instantiates at [Arch.pa]),
      - bytes are [bv 8]        (as in the tree today),
      - agents are [nat]        (the real machine instantiates at [CPU]).

    Nothing below inspects an agent identifier, and addresses are used only as
    [gmap] keys and under [Z.le]/[Z.sub], so the instantiation at [Arch.pa]
    needs exactly: [EqDecision], [Countable], and a [pa_add]-flavoured
    "byte i of a message" arithmetic (see [msg_byte]).  Beware the
    [gmap Arch.pa _] Countable trap recorded in the durable notes: a file that
    also imports [SailStdpp.Values] elaborates the key type's [Countable]
    instance differently, so the eventual instantiation must NOT write
    [gmap Arch.pa (bv 8)] as an explicit binder type in a Sail-importing file.
*)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.

Local Open Scope Z_scope.

(** Agents (harts, DMA engines).  Abstract in the spike. *)
Notation agent := nat.

(** The era-initial image is a PARTIAL FUNCTION on [Z], not a [gmap Z _].
    M1's interpreter ([WeakInterp.v]) keeps the image in the tree's own
    [gmap Arch.pa (bv 8)] form and converts at the seam ([WeakInterp.img_z]),
    so a [gmap Z _] here would force a key-space [kmap] — and with it exactly
    the [gmap Arch.pa _] Countable trap the header warns about.  A function
    parameter costs nothing (the litmus image is still built as a [gmap] and
    read through one lambda) and makes the seam a definition, not a theorem. *)
Definition image : Type := Z → option (bv 8).

(* ------------------------------------------------------------------ *)
(** ** Messages and the global write log *)

(** THE MESSAGE CLASS (M6 D-M6-6).  An INERT syntactic tag recording how the
    write was issued, so that Layer 2's classification is a FUNCTION of the
    machine state rather than a ghost existential (see
    [claude-notes/projects/weak-memory-m6.md], W3).  No rule of any machine in
    this tree inspects it — it exists only for the M6 statements, exactly like
    [wm_tid].

      - [WCexcl]  — the write half of an exclusive/[ak_latest] access
                    (the walker's CAS, an AMO): SCexcl.
      - [WCrel]   — a release-class publication: the store is an [.rl] store,
                    or it is the first store after a [pw ∧ sw] fence
                    ([w_relp], the RISC-V [fence rw,w; sd flag] idiom): SCfenced.
      - [WCplain] — everything else, i.e. the [↦w{1}]-owned stores: SCowned. *)
Inductive wm_class := WCplain | WCrel | WCexcl.

Global Instance wm_class_eq_dec : EqDecision wm_class.
Proof. solve_decision. Defined.

(** One write event.  It covers the byte range [wm_pa, wm_pa + |wm_data|).
    [wm_tid] names the AGENT that appended the message; every agent of the
    composed machine — harts AND the disk — has an index, so [None] is now
    only the never-used boot-era slot (the DMA-tid unification, seam 1a of
    [claude-notes/completed/weak-memory-lift.md]: [WeakLang.wmsgs_of_map]
    stamps [Some WeakLang.n_disk], matching the disk's index in
    [WeakCompose.xv6_ps]).  Predicates that used to exempt [wm_tid = None]
    are re-keyed on IS-A-HART ([tid_hart] below).  [wm_ak] is the inert class
    field above; it is LAST so that positional literals that predate it fail
    loudly rather than silently permuting. *)
Record wmsg := WMsg {
  wm_pa   : Z;
  wm_data : list (bv 8);
  wm_tid  : option agent;
  wm_ak   : wm_class;
}.
Add Printing Constructor wmsg.

Global Instance wmsg_eq_dec : EqDecision wmsg.
Proof. solve_decision. Defined.

(** The byte message [m] writes at address [a] (None if [a] is outside its
    range). *)
Definition msg_byte (m : wmsg) (a : Z) : option (bv 8) :=
  if bool_decide (wm_pa m ≤ a)
  then wm_data m !! Z.to_nat (a - wm_pa m)
  else None.

(* ------------------------------------------------------------------ *)
(** ** The two tid-space notions both towers share

    [tid_hart nh t] — "[t] is one of the first [nh] agents", i.e. A HART.
    The DMA-tid unification (seam 1a) gives the disk an ordinary agent index
    ([nh] itself), so "is a hart" — not "[wm_tid = None]" — is what every
    ownership/publication invariant is keyed on.  The bound is a PARAMETER
    here because [WeakMem] is deliberately stdpp-only and knows no [NCPU];
    [WeakLang.tid_is_hart] and [WeakCompose] fix it at [RiscvLang.NCPU]. *)
Definition tid_hart (nh : nat) (t : option agent) : Prop :=
  ∃ i : agent, t = Some i ∧ (i < nh)%nat.

Lemma tid_hart_ne_disk nh t : tid_hart nh t → t ≠ Some nh.
Proof. intros (i & -> & Hlt) [= ->]. lia. Qed.

Lemma tid_hart_none nh : ¬ tid_hart nh None.
Proof. by intros (i & ? & _). Qed.

(** *** PUBLICATION, PURELY OVER THE LOG (φ-upgrade §1b, delta 1).

    [wpublished log tid p] — "position [p] has been published by agent
    [tid]": a LATER message of the SAME agent is release-class.  Since
    [WeakMem.store_post] raises the storing agent's [w_pub] to the store's
    own timestamp whenever the store is release-class, and [w_pub] only ever
    grows, this IMPLIES the watermark reading — and it is a predicate of the
    LOG ALONE, which is what lets the Iris-side C/D/S invariant keep
    [wlat_interp]'s arity AND what lets Layer 1 ([WeakRobustMain.pub_of])
    spell publication without reaching into the agent vector.

    IT LIVES HERE, not in [WeakGhost] or [WeakRobustMain], because BOTH
    towers must mean the same thing by it: the φ export produces
    [WeakGhost.no_violation] (stated with this predicate) and Layer 1
    consumes [WeakRobust.violation cls_of pub_of] (also stated with it), and
    the lift's whole job is to identify the two. *)
Definition wpublished (log : list wmsg) (tid : option agent) (p : nat) : Prop :=
  ∃ (q : nat) (mq : wmsg),
    (p ≤ q)%nat ∧ log !! q = Some mq ∧ wm_tid mq = tid ∧ wm_ak mq = WCrel.

Lemma wpublished_app log ms tid p :
  wpublished log tid p → wpublished (log ++ ms) tid p.
Proof.
  intros (q & mq & Hle & Hq & Ht & Hk). exists q, mq. split_and!; try done.
  rewrite lookup_app_l //. by eapply lookup_lt_Some.
Qed.

(** Memory is an era-initial image plus an append-only log.  Timestamp 0 is the
    image; timestamp [i+1] is log entry [i].  [log_byte img log t a] is the
    value timestamp [t] writes at byte [a], or None if [t] does not write [a].

    One shared total order over all writes is exactly what multi-copy atomicity
    licenses (design doc, Decision 1). *)
Definition log_byte (img : image) (log : list wmsg) (t : nat) (a : Z)
    : option (bv 8) :=
  match t with
  | O => img a
  | S i => m ← log !! i; msg_byte m a
  end.

Lemma log_byte_0 img log a : log_byte img log 0 a = img a.
Proof. done. Qed.

Lemma log_byte_S img log i a :
  log_byte img log (S i) a = (log !! i) ≫= (λ m, msg_byte m a).
Proof. done. Qed.

(** A timestamp that writes anything is within the log. *)
Lemma log_byte_bounded img log t a :
  is_Some (log_byte img log t a) → (t ≤ length log)%nat.
Proof.
  destruct t as [|i]; [lia|]. rewrite log_byte_S.
  intros [v Hv]. destruct (log !! i) as [m|] eqn:Hm; simplify_eq/=.
  apply lookup_lt_Some in Hm. lia.
Qed.

(** The log is append-only, so old timestamps keep their values. *)
Lemma log_byte_app img log l t a :
  (t ≤ length log)%nat → log_byte img (log ++ l) t a = log_byte img log t a.
Proof.
  destruct t as [|i]; [done|]. intros ?.
  rewrite !log_byte_S lookup_app_l //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [writes_in]: some timestamp in a half-open view window writes a byte *)

(** [writes_in log a lo hi] — some timestamp [t] with [lo < t ≤ hi] writes
    byte [a].  Since [t > lo ≥ 0], the image is never consulted, which is why
    this does not mention [img]. *)
Definition writes_in (log : list wmsg) (a : Z) (lo hi : nat) : Prop :=
  ∃ t : nat, (lo < t)%nat ∧ (t ≤ hi)%nat ∧
             ∃ m, log !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a).

(** The bridge to [log_byte] at any image. *)
Lemma writes_in_log_byte img log a lo hi :
  writes_in log a lo hi ↔
  ∃ t : nat, (lo < t)%nat ∧ (t ≤ hi)%nat ∧ is_Some (log_byte img log t a).
Proof.
  split.
  - intros (t & Hlo & Hhi & m & Hm & [v Hv]).
    exists t. split_and!; [done|done|].
    destruct t as [|i]; [lia|]. rewrite log_byte_S.
    replace (S i - 1)%nat with i in Hm by lia. rewrite Hm /=. exists v. exact Hv.
  - intros (t & Hlo & Hhi & Hs).
    exists t. split_and!; [done|done|].
    destruct t as [|i]; [lia|]. rewrite log_byte_S in Hs.
    destruct (log !! i) as [m|] eqn:Hm; simpl in Hs; [|by destruct Hs].
    exists m. replace (S i - 1)%nat with i by lia. by split.
Qed.

Lemma writes_in_mono log a lo hi lo' hi' :
  (lo' ≤ lo)%nat → (hi ≤ hi')%nat → writes_in log a lo hi → writes_in log a lo' hi'.
Proof. intros ?? (t & ? & ? & ?). exists t. split_and!; [lia|lia|done]. Qed.

Lemma writes_in_mono_hi log a lo hi hi' :
  (hi ≤ hi')%nat → writes_in log a lo hi → writes_in log a lo hi'.
Proof. intros. by eapply writes_in_mono. Qed.

Lemma writes_in_app log l a lo hi :
  writes_in log a lo hi → writes_in (log ++ l) a lo hi.
Proof.
  intros (t & ? & ? & m & Hm & ?). exists t. split_and!; [done|done|].
  exists m. rewrite lookup_app_l //. apply lookup_lt_Some in Hm. lia.
Qed.

(** A write in a window that predates the extension was already there. *)
Lemma writes_in_app_inv log l a lo hi :
  (hi ≤ length log)%nat → writes_in (log ++ l) a lo hi → writes_in log a lo hi.
Proof.
  intros Hle (t & ? & ? & m & Hm & ?). exists t. split_and!; [done|done|].
  assert ((log ++ l) !! (t - 1)%nat = log !! (t - 1)%nat) as Heq.
  { apply lookup_app_l. lia. }
  exists m. rewrite -Heq. by split.
Qed.

(** Any witness is inside the log, so the window may be clipped to it. *)
Lemma writes_in_clip log a lo hi :
  writes_in log a lo hi → writes_in log a lo (Nat.min hi (length log)).
Proof.
  intros (t & ? & ? & m & Hm & ?).
  pose proof (lookup_lt_Some _ _ _ Hm) as Hlt.
  exists t. split_and!; [done|lia|]. exists m. by split.
Qed.

Lemma not_writes_in_clip log a lo hi :
  ¬ writes_in log a lo (Nat.min hi (length log)) → ¬ writes_in log a lo hi.
Proof. intros Hn Hw. apply Hn, writes_in_clip, Hw. Qed.

(* ------------------------------------------------------------------ *)
(** ** Deciding [writes_in] by reflection

    Every concrete side condition of the model — a litmus verdict, and every
    admissibility check the functional interpreter [WeakInterp.wexec] performs
    — is "no message in this window writes this byte" over a concrete log.
    Reflect it once, here, so both consumers share the decision procedure. *)

Definition msg_writesb (m : wmsg) (a : Z) : bool :=
  match msg_byte m a with Some _ => true | None => false end.

Lemma msg_writesb_true m a : msg_writesb m a = true ↔ is_Some (msg_byte m a).
Proof.
  rewrite /msg_writesb. destruct (msg_byte m a) as [v|].
  - split; [intros _; by eexists|done].
  - split; [done|by intros [? ?]].
Qed.

Lemma msg_writesb_false m a : msg_writesb m a = false ↔ msg_byte m a = None.
Proof. rewrite /msg_writesb. by destruct (msg_byte m a). Qed.

Definition writes_inb (log : list wmsg) (a : Z) (lo hi : nat) : bool :=
  existsb (λ t, bool_decide (lo < t)%nat && bool_decide (t ≤ hi)%nat &&
                match log !! (t - 1)%nat with
                | Some m => msg_writesb m a
                | None => false
                end)
          (seq 1 (length log)).

Lemma writes_inb_spec log a lo hi :
  writes_in log a lo hi ↔ writes_inb log a lo hi = true.
Proof.
  rewrite /writes_inb existsb_exists. split.
  - intros (t & Hlo & Hhi & m & Hm & Hs).
    pose proof (lookup_lt_Some _ _ _ Hm) as Hlt.
    exists t. split.
    + apply elem_of_list_In, elem_of_seq. lia.
    + rewrite Hm /msg_writesb. destruct Hs as [v Hv]. rewrite Hv /=.
      rewrite andb_true_r andb_true_iff.
      split; by apply bool_decide_eq_true_2.
  - intros (t & Ht & Hb). apply elem_of_list_In, elem_of_seq in Ht.
    rewrite !andb_true_iff in Hb. destruct Hb as [[H1 H2] H3].
    apply bool_decide_eq_true_1 in H1. apply bool_decide_eq_true_1 in H2.
    destruct (log !! (t - 1)%nat) as [m|] eqn:Hm; [|done].
    exists t. split_and!; [done|done|]. exists m. split; [done|].
    rewrite /msg_writesb in H3. destruct (msg_byte m a) as [v|]; [|done].
    by exists v.
Qed.

Lemma not_writes_in_compute log a lo hi :
  writes_inb log a lo hi = false → ¬ writes_in log a lo hi.
Proof. intros Hb Hw. apply writes_inb_spec in Hw. by rewrite Hw in Hb. Qed.

Lemma writes_in_compute log a lo hi :
  writes_inb log a lo hi = true → writes_in log a lo hi.
Proof. apply writes_inb_spec. Qed.

Lemma not_writes_inb log a lo hi :
  writes_inb log a lo hi = false ↔ ¬ writes_in log a lo hi.
Proof.
  split; [apply not_writes_in_compute|].
  intros Hn. destruct (writes_inb log a lo hi) eqn:Hb; [|done].
  by destruct Hn; apply writes_in_compute.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The per-agent weak state *)

(** The Promising-RISC-V thread state minus promises, minus register views,
    minus the exclusives bank (design doc, Decisions 1 and 3). *)
Record wstate := WState {
  w_coh   : gmap Z nat;         (* per-byte coherence floor; default 0 *)
  w_vrOld : nat;                (* max post-view of past loads  *)
  w_vwOld : nat;                (* max post-view of past stores *)
  w_vrNew : nat;                (* pre-view floor for future loads  *)
  w_vwNew : nat;                (* pre-view floor for future stores *)
  w_vRel  : nat;                (* release view; inert until .rl appears *)
  w_fwd   : gmap Z (nat * nat); (* forward bank: timestamp + fwd view *)
  (* THE TWO M6 INERT COMPONENTS (D-M6-6, revised semantics 2026-08-12).
     Read by NO rule of any machine in this tree; they exist so that
     "published" is a total function of the state.

     [w_pub]  — the publication watermark: every log position [p] with
                [S p ≤ w_pub] of this agent is PUBLISHED.  Raised to the
                store's own timestamp at a store taken with [w_relp] set, and
                at an [rl] store.  Raising it at the FENCE instead would leave
                the flag store itself — the very message racy readers read —
                forever unpublished.
     [w_relp] — pending release: SET by a [pw ∧ sw] fence, CLEARED by the
                agent's next store (which is the publication).  It TOGGLES, so
                it is deliberately absent from [ws_le]. *)
  w_pub   : nat;
  w_relp  : bool;
}.
Add Printing Constructor wstate.

(** Coherence lookup with default 0. *)
Definition coh (ws : wstate) (a : Z) : nat := default 0%nat (w_coh ws !! a).

Definition ws_init : wstate :=
  {| w_coh := ∅; w_vrOld := 0; w_vwOld := 0; w_vrNew := 0; w_vwNew := 0;
     w_vRel := 0; w_fwd := ∅; w_pub := 0; w_relp := false |}.

Lemma coh_init a : coh ws_init a = 0%nat.
Proof. done. Qed.

Lemma coh_upd_eq m vrO vwO vrN vwN vR fwd pb rp a n :
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
         w_pub := pb; w_relp := rp |} a = n.
Proof. rewrite /coh /= lookup_insert //. Qed.

Lemma coh_upd_ne m vrO vwO vrN vwN vR fwd pb rp a a' n :
  a' ≠ a →
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
         w_pub := pb; w_relp := rp |} a'
  = default 0%nat (m !! a').
Proof. intros ?. rewrite /coh /= lookup_insert_ne //. Qed.

(* ------------------------------------------------------------------ *)
(** ** Readability *)

(** [readable img log ws vpre a t]: the agent in state [ws] with load pre-view
    [vpre] may read timestamp [t] for byte [a].  Two conditions:
    (i) [t] writes [a]; (ii) no timestamp strictly between [t] and the agent's
    floor [vpre ⊔ coh(a)] writes [a] — i.e. [t] is not stale relative to
    anything the agent has already observed. *)
Definition readable (img : image) (log : list wmsg) (ws : wstate)
    (vpre : nat) (a : Z) (t : nat) : Prop :=
  is_Some (log_byte img log t a) ∧
  ¬ writes_in log a t (Nat.max vpre (coh ws a)).

(** The decision procedure [WeakInterp.wexec] checks a read with. *)
Definition readableb (img : image) (log : list wmsg) (ws : wstate)
    (vpre : nat) (a : Z) (t : nat) : bool :=
  match log_byte img log t a with
  | Some _ => negb (writes_inb log a t (Nat.max vpre (coh ws a)))
  | None => false
  end.

Lemma readableb_spec img log ws vpre a t :
  readableb img log ws vpre a t = true ↔ readable img log ws vpre a t.
Proof.
  rewrite /readableb /readable. destruct (log_byte img log t a) as [v|] eqn:Hv.
  - rewrite negb_true_iff not_writes_inb. split.
    + intros ?. split; [by eexists|done].
    + by intros [_ ?].
  - split; [done|]. by intros [[? ?] _].
Qed.

(** Readability is ANTI-monotone in the pre-view: a smaller floor admits more
    timestamps.  NOTE what is deliberately absent: readability is NOT
    downward-closed in [t] (a smaller timestamp can be blocked by an
    intervening write to [a]), and it is NOT upward-closed in [t] either
    (a larger timestamp need not write [a] at all).  These two are exactly the
    coherence constraints, so there is no monotonicity lemma in [t] to state. *)
Lemma readable_anti_vpre img log ws vpre vpre' a t :
  (vpre' ≤ vpre)%nat → readable img log ws vpre a t → readable img log ws vpre' a t.
Proof.
  intros Hle [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(** THE WORKHORSE of the litmus proofs: if the agent's pre-view already covers
    a write to [a], the era-initial image is no longer readable. *)
Lemma readable_not_init img log ws vpre a t :
  readable img log ws vpre a t → writes_in log a 0 vpre → t ≠ 0%nat.
Proof.
  intros [_ Hn] Hw ->. apply Hn. eapply writes_in_mono_hi; [|done]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Coherent (latest) reads

    Two consumers: the AMO/exclusive read half, whose atomicity constraint is
    exactly this side condition, and the reads the design doc declares
    coherent — instruction fetch and the page-table walker (Decision 6).
    [latest] pins the timestamp uniquely ([latest_unique]), so a coherent read
    is deterministic even though it is stated relationally. *)

Definition latest (img : image) (log : list wmsg) (a : Z) (t : nat) : Prop :=
  is_Some (log_byte img log t a) ∧ ¬ writes_in log a t (length log).

Lemma latest_unique img log a t t' :
  latest img log a t → latest img log a t' → t = t'.
Proof.
  intros [Ht Hnt] [Ht' Hnt'].
  destruct (decide (t < t')%nat) as [Hlt|?].
  { exfalso. apply Hnt. apply (writes_in_log_byte img). exists t'.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht'). }
  destruct (decide (t' < t)%nat) as [Hlt'|?].
  { exfalso. apply Hnt'. apply (writes_in_log_byte img). exists t.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht). }
  lia.
Qed.

(** A latest timestamp is readable at any pre-view: nothing above it writes
    [a] at all, so in particular nothing in the agent's window does. *)
Lemma latest_readable img log ws vpre a t :
  (Nat.max vpre (coh ws a) ≤ length log)%nat →
  latest img log a t → readable img log ws vpre a t.
Proof.
  intros Hle [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(** The COMPUTED latest timestamp: the index (+1) of the last message writing
    [a], or 0 (the era-initial image) if none does. *)
Definition latest_ts_acc (log : list wmsg) (a : Z) : nat * nat :=
  foldl (λ p m, (S p.1, if msg_writesb m a then S p.1 else p.2)) (0%nat, 0%nat) log.

Definition latest_ts (log : list wmsg) (a : Z) : nat := (latest_ts_acc log a).2.

Lemma latest_ts_acc_fst log a : (latest_ts_acc log a).1 = length log.
Proof.
  rewrite /latest_ts_acc. induction log as [|m l IH] using rev_ind; [done|].
  rewrite foldl_app /= IH length_app /=. lia.
Qed.

Lemma latest_ts_nil a : latest_ts [] a = 0%nat.
Proof. done. Qed.

Lemma latest_ts_app log m a :
  latest_ts (log ++ [m]) a =
  (if msg_writesb m a then S (length log) else latest_ts log a).
Proof.
  rewrite /latest_ts /latest_ts_acc foldl_app /=.
  rewrite -/(latest_ts_acc log a) latest_ts_acc_fst.
  by destruct (msg_writesb m a).
Qed.

Lemma latest_ts_le log a : (latest_ts log a ≤ length log)%nat.
Proof.
  induction log as [|m l IH] using rev_ind; [done|].
  rewrite latest_ts_app length_app /=. destruct (msg_writesb m a); lia.
Qed.

(** Nothing above [latest_ts] writes [a] — unconditionally, including the
    "nothing writes [a] at all" case, where [latest_ts = 0]. *)
Lemma latest_ts_top log a : ¬ writes_in log a (latest_ts log a) (length log).
Proof.
  induction log as [|m l IH] using rev_ind.
  { intros (t & ? & ? & ?). simpl in *. lia. }
  rewrite latest_ts_app length_app /=.
  destruct (msg_writesb m a) eqn:Hm.
  - intros (t & ? & ? & ?). lia.
  - intros (t & Hlo & Hhi & mm & Hmm & Hs).
    destruct (decide (t ≤ length l)%nat) as [Hle|Hgt].
    + apply IH. exists t. split_and!; [done|done|]. exists mm.
      rewrite lookup_app_l in Hmm; [lia|]. by split.
    + assert (t = S (length l)) as -> by lia.
      replace (S (length l) - 1)%nat with (length l) in Hmm by lia.
      rewrite lookup_app_r in Hmm; [lia|].
      rewrite Nat.sub_diag /= in Hmm. simplify_eq.
      apply msg_writesb_false in Hm. rewrite Hm in Hs. by destruct Hs.
Qed.

Lemma latest_ts_latest img log a :
  is_Some (log_byte img log (latest_ts log a) a) → latest img log a (latest_ts log a).
Proof. intros ?. split; [done|apply latest_ts_top]. Qed.

(** [latest_ts] is either 0 (nothing in the log writes [a]) or the index of a
    message that does. *)
Lemma latest_ts_writes log a :
  latest_ts log a = 0%nat ∨
  ∃ i m, latest_ts log a = S i ∧ log !! i = Some m ∧ is_Some (msg_byte m a).
Proof.
  induction log as [|m l IH] using rev_ind; [by left|].
  rewrite latest_ts_app. destruct (msg_writesb m a) eqn:Hm.
  - right. exists (length l), m. split_and!; [done| |].
    + rewrite lookup_app_r; [lia|]. rewrite Nat.sub_diag //.
    + by apply msg_writesb_true.
  - destruct IH as [Hz|(i & m' & Hr & Hlk & Hs)]; [by left|].
    right. exists i, m'. split_and!; [exact Hr| |exact Hs].
    rewrite lookup_app_l; [|exact Hlk]. by apply lookup_lt_Some in Hlk.
Qed.

(** If ANY timestamp holds a value for [a], then so does [latest_ts]. *)
Lemma latest_ts_some img log a t :
  is_Some (log_byte img log t a) →
  is_Some (log_byte img log (latest_ts log a) a).
Proof.
  intros Ht. destruct (latest_ts_writes log a) as [Hz|(i & m & Hr & Hlk & Hs)].
  - rewrite Hz log_byte_0. destruct t as [|i]; [exact Ht|exfalso].
    apply (latest_ts_top log a). rewrite Hz.
    apply (writes_in_log_byte img). exists (S i).
    split_and!; [lia|exact (log_byte_bounded _ _ _ _ Ht)|exact Ht].
  - rewrite Hr log_byte_S Hlk /=. exact Hs.
Qed.

(** Hence [latest_ts] IS the latest timestamp whenever one exists — the fact
    that makes a coherent read deterministic. *)
Lemma latest_ts_eq img log a t : latest img log a t → latest_ts log a = t.
Proof.
  intros Hl. apply (latest_unique img log a);
    [|exact Hl].
  split; [exact (latest_ts_some img log a t (proj1 Hl))|apply latest_ts_top].
Qed.

(** SC DEGENERACY.  An agent whose read floor already covers the whole log has
    no read choice: readability collapses to [latest]. *)
Lemma readable_all_seen img log ws vpre a t :
  (length log ≤ vpre)%nat → readable img log ws vpre a t → latest img log a t.
Proof.
  intros Hall [Hs Hn]. split; [done|]. intros Hw. apply Hn.
  eapply writes_in_mono_hi; [|done]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The step functions *)

(** Loads.  Pre-view [vpre = vrNew ⊔ (aq ? vRel)]. *)
Definition load_vpre (ws : wstate) (aq : bool) : nat :=
  Nat.max (w_vrNew ws) (if aq then w_vRel ws else 0%nat).

(** THE FORWARD BANK, wired into the read view at M1 (design doc, Decision 3).

    A load that reads the timestamp the agent's own last store to [a] left in
    the bank is FORWARDED: it takes the view the bank recorded instead of the
    timestamp itself.  Any other timestamp contributes [t] as before.

    WHAT THE BANK RECORDS (corrected 2026-08-17, deps design §2.3′ D-7).
    Promising-ARM/RISC-V banks [FwdItem.mk ts (join view_loc view_val) ex]:
    the store's ADDRESS and DATA dependency views, which is RVWMO ppo 12 —
    "a load that reads an intermediate store inherits that store's syntactic
    dependencies", and nothing else.  In a machine with no register views
    (today's) that join is [0], so [store_post] banks [0]; the dependency
    track (D2) will replace it by [V(asrc) ⊔ V(dsrc)].
    M1 banked [w_vwNew ws] — the store's FENCE FLOOR — instead, and described
    it as "the weakest sound choice".  That was the wrong polarity: the fence
    floor is ≥ PARM's value, so it makes the forwarded read's post-view LARGER
    and hence REMOVES hardware behaviours (e.g. [fence rw,w; st x; ld x (fwd);
    fence r,r; ld y] ordered [ld y] after the pre-fence accesses in our
    machine but not in RVWMO).  Smaller is the sound direction here: a
    forwarded read is the one place where the model deliberately declines to
    inherit ordering, and [0] is exactly PARM's dependency-free value.

    Two notes on faithfulness to Promising-ARM's [read_view], which this
    mirrors:
    - Forwarding is DISABLED for an acquire load ([if aq then t]).  PARM does
      the same: an acquire may not take the weaker forwarded view.  This is
      the arm the kernel's [amoswap.w.aq] takes, so the kernel's acquires are
      never forwarded.
    - PARM additionally disables forwarding for an EXCLUSIVE read.  We do not,
      which makes this machine weaker (more behaviours) — the sound direction
      for adequacy; and since every exclusive read the kernel issues carries
      [.aq], the arm above already covers it. *)
Definition fwd_view (ws : wstate) (aq : bool) (a : Z) (t : nat) : nat :=
  if aq then t
  else match w_fwd ws !! a with
       | Some (tf, vf) => if bool_decide (t = tf) then vf else t
       | None => t
       end.

Lemma fwd_view_aq ws a t : fwd_view ws true a t = t.
Proof. done. Qed.

Lemma fwd_view_miss ws aq a t : w_fwd ws !! a = None → fwd_view ws aq a t = t.
Proof. rewrite /fwd_view. destruct aq; [done|]. by move=> ->. Qed.

Lemma fwd_view_empty ws aq a t : w_fwd ws = ∅ → fwd_view ws aq a t = t.
Proof. intros H. apply fwd_view_miss. rewrite H lookup_empty //. Qed.

Lemma fwd_view_hit ws a t tf vf :
  w_fwd ws !! a = Some (tf, vf) → t = tf → fwd_view ws false a t = vf.
Proof.
  intros Hf ->. rewrite /fwd_view Hf. case_bool_decide; [done|congruence].
Qed.

(** The post-view update at an explicitly supplied pre-view (so that a
    multi-byte load computes [vpre] ONCE, from the pre-load state).

    [vpost] is the FORWARDED view; the COHERENCE floor still takes the raw
    timestamp [t] (PARM updates [coh] with the timestamp, not the read view —
    forwarding weakens ordering, never coherence).  That split is what keeps
    every [coh] fact of the spike literally true while the vrOld/vrNew floors
    become forwarding-sensitive. *)
Definition load_post_at (ws : wstate) (aq : bool) (vpre : nat) (a : Z) (t : nat)
    : wstate :=
  let vpost := Nat.max vpre (fwd_view ws aq a t) in
  {| w_coh   := <[a := Nat.max (coh ws a) (Nat.max vpost t)]> (w_coh ws);
     w_vrOld := Nat.max (w_vrOld ws) vpost;
     w_vwOld := w_vwOld ws;
     w_vrNew := if aq then Nat.max (w_vrNew ws) vpost else w_vrNew ws;
     w_vwNew := if aq then Nat.max (w_vwNew ws) vpost else w_vwNew ws;
     w_vRel  := w_vRel ws;
     w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;
     w_relp  := w_relp ws |}.

Definition load_post (ws : wstate) (aq : bool) (a : Z) (t : nat) : wstate :=
  load_post_at ws aq (load_vpre ws aq) a t.

(** Stores.  Promise-free: the timestamp is always the log's fresh top, so the
    store rule has no admissibility condition to check. *)
(** [w_pub]/[w_relp] (M6, inert): a store taken with the release-pending flag
    set — or an [.rl] store — PUBLISHES, raising the watermark to its own
    timestamp; the flag is cleared either way.

    IDEMPOTENCE NOTE.  [store_post_bytes] folds [store_post] per byte at the
    SAME timestamp [t], so the FIRST byte performs the raise and clears
    [w_relp]; every later byte sees [w_relp = false] and (unless [rl]) leaves
    [w_pub] alone.  With [rl] the later bytes redo [Nat.max _ t], which is
    idempotent.  Net effect over a whole access: exactly one raise to [t] iff
    the access publishes — which is what [published p := S p ≤ w_pub] needs. *)
Definition store_post (ws : wstate) (rl : bool) (a : Z) (t : nat) : wstate :=
  {| w_coh   := <[a := Nat.max (coh ws a) t]> (w_coh ws);
     w_vrOld := w_vrOld ws;
     w_vwOld := Nat.max (w_vwOld ws) t;
     w_vrNew := w_vrNew ws;
     w_vwNew := w_vwNew ws;
     w_vRel  := if rl then Nat.max (w_vRel ws) t else w_vRel ws;
     (* THE FORWARD BANK.  The recorded view is PARM's [FwdItem] view, i.e.
        the store's ADDRESS/DATA dependency views [V(asrc) ⊔ V(dsrc)] (RVWMO
        ppo 12); today's machine has no register views, so that is [0].  D2
        (the dependency track) replaces the [0] by [V(asrc) ⊔ V(dsrc)].
        It is deliberately NOT [w_vwNew ws] (the store's fence floor): that
        was the M1 choice and it is LARGER than PARM's, i.e. it REMOVES
        hardware behaviours (design doc deps §2.3′ D-7, fixed 2026-08-17). *)
     w_fwd   := <[a := (t, 0%nat)]> (w_fwd ws);
     w_pub   := if (w_relp ws || rl)%bool then Nat.max (w_pub ws) t
                else w_pub ws;
     w_relp  := false |}.

(** FENCE pred,succ.  [pr]/[pw] are R/W ∈ pred; [sr]/[sw] are R/W ∈ succ.
    [fence.tso] = [fence r,r ; fence rw,w]. *)
Definition fence_post (ws : wstate) (pr pw sr sw : bool) : wstate :=
  let v1 := Nat.max (if pr then w_vrOld ws else 0%nat)
                    (if pw then w_vwOld ws else 0%nat) in
  {| w_coh   := w_coh ws;
     w_vrOld := w_vrOld ws;
     w_vwOld := w_vwOld ws;
     w_vrNew := if sr then Nat.max (w_vrNew ws) v1 else w_vrNew ws;
     w_vwNew := if sw then Nat.max (w_vwNew ws) v1 else w_vwNew ws;
     w_vRel  := w_vRel ws;
     w_fwd   := w_fwd ws;
     w_pub   := w_pub ws;
     (* M6, inert: a [pw ∧ sw] fence ([fence rw,w]) ARMS the next store as the
        publication of everything it covers. *)
     w_relp  := if (pw && sw)%bool then true else w_relp ws |}.

(** Multi-byte accesses are per-byte folds.  [vpre] is computed once from the
    PRE-load state, which is why [load_post_at] takes it explicitly: folding
    [load_post] itself would let an acquire load's own [vrNew] update raise the
    pre-view of its later bytes. *)
Definition load_post_bytes (ws : wstate) (aq : bool) (ats : list (Z * nat))
    : wstate :=
  foldl (λ w at_, load_post_at w aq (load_vpre ws aq) at_.1 at_.2) ws ats.

Definition store_post_bytes (ws : wstate) (rl : bool) (as_ : list Z) (t : nat)
    : wstate :=
  foldl (λ w a, store_post w rl a t) ws as_.

(** The CONTIGUOUS instances the interpreter uses: byte [j] of an access whose
    base byte address is [base] lives at [base + j] (see [WeakInterp.acc_addr]
    for why the seam is spelled additively rather than through the model's own
    [pa_add]). *)
Definition load_post_run (ws : wstate) (aq : bool) (base : Z) (ts : list nat)
    : wstate :=
  load_post_bytes ws aq
    (zip_with (λ j t, (base + Z.of_nat j, t)) (seq 0 (length ts)) ts).

Definition store_post_run (ws : wstate) (rl : bool) (base : Z) (n : nat)
    (t : nat) : wstate :=
  store_post_bytes ws rl (map (λ j : nat, base + Z.of_nat j) (seq 0 n)) t.

(* ------------------------------------------------------------------ *)
(** ** Monotonicity: every step function only raises views *)

(** NOTE [w_relp] is NOT ordered: it TOGGLES (set by a fence, cleared by the
    next store), so there is no conjunct for it.  [w_pub] only ever grows. *)
Definition ws_le (w1 w2 : wstate) : Prop :=
  (∀ a, (coh w1 a ≤ coh w2 a)%nat) ∧
  (w_vrOld w1 ≤ w_vrOld w2)%nat ∧ (w_vwOld w1 ≤ w_vwOld w2)%nat ∧
  (w_vrNew w1 ≤ w_vrNew w2)%nat ∧ (w_vwNew w1 ≤ w_vwNew w2)%nat ∧
  (w_vRel  w1 ≤ w_vRel  w2)%nat ∧ (w_pub w1 ≤ w_pub w2)%nat.

Global Instance ws_le_refl : Reflexive ws_le.
Proof. intros w. rewrite /ws_le. split_and!; auto with lia. Qed.

Global Instance ws_le_trans : Transitive ws_le.
Proof.
  intros w1 w2 w3 (?&?&?&?&?&?&?) (?&?&?&?&?&?&?).
  rewrite /ws_le; split_and!; try lia. intros a. etrans; eauto.
Qed.

(** The projections.  (Lifted from [WeakAxiomatic]/[WeakRobustAcyc], which
    proved them locally while this file was frozen.) *)
Lemma ws_le_coh w1 w2 a : ws_le w1 w2 → (coh w1 a ≤ coh w2 a)%nat.
Proof. by intros (H & _). Qed.

Lemma ws_le_vrOld w1 w2 : ws_le w1 w2 → (w_vrOld w1 ≤ w_vrOld w2)%nat.
Proof. by intros (_ & ? & _). Qed.

Lemma ws_le_vwOld w1 w2 : ws_le w1 w2 → (w_vwOld w1 ≤ w_vwOld w2)%nat.
Proof. by intros (_ & _ & ? & _). Qed.

Lemma ws_le_vrNew w1 w2 : ws_le w1 w2 → (w_vrNew w1 ≤ w_vrNew w2)%nat.
Proof. by intros (_ & _ & _ & ? & _). Qed.

Lemma ws_le_vwNew w1 w2 : ws_le w1 w2 → (w_vwNew w1 ≤ w_vwNew w2)%nat.
Proof. by intros (_ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_vRel w1 w2 : ws_le w1 w2 → (w_vRel w1 ≤ w_vRel w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & ? & _). Qed.

Lemma ws_le_pub w1 w2 : ws_le w1 w2 → (w_pub w1 ≤ w_pub w2)%nat.
Proof. by intros (_ & _ & _ & _ & _ & _ & ?). Qed.

Lemma load_post_at_le ws aq vpre a t : ws_le ws (load_post_at ws aq vpre a t).
Proof.
  rewrite /ws_le /load_post_at /=. split_and!; try (destruct aq; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. lia.
  - rewrite coh_upd_ne //.
Qed.

Lemma load_post_le ws aq a t : ws_le ws (load_post ws aq a t).
Proof. apply load_post_at_le. Qed.

Lemma store_post_le ws rl a t : ws_le ws (store_post ws rl a t).
Proof.
  rewrite /ws_le /store_post /=.
  split_and!; try (destruct rl, (w_relp ws); simpl; lia).
  intros a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. lia.
  - rewrite coh_upd_ne //.
Qed.

Lemma fence_post_le ws pr pw sr sw : ws_le ws (fence_post ws pr pw sr sw).
Proof.
  rewrite /ws_le /fence_post /=.
  split_and!; try (destruct sr; destruct sw; lia).
  intros a. apply Nat.le_refl.
Qed.

(** ... and so do the multi-byte folds, which is what the interpreter's
    read/write arms actually build ([WeakInterp.wrun_ws_le]). *)
Lemma load_post_fold_le aq vpre ats ws :
  ws_le ws (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats).
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws; [reflexivity|].
  etrans; [apply load_post_at_le|apply IH].
Qed.

Lemma load_post_bytes_le ws aq ats : ws_le ws (load_post_bytes ws aq ats).
Proof. apply load_post_fold_le. Qed.

Lemma load_post_run_le ws aq base ts : ws_le ws (load_post_run ws aq base ts).
Proof. apply load_post_bytes_le. Qed.

Lemma store_post_fold_le rl t as_ ws :
  ws_le ws (foldl (λ w a, store_post w rl a t) ws as_).
Proof.
  revert ws. induction as_ as [|a l IH]; intros ws; [reflexivity|].
  etrans; [apply store_post_le|apply IH].
Qed.

Lemma store_post_bytes_le ws rl as_ t : ws_le ws (store_post_bytes ws rl as_ t).
Proof. apply store_post_fold_le. Qed.

Lemma store_post_run_le ws rl base n t : ws_le ws (store_post_run ws rl base n t).
Proof. apply store_post_bytes_le. Qed.

(* ------------------------------------------------------------------ *)
(** ** The individual view facts the litmus proofs consume *)

Lemma load_vpre_vrNew ws aq : (w_vrNew ws ≤ load_vpre ws aq)%nat.
Proof. rewrite /load_vpre. lia. Qed.

(** The read floor is the FORWARDED view, not the timestamp: a load that reads
    back the agent's own store gains only the view that store banked.  The
    [_nofwd] corollaries are what a consumer with an empty forward bank (any
    agent that has not stored to [a]) uses, and are the M0 statements. *)
Lemma load_post_at_vrOld ws aq vpre a t :
  (fwd_view ws aq a t ≤ w_vrOld (load_post_at ws aq vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma load_post_vrOld ws aq a t :
  (fwd_view ws aq a t ≤ w_vrOld (load_post ws aq a t))%nat.
Proof. apply load_post_at_vrOld. Qed.

Lemma load_post_at_vrOld_nofwd ws aq vpre a t :
  w_fwd ws = ∅ → (t ≤ w_vrOld (load_post_at ws aq vpre a t))%nat.
Proof.
  intros H. rewrite -{1}(fwd_view_empty ws aq a t H). apply load_post_at_vrOld.
Qed.

Lemma load_post_vrOld_nofwd ws aq a t :
  w_fwd ws = ∅ → (t ≤ w_vrOld (load_post ws aq a t))%nat.
Proof. apply load_post_at_vrOld_nofwd. Qed.

(** No step function ever CHANGES the bank except [store_post], which is what
    lets "this agent has never stored to [a]" be an invariant. *)
Lemma load_post_at_fwd ws aq vpre a t :
  w_fwd (load_post_at ws aq vpre a t) = w_fwd ws.
Proof. done. Qed.

Lemma load_post_fwd ws aq a t : w_fwd (load_post ws aq a t) = w_fwd ws.
Proof. done. Qed.

Lemma fence_post_fwd ws pr pw sr sw :
  w_fwd (fence_post ws pr pw sr sw) = w_fwd ws.
Proof. done. Qed.

Lemma load_post_fold_fwd aq vpre ats ws :
  w_fwd (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) = w_fwd ws.
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws; [done|].
  by rewrite /= IH load_post_at_fwd.
Qed.

Lemma load_post_bytes_fwd ws aq ats :
  w_fwd (load_post_bytes ws aq ats) = w_fwd ws.
Proof. apply load_post_fold_fwd. Qed.

Lemma load_post_run_fwd ws aq base ts :
  w_fwd (load_post_run ws aq base ts) = w_fwd ws.
Proof. apply load_post_bytes_fwd. Qed.

(** THE MULTI-BYTE READ GAIN.  [load_post_vrOld_nofwd] says a single
    non-forwarded byte read of timestamp [t] leaves [t ≤ w_vrOld]; this is the
    same fact for the FOLD the interpreter actually builds
    ([WeakInterp.wread_post]), and it is what turns "the load returned byte
    [b]" into "the timestamp [b] came from is covered by my read floor" — the
    reader half of every fence-mediated handoff.

    The side condition is per-BYTE ([w_fwd ws !! a = None], "this hart has not
    stored to that byte"), not the global [w_fwd ws = ∅] the M0 corollary
    used: a hart that has stored elsewhere still reads a foreign flag
    unforwarded. *)
Lemma load_post_fold_vrOld aq vpre ats ws a t :
  (a, t) ∈ ats → w_fwd ws !! a = None →
  (t ≤ w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|at_ l IH]; intros ws Hin Hfwd.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin].
  - (* the head IS our byte: the step raises [w_vrOld] past [t], the rest of
       the fold only raises it further *)
    simpl.
    etrans; [|apply (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t))].
    rewrite /load_post_at /= (fwd_view_miss ws aq a t Hfwd). lia.
  - apply IH; [exact Hin|]. by rewrite load_post_at_fwd.
Qed.

Lemma load_post_bytes_vrOld ws aq ats a t :
  (a, t) ∈ ats → w_fwd ws !! a = None →
  (t ≤ w_vrOld (load_post_bytes ws aq ats))%nat.
Proof. apply load_post_fold_vrOld. Qed.

Lemma load_post_run_vrOld ws aq base ts j :
  (j < length ts)%nat → w_fwd ws !! (base + Z.of_nat j)%Z = None →
  (ts !!! j ≤ w_vrOld (load_post_run ws aq base ts))%nat.
Proof.
  intros Hj Hfwd. apply (load_post_bytes_vrOld _ _ _ (base + Z.of_nat j)%Z);
    [|exact Hfwd].
  apply elem_of_list_lookup_2 with j.
  destruct (lookup_lt_is_Some_2 ts j Hj) as [t Ht].
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht /=.
  by rewrite (list_lookup_total_correct ts j t Ht).
Qed.

Lemma load_post_at_coh ws aq vpre a t :
  (t ≤ coh (load_post_at ws aq vpre a t) a)%nat.
Proof. rewrite /load_post_at coh_upd_eq. lia. Qed.

Lemma load_post_coh ws aq a t : (t ≤ coh (load_post ws aq a t) a)%nat.
Proof. apply load_post_at_coh. Qed.

(** An ACQUIRE load raises the read AND write pre-view floors — this is what
    makes [MP+amoswap.aq]-style reader-side ordering work with no fence. *)
Lemma load_post_at_vrNew_aq ws vpre a t :
  (t ≤ w_vrNew (load_post_at ws true vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma load_post_vrNew_aq ws a t : (t ≤ w_vrNew (load_post ws true a t))%nat.
Proof. apply load_post_at_vrNew_aq. Qed.

Lemma load_post_at_vwNew_aq ws vpre a t :
  (t ≤ w_vwNew (load_post_at ws true vpre a t))%nat.
Proof. rewrite /load_post_at /=. lia. Qed.

Lemma store_post_coh ws rl a t : (t ≤ coh (store_post ws rl a t) a)%nat.
Proof. rewrite /store_post coh_upd_eq. lia. Qed.

Lemma store_post_vwOld ws rl a t : (t ≤ w_vwOld (store_post ws rl a t))%nat.
Proof. rewrite /store_post /=. lia. Qed.

Lemma store_post_vRel_rl ws a t : (t ≤ w_vRel (store_post ws true a t))%nat.
Proof. rewrite /store_post /=. lia. Qed.

(** A succ-R fence with pred-R delivers the past loads' floor to future loads.
    (The pred-W half is the one that constrains nothing in a promise-free
    machine — see the design doc's FENCE note.) *)
Lemma fence_post_vrNew_r ws pw sw :
  (w_vrOld ws ≤ w_vrNew (fence_post ws true pw true sw))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vrNew_w ws pr sw :
  (w_vwOld ws ≤ w_vrNew (fence_post ws pr true true sw))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vwNew_r ws pw sr :
  (w_vrOld ws ≤ w_vwNew (fence_post ws true pw sr true))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

Lemma fence_post_vwNew_w ws pr sr :
  (w_vwOld ws ≤ w_vwNew (fence_post ws pr true sr true))%nat.
Proof. rewrite /fence_post /=. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Own-write read-back *)

(** THE COLLAPSE LEMMA — the pure heart of the M2 load rule.  If [t] is the
    LATEST write to [a] and the reader's FLOOR (its load pre-view joined with
    its coherence floor for [a]) already covers [t], then [t] is the ONLY
    admissible timestamp: the ∀-over-oracles quantifier of a weak read
    collapses to a single value.

    The floor premise is deliberately stated at [Nat.max vpre (coh ws a)] —
    exactly [readable]'s own window — because the floor the vProp layer owns
    is the hart's index [w_vrNew ⊔ coh(a)], not [coh(a)] alone. *)
Lemma readable_latest_pin img log ws vpre a t t' :
  latest img log a t →
  (t ≤ Nat.max vpre (coh ws a))%nat →
  readable img log ws vpre a t' →
  t' = t.
Proof.
  intros [Ht Htop] Hfloor [Ht' Hn'].
  destruct (decide (t' = t)) as [->|Hne]; [done|exfalso].
  destruct (decide (t' < t)%nat) as [Hlt|Hge].
  - (* [t] itself is a write in [t']'s forbidden window *)
    apply Hn'. eapply (writes_in_log_byte img). exists t.
    split_and!; [lia|lia|done].
  - (* [t'] is a write strictly above [t], contradicting latest-ness *)
    apply Htop. eapply (writes_in_log_byte img). exists t'.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht').
Qed.

(** If [t] writes [a], the agent's coherence floor already covers [t], and no
    LATER timestamp in the whole log writes [a], then [t] is the ONLY readable
    timestamp for [a] — the reader is pinned to the top message.  The
    [vpre = 0] instance of [readable_latest_pin]. *)
Lemma readable_top_unique img log ws vpre a t t' :
  is_Some (log_byte img log t a) →
  (t ≤ coh ws a)%nat →
  ¬ writes_in log a t (length log) →
  readable img log ws vpre a t' →
  t' = t.
Proof.
  intros Ht Hcoh Htop Hr.
  eapply readable_latest_pin; [split; [exact Ht|exact Htop]| |exact Hr]. lia.
Qed.

(** The store case: right after a store, the storer can only read back its own
    message.  The store lands at the log's fresh top [S (length log)], and
    [store_post] pushes [coh(a)] up to it. *)
Lemma store_fresh_top_unique img log ws rl m a vpre t' :
  is_Some (msg_byte m a) →
  readable img (log ++ [m]) (store_post ws rl a (S (length log)))
           vpre a t' →
  t' = S (length log).
Proof.
  intros Hm Hr.
  eapply (readable_top_unique img (log ++ [m])); [| | |exact Hr].
  - assert (Hle : (length log ≤ length log)%nat) by lia.
    rewrite log_byte_S (lookup_app_r log [m] (length log) Hle) Nat.sub_diag /=.
    exact Hm.
  - apply store_post_coh.
  - rewrite length_app /=. intros (t & ? & ? & ?). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [ws_bounded]: every view a hart holds is a real timestamp

    THE MACHINE INVARIANT of M2b.  A [wstate] is a bundle of timestamps; the
    step functions only ever join them with timestamps drawn from the log, so
    every view a hart holds stays below the log's length.  Stated over a NAT
    bound rather than a log: the bound is then monotone ([ws_bounded_mono]),
    which is exactly what the OTHER harts need when the stepping hart appends.
    THE TIE IS ALWAYS USED AT [n = length log] — see
    [WeakInterp.wrun_ws_bounded] and [WeakGhost.weak_state_interp].

    THE FORWARD-BANK CONJUNCT IS NOT OPTIONAL.  [fwd_view] puts a BANKED view
    into a load's post-view ([load_post_at]'s [vpost]), so without a bound on
    the bank's second components [load_post_at] would not preserve
    boundedness — the banked view would flow straight into [w_vrOld]. *)

Definition ws_bounded (ws : wstate) (n : nat) : Prop :=
  (w_vrOld ws ≤ n)%nat ∧ (w_vwOld ws ≤ n)%nat ∧
  (w_vrNew ws ≤ n)%nat ∧ (w_vwNew ws ≤ n)%nat ∧ (w_vRel ws ≤ n)%nat ∧
  (w_pub ws ≤ n)%nat ∧
  (∀ a, (coh ws a ≤ n)%nat) ∧
  (∀ a tv, w_fwd ws !! a = Some tv → (tv.1 ≤ n)%nat ∧ (tv.2 ≤ n)%nat).

Lemma ws_bounded_init n : ws_bounded ws_init n.
Proof.
  rewrite /ws_bounded. split_and!; try (simpl; lia).
  - intros a. rewrite coh_init. lia.
  - intros a tv. rewrite /ws_init /= lookup_empty. done.
Qed.

Lemma ws_bounded_mono ws n n' :
  ws_bounded ws n → (n ≤ n')%nat → ws_bounded ws n'.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd) Hle.
  rewrite /ws_bounded. split_and!; try lia.
  - intros a. pose proof (Hcoh a). lia.
  - intros a tv Ha. destruct (Hfwd a tv Ha). split; lia.
Qed.

(** The [coh] half of every preservation proof below: an insert stays bounded
    if the inserted value is. *)
Local Lemma coh_upd_bounded ws vrO vwO vrN vwN vR fwd pb rp a v n :
  (∀ a', (coh ws a' ≤ n)%nat) → (v ≤ n)%nat →
  ∀ a', (coh {| w_coh := <[a := v]> (w_coh ws); w_vrOld := vrO; w_vwOld := vwO;
                w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd;
                w_pub := pb; w_relp := rp |} a'
         ≤ n)%nat.
Proof.
  intros Hm Hv a'. destruct (decide (a' = a)) as [->|Hne].
  - rewrite coh_upd_eq. exact Hv.
  - rewrite coh_upd_ne //. apply Hm.
Qed.

Lemma load_vpre_bounded ws aq n : ws_bounded ws n → (load_vpre ws aq ≤ n)%nat.
Proof.
  intros (_ & _ & Hrn & _ & Hrel & _ & _ & _).
  rewrite /load_vpre. destruct aq; lia.
Qed.

Lemma fwd_view_bounded ws aq a t n :
  ws_bounded ws n → (t ≤ n)%nat → (fwd_view ws aq a t ≤ n)%nat.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hfwd) Ht. rewrite /fwd_view.
  destruct aq; [exact Ht|].
  destruct (w_fwd ws !! a) as [[tf vf]|] eqn:Hf; [|exact Ht].
  case_bool_decide; [|exact Ht].
  destruct (Hfwd a (tf, vf) Hf) as [_ Hvf]. exact Hvf.
Qed.

Lemma load_post_at_bounded ws aq vpre a t n :
  ws_bounded ws n → (vpre ≤ n)%nat → (t ≤ n)%nat →
  ws_bounded (load_post_at ws aq vpre a t) n.
Proof.
  intros Hb Hvp Ht.
  pose proof (fwd_view_bounded ws aq a t n Hb Ht) as Hfv.
  destruct Hb as (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd).
  rewrite /ws_bounded /load_post_at /=.
  split_and!; try (destruct aq; lia).
  - apply coh_upd_bounded; [exact Hcoh|]. pose proof (Hcoh a). lia.
  - exact Hfwd.
Qed.

Lemma store_post_bounded ws rl a t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post ws rl a t) n'.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd) Ht Hle.
  rewrite /ws_bounded /store_post /=.
  split_and!; try (destruct rl, (w_relp ws); simpl; lia).
  - apply coh_upd_bounded.
    + intros a'. pose proof (Hcoh a'). lia.
    + pose proof (Hcoh a). lia.
  - intros a' tv. destruct (decide (a' = a)) as [->|Hne].
    + rewrite lookup_insert. intros [= <-]. simpl. split; lia.
    + rewrite lookup_insert_ne //. intros Ha'.
      destruct (Hfwd a' tv Ha'). split; lia.
Qed.

Lemma fence_post_bounded ws pr pw sr sw n :
  ws_bounded ws n → ws_bounded (fence_post ws pr pw sr sw) n.
Proof.
  intros (Hro & Hwo & Hrn & Hwn & Hrel & Hpub & Hcoh & Hfwd).
  rewrite /ws_bounded /fence_post /=.
  split_and!; try (destruct pr, pw, sr, sw; simpl; lia).
  - exact Hcoh.
  - exact Hfwd.
Qed.

(** ... and the multi-byte folds the interpreter's read/write arms build. *)

Local Lemma load_post_fold_bounded aq vpre n ats :
  (vpre ≤ n)%nat →
  ∀ ws, ws_bounded ws n → Forall (λ p : Z * nat, (p.2 ≤ n)%nat) ats →
    ws_bounded (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) n.
Proof.
  intros Hvp. induction ats as [|at_ l IH]; intros ws Hb Hall; [exact Hb|].
  apply Forall_cons_1 in Hall as [Hat Hl].
  simpl. apply IH; [|exact Hl]. by apply load_post_at_bounded.
Qed.

(** NOTE the pre-view: [load_post_bytes] folds [load_post_at] with the
    pre-view computed ONCE from [ws], so the bound needed on it is exactly
    [load_vpre_bounded] and there is no [vpre] premise to state. *)
Lemma load_post_bytes_bounded ws aq ats n :
  ws_bounded ws n → Forall (λ p : Z * nat, (p.2 ≤ n)%nat) ats →
  ws_bounded (load_post_bytes ws aq ats) n.
Proof.
  intros Hb Hall. rewrite /load_post_bytes.
  apply load_post_fold_bounded; [by apply load_vpre_bounded|exact Hb|exact Hall].
Qed.

Local Lemma store_post_fold_bounded rl t n' as_ :
  (t ≤ n')%nat →
  ∀ ws, ws_bounded ws n' →
    ws_bounded (foldl (λ w a, store_post w rl a t) ws as_) n'.
Proof.
  intros Ht. induction as_ as [|a l IH]; intros ws Hb; [exact Hb|].
  simpl. apply IH. by apply (store_post_bounded ws rl a t n' n').
Qed.

Lemma store_post_bytes_bounded ws rl as_ t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post_bytes ws rl as_ t) n'.
Proof.
  intros Hb Ht Hle. rewrite /store_post_bytes.
  apply store_post_fold_bounded; [exact Ht|].
  eapply ws_bounded_mono; [exact Hb|exact Hle].
Qed.

(** The contiguous-run transport: byte [j] of the access sits at
    [base + j], and only the SECOND component of the zipped pair carries a
    timestamp. *)
Local Lemma Forall_zip_seq (base : Z) (n : nat) (ts : list nat) :
  Forall (λ t, (t ≤ n)%nat) ts →
  ∀ k, Forall (λ p : Z * nat, (p.2 ≤ n)%nat)
         (zip_with (λ j t, (base + Z.of_nat j, t)) (seq k (length ts)) ts).
Proof.
  induction ts as [|t l IH]; intros Hall k; [constructor|].
  apply Forall_cons_1 in Hall as [Ht Hl].
  (* [seq k (S m) = k :: seq (S k) m] holds by [reflexivity] *)
  simpl. constructor; [exact Ht|]. by apply IH.
Qed.

Lemma load_post_run_bounded ws aq base ts n :
  ws_bounded ws n → Forall (λ t, (t ≤ n)%nat) ts →
  ws_bounded (load_post_run ws aq base ts) n.
Proof.
  intros Hb Hall. rewrite /load_post_run.
  apply load_post_bytes_bounded; [exact Hb|by apply Forall_zip_seq].
Qed.

Lemma store_post_run_bounded ws rl base cnt t n n' :
  ws_bounded ws n → (t ≤ n')%nat → (n ≤ n')%nat →
  ws_bounded (store_post_run ws rl base cnt t) n'.
Proof.
  intros Hb Ht Hle. rewrite /store_post_run.
  by apply (store_post_bytes_bounded ws rl _ t n n').
Qed.

(** THE PAYOFF.  The hart's own index into the log — its read floor joined
    with a byte's coherence floor, i.e. exactly [readable]'s window — is a
    real timestamp.  This is what M3's lock transfer consumes; the view-level
    restatement lives above [WeakView], not here. *)
Lemma ws_bounded_scl ws n :
  ws_bounded ws n → ∀ a, (Nat.max (w_vrNew ws) (coh ws a) ≤ n)%nat.
Proof.
  intros (_ & _ & Hrn & _ & _ & _ & Hcoh & _) a. pose proof (Hcoh a). lia.
Qed.

(* ================================================================== *)
(** ** THE W4 LIFT BATCH — fold facts the consumers used to prove locally

    Every lemma below was proved verbatim in a consumer file
    ([WeakAxiomatic], [WeakAxiomatic2], [WeakAxiomatic3], [WeakLitmusProj],
    [WeakPromiseLitmus], [WeakPromiseBridge], [WeakRobustAcyc],
    [WeakRobustGraph]) with a header explaining that it belonged here and was
    only elsewhere because this file was frozen while sibling [.vo]s were in
    flight.  They are now here, and the local copies are gone.

    Three kinds of fact about the step functions live in this file:
    MONOTONE ([ws_le]), BOUNDED ([ws_bounded]), and — the third kind, added by
    this batch — DOMINATED (an upper bound on each component in terms of the
    step's inputs, §5 of [WeakAxiomatic3]). *)

(* ------------------------------------------------------------------ *)
(** *** Singleton collapses of the run-shaped post-states

    The byte address [base + Z.of_nat 0] normalizes to [base].  The store form
    is stated at [length [v]] rather than at [1] so that it matches the
    step relations' post-states syntactically. *)

Lemma load_post_run_single ws aq base t :
  load_post_run ws aq base [t] = load_post ws aq base t.
Proof. rewrite /load_post_run /load_post_bytes /load_post /= Z.add_0_r //. Qed.

Lemma store_post_run_single ws rl base (v : bv 8) t :
  store_post_run ws rl base (length [v]) t = store_post ws rl base t.
Proof. rewrite /store_post_run /store_post_bytes /= Z.add_0_r //. Qed.

(* ------------------------------------------------------------------ *)
(** *** A message writes only inside its own byte range *)

Lemma msg_byte_range m a :
  is_Some (msg_byte m a) →
  ∃ j : nat, (j < length (wm_data m))%nat ∧ a = wm_pa m + Z.of_nat j.
Proof.
  rewrite /msg_byte. case_bool_decide as Hle; [|by intros []].
  intros Hs. exists (Z.to_nat (a - wm_pa m)). split.
  - by eapply lookup_lt_is_Some_1.
  - lia.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The missing [coh] / [w_vwOld] / forwarded-[w_vrOld] fold instances *)

Local Lemma load_post_fold_coh aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ coh (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) a)%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_coh ws aq vpre a t)|].
  apply ws_le_coh, (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t)).
Qed.

Lemma load_post_run_coh ws aq base ts (j : nat) t :
  ts !! j = Some t →
  (t ≤ coh (load_post_run ws aq base ts) (base + Z.of_nat j))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes. apply load_post_fold_coh.
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Local Lemma store_post_fold_coh rl t as_ ws a :
  a ∈ as_ → (t ≤ coh (foldl (λ w a, store_post w rl a t) ws as_) a)%nat.
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (store_post_coh ws rl a t)|].
  apply ws_le_coh, (store_post_fold_le rl t l (store_post ws rl a t)).
Qed.

Lemma store_post_run_coh ws rl base n t (j : nat) :
  (j < n)%nat → (t ≤ coh (store_post_run ws rl base n t) (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite /store_post_run /store_post_bytes.
  apply store_post_fold_coh, elem_of_list_In, in_map_iff.
  exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

Local Lemma store_post_fold_vwOld rl t as_ ws :
  as_ ≠ [] → (t ≤ w_vwOld (foldl (λ w a, store_post w rl a t) ws as_))%nat.
Proof.
  destruct as_ as [|a l]; [done|]. intros _. simpl.
  etrans; [apply (store_post_vwOld ws rl a t)|].
  apply ws_le_vwOld, (store_post_fold_le rl t l (store_post ws rl a t)).
Qed.

Lemma store_post_run_vwOld ws rl base n t :
  (0 < n)%nat → (t ≤ w_vwOld (store_post_run ws rl base n t))%nat.
Proof.
  intros Hn. rewrite /store_post_run /store_post_bytes.
  apply store_post_fold_vwOld. by destruct n; [lia|].
Qed.

(** The generalized [load_post_run_vrOld]: what the read floor gains is the
    FORWARDED view, so the side condition needed is "this byte's read was not
    forwarded", not the stronger "this agent never stored to it". *)
Local Lemma load_post_fold_vrOld' aq vpre ats ws a t :
  (a, t) ∈ ats → fwd_view ws aq a t = t →
  (t ≤ w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin Hfv.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin].
  - simpl. etrans; [|apply ws_le_vrOld,
      (load_post_fold_le aq vpre l (load_post_at ws aq vpre a t))].
    rewrite /load_post_at /= Hfv. lia.
  - apply IH; [exact Hin|]. by rewrite /fwd_view load_post_at_fwd.
Qed.

Lemma load_post_run_vrOld' ws aq base ts (j : nat) t :
  ts !! j = Some t → fwd_view ws aq (base + Z.of_nat j) t = t →
  (t ≤ w_vrOld (load_post_run ws aq base ts))%nat.
Proof.
  intros Ht Hfv. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vrOld' _ _ _ _ (base + Z.of_nat j) t); [|exact Hfv].
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The acquire-load fold instances

    An acquire load pushes every byte's timestamp — and its own pre-view —
    into both [w_vrNew] and [w_vwNew]. *)

Local Lemma load_post_fold_vrNew_aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ w_vrNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_vrNew_aq ws vpre a t)|].
  apply ws_le_vrNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre a t)).
Qed.

Lemma load_post_run_vrNew_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vrNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vrNew_aq _ _ _ (base + Z.of_nat j) t).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

Local Lemma load_post_fold_vwNew_aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ w_vwNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_vwNew_aq ws vpre a t)|].
  apply ws_le_vwNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre a t)).
Qed.

Lemma load_post_run_vwNew_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vwNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vwNew_aq _ _ _ (base + Z.of_nat j) t).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(** An ACQUIRE load's own PRE-VIEW lands under its post-[w_vrNew] — needed
    because [load_vpre] of an acquire joins [w_vRel], which is NOT below
    [w_vrNew] before the step. *)
Local Lemma load_post_fold_vrNew_aq_vpre vpre ats ws p :
  p ∈ ats →
  (vpre ≤ w_vrNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|q l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [|apply ws_le_vrNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre p.1 p.2))].
  rewrite /load_post_at /=. lia.
Qed.

Lemma load_post_run_vrNew_aq_vpre ws base ts (j : nat) t :
  ts !! j = Some t →
  (load_vpre ws true ≤ w_vrNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vrNew_aq_vpre _ _ _ (base + Z.of_nat j, t)).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The forward-bank inversion for a store fold *)

Local Lemma store_post_fold_fwd rl t as_ ws a tf vf :
  w_fwd (foldl (λ w a, store_post w rl a t) ws as_) !! a = Some (tf, vf) →
  tf = t ∨ w_fwd ws !! a = Some (tf, vf).
Proof.
  revert ws. induction as_ as [|b l IH]; intros ws Hlk; [by right|].
  destruct (IH _ Hlk) as [->|Hlk']; [by left|].
  rewrite /store_post /= in Hlk'.
  destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert in Hlk'. simplify_eq. by left.
  - rewrite lookup_insert_ne in Hlk'; [done|]. by right.
Qed.

Lemma store_post_run_fwd_inv ws rl base n t a tf vf :
  w_fwd (store_post_run ws rl base n t) !! a = Some (tf, vf) →
  tf = t ∨ w_fwd ws !! a = Some (tf, vf).
Proof. rewrite /store_post_run /store_post_bytes. apply store_post_fold_fwd. Qed.

(* ================================================================== *)
(** ** DOMINATION: upper bounds for the step functions

    The THIRD kind of step-function fact (§5 of [WeakAxiomatic3]): after this
    step, each component is a join of the old component, the pre-view, and the
    timestamps the step touched.  Stated once for an arbitrary predicate
    closed under [Nat.max] and holding at 0, because the consumers instantiate
    it at several different predicates. *)

Definition maxcl (P : nat → Prop) : Prop :=
  P 0%nat ∧ ∀ n1 n2, P n1 → P n2 → P (Nat.max n1 n2).

Lemma maxcl_0 P : maxcl P → P 0%nat.
Proof. by intros [? _]. Qed.
Lemma maxcl_max P n1 n2 : maxcl P → P n1 → P n2 → P (Nat.max n1 n2).
Proof. intros [_ H]. exact (H n1 n2). Qed.

(** *** Pointwise shapes of the two per-byte updates *)

Lemma coh_load_post_at_eq ws aq vpre a t :
  coh (load_post_at ws aq vpre a t) a =
  Nat.max (coh ws a) (Nat.max (Nat.max vpre (fwd_view ws aq a t)) t).
Proof. rewrite /load_post_at coh_upd_eq //. Qed.

Lemma coh_load_post_at_ne ws aq vpre a t a' :
  a' ≠ a → coh (load_post_at ws aq vpre a t) a' = coh ws a'.
Proof. intros Hne. rewrite /load_post_at coh_upd_ne // /coh //. Qed.

Lemma coh_store_post_eq ws rl a t :
  coh (store_post ws rl a t) a = Nat.max (coh ws a) t.
Proof. rewrite /store_post coh_upd_eq //. Qed.

Lemma coh_store_post_ne ws rl a t a' :
  a' ≠ a → coh (store_post ws rl a t) a' = coh ws a'.
Proof. intros Hne. rewrite /store_post coh_upd_ne // /coh //. Qed.

(** *** The load fold: the components it does not touch *)

Lemma load_fold_vwOld aq vpre ats ws :
  w_vwOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_vwOld ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma load_fold_vRel aq vpre ats ws :
  w_vRel (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)
  = w_vRel ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma load_fold_vrNew_plain vpre ats ws :
  w_vrNew (foldl (λ w at_, load_post_at w false vpre at_.1 at_.2) ws ats)
  = w_vrNew ws.
Proof. revert ws. induction ats as [|p l IH]; intros ws; [done|by rewrite /= IH]. Qed.

(** *** The load fold: upper bounds, under "no byte of this load is
    forwarded". *)

Lemma load_fold_coh P aq vpre ats ws a :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (coh ws a) → P vpre → (∀ p, p ∈ ats → p.1 = a → P p.2) →
  P (coh (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats) a).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - destruct (decide (a = p.1)) as [Heq|Hne]; last first.
    { rewrite (coh_load_post_at_ne _ _ _ _ _ _ Hne). exact Hc. }
    assert (Hpa : P p.2).
    { apply (Hts p); [apply elem_of_cons; by left|by rewrite -Heq]. }
    rewrite Heq coh_load_post_at_eq (Hfv p ltac:(apply elem_of_cons; by left)).
    apply maxcl_max; [done|rewrite -Heq; exact Hc|].
    apply maxcl_max; [done| |exact Hpa].
    apply maxcl_max; [done|exact Hv|exact Hpa].
  - exact Hv.
  - intros q Hq Hqa. apply (Hts q); [apply elem_of_cons; by right|exact Hqa].
Qed.

Lemma load_fold_vrOld P aq vpre ats ws :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (w_vrOld ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrOld (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - rewrite /load_post_at /= (Hfv p ltac:(apply elem_of_cons; by left)).
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

Lemma load_fold_vrNew P aq vpre ats ws :
  maxcl P → (∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2) →
  P (w_vrNew ws) → P vpre → (∀ p, p ∈ ats → P p.2) →
  P (w_vrNew (foldl (λ w at_, load_post_at w aq vpre at_.1 at_.2) ws ats)).
Proof.
  intros Hcl. revert ws. induction ats as [|p l IH]; intros ws Hfv Hc Hv Hts;
    [exact Hc|].
  simpl. apply IH.
  - intros q Hq. rewrite /fwd_view load_post_at_fwd -/(fwd_view ws aq q.1 q.2).
    apply Hfv, elem_of_cons; by right.
  - rewrite /load_post_at /= (Hfv p ltac:(apply elem_of_cons; by left)).
    destruct aq; [|exact Hc].
    apply maxcl_max; [done|exact Hc|].
    apply maxcl_max; [done|exact Hv|apply Hts, elem_of_cons; by left].
  - exact Hv.
  - intros q Hq. apply Hts, elem_of_cons; by right.
Qed.

(** *** The store fold *)

Lemma store_fold_vrOld rl t as_ ws :
  w_vrOld (foldl (λ w a, store_post w rl a t) ws as_) = w_vrOld ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vrNew rl t as_ ws :
  w_vrNew (foldl (λ w a, store_post w rl a t) ws as_) = w_vrNew ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vRel_norl t as_ ws :
  w_vRel (foldl (λ w a, store_post w false a t) ws as_) = w_vRel ws.
Proof. revert ws. induction as_ as [|a l IH]; intros ws; [done|by rewrite /= IH]. Qed.

Lemma store_fold_vwOld P rl t as_ ws :
  maxcl P → P (w_vwOld ws) → P t →
  P (w_vwOld (foldl (λ w a, store_post w rl a t) ws as_)).
Proof.
  intros Hcl. revert ws. induction as_ as [|a l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH; [|exact Ht]. rewrite /store_post /=. by apply maxcl_max.
Qed.

Lemma store_fold_coh P rl t as_ ws a :
  maxcl P → P (coh ws a) → (a ∈ as_ → P t) →
  P (coh (foldl (λ w a, store_post w rl a t) ws as_) a).
Proof.
  intros Hcl. revert ws. induction as_ as [|b l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH.
  - destruct (decide (a = b)) as [->|Hne]; last first.
    { rewrite (coh_store_post_ne _ _ _ _ _ Hne). exact Hc. }
    rewrite coh_store_post_eq.
    apply maxcl_max; [done|exact Hc|apply Ht, elem_of_cons; by left].
  - intros Hin. apply Ht, elem_of_cons; by right.
Qed.

(** *** The fence *)

Lemma fence_post_vrNew_pred P ws pr pw sr sw :
  maxcl P → P (w_vrNew ws) →
  (pr = true → sr = true → P (w_vrOld ws)) →
  (pw = true → sr = true → P (w_vwOld ws)) →
  P (w_vrNew (fence_post ws pr pw sr sw)).
Proof.
  intros Hcl Hn Hro Hwo. rewrite /fence_post /=.
  destruct sr; [|exact Hn].
  apply maxcl_max; [done|exact Hn|].
  apply maxcl_max; [done| |].
  - destruct pr; [by apply Hro|by apply maxcl_0].
  - destruct pw; [by apply Hwo|by apply maxcl_0].
Qed.

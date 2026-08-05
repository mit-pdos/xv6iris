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

(** One write event.  It covers the byte range [wm_pa, wm_pa + |wm_data|).
    [wm_tid = None] is reserved for the DMA/boot-era agents. *)
Record wmsg := WMsg {
  wm_pa   : Z;
  wm_data : list (bv 8);
  wm_tid  : option agent;
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
}.
Add Printing Constructor wstate.

(** Coherence lookup with default 0. *)
Definition coh (ws : wstate) (a : Z) : nat := default 0%nat (w_coh ws !! a).

Definition ws_init : wstate :=
  {| w_coh := ∅; w_vrOld := 0; w_vwOld := 0; w_vrNew := 0; w_vwNew := 0;
     w_vRel := 0; w_fwd := ∅ |}.

Lemma coh_init a : coh ws_init a = 0%nat.
Proof. done. Qed.

Lemma coh_upd_eq m vrO vwO vrN vwN vR fwd a n :
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd |} a = n.
Proof. rewrite /coh /= lookup_insert //. Qed.

Lemma coh_upd_ne m vrO vwO vrN vwN vR fwd a a' n :
  a' ≠ a →
  coh {| w_coh := <[a := n]> m; w_vrOld := vrO; w_vwOld := vwO;
         w_vrNew := vrN; w_vwNew := vwN; w_vRel := vR; w_fwd := fwd |} a'
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
    the bank is FORWARDED: it takes the view the bank recorded (the store's
    fence floor at store time — the weakest sound choice) instead of the
    timestamp itself.  Any other timestamp contributes [t] as before.

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
     w_fwd   := w_fwd ws |}.

Definition load_post (ws : wstate) (aq : bool) (a : Z) (t : nat) : wstate :=
  load_post_at ws aq (load_vpre ws aq) a t.

(** Stores.  Promise-free: the timestamp is always the log's fresh top, so the
    store rule has no admissibility condition to check. *)
Definition store_post (ws : wstate) (rl : bool) (a : Z) (t : nat) : wstate :=
  {| w_coh   := <[a := Nat.max (coh ws a) t]> (w_coh ws);
     w_vrOld := w_vrOld ws;
     w_vwOld := Nat.max (w_vwOld ws) t;
     w_vrNew := w_vrNew ws;
     w_vwNew := w_vwNew ws;
     w_vRel  := if rl then Nat.max (w_vRel ws) t else w_vRel ws;
     w_fwd   := <[a := (t, w_vwNew ws)]> (w_fwd ws) |}.

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
     w_fwd   := w_fwd ws |}.

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

Definition ws_le (w1 w2 : wstate) : Prop :=
  (∀ a, (coh w1 a ≤ coh w2 a)%nat) ∧
  (w_vrOld w1 ≤ w_vrOld w2)%nat ∧ (w_vwOld w1 ≤ w_vwOld w2)%nat ∧
  (w_vrNew w1 ≤ w_vrNew w2)%nat ∧ (w_vwNew w1 ≤ w_vwNew w2)%nat ∧
  (w_vRel  w1 ≤ w_vRel  w2)%nat.

Global Instance ws_le_refl : Reflexive ws_le.
Proof. intros w. rewrite /ws_le. split_and!; auto with lia. Qed.

Global Instance ws_le_trans : Transitive ws_le.
Proof.
  intros w1 w2 w3 (?&?&?&?&?&?) (?&?&?&?&?&?).
  rewrite /ws_le; split_and!; try lia. intros a. etrans; eauto.
Qed.

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
  rewrite /ws_le /store_post /=. split_and!; try (destruct rl; lia).
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

(** If [t] writes [a], the agent's coherence floor already covers [t], and no
    LATER timestamp in the whole log writes [a], then [t] is the ONLY readable
    timestamp for [a] — the reader is pinned to the top message. *)
Lemma readable_top_unique img log ws vpre a t t' :
  is_Some (log_byte img log t a) →
  (t ≤ coh ws a)%nat →
  ¬ writes_in log a t (length log) →
  readable img log ws vpre a t' →
  t' = t.
Proof.
  intros Ht Hcoh Htop [Ht' Hn'].
  destruct (decide (t' = t)) as [->|Hne]; [done|exfalso].
  destruct (decide (t' < t)%nat) as [Hlt|Hge].
  - (* [t] itself is a write in [t']'s forbidden window *)
    apply Hn'. eapply (writes_in_log_byte img). exists t.
    split_and!; [lia|lia|done].
  - (* [t'] is a write strictly above [t], contradicting topness *)
    apply Htop. eapply (writes_in_log_byte img). exists t'.
    split_and!; [lia| |done]. exact (log_byte_bounded _ _ _ _ Ht').
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

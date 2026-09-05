(** * TsoMem.v — the minimal view machine (leg T spike), RELAXED FOR R→R AND W→W

    The memory model of record: a global append-only ISSUE log, a global
    DRAIN log, and a small per-hart state.  Born as the Ztso machine of the
    TSO port ([claude-notes/completed/tso-cutover-endgame.md]) with ONE
    monotone log index per hart; relaxed for load–load reordering per
    [claude-notes/completed/relaxed-rr.md] (two per-hart pieces, one
    deleted assignment); relaxed for store–store reordering per
    [claude-notes/projects/relaxed-ww.md] (the second log).  It is still
    the deliberate simplification of the `weak-memory` branch's
    promise-free RVWMO machine: R→W order and multi-copy atomicity are
    KEPT, syntactic dependencies are not modelled.

    THE MACHINE.  State = era-initial image + `log : list wmsg` (the ISSUE
    log; each message carries its author) + `dl : list nat` (the DRAIN log:
    issue indices in the order they reached memory) + per hart: a FLOOR
    `tv`, a READ WATERMARK `rv`, a per-byte COHERENCE FLOOR `coh`, all of
    them DRAIN POSITIONS.

      - A message at issue index `i` has TIMESTAMP `S i` (timestamp 0 the
        image): its IDENTITY, what the ghost layer keys on.  It is PENDING
        until `i ∈ dl`; the drain log's position `S q` of `dl !! q = i` is
        its COHERENCE position.  The drain order IS the coherence order:
        memory is the image with `dl`'s messages applied in order.
      - VISIBILITY: hart `h` at view `tv'` sees drain position `p` iff
        `p ≤ tv'` or the message there is h's own.  Its own PENDING
        messages it always sees (store-buffer forwarding); a foreign
        pending message is invisible to everyone.
      - LOAD of byte `a`: choose any `tv'` with `tv ≤ tv'`, `coh a ≤ tv'`,
        `tv' ≤ length dl`.  The value is the hart's latest ISSUED pending
        message to `a` if it has one — it will drain after everything
        drained today, so it is coherence-latest — else the LATEST VISIBLE
        drain position writing `a`.  The floor does not move (relaxed-rr);
        `rv := max rv tv'`, `coh a := tv'`.
      - STORE: append to the issue log; born pending.  Nothing else moves.
      - DRAIN: an environment step.  Any pending message whose author's
        earlier OVERLAPPING messages have all drained may drain (per-byte
        FIFO per hart is CoWW; different bytes are unordered).
      - FENCE: a fence whose predecessor set contains W ([fence_rel]) is
        ENABLED only when every own message has drained — the model's
        "wait for my store buffer".  Then a W→R edge ([fence_drains])
        raises the floor past [own_pub], the hart's highest own drain
        position ("everything drained before my last store"); an R→R edge
        ([fence_acq]) raises it past the read watermark.  `w,w`/`rw,w`
        wait and move nothing; `r,*` fences do not wait.
      - EXCLUSIVE/AMO read: enabled only when the hart has no pending
        message to the byte (same-address program order), or — for `.rl` —
        no pending message at all; reads MEMORY, i.e. the drain log's flat.
        The write half appends to BOTH logs (an AMO is performed at
        memory); the `.aq` floor rule is relaxed-rr's.
      - NOT MODELLED: RVWMO's syntactic address/data/control dependency
        order (ppo 9–13).  The MP+addr litmus records this as ALLOWED on
        purpose.

    Devices (the disk's DMA) are agents that read memory and whose writes
    drain at once.  Crash/power: the logs are per-era and die with RAM at a
    power edge; that is the language layer's era machinery, not this file's.

    DELIBERATELY DEPENDENCY-FREE: stdpp only, no Iris, no Sail.  Addresses
    are [Z], bytes [bv 8], agents [nat]; the real machine instantiates at
    [Arch.pa]/[CPU].  Beware the [gmap Arch.pa _] Countable trap (durable
    notes): the era image is a partial FUNCTION on [Z], not a [gmap]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.

Local Open Scope Z_scope.

(** Agents: harts AND bus-master devices (the disk).  Abstract. *)
Notation agent := nat.

(** The era-initial image (timestamp 0 / drain position 0). *)
Definition image : Type := Z → option (bv 8).

(* ------------------------------------------------------------------ *)
(** ** Messages and the issue log *)

(** One write event, covering the byte range [wm_pa, wm_pa + |wm_data|).
    Every message carries its author: forwarding and the drain FIFO key on
    it.  No message class, no annotation field: what orders a store is the
    author's fences (when it may drain), what orders a load is the reader's
    floor. *)
Record wmsg := WMsg {
  wm_pa   : Z;
  wm_data : list (bv 8);
  wm_tid  : agent;
}.
Add Printing Constructor wmsg.

Global Instance wmsg_eq_dec : EqDecision wmsg.
Proof. solve_decision. Defined.

(** The byte message [m] writes at address [a] (None outside its range). *)
Definition msg_byte (m : wmsg) (a : Z) : option (bv 8) :=
  if bool_decide (wm_pa m ≤ a)
  then wm_data m !! Z.to_nat (a - wm_pa m)
  else None.

(** The byte written at timestamp [t] of the ISSUE log (0 = the image;
    [S i] = issue index [i]).  The ledger side's vocabulary. *)
Definition log_byte (img : image) (log : list wmsg) (t : nat) (a : Z)
    : option (bv 8) :=
  match t with
  | O => img a
  | S i => match log !! i with Some m => msg_byte m a | None => None end
  end.

(** Two messages overlap when some byte is in both ranges. *)
Definition msg_overlapb (m m' : wmsg) : bool :=
  bool_decide (wm_pa m < wm_pa m' + Z.of_nat (length (wm_data m'))) &&
  bool_decide (wm_pa m' < wm_pa m + Z.of_nat (length (wm_data m))).

Lemma msg_byte_some_range m a v :
  msg_byte m a = Some v →
  wm_pa m ≤ a ∧ a < wm_pa m + Z.of_nat (length (wm_data m)).
Proof.
  rewrite /msg_byte. case_bool_decide as Hle; [|done].
  move => Hlk. apply lookup_lt_Some in Hlk. split; [done|lia].
Qed.

Lemma msg_overlapb_of_byte m m' a v v' :
  msg_byte m a = Some v → msg_byte m' a = Some v' → msg_overlapb m m' = true.
Proof.
  move => /msg_byte_some_range [? ?] /msg_byte_some_range [? ?].
  rewrite /msg_overlapb. apply andb_true_intro.
  split; apply bool_decide_eq_true_2; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The drain log *)

(** [i] has reached memory. *)
Definition drainedb (dl : list nat) (i : nat) : bool := bool_decide (i ∈ dl).

Lemma drainedb_true dl i : drainedb dl i = true ↔ i ∈ dl.
Proof. rewrite /drainedb. apply bool_decide_eq_true. Qed.

Lemma drainedb_false dl i : drainedb dl i = false ↔ i ∉ dl.
Proof. rewrite /drainedb. apply bool_decide_eq_false. Qed.

(** The message at drain position [p] (1-based; none at 0 or past the top). *)
Definition dmsg (log : list wmsg) (dl : list nat) (p : nat) : option wmsg :=
  match p with
  | O => None
  | S q => match dl !! q with Some i => log !! i | None => None end
  end.

(** The byte written at drain position [p] (0 = the image). *)
Definition dpos_byte (img : image) (log : list wmsg) (dl : list nat)
    (p : nat) (a : Z) : option (bv 8) :=
  match p with
  | O => img a
  | S _ => match dmsg log dl p with Some m => msg_byte m a | None => None end
  end.

(** Well-formed drain log: no message drains twice, every entry is issued. *)
Definition dl_ok (log : list wmsg) (dl : list nat) : Prop :=
  NoDup dl ∧ ∀ i, i ∈ dl → (i < length log)%nat.

(* ------------------------------------------------------------------ *)
(** ** Per-hart state: the view is a drain position *)

Notation tview := nat (only parsing).

(** Drain position [p] is visible to agent [h] at view [tv]. *)
Definition visibleb (h : agent) (tv : tview) (log : list wmsg)
    (dl : list nat) (p : nat) : bool :=
  bool_decide (p ≤ tv)%nat ||
  match dmsg log dl p with
  | Some m => bool_decide (wm_tid m = h)
  | None => false
  end.

Lemma visibleb_below h tv log dl p :
  (p ≤ tv)%nat → visibleb h tv log dl p = true.
Proof. rewrite /visibleb => Hp. rewrite bool_decide_eq_true_2 //. Qed.

Lemma visibleb_own h tv log dl q i m :
  dl !! q = Some i → log !! i = Some m → wm_tid m = h →
  visibleb h tv log dl (S q) = true.
Proof.
  rewrite /visibleb /dmsg => Hq Hi Htid. rewrite Hq Hi Htid.
  have -> : bool_decide (h = h) = true by apply bool_decide_eq_true_2.
  by destruct (bool_decide (S q ≤ tv)%nat).
Qed.

Lemma visibleb_le h tv tv' log dl p :
  (tv ≤ tv')%nat → visibleb h tv log dl p = true →
  visibleb h tv' log dl p = true.
Proof.
  rewrite /visibleb => Hle.
  destruct (bool_decide (p ≤ tv)%nat) eqn:Hp => /=.
  - move => _. apply bool_decide_eq_true in Hp.
    have -> : bool_decide (p ≤ tv')%nat = true
      by apply bool_decide_eq_true_2; lia.
    done.
  - move => Ho. rewrite Ho. by destruct (bool_decide (p ≤ tv')%nat).
Qed.

Lemma visibleb_true h tv log dl p :
  visibleb h tv log dl p = true →
  (p ≤ tv)%nat ∨
  ∃ q i m, p = S q ∧ dl !! q = Some i ∧ log !! i = Some m ∧ wm_tid m = h.
Proof.
  rewrite /visibleb.
  destruct (bool_decide (p ≤ tv)%nat) eqn:Hp => /=.
  { move => _. left. by apply bool_decide_eq_true in Hp. }
  destruct p as [|q]; first by move => _; left; lia.
  rewrite /dmsg.
  destruct (dl !! q) as [i|] eqn:Hq; last by move => H; discriminate H.
  destruct (log !! i) as [m|] eqn:Hi; last by move => H; discriminate H.
  destruct (bool_decide (wm_tid m = h)) eqn:Htid;
    last by move => H; discriminate H.
  move => _. right. exists q, i, m.
  split_and!; [done|done|done|by apply bool_decide_eq_true in Htid].
Qed.

(** Appending to EITHER log preserves the visibility of an in-range drain
    position.  (Both arms: the position's message does not change.) *)
Lemma dmsg_app_log log m dl p :
  dl_ok log dl → dmsg (log ++ [m]) dl p = dmsg log dl p.
Proof.
  move => [_ Hlt]. rewrite /dmsg. destruct p as [|q]; first done.
  destruct (dl !! q) as [i|] eqn:Hq; last done.
  apply lookup_app_l. apply Hlt. by eapply elem_of_list_lookup_2.
Qed.

Lemma dmsg_app_dl log dl j p :
  (p ≤ length dl)%nat → dmsg log (dl ++ [j]) p = dmsg log dl p.
Proof.
  move => Hp. rewrite /dmsg. destruct p as [|q]; first done.
  have -> : (dl ++ [j]) !! q = dl !! q by apply lookup_app_l; lia.
  done.
Qed.

Lemma visibleb_app_log h tv log m dl p :
  dl_ok log dl →
  visibleb h tv (log ++ [m]) dl p = visibleb h tv log dl p.
Proof. move => Hok. rewrite /visibleb (dmsg_app_log _ _ _ _ Hok) //. Qed.

Lemma visibleb_app_dl h tv log dl j p :
  (p ≤ length dl)%nat →
  visibleb h tv log (dl ++ [j]) p = visibleb h tv log dl p.
Proof. move => Hp. rewrite /visibleb (dmsg_app_dl _ _ _ _ Hp) //. Qed.

(* ------------------------------------------------------------------ *)
(** ** Reading: own pending first, else the latest visible drain position *)

(** Scan drain positions downward from [p]; the first visible one that
    writes [a] supplies the value. *)
Fixpoint read_down (img : image) (log : list wmsg) (dl : list nat)
    (h : agent) (tv : tview) (a : Z) (p : nat) : option (bv 8) :=
  match (if visibleb h tv log dl p then dpos_byte img log dl p a else None) with
  | Some v => Some v
  | None => match p with O => None | S p' => read_down img log dl h tv a p' end
  end.

(** The hart's latest ISSUED pending message to [a]: scan issue indices
    downward from [t]. *)
Fixpoint pend_down (log : list wmsg) (dl : list nat) (h : agent) (a : Z)
    (t : nat) : option (bv 8) :=
  match t with
  | O => None
  | S i =>
      match log !! i with
      | Some m =>
          if bool_decide (wm_tid m = h) && negb (drainedb dl i)
          then match msg_byte m a with
               | Some v => Some v
               | None => pend_down log dl h a i
               end
          else pend_down log dl h a i
      | None => pend_down log dl h a i
      end
  end.

Definition pend_read (log : list wmsg) (dl : list nat) (h : agent) (a : Z)
    : option (bv 8) :=
  pend_down log dl h a (length log).

(** The value agent [h] at view [tv] reads at byte [a]. *)
Definition tso_read (img : image) (log : list wmsg) (dl : list nat)
    (h : agent) (tv : tview) (a : Z) : option (bv 8) :=
  match pend_read log dl h a with
  | Some v => Some v
  | None => read_down img log dl h tv a (length dl)
  end.

(** An [n]-byte load reads every byte at the SAME view. *)
Definition tso_read_bytes (img : image) (log : list wmsg) (dl : list nat)
    (h : agent) (tv : tview) (a : Z) (n : nat) : list (option (bv 8)) :=
  (λ i, tso_read img log dl h tv (a + Z.of_nat i)) <$> seq 0 n.

(** MEMORY: the image with the drain log's messages applied in order.
    What an AMO and a bus master read. *)
Definition dflat (img : image) (log : list wmsg) (dl : list nat) (a : Z)
    : option (bv 8) :=
  foldl (λ acc i, match log !! i with
                  | Some m => match msg_byte m a with Some v => Some v | None => acc end
                  | None => acc
                  end)
        (img a) dl.

(* ------------------------------------------------------------------ *)
(** ** The step vocabulary *)

(** [forallb] over a list, read at one element. *)
Lemma forallb_lookup {A} (f : A → bool) (l : list A) (x : A) :
  forallb f l = true → x ∈ l → f x = true.
Proof. move => /forallb_forall Hf /elem_of_list_In Hx. by apply Hf. Qed.

(** All of [h]'s messages have drained. *)
Definition own_drainedb (h : agent) (log : list wmsg) (dl : list nat) : bool :=
  forallb (λ j, match log !! j with
                | Some m => if bool_decide (wm_tid m = h) then drainedb dl j else true
                | None => true
                end) (seq 0 (length log)).

Definition own_drained (h : agent) (log : list wmsg) (dl : list nat) : Prop :=
  own_drainedb h log dl = true.

Lemma own_drained_lookup h log dl i m :
  own_drained h log dl → log !! i = Some m → wm_tid m = h → i ∈ dl.
Proof.
  rewrite /own_drained /own_drainedb => Hall Hi Htid.
  have Hlt : (i < length log)%nat by eapply lookup_lt_Some.
  have Hin : i ∈ seq 0 (length log) by apply elem_of_seq; lia.
  have Hj := forallb_lookup _ _ _ Hall Hin.
  rewrite Hi Htid bool_decide_eq_true_2 // in Hj. by apply drainedb_true.
Qed.

(** The hart's highest own DRAIN position: [S q] of its last drained
    message, 0 if none. *)
Definition own_pub (h : agent) (log : list wmsg) (dl : list nat) : nat :=
  foldr Nat.max 0%nat
    (imap (λ q i, match log !! i with
                  | Some m => if bool_decide (wm_tid m = h) then S q else 0%nat
                  | None => 0%nat
                  end) dl).

(** The per-byte coherence floor: the view at which this hart last read
    the byte (0 = never).  A total function on [Z], like the image. *)
Definition cohmap : Type := Z → nat.

Definition coh_upd (c : cohmap) (a : Z) (t : nat) : cohmap :=
  λ a', if bool_decide (a' = a) then t else c a'.

Lemma coh_upd_eq c a t : coh_upd c a t a = t.
Proof. rewrite /coh_upd. by rewrite bool_decide_eq_true_2. Qed.

Lemma coh_upd_ne c a a' t : a' ≠ a → coh_upd c a t a' = c a'.
Proof. intros Hne. rewrite /coh_upd. by rewrite bool_decide_eq_false_2. Qed.

(** LOAD: pick a view at or above the hart's floor [tv] AND at or above
    the byte's coherence floor [ca], bounded by the drain log's top; read
    there.  The floor itself does not move — the caller records
    [rv := max rv tv'] and [coh a := tv']. *)
Definition load_ok (img : image) (log : list wmsg) (dl : list nat) (h : agent)
    (tv ca tv' : tview) (a : Z) (v : bv 8) : Prop :=
  (tv ≤ tv')%nat ∧ (ca ≤ tv')%nat ∧ (tv' ≤ length dl)%nat ∧
  tso_read img log dl h tv' a = Some v.

(** STORE: append to the issue log; born pending; nothing per-hart moves. *)
Definition store_log (log : list wmsg) (h : agent) (a : Z)
    (data : list (bv 8)) : list wmsg :=
  log ++ [WMsg a data h].

(** DRAIN: [i] is issued, pending, and every earlier message of the same
    author that overlaps it has drained. *)
Definition drain_okb (log : list wmsg) (dl : list nat) (i : nat) : bool :=
  match log !! i with
  | None => false
  | Some m =>
      negb (drainedb dl i) &&
      forallb (λ j, match log !! j with
                    | Some mj =>
                        if bool_decide (wm_tid mj = wm_tid m) && msg_overlapb mj m
                        then drainedb dl j else true
                    | None => true
                    end) (seq 0 i)
  end.

Definition drain_ok (log : list wmsg) (dl : list nat) (i : nat) : Prop :=
  drain_okb log dl i = true.

Definition drain_log (dl : list nat) (i : nat) : list nat := dl ++ [i].

Lemma drain_ok_issued log dl i : drain_ok log dl i → ∃ m, log !! i = Some m.
Proof. rewrite /drain_ok /drain_okb. destruct (log !! i); [eauto|done]. Qed.

Lemma drain_ok_pending log dl i : drain_ok log dl i → i ∉ dl.
Proof.
  rewrite /drain_ok /drain_okb. destruct (log !! i); [|done].
  move => /andb_true_iff [Hp _]. apply drainedb_false. by apply negb_true_iff.
Qed.

Lemma drain_ok_fifo log dl i j m mj :
  drain_ok log dl i → (j < i)%nat →
  log !! i = Some m → log !! j = Some mj →
  wm_tid mj = wm_tid m → msg_overlapb mj m = true → j ∈ dl.
Proof.
  rewrite /drain_ok /drain_okb => Hok Hji Hi Hj Htid Hov. rewrite Hi in Hok.
  move: Hok => /andb_true_iff [_ Hall].
  have Hin : j ∈ seq 0 i by apply elem_of_seq; lia.
  have Hjj := forallb_lookup _ _ _ Hall Hin.
  rewrite Hj Htid Hov bool_decide_eq_true_2 // in Hjj. by apply drainedb_true.
Qed.

Lemma drain_dl_ok log dl i :
  dl_ok log dl → drain_ok log dl i → dl_ok log (drain_log dl i).
Proof.
  move => [Hnd Hlt] Hok. rewrite /drain_log. split.
  - apply list_relations.NoDup_app. split_and!; [done| |apply NoDup_singleton].
    move => x Hx Hx'. apply elem_of_list_singleton in Hx' as ->.
    by apply (drain_ok_pending _ _ _ Hok).
  - move => j /elem_of_app [Hj|Hj]; first by apply Hlt.
    apply elem_of_list_singleton in Hj as ->.
    destruct (drain_ok_issued _ _ _ Hok) as [m Hm]. by eapply lookup_lt_Some.
Qed.

(** FENCE.  [fence_rel] (predecessor set contains W) is the ENABLING
    condition: every own message has drained.  Then a W→R edge DRAINS —
    the floor passes the hart's highest own drain position — and an R→R
    edge ACQUIRES — the floor passes the read watermark. *)
Definition fence_rel (pw : bool) : bool := pw.
Definition fence_drains (pw sr : bool) : bool := pw && sr.
Definition fence_acq (pr sr : bool) : bool := pr && sr.

Definition fence_okb (h : agent) (log : list wmsg) (dl : list nat) (pw : bool)
    : bool :=
  negb (fence_rel pw) || own_drainedb h log dl.

Definition fence_ok (h : agent) (log : list wmsg) (dl : list nat) (pw : bool)
    : Prop :=
  fence_okb h log dl pw = true.

Lemma fence_ok_rel h log dl pw :
  fence_ok h log dl pw → fence_rel pw = true → own_drained h log dl.
Proof.
  rewrite /fence_ok /fence_okb => Hok Hrel. rewrite Hrel /= in Hok. exact Hok.
Qed.

Definition fence_post (h : agent) (log : list wmsg) (dl : list nat)
    (pr pw sr sw : bool) (tv rv : tview) : tview :=
  Nat.max tv (Nat.max (if fence_drains pw sr then own_pub h log dl else 0%nat)
                      (if fence_acq pr sr then rv else 0%nat)).

Lemma fence_post_ge_tv h log dl pr pw sr sw tv rv :
  (tv ≤ fence_post h log dl pr pw sr sw tv rv)%nat.
Proof. rewrite /fence_post. lia. Qed.

Lemma fence_post_drain h log dl pr pw sr sw tv rv :
  fence_drains pw sr = true →
  (own_pub h log dl ≤ fence_post h log dl pr pw sr sw tv rv)%nat.
Proof. rewrite /fence_post => ->. lia. Qed.

Lemma fence_post_acq h log dl pr pw sr sw tv rv :
  fence_acq pr sr = true →
  (rv ≤ fence_post h log dl pr pw sr sw tv rv)%nat.
Proof. rewrite /fence_post => ->. lia. Qed.

(** EXCLUSIVE READ (the read half of an AMO): enabled when the hart has no
    pending message to the byte — or, with [.rl], none at all — and reads
    MEMORY. *)
Definition amo_okb (h : agent) (log : list wmsg) (dl : list nat) (rl : bool)
    (a : Z) : bool :=
  if rl then own_drainedb h log dl
  else bool_decide (pend_read log dl h a = None).

Definition excl_read_ok (img : image) (log : list wmsg) (dl : list nat)
    (h : agent) (rl : bool) (a : Z) (v : bv 8) : Prop :=
  amo_okb h log dl rl a = true ∧ dflat img log dl a = Some v.

(** The write half of an AMO: append to both logs — performed at memory. *)
Definition amo_store (log : list wmsg) (dl : list nat) (h : agent) (a : Z)
    (data : list (bv 8)) : list wmsg * list nat :=
  (store_log log h a data, dl ++ [length log]).

(* ------------------------------------------------------------------ *)
(** ** Sanity theorems *)

(** One-step unfolding equations, so proofs never [simpl] the fixpoints. *)
Lemma read_down_S img log dl h tv a p :
  read_down img log dl h tv a (S p) =
  match (if visibleb h tv log dl (S p) then dpos_byte img log dl (S p) a else None)
  with
  | Some v => Some v
  | None => read_down img log dl h tv a p
  end.
Proof. done. Qed.

Lemma read_down_0 img log dl h tv a :
  read_down img log dl h tv a 0 = img a.
Proof. simpl. by destruct (bool_decide (0 ≤ tv)%nat); destruct (img a). Qed.

Lemma pend_down_S log dl h a i :
  pend_down log dl h a (S i) =
  match log !! i with
  | Some m =>
      if bool_decide (wm_tid m = h) && negb (drainedb dl i)
      then match msg_byte m a with
           | Some v => Some v
           | None => pend_down log dl h a i
           end
      else pend_down log dl h a i
  | None => pend_down log dl h a i
  end.
Proof. done. Qed.

(** Reading down from [p] reads SOME visible drain position ≤ [p]. *)
Lemma read_down_le img log dl h tv a p :
  ∀ v, read_down img log dl h tv a p = Some v →
  ∃ p', (p' ≤ p)%nat ∧ visibleb h tv log dl p' = true ∧
        dpos_byte img log dl p' a = Some v.
Proof.
  induction p as [|p IH] => v.
  - rewrite read_down_0 => Hi. exists 0%nat.
    split_and!; [lia| by (apply visibleb_below; lia) | done].
  - rewrite read_down_S.
    destruct (visibleb h tv log dl (S p)) eqn:Hv.
    + destruct (dpos_byte img log dl (S p) a) eqn:Hb.
      * move => [<-]. exists (S p). by split_and!.
      * move => /IH [p' [? [? ?]]]. exists p'. split_and!; [lia|done|done].
    + move => /IH [p' [? [? ?]]]. exists p'. split_and!; [lia|done|done].
Qed.

(** The latest-visible characterization: a visible write below the scan
    start forces the scan to return a value from at least that high. *)
Lemma read_down_latest img log dl h tv a p p' v' :
  (p' ≤ p)%nat → visibleb h tv log dl p' = true →
  dpos_byte img log dl p' a = Some v' →
  ∃ p'' v'', (p' ≤ p'')%nat ∧ read_down img log dl h tv a p = Some v'' ∧
             visibleb h tv log dl p'' = true ∧
             dpos_byte img log dl p'' a = Some v''.
Proof.
  induction p as [|p IH] => Hle Hvis Hb.
  - assert (p' = 0%nat) as -> by lia.
    exists 0%nat, v'. split_and!; [lia|by rewrite read_down_0|exact Hvis|exact Hb].
  - rewrite read_down_S.
    destruct (visibleb h tv log dl (S p)) eqn:Hv.
    + destruct (dpos_byte img log dl (S p) a) eqn:Hbt.
      * exists (S p), b. split_and!; [lia|done|done|done].
      * destruct (decide (p' = S p)) as [->|Hne].
        { rewrite Hbt in Hb. done. }
        destruct (IH ltac:(lia) Hvis Hb) as (p''&v''&?&Hr&?&?).
        exists p'', v''. rewrite Hr. split_and!; [lia|done|done|done].
    + destruct (decide (p' = S p)) as [->|Hne].
      { rewrite Hv in Hvis. done. }
      destruct (IH ltac:(lia) Hvis Hb) as (p''&v''&?&Hr&?&?).
      exists p'', v''. rewrite Hr. split_and!; [lia|done|done|done].
Qed.

(** FRAME: appending a message to the ISSUE log changes no drain position's
    byte. *)
Lemma dpos_byte_app_log img log m dl p a :
  dl_ok log dl → dpos_byte img (log ++ [m]) dl p a = dpos_byte img log dl p a.
Proof.
  move => Hok. rewrite /dpos_byte. destruct p; first done.
  by rewrite (dmsg_app_log _ _ _ _ Hok).
Qed.

Lemma read_down_app_log img log m dl h tv a p :
  dl_ok log dl →
  read_down img (log ++ [m]) dl h tv a p = read_down img log dl h tv a p.
Proof.
  move => Hok. induction p as [|p IH]; first by rewrite !read_down_0.
  rewrite !read_down_S (visibleb_app_log _ _ _ _ _ _ Hok)
          (dpos_byte_app_log _ _ _ _ _ _ Hok) IH //.
Qed.

(** FRAME: appending to the DRAIN log changes nothing a scan of the old
    range sees, at any two views that both cover the range. *)
Lemma dpos_byte_app_dl img log dl j p a :
  (p ≤ length dl)%nat →
  dpos_byte img log (dl ++ [j]) p a = dpos_byte img log dl p a.
Proof.
  move => Hp. rewrite /dpos_byte. destruct p; first done.
  by rewrite (dmsg_app_dl _ _ _ _ Hp).
Qed.

Lemma read_down_app_dl_below img log dl j h tv tv' a p :
  (p ≤ length dl)%nat → (p ≤ tv)%nat → (p ≤ tv')%nat →
  read_down img log (dl ++ [j]) h tv' a p = read_down img log dl h tv a p.
Proof.
  induction p as [|p IH] => Hlen Htv Htv'.
  - by rewrite !read_down_0.
  - rewrite !read_down_S.
    have -> : visibleb h tv' log (dl ++ [j]) (S p) = true
      by apply visibleb_below; lia.
    have -> : visibleb h tv log dl (S p) = true by apply visibleb_below; lia.
    rewrite (dpos_byte_app_dl _ _ _ _ _ _ Hlen).
    destruct (dpos_byte img log dl (S p) a); first done. apply IH; lia.
Qed.

(** The pending scan over the OLD range does not see an appended message. *)
Lemma pend_down_app_log log m dl h a t :
  (t ≤ length log)%nat →
  pend_down (log ++ [m]) dl h a t = pend_down log dl h a t.
Proof.
  induction t as [|t IH] => Ht; first done.
  rewrite !pend_down_S.
  have -> : (log ++ [m]) !! t = log !! t by apply lookup_app_l; lia.
  rewrite IH; [lia|]. done.
Qed.

(** FORWARDING IS MANDATORY: a hart reads its own latest pending store at
    EVERY view.  (This is what makes SB and n6 go.) *)
Lemma pend_read_own_new log dl h a data v :
  dl_ok log dl →
  msg_byte (WMsg a data h) a = Some v →
  pend_read (store_log log h a data) dl h a = Some v.
Proof.
  move => [_ Hlt] Hb. rewrite /pend_read /store_log length_app /= Nat.add_1_r.
  rewrite pend_down_S.
  have -> : (log ++ [WMsg a data h]) !! length log = Some (WMsg a data h)
    by apply list_lookup_middle.
  have -> : drainedb dl (length log) = false.
  { apply drainedb_false => Hin. specialize (Hlt _ Hin). lia. }
  rewrite bool_decide_eq_true_2 //= Hb //.
Qed.

Lemma tso_read_own_pending img log dl h tv a v :
  pend_read log dl h a = Some v → tso_read img log dl h tv a = Some v.
Proof. rewrite /tso_read => -> //. Qed.

(** A pending scan that finds a value found one of the hart's OWN pending
    messages. *)
Lemma pend_down_some log dl h a t v :
  pend_down log dl h a t = Some v →
  ∃ i m, (i < t)%nat ∧ log !! i = Some m ∧ wm_tid m = h ∧ i ∉ dl ∧
         msg_byte m a = Some v.
Proof.
  induction t as [|t IH]; first done.
  rewrite pend_down_S.
  destruct (log !! t) as [m|] eqn:Hm.
  - destruct (bool_decide (wm_tid m = h) && negb (drainedb dl t)) eqn:Hc.
    + destruct (msg_byte m a) as [v0|] eqn:Hb.
      * move => [<-]. exists t, m.
        move: Hc => /andb_true_iff [/bool_decide_eq_true Htid /negb_true_iff Hd].
        split_and!; [lia|done|done|by apply drainedb_false|done].
      * intros Hr; destruct (IH Hr) as (i & m' & ? & ? & ? & ? & ?). exists i, m'. split_and!; [lia|done..].
    + intros Hr; destruct (IH Hr) as (i & m' & ? & ? & ? & ? & ?). exists i, m'. split_and!; [lia|done..].
  - intros Hr; destruct (IH Hr) as (i & m' & ? & ? & ? & ? & ?). exists i, m'. split_and!; [lia|done..].
Qed.

(** And conversely: a hart with an undrained message to [a] has SOME
    pending value there. *)
Lemma pend_down_none log dl h a t i m v :
  (i < t)%nat → log !! i = Some m → wm_tid m = h → i ∉ dl →
  msg_byte m a = Some v → pend_down log dl h a t ≠ None.
Proof.
  induction t as [|t IH] => Hlt Hi Htid Hnd Hb; first lia.
  rewrite pend_down_S.
  destruct (decide (i = t)) as [->|Hne].
  - rewrite Hi Htid bool_decide_eq_true_2 //.
    have -> : drainedb dl t = false by apply drainedb_false.
    rewrite /= Hb //.
  - have Hlt' : (i < t)%nat by lia.
    destruct (log !! t) as [m'|]; [|by apply IH].
    destruct (bool_decide (wm_tid m' = h) && negb (drainedb dl t)); [|by apply IH].
    destruct (msg_byte m' a); [done|by apply IH].
Qed.

(** THE SC COLLAPSE, at memory: with nothing of its own pending, a hart
    reading at the top reads [dflat].  An agent whose view is pinned to the
    top and whose stores drain at once is a sequentially consistent agent. *)
Lemma dflat_snoc img log dl i a :
  dflat img log (dl ++ [i]) a =
  match log !! i with
  | Some m => match msg_byte m a with Some v => Some v | None => dflat img log dl a end
  | None => dflat img log dl a
  end.
Proof. rewrite /dflat foldl_app //. Qed.

Lemma read_down_top_flat img log dl h a :
  read_down img log dl h (length dl) a (length dl) = dflat img log dl a.
Proof.
  induction dl as [|i dl IH] using rev_ind.
  - rewrite read_down_0 /dflat //.
  - rewrite dflat_snoc.
    have Hlen : length (dl ++ [i]) = S (length dl) by rewrite length_app /=; lia.
    rewrite Hlen read_down_S.
    have -> : visibleb h (S (length dl)) log (dl ++ [i]) (S (length dl)) = true
      by apply visibleb_below; lia.
    rewrite {1}/dpos_byte /dmsg.
    have -> : (dl ++ [i]) !! length dl = Some i by apply list_lookup_middle.
    destruct (log !! i) as [m|] eqn:Hm.
    + destruct (msg_byte m a) eqn:Hb; first done.
      rewrite (read_down_app_dl_below img log dl i h (length dl) (S (length dl))
                 a (length dl)); [lia|lia|lia|]. exact IH.
    + rewrite (read_down_app_dl_below img log dl i h (length dl) (S (length dl))
                 a (length dl)); [lia|lia|lia|]. exact IH.
Qed.

Lemma tso_read_top_flat img log dl h a :
  pend_read log dl h a = None →
  tso_read img log dl h (length dl) a = dflat img log dl a.
Proof. rewrite /tso_read => ->. apply read_down_top_flat. Qed.

(** A hart with everything drained has nothing pending anywhere. *)
Lemma own_drained_pend_none h log dl a :
  own_drained h log dl → pend_read log dl h a = None.
Proof.
  move => Hod. rewrite /pend_read.
  destruct (pend_down log dl h a (length log)) as [v|] eqn:Hp; last done.
  destruct (pend_down_some _ _ _ _ _ _ Hp) as (i & m & _ & Hi & Htid & Hnd & _).
  by destruct Hnd; eapply own_drained_lookup.
Qed.

(** [own_pub] bounds the hart's own drain positions from above, and sits
    under the top. *)
Lemma foldr_max_ge_lookup (l : list nat) (i x : nat) :
  l !! i = Some x → (x ≤ foldr Nat.max 0 l)%nat.
Proof.
  revert i. induction l as [|y l IH]; intros [|i] Hlk; simpl in Hlk;
    try discriminate.
  - simplify_eq. simpl. lia.
  - specialize (IH _ Hlk). simpl. lia.
Qed.

Lemma foldr_max_le_all (l : list nat) (n : nat) :
  Forall (λ x, x ≤ n)%nat l → (foldr Nat.max 0 l ≤ n)%nat.
Proof. induction 1 => /=; lia. Qed.

Lemma own_pub_ge h log dl q i m :
  dl !! q = Some i → log !! i = Some m → wm_tid m = h →
  (S q ≤ own_pub h log dl)%nat.
Proof.
  move => Hq Hi Htid. rewrite /own_pub. apply (foldr_max_ge_lookup _ q).
  rewrite list_lookup_imap Hq /= Hi Htid bool_decide_eq_true_2 //.
Qed.

Lemma own_pub_le h log dl : (own_pub h log dl ≤ length dl)%nat.
Proof.
  apply foldr_max_le_all. apply Forall_forall => x Hx.
  apply elem_of_list_In, elem_of_list_lookup in Hx as [q Hq].
  rewrite list_lookup_imap in Hq.
  destruct (dl !! q) as [i|] eqn:Hdq; simpl in Hq; [|done].
  apply lookup_lt_Some in Hdq. simplify_eq.
  destruct (log !! i); [case_bool_decide|]; lia.
Qed.

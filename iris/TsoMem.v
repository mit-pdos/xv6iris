(** * TsoMem.v — the minimal Ztso view machine (leg T spike)

    The memory model for the TSO port ([claude-notes/projects/tso-port.md],
    leg T): a global append-only write log plus, per hart, a SINGLE monotone
    log index — nothing else.  This is the deliberate simplification of the
    `weak-memory` branch's promise-free RVWMO machine (its `WeakMem.v`, whose
    per-hart state is a per-byte coherence map, five scalar views, a forward
    bank and more): TSO's implicit annotations (every load an acquire, every
    store a release) collapse all of that into one number.

    THE MACHINE.  State = era-initial image + `glog : list wmsg` (each
    message carries its author) + per hart a view `tv : nat`.

      - A message at log position `i` has TIMESTAMP `S i`; timestamp 0 is
        the era-initial image.  The log order IS the total store order.
      - VISIBILITY: hart `h` at view `tv` sees timestamp `t` iff `t ≤ tv`
        or the message at `t` is h's own.  Own messages being always
        visible is store-buffer FORWARDING; it is load-bearing (a store
        must NOT advance the author's view — that would forbid SB).
      - LOAD: choose any `tv' ` with `tv ≤ tv' ≤ length glog` (drain
        nondeterminism), move to `tv'`, and read the LATEST visible write
        of each byte.  Latest-visible (not "any non-superseded", as in
        RVWMO) is what forbids stale reads after fresh ones (R→R).
      - STORE: append at the top; the view does not move.
      - FENCE with a W→R edge (`pw ∧ sr`): raise the view past the hart's
        own last message — "my buffer has drained", and because drains
        happen in log order, everything below it has drained too.  All
        other fences are no-ops: Ztso already orders R→R, R→W, W→W.
      - EXCLUSIVE/AMO read: read at `tv' = length glog` — the globally
        latest value ("drain, then read memory").  The write half appends
        and takes the view past its own append.  Atomicity — no foreign
        write lands between the two halves — is the LANGUAGE's obligation,
        exactly today's reservation self-loop arms in `RiscvLang.mnode_step`,
        which this port keeps.

    Devices (the disk's DMA) are just agents: an agent index, a view, the
    same rules.  Crash/power: the log is per-era and dies with RAM at a
    power edge; that is the language layer's era machinery, not this file's.

    DELIBERATELY DEPENDENCY-FREE: stdpp only, no Iris, no Sail.  Addresses
    are [Z], bytes [bv 8], agents [nat]; the real machine instantiates at
    [Arch.pa]/[CPU].  Beware the [gmap Arch.pa _] Countable trap (durable
    notes): the era image is a partial FUNCTION on [Z], not a [gmap], so
    the eventual Sail-side seam is a definition, not a [kmap]. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.

Local Open Scope Z_scope.

(** Agents: harts AND bus-master devices (the disk).  Abstract. *)
Notation agent := nat.

(** The era-initial image (timestamp 0). *)
Definition image : Type := Z → option (bv 8).

(* ------------------------------------------------------------------ *)
(** ** Messages and the global write log *)

(** One write event, covering the byte range [wm_pa, wm_pa + |wm_data|).
    Every message carries its author: forwarding keys on it.  There is no
    message class and no annotation field — under Ztso every store is a
    release and every load an acquire, so there is nothing to record. *)
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

(** The byte written at timestamp [t] (0 = the image; [S i] = log slot [i]). *)
Definition log_byte (img : image) (log : list wmsg) (t : nat) (a : Z)
    : option (bv 8) :=
  match t with
  | O => img a
  | S i => match log !! i with Some m => msg_byte m a | None => None end
  end.

(* ------------------------------------------------------------------ *)
(** ** Per-hart state: one view *)

(** The WHOLE per-hart memory-model state. *)
Notation tview := nat (only parsing).

(** Timestamp [t] is visible to agent [h] at view [tv]. *)
Definition visibleb (h : agent) (tv : tview) (log : list wmsg) (t : nat)
    : bool :=
  bool_decide (t ≤ tv)%nat ||
  match t with
  | O => true
  | S i => match log !! i with
           | Some m => bool_decide (wm_tid m = h)
           | None => false
           end
  end.

Lemma visibleb_below h tv log t :
  (t ≤ tv)%nat → visibleb h tv log t = true.
Proof. rewrite /visibleb => Ht. rewrite bool_decide_eq_true_2 //. Qed.

Lemma visibleb_own h tv log i m :
  log !! i = Some m → wm_tid m = h → visibleb h tv log (S i) = true.
Proof.
  rewrite /visibleb => Hlk Htid. rewrite Hlk /= Htid.
  have -> : bool_decide (h = h) = true by apply bool_decide_eq_true_2.
  by destruct (bool_decide (S i ≤ tv)%nat).
Qed.

Lemma visibleb_le h tv tv' log t :
  (tv ≤ tv')%nat → visibleb h tv log t = true → visibleb h tv' log t = true.
Proof.
  rewrite /visibleb => Hle.
  destruct (bool_decide (t ≤ tv)%nat) eqn:Ht => /=.
  - move => _. apply bool_decide_eq_true in Ht.
    have -> : bool_decide (t ≤ tv')%nat = true
      by apply bool_decide_eq_true_2; lia.
    done.
  - move => Ho. rewrite Ho. by destruct (bool_decide (t ≤ tv')%nat).
Qed.

Lemma visibleb_true h tv log t :
  visibleb h tv log t = true →
  (t ≤ tv)%nat ∨ ∃ i m, t = S i ∧ log !! i = Some m ∧ wm_tid m = h.
Proof.
  rewrite /visibleb.
  destruct (bool_decide (t ≤ tv)%nat) eqn:Ht => /=.
  { move => _. left. by apply bool_decide_eq_true in Ht. }
  destruct t as [|i]; first by move => _; left; lia.
  destruct (log !! i) as [m|] eqn:Hlk; last by move => H; discriminate H.
  destruct (bool_decide (wm_tid m = h)) eqn:Htid;
    last by move => H; discriminate H.
  move => _. right. exists i, m.
  split_and!; [done|done|by apply bool_decide_eq_true in Htid].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reading: the latest visible write *)

(** Scan timestamps downward from [t]; the first visible one that writes
    [a] supplies the value.  The machine's read is DETERMINISTIC given the
    view — the only nondeterminism in a TSO load is the view advance. *)
Fixpoint read_down (img : image) (log : list wmsg) (h : agent) (tv : tview)
    (a : Z) (t : nat) : option (bv 8) :=
  match (if visibleb h tv log t then log_byte img log t a else None) with
  | Some v => Some v
  | None => match t with O => None | S t' => read_down img log h tv a t' end
  end.

(** The value agent [h] at view [tv] reads at byte [a]. *)
Definition tso_read (img : image) (log : list wmsg) (h : agent) (tv : tview)
    (a : Z) : option (bv 8) :=
  read_down img log h tv a (length log).

(** An [n]-byte load reads every byte at the SAME view. *)
Definition tso_read_bytes (img : image) (log : list wmsg) (h : agent)
    (tv : tview) (a : Z) (n : nat) : list (option (bv 8)) :=
  (λ i, tso_read img log h tv (a + Z.of_nat i)) <$> seq 0 n.

(* ------------------------------------------------------------------ *)
(** ** The step rules *)

(** The author's latest published timestamp: [S i] of its last message. *)
Definition own_pub (h : agent) (log : list wmsg) : nat :=
  foldr Nat.max 0%nat
    (imap (λ i m, if bool_decide (wm_tid m = h) then S i else 0%nat) log).

(** LOAD: advance the view (bounded by the log top), read latest-visible. *)
Definition load_ok (img : image) (log : list wmsg) (h : agent)
    (tv tv' : tview) (a : Z) (v : bv 8) : Prop :=
  (tv ≤ tv')%nat ∧ (tv' ≤ length log)%nat ∧
  tso_read img log h tv' a = Some v.

(** STORE: append at the top; the view does not move. *)
Definition store_log (log : list wmsg) (h : agent) (a : Z)
    (data : list (bv 8)) : list wmsg :=
  log ++ [WMsg a data h].

(** FENCE: only a fence ordering W→R ([pw ∧ sr]) does anything — it
    certifies the author's buffer drained, i.e. the view passes the
    author's last message.  Every other fence is a no-op under Ztso. *)
Definition fence_post (h : agent) (log : list wmsg)
    (pr pw sr sw : bool) (tv : tview) : tview :=
  if pw && sr then Nat.max tv (own_pub h log) else tv.

(** EXCLUSIVE READ (the read half of an AMO, `ak_latest`): drain and read
    the globally latest value; the view goes to the top. *)
Definition excl_read_ok (img : image) (log : list wmsg) (h : agent)
    (tv : tview) (a : Z) (v : bv 8) : Prop :=
  tso_read img log h (length log) a = Some v.

(** The write half of an AMO: append, and take the view past the append. *)
Definition amo_store (log : list wmsg) (h : agent) (a : Z)
    (data : list (bv 8)) : list wmsg * tview :=
  (store_log log h a data, S (length log)).

(* ------------------------------------------------------------------ *)
(** ** Sanity theorems *)

(** One-step unfolding equations, so proofs never [simpl] the fixpoint. *)
Lemma read_down_S img log h tv a t :
  read_down img log h tv a (S t) =
  match (if visibleb h tv log (S t) then log_byte img log (S t) a else None)
  with
  | Some v => Some v
  | None => read_down img log h tv a t
  end.
Proof. done. Qed.

Lemma read_down_0 img log h tv a :
  read_down img log h tv a 0 = img a.
Proof.
  simpl. by destruct (bool_decide (0 ≤ tv)%nat); destruct (img a).
Qed.

(** Reading down from [t] reads SOME visible timestamp ≤ [t]. *)
Lemma read_down_le img log h tv a t :
  ∀ v, read_down img log h tv a t = Some v →
  ∃ t', (t' ≤ t)%nat ∧ visibleb h tv log t' = true ∧
        log_byte img log t' a = Some v.
Proof.
  induction t as [|t IH] => v.
  - rewrite read_down_0 => Hi. exists 0%nat.
    split_and!; [lia| by (apply visibleb_below; lia) | done].
  - rewrite read_down_S.
    destruct (visibleb h tv log (S t)) eqn:Hv.
    + destruct (log_byte img log (S t) a) eqn:Hb.
      * move => [<-]. exists (S t). by split_and!.
      * move => /IH [t' [? [? ?]]]. exists t'. split_and!; [lia|done|done].
    + move => /IH [t' [? [? ?]]]. exists t'. split_and!; [lia|done|done].
Qed.

(** The latest-visible characterization, the direction the litmus
    "forbidden" proofs consume: a visible write below the scan start
    forces the scan to return a value from at least that high. *)
Lemma read_down_latest img log h tv a t t' v' :
  (t' ≤ t)%nat → visibleb h tv log t' = true →
  log_byte img log t' a = Some v' →
  ∃ t'' v'', (t' ≤ t'')%nat ∧ read_down img log h tv a t = Some v'' ∧
             visibleb h tv log t'' = true ∧
             log_byte img log t'' a = Some v''.
Proof.
  induction t as [|t IH] => Hle Hvis Hb.
  - assert (t' = 0%nat) as -> by lia.
    exists 0%nat, v'. split_and!.
    + lia.
    + rewrite read_down_0. exact Hb.
    + exact Hvis.
    + exact Hb.
  - rewrite read_down_S.
    destruct (visibleb h tv log (S t)) eqn:Hv.
    + destruct (log_byte img log (S t) a) eqn:Hbt.
      * exists (S t), b. split_and!; [lia|done|done|done].
      * destruct (decide (t' = S t)) as [->|Hne].
        { rewrite Hbt in Hb. done. }
        destruct (IH ltac:(lia) Hvis Hb) as (t''&v''&?&Hr&?&?).
        exists t'', v''. rewrite Hr. split_and!; [lia|done|done|done].
    + destruct (decide (t' = S t)) as [->|Hne].
      { rewrite Hv in Hvis. done. }
      destruct (IH ltac:(lia) Hvis Hb) as (t''&v''&?&Hr&?&?).
      exists t'', v''. rewrite Hr. split_and!; [lia|done|done|done].
Qed.

(** Appending a message does not change what a saturated-view scan of the
    OLD range sees: the frame lemma every top-of-log argument factors
    through. *)
Lemma read_down_app_below img log m h tv tv' a t :
  (t ≤ length log)%nat → (t ≤ tv)%nat → (t ≤ tv')%nat →
  read_down img (log ++ [m]) h tv' a t = read_down img log h tv a t.
Proof.
  induction t as [|t IH] => Hlen Htv Htv'.
  - by rewrite !read_down_0.
  - rewrite !read_down_S.
    have -> : visibleb h tv' (log ++ [m]) (S t) = true
      by apply visibleb_below; lia.
    have -> : visibleb h tv log (S t) = true by apply visibleb_below; lia.
    have Hlk : (log ++ [m]) !! t = log !! t by apply lookup_app_l; lia.
    rewrite {1}/log_byte /= Hlk.
    destruct (log !! t) as [m0|] eqn:Hm0.
    + destruct (msg_byte m0 a); first done. apply IH; lia.
    + apply IH; lia.
Qed.

(** FORWARDING IS MANDATORY: an agent whose message sits at the log top
    reads its own byte at EVERY view.  (This is what makes SB and n6 go.) *)
Lemma tso_read_own_top img log h a m v :
  wm_tid m = h → msg_byte m a = Some v →
  ∀ tv, tso_read img (log ++ [m]) h tv a = Some v.
Proof.
  move => Htid Hb tv. rewrite /tso_read.
  have -> : length (log ++ [m]) = S (length log).
  { rewrite length_app /=. lia. }
  have Hlk : (log ++ [m]) !! length log = Some m.
  { by apply list_lookup_middle. }
  rewrite read_down_S.
  have -> : visibleb h tv (log ++ [m]) (S (length log)) = true
    by eapply visibleb_own.
  by rewrite {1}/log_byte /= Hlk Hb.
Qed.

(** THE SC COLLAPSE: at the top view, [tso_read] is flat memory — the
    image with every message applied in log order.  This equation is the
    leg-C compatibility story in miniature: a hart whose view is pinned to
    the top is a sequentially consistent hart. *)
Definition flat (img : image) (log : list wmsg) (a : Z) : option (bv 8) :=
  foldl (λ acc m, match msg_byte m a with Some v => Some v | None => acc end)
        (img a) log.

Lemma flat_snoc img log m a :
  flat img (log ++ [m]) a =
  match msg_byte m a with Some v => Some v | None => flat img log a end.
Proof. rewrite /flat foldl_app //. Qed.

Lemma tso_read_top_flat img log h a :
  tso_read img log h (length log) a = flat img log a.
Proof.
  induction log as [|m log IH] using rev_ind.
  - rewrite /tso_read /flat /=. by repeat case_match.
  - rewrite /tso_read flat_snoc.
    have -> : length (log ++ [m]) = S (length log).
    { rewrite length_app /=. lia. }
    have Hlk : (log ++ [m]) !! length log = Some m.
    { by apply list_lookup_middle. }
    rewrite read_down_S.
    have -> : visibleb h (S (length log)) (log ++ [m]) (S (length log)) = true
      by apply visibleb_below; lia.
    rewrite {1}/log_byte /= Hlk.
    destruct (msg_byte m a) eqn:Hb; first done.
    rewrite (read_down_app_below img log m h (length log) (S (length log))
               a (length log)); [lia|lia|lia|].
    exact IH.
Qed.

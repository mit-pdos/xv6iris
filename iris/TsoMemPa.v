(** * TsoMemPa.v — the Ztso view machine AT THE MACHINE'S TYPES

    [TsoMem.v] is the leg-T spike: the minimal Ztso machine over [Z]
    addresses and base+byte-list messages, dependency-free, with the
    litmus suite ([TsoLitmus.v]) as its regression harness.  THIS file
    is the same machine restated at the types [RiscvLang.mnode_step]
    actually works in — [Arch.pa] keys, [gmap] image — so the flipped
    arms and the state interpretation can use it verbatim.  See
    [claude-notes/projects/tso-machine-flip.md] §1 for the design and
    the payload ruling; [TsoMem.v] stays as the model of record for the
    litmus verdicts (its shape and this one are the same machine).

    THE PAYLOAD RULING (tso-machine-flip.md): a message carries its
    byte MAP — [pwmsg := { pm_map : gmap Arch.pa (bv 8); pm_tid }],
    minted by the write arm as [PWMsg (write_bytes ∅ pa n v) tid], the
    same snapshot shape the reservations already use ([snap_of]).
    Consequences: [msg_byte] is a map lookup, the flat cache is a
    [foldl] of left-biased unions, and the ONE bridge to the arms'
    [write_bytes] update is [write_bytes_union] — no mword wrap
    arithmetic anywhere in this file.

    The machine, in one breath (TsoMem.v's header has the long form):
    memory-order TSO — a global append-only write log (log order IS the
    total store order; timestamp [S i] = slot [i], [0] = the era
    image), one monotone log index per agent (its VIEW), visibility =
    below-view OR own message (own-always-visible IS store forwarding),
    loads advance the view nondeterministically and read the LATEST
    visible write, stores append without moving the author's view,
    a W→R fence drains (view past the author's last message), and
    exclusive/AMO reads read at the top. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.

Local Open Scope Z_scope.

(** Agents: harts AND bus-master devices (the disk).  [RiscvLang] maps
    [CPU] in by [fin_to_nat] and gives the disk [NCPU]. *)
Notation agent := nat (only parsing).

(* THE FLAT BYTE MAP, AS A NAME.  A file that imports [SailStdpp.Base]
   elaborates a fresh [gmap Arch.pa (bv 8)] BINDER at the SAIL key instances
   ([Decidable_eq_mword]/[Countable_mword]) and it will not unify with the
   stdpp-keyed one this file and [RiscvLang] use -- the durable-notes binder
   trap, whose error names neither file.  [RiscvLang.v] avoids it by
   importing [SailStdpp.Base] LATE; a leaf file that cannot reorder its
   imports spells the type with this name instead. *)
Definition bytemap : Type := gmap Arch.pa (bv 8).

(* ------------------------------------------------------------------ *)
(** ** Messages and the global write log *)

Record pwmsg := PWMsg {
  pm_map : gmap Arch.pa (bv 8);
  pm_tid : agent;
}.
Add Printing Constructor pwmsg.

Global Instance pwmsg_eq_dec : EqDecision pwmsg.
Proof. solve_decision. Defined.

(* the ghost log ([era_logm_name]) stores messages as ghost_map VALUES;
   countability comes componentwise off the map and the agent *)
Global Instance pwmsg_countable : Countable pwmsg.
Proof.
  apply (inj_countable' (λ m, (pm_map m, pm_tid m))
           (λ p, PWMsg p.1 p.2)).
  by intros [].
Qed.

(** The byte message [m] writes at address [a]. *)
Definition msg_byte (m : pwmsg) (a : Arch.pa) : option (bv 8) :=
  pm_map m !! a.

(** The byte written at timestamp [t] (0 = the image; [S i] = slot [i]). *)
Definition log_byte (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (t : nat) (a : Arch.pa) : option (bv 8) :=
  match t with
  | O => img !! a
  | S i => match log !! i with Some m => msg_byte m a | None => None end
  end.

(* ------------------------------------------------------------------ *)
(** ** Visibility: below the view, or the agent's own message *)

Definition visibleb (h : agent) (tv : nat) (log : list pwmsg) (t : nat)
    : bool :=
  bool_decide (t ≤ tv)%nat ||
  match t with
  | O => true
  | S i => match log !! i with
           | Some m => bool_decide (pm_tid m = h)
           | None => false
           end
  end.

Lemma visibleb_below h tv log t :
  (t ≤ tv)%nat → visibleb h tv log t = true.
Proof. rewrite /visibleb => Ht. rewrite bool_decide_eq_true_2 //. Qed.

Lemma visibleb_own h tv log i m :
  log !! i = Some m → pm_tid m = h → visibleb h tv log (S i) = true.
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
  (t ≤ tv)%nat ∨ ∃ i m, t = S i ∧ log !! i = Some m ∧ pm_tid m = h.
Proof.
  rewrite /visibleb.
  destruct (bool_decide (t ≤ tv)%nat) eqn:Ht => /=.
  { move => _. left. by apply bool_decide_eq_true in Ht. }
  destruct t as [|i]; first by move => _; left; lia.
  destruct (log !! i) as [m|] eqn:Hlk; last by move => H; discriminate H.
  destruct (bool_decide (pm_tid m = h)) eqn:Htid;
    last by move => H; discriminate H.
  move => _. right. exists i, m.
  split_and!; [done|done|by apply bool_decide_eq_true in Htid].
Qed.

(** Appending preserves visibility of in-range timestamps (both arms). *)
Lemma visibleb_app h tv log m t :
  (t ≤ length log)%nat → visibleb h tv log t = true →
  visibleb h tv (log ++ [m]) t = true.
Proof.
  move => Ht Hvis.
  destruct (visibleb_true _ _ _ _ Hvis) as [Hle | (i & m0 & -> & Hlk & Htid)].
  - by apply visibleb_below.
  - have Hlk' : (log ++ [m]) !! i = Some m0 by apply lookup_app_l_Some.
    by apply (visibleb_own _ _ _ _ _ Hlk' Htid).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reading: the latest visible write *)

Fixpoint read_down (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (a : Arch.pa) (t : nat) : option (bv 8) :=
  match (if visibleb h tv log t then log_byte img log t a else None) with
  | Some v => Some v
  | None => match t with O => None | S t' => read_down img log h tv a t' end
  end.

Definition tso_read (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (a : Arch.pa) : option (bv 8) :=
  read_down img log h tv a (length log).

(** An [n]-byte load reads every byte at the SAME view. *)
Definition tso_read_bytes (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (a : Arch.pa) (n : N) {w : N} (v : bv w) : Prop :=
  ∀ j : nat, (N.of_nat j < n)%N →
    tso_read img log h tv (pa_add a j) = Some (nth_byte v j).

(* ------------------------------------------------------------------ *)
(** ** The step vocabulary the arms use *)

(** The author's latest published timestamp: [S i] of its last message. *)
Definition own_pub (h : agent) (log : list pwmsg) : nat :=
  foldr Nat.max 0%nat
    (imap (λ i m, if bool_decide (pm_tid m = h) then S i else 0%nat) log).

Lemma foldr_max_le (l : list nat) (n : nat) :
  Forall (λ x, x ≤ n)%nat l → (foldr Nat.max 0 l ≤ n)%nat.
Proof. induction 1 => /=; lia. Qed.

Lemma own_pub_le h log : (own_pub h log ≤ length log)%nat.
Proof.
  apply foldr_max_le. apply Forall_forall => x Hx.
  apply elem_of_list_In, elem_of_lookup_imap in Hx.
  destruct Hx as (i & y & -> & Hlk).
  apply lookup_lt_Some in Hlk. case_bool_decide => /=; lia.
Qed.

(** FENCE: the drain (the caller decides drain-ness from the barrier
    kind — [RiscvLang.fence_drains], W→R edges only under Ztso). *)
Definition fence_post (h : agent) (log : list pwmsg) (drain : bool)
    (tv : nat) : nat :=
  if drain then Nat.max tv (own_pub h log) else tv.

(* ------------------------------------------------------------------ *)
(** ** The flat cache: memory at the top of the log *)

Definition flat (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    : gmap Arch.pa (bv 8) :=
  foldl (λ acc m, pm_map m ∪ acc) img log.

Lemma flat_snoc img log m :
  flat img (log ++ [m]) = pm_map m ∪ flat img log.
Proof. rewrite /flat foldl_app //. Qed.

(* the option-union left unit, spelled once (stdpp has no rewrite form) *)
Lemma union_None_l {A} (my : option A) : None ∪ my = my.
Proof. by destruct my. Qed.

(** THE ONE BRIDGE between the arms' [write_bytes] update and the log
    append (the payload ruling's payoff): writing into a map IS the
    snapshot unioned over it. *)
Lemma write_bytes_union (m : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    {w : N} (v : bv w) :
  write_bytes m pa n v = write_bytes ∅ pa n v ∪ m.
Proof.
  rewrite /write_bytes. generalize (seq 0 (N.to_nat n)). clear.
  induction l as [|j l IH] => /=.
  - by rewrite left_id_L.
  - rewrite IH insert_union_l //.
Qed.

(** ... so the write arm's cache update is exactly a log append. *)
Lemma flat_store img log (pa : Arch.pa) (n : N) {w : N} (v : bv w) h :
  flat img (log ++ [PWMsg (write_bytes ∅ pa n v) h])
  = write_bytes (flat img log) pa n v.
Proof. by rewrite flat_snoc (write_bytes_union (flat img log)). Qed.

(* ------------------------------------------------------------------ *)
(** ** Sanity theorems (ports of TsoMem.v's, payload-agnostic) *)

Lemma read_down_S img log h tv a t :
  read_down img log h tv a (S t) =
  match (if visibleb h tv log (S t) then log_byte img log (S t) a else None)
  with
  | Some v => Some v
  | None => read_down img log h tv a t
  end.
Proof. done. Qed.

Lemma read_down_0 img log h tv a :
  read_down img log h tv a 0 = img !! a.
Proof.
  cbn [read_down].
  have -> : visibleb h tv log 0 = true by (apply visibleb_below; lia).
  rewrite {1}/log_byte. by destruct (img !! a).
Qed.

Lemma read_down_le img log h tv a t :
  ∀ v, read_down img log h tv a t = Some v →
  ∃ t', (t' ≤ t)%nat ∧ visibleb h tv log t' = true ∧
        log_byte img log t' a = Some v.
Proof.
  induction t as [|t IH] => v.
  - rewrite read_down_0 => Hi. exists 0%nat.
    split_and!; [lia| by (apply visibleb_below; lia) | exact Hi].
  - rewrite read_down_S.
    destruct (visibleb h tv log (S t)) eqn:Hv.
    + destruct (log_byte img log (S t) a) eqn:Hb.
      * move => [<-]. exists (S t). by split_and!.
      * move => /IH [t' [? [? ?]]]. exists t'. split_and!; [lia|done|done].
    + move => /IH [t' [? [? ?]]]. exists t'. split_and!; [lia|done|done].
Qed.

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
    + rewrite read_down_0. move: Hb. rewrite /log_byte //.
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

(* TOTALITY: a read of an IMAGE-COVERED address always answers.  [read_down]
   scans down and bottoms out at timestamp 0, which is visible at every view
   ([visibleb_below]) and is the era image.  This is what the "no evidence"
   leaves need -- they conclude nothing about the VALUE but still owe a read
   RESULT at every reachable view (tso-machine-flip.md A6.74 §(3)'s third
   kit item).  The image-coverage premise is supplied by [win_ok1]'s
   conjunct (2) for a windowed cell. *)
Lemma read_down_total img log h tv a b k :
  img !! a = Some b -> exists c, read_down img log h tv a k = Some c.
Proof.
  move => Hi. elim: k => [|k [c IH]].
  - rewrite read_down_0 Hi. by exists b.
  - rewrite read_down_S.
    case: (if visibleb h tv log (S k) then log_byte img log (S k) a else None)
      => [d|]; [ by exists d | by exists c ].
Qed.

Lemma tso_read_total img log h tv a b :
  img !! a = Some b -> exists c, tso_read img log h tv a = Some c.
Proof. move => Hi. rewrite /tso_read. exact (read_down_total _ _ _ _ _ b _ Hi). Qed.

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
    reads its own byte at EVERY view. *)
Lemma tso_read_own_top img log h a m v :
  pm_tid m = h → msg_byte m a = Some v →
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

(** THE SC COLLAPSE: at the top view, [tso_read] IS the flat cache —
    the equation the exclusive/ifetch/ttw/DMA arms lean on. *)
Lemma tso_read_top_flat img log h a :
  tso_read img log h (length log) a = flat img log !! a.
Proof.
  induction log as [|m log IH] using rev_ind.
  - by rewrite /tso_read [length _]/= read_down_0 /flat /=.
  - rewrite /tso_read flat_snoc.
    have -> : length (log ++ [m]) = S (length log).
    { rewrite length_app /=. lia. }
    have Hlk : (log ++ [m]) !! length log = Some m.
    { by apply list_lookup_middle. }
    rewrite read_down_S.
    have -> : visibleb h (S (length log)) (log ++ [m]) (S (length log)) = true
      by apply visibleb_below; lia.
    rewrite {1}/log_byte /= Hlk.
    destruct (msg_byte m a) eqn:Hb; rewrite /msg_byte in Hb.
    + by rewrite /= (lookup_union_Some_l _ _ _ _ Hb).
    + rewrite /= (lookup_union_r _ _ _ Hb).
      rewrite (read_down_app_below img log m h (length log) (S (length log))
                 a (length log)); [lia|lia|lia|].
      by rewrite -IH /tso_read.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE SOLO ERA: a log with a single author

    The SC collapse above is the collapse AT THE TOP VIEW.  There is a
    second, orthogonal one, and it is what makes the solo-block bracket
    ([HartBlock.v], tso-machine-flip.md RULING 3) true at TSO: when the
    log holds NOTHING BUT [h]'s own messages, the own-author arm of
    [visibleb] fires at every timestamp, so [h] sees the whole log at
    EVERY view and its plain loads read the flat cache no matter where
    the view happens to sit.  "My store buffer is the only one" — the
    boot era before the other harts are released, and the
    device-conformance tester's single-agent runs.

    This is exactly the premise the bracket's plain-load arm needs to
    fold back into [run]'s [s.(mem)] read; the FLAT TIE ([s.(mem)] =
    [flat img log], the [RiscvLang.mm_ok] conjunct) supplies the other
    half.  Note that the collapse is UNCONDITIONAL in [tv]: no
    view-position side condition, which is what keeps the bracket from
    having to thread a view through the block. *)

Definition all_own (h : agent) (log : list pwmsg) : Prop :=
  ∀ m, m ∈ log → pm_tid m = h.

Lemma all_own_nil h : all_own h [].
Proof. move => m. by rewrite elem_of_nil. Qed.

(** The era invariant is INDUCTIVE over the write arm: a hart's own
    store appends its own message. *)
Lemma all_own_app h log m :
  all_own h log → pm_tid m = h → all_own h (log ++ [m]).
Proof.
  move => Hl Hm m0 /elem_of_app [Hin|Hin]; first by apply Hl.
  by apply elem_of_list_singleton in Hin as ->.
Qed.

(** Every in-range timestamp is visible to the sole author, at any view. *)
Lemma all_own_visible h tv log t :
  all_own h log → (t ≤ length log)%nat → visibleb h tv log t = true.
Proof.
  move => Hown Ht. destruct t as [|i]; first by apply visibleb_below; lia.
  destruct (log !! i) as [m|] eqn:Hlk.
  - eapply visibleb_own; [exact Hlk|].
    apply Hown. by eapply elem_of_list_lookup_2.
  - exfalso. apply lookup_ge_None_1 in Hlk. simpl in Ht. lia.
Qed.

(** [read_down] only ever consults [visibleb] at timestamps it scans, so
    two views that agree "visible" over the whole scan read alike. *)
Lemma read_down_vis_irrel img log h tv tv' a n :
  (∀ t, (t ≤ n)%nat → visibleb h tv log t = true) →
  (∀ t, (t ≤ n)%nat → visibleb h tv' log t = true) →
  read_down img log h tv a n = read_down img log h tv' a n.
Proof.
  induction n as [|n IH] => Hv Hv'.
  - by rewrite !read_down_0.
  - rewrite !read_down_S (Hv (S n) ltac:(lia)) (Hv' (S n) ltac:(lia)).
    cbn beta iota.
    destruct (log_byte img log (S n) a); first done.
    apply IH; move => t Ht; [apply Hv|apply Hv']; lia.
Qed.

(** THE SOLO COLLAPSE: the sole author of the log reads the flat cache
    at EVERY view.  (Contrast [tso_read_top_flat], which is any agent at
    the top view.) *)
Lemma tso_read_all_own img log h tv a :
  all_own h log → tso_read img log h tv a = flat img log !! a.
Proof.
  move => Hown. rewrite -(tso_read_top_flat img log h a) /tso_read.
  apply read_down_vis_irrel; move => t Ht; by apply all_own_visible.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The latest-write layer (port of TsoCtxTwin.v's pure layer) *)

(** Timestamp [t] holds a's latest write, with value [v]. *)
Definition latest (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (t : nat) (v : bv 8) : Prop :=
  log_byte img log t a = Some v ∧
  ∀ t', (t < t')%nat → log_byte img log t' a = None.

Lemma log_byte_some_le img log t a v :
  log_byte img log t a = Some v → (t ≤ length log)%nat.
Proof.
  destruct t as [|i]; first by move => _; lia.
  rewrite /log_byte. destruct (log !! i) as [m|] eqn:Hlk; last done.
  move => _. apply lookup_lt_Some in Hlk. lia.
Qed.

Lemma log_byte_app_le img log m t a :
  (t ≤ length log)%nat →
  log_byte img (log ++ [m]) t a = log_byte img log t a.
Proof.
  destruct t as [|i] => Ht //.
  have Hlk : (log ++ [m]) !! i = log !! i by apply lookup_app_l; lia.
  by rewrite /log_byte Hlk.
Qed.

Lemma log_byte_top img log m a :
  log_byte img (log ++ [m]) (S (length log)) a = msg_byte m a.
Proof.
  rewrite /log_byte /=.
  have -> : (log ++ [m]) !! length log = Some m by apply list_lookup_middle.
  done.
Qed.

Lemma log_byte_beyond img log t a :
  (length log < t)%nat → log_byte img log t a = None.
Proof.
  destruct t as [|i] => Ht; first lia.
  rewrite /log_byte /=.
  have -> : log !! i = None by apply lookup_ge_None_2; lia.
  done.
Qed.

(** A fresh append is the latest write of everything in its footprint … *)
Lemma latest_app_new img log m a v :
  msg_byte m a = Some v →
  latest img (log ++ [m]) a (S (length log)) v.
Proof.
  move => Hb. split.
  - rewrite log_byte_top //.
  - move => t' Ht'. apply log_byte_beyond. rewrite length_app /=. lia.
Qed.

(** … and frames everything outside it. *)
Lemma latest_app_frame img log m a t v :
  msg_byte m a = None → latest img log a t v →
  latest img (log ++ [m]) a t v.
Proof.
  move => Hm [Hb Hab]. split.
  - rewrite log_byte_app_le //. by eapply log_byte_some_le.
  - move => t' Ht'.
    destruct (decide (t' ≤ length log)%nat) as [Hle|Hgt].
    + rewrite log_byte_app_le //. by apply Hab.
    + destruct (decide (t' = S (length log))) as [->|Hne].
      * rewrite log_byte_top //.
      * apply log_byte_beyond. rewrite length_app /=. lia.
Qed.

(** THE BRIDGE: a visible latest write determines the machine's read. *)
Lemma tso_read_of_latest img log h tv a t v :
  latest img log a t v → visibleb h tv log t = true →
  tso_read img log h tv a = Some v.
Proof.
  move => [Hb Hab] Hvis.
  have Hle : (t ≤ length log)%nat by eapply log_byte_some_le.
  destruct (read_down_latest img log h tv a (length log) t v Hle Hvis Hb)
    as (t'' & v'' & Ht'' & Hr & Hvis'' & Hb'').
  rewrite /tso_read Hr.
  destruct (decide (t'' = t)) as [->|Hne]; first congruence.
  exfalso.
  have HN : log_byte img log t'' a = None by apply Hab; lia.
  congruence.
Qed.

(** The flat cache and [latest] name the same thing, both directions —
    the era-interp tie between the timestamp ghost and [gen_heap]. *)
Lemma latest_flat img log a t v :
  latest img log a t v → flat img log !! a = Some v.
Proof.
  move => [Hb Hab].
  have Hle : (t ≤ length log)%nat by eapply log_byte_some_le.
  move: t Hle Hb Hab.
  induction log as [|m log IH] using rev_ind => t Hle Hb Hab.
  - destruct t as [|i]; last by simpl in Hle; lia.
    move: Hb. rewrite /flat /= /log_byte //.
  - rewrite flat_snoc lookup_union.
    destruct (decide (t = S (length log))) as [->|Hne].
    + move: Hb. rewrite log_byte_top /msg_byte => ->. by rewrite union_Some_l.
    + rewrite length_app /= in Hle.
      have Hle' : (t ≤ length log)%nat by lia.
      have Hb' : log_byte img log t a = Some v.
      { rewrite -(log_byte_app_le img log m) //. }
      have Hab' : ∀ t', (t < t')%nat → log_byte img log t' a = None.
      { move => t' Ht'.
        destruct (decide (t' ≤ length log)%nat) as [Hle''|Hgt].
        - rewrite -(log_byte_app_le img log m) //. by apply Hab.
        - apply log_byte_beyond. lia. }
      have Hm : msg_byte m a = None.
      { have := Hab (S (length log)) ltac:(lia).
        rewrite log_byte_top //. }
      rewrite /msg_byte in Hm. rewrite Hm union_None_l.
      by apply (IH t Hle' Hb' Hab').
Qed.

Lemma flat_latest img log a v :
  flat img log !! a = Some v → ∃ t, latest img log a t v.
Proof.
  induction log as [|m log IH] using rev_ind.
  - rewrite /flat /= => Hb. exists 0%nat. split.
    + rewrite /log_byte //.
    + move => t' Ht'. apply log_byte_beyond. simpl. lia.
  - rewrite flat_snoc lookup_union.
    destruct (msg_byte m a) eqn:Hm; rewrite /msg_byte in Hm; rewrite Hm.
    + rewrite union_Some_l. move => [<-]. exists (S (length log)).
      apply latest_app_new. rewrite /msg_byte Hm //.
    + rewrite union_None_l. move => Hb. destruct (IH Hb) as [t Hl].
      exists t. apply latest_app_frame; [rewrite /msg_byte Hm //|done].
Qed.

(* ===================================================================== *)
(* §10  THE CANON PIN'S PURE LAYER (tso-pin-memo.md §5, ruling 2).        *)
(*                                                                       *)
(* [pin_ok img log a B Sv] is the DISCHARGE CONCLUSION the kernel-PT walk *)
(* wants, stated where it can be maintained: "from view [B] on, EVERY     *)
(* agent's read of [a] lands in [Sv]".  It is not a history, not a list   *)
(* of messages and not a timestamp comparison -- which is why the walk's  *)
(* final lemma is a one-liner off it and why (i)'s inv-local history      *)
(* big-op (unprovable without the log auth) is not needed.                *)
(*                                                                       *)
(* The three laws are the pin's whole life cycle: MINT (at publication,   *)
(* off the address's latest write -- exactly A6.47's refuted [t ≤ B] tie, *)
(* true as a CREATION obligation and false only as a standing one),       *)
(* PRESERVE (an append whose byte at [a] is in [Sv]), and FRAME (an       *)
(* append that misses [a], free, no premise).                            *)
(* ===================================================================== *)

Definition pin_ok (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (B : nat) (Sv : gset (bv 8)) : Prop :=
  (* [Sv] is [byteset] below; stated at the raw type here because the
     definition PRECEDES the name (the name is §11's, beside [ts_elem]). *)
  forall (h : agent) (tv' : nat), (B <= tv')%nat ->
    exists b, tso_read img log h tv' a = Some b /\ b ∈ Sv.

Lemma pin_ok_mint img log a B Sv t v :
  latest img log a t v -> (t <= B)%nat -> v ∈ Sv -> pin_ok img log a B Sv.
Proof.
  move => Hlat HtB Hv h tv' HB. exists v. split; [|exact Hv].
  apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
  apply visibleb_below. lia.
Qed.

(* the frame law the preservation step needs: [read_down_app_below] asks
   [t ≤ tv], which a reader BELOW the append does not have. *)
Lemma read_down_app_frame img log m h tv a t :
  (t <= length log)%nat ->
  read_down img (log ++ [m]) h tv a t = read_down img log h tv a t.
Proof.
  elim: t => [|t IH] Hlen; first by rewrite !read_down_0.
  rewrite !read_down_S.
  have Hlk : (log ++ [m]) !! t = log !! t by apply lookup_app_l; lia.
  have Hvis : visibleb h tv (log ++ [m]) (S t) = visibleb h tv log (S t)
    by rewrite /visibleb Hlk.
  rewrite Hvis {1}/log_byte /= Hlk.
  case: (visibleb h tv log (S t)) => /=; last by apply IH; lia.
  case: (log !! t) => [m0|]; last by apply IH; lia.
  case: (msg_byte m0 a) => [b|] //. apply IH; lia.
Qed.

Lemma pin_ok_app img log m a B Sv :
  pin_ok img log a B Sv ->
  (msg_byte m a = None \/ exists b, msg_byte m a = Some b /\ b ∈ Sv) ->
  pin_ok img (log ++ [m]) a B Sv.
Proof.
  move => Hpin Hm h tv' HB.
  rewrite /tso_read length_app /= Nat.add_1_r read_down_S.
  rewrite log_byte_top.
  case Hv : (visibleb h tv' (log ++ [m]) (S (length log))) => /=.
  - case: Hm => [-> | [b [-> Hb]]].
    + rewrite read_down_app_frame //.
      have [b [Hr Hb]] := Hpin h tv' HB. by exists b.
    + by exists b.
  - rewrite read_down_app_frame //.
    have [b [Hr Hb]] := Hpin h tv' HB. by exists b.
Qed.

Lemma pin_ok_app_frame img log m a B Sv :
  pin_ok img log a B Sv -> msg_byte m a = None ->
  pin_ok img (log ++ [m]) a B Sv.
Proof. move => Hpin Hm. apply pin_ok_app; [done|by left]. Qed.

(* the pin's bound only ever moves UP with a later reader, so a receipt
   above [B] is as good as one at it. *)
Lemma pin_ok_mono img log a B B' Sv :
  pin_ok img log a B Sv -> (B <= B')%nat -> pin_ok img log a B' Sv.
Proof. move => Hpin Hle h tv' HB'. apply Hpin. lia. Qed.

(* ===================================================================== *)
(* §11  THE TIMESTAMP GHOST'S ELEMENT, AND WHAT THE INTERP TIES IT TO.    *)
(*                                                                       *)
(* NAMED HERE, and not spelled at the two interp sites, for the reason    *)
(* [bytemap] exists (durable-notes' binder trap): [gset (bv 8)] picks its *)
(* [Countable] instance from whatever the ambient file imported, and the  *)
(* two resulting types print identically while refusing to unify.  One    *)
(* name, elaborated once, in the file that owns the pure layer.           *)
(*                                                                       *)
(* ONE conjunct, not two: [ts_ok] bundles the LATEST tie (which every     *)
(* ordinary byte has) with the PIN tie (which only a pinned element has,  *)
(* vacuous at [None]), so the ~20 positional destructurings of the interp *)
(* across [RiscvExec] / [HartLift] / [HartSpan] / [TsoCtx] do not move.   *)
(* ===================================================================== *)

(* NAMED for the binder trap, exactly as [bytemap] is: a file that imports
   [SailStdpp.Values] elaborates [gset (bv 8)] at [Instances.Countable_mword]
   and it will not unify with the stdpp-keyed one, while both print the same.
   Every consumer of the pin -- [TsoGhost], [TsoCtx], [PtTree]'s slot sets --
   spells THIS. *)
Definition byteset : Type := gset (bv 8).

(* [ts_elem] / [ts_ok] THEMSELVES now live at the END of this file (§12c):
   the element's payload grew a WINDOW arm whose claim ([win_ok1]) is stated
   over the racy kit of §12, so the definition has to follow it.  Nothing
   outside this file sees the move -- the names and their argument orders
   are unchanged, and [ts_ok] still BUNDLES (three conjuncts now, the new
   one LAST per durable-notes' rule), so the ~20 positional destructurings
   of the interp do not move. *)

(* the two set SHAPES the pin's consumers need, built HERE so the [gset]
   instance is the one [ts_elem] was elaborated at (the binder trap again:
   a consumer that imports [SailStdpp.Values] would build a different one
   from the same notation). *)
Definition byteset_sing (b : bv 8) : byteset := {[ b ]}.
Definition byteset_of4 (b0 b1 b2 b3 : bv 8) : byteset := {[ b0; b1; b2; b3 ]}.

Lemma elem_of_byteset_sing (b b' : bv 8) : b ∈ byteset_sing b' <-> b = b'.
Proof. rewrite /byteset_sing elem_of_singleton //. Qed.

Lemma byteset_sing_in (b : bv 8) : b ∈ byteset_sing b.
Proof. by apply elem_of_byteset_sing. Qed.

Lemma elem_of_byteset_of4 (b b0 b1 b2 b3 : bv 8) :
  b ∈ byteset_of4 b0 b1 b2 b3 <-> (b = b0 \/ b = b1 \/ b = b2 \/ b = b3).
Proof.
  rewrite /byteset_of4 !elem_of_union !elem_of_singleton. tauto.
Qed.

(* ===================================================================== *)
(* §12  THE RACY-READ KIT (tso-m4-memo.md §3/§8, both probes ported       *)
(* VERBATIM).                                                            *)
(*                                                                       *)
(* WHAT IT IS FOR: the ONE plain load in the tree that has no receipt and *)
(* no synchronisation and still has to conclude something -- [holding()]'s*)
(* [ld a5,16(a0)] of [lk->cpu] by a hart that does NOT hold the lock      *)
(* ([WpSconfLock.wp_cld_lkcpu_lockopen_notheld_s_sconf], the leaf that    *)
(* makes acquire's [if(holding(lk)) panic] arm DEAD CODE).  It must       *)
(* conclude "the word I read is not MY [struct cpu]" -- an EXCLUSION, and *)
(* the pin of §10 cannot deliver it: [pin_ok] gives value-IN-SET,         *)
(* [cpus_ptr cpu_id] is in that set, and no per-agent generalisation of   *)
(* [pin_ok] can help (an append's top-view maintenance obligation is      *)
(* [∀ h, P h b], i.e. every store's value must be allowed for EVERY       *)
(* reader, which is exactly the exclusion's negation).                    *)
(*                                                                       *)
(* THE EXCLUSION IS NOT A PROPERTY OF THE VALUE, IT IS A PROPERTY OF THE  *)
(* READER'S OWN WRITE HISTORY, and it is true only because [read_down]    *)
(* scans DOWN from the top and [visibleb_own] makes a hart's own message  *)
(* visible at every view.  Two facts carry it, both O(1) per address and  *)
(* both maintainable per store:                                          *)
(*                                                                       *)
(*   [own_last]    h's own latest write to [a] is at timestamp [t]        *)
(*   [writer_pin]  every message writing [a] writes a value allowed for   *)
(*                 ITS AUTHOR                                            *)
(*                                                                       *)
(* AND THE KIT MUST BE WINDOW-SHAPED, NOT BYTE-SHAPED -- this is the      *)
(* memo's decisive measurement and the reason [tso-pin-memo.md] §2's      *)
(* "byte-keyed is as strong as window-keyed" is TRUE for the PTE and      *)
(* FALSE here.  The eight [cpus_ptr] values (base 0x800123e8, stride 128) *)
(* differ only in bytes 0 and 1:                                         *)
(*                                                                       *)
(*     byte 0 ∈ {0xe8, 0x68}   byte 1 ∈ {0x23,0x24,0x25,0x26,0x27}       *)
(*     distinguishing single offset: hart 0 -> [1], harts 1..6 -> NONE,  *)
(*     hart 7 -> [1]                                                     *)
(*                                                                       *)
(* so for harts 1..6 no single byte separates a hart from all the others, *)
(* and a byte-keyed writer-pin would license a FORGERY: hart 1 assembles  *)
(* 0x80012468 from hart 3's byte 0 (0x68) and hart 2's byte 1 (0x24),     *)
(* both legal writes by their own authors.  [win_ok] -- every timestamp   *)
(* writes the WHOLE window or none of it -- is what closes that gap, and  *)
(* [racy_read_window] is the proof that one timestamp then resolves every *)
(* byte of the read.                                                     *)
(*                                                                       *)
(* All three facts are COVERAGE CLAIMS OVER THE LOG, so [tso-pin-memo.md] *)
(* §3's refutation applies verbatim: they cannot live in an invariant,    *)
(* they live in the interp -- in the [ts_elem] payload beside the pin.    *)
(* ===================================================================== *)

Section racy.

  (* h's own latest write to [a] is at timestamp [t] (t = 0: never wrote). *)
  Definition own_last (log : list pwmsg) (h : agent) (a : Arch.pa) (t : nat)
    : Prop :=
    forall i m, log !! i = Some m -> pm_tid m = h ->
      is_Some (msg_byte m a) -> (S i <= t)%nat.

  (* every message writing [a] writes a value ALLOWED FOR ITS AUTHOR *)
  Definition writer_pin (log : list pwmsg) (a : Arch.pa)
      (Sf : agent -> bv 8 -> Prop) : Prop :=
    forall i m c, log !! i = Some m -> msg_byte m a = Some c ->
      Sf (pm_tid m) c.

  (* ---- MAINTENANCE: both facts are inductive over the append ---- *)

  Lemma own_last_app_other log m h a t :
    own_last log h a t -> pm_tid m <> h -> own_last (log ++ [m]) h a t.
  Proof.
    move => Ho Hne i m0 Hlk Htid Hs.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge Hlk]].
    - exact (Ho i m0 Hlk Htid Hs).
    - destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk;
        [ injection Hlk as <-; congruence | done ].
  Qed.

  (* the general frame: an append that is not h's OWN WRITE TO [a] is free.
     ITS SIDE CONDITION IS ALREADY A PARAMETER OF EVERY STORE GATE -- the
     author [auth] is one of [ledger_store_ok]'s arguments. *)
  Lemma own_last_app_frame log m h a t :
    own_last log h a t ->
    (pm_tid m = h -> msg_byte m a = None) ->
    own_last (log ++ [m]) h a t.
  Proof.
    move => Ho Hfr i m0 Hlk Htid Hs.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge Hlk]].
    - exact (Ho i m0 Hlk Htid Hs).
    - destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk; last done.
      injection Hlk as <-. rewrite /is_Some (Hfr Htid) in Hs.
      by destruct Hs as [? ?].
  Qed.

  (* h's OWN store: free, and it lands at the TOP *)
  Lemma own_last_app_self log m h a :
    pm_tid m = h -> own_last log h a (S (length log)) ->
    own_last (log ++ [m]) h a (S (length log)).
  Proof.
    move => Htid Ho i m0 Hlk Htid0 Hs.
    apply lookup_lt_Some in Hlk. rewrite length_app /= in Hlk. lia.
  Qed.

  Lemma writer_pin_app log m a Sf :
    writer_pin log a Sf ->
    (forall c, msg_byte m a = Some c -> Sf (pm_tid m) c) ->
    writer_pin (log ++ [m]) a Sf.
  Proof.
    move => Hw Hm i m0 c Hlk Hb.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge Hlk]].
    - exact (Hw i m0 c Hlk Hb).
    - destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk;
        [ injection Hlk as <-; by apply Hm | done ].
  Qed.

  (* ---- THE READ THEOREM: no receipt, no view premise, any [tv] ---- *)

  Lemma racy_read_split (img : gmap Arch.pa (bv 8)) (log : list pwmsg) (h : agent)
      (a : Arch.pa) (tv t : nat) (v b : bv 8) (Sf : agent -> bv 8 -> Prop) :
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    log_byte img log t a = Some v ->
    own_last log h a t ->
    writer_pin log a Sf ->
    tso_read img log h tv a = Some b ->
    b = v \/ exists h', h' <> h /\ Sf h' b.
  Proof.
    move => Hlen Hvis Hb Ho Hw Hrd.
    destruct (read_down_latest img log h tv a (length log) t v Hlen Hvis Hb)
      as (t'' & v'' & Hle & Hrd'' & Hvis'' & Hb'').
    rewrite /tso_read Hrd'' in Hrd. injection Hrd as <-.
    destruct (decide (t'' = t)) as [->|Hne].
    { left. rewrite Hb'' in Hb. by injection Hb as <-. }
    right.
    (* t'' > t, so it is a real message, and it is NOT h's *)
    destruct t'' as [|i]; first lia.
    rewrite /log_byte in Hb''.
    destruct (log !! i) as [m|] eqn:Hlk; last done.
    exists (pm_tid m). split.
    - move => Htid. have := Ho i m Hlk Htid ltac:(by eexists). lia.
    - exact (Hw i m _ Hlk Hb'').
  Qed.

  (* ---- THE PER-BYTE CONSUMER SHAPE: "the recorded owner is not me".
     Kept because it is the honest statement of what ONE byte can say, and
     because the window theorem below is measured AGAINST it: this is the
     form that the [cpus_ptr] layout defeats for harts 1..6. ---- *)
  Lemma racy_read_not_mine (img : gmap Arch.pa (bv 8)) (log : list pwmsg) (h : agent)
      (a : Arch.pa) (tv t : nat) (b z : bv 8) (cp : agent -> bv 8) :
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    log_byte img log t a = Some z ->              (* my own last write was the CLEAR *)
    own_last log h a t ->
    writer_pin log a (fun j c => c = z \/ c = cp j) ->
    z <> cp h ->
    (forall j, j <> h -> cp j <> cp h) ->         (* cp injective at h *)
    tso_read img log h tv a = Some b ->
    b <> cp h.
  Proof.
    move => Hlen Hvis Hb Ho Hw Hz Hinj Hrd.
    destruct (racy_read_split img log h a tv t z b _ Hlen Hvis Hb Ho Hw Hrd)
      as [-> | (h' & Hne & [-> | ->])]; [ done | done | ].
    exact (Hinj h' Hne).
  Qed.

  (* ---- AND THE FREE HALF: the OWN-WRITE read needs no receipt at all.
     [visibleb_own] makes the author's own message visible at EVERY view,
     so the holder's read of the cell it itself wrote is exact.  This is
     the pure form of what [TsoCtx.ledger_read_vis_ok] already does in
     Iris -- recorded here because it is what makes the memo's ruling 2
     ("only [notheld] gets new kit") true. ---- *)
  Lemma racy_read_own (img : gmap Arch.pa (bv 8)) (log : list pwmsg) (h : agent)
      (a : Arch.pa) (tv i : nat) (m : pwmsg) (v b : bv 8) :
    log !! i = Some m -> pm_tid m = h -> msg_byte m a = Some v ->
    own_last log h a (S i) ->
    tso_read img log h tv a = Some b ->
    b = v \/ exists j m', (S i <= j)%nat /\ log !! j = Some m' /\
                          pm_tid m' <> h /\ msg_byte m' a = Some b.
  Proof.
    move => Hlk Htid Hb Ho Hrd.
    have Hlen : (S i <= length log)%nat by (apply lookup_lt_Some in Hlk; lia).
    have Hvis : visibleb h tv log (S i) = true
      by apply (visibleb_own _ _ _ _ _ Hlk Htid).
    have Hlb : log_byte img log (S i) a = Some v
      by rewrite /log_byte Hlk.
    destruct (read_down_latest img log h tv a (length log) (S i) v Hlen Hvis Hlb)
      as (t'' & v'' & Hle & Hrd'' & Hvis'' & Hb'').
    rewrite /tso_read Hrd'' in Hrd. injection Hrd as <-.
    destruct (decide (t'' = S i)) as [->|Hne].
    { left. rewrite Hb'' in Hlb. by injection Hlb as <-. }
    right. destruct t'' as [|j]; first lia.
    rewrite /log_byte in Hb''.
    destruct (log !! j) as [m'|] eqn:Hlk'; last done.
    exists j, m'. split_and!; [ lia | done | | done ].
    move => Htid'. have := Ho j m' Hlk' Htid' ltac:(by eexists). lia.
  Qed.

End racy.

(* ===================================================================== *)
(* §12b  THE WINDOW HALF.  One timestamp resolves every byte, so the      *)
(* forgery the byte-keyed kit allowed is impossible.                      *)
(* ===================================================================== *)

Section window.
  Variable img : gmap Arch.pa (bv 8).
  Variable log : list pwmsg.
  Variable a : Arch.pa.
  Variable n : nat.
  (* the window is non-empty: byte 0 is where the payload hangs and where
     [find_top] computes, so every theorem below needs it *)
  Hypothesis Hn : (0 < n)%nat.

  (* (W1) every timestamp writes the WHOLE window or none of it.  [t = 0]
     (the era image) is included: RAM is covered by the image, so the
     left arm holds there.  MAINTENANCE IS TRIVIAL AT THE LOCK: every
     write to [lk->cpu] is one 8-byte [sd], so the appended message writes
     all eight bytes -- a per-store side condition of exactly the pin's
     shape ([vnew ∈ Sv]). *)
  Definition win_ok : Prop :=
    forall t : nat,
      (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j)))
      \/ (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = None).

  (* the timestamp [read_down] settles on, computed at BYTE 0 *)
  Fixpoint find_top (h : agent) (tv : nat) (t : nat) : option nat :=
    match (if visibleb h tv log t then log_byte img log t (pa_add a 0) else None) with
    | Some _ => Some t
    | None => match t with O => None | S t' => find_top h tv t' end
    end.

  Lemma find_top_0 (h : agent) (tv : nat) :
    find_top h tv 0 =
      match (if visibleb h tv log 0 then log_byte img log 0 (pa_add a 0) else None) with
      | Some _ => Some 0%nat | None => None end.
  Proof. reflexivity. Qed.

  Lemma find_top_S (h : agent) (tv t : nat) :
    find_top h tv (S t) =
      match (if visibleb h tv log (S t) then log_byte img log (S t) (pa_add a 0) else None) with
      | Some _ => Some (S t) | None => find_top h tv t end.
  Proof. reflexivity. Qed.

  (* ---- THE REASSEMBLY: one timestamp serves every byte ---- *)
  Lemma read_down_win (h : agent) (tv t : nat) (j : nat) :
    win_ok -> (j < n)%nat ->
    read_down img log h tv (pa_add a j) t
    = match find_top h tv t with
      | Some T => log_byte img log T (pa_add a j)
      | None => None
      end.
  Proof.
    move => Hw Hj. elim: t => [|t IH].
    - rewrite read_down_0 find_top_0.
      have Hv : visibleb h tv log 0 = true by (apply visibleb_below; lia).
      rewrite Hv.
      case E0 : (log_byte img log 0 (pa_add a 0)) => [b0|].
      + by rewrite /log_byte.
      + case: (Hw 0%nat) => Hall.
        * have := Hall 0%nat ltac:(lia). rewrite E0. by move => [? ?].
        * have H := Hall j Hj. move: H. rewrite /log_byte. by move => ->.
    - rewrite read_down_S find_top_S.
      case Ev : (visibleb h tv log (S t)); last by rewrite IH.
      case E0 : (log_byte img log (S t) (pa_add a 0)) => [b0|].
      + case: (Hw (S t)) => Hall.
        * have [bj Hbj] := Hall j Hj. by rewrite Hbj.
        * have := Hall 0%nat ltac:(lia). by rewrite E0.
      + case: (Hw (S t)) => Hall.
        * have := Hall 0%nat ltac:(lia). rewrite E0. by move => [? ?].
        * have := Hall j Hj => ->. by rewrite IH.
  Qed.

  (* find_top lands on a visible, window-writing timestamp *)
  Lemma find_top_spec (h : agent) (tv t T : nat) :
    find_top h tv t = Some T ->
    (T <= t)%nat /\ visibleb h tv log T = true
    /\ is_Some (log_byte img log T (pa_add a 0)).
  Proof.
    elim: t => [|t IH].
    - rewrite find_top_0.
      case Ev : (visibleb h tv log 0); last by [].
      case E0 : (log_byte img log 0 (pa_add a 0)) => [b0|]; last by [].
      move => [<-]. split_and!; [lia|done|by eexists].
    - rewrite find_top_S.
      case Ev : (visibleb h tv log (S t)).
      + case E0 : (log_byte img log (S t) (pa_add a 0)) => [b0|].
        * move => [<-]. split_and!; [lia|done|by eexists].
        * move => /IH [? [? ?]]. split_and!; [lia|done|done].
      + move => /IH [? [? ?]]. split_and!; [lia|done|done].
  Qed.

  (* find_top is MAXIMAL: nothing visible and window-writing sits above it *)
  Lemma find_top_max (h : agent) (tv t t' : nat) :
    (t' <= t)%nat -> visibleb h tv log t' = true ->
    is_Some (log_byte img log t' (pa_add a 0)) ->
    exists T, find_top h tv t = Some T /\ (t' <= T)%nat.
  Proof.
    elim: t => [|t IH] Hle Hv [b Hb].
    - have Ht0 : t' = 0%nat by lia.
      rewrite find_top_0. move: Hb Hv. rewrite Ht0 => -> ->.
      exists 0%nat. split; [done|lia].
    - rewrite find_top_S.
      case Ev : (visibleb h tv log (S t)).
      + case E0 : (log_byte img log (S t) (pa_add a 0)) => [b0|].
        * exists (S t). split; [done|lia].
        * have Hne : t' <> S t.
          { move => Heq. move: Hb. rewrite Heq E0. discriminate. }
          have [T [HT ?]] := IH ltac:(lia) Hv ltac:(by eexists).
          exists T. rewrite HT. split; [done|lia].
      + have Hne : t' <> S t.
        { move => Heq. move: Hv. rewrite Heq Ev. discriminate. }
        have [T [HT ?]] := IH ltac:(lia) Hv ltac:(by eexists).
        exists T. rewrite HT. split; [done|lia].
  Qed.

  (* ==================================================================
     THE THEOREM.  One index [T] resolves the whole window, and it is
     either the reader's own last write or a message by someone else.
     ================================================================== *)
  Lemma racy_read_window (h : agent) (tv t : nat) :
    win_ok ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j))) ->
    (forall j, (j < n)%nat -> own_last log h (pa_add a j) t) ->
    exists T : nat,
      (t <= T)%nat
      /\ (forall j, (j < n)%nat ->
            tso_read img log h tv (pa_add a j) = log_byte img log T (pa_add a j))
      /\ (T = t \/ exists i m, T = S i /\ log !! i = Some m /\ pm_tid m <> h
                            /\ is_Some (msg_byte m (pa_add a 0))).
  Proof.
    move => Hw Hlen Hvis Hsome Ho.
    have [T [HT Hge]] := find_top_max h tv (length log) t Hlen Hvis (Hsome 0%nat ltac:(lia)).
    exists T. split; first done.
    split.
    { move => j Hj. rewrite /tso_read (read_down_win h tv (length log) j Hw Hj) HT //. }
    case: (decide (T = t)) => [->|Hne]; first by left.
    right.
    have [Hle [Hv [b0 Hb0]]] := find_top_spec h tv (length log) T HT.
    case ET : T => [|i]; first lia.
    move: Hb0. rewrite ET /log_byte.
    case El : (log !! i) => [m|]; last by [].
    move => Hb0. exists i, m. split_and!; [done|done| |by eexists].
    move => Htid.
    have := Ho 0%nat ltac:(lia) i m El Htid ltac:(by eexists).
    lia.
  Qed.

  (* ==================================================================
     THE CONSUMER SHAPE: the WINDOW-keyed writer pin, and the forgery
     the byte-keyed one allowed is now impossible.
     ================================================================== *)

  (* every message that touches the window writes a word allowed for ITS
     AUTHOR -- stated on the message's byte FUNCTION, so no [bv] width
     arithmetic is needed here and the whole layer stays free of
     [bv (8*n)] dependent types. *)
  Definition wpin (Wf : agent -> (nat -> option (bv 8)) -> Prop) : Prop :=
    forall i m, log !! i = Some m ->
      is_Some (msg_byte m (pa_add a 0)) ->
      Wf (pm_tid m) (fun j => msg_byte m (pa_add a j)).

  Lemma racy_read_window_pin (h : agent) (tv t : nat)
      (Wf : agent -> (nat -> option (bv 8)) -> Prop) :
    win_ok -> wpin Wf ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j))) ->
    (forall j, (j < n)%nat -> own_last log h (pa_add a j) t) ->
    (forall j, (j < n)%nat ->
       tso_read img log h tv (pa_add a j) = log_byte img log t (pa_add a j))
    \/ (exists (h' : agent) (m : pwmsg),
          h' <> h /\ pm_tid m = h'
          /\ Wf h' (fun j => msg_byte m (pa_add a j))
          /\ forall j, (j < n)%nat ->
               tso_read img log h tv (pa_add a j) = msg_byte m (pa_add a j)).
  Proof.
    move => Hw Hp Hlen Hvis Hsome Ho.
    have [T [Hge [Hrd Harm]]] := racy_read_window h tv t Hw Hlen Hvis Hsome Ho.
    destruct Harm as [->|(i & m & Heq & El & Htid & Hb0)]; first by left.
    subst T. right. exists (pm_tid m), m. split_and!.
    - by move => ?; apply Htid.
    - done.
    - exact (Hp i m El Hb0).
    - move => j Hj. rewrite (Hrd j Hj) /log_byte El //.
  Qed.

  (* ------------------------------------------------------------------
     THE LOCK'S INSTANCE.  Every writer stores either the CLEAR word [z]
     or its OWN word [cp j]; the reader's own last write was the clear.
     Conclusion: the read CANNOT be [cp h] -- [holding()]'s answer.

     NOTE THE TWO FINAL PREMISES, because they are the whole content of
     the byte-vs-window ruling: each asks for a distinguishing offset
     PER OTHER HART ([cp h' <> cp h] at SOME k, i.e. injectivity of the
     WORD) -- not for one offset that separates [h] from all harts at
     once, which the measured [cpus_ptr] layout does NOT provide for
     harts 1..6.  Both premises are WORD-level and both are true
     ([ProcGeom.cpus_ptr_inj] and [cpus_ptr_nonzero]).
     ------------------------------------------------------------------ *)
  Lemma lkcpu_not_mine (h : agent) (tv t : nat)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8) :
    win_ok ->
    wpin (fun j f => (forall k, (k < n)%nat -> f k = Some (z k))
                  \/ (forall k, (k < n)%nat -> f k = Some (cp j k))) ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = Some (z j)) ->
    (forall j, (j < n)%nat -> own_last log h (pa_add a j) t) ->
    (exists k, (k < n)%nat /\ z k <> cp h k) ->
    (forall h', h' <> h -> exists k, (k < n)%nat /\ cp h' k <> cp h k) ->
    exists k, (k < n)%nat /\ tso_read img log h tv (pa_add a k) <> Some (cp h k).
  Proof.
    move => Hw Hp Hlen Hvis Hz Ho [k0 [Hk0 Hzk]] Hinj.
    have Hsome : forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j))
      by move => j Hj; rewrite (Hz j Hj); by eexists.
    destruct (racy_read_window_pin h tv t _ Hw Hp Hlen Hvis Hsome Ho)
      as [Hown | (h' & m & Hne & Htid & HW & Hrd)].
    - exists k0. split; first done.
      rewrite (Hown k0 Hk0) (Hz k0 Hk0). move => [Heq]. exact (Hzk Heq).
    - case: HW => [Hcl | Hme].
      + exists k0. split; first done.
        rewrite (Hrd k0 Hk0) (Hcl k0 Hk0). move => [Heq]. exact (Hzk Heq).
      + have [k [Hk Hd]] := Hinj h' Hne.
        exists k. split; first done.
        rewrite (Hrd k Hk) (Hme k Hk). move => [Heq]. exact (Hd Heq).
  Qed.

End window.

(* ===================================================================== *)
(* §12c  THE WINDOW PAYLOAD, PER BYTE -- AND WHY IT IS NOT ON BYTE 0.      *)
(*                                                                       *)
(* [tso-m4-memo.md] ruling 3 puts all three coverage claims "in ONE        *)
(* [ts_elem] option payload on BYTE 0", and §8 adds that [win_ok]'s        *)
(* maintenance "is a per-store side condition of the same shape as the     *)
(* pin's".  THE FIRST HALF IS RIGHT ABOUT THE GHOST MAP AND WRONG ABOUT    *)
(* THE BYTE, AND THE SECOND HALF IS FALSE -- and the two are the same      *)
(* fact.  (Owner-ratified amendment to ruling 3, 2026-08-27;               *)
(* tso-machine-flip.md A6.74 §(2) is the full argument.)                   *)
(*                                                                       *)
(* [win_ok] says every timestamp writes the WHOLE window or none of it.    *)
(* Hang it on byte 0 and its FRAME arm -- the arm every store in the tree  *)
(* that is not the lock's must take -- needs "the appended message does    *)
(* not write SOME of [a .. a+n-1] while missing byte 0", a fact about a    *)
(* SET of addresses.  The pin's frame arm is free because                  *)
(* [pin_ok_app_frame]'s side condition is [msg_byte m a = None], i.e.      *)
(* [a ∉ dom Pnew], which the store gate knows PER ADDRESS.  It does not    *)
(* know disjointness from a window whose extent lives inside the interp's  *)
(* existential map, and no caller can state it: the window's addresses are *)
(* not visible from the store site.  Carried honestly it becomes a premise *)
(* on [ledger_store_ok] -- i.e. on every store in the tree.                *)
(*                                                                       *)
(* THE FIX PUTS THE PAYLOAD ON EVERY BYTE OF THE WINDOW and states the     *)
(* writer-pin AT THAT BYTE but ABOUT the window.  Then the frame           *)
(* condition is [msg_byte m a = None] again -- exactly the pin's -- and    *)
(* [win_ok] / [wpin] stop being interp conjuncts and become the ASSEMBLY   *)
(* the READER runs over the [n] copies it already holds ([phys_ledger_word] *)
(* is eight [phys_ledger]s).  Same ghost surface, no second map.           *)
(*                                                                       *)
(* THE GENERAL RULE: a coverage claim's home is decided by its FRAME       *)
(* condition, not by its content.  [tso-pin-memo.md] §3 said such a claim  *)
(* belongs in the interp rather than an invariant; this says WHERE in the  *)
(* interp -- at the finest key whose frame arm the store gate can already  *)
(* discharge.  A claim about [n] addresses parked on one of them is a      *)
(* claim no framing store can pay.                                        *)
(* ===================================================================== *)

Record ts_win : Type := TsWin {
  tw_base : Arch.pa;               (* byte 0 of the window *)
  tw_n    : nat;                   (* its width *)
  tw_j    : nat;                   (* THIS byte's offset inside it *)
  tw_z    : nat -> bv 8;           (* the CLEAR word, byte-wise *)
  tw_cp   : agent -> nat -> bv 8;  (* each author's own word, byte-wise *)
  tw_own  : agent -> option nat;   (* per-agent own-last index into the log *)
}.

(* the per-BYTE claim.  Every conjunct's frame arm is [msg_byte m a = None]
   or free. *)
Definition win_ok1 (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (W : ts_win) : Prop :=
  a = pa_add (tw_base W) (tw_j W)
  /\ (tw_j W < tw_n W)%nat
  (* (1) ANY message touching THIS byte writes the WHOLE window, with a word
     allowed for its author.  This is what makes a partial write impossible
     and therefore what makes [win_ok] a theorem below. *)
  /\ (forall i m, log !! i = Some m -> is_Some (msg_byte m a) ->
        (forall k, (k < tw_n W)%nat ->
           msg_byte m (pa_add (tw_base W) k) = Some (tw_z W k))
        \/ (forall k, (k < tw_n W)%nat ->
           msg_byte m (pa_add (tw_base W) k) = Some (tw_cp W (pm_tid m) k)))
  (* (2) the era image covers the window: [win_ok]'s [t = 0] arm.  Free at
     the lock, whose cell is RAM. *)
  /\ (forall k, (k < tw_n W)%nat -> is_Some (img !! pa_add (tw_base W) k))
  (* (3) per agent, AT THIS BYTE: where its own last write to this byte is,
     that it is visible to it at every view, and that it left the CLEAR
     value there. *)
  /\ (forall h t, tw_own W h = Some t ->
        (t <= length log)%nat
        /\ (forall tv, visibleb h tv log t = true)
        /\ log_byte img log t a = Some (tw_z W (tw_j W))
        /\ own_last log h a t).

(* THE FRAME ARM, AND IT IS DEFINITIONAL -- which is the whole point of
   §12c's correction.  An append that misses THIS BYTE preserves the claim,
   with no premise about the rest of the window: conjunct (1)'s premise
   ([is_Some (msg_byte m a)]) is false for the new message, so it says
   nothing about it; (2) is about the image; (3)'s four parts frame by
   [visibleb_app], [log_byte_app_le] and [own_last_app_frame], whose own
   side condition [pm_tid m = h -> msg_byte m a = None] this premise
   implies outright.

   A store that wrote SOME of the window and not this byte would not
   VIOLATE the claim -- it would be a store to a byte whose element is in
   [dom Pnew] and therefore replaced, i.e. it drops the claim rather than
   falsifying it.  And it cannot happen anyway: [ledger_store_ok] demands
   FULL ownership of every byte it writes, so a partial writer would have
   to own a window byte the lock's invariant is holding. *)
Lemma win_ok1_app_frame img log m a W :
  win_ok1 img log a W -> msg_byte m a = None ->
  win_ok1 img (log ++ [m]) a W.
Proof.
  move => [Ha [Hj [H1 [H2 H3]]]] Hm.
  split_and!; [ exact Ha | exact Hj | | exact H2 | ].
  - move => i m0 Hlk Hs.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge Hlk]].
    + exact (H1 i m0 Hlk Hs).
    + destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk; last done.
      injection Hlk as <-. rewrite /is_Some Hm in Hs. by destruct Hs as [? ?].
  - move => h t Hown.
    have [Hlen [Hvis [Hlb Hol]]] := H3 h t Hown.
    split_and!.
    + rewrite length_app /=. lia.
    + move => tv. by apply visibleb_app.
    + by rewrite (log_byte_app_le _ _ _ _ _ Hlen).
    + apply own_last_app_frame; [exact Hol | move => _; exact Hm].
Qed.

(* the appended message sits at index [length log] *)
Lemma lookup_app_r_Some_eq {A} (l : list A) (x : A) :
  (l ++ [x]) !! length l = Some x.
Proof. by rewrite lookup_app_r // Nat.sub_diag. Qed.

(* the top is always an own-last bound: nothing in [log] is at or above
   [S (length log)] *)
Lemma own_last_top log h a : own_last log h a (S (length log)).
Proof. move => i m Hlk _ _. apply lookup_lt_Some in Hlk. lia. Qed.

(* THE STORE ARM.  A message that writes the WHOLE window with an allowed
   word re-establishes the per-byte claim, with the AUTHOR's own-last entry
   moved to the top -- or REVOKED, if what it wrote was its own word rather
   than the clear.  That two-armed premise is the honest content of the
   lock's two stores: release writes the clear (and the author may then read
   "not mine" again), acquire writes [cp auth] (and the author is excluded
   until it releases).  Every OTHER agent's entry is untouched and frames. *)
Lemma win_ok1_app_store img log msg base n j
    (z : nat -> bv 8) (cp : agent -> nat -> bv 8) (own own' : agent -> option nat) :
  win_ok1 img log (pa_add base j) (TsWin base n j z cp own) ->
  ((forall k, (k < n)%nat -> msg_byte msg (pa_add base k) = Some (z k))
     /\ own' (pm_tid msg) = Some (S (length log))
   \/ (forall k, (k < n)%nat -> msg_byte msg (pa_add base k)
                               = Some (cp (pm_tid msg) k))
     /\ own' (pm_tid msg) = None) ->
  (forall h, h <> pm_tid msg -> own' h = own h) ->
  win_ok1 img (log ++ [msg]) (pa_add base j) (TsWin base n j z cp own').
Proof.
  move => [Ha [Hj [H1 [H2 H3]]]] Hnew Hoth.
  have Hlk_top : (log ++ [msg]) !! length log = Some msg
    by (apply lookup_app_r_Some_eq).
  split_and!; [ exact Ha | exact Hj | | exact H2 | ].
  - move => i m Hlk Hs.
    apply lookup_app_Some in Hlk. destruct Hlk as [Hlk | [Hge Hlk]].
    + exact (H1 i m Hlk Hs).
    + destruct (i - length log)%nat as [|k] eqn:Hk; cbn in Hlk; last done.
      injection Hlk as <-. cbn [tw_base tw_n tw_z tw_cp].
      case: Hnew => [[Hcl _] | [Hme _]]; [ by left | by right ].
  - move => h t Hown. cbn [tw_base tw_n tw_j tw_z tw_cp tw_own] in Hown |- *.
    (* NOTE: ssreflect's [->] intro pattern rewrites the GOAL only, and
       [Hown] mentions [h] -- hence the explicit [subst]. *)
    case: (decide (h = pm_tid msg)) => [Heq|Hne]; first subst h.
    + case: Hnew => [[Hcl Ho] | [_ Ho]]; last by rewrite Ho in Hown.
      rewrite Ho in Hown. injection Hown as <-.
      split_and!.
      * rewrite length_app /=. lia.
      * move => tv. exact (visibleb_own _ _ _ _ _ Hlk_top eq_refl).
      * rewrite log_byte_top. exact (Hcl j Hj).
      * apply own_last_app_self; [reflexivity | apply own_last_top].
    + rewrite (Hoth h Hne) in Hown.
      have [Hlen [Hvis [Hlb Hol]]] := H3 h t Hown.
      split_and!.
      * rewrite length_app /=. lia.
      * move => tv. by apply visibleb_app.
      * by rewrite (log_byte_app_le _ _ _ _ _ Hlen).
      * apply own_last_app_frame; [exact Hol | by move => Heq; congruence].
Qed.

(* ---- THE ASSEMBLY: [n] agreeing per-byte copies give the WINDOW facts ---- *)
Section assemble.
  Variable img : gmap Arch.pa (bv 8).
  Variable log : list pwmsg.
  Variable base : Arch.pa.
  Variable n : nat.
  Variable z : nat -> bv 8.
  Variable cp : agent -> nat -> bv 8.
  Variable own : agent -> option nat.
  Hypothesis Hn : (0 < n)%nat.

  Definition win_at (j : nat) : ts_win := TsWin base n j z cp own.

  (* what the READER holds: one copy per byte, all naming the same window *)
  Hypothesis Hcov :
    forall j, (j < n)%nat -> win_ok1 img log (pa_add base j) (win_at j).

  (* a message that touches ANY byte of the window writes ALL of it *)
  Lemma win_msg_all (i : nat) (m : pwmsg) (k : nat) :
    log !! i = Some m -> (k < n)%nat -> is_Some (msg_byte m (pa_add base k)) ->
    (forall j, (j < n)%nat -> msg_byte m (pa_add base j) = Some (z j))
    \/ (forall j, (j < n)%nat -> msg_byte m (pa_add base j) = Some (cp (pm_tid m) j)).
  Proof.
    move => Hlk Hk Hs.
    have [_ [_ [H1 _]]] := Hcov k Hk.
    exact (H1 i m Hlk Hs).
  Qed.

  Lemma win_assemble_win_ok : win_ok img log base n.
  Proof.
    move => t. case: t => [|i].
    - left. move => j Hj.
      have [_ [_ [_ [H2 _]]]] := Hcov 0%nat Hn.
      have := H2 j Hj. by rewrite /log_byte.
    - rewrite /log_byte. case El : (log !! i) => [m|]; last by right.
      case E0 : (msg_byte m (pa_add base 0%nat)) => [b0|].
      + case: (win_msg_all i m 0%nat El Hn ltac:(by rewrite E0)) => Hall;
          left; move => j Hj; rewrite (Hall j Hj); by eexists.
      + right. move => j Hj.
        case Ej : (msg_byte m (pa_add base j)) => [bj|]; last done.
        exfalso.
        case: (win_msg_all i m j El Hj ltac:(by rewrite Ej)) => Hall;
          have := Hall 0%nat Hn; by rewrite E0.
  Qed.

  (* [wpin] mentions neither [img] nor [n] in its body, so the section
     closes it over [log] and [base] only -- the arity is not the same as
     [win_ok]'s and the mismatch reports as a TYPE error on [img]. *)
  Lemma win_assemble_wpin :
    wpin log base
      (fun j f => (forall k, (k < n)%nat -> f k = Some (z k))
               \/ (forall k, (k < n)%nat -> f k = Some (cp j k))).
  Proof.
    move => i m Hlk Hs. exact (win_msg_all i m 0%nat Hlk Hn Hs).
  Qed.

  (* THE READER'S CONCLUSION.  [own h = Some t] is the agent's own-last
     record; the two final premises are WORD-level and both true of the lock
     ([cpus_ptr] injective and never 0). *)
  Lemma win_assemble_not_mine (h : agent) (t tv : nat) :
    own h = Some t ->
    (exists k, (k < n)%nat /\ z k <> cp h k) ->
    (forall h', h' <> h -> exists k, (k < n)%nat /\ cp h' k <> cp h k) ->
    exists k, (k < n)%nat /\ tso_read img log h tv (pa_add base k) <> Some (cp h k).
  Proof.
    move => Hown Hzk Hinj.
    have Hlen : (t <= length log)%nat
      by (have [_ [_ [_ [_ H3]]]] := Hcov 0%nat Hn;
          by have [? _] := H3 h t Hown).
    have Hvis : visibleb h tv log t = true
      by (have [_ [_ [_ [_ H3]]]] := Hcov 0%nat Hn;
          have [_ [Hv _]] := H3 h t Hown; exact (Hv tv)).
    have Hz : forall j, (j < n)%nat ->
                log_byte img log t (pa_add base j) = Some (z j).
    { move => j Hj. have [_ [_ [_ [_ H3]]]] := Hcov j Hj.
      by have [_ [_ [Hl _]]] := H3 h t Hown. }
    have Ho : forall j, (j < n)%nat -> own_last log h (pa_add base j) t.
    { move => j Hj. have [_ [_ [_ [_ H3]]]] := Hcov j Hj.
      by have [_ [_ [_ Hol]]] := H3 h t Hown. }
    exact (lkcpu_not_mine img log base n Hn h tv t z cp
             win_assemble_win_ok win_assemble_wpin Hlen Hvis Hz Ho Hzk Hinj).
  Qed.
End assemble.

(* ===================================================================== *)
(* §12d  THE TIMESTAMP GHOST'S ELEMENT (was §11).                         *)
(*                                                                       *)
(* THREE conjuncts, not one and not two: [ts_ok] BUNDLES the LATEST tie    *)
(* (which every ordinary byte has), the PIN tie (only a pinned element     *)
(* has it, vacuous at [None]) and the WINDOW tie (only a lock-cell byte    *)
(* has it, vacuous at [None]).  The new one is LAST, per durable-notes'    *)
(* new-conjunct rule, so the ~20 positional destructurings of the interp   *)
(* across [RiscvExec] / [HartLift] / [HartSpan] / [TsoCtx] do not move.    *)
(*                                                                       *)
(* THE PAYLOAD IS A RECORD, not a nested pair: [e.1] (the timestamp) is    *)
(* what the interp's ~20 sites project, and a record keeps it at [.1]      *)
(* while the two optional arms get NAMES rather than positions.           *)
(* ===================================================================== *)

Record ts_pay : Type := TsPay {
  (* the field names are [tsp_], not [tp_]: [HartTp.tp_pin] already exists
     tree-wide (the hart's register-file pin) and a record field shadows it
     in every file that imports this one -- the failure surfaces far away,
     as [The term "m" has type "regfile" while it is expected to have type
     "ts_pay"] in [IntrDefs]. *)
  tsp_pin : option (byteset * nat);   (* tso-pin-memo.md §5's confinement *)
  tsp_win : option ts_win;            (* §12c's per-byte window claim *)
}.

Definition ts_pay_none : ts_pay := TsPay None None.
Definition ts_pay_pin (Sv : byteset) (B : nat) : ts_pay := TsPay (Some (Sv, B)) None.
Definition ts_pay_win (W : ts_win) : ts_pay := TsPay None (Some W).

Definition ts_elem : Type := nat * ts_pay.

Definition ts_ok (img mem : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (e : ts_elem) : Prop :=
  (exists v, mem !! a = Some v /\ latest img log a e.1 v)
  /\ (forall (Sv : byteset) (B : nat),
        tsp_pin e.2 = Some (Sv, B) -> pin_ok img log a B Sv)
  /\ (forall W : ts_win, tsp_win e.2 = Some W -> win_ok1 img log a W).

Lemma ts_ok_latest img mem log a e :
  ts_ok img mem log a e -> exists v, mem !! a = Some v /\ latest img log a e.1 v.
Proof. by move => [H _]. Qed.

Lemma ts_ok_pin img mem log a e Sv B :
  ts_ok img mem log a e -> tsp_pin e.2 = Some (Sv, B) -> pin_ok img log a B Sv.
Proof. move => [_ [H _]]. by apply H. Qed.

Lemma ts_ok_win img mem log a e W :
  ts_ok img mem log a e -> tsp_win e.2 = Some W -> win_ok1 img log a W.
Proof. move => [_ [_ H]]. by apply H. Qed.

(* the UNPAYLOADED element: exactly the old tie, and nothing more to prove *)
Lemma ts_ok_unpinned img mem log a t v :
  mem !! a = Some v -> latest img log a t v ->
  ts_ok img mem log a (t, ts_pay_none).
Proof.
  move => Hm Hl. split; [by exists v |].
  split; by move => *.
Qed.

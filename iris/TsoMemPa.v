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

Definition ts_elem : Type := nat * option (byteset * nat).

Definition ts_ok (img mem : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (a : Arch.pa) (e : ts_elem) : Prop :=
  (exists v, mem !! a = Some v /\ latest img log a e.1 v)
  /\ (forall (Sv : byteset) (B : nat), e.2 = Some (Sv, B) -> pin_ok img log a B Sv).

Lemma ts_ok_latest img mem log a e :
  ts_ok img mem log a e -> exists v, mem !! a = Some v /\ latest img log a e.1 v.
Proof. by move => [H _]. Qed.

Lemma ts_ok_pin img mem log a e Sv B :
  ts_ok img mem log a e -> e.2 = Some (Sv, B) -> pin_ok img log a B Sv.
Proof. move => [_ H]. by apply H. Qed.

(* the UNPINNED element: exactly the old tie, and nothing more to prove *)
Lemma ts_ok_unpinned img mem log a t v :
  mem !! a = Some v -> latest img log a t v -> ts_ok img mem log a (t, None).
Proof. move => Hm Hl. split; [by exists v | by move => Sv B]. Qed.

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

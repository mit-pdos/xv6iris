(* TsoCtxTwin3.v -- THE TWO-LOG TWIN (claude-notes/projects/relaxed-ww.md,
   order of work item 2).

   [TsoCtxTwin2.v] proved the context machinery the tree runs on --
   authorities in the tokens, one monotone nat per context, the clean/dirty
   bit in the fact -- over the ONE-LOG view machine, where a store's
   timestamp is both its identity and its coherence position.  The
   store-store relaxation splits those two ([TsoMem.v]): the ISSUE log keeps
   the identities and the DRAIN log carries coherence and every view.  This
   file re-proves the machinery over the two-log machine.  It is a
   self-contained Iris ghost theory: no WP, no language, ghost updates only.
   What it settles, before the real files move:

     - THE TWO NUMBER LINES.  Timestamps in facts and dirty keys stay ISSUE
       indices; the context bound, the view receipt and every stamp are DRAIN
       positions.  The tie between them is [dpos_ev t B]: persistent evidence
       that message [t] is drained at a position under [B], either a per-
       message witness off the drain map or the bulk receipt of the author's
       release fence, [drain_lb A N M] ("every A-message issued below N is
       drained below M").
     - CLEAN = DRAINED UNDER THE BOUND.  [ctx_pointsto]'s clean arm carries
       [dpos_ev]; a dirty entry's bundle-side justification is [dpos_ev] or
       "the author's own message".  [twin_load_ok] holds at every view above
       the floor, both arms.
     - COHERENCE FOR OWNED BYTES IS A FACT OF THE HEAP TIE, not of the
       machine: [chain_ok] says every earlier message to the byte is drained
       or by the same author, and drained before it.  The store gate keeps
       it (the previous latest is clean-or-own), and with the machine's
       per-hart FIFO ([fifo_ok]) it makes the issue-latest write the
       coherence-latest one -- which is what [tso_read] returns.
     - PARK KEEPS DIRTY ENTRIES DIRTY, WITH AN AUTHOR.  A pending store has
       no drain position, so [ctx_parked ξ B W A] carries the author and the
       per-entry justifications, and RESUME needs the author's receipt with
       [W ≤ N] and [M ≤ K] beside [view_lb h K] with [B ≤ K].  The releaser
       proves [W ≤ N] at its fence (it holds [llb W]); the acquirer proves
       [M ≤ K] and [B ≤ K] at its acquire leaf (it sits at the top).
     - THE TRANSPORT PERMISSION HAS TWO FLAVOURS.  Same-hart (fork deposit,
       release): dirty facts stay dirty and are re-registered in the target's
       set, so the dom LENDS the target's dirty authority and the target token
       comes back at the give-back.  Acquire: dirty facts become clean through
       the receipt, so the dom carries the receipt and the source's per-entry
       justifications.  [CtxMorph] keeps its bare shape.

   Kept as the design record for stage D; the tree's [TsoCtx.v] is this file
   restated at [Arch.pa]/[CPU]. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.algebra Require Import auth dfrac numbers functions gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map mono_nat.
From xv6iris Require Import TsoMem.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * 0.  The pure layer                                               *)
(* ================================================================== *)

Definition img_fun (img : gmap Z (bv 8)) : image := λ a, img !! a.

(** Timestamp [t] holds a's latest ISSUED write, with value [v]. *)
Definition latest (img : image) (log : list wmsg) (a : Z) (t : nat)
    (v : bv 8) : Prop :=
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

Lemma msg_byte_singleton_eq a w h : msg_byte (WMsg a [w] h) a = Some w.
Proof.
  rewrite /msg_byte /=.
  have -> : bool_decide (a ≤ a) = true by apply bool_decide_eq_true_2; lia.
  by rewrite Z.sub_diag.
Qed.

Lemma msg_byte_singleton_ne a w h a0 :
  a0 ≠ a → msg_byte (WMsg a [w] h) a0 = None.
Proof.
  move => Hne. rewrite /msg_byte /=.
  destruct (bool_decide (a ≤ a0)) eqn:Hle; last done.
  apply bool_decide_eq_true in Hle.
  have -> : Z.to_nat (a0 - a) = S (Z.to_nat (a0 - a - 1)) by lia.
  done.
Qed.

Lemma latest_app_new img log h a w :
  latest img (store_log log h a [w]) a (S (length log)) w.
Proof.
  rewrite /store_log. split.
  - rewrite log_byte_top msg_byte_singleton_eq //.
  - move => t' Ht'. apply log_byte_beyond. rewrite length_app /=. lia.
Qed.

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

(** [latest] at a message index: the message writes the byte, and nothing
    above it does. *)
Lemma latest_S img log a j v :
  latest img log a (S j) v →
  ∃ m, log !! j = Some m ∧ msg_byte m a = Some v ∧
       ∀ i mi, (j < i)%nat → log !! i = Some mi → msg_byte mi a = None.
Proof.
  move => [Hb Hab]. rewrite /log_byte in Hb.
  destruct (log !! j) as [m|] eqn:Hj; last done.
  exists m. split_and!; [done|done|].
  move => i mi Hlt Hi. have := Hab (S i) ltac:(lia). rewrite /log_byte Hi //.
Qed.

Lemma latest_0 img log a v :
  latest img log a 0 v →
  img a = Some v ∧ ∀ i mi, log !! i = Some mi → msg_byte mi a = None.
Proof.
  move => [Hb Hab]. split; [done|].
  move => i mi Hi. have := Hab (S i) ltac:(lia). rewrite /log_byte Hi //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The machine invariants the twin carries *)

(** Per-hart FIFO across the drain log: a drained message's earlier
    same-author overlapping messages are drained BELOW it.  A step invariant
    of the machine (the drain rule's premise), stated so the ghost layer can
    use it without the run's history. *)
Definition fifo_ok (log : list wmsg) (dl : list nat) : Prop :=
  ∀ i j mi mj qj, (i < j)%nat → log !! i = Some mi → log !! j = Some mj →
    wm_tid mi = wm_tid mj → msg_overlapb mi mj = true → dl !! qj = Some j →
    ∃ qi, dl !! qi = Some i ∧ (qi < qj)%nat.

(** The per-byte CHAIN at the byte's latest write [t]: every earlier message
    to the byte is drained or by the same author, and if [t]'s message has
    drained then every earlier one drained below it.  Not a machine
    invariant -- the machine lets a foreign later store drain first -- but a
    consequence of the ownership discipline the store gate enforces. *)
Definition chain_ok (log : list wmsg) (dl : list nat) (a : Z) (t : nat) : Prop :=
  ∀ j mj, t = S j → log !! j = Some mj →
  ∀ i mi, (i < j)%nat → log !! i = Some mi → is_Some (msg_byte mi a) →
    (i ∈ dl ∨ wm_tid mi = wm_tid mj) ∧
    (∀ q, dl !! q = Some j → ∃ q', dl !! q' = Some i ∧ (q' < q)%nat).

Lemma chain_ok_0 log dl a : chain_ok log dl a 0.
Proof. by move => j mj. Qed.

Lemma dl_ok_app_log log m dl : dl_ok log dl → dl_ok (log ++ [m]) dl.
Proof.
  move => [Hnd Hlt]. split; [done|]. move => i Hi. rewrite length_app /=.
  have := Hlt _ Hi. lia.
Qed.

Lemma dl_lookup_lt log dl q i :
  dl_ok log dl → dl !! q = Some i → (i < length log)%nat.
Proof. move => [_ Hlt] Hq. apply Hlt. by eapply elem_of_list_lookup_2. Qed.

Lemma lookup_app_last' {A} (l : list A) (m : A) (j : nat) (m' : A) :
  (l ++ [m]) !! j = Some m' →
  ((j < length l)%nat ∧ l !! j = Some m') ∨ (j = length l ∧ m' = m).
Proof.
  move => Hlk. destruct (decide (j < length l)%nat) as [Hlt|Hge].
  - left. split; [done|]. rewrite -Hlk. symmetry. by apply lookup_app_l.
  - right.
    have Heq : (l ++ [m]) !! j = [m] !! (j - length l)%nat by apply lookup_app_r; lia.
    rewrite Heq in Hlk.
    destruct (j - length l)%nat as [|k] eqn:Hk; simpl in Hlk; [|done].
    split; [lia|]. by simplify_eq.
Qed.

Lemma fifo_ok_app_log log dl m : dl_ok log dl → fifo_ok log dl → fifo_ok (log ++ [m]) dl.
Proof.
  move => Hok Hf i j mi mj qj Hij Hi Hj Htid Hov Hqj.
  have Hjl : (j < length log)%nat by eapply dl_lookup_lt.
  rewrite lookup_app_l // in Hj. rewrite lookup_app_l in Hi; [|lia].
  by eapply Hf.
Qed.

Lemma fifo_ok_drain log dl k :
  dl_ok log dl → drain_ok log dl k → fifo_ok log dl → fifo_ok log (dl ++ [k]).
Proof.
  move => Hok Hdr Hf i j mi mj qj Hij Hi Hj Htid Hov Hqj.
  apply lookup_app_last' in Hqj as [[_ Hqj]|[-> <-]].
  - destruct (Hf _ _ _ _ _ Hij Hi Hj Htid Hov Hqj) as (qi & Hqi & ?).
    exists qi. split; [by apply lookup_app_l_Some|done].
  - have Hin := drain_ok_fifo _ _ _ _ _ _ Hdr Hij Hj Hi Htid Hov.
    apply elem_of_list_lookup_1 in Hin as [qi Hqi]. exists qi.
    split; [by apply lookup_app_l_Some|by eapply lookup_lt_Some].
Qed.

Lemma chain_ok_app_log log dl a t m :
  (t ≤ length log)%nat → chain_ok log dl a t → chain_ok (log ++ [m]) dl a t.
Proof.
  move => Ht Hc j mj Ht' Hj i mi Hij Hi Hb. subst t.
  rewrite lookup_app_l in Hj; [|lia]. rewrite lookup_app_l in Hi; [|lia].
  by eapply Hc.
Qed.

Lemma chain_ok_drain img log dl a t v k :
  dl_ok log dl → drain_ok log dl k → latest img log a t v →
  chain_ok log dl a t → chain_ok log (dl ++ [k]) a t.
Proof.
  move => Hok Hdr Hlat Hc j mj Ht Hj i mi Hij Hi Hb.
  destruct (Hc _ _ Ht Hj _ _ Hij Hi Hb) as [Hor Hpos]. split.
  - destruct Hor as [Hin|?]; [left; apply elem_of_app; by left|by right].
  - move => q Hq. apply lookup_app_last' in Hq as [[_ Hq]|[-> <-]].
    + destruct (Hpos _ Hq) as (q' & Hq' & ?). exists q'.
      split; [by apply lookup_app_l_Some|done].
    + (* [j] drains now: every earlier message to the byte is already in *)
      have Hin : i ∈ dl.
      { destruct Hor as [Hin|Htid]; [done|].
        destruct Hb as [vi Hvi].
        subst t. destruct (latest_S _ _ _ _ _ Hlat) as (mj' & Hj' & Hvj & _).
        rewrite Hj in Hj'. injection Hj' as <-.
        eapply (drain_ok_fifo _ _ _ _ _ _ Hdr Hij Hj Hi Htid).
        by eapply msg_overlapb_of_byte. }
      apply elem_of_list_lookup_1 in Hin as [q' Hq']. exists q'.
      split; [by apply lookup_app_l_Some|by eapply lookup_lt_Some].
Qed.

(** The STORE GATE's pure half: a new message to [a] by [h] becomes the
    latest, and its chain holds because the previous latest was drained or
    [h]'s own, and everything under THAT was drained or its author's. *)
Definition drained_or_by (log : list wmsg) (dl : list nat) (h : agent) (t : nat)
    : Prop :=
  ∀ j mj, t = S j → log !! j = Some mj → j ∈ dl ∨ wm_tid mj = h.

Lemma chain_ok_new img log dl a t v h w :
  dl_ok log dl → fifo_ok log dl →
  latest img log a t v → chain_ok log dl a t → drained_or_by log dl h t →
  chain_ok (store_log log h a [w]) dl a (S (length log)).
Proof.
  move => Hok Hf Hlat Hc Hgate j mj [= <-] Hj i mi Hij Hi Hb.
  rewrite /store_log in Hj. rewrite list_lookup_middle // in Hj. injection Hj as <-.
  rewrite lookup_app_l // in Hi.
  split; last first.
  { (* the new message is not drained: [length log] is not an issue index yet *)
    move => q Hq. exfalso. have := dl_lookup_lt _ _ _ _ Hok Hq. lia. }
  simpl.
  destruct t as [|j0].
  { exfalso. destruct (latest_0 _ _ _ _ Hlat) as [_ Hnone].
    destruct Hb as [vi Hvi]. rewrite (Hnone _ _ Hi) in Hvi. discriminate. }
  destruct (latest_S _ _ _ _ _ Hlat) as (m0 & Hj0 & Hv0 & Habove).
  destruct (decide (i = j0)) as [->|Hne].
  - rewrite Hj0 in Hi. injection Hi as <-. by apply (Hgate _ _ eq_refl Hj0).
  - destruct (decide (j0 < i)%nat) as [Hlt|Hge].
    { exfalso. destruct Hb as [vi Hvi]. rewrite (Habove _ _ Hlt Hi) in Hvi. discriminate. }
    have Hij0 : (i < j0)%nat by lia.
    destruct (Hc _ _ eq_refl Hj0 _ _ Hij0 Hi Hb) as [[Hin|Htid] _]; [by left|].
    destruct (Hgate _ _ eq_refl Hj0) as [Hin0|Htid0]; last by right; congruence.
    (* the previous latest drained, so its earlier same-author messages did *)
    left. apply elem_of_list_lookup_1 in Hin0 as [q0 Hq0].
    destruct Hb as [vi Hvi].
    destruct (Hf _ _ _ _ _ Hij0 Hi Hj0 Htid (msg_overlapb_of_byte _ _ _ _ _ Hvi Hv0) Hq0)
      as (qi & Hqi & _).
    by eapply elem_of_list_lookup_2.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The ghost mirrors of the drain log *)

(** [DP] mirrors the drain log: message [i] is at position [S q]. *)
Definition dpos_ok (dl : list nat) (DP : gmap nat nat) : Prop :=
  ∀ i p, DP !! i = Some p ↔ ∃ q, dl !! q = Some i ∧ p = S q.

Lemma dpos_ok_drain log dl DP k :
  dl_ok log dl → drain_ok log dl k → dpos_ok dl DP →
  DP !! k = None ∧ dpos_ok (dl ++ [k]) (<[k := S (length dl)]> DP).
Proof.
  move => Hok Hdr Hdp.
  have Hk : k ∉ dl by apply (drain_ok_pending _ _ _ Hdr).
  have HDPk : DP !! k = None.
  { destruct (DP !! k) as [p|] eqn:HDP; last done.
    apply Hdp in HDP as (q & Hq & _). exfalso. apply Hk. by eapply elem_of_list_lookup_2. }
  split; [done|].
  move => i p. destruct (decide (i = k)) as [->|Hne].
  - rewrite lookup_insert. split.
    + move => [= <-]. exists (length dl). split; [by apply list_lookup_middle|done].
    + move => [q [Hq ->]]. apply lookup_app_last' in Hq as [[_ Hq]|[-> _]].
      * exfalso. apply Hk. by eapply elem_of_list_lookup_2.
      * done.
  - rewrite lookup_insert_ne //. rewrite Hdp. split.
    + move => [q [Hq ->]]. exists q. split; [by apply lookup_app_l_Some|done].
    + move => [q [Hq ->]]. apply lookup_app_last' in Hq as [[_ Hq]|[_ Heq]];
        [by exists q|congruence].
Qed.

(** [RL] holds the release receipts: at [(A, N) ↦ M], every A-message
    issued below [N] is drained at a position at most [M]. *)
Definition rl_ok (log : list wmsg) (dl : list nat) (RL : gmap (agent * nat) nat)
    : Prop :=
  ∀ A N M, RL !! (A, N) = Some M →
    (N ≤ length log)%nat ∧ (M ≤ length dl)%nat ∧
    ∀ i m, (i < N)%nat → log !! i = Some m → wm_tid m = A →
      ∃ q, dl !! q = Some i ∧ (S q ≤ M)%nat.

Lemma rl_ok_app_log log dl RL m : rl_ok log dl RL → rl_ok (log ++ [m]) dl RL.
Proof.
  move => Hrl A N M HAN. destruct (Hrl _ _ _ HAN) as (HN & HM & Hall).
  split_and!; [rewrite length_app /=; lia|done|].
  move => i mi Hi Hlk Htid. rewrite lookup_app_l in Hlk; [|lia]. by eapply Hall.
Qed.

Lemma rl_ok_drain log dl RL k : rl_ok log dl RL → rl_ok log (dl ++ [k]) RL.
Proof.
  move => Hrl A N M HAN. destruct (Hrl _ _ _ HAN) as (HN & HM & Hall).
  split_and!; [done|rewrite length_app /=; lia|].
  move => i mi Hi Hlk Htid. destruct (Hall _ _ Hi Hlk Htid) as (q & Hq & ?).
  exists q. split; [by apply lookup_app_l_Some|done].
Qed.

Lemma rl_ok_mint log dl RL h :
  own_drained h log dl → rl_ok log dl RL →
  rl_ok log dl (<[(h, length log) := length dl]> RL).
Proof.
  move => Hod Hrl A N M. destruct (decide ((A, N) = (h, length log))) as [[= -> ->]|Hne].
  - rewrite lookup_insert. move => [= <-]. split_and!; [done|done|].
    move => i m Hi Hlk Htid.
    have Hin := own_drained_lookup _ _ _ _ _ Hod Hlk Htid.
    apply elem_of_list_lookup_1 in Hin as [q Hq]. exists q.
    split; [done|by eapply lookup_lt_Some].
  - rewrite lookup_insert_ne //. apply Hrl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The read bridge *)

(** A hart with no undrained message to [a] forwards nothing. *)
Lemma pend_read_none_of log dl h a :
  (∀ i m, log !! i = Some m → wm_tid m = h → i ∉ dl → msg_byte m a = None) →
  pend_read log dl h a = None.
Proof.
  move => Hno. rewrite /pend_read.
  destruct (pend_down log dl h a (length log)) as [v|] eqn:Hp; [|done].
  destruct (pend_down_some _ _ _ _ _ _ Hp) as (i & m & _ & Hi & Htid & Hnd & Hb).
  rewrite (Hno _ _ Hi Htid Hnd) in Hb. discriminate.
Qed.

(** The pending scan finds the hart's topmost pending message to [a] when
    nothing above it writes [a]. *)
Lemma pend_down_hit log dl h a t j m v :
  (j < t)%nat → log !! j = Some m → wm_tid m = h → j ∉ dl → msg_byte m a = Some v →
  (∀ i mi, (j < i)%nat → log !! i = Some mi → msg_byte mi a = None) →
  pend_down log dl h a t = Some v.
Proof.
  induction t as [|t IH] => Hjt Hj Htid Hnd Hb Habove; first lia.
  rewrite pend_down_S.
  destruct (decide (t = j)) as [->|Hne].
  - rewrite Hj Htid bool_decide_eq_true_2 //.
    have -> : drainedb dl j = false by apply drainedb_false.
    rewrite /= Hb //.
  - have Hlt : (j < t)%nat by lia.
    destruct (log !! t) as [mt|] eqn:Ht; last by apply IH.
    rewrite (Habove _ _ Hlt Ht).
    destruct (bool_decide (wm_tid mt = h) && negb (drainedb dl t)); by apply IH.
Qed.

(** A scan over positions none of which writes [a] returns the image. *)
Lemma read_down_none_above img log dl h tv a P :
  (∀ p, (1 ≤ p)%nat → (p ≤ P)%nat → dpos_byte img log dl p a = None) →
  read_down img log dl h tv a P = img a.
Proof.
  induction P as [|P IH] => Hnone; first by rewrite read_down_0.
  rewrite read_down_S. rewrite Hnone; [|lia|lia].
  destruct (visibleb h tv log dl (S P)); apply IH; move => p ? ?; apply Hnone; lia.
Qed.

(** THE BRIDGE.  The latest issued write to [a] is at [t]; the chain holds;
    and [t]'s message is VISIBLE to [h] at [tv] -- drained at a position under
    the view, or [h]'s own (pending or drained).  Then [h] reads its value. *)
Definition msg_visible (log : list wmsg) (dl : list nat) (h : agent) (tv : nat)
    (t : nat) : Prop :=
  t = 0%nat ∨
  ∃ j m, t = S j ∧ log !! j = Some m ∧
    ((∃ q, dl !! q = Some j ∧ (S q ≤ tv)%nat) ∨ wm_tid m = h).

Lemma tso_read_of_latest img log dl h tv a t v :
  dl_ok log dl → fifo_ok log dl →
  latest img log a t v → chain_ok log dl a t → msg_visible log dl h tv t →
  tso_read img log dl h tv a = Some v.
Proof.
  move => [Hnd Hlt] Hf Hlat Hc Hvis.
  destruct Hvis as [->|(j & m & -> & Hj & Hvis)].
  { (* the image: nothing in the log writes [a] *)
    destruct (latest_0 _ _ _ _ Hlat) as [Hi Hnone].
    rewrite /tso_read pend_read_none_of; last first.
    { move => i mi Hi' _ _. by apply (Hnone _ _ Hi'). }
    rewrite read_down_none_above //.
    move => p Hp1 HpP. rewrite /dpos_byte /dmsg. destruct p as [|q]; first lia.
    destruct (dl !! q) as [i|]; last done.
    destruct (log !! i) as [mi|] eqn:Hi'; last done. by apply (Hnone _ _ Hi'). }
  destruct (latest_S _ _ _ _ _ Hlat) as (m' & Hj' & Hb & Habove).
  rewrite Hj in Hj'. injection Hj' as <-.
  (* every earlier message to [a] from another author is drained; from the
     same author it is drained if [j] is *)
  have Hchain := Hc _ _ eq_refl Hj.
  destruct (decide (j ∈ dl)) as [Hin|Hout]; last first.
  { (* [j] pending: it must be [h]'s own, and it is forwarded *)
    destruct Hvis as [(q & Hq & _)|Htid].
    { exfalso. apply Hout. by eapply elem_of_list_lookup_2. }
    rewrite /tso_read /pend_read.
    rewrite (pend_down_hit _ _ _ _ _ j m v) //. by eapply lookup_lt_Some. }
  (* [j] drained at [q]: nothing of [h]'s is pending to [a] *)
  apply elem_of_list_lookup_1 in Hin as [q Hq].
  have Hpend : pend_read log dl h a = None.
  { apply pend_read_none_of. move => i mi Hi Htid Hnd0.
    destruct (msg_byte mi a) as [vi|] eqn:Hvi; last done. exfalso.
    destruct (decide (j < i)%nat) as [Hlt'|Hge].
    { rewrite (Habove _ _ Hlt' Hi) in Hvi. discriminate. }
    destruct (decide (i = j)) as [->|Hne].
    { apply Hnd0. by eapply elem_of_list_lookup_2. }
    have Hij : (i < j)%nat by lia.
    destruct (Hchain _ _ Hij Hi ltac:(by eexists)) as [[Hin'|Hsame] _]; [done|].
    destruct (Hf _ _ _ _ _ Hij Hi Hj Hsame (msg_overlapb_of_byte _ _ _ _ _ Hvi Hb) Hq)
      as (qi & Hqi & _).
    apply Hnd0. by eapply elem_of_list_lookup_2. }
  rewrite /tso_read Hpend.
  have Hvq : visibleb h tv log dl (S q) = true.
  { destruct Hvis as [(q' & Hq' & Hle)|Htid].
    - have Heq : q' = q by eapply NoDup_lookup. subst q'. by apply visibleb_below.
    - by eapply visibleb_own. }
  have Hbq : dpos_byte img log dl (S q) a = Some v by rewrite /dpos_byte /dmsg Hq Hj.
  have Hqlen : (S q ≤ length dl)%nat by apply lookup_lt_Some in Hq; lia.
  destruct (read_down_latest img log dl h tv a (length dl) (S q) v Hqlen Hvq Hbq)
    as (p'' & v'' & Hge & Hr & Hvis'' & Hb'').
  rewrite Hr. destruct (decide (p'' = S q)) as [->|Hne]; first congruence.
  exfalso.
  (* a higher position writing [a] would be an earlier message drained above [j] *)
  destruct p'' as [|q'']; first lia.
  rewrite /dpos_byte /dmsg in Hb''.
  destruct (dl !! q'') as [i|] eqn:Hq''; last done.
  destruct (log !! i) as [mi|] eqn:Hi; last done.
  destruct (decide (j < i)%nat) as [Hlt'|Hge'].
  { rewrite (Habove _ _ Hlt' Hi) in Hb''. discriminate. }
  destruct (decide (i = j)) as [->|Hne'].
  { have : q'' = q by eapply NoDup_lookup. lia. }
  have Hij : (i < j)%nat by lia.
  destruct (Hchain _ _ Hij Hi ltac:(by eexists)) as [_ Hpos].
  destruct (Hpos _ Hq) as (q' & Hq' & Hlt2).
  have : q' = q'' by eapply NoDup_lookup. lia.
Qed.

(* ================================================================== *)
(** * 1.  The view algebra (TsoCtxTwin2 §1, verbatim)                  *)
(* ================================================================== *)

Definition viewUR : ucmra := discrete_funUR (λ _ : agent, max_natUR).

Definition vf (tvs : agent → nat) : viewUR := λ h, MaxNat (tvs h).

Definition vone (h : agent) (K : nat) : viewUR :=
  λ h', MaxNat (if decide (h' = h) then K else 0%nat).

Global Instance vf_core_id tvs : CoreId (vf tvs).
Proof. constructor => h. reflexivity. Qed.

Global Instance vone_core_id h K : CoreId (vone h K).
Proof. constructor => h'. reflexivity. Qed.

Lemma vone_incl_vf h K tvs : (K ≤ tvs h)%nat → vone h K ≼ vf tvs.
Proof.
  intros HK. exists (vf tvs). intros h'.
  rewrite discrete_fun_lookup_op /vone /vf max_nat_op.
  rewrite Nat.max_r; [done|].
  destruct (decide (h' = h)) as [->|Hne]; lia.
Qed.

Lemma vf_local_update tvs tvs' :
  (∀ h, tvs h ≤ tvs' h)%nat → (vf tvs, vf tvs) ~l~> (vf tvs', vf tvs').
Proof.
  intros Hle. rewrite local_update_unital_discrete => z _ Heq.
  split; [by intros h|]. intros h. specialize (Heq h). specialize (Hle h).
  rewrite discrete_fun_lookup_op in Heq. rewrite discrete_fun_lookup_op.
  rewrite /vf in Heq |- *.
  destruct (z h) as [zh].
  rewrite max_nat_op in Heq. rewrite max_nat_op.
  revert Heq. intros [= Heq]. rewrite Nat.max_l; [done|lia].
Qed.

(* ================================================================== *)
(** * 2.  The ghost classes                                            *)
(* ================================================================== *)

Class tsoCtx3G Σ := TsoCtx3G {
  tc3_heapG :: ghost_mapG Σ Z (nat * bv 8);
  tc3_logmG :: ghost_mapG Σ nat wmsg;
  tc3_dposG :: ghost_mapG Σ nat nat;
  tc3_rlG   :: ghost_mapG Σ (agent * nat) nat;
  tc3_natG  :: mono_natG Σ;
  tc3_viewG :: inG Σ (authR viewUR);
  tc3_dsetG :: inG Σ (authR (gsetUR (nat * Z)));
}.

Record CtxId := MkCtxId { tc_bnd : gname; tc_dirty : gname }.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
Global Instance ctx_id_inhabited : Inhabited CtxId :=
  populate (MkCtxId inhabitant inhabitant).
Global Instance ctx_id_countable : Countable CtxId.
Proof.
  apply (inj_countable' (λ ξ, (tc_bnd ξ, tc_dirty ξ))
           (λ p, MkCtxId p.1 p.2)).
  by intros [].
Qed.

Section twin3.
  Context {Σ : gFunctors} `{!tsoCtx3G Σ}.
  Context (γheap γlogm γdpos γrl γloglen γdlen γview : gname).

  (* ---------------------------------------------------------------- *)
  (** ** 3. Persistent receipts: two lengths, a view, an author, a
         drain position, a release                                    *)
  (* ---------------------------------------------------------------- *)

  (** A lower bound on a monotone counter, with the zero arm pure. *)
  Definition nlb (γ : gname) (K : nat) : iProp Σ :=
    (mono_nat_lb_own γ K ∨ ⌜K = 0%nat⌝)%I.

  Global Instance nlb_persistent γ K : Persistent (nlb γ K).
  Proof. apply _. Qed.
  Global Instance nlb_timeless γ K : Timeless (nlb γ K).
  Proof. apply _. Qed.

  Lemma nlb_0 γ : ⊢ nlb γ 0.
  Proof. by iRight. Qed.

  Lemma nlb_le γ K K' : (K' ≤ K)%nat → nlb γ K -∗ nlb γ K'.
  Proof.
    iIntros (Hle) "[Hlb|%Hz]".
    - iLeft. by iApply mono_nat_lb_own_le.
    - iRight. iPureIntro. lia.
  Qed.

  Lemma nlb_max γ K1 K2 : nlb γ K1 -∗ nlb γ K2 -∗ nlb γ (Nat.max K1 K2).
  Proof.
    iIntros "H1 H2". destruct (decide (K1 ≤ K2)%nat) as [Hle|Hgt].
    - iClear "H1". iApply (nlb_le with "H2"). lia.
    - iClear "H2". iApply (nlb_le with "H1"). lia.
  Qed.

  Lemma nlb_valid γ n K : mono_nat_auth_own γ 1 n -∗ nlb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  Lemma nlb_get γ n : mono_nat_auth_own γ 1 n -∗ nlb γ n.
  Proof. iIntros "Ha". iLeft. by iApply mono_nat_lb_own_get. Qed.

  (** The ISSUE-log length bound (dirty watermarks) and the DRAIN-log length
      bound (stamps, bounds, views). *)
  Notation llb := (nlb γloglen).
  Notation dlb := (nlb γdlen).

  (** THE STABLE HART-VIEW LOWER BOUND: "hart [h]'s view has passed drain
      position [K]".  Carries [dlb K]. *)
  Definition view_lb (h : agent) (K : nat) : iProp Σ :=
    ((own γview (◯ vone h K) ∗ mono_nat_lb_own γdlen K) ∨ ⌜K = 0%nat⌝)%I.

  Global Instance view_lb_persistent h K : Persistent (view_lb h K).
  Proof. apply _. Qed.
  Global Instance view_lb_timeless h K : Timeless (view_lb h K).
  Proof. apply _. Qed.

  Lemma view_lb_0 h : ⊢ view_lb h 0.
  Proof. by iRight. Qed.

  Lemma view_lb_dlb h K : view_lb h K -∗ dlb K.
  Proof. iIntros "[[_ Hlb]|%Hz]"; [by iLeft | by iRight]. Qed.

  Definition view_auth (tvs : agent → nat) : iProp Σ :=
    own γview (● vf tvs ⋅ ◯ vf tvs).

  Lemma view_auth_frag tvs h K :
    (K ≤ tvs h)%nat → view_auth tvs -∗ own γview (◯ vone h K).
  Proof.
    iIntros (HK) "Hv". iApply (own_mono with "Hv").
    etrans; [apply auth_frag_mono, vone_incl_vf, HK | apply cmra_included_r].
  Qed.

  Lemma view_auth_valid tvs h K :
    view_auth tvs -∗ view_lb h K -∗ ⌜(K ≤ tvs h)%nat⌝.
  Proof.
    iIntros "Ha [[Hf _]|%Hz]"; last (iPureIntro; lia).
    iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro.
    move: Hv. rewrite -assoc -auth_frag_op.
    rewrite auth_both_valid_discrete => -[Hincl _].
    apply (discrete_fun_included_spec_1 _ _ h) in Hincl.
    move: Hincl. rewrite discrete_fun_lookup_op /vf /vone max_nat_op.
    rewrite decide_True; last done.
    move => /max_nat_included /=. lia.
  Qed.

  Lemma view_auth_update tvs tvs' :
    (∀ h, tvs h ≤ tvs' h)%nat → view_auth tvs ==∗ view_auth tvs'.
  Proof.
    iIntros (Hle). iApply own_update.
    by apply auth_update, vf_local_update.
  Qed.

  (** The author of an issued message (a persistent log fragment). *)
  Definition author (i : nat) (A : agent) : iProp Σ :=
    (∃ m, i ↪[γlogm]□ m ∗ ⌜wm_tid m = A⌝)%I.
  Global Instance author_persistent i A : Persistent (author i A).
  Proof. apply _. Qed.

  (** Message [i] drained at position [p]. *)
  Definition dpos_at (i p : nat) : iProp Σ := i ↪[γdpos]□ p.

  (** THE RELEASE RECEIPT: every A-message issued below [N] is drained at a
      position at most [M].  Born at A's release fence.  Carries the two
      length bounds so consumers can place [N] and [M] without the interp. *)
  Definition drain_lb (A N M : nat) : iProp Σ :=
    ((A, N) ↪[γrl]□ M ∗ mono_nat_lb_own γdlen M ∗ mono_nat_lb_own γloglen N)%I.
  Global Instance drain_lb_persistent A N M : Persistent (drain_lb A N M).
  Proof. apply _. Qed.

  (** THE TIE BETWEEN THE NUMBER LINES: issue timestamp [t]'s message is
      drained at a position under [B] -- the image, a per-message witness,
      or the author's release receipt. *)
  Definition dpos_ev (t B : nat) : iProp Σ :=
    (⌜t = 0%nat⌝ ∨
     (∃ i p, ⌜t = S i⌝ ∗ dpos_at i p ∗ ⌜(p ≤ B)%nat⌝) ∨
     (∃ i A N M, ⌜t = S i⌝ ∗ author i A ∗ drain_lb A N M ∗ ⌜(i < N)%nat⌝ ∗ ⌜(M ≤ B)%nat⌝))%I.
  Global Instance dpos_ev_persistent t B : Persistent (dpos_ev t B).
  Proof. apply _. Qed.

  Lemma dpos_ev_mono t B B' : (B ≤ B')%nat → dpos_ev t B -∗ dpos_ev t B'.
  Proof.
    iIntros (Hle) "[%|[(%i & %p & % & #H & %)|(%i & %A & %N & %M & % & #Ha & #Hr & % & %)]]".
    - by iLeft.
    - iRight; iLeft. iExists i, p. iFrame "H". iPureIntro. split; [done|lia].
    - iRight; iRight. iExists i, A, N, M. iFrame "Ha Hr". iPureIntro. split_and!; [done|done|lia].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 4. The monotone dirty set (TsoGhost.dset at [nat * Z])        *)
  (* ---------------------------------------------------------------- *)

  Definition dset_auth (γ : gname) (q : Qp) (S : gset (nat * Z)) : iProp Σ :=
    own γ (●{#q} S).
  Definition dset_in (γ : gname) (k : nat * Z) : iProp Σ :=
    own γ (◯ ({[k]} : gset (nat * Z))).

  Global Instance dset_in_persistent γ k : Persistent (dset_in γ k).
  Proof. rewrite /dset_in. apply _. Qed.
  Global Instance dset_in_timeless γ k : Timeless (dset_in γ k).
  Proof. rewrite /dset_in. apply _. Qed.
  Global Instance dset_auth_timeless γ q S : Timeless (dset_auth γ q S).
  Proof. rewrite /dset_auth. apply _. Qed.

  Lemma dset_alloc : ⊢ |==> ∃ γ : gname, dset_auth γ 1 ∅.
  Proof.
    iMod (own_alloc (● (∅ : gset (nat * Z)))) as (γ) "H".
    { apply auth_auth_valid. done. }
    iModIntro. iExists γ. iExact "H".
  Qed.

  Lemma dset_halves γ S :
    dset_auth γ 1 S ⊣⊢ dset_auth γ (1/2) S ∗ dset_auth γ (1/2) S.
  Proof.
    rewrite /dset_auth -own_op -auth_auth_dfrac_op dfrac_op_own Qp.half_half. done.
  Qed.

  Lemma dset_agree γ q1 q2 S1 S2 :
    dset_auth γ q1 S1 -∗ dset_auth γ q2 S2 -∗ ⌜S1 = S2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    exact (auth_auth_dfrac_op_inv_L _ _ _ _ Hv).
  Qed.

  Lemma dset_lookup γ q S k :
    dset_auth γ q S -∗ dset_in γ k -∗ ⌜k ∈ S⌝.
  Proof.
    iIntros "Ha Hk". iCombine "Ha Hk" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    apply auth_both_dfrac_valid_discrete in Hv as (_ & Hincl & _).
    apply gset_included in Hincl. set_solver.
  Qed.

  Lemma dset_insert γ S k :
    dset_auth γ 1 S ==∗ dset_auth γ 1 (S ∪ {[k]}) ∗ dset_in γ k.
  Proof.
    iIntros "H".
    iMod (own_update _ _ (● (S ∪ {[k]}) ⋅ ◯ (S ∪ {[k]})) with "H") as "[H Hf]".
    { apply auth_update_alloc. apply gset_local_update. set_solver. }
    iModIntro. iFrame "H". iApply (own_mono with "Hf").
    apply auth_frag_mono, gset_included. set_solver.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 5. The tokens and the fact                                    *)
  (* ---------------------------------------------------------------- *)

  (** Both per-context authorities at a fraction: the BOUND (a drain
      position) and the DIRTY SET (issue keys). *)
  Definition ctx_at (ξ : CtxId) (q : Qp) (B : nat) (D : gset (nat * Z)) : iProp Σ :=
    (mono_nat_auth_own (tc_bnd ξ) q B ∗ dset_auth (tc_dirty ξ) q D)%I.

  Lemma ctx_at_halves ξ B D :
    ctx_at ξ 1 B D ⊣⊢ ctx_at ξ (1/2) B D ∗ ctx_at ξ (1/2) B D.
  Proof.
    rewrite /ctx_at.
    rewrite (fractional_half (mono_nat_auth_own (tc_bnd ξ) 1 B)).
    rewrite dset_halves.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma ctx_at_agree ξ q1 q2 B1 D1 B2 D2 :
    ctx_at ξ q1 B1 D1 -∗ ctx_at ξ q2 B2 D2 -∗ ⌜B1 = B2 ∧ D1 = D2⌝.
  Proof.
    iIntros "[Hb1 Hd1] [Hb2 Hd2]".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb2") as %[_ ?].
    iDestruct (dset_agree with "Hd1 Hd2") as %?.
    by iPureIntro.
  Qed.

  (** A DIRTY ENTRY'S JUSTIFICATION at author [A] and bound [B]: drained
      under the bound, or [A]'s own message (forwarding, pending or not). *)
  Definition dirty_ok (A B : nat) (k : nat * Z) : iProp Σ :=
    (dpos_ev k.1 B ∨ ∃ i, ⌜k.1 = S i⌝ ∗ author i A)%I.
  Global Instance dirty_ok_persistent A B k : Persistent (dirty_ok A B k).
  Proof. apply _. Qed.

  Lemma dirty_ok_mono A B B' k : (B ≤ B')%nat → dirty_ok A B k -∗ dirty_ok A B' k.
  Proof.
    iIntros (Hle) "[H|H]"; [iLeft; by iApply dpos_ev_mono | by iRight].
  Qed.

  (** All entries of a set, justified. *)
  Definition dirty_all (A B : nat) (D : gset (nat * Z)) : iProp Σ :=
    (□ ∀ k, ⌜k ∈ D⌝ → dirty_ok A B k)%I.
  Global Instance dirty_all_persistent A B D : Persistent (dirty_all A B D).
  Proof. apply _. Qed.

  Lemma dirty_all_mono A B B' D : (B ≤ B')%nat → dirty_all A B D -∗ dirty_all A B' D.
  Proof.
    iIntros (Hle) "#H !> %k %Hk". iApply dirty_ok_mono; [done|]. by iApply "H".
  Qed.

  Lemma dirty_all_empty A B : ⊢ dirty_all A B ∅.
  Proof. iIntros "!> %k %Hk". set_solver. Qed.

  Lemma dirty_all_insert A B D k :
    dirty_ok A B k -∗ dirty_all A B D -∗ dirty_all A B (D ∪ {[k]}).
  Proof.
    iIntros "#Hk #H !> %k' %Hk'". apply elem_of_union in Hk' as [Hk'|Hk'].
    - by iApply "H".
    - apply elem_of_singleton in Hk' as ->. iExact "Hk".
  Qed.

  (** THE RUNNING BUNDLE: "hart [h] runs as ξ".  The bound is under the
      hart's view receipt (drain positions); the dirty watermark [W] bounds
      the dirty keys (issue indices); every dirty entry is justified at [h]. *)
  Definition own_context (ξ : CtxId) (h : agent) : iProp Σ :=
    (∃ (B K W : nat) (D : gset (nat * Z)),
      ctx_at ξ 1 B D ∗
      view_lb h K ∗ ⌜(B ≤ K)%nat⌝ ∗
      llb W ∗ ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗
      dirty_all h B D)%I.

  (** THE PARKED TOKEN: bound [B] (a drain position, a legal one), dirty
      watermark [W], and the AUTHOR of its dirty entries. *)
  Definition ctx_parked (ξ : CtxId) (B W A : nat) : iProp Σ :=
    (∃ D : gset (nat * Z),
      ctx_at ξ 1 B D ∗ dlb B ∗ llb W ∗ ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗
      dirty_all A B D)%I.

  (** THE FACT: the heap element (issue timestamp and value) plus the BIT:
      clean -- drained at a position under ξ's bound -- or dirty, a
      persistent member of ξ's dirty set.  Both arms are persistent, so the
      dq lives in the heap element alone. *)
  Definition ctx_pointsto (ξ : CtxId) (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, a ↪[γheap]{dq} (t, v) ∗
       ((∃ p, dpos_ev t p ∗ mono_nat_lb_own (tc_bnd ξ) p) ∨
        dset_in (tc_dirty ξ) (t, a)))%I.

  (** THE TRANSPORT PERMISSION.  Half of ξ's authorities (value-pinned by
      agreement with the half left behind), ξ's per-entry justifications at
      author [A], a bound-lb of ξ' dominating ξ's bound -- AND the target's
      WHOLE dirty authority, lent, with its justifications at author [A'],
      because a pending fact re-registers in the target's set.  The
      conversion evidence: same author (the fact stays dirty) or [A]'s
      release receipt covering ξ's dirty watermark (the fact becomes clean).
      INDEXED BY THE TARGET'S AUTHOR [A']: the give-back rebuilds the
      target's token from the dom's lent authority and must know at which
      hart the returned justifications hold -- nothing in the ghost pins a
      context's author (it changes at every resume), so the index does. *)
  Definition ctx_dom (A' : agent) (ξ ξ' : CtxId) : iProp Σ :=
    (∃ (B W B' A W' : nat) (D D' : gset (nat * Z)),
      ctx_at ξ (1/2) B D ∗
      ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗ ⌜(B ≤ B')%nat⌝ ∗
      mono_nat_lb_own (tc_bnd ξ') B' ∗ dirty_all A B D ∗
      dset_auth (tc_dirty ξ') 1 D' ∗ llb W' ∗
      ⌜∀ k, k ∈ D' → (k.1 ≤ W')%nat⌝ ∗ ⌜(W ≤ W')%nat⌝ ∗ dirty_all A' B' D' ∗
      (⌜A = A'⌝ ∨ ∃ N M, drain_lb A N M ∗ ⌜(W ≤ N)%nat⌝ ∗ ⌜(M ≤ B')%nat⌝))%I.

  Lemma own_context_excl ξ h1 h2 :
    own_context ξ h1 -∗ own_context ξ h2 -∗ False.
  Proof.
    iIntros "(%B1 & %K1 & %W1 & %D1 & [Hb1 _] & _)".
    iIntros "(%B2 & %K2 & %W2 & %D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Lemma ctx_parked_excl ξ B1 W1 A1 B2 W2 A2 :
    ctx_parked ξ B1 W1 A1 -∗ ctx_parked ξ B2 W2 A2 -∗ False.
  Proof.
    iIntros "(%D1 & [Hb1 _] & _) (%D2 & [Hb2 _] & _)".
    iApply (mono_nat_auth_own_exclusive with "Hb1 Hb2").
  Qed.

  Global Instance own_context_timeless ξ h : Timeless (own_context ξ h).
  Proof. apply _. Qed.
  Global Instance ctx_parked_timeless ξ B W A : Timeless (ctx_parked ξ B W A).
  Proof. apply _. Qed.
  Global Instance ctx_pointsto_timeless ξ a dq v : Timeless (ctx_pointsto ξ a dq v).
  Proof. apply _. Qed.
  Global Instance ctx_pointsto_discarded_persistent ξ a v :
    Persistent (ctx_pointsto ξ a DfracDiscarded v).
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 6. The state interpretation -- MACHINE ONLY                   *)
  (* ---------------------------------------------------------------- *)

  (** The heap tie: the byte's latest ISSUED write, and its chain. *)
  Definition tie_ok (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (HM : gmap Z (nat * bv 8)) : Prop :=
    ∀ a t v, HM !! a = Some (t, v) → latest (img_fun img) log a t v ∧ chain_ok log dl a t.

  Definition interp_pure (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (tvs : agent → nat) (HM : gmap Z (nat * bv 8)) (LM : gmap nat wmsg)
      (DP : gmap nat nat) (RL : gmap (agent * nat) nat) : Prop :=
    tie_ok img log dl HM ∧ (∀ i, LM !! i = log !! i) ∧ dpos_ok dl DP ∧
    rl_ok log dl RL ∧ (∀ h, (tvs h ≤ length dl)%nat) ∧ dl_ok log dl ∧ fifo_ok log dl.

  (** The drain map's and the receipt map's persistent fragments are kept
      IN the interp: a drain is an environment step nobody's proof holds the
      fragment for, so the interp re-mints them on demand. *)
  Definition tso_interp (img : gmap Z (bv 8)) (log : list wmsg) (dl : list nat)
      (tvs : agent → nat) : iProp Σ :=
    (∃ (HM : gmap Z (nat * bv 8)) (LM : gmap nat wmsg) (DP : gmap nat nat)
       (RL : gmap (agent * nat) nat),
      ghost_map_auth γheap 1 HM ∗ ghost_map_auth γlogm 1 LM ∗
      ghost_map_auth γdpos 1 DP ∗ ([∗ map] i ↦ p ∈ DP, dpos_at i p) ∗
      ghost_map_auth γrl 1 RL ∗ ([∗ map] k ↦ M ∈ RL, k ↪[γrl]□ M) ∗
      mono_nat_auth_own γloglen 1 (length log) ∗
      mono_nat_auth_own γdlen 1 (length dl) ∗
      view_auth tvs ∗
      ⌜interp_pure img log dl tvs HM LM DP RL⌝)%I.

  (** What the evidence says at the machine: [t]'s message is the image or
      is drained under [B]. *)
  Lemma dpos_ev_vis img log dl tvs t B :
    tso_interp img log dl tvs -∗ dpos_ev t B -∗
    ⌜t = 0%nat ∨ ∃ i q, t = S i ∧ dl !! q = Some i ∧ (S q ≤ B)%nat⌝.
  Proof.
    iIntros "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iIntros "[%|[(%i & %p & -> & Hat & %Hp)|(%i & %A & %N & %M & -> & (%m & Ha & %Htid) & (Hr & _ & _) & %HiN & %HMB)]]".
    - by iLeft.
    - iDestruct (ghost_map_lookup with "Hdp Hat") as %HDP.
      apply Hdpo in HDP as (q & Hq & ->). iPureIntro. right. exists i, q. done.
    - iDestruct (ghost_map_lookup with "Hm Ha") as %HLMi. rewrite HLM in HLMi.
      iDestruct (ghost_map_lookup with "Hrl Hr") as %HRL.
      destruct (Hrlo _ _ _ HRL) as (_ & _ & Hall).
      destruct (Hall _ _ HiN HLMi Htid) as (q & Hq & HqM).
      iPureIntro. right. exists i, q. split_and!; [done|done|lia].
  Qed.

  Lemma dpos_ev_drained img log dl tvs i B :
    tso_interp img log dl tvs -∗ dpos_ev (S i) B -∗ ⌜i ∈ dl⌝.
  Proof.
    iIntros "Hint Hev". iDestruct (dpos_ev_vis with "Hint Hev") as %[?|(i' & q & [= <-] & Hq & _)];
      [done|]. iPureIntro. by eapply elem_of_list_lookup_2.
  Qed.

  (** The view receipt, minted at the hart's current view. *)
  Lemma twin_view_lb_get img log dl tvs h :
    tso_interp img log dl tvs -∗ tso_interp img log dl tvs ∗ view_lb h (tvs h).
  Proof.
    iIntros "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iDestruct (view_auth_frag tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hdlen") as "#Hlb".
    iSplitL; last first.
    { iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs. }
    iExists HM, LM, DP, RL. iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv".
    iPureIntro. by split_and!.
  Qed.

  (** The machine's view advance (a load's choice of view). *)
  Lemma twin_view_advance img log dl tvs h tv' :
    (tvs h ≤ tv')%nat → (tv' ≤ length dl)%nat →
    tso_interp img log dl tvs ==∗
    tso_interp img log dl (λ h0, if decide (h0 = h) then tv' else tvs h0).
  Proof.
    iIntros (Hle Htop) "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iMod (view_auth_update tvs (λ h0, if decide (h0 = h) then tv' else tvs h0)
            with "Hv") as "Hv".
    { intros h0. destruct (decide (h0 = h)); [subst; lia | lia]. }
    iModIntro. iExists HM, LM, DP, RL. iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv".
    iPureIntro. split_and!; try done.
    intros h0. destruct (decide (h0 = h)); [lia | apply Htvs].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 7. Gate lemma: LOAD                                           *)
  (* ---------------------------------------------------------------- *)

  Lemma twin_load_ok img log dl tvs ξ h a dq v :
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_pointsto ξ a dq v -∗
    ⌜∀ tv', (tvs h ≤ tv')%nat →
       tso_read (img_fun img) log dl h tv' a = Some v⌝.
  Proof.
    iIntros "Hint Hrun (%t & Hpt & #Hbit)".
    iDestruct "Hrun" as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & _ & _ & #Hoks)".
    (* the visibility of [t]'s message, from either arm *)
    iAssert (⌜t = 0%nat ∨ (∃ i q, t = S i ∧ dl !! q = Some i ∧ (S q ≤ B)%nat) ∨
              (∃ i m, t = S i ∧ log !! i = Some m ∧ wm_tid m = h)⌝)%I as %Hvis.
    { iDestruct "Hbit" as "[(%p & Hev & Hlb)|Hdt]".
      - iDestruct (mono_nat_lb_own_valid with "Hb Hlb") as %[_ HpB].
        iDestruct (dpos_ev_vis with "Hint Hev") as %[->|(i & q & -> & Hq & Hle)].
        + iPureIntro. by left.
        + iPureIntro. right; left. exists i, q. split_and!; [done|done|lia].
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct ("Hoks" $! (t, a) HDt) as "[Hev|(%i & %Hti & (%m & Ha & %Htid))]".
        + iDestruct (dpos_ev_vis with "Hint Hev") as %[Ht0|(i & q & Hti' & Hq & Hle)].
          * simpl in Ht0. subst t. iPureIntro. by left.
          * simpl in Hti'. subst t. iPureIntro. right; left. exists i, q. done.
        + iDestruct "Hint" as "(%HM & %LM & %DP & %RL & Hh & Hm & _ & _ & _ & _ & _ & _ & _ & %Hp)".
          iDestruct (ghost_map_lookup with "Hm Ha") as %HLMi.
          destruct Hp as (_ & HLM & _). rewrite HLM in HLMi.
          iPureIntro. right; right. simpl in Hti. exists i, m. done. }
    iDestruct "Hint" as "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    destruct (Htie _ _ _ HHa) as [Hlat Hc].
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    iPureIntro. move => tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ _ t v Hok Hf Hlat Hc).
    destruct Hvis as [->|[(i & q & -> & Hq & Hle)|(i & m & -> & Hi & Htid)]].
    - by left.
    - right. have Hlt := dl_lookup_lt _ _ _ _ Hok Hq.
      destruct (lookup_lt_is_Some_2 log i Hlt) as [m Hm].
      exists i, m. split_and!; [done|done|]. left. exists q. split; [done|lia].
    - right. exists i, m. split_and!; [done|done|by right].
  Qed.

  Lemma twin_view_valid img log dl tvs h K :
    tso_interp img log dl tvs -∗ view_lb h K -∗
    tso_interp img log dl tvs ∗ ⌜(K ≤ tvs h)%nat⌝.
  Proof.
    iIntros "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp) #HK".
    iDestruct (view_auth_valid with "Hv HK") as %?.
    iSplitL "Hh Hm Hdp Hrl Hlen Hdlen Hv"; [|by iPureIntro].
    iExists HM, LM, DP, RL. iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 8. Gate lemma: STORE                                          *)
  (* ---------------------------------------------------------------- *)

  (** The fact's bit says the previous latest write is drained or [h]'s
      own -- the pure half of the gate, [drained_or_by]. *)
  Lemma twin_store_gate img log dl tvs ξ h a dq v :
    tso_interp img log dl tvs -∗ own_context ξ h -∗ ctx_pointsto ξ a dq v -∗
    tso_interp img log dl tvs ∗ own_context ξ h ∗
    ∃ t, a ↪[γheap]{dq} (t, v) ∗ ⌜drained_or_by log dl h t⌝.
  Proof.
    iIntros "Hint Hrun (%t & Hpt & #Hbit)".
    iAssert (⌜drained_or_by log dl h t⌝)%I as %Hgate.
    { iDestruct "Hrun" as "(%B & %K & %W & %D & [Hb Hd] & _ & _ & _ & _ & #Hoks)".
      iDestruct "Hbit" as "[(%p & #Hev & _)|#Hdt]".
      - destruct t as [|j]; first by (iPureIntro; move => j mj).
        iDestruct (dpos_ev_drained with "Hint Hev") as %Hin.
        iPureIntro. move => j' mj [= <-] _. by left.
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct ("Hoks" $! (t, a) HDt) as "[#Hev|(%i & %Hti & (%m & #Ha & %Htid))]".
        + destruct t as [|j]; first by (iPureIntro; move => j mj).
          iDestruct (dpos_ev_drained with "Hint Hev") as %Hin.
          iPureIntro. move => j' mj [= <-] _. by left.
        + simpl in Hti. subst t.
          iDestruct "Hint" as "(%HM & %LM & %DP & %RL & Hh & Hm & _ & _ & _ & _ & _ & _ & _ & %Hp)".
          iDestruct (ghost_map_lookup with "Hm Ha") as %HLMi.
          destruct Hp as (_ & HLM & _). rewrite HLM in HLMi.
          iPureIntro. move => j' mj [= <-] Hj'. right. congruence. }
    iFrame "Hint Hrun". iExists t. by iFrame "Hpt".
  Qed.

  Lemma twin_store_ok img log dl tvs ξ h a v w :
    tso_interp img log dl tvs -∗ own_context ξ h -∗
    ctx_pointsto ξ a (DfracOwn 1) v ==∗
    tso_interp img (store_log log h a [w]) dl tvs ∗ own_context ξ h ∗
    ctx_pointsto ξ a (DfracOwn 1) w.
  Proof.
    iIntros "Hint Hrun Hpt".
    iDestruct (twin_store_gate with "Hint Hrun Hpt") as "(Hint & Hrun & %t & Hpt & %Hgate)".
    iDestruct "Hint" as "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iDestruct "Hrun" as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct (ghost_map_lookup with "Hh Hpt") as %HHa.
    destruct (Htie _ _ _ HHa) as [Hlat Hc].
    set (m := WMsg a [w] h). set (t' := S (length log)).
    iMod (ghost_map_update (t', w) with "Hh Hpt") as "[Hh Hpt]".
    iDestruct (nlb_valid with "Hlen HW") as %HWlen.
    have HLMfresh : LM !! length log = None.
    { rewrite HLM. apply lookup_ge_None_2. lia. }
    iMod (ghost_map_insert_persist (length log) m HLMfresh with "Hm") as "[Hm #Hlogm]".
    iMod (mono_nat_own_update (length (store_log log h a [w])) with "Hlen")
      as "[Hlen #Hlen']".
    { rewrite /store_log length_app /=. lia. }
    iMod (dset_insert _ D (t', a) with "Hd") as "[Hd #Hdt']".
    iModIntro.
    iSplitR "Hb Hd Hpt"; last first.
    { iSplitR "Hpt"; last first.
      { iExists t'. iFrame "Hpt". iRight. iExact "Hdt'". }
      iExists B, K, t', (D ∪ {[(t', a)]}). iFrame "Hb Hd HK".
      iSplitR; first done.
      iSplitR.
      { iLeft. iApply (mono_nat_lb_own_le with "Hlen'").
        rewrite /store_log length_app /=. lia. }
      iSplitR.
      { iPureIntro. intros k Hk. apply elem_of_union in Hk as [Hk|Hk].
        - have := HDW _ Hk. lia.
        - apply elem_of_singleton in Hk. subst k. simpl. lia. }
      iApply (dirty_all_insert with "[] Hoks").
      iRight. iExists (length log). iSplit; first done. iExists m. iFrame "Hlogm". done. }
    iExists (<[a := (t', w)]> HM), (<[length log := m]> LM), DP, RL.
    iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv".
    iPureIntro.
    have Hdlok' : dl_ok (store_log log h a [w]) dl by apply dl_ok_app_log.
    split_and!.
    - intros a0 t0 v0. destruct (decide (a0 = a)) as [->|Hne].
      + rewrite lookup_insert. intros [= <- <-]. split.
        * apply latest_app_new.
        * exact (chain_ok_new (img_fun img) log dl a t v h w Hok Hf Hlat Hc Hgate).
      + rewrite lookup_insert_ne; last congruence. intros HH0.
        destruct (Htie _ _ _ HH0) as [Hl0 Hc0]. split.
        * apply latest_app_frame; [by apply msg_byte_singleton_ne|done].
        * apply chain_ok_app_log; [|done]. destruct Hl0 as [Hb0 _]. by eapply log_byte_some_le.
    - intros i. rewrite /store_log. destruct (decide (i = length log)) as [->|Hne].
      + rewrite lookup_insert. symmetry. by apply list_lookup_middle.
      + rewrite lookup_insert_ne; last congruence. rewrite HLM.
        destruct (decide (i < length log)%nat) as [Hlt|Hge].
        * by rewrite lookup_app_l.
        * rewrite !lookup_ge_None_2 //; rewrite ?length_app /=; lia.
    - done.
    - by apply rl_ok_app_log.
    - done.
    - done.
    - by apply fifo_ok_app_log.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 9. The environment step: DRAIN                                *)
  (* ---------------------------------------------------------------- *)

  (** Nothing any client holds moves: the heap tie, the log fragments and
      the view stay; the drain map gains a persistent entry, the drain
      length grows, every byte's chain survives. *)
  Lemma twin_drain img log dl tvs k :
    drain_ok log dl k →
    tso_interp img log dl tvs ==∗ tso_interp img log (dl ++ [k]) tvs.
  Proof.
    iIntros (Hdr) "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    destruct (dpos_ok_drain _ _ _ _ Hok Hdr Hdpo) as [HDPk Hdpo'].
    iMod (ghost_map_insert_persist k (S (length dl)) HDPk with "Hdp") as "[Hdp #Hk]".
    iMod (mono_nat_own_update (length (dl ++ [k])) with "Hdlen") as "[Hdlen _]".
    { rewrite length_app /=. lia. }
    iModIntro. iExists HM, LM, (<[k := S (length dl)]> DP), RL.
    iFrame "Hh Hm Hdp Hrl Hrls Hlen Hdlen Hv".
    iSplitR.
    { rewrite big_sepM_insert //. iFrame "Hk Hdps". }
    iPureIntro. split_and!.
    - intros a t v Ha. destruct (Htie _ _ _ Ha) as [Hl Hc]. split; [done|].
      by eapply (chain_ok_drain (img_fun img)).
    - done.
    - done.
    - by apply rl_ok_drain.
    - intros h. rewrite length_app /=. have := Htvs h. lia.
    - by apply drain_dl_ok.
    - by apply fifo_ok_drain.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 10. The release fence: the receipt is born                     *)
  (* ---------------------------------------------------------------- *)

  (** At a fence with a W predecessor the machine has waited for every own
      store to drain ([own_drained]); the leaf mints [drain_lb h N M] with
      [N] the issue length and [M] the drain length, and -- holding the
      record's dirty watermark [W] -- proves [W ≤ N] for the acquirer. *)
  Lemma twin_fence_rel img log dl tvs h W :
    own_drained h log dl →
    tso_interp img log dl tvs -∗ llb W ==∗
    tso_interp img log dl tvs ∗
    ∃ N M, drain_lb h N M ∗ ⌜(W ≤ N)%nat⌝.
  Proof.
    iIntros (Hod) "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp) #HW".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iDestruct (nlb_valid with "Hlen HW") as %HWlen.
    iDestruct (mono_nat_lb_own_get with "Hlen") as "#HlenLb".
    iDestruct (mono_nat_lb_own_get with "Hdlen") as "#HdlenLb".
    destruct (RL !! (h, length log)) as [M'|] eqn:HRL.
    - iDestruct (big_sepM_lookup _ _ _ _ HRL with "Hrls") as "#Hr".
      destruct (Hrlo _ _ _ HRL) as (_ & HM' & _).
      iModIntro. iSplitL.
      { iExists HM, LM, DP, RL. iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv".
        iPureIntro. by split_and!. }
      iExists (length log), M'. iSplitR; [|done]. iFrame "Hr HlenLb".
      by iApply (mono_nat_lb_own_le with "HdlenLb").
    - iMod (ghost_map_insert_persist (h, length log) (length dl) HRL with "Hrl")
        as "[Hrl #Hr]".
      iModIntro. iSplitL.
      { iExists HM, LM, DP, (<[(h, length log) := length dl]> RL).
        iFrame "Hh Hm Hdp Hdps Hrl Hlen Hdlen Hv".
        iSplitR. { rewrite big_sepM_insert //. iFrame "Hr Hrls". }
        iPureIntro. split_and!; try done. by apply rl_ok_mint. }
      iExists (length log), (length dl). iSplitR; [|done]. iFrame "Hr HlenLb HdlenLb".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 11. The acquire leaf: placing the stamps under the view        *)
  (* ---------------------------------------------------------------- *)

  (** The one place the parked record's stamp and the receipt's [M] meet an
      authority: the acquirer sits at the drain top, so both are under its
      view.  Yields the stable facts [twin_resume] consumes. *)
  Lemma twin_passed_get img log dl tvs h B A N M :
    (length dl ≤ tvs h)%nat →
    tso_interp img log dl tvs -∗ dlb B -∗ drain_lb A N M -∗
    tso_interp img log dl tvs ∗ view_lb h (tvs h) ∗ ⌜(B ≤ tvs h)%nat⌝ ∗ ⌜(M ≤ tvs h)%nat⌝.
  Proof.
    iIntros (Htop) "Hint #HB #(Hr & HMlb & HNlb)".
    iDestruct "Hint" as "(%HM & %LM & %DP & %RL & Hh & Hm & Hdp & #Hdps & Hrl & #Hrls & Hlen & Hdlen & Hv & %Hp)".
    destruct Hp as (Htie & HLM & Hdpo & Hrlo & Htvs & Hok & Hf).
    iDestruct (nlb_valid with "Hdlen HB") as %HBlen.
    iDestruct (mono_nat_lb_own_valid with "Hdlen HMlb") as %[_ HMlen].
    iDestruct (view_auth_frag tvs h (tvs h) with "Hv") as "#Hf"; first done.
    iDestruct (mono_nat_lb_own_get with "Hdlen") as "#Hlb".
    iSplitL.
    { iExists HM, LM, DP, RL. iFrame "Hh Hm Hdp Hdps Hrl Hrls Hlen Hdlen Hv".
      iPureIntro. by split_and!. }
    iSplitR; last (iPureIntro; lia).
    iLeft. iFrame "Hf". iApply (mono_nat_lb_own_le with "Hlb"). apply Htvs.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 12. PARK / RESUME / EXCHANGE                                  *)
  (* ---------------------------------------------------------------- *)

  (** PARK is free: the bound stays, the dirty entries stay dirty, the
      record names the parking hart as their author.  The parker keeps
      [llb W] for its release fence. *)
  Lemma twin_park ξ h :
    own_context ξ h -∗ ∃ B W, ctx_parked ξ B W h ∗ llb W.
  Proof.
    iIntros "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iExists B, W. iSplitL "Hat"; last iExact "HW".
    iExists D. iFrame "Hat". iSplitR.
    { iApply (nlb_le with "[]"); [exact HBK|]. by iApply view_lb_dlb. }
    iFrame "HW Hoks". by iPureIntro.
  Qed.

  (** RESUME: the stable facts -- the resumer's view receipt above the
      record's bound and above the receipt's [M], and the receipt covering
      the record's dirty watermark.  Every dirty entry is re-justified as
      drained under the new bound, the resumer's view. *)
  Lemma twin_resume ξ B W A h K N M :
    (B ≤ K)%nat → (M ≤ K)%nat → (W ≤ N)%nat →
    view_lb h K -∗ drain_lb A N M -∗ ctx_parked ξ B W A ==∗ own_context ξ h.
  Proof.
    iIntros (HBK HMK HWN) "#HK #Hr (%D & [Hb Hd] & #HB & #HW & %HDW & #Hoks)".
    iMod (mono_nat_own_update K with "Hb") as "[Hb _]"; first done.
    iModIntro. iExists K, K, W, D. iFrame "Hb Hd HK HW".
    iSplitR; first done. iSplitR; first done.
    iIntros "!> %k %Hk". iLeft.
    iDestruct ("Hoks" $! k Hk) as "[Hev|(%i & %Hki & #Ha)]".
    - iApply (dpos_ev_mono _ B K HBK with "Hev").
    - have HiN : (i < N)%nat by have := HDW _ Hk; lia.
      iRight; iRight. iExists i, A, N, M. iFrame "Ha Hr". iPureIntro. by split_and!.
  Qed.

  Lemma twin_exchange ξ1 ξ2 B W A h K N M :
    (B ≤ K)%nat → (M ≤ K)%nat → (W ≤ N)%nat →
    view_lb h K -∗ drain_lb A N M -∗ own_context ξ1 h -∗ ctx_parked ξ2 B W A ==∗
    own_context ξ2 h ∗ ∃ B1 W1, ctx_parked ξ1 B1 W1 h ∗ llb W1.
  Proof.
    iIntros (HBK HMK HWN) "#HK #Hr Hrun Hpk".
    iDestruct (twin_park with "Hrun") as (B1 W1) "[Hpk1 #HW1]".
    iMod (twin_resume with "HK Hr Hpk") as "Hrun2"; [done|done|done|].
    iModIntro. iFrame "Hrun2". iExists B1, W1. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 13. TRANSPORT: [CtxMorph], bare shape, at the indexed dom      *)
  (* ---------------------------------------------------------------- *)

  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ A' ξ ξ', ctx_dom A' ξ ξ' -∗ R ξ ==∗ ctx_dom A' ξ ξ' ∗ R ξ'.

  Global Instance ctx_morph_pointsto a dq v :
    CtxMorph (λ ξ, ctx_pointsto ξ a dq v).
  Proof.
    iIntros (A' ξ ξ') "(%B & %W & %B' & %A & %W' & %D & %D' & [Hb Hd] & %HDW & %HBB' & #Hlb' & #Hoks & Hd' & #HW' & %HD'W' & %HWW' & #Hoks' & #Hconv)".
    iIntros "(%t & Hpt & #Hbit)".
    iDestruct "Hbit" as "[(%p & #Hev & #Hlb)|#Hdt]".
    - (* clean: p ≤ B ≤ B' *)
      iDestruct (mono_nat_lb_own_valid with "Hb Hlb") as %[_ HpB].
      iModIntro. iSplitL "Hb Hd Hd'".
      { iExists B, W, B', A, W', D, D'. iFrame "Hb Hd Hlb' Hoks Hd' HW' Hoks' Hconv".
        iPureIntro. by split_and!. }
      iExists t. iFrame "Hpt". iLeft. iExists B'. iFrame "Hlb'".
      iApply (dpos_ev_mono with "Hev"). lia.
    - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
      iDestruct ("Hoks" $! (t, a) HDt) as "#[Hev|(%i & %Hti & #Ha)]"; simpl in *.
      + (* drained under B: clean at ξ' *)
        iModIntro. iSplitL "Hb Hd Hd'".
        { iExists B, W, B', A, W', D, D'. iFrame "Hb Hd Hlb' Hoks Hd' HW' Hoks' Hconv".
          iPureIntro. by split_and!. }
        iExists t. iFrame "Hpt". iLeft. iExists B'. iFrame "Hlb'".
        iApply (dpos_ev_mono with "Hev"). lia.
      + iDestruct "Hconv" as "[%HAA|(%N & %M & #Hr & %HWN & %HMB')]".
        * (* same author: re-registered dirty at ξ' *)
          subst A'.
          iMod (dset_insert _ D' (t, a) with "Hd'") as "[Hd' #Hdt']".
          iModIntro. iSplitL "Hb Hd Hd'".
          { iExists B, W, B', A, W', D, (D' ∪ {[(t, a)]}). iFrame "Hb Hd Hlb' Hoks Hd' HW'".
            iSplitR; first done. iSplitR; first done.
            iSplitR.
            { iPureIntro. intros k Hk. apply elem_of_union in Hk as [Hk|Hk]; [by apply HD'W'|].
              apply elem_of_singleton in Hk. subst k. have := HDW _ HDt. simpl. lia. }
            iSplitR; first done.
            iSplitR.
            { iApply (dirty_all_insert with "[] Hoks'"). iRight. iExists i. by iFrame "Ha". }
            by iLeft. }
          iExists t. iFrame "Hpt". iRight. iExact "Hdt'".
        * (* the receipt: clean at ξ' *)
          iModIntro. iSplitL "Hb Hd Hd'".
          { iExists B, W, B', A, W', D, D'. iFrame "Hb Hd Hlb' Hoks Hd' HW' Hoks'".
            iSplitR; first done. iSplitR; first done. iSplitR; first done.
            iSplitR; first done.
            iRight. iExists N, M. iFrame "Hr". by iPureIntro. }
          iExists t. iFrame "Hpt". iLeft. iExists B'. iFrame "Hlb'".
          iRight; iRight. iExists i, A, N, M. iFrame "Ha Hr".
          have HiN : (i < N)%nat by have := HDW _ HDt; simpl; lia.
          iPureIntro. repeat split; try done.
  Qed.

  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P) | 100.
  Proof. iIntros (A' ξ ξ') "Hd HP !>". iFrame. Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 A' ξ ξ') "Hd [HR1 HR2]".
    iMod (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iMod (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ A' ξ ξ') "Hd [%x HR]".
    iMod (ctx_morph with "Hd HR") as "[Hd HR]".
    iModIntro. iFrame "Hd". iExists x. iExact "HR".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 14. The dom mints                                             *)
  (* ---------------------------------------------------------------- *)

  (** SAME-HART MINT (fork deposit, release): the running source lends
      half of itself, the parked target lends its whole dirty authority.
      The target comes back at the give-back with its bound raised to cover
      the source's and its watermark raised to cover the source's keys. *)
  Lemma ctx_dom_to_parked ξ ξ' h B' W' :
    own_context ξ h -∗ ctx_parked ξ' B' W' h ==∗
    ctx_dom h ξ ξ' ∗
    (ctx_dom h ξ ξ' -∗ own_context ξ h ∗
       ∃ B'' W'', ⌜(B' ≤ B'')%nat⌝ ∗ ctx_parked ξ' B'' W'' h).
  Proof.
    iIntros "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iIntros "(%D' & [Hb' Hd'] & #HB' & #HW' & %HD'W' & #Hoks')".
    set (B'' := Nat.max B' B). set (W'' := Nat.max W' W).
    iMod (mono_nat_own_update B'' with "Hb'") as "[Hb' #Hlb'']"; first lia.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iModIntro.
    iSplitL "Hat1 Hd'".
    { iExists B, W, B'', h, W'', D, D'. iFrame "Hat1 Hd' Hlb'' Hoks".
      iSplitR; first done. iSplitR; first (iPureIntro; lia).
      iSplitR; first by iApply (nlb_max with "HW' HW").
      iSplitR. { iPureIntro. intros k Hk. have := HD'W' _ Hk. lia. }
      iSplitR; first (iPureIntro; lia).
      iSplitR. { iApply (dirty_all_mono with "Hoks'"). lia. }
      by iLeft. }
    (* the give-back *)
    iIntros "(%B0 & %W0 & %B0' & %A0 & %W0' & %D0 & %D0' & Hat0 & _ & _ & #Hlb0' & _ & Hd0' & #HW0' & %HD0' & _ & #Hoks0' & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iDestruct (mono_nat_lb_own_valid with "Hb' Hlb0'") as %[_ HB0'].
    iSplitL "Hat".
    { iExists B, K, W, D. iFrame "Hat HK HW Hoks". by iPureIntro. }
    iExists B'', W0'. iSplitR; first (iPureIntro; lia).
    iExists D0'. iFrame "Hb' Hd0' HW0'".
    iSplitR.
    { iApply (nlb_max with "HB' []"). iApply (nlb_le with "[]"); [exact HBK|]. by iApply view_lb_dlb. }
    iSplitR; first done.
    iApply (dirty_all_mono with "Hoks0'"). lia.
  Qed.

  (** ACQUIRE-SIDE MINT: domination FROM a parked source INTO the running
      acquirer, whose hart sits at the drain top.  The receipt covers the
      source's dirty watermark ([W ≤ N], the releaser's fact); [M] and the
      source's bound are placed under the acquirer's view here. *)
  Lemma ctx_dom_of_parked img log dl tvs ξ ξ' h B W A N M :
    (length dl ≤ tvs h)%nat → (W ≤ N)%nat →
    tso_interp img log dl tvs -∗ own_context ξ' h -∗ ctx_parked ξ B W A -∗
    drain_lb A N M ==∗
    tso_interp img log dl tvs ∗ ctx_dom h ξ ξ' ∗
    (ctx_dom h ξ ξ' -∗ own_context ξ' h ∗ ctx_parked ξ B W A).
  Proof.
    iIntros (Htop HWN) "Hint Hrun Hpk #Hr".
    iDestruct "Hpk" as "(%D & Hat & #HB & #HW & %HDW & #Hoks)".
    iDestruct (twin_passed_get with "Hint HB Hr") as "(Hint & #HKt & %HBK & %HMK)"; first done.
    iDestruct "Hrun" as "(%B' & %K & %W' & %D' & [Hb' Hd'] & #HK & %HB'K & #HW' & %HD'W' & #Hoks')".
    iDestruct (twin_view_valid with "Hint HK") as "[Hint %HKtvs]".
    iMod (mono_nat_own_update (tvs h) with "Hb'") as "[Hb' #Hlb']"; first lia.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    set (W'' := Nat.max W' W).
    iModIntro. iFrame "Hint".
    iSplitL "Hat1 Hd'".
    { iExists B, W, (tvs h), A, W'', D, D'. iFrame "Hat1 Hd' Hlb' Hoks".
      iSplitR; first done. iSplitR; first done.
      iSplitR; first by iApply (nlb_max with "HW' HW").
      iSplitR. { iPureIntro. intros k Hk. have := HD'W' _ Hk. lia. }
      iSplitR; first (iPureIntro; lia).
      iSplitR. { iApply (dirty_all_mono with "Hoks'"). lia. }
      iRight. iExists N, M. iFrame "Hr". iPureIntro. split; [done|lia]. }
    iIntros "(%B0 & %W0 & %B0' & %A0 & %W0' & %D0 & %D0' & Hat0 & _ & _ & #Hlb0' & _ & Hd0' & #HW0' & %HD0' & _ & #Hoks0' & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat". rewrite -ctx_at_halves.
    iDestruct (mono_nat_lb_own_valid with "Hb' Hlb0'") as %[_ HB0'].
    iSplitL "Hb' Hd0'".
    { iExists (tvs h), (tvs h), W0', D0'. iFrame "Hb' Hd0' HKt HW0'".
      iSplitR; first done. iSplitR; first done.
      iApply (dirty_all_mono with "Hoks0'"). lia. }
    iExists D. iFrame "Hat HB HW Hoks". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 15. FORK and DEPOSIT                                          *)
  (* ---------------------------------------------------------------- *)

  (** The child is born PARKED at bound 0 with nothing dirty, its gnames
      fresh, the parent named as its author. *)
  Lemma twin_fork ξ h :
    own_context ξ h ==∗ own_context ξ h ∗ ∃ ξc, ctx_parked ξc 0 0 h.
  Proof.
    iIntros "Hrun".
    iMod (mono_nat_own_alloc 0) as (γb) "[Hbc _]".
    iMod dset_alloc as (γd) "Hdc".
    iModIntro. iFrame "Hrun". iExists (MkCtxId γb γd), ∅. iFrame "Hbc Hdc".
    iSplitR; first by iApply nlb_0. iSplitR; first by iApply nlb_0.
    iSplitR; first (iPureIntro; set_solver). iApply dirty_all_empty.
  Qed.

  Lemma twin_parked_alloc A : ⊢ |==> ∃ ξc, ctx_parked ξc 0 0 A.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), ∅. iFrame "Hb Hd".
    iSplitR; first by iApply nlb_0. iSplitR; first by iApply nlb_0.
    iSplitR; first (iPureIntro; set_solver). iApply dirty_all_empty.
  Qed.

  Lemma twin_run_alloc h : ⊢ |==> ∃ ξ, own_context ξ h.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd), 0%nat, 0%nat, 0%nat, ∅. iFrame "Hb Hd".
    iSplitR; first by iApply view_lb_0.
    iSplitR; first done.
    iSplitR; first by iApply nlb_0.
    iSplitR; first (iPureIntro; set_solver).
    iApply dirty_all_empty.
  Qed.

  (** THE GENERAL DEPOSIT: a running context hands any morphable payload to
      a parked one of the same hart. *)
  Lemma twin_deposit (R : CtxId → iProp Σ) `{!CtxMorph R} ξ ξc h B' W' :
    own_context ξ h -∗ ctx_parked ξc B' W' h -∗ R ξ ==∗
    own_context ξ h ∗
    ∃ B'' W'', ⌜(B' ≤ B'')%nat⌝ ∗ ctx_parked ξc B'' W'' h ∗ R ξc.
  Proof.
    iIntros "Hrun Hpk HR".
    iMod (ctx_dom_to_parked with "Hrun Hpk") as "[Hdom Hback]".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iDestruct ("Hback" with "Hdom") as "[Hrun (%B'' & %W'' & % & Hpk)]".
    iModIntro. iFrame "Hrun". iExists B'', W''. by iFrame.
  Qed.

  (** THE ACID TEST: the parent hands the child a byte fact -- clean OR
      dirty (pending!), any fraction -- with nothing to prove. *)
  Lemma twin_fork_deposit ξ h a dq v :
    own_context ξ h -∗ ctx_pointsto ξ a dq v ==∗
    own_context ξ h ∗ ∃ ξc B W, ctx_parked ξc B W h ∗ ctx_pointsto ξc a dq v.
  Proof.
    iIntros "Hrun Hpt".
    iMod (twin_fork with "Hrun") as "[Hrun (%ξc & Hpk)]".
    iMod (twin_deposit (λ ξ0, ctx_pointsto ξ0 a dq v) with "Hrun Hpk Hpt")
      as "[Hrun (%B & %W & _ & Hpk & Hpt)]".
    iModIntro. iFrame "Hrun". iExists ξc, B, W. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 16. The dq law surface                                        *)
  (* ---------------------------------------------------------------- *)

  Lemma ctx_pointsto_agree ξ1 ξ2 a dq1 v1 dq2 v2 :
    ctx_pointsto ξ1 a dq1 v1 -∗ ctx_pointsto ξ2 a dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "(%t1 & H1 & _) (%t2 & H2 & _)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= _ ->]. done.
  Qed.

  Lemma ctx_pointsto_ne ξ1 ξ2 a1 a2 dq v1 v2 :
    ctx_pointsto ξ1 a1 (DfracOwn 1) v1 -∗ ctx_pointsto ξ2 a2 dq v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "(%t1 & H1 & _) (%t2 & H2 & _)".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  (** Both arms of the bit are persistent, so a fraction split is a split
      of the heap element alone. *)
  Lemma ctx_pointsto_frac_split ξ a q1 q2 v :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) v ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) v ∗ ctx_pointsto ξ a (DfracOwn q2) v.
  Proof.
    iSplit.
    - iIntros "(%t & [Hpt1 Hpt2] & #Hbit)".
      iSplitL "Hpt1"; iExists t; by iFrame "Hbit".
    - iIntros "[(%t1 & Hpt1 & #Hbit1) (%t2 & Hpt2 & _)]".
      iDestruct (ghost_map_elem_combine with "Hpt1 Hpt2") as "[Hpt %Heq]".
      injection Heq as <-. rewrite dfrac_op_own.
      iExists t1. by iFrame "Hpt Hbit1".
  Qed.

  Lemma ctx_pointsto_persist ξ a dq v :
    ctx_pointsto ξ a dq v ==∗ ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "(%t & Hpt & #Hbit)".
    iMod (ghost_map_elem_persist with "Hpt") as "Hpt".
    iModIntro. iExists t. by iFrame "Hpt Hbit".
  Qed.

  (** Cross-context sharing: transport COPIES a justification. *)
  Lemma twin_share A' ξ ξ' a v :
    ctx_dom A' ξ ξ' -∗ ctx_pointsto ξ a (DfracOwn 1) v ==∗
    ctx_dom A' ξ ξ' ∗ ctx_pointsto ξ a (DfracOwn (1/2)) v ∗
    ctx_pointsto ξ' a (DfracOwn (1/2)) v.
  Proof.
    iIntros "Hdom Hpt".
    rewrite -{1}(Qp.div_2 1) ctx_pointsto_frac_split.
    iDestruct "Hpt" as "[Hpt1 Hpt2]".
    iMod (ctx_morph (R := λ ξ0, ctx_pointsto ξ0 a (DfracOwn (1/2)) v)
            with "Hdom Hpt2") as "[Hdom Hpt2]".
    iModIntro. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 17. The image: every context can hold a timestamp-0 fact        *)
  (* ---------------------------------------------------------------- *)

  Lemma own_context_lb0 ξ h :
    own_context ξ h -∗ own_context ξ h ∗ mono_nat_lb_own (tc_bnd ξ) 0.
  Proof.
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct (mono_nat_lb_own_get with "Hb") as "#Hlb".
    iSplitL.
    { iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iApply (mono_nat_lb_own_le with "Hlb"). lia.
  Qed.

  Lemma ctx_pointsto_intro_zero ξ a dq v :
    a ↪[γheap]{dq} ((0%nat, v) : nat * bv 8) -∗
    mono_nat_lb_own (tc_bnd ξ) 0 -∗
    ctx_pointsto ξ a dq v.
  Proof.
    iIntros "Hpt #Hlb". iExists 0%nat. iFrame "Hpt". iLeft. iExists 0%nat.
    iFrame "Hlb". by iLeft.
  Qed.

End twin3.

(* ================================================================== *)
(** * 18. Satisfiability: the interp at the boot image                 *)
(* ================================================================== *)

Lemma twin3_init `{!tsoCtx3G Σ} (img : gmap Z (bv 8)) :
  ⊢ |==> ∃ γheap γlogm γdpos γrl γloglen γdlen γview,
      tso_interp γheap γlogm γdpos γrl γloglen γdlen γview img [] [] (λ _, 0%nat) ∗
      [∗ map] a ↦ v ∈ img, a ↪[γheap] ((0%nat, v) : nat * bv 8).
Proof.
  iMod (ghost_map_alloc ((λ v, (0%nat, v)) <$> img)) as (γheap) "[Hh Hfr]".
  iMod (ghost_map_alloc_empty (K := nat) (V := wmsg)) as (γlogm) "Hm".
  iMod (ghost_map_alloc_empty (K := nat) (V := nat)) as (γdpos) "Hdp".
  iMod (ghost_map_alloc_empty (K := agent * nat) (V := nat)) as (γrl) "Hrl".
  iMod (mono_nat_own_alloc 0) as (γloglen) "[Hlen _]".
  iMod (mono_nat_own_alloc 0) as (γdlen) "[Hdlen _]".
  iMod (own_alloc (● vf (λ _, 0%nat) ⋅ ◯ vf (λ _, 0%nat))) as (γview) "Hv".
  { apply auth_both_valid_discrete. split; [done | by intros h]. }
  iModIntro. iExists γheap, γlogm, γdpos, γrl, γloglen, γdlen, γview.
  iSplitR "Hfr"; last first.
  { iApply (big_sepM_impl with "[Hfr]").
    { by rewrite big_sepM_fmap. }
    iIntros "!>" (a v Hlk) "H". iExact "H". }
  iExists ((λ v, (0%nat, v)) <$> img), ∅, ∅, ∅.
  iFrame "Hh Hm Hdp Hrl Hlen Hdlen Hv".
  iSplitR; first by rewrite big_sepM_empty.
  iSplitR; first by rewrite big_sepM_empty.
  iPureIntro. split_and!.
  - intros a t v. rewrite lookup_fmap.
    destruct (img !! a) as [v0|] eqn:Ha; last done.
    simpl. intros [= <- <-]. split; [|apply chain_ok_0]. split.
    + rewrite /log_byte /img_fun Ha //.
    + intros t' Ht'. destruct t' as [|i]; first lia. rewrite /log_byte /=. done.
  - intros i. rewrite lookup_empty lookup_nil //.
  - intros i p. rewrite lookup_empty. split; [done|]. intros (q & Hq & _). rewrite lookup_nil in Hq. done.
  - intros A N M. rewrite lookup_empty. done.
  - intros h. simpl. lia.
  - split; [apply NoDup_nil_2|]. intros i Hi. by apply elem_of_nil in Hi.
  - intros i j mi mj qj _ _ _ _ _ Hq. rewrite lookup_nil in Hq. done.
Qed.

(** * WeakStarted.v — the [started] handoff, weak-memory form (M3b item 4)

    xv6's one unlocked cross-hart channel:

      volatile static int started = 0;
      main() { if (cpuid() == 0) { <all the init>; fence rw,rw; started = 1; }
               else              { while (started == 0) ; fence rw,rw; ... } }

    [StartedInv.v] gives it the SC reading: a one-shot escrow keyed on the
    word, [started_body P := ∃ v, started ↦₄ v ∗ (⌜v = 0⌝ ∨ P)], with a
    PERSISTENT payload (up to NCPU−1 readers take it, and the invariant is
    re-closed unchanged after each).

    THE WEAK READING KEEPS THAT SHAPE AND ADDS ONE NUMBER: the timestamp.  The
    escrow's right disjunct becomes [monPred_at P (view_scl t)] with [t] the
    timestamp of the flag's own message — the payload is frozen exactly where
    the writer's store put it.  The two machine-level fences, which are
    NO-OPS in the SC model, become the two halves of the transfer:

      WRITER  [fence rw,w] ; [sw]:  [WeakInstr.wwp_release_deposit] — every
        view the writer holds is below its store's own timestamp
        ([WeakMem.ws_bounded]), so the whole payload may be frozen at
        [view_scl (S (length log))] and handed to the escrow.  Promise-free,
        the fence carries no view content of its own; it is the STORE that
        publishes (design doc, Decision 1).
      READER  [lw] ; [fence rw,rw]:  the load raises [w_vrOld] to the
        timestamp it read ([WeakMem.load_post_vrOld_nofwd]) and the succ-R
        fence turns that into an index gain ([WeakInstr.wwp_fence_scl]), which
        thaws the payload into the reader's own index.  WITHOUT the fence the
        reader gets the flag's value and NOTHING else — which is exactly the
        MP litmus test this machine already forbids ([WeakLitmus]).

    ONE THING THE SC VERSION NEVER HAD TO SAY: a plain load may read a STALE
    message, so "I read a nonzero flag" does not by itself identify WHICH
    message was read.  It does once the escrow records that the flag is
    written once ([wstarted_oneshot]).

    ================== THE ONE-SHOT CONJUNCT (M4 batch 5) ==================

    §1's [wstarted_oneshot] is the SHAPE of that record, but it is not what
    the escrow can carry, and the three reasons are all worth writing down.

    (a) IT IS A WHOLE-LOG FACT, so it cannot be a pure conjunct of an
        invariant: the log grows under every hart's feet.  The escrow stores
        it CLIPPED, against a log SNAPSHOT ([WeakGhost.wlog_lb]), exactly as
        [WeakKpt] §1 stores the page-table closure, and the CURRENT-log form
        is derived at every use from the snapshot plus the escrow's own
        latest-write elements (nothing above the element's timestamp writes
        the byte).  [wstarted_lb_now] is that derivation.

    (b) THE EXACT-TIMESTAMP FORM IS NOT STABLE UNDER THE SETTER.  "every
        non-clear write is at [t]" cannot be re-established by
        [wstarted_set] from an ALREADY-SET escrow — the previous set's
        message is a non-clear write at the old timestamp — and
        [wstarted_set] has to hold for every escrow state, because nothing
        in [WeakAcquire.wwp_started_set] rations the setter.  What IS stable
        is a LOWER BOUND: every non-clear write is at a timestamp ≥ [T],
        with the payload frozen at [view_scl T].  That is all the reader
        needs (it must produce [P] at a view BELOW the timestamp it read),
        and a second set keeps the FIRST deposit, which is the stronger one.

    (c) TIMESTAMP 0 IS THE ERA IMAGE, and no [iProp] can name it.  The
        flag's timestamp-0 element WOULD say the image byte is clear — but
        that element is exactly what the setter retargets, and a second
        (discarded) element at the same address is unownable.  So the
        image half travels as a PURE side condition, [wstarted_img_clear],
        which the MINT hands out: minting the escrow from the flag's
        era-image elements ([wlat4 a 1 0 lock_zero], which is what boot has
        for a [.bss] word) proves it on the spot, and [wm_img] is constant
        along every step ([WeakInstr.wstep_post]), so it travels for free. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import iprop invariants ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakLock.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(** THE ONE-SHOT FACT.  Every write of a NON-CLEAR value to byte [a] is the
    escrow's own message at timestamp [t] (the era image holds the flag
    cleared — it is in .bss).  This is what makes "the value I read is
    nonzero" imply "the timestamp I read is [t]" for a PLAIN load. *)
Definition wstarted_oneshot (img : image) (log : list wmsg) (a : Z) (t : nat)
    : Prop :=
  forall (t' : nat) (b : bv 8),
    log_byte img log t' a = Some b -> b <> nth_byte lock_zero 0 -> t' = t.

(** It survives every append that does not write the byte — which is every
    step of every OTHER hart, since the escrow owns the byte's elements
    outright and nobody else can re-establish [wlat_interp] over them. *)
Lemma wstarted_oneshot_app img log ms a t :
  wstarted_oneshot img log a t ->
  (forall m, m ∈ ms -> msg_byte m a = None) ->
  wstarted_oneshot img (log ++ ms) a t.
Proof.
  intros Hone Hno t' b Hb Hne. apply (Hone t' b); [|exact Hne].
  destruct t' as [|i]; [exact Hb|].
  rewrite log_byte_S in Hb. rewrite log_byte_S.
  destruct ((log ++ ms)%list !! i) as [m|] eqn:Hl; [|by simpl in Hb].
  simpl in Hb.
  apply lookup_app_Some in Hl as [Hl2|[_ Hms]].
  - rewrite Hl2 /=. exact Hb.
  - exfalso. rewrite (Hno m (elem_of_list_lookup_2 _ _ _ Hms)) in Hb.
    discriminate.
Qed.

(* ====================================================================== *)
(** ** 1b. THE STORABLE FORM: a lower bound on the non-clear writes

    The two halves of the one-shot fact, split along the seam that decides
    where each can live (header (a)–(c)).

    [wstarted_lb log a T] is the LOG half: every MESSAGE of [log] that writes
    a non-clear byte anywhere in the flag word does so at a timestamp at or
    above [T], and writes the SETTER's byte there.  It never consults the
    image (a message timestamp is ≥ 1), so it is an honest pure conjunct of
    an [iProp] invariant once a snapshot pins [log].

    [wstarted_img_clear σ a] is the IMAGE half: the era image holds the flag
    cleared.  It IS about [σ], hence not storable; it is minted with the
    escrow and carried as a side condition. *)

Definition wstarted_lb (log : list wmsg) (a : Arch.pa) (T : nat) : Prop :=
  forall (j i : nat) (m : wmsg) (b : bv 8),
    (j < 4)%nat ->
    log !! i = Some m ->
    msg_byte m (acc_addr a j) = Some b ->
    b <> nth_byte lock_zero 0 ->
    (T <= S i)%nat /\ b = nth_byte lock_one j.

Definition wstarted_img_clear (σ : wmstate) (a : Arch.pa) : Prop :=
  forall j : nat, (j < 4)%nat ->
    wimg σ (acc_addr a j) = Some (nth_byte lock_zero j).

(** Every byte of the cleared word is THE clear byte — so "non-clear" may be
    stated once, at byte 0, and used at all four. *)
Lemma nth_byte_clear (j : nat) :
  (j < 4)%nat -> nth_byte lock_zero j = nth_byte lock_zero 0.
Proof.
  intros Hj. destruct j as [|[|[|[|j]]]]; [reflexivity| | | |lia];
    apply bv_eq; vm_compute; reflexivity.
Qed.

(** Two log lower bounds are comparable — the mono-list's own property, and
    what lets the escrow's snapshot be read against the CURRENT log with no
    authority in hand (a persistent [wlog_lb] of the current log is all a
    consumer needs, and every [wmstate_interp] hands one out for free). *)
Lemma prefix_either_lookup {A : Type} (l1 l2 : list A) (i : nat) (x : A) :
  (l1 `prefix_of` l2 \/ l2 `prefix_of` l1) ->
  l2 !! i = Some x -> (i < length l1)%nat -> l1 !! i = Some x.
Proof.
  intros [[k ->]|[k ->]] Hx Hi.
  - rewrite (lookup_app_l l1 k i Hi) in Hx. exact Hx.
  - apply lookup_lt_Some in Hx as Hlt.
    rewrite (lookup_app_l l2 k i Hlt). exact Hx.
Qed.

(** THE EXTENSION, pure half: the snapshot's bound, the escrow's element and
    the log comparison give the bound over the CURRENT log.

    The three cases of [i] are the whole argument: below the snapshot the
    stored fact applies; above the element's timestamp nothing writes the
    byte at all; and AT the element's timestamp the write is the escrow's
    own, whose value the element names. *)
Lemma wstarted_lb_now (img : image) (log log0 : list wmsg) (a : Arch.pa)
    (T t : nat) (v : bv 32) :
  (t <= S (length log0))%nat ->
  wstarted_lb log0 a T ->
  (log0 `prefix_of` log \/ log `prefix_of` log0) ->
  (forall k : nat, (k < 4)%nat ->
     latest_val img log (acc_addr a k) t (nth_byte v k)) ->
  ((v = lock_zero /\ (length log0 < T)%nat) \/ (v = lock_one /\ (T <= t)%nat)) ->
  wstarted_lb log a T.
Proof.
  intros Hcov Hlb Hcmp Hlv Hdisj j i m b Hj Hm Hbb Hne.
  assert (Hbyte : log_byte img log (S i) (acc_addr a j) = Some b)
    by (rewrite log_byte_S Hm /=; exact Hbb).
  assert (Hilt : (i < length log)%nat) by (by eapply lookup_lt_Some).
  (* nothing above the element's timestamp writes the byte *)
  assert (Hle : (S i <= t)%nat).
  { destruct (decide (S i <= t)%nat) as [?|Hgt]; [assumption|exfalso].
    destruct (Hlv j Hj) as [_ Hno]. apply Hno.
    apply (writes_in_log_byte img). exists (S i).
    split_and!; [lia|lia|by exists b]. }
  destruct (decide (i < length log0)%nat) as [Hin|Hout].
  - exact (Hlb j i m b Hj (prefix_either_lookup log0 log i m Hcmp Hm Hin) Hbb Hne).
  - (* [i] is the snapshot's own top: the write is the escrow's element *)
    assert (Hit : (S i = t)%nat) by lia.
    destruct (Hlv j Hj) as [Hvj _]. rewrite Hit Hvj in Hbyte.
    injection Hbyte as <-.
    destruct Hdisj as [[-> _]|[-> HT]].
    + by rewrite (nth_byte_clear j Hj) in Hne.
    + split; [lia|reflexivity].
Qed.

(** ... and its image-aware form, which is what the READER consumes: an
    admissible read that came back non-clear read a timestamp at or above
    [T] — timestamp 0 is barred by the image half. *)
Lemma wstarted_collapse (img : image) (log log0 : list wmsg) (a : Arch.pa)
    (T t : nat) (v : bv 32) (j t' : nat) (b : bv 8) :
  (j < 4)%nat ->
  (forall k : nat, (k < 4)%nat -> img (acc_addr a k) = Some (nth_byte lock_zero k)) ->
  (t <= S (length log0))%nat ->
  wstarted_lb log0 a T ->
  (log0 `prefix_of` log \/ log `prefix_of` log0) ->
  (forall k : nat, (k < 4)%nat ->
     latest_val img log (acc_addr a k) t (nth_byte v k)) ->
  ((v = lock_zero /\ (length log0 < T)%nat) \/ (v = lock_one /\ (T <= t)%nat)) ->
  log_byte img log t' (acc_addr a j) = Some b ->
  b <> nth_byte lock_zero 0 ->
  (T <= t')%nat /\ b = nth_byte lock_one j.
Proof.
  intros Hj Himg Hcov Hlb Hcmp Hlv Hdisj Hbyte Hne.
  destruct t' as [|i].
  - exfalso. rewrite log_byte_0 (Himg j Hj) in Hbyte.
    injection Hbyte as <-. by rewrite (nth_byte_clear j Hj) in Hne.
  - rewrite log_byte_S in Hbyte.
    destruct (log !! i) as [m|] eqn:Hm; [|by simpl in Hbyte]. simpl in Hbyte.
    exact (wstarted_lb_now img log log0 a T t v Hcov Hlb Hcmp Hlv Hdisj
             j i m b Hj Hm Hbyte Hne).
Qed.

(** IN THE CLEAR STATE THERE IS NO NON-CLEAR WRITE AT ALL — image included.
    The escrow's [T] is placed beyond the snapshot and its element's timestamp
    is inside it, so the only write the bound would admit is the escrow's own,
    whose value is the cleared word.  This is what lets a reader that came
    back non-clear RULE OUT the unset escrow, which is the step that turns the
    disjunction into the payload. *)
Lemma wstarted_clear_now (img : image) (log log0 : list wmsg) (a : Arch.pa)
    (T t : nat) (j t' : nat) (b : bv 8) :
  (j < 4)%nat ->
  (forall k : nat, (k < 4)%nat -> img (acc_addr a k) = Some (nth_byte lock_zero k)) ->
  (t <= S (length log0))%nat ->
  (length log0 < T)%nat ->
  wstarted_lb log0 a T ->
  (log0 `prefix_of` log \/ log `prefix_of` log0) ->
  (forall k : nat, (k < 4)%nat ->
     latest_val img log (acc_addr a k) t (nth_byte lock_zero k)) ->
  log_byte img log t' (acc_addr a j) = Some b ->
  b <> nth_byte lock_zero 0 ->
  False.
Proof.
  intros Hj Himg Hcov HT Hlb Hcmp Hlv Hbyte Hne.
  destruct t' as [|i].
  - rewrite log_byte_0 (Himg j Hj) in Hbyte. injection Hbyte as <-.
    by rewrite (nth_byte_clear j Hj) in Hne.
  - rewrite log_byte_S in Hbyte.
    destruct (log !! i) as [m|] eqn:Hm; [|by simpl in Hbyte]. simpl in Hbyte.
    assert (Hilt : (i < length log)%nat) by (by eapply lookup_lt_Some).
    assert (Hle : (S i <= t)%nat).
    { destruct (decide (S i <= t)%nat) as [?|Hgt]; [assumption|exfalso].
      destruct (Hlv j Hj) as [_ Hno]. apply Hno.
      apply (writes_in_log_byte img). exists (S i).
      split_and!; [lia|lia|]. exists b. rewrite log_byte_S Hm /=. exact Hbyte. }
    destruct (decide (i < length log0)%nat) as [Hin|Hout].
    + destruct (Hlb j i m b Hj (prefix_either_lookup log0 log i m Hcmp Hm Hin)
                  Hbyte Hne) as [HTle _]. lia.
    + assert (Hteq : (S i = t)%nat) by lia.
      assert (Hb2 : log_byte img log (S i) (acc_addr a j) = Some b)
        by (rewrite log_byte_S Hm /=; exact Hbyte).
      destruct (Hlv j Hj) as [Hvj _]. rewrite Hteq Hvj in Hb2.
      injection Hb2 as <-. by rewrite (nth_byte_clear j Hj) in Hne.
Qed.

(** THE ESCROW STATE IS ONE OF TWO WORDS.  A corollary of the same bound —
    every write to the flag writes the setter's byte or leaves the clear one
    — and the premise [WeakRacy]'s [wadm_two_valued] takes.  (The reader does
    not need it: the hardware's own [bnez] branches on the loaded word.  It is
    here because it costs one line and makes the collapse quotable.) *)
Lemma wstarted_two_valued (img : image) (log : list wmsg) (a : Arch.pa)
    (T : nat) (j t' : nat) (b : bv 8) :
  (j < 4)%nat ->
  (forall k : nat, (k < 4)%nat -> img (acc_addr a k) = Some (nth_byte lock_zero k)) ->
  wstarted_lb log a T ->
  log_byte img log t' (acc_addr a j) = Some b ->
  b = nth_byte lock_zero j \/ b = nth_byte lock_one j.
Proof.
  intros Hj Himg Hlb Hbyte.
  destruct (decide (b = nth_byte lock_zero 0)) as [->|Hne].
  - left. symmetry. by apply nth_byte_clear.
  - right. destruct t' as [|i].
    + rewrite log_byte_0 (Himg j Hj) in Hbyte. injection Hbyte as <-.
      by rewrite (nth_byte_clear j Hj) in Hne.
    + rewrite log_byte_S in Hbyte.
      destruct (log !! i) as [m|] eqn:Hm; [|by simpl in Hbyte]. simpl in Hbyte.
      exact (proj2 (Hlb j i m b Hj Hm Hbyte Hne)).
Qed.

Section weak_started.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P : vProp Σ.

  Definition wstartedN : namespace := nroot .@ "weakstarted".

  (** *** The escrow's LATEST-WRITE reading of its own elements

      Four applications of [WeakGhost.wlat_lookup]; no view hypothesis and no
      well-formedness, because an element IS the latest write by definition of
      [wlat_interp]. *)
  Lemma wlat4_latest_val (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (w : bv 32) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4 a dq t w -∗
    ⌜forall j : nat, (j < 4)%nat ->
       latest_val (wimg σ) (wm_log σ) (acc_addr a j) t (nth_byte w j)⌝.
  Proof.
    iIntros "Hi (H0 & H1 & H2 & H3)".
    iDestruct (wlat_lookup with "Hi H0") as %E0.
    iDestruct (wlat_lookup with "Hi H1") as %E1.
    iDestruct (wlat_lookup with "Hi H2") as %E2.
    iDestruct (wlat_lookup with "Hi H3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** Two log lower bounds are comparable (mono-list). *)
  (** ... and its [wlat4_sync] instance, which is what the escrow's own
      elements are since the φ-upgrade's deliverable A. *)
  Lemma wlat4_sync_latest_val (σ : wmstate) (a : Arch.pa) (t : nat)
      (w : bv 32) :
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4_sync a t w -∗
    ⌜forall j : nat, (j < 4)%nat ->
       latest_val (wimg σ) (wm_log σ) (acc_addr a j) t (nth_byte w j)⌝.
  Proof.
    iIntros "Hi [He _]".
    by iApply (wlat4_el_latest_val (wm_img σ) (wm_log σ) a (DfracOwn 1) t w
                 with "Hi He").
  Qed.

  Lemma wlog_lb_compare (l1 l2 : list wmsg) :
    wlog_lb l1 -∗ wlog_lb l2 -∗ ⌜l1 `prefix_of` l2 \/ l2 `prefix_of` l1⌝.
  Proof.
    rewrite /wlog_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  (** THE ESCROW, at a known timestamp/value pair.

      Two conjuncts beyond [StartedInv]'s: the element bundle, and the
      ONE-SHOT RECORD — a log snapshot, the clipped lower bound over it, and
      the deposit timestamp [T] the bound is keyed on.  Read the disjunction
      as the SC escrow's, with the payload's freezing view decoupled from the
      element's timestamp: the flag is either still clear (and then NO write
      is non-clear — [T] is placed beyond the snapshot, which is exactly that
      statement), or it has been set, and then [P] is frozen at [view_scl T]
      with every non-clear write at or above [T].

      COVERAGE is [t ≤ S (length log0)], one MORE than [WeakKpt]'s
      [T0 ≤ length log0], and the slack is what lets [wstarted_set] refresh
      the snapshot to the PRE-state's log (which a caller holding
      [wmstate_interp σ] has for free) rather than the successor's: the one
      write the snapshot then fails to cover is the escrow's OWN, whose value
      the element already names. *)
  Definition wstarted_hist (a : Arch.pa) P (t : nat) (v : bv 32) : iProp Σ :=
    (∃ (T : nat) (log0 : list wmsg),
       wlog_lb log0 ∗
       ⌜(t <= S (length log0))%nat⌝ ∗
       ⌜wstarted_lb log0 a T⌝ ∗
       ((⌜v = lock_zero⌝ ∗ ⌜(length log0 < T)%nat⌝)
        ∨ (⌜v = lock_one⌝ ∗ ⌜(T <= t)%nat⌝ ∗ monPred_at P (view_scl T))))%I.

  Definition wstarted_at (a : Arch.pa) P (t : nat) (v : bv 32) : iProp Σ :=
    (wlat4_sync a t v ∗ wstarted_hist a P t v)%I.

  (** The flag word is a SYNC window (φ-upgrade, deliverable A), and the
      witness is persistent, so it can be read out of the escrow and handed
      to [WeakRacy]'s load rules without disturbing anything. *)
  Lemma wstarted_at_sync a P t v : wstarted_at a P t v -∗ sync_win a 4.
  Proof. iIntros "[Hw _]". by iApply wlat4_sync_win. Qed.

  (** ... and the invariant body: an [iProp], hence objective, hence
      admissible in an [inv]. *)
  Definition wstarted_body (a : Arch.pa) P : iProp Σ :=
    (∃ (t : nat) (v : bv 32), wstarted_at a P t v)%I.

  Definition wstarted_inv (a : Arch.pa) P : iProp Σ :=
    inv wstartedN (wstarted_body a P).

  Global Instance wstarted_inv_persistent a P : Persistent (wstarted_inv a P).
  Proof. apply _. Qed.

  (** THE MINT.  The premise is the flag word's ERA-IMAGE elements — the four
      latest-write cells at TIMESTAMP 0, holding the cleared word — which is
      what boot has for a [.bss] word and nothing more.  At timestamp 0 the
      element says two things at once, and the mint needs both: the image byte
      is clear (handed back as [wstarted_img_clear], the side condition the
      reader carries — see header (c)), and NO message of the log writes the
      byte at all, which is the clipped bound at any [T]. *)
  Lemma wstarted_alloc (a : Arch.pa) P (σ : wmstate) E :
    wlog_lb (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4 a (DfracOwn 1) 0 lock_zero
    ={E}=∗ (wlat_interp (wm_img σ) (wm_log σ) ∗
            ⌜wstarted_img_clear σ a⌝ ∗ sync_win a 4 ∗ wstarted_inv a P).
  Proof.
    iIntros "#Hlb Hi Hw".
    iDestruct (wlat4_latest_val σ a (DfracOwn 1) 0 lock_zero with "Hi Hw")
      as %Hlv.
    iAssert (⌜wstarted_img_clear σ a⌝)%I as %Himg.
    { iPureIntro. intros j Hj. destruct (Hlv j Hj) as [Hb _].
      rewrite log_byte_0 in Hb. exact Hb. }
    (* nothing in the log writes the flag: the element is the era image's *)
    iAssert (⌜wstarted_lb (wm_log σ) a (S (length (wm_log σ)))⌝)%I as %Hlb0.
    { iPureIntro. intros j i m b Hj Hm Hbb _. exfalso.
      destruct (Hlv j Hj) as [_ Hno]. apply Hno.
      apply (writes_in_log_byte (wimg σ)). exists (S i).
      apply lookup_lt_Some in Hm as Hlt.
      split_and!; [lia|lia|]. exists b. rewrite log_byte_S Hm /=. exact Hbb. }
    (* THE S MINT (φ-upgrade, deliverable A).  The very fact just proved —
       no message of the log writes the flag — IS [WeakGhost.wcds_sync] at
       each of the four bytes, so the escrow's own allocation premise pays
       for turning the word sync.  No boot-bundle parameter is needed: the
       mint is local to the site that knows the word is untouched. *)
    assert (Hsy : forall j : nat, (j < 4)%nat ->
              wcds_sync (wm_log σ) (acc_addr a j)).
    { intros j Hj p m (Hp & [b Hb] & _).
      destruct (Hlv j Hj) as [_ Hno]. apply Hno.
      apply (writes_in_log_byte (wimg σ)). exists (S p).
      apply lookup_lt_Some in Hp as Hlt.
      split_and!; [lia|lia|]. exists b. rewrite log_byte_S Hp /=. exact Hb. }
    iMod (wlat4_sync_mint (wm_img σ) (wm_log σ) a 0 lock_zero Hsy
            with "Hi Hw") as "[Hi Hw]".
    iDestruct (wlat4_sync_win with "Hw") as "#Hsw".
    iFrame "Hi". iSplitR; [by iPureIntro|]. iFrame "Hsw".
    iApply inv_alloc. iNext.
    iExists 0%nat, lock_zero. rewrite /wstarted_at. iFrame "Hw".
    iExists (S (length (wm_log σ))), (wm_log σ). iFrame "Hlb".
    iSplitR; [iPureIntro; lia|]. iSplitR; [by iPureIntro|].
    iLeft. iSplitR; [by iPureIntro|]. iPureIntro; lia.
  Qed.

  (** The log lower bound every consumer of the escrow needs, off the state
      interpretation it already holds.  Persistent, so it costs nothing. *)
  Lemma wmstate_interp_log_lb `{CpuId} (σ : wmstate) :
    wmstate_interp σ ⊢ wmstate_interp σ ∗ wlog_lb (wm_log σ).
  Proof.
    rewrite /wmstate_interp.
    iIntros "(%Hb & %Hn & %Hw & Hr & Hd & Hl & Hlat & Hws)".
    iDestruct (wlog_snapshot with "Hl") as "[Hl #Hlb]".
    iFrame "Hlb". iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** The WRITER: [fence rw,w] ; [sw a5,0(a4)] with a5 = 1

      Structurally identical to [WeakLock.wrelease_core] — because it IS a
      release: the payload is deposited at the store's own timestamp and the
      escrow's elements are retargeted at the message the step appended.

      THE ONE NEW PREMISE is the log lower bound of the PRE-state, which is
      what refreshes the escrow's snapshot: without it the re-established
      bound would still be keyed on a snapshot the set has outrun (header
      (a)).  It is persistent and every caller already holds
      [wmstate_interp σ], so it costs one [wmstate_interp_log_lb].

      THE SECOND SET IS PROVED, NOT RATIONED.  Nothing here says the escrow
      is unset, so the proof splits: from the CLEAR state the deposit is the
      caller's, at the store's own timestamp; from an ALREADY-SET state the
      old deposit is KEPT (it sits at a strictly lower [T], hence is the
      stronger fact) and the caller's is dropped.  That is the whole reason
      the conjunct is a lower bound and not an exact timestamp. *)
  Lemma wstarted_set (a : Arch.pa) P (tid : option nat) (σ σ' : wmstate) :
    wQ_store tid a lock_one σ σ' ->
    (* φ-upgrade §1, as in [WeakLock.wrelease_core]: the [fence rw,w] before
       the [started] store is what makes its message release-class, hence what
       keeps the escrow's element bundle CLEAN. *)
    w_relp (wm_ws σ) = true ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    wlog_lb (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wstarted_body a P -∗
    vwp_hold P (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wstarted_at a P (S (length (wm_log σ))) lock_one.
  Proof.
    intros (Himg & (kc & Hlog & Hnp) & Hle & Hflr) Hrelp Hbnd.
    specialize (Hnp Hrelp).
    iIntros "#Hlbσ Hi Hbody HP".
    iDestruct "Hbody" as (t v) "[Hw Hhist]".
    iDestruct "Hhist" as (T log0) "(#Hlb0 & %Hcov & %Hlbf & Hdisj)".
    iDestruct (wlog_lb_compare with "Hlb0 Hlbσ") as %Hcmp.
    iDestruct (wlat4_sync_latest_val σ a t v with "Hi Hw") as %Hlv.
    (* the element is a write of the log, so the escrow's timestamp is one
       the fresh snapshot covers *)
    assert (Htlen : (t <= length (wm_log σ))%nat \/ t = 0%nat).
    { destruct t as [|t]; [by right|left].
      apply (log_byte_bounded (wimg σ) (wm_log σ) (S t) (acc_addr a 0)).
      destruct (Hlv 0%nat ltac:(lia)) as [Hb _]. by exists (nth_byte v 0). }
    iAssert (monPred_at P (view_scl (S (length (wm_log σ)))))%I with "[HP]"
      as "HPnew".
    { by iApply (wwp_release_deposit P σ Hbnd with "HP"). }
    iDestruct "Hdisj" as "[[-> %HT]|(-> & %HT & HP0)]".
    - (* CLEAR: nothing non-clear was ever written, so the deposit is ours *)
      pose proof (wstarted_lb_now (wimg σ) (wm_log σ) log0 a T t lock_zero
                    Hcov Hlbf Hcmp Hlv (or_introl (conj eq_refl HT))) as Hnow.
      iMod (wlat4_sync_store_gen tid kc σ σ' a t lock_zero lock_one Hnp Himg
              Hlog with "Hi Hw") as "[Hi Hw]".
      iModIntro. iFrame "Hi". rewrite /wstarted_at. iFrame "Hw".
      iExists (S (length (wm_log σ))), (wm_log σ). iFrame "Hlbσ".
      iSplitR; [iPureIntro; lia|]. iSplitR.
      { iPureIntro. intros j i m b Hj Hm Hbb Hne. exfalso.
        destruct (Hnow j i m b Hj Hm Hbb Hne) as [HTle _].
        (* the only candidate is the escrow's own message, and it is clear *)
        assert (Hilt : (i < length (wm_log σ))%nat) by (by eapply lookup_lt_Some).
        assert (Hit : (S i <= t)%nat).
        { destruct (decide (S i <= t)%nat) as [?|Hgt]; [assumption|exfalso].
          destruct (Hlv j Hj) as [_ Hno]. apply Hno.
          apply (writes_in_log_byte (wimg σ)). exists (S i).
          split_and!; [lia|lia|]. exists b. rewrite log_byte_S Hm /=. exact Hbb. }
        assert (Hteq : (S i = t)%nat) by lia.
        assert (Hbyte : log_byte (wimg σ) (wm_log σ) (S i) (acc_addr a j) = Some b)
          by (rewrite log_byte_S Hm /=; exact Hbb).
        destruct (Hlv j Hj) as [Hvj _]. rewrite Hteq Hvj in Hbyte.
        injection Hbyte as <-.
        by rewrite (nth_byte_clear j Hj) in Hne. }
      iRight. iSplitR; [by iPureIntro|]. iSplitR; [iPureIntro; lia|].
      iExact "HPnew".
    - (* ALREADY SET: keep the earlier deposit, and with it the earlier [T] *)
      pose proof (wstarted_lb_now (wimg σ) (wm_log σ) log0 a T t lock_one
                    Hcov Hlbf Hcmp Hlv (or_intror (conj eq_refl HT))) as Hnow.
      iMod (wlat4_sync_store_gen tid kc σ σ' a t lock_one lock_one Hnp Himg
              Hlog with "Hi Hw") as "[Hi Hw]".
      iModIntro. iFrame "Hi". rewrite /wstarted_at. iFrame "Hw".
      iExists T, (wm_log σ). iFrame "Hlbσ".
      iSplitR; [iPureIntro; lia|]. iSplitR; [by iPureIntro|].
      iRight. iSplitR; [by iPureIntro|]. iSplitR; [iPureIntro; lia|].
      iExact "HP0".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** The READER: [lw a5,0(a4)] ; [fence rw,rw]

      Three facts, in the order the two instructions produce them. *)

  (** (a) WHICH MESSAGE THE LOAD READ.  A plain load's admissibility
      ([WeakInterp.wbyte_ok]) allows any readable timestamp; the one-shot fact
      pins it as soon as the byte read back non-clear. *)
  Lemma wstarted_read_ts (σ : wmstate) (ak : akinfo) (a : Z) (t t' : nat)
      (b : bv 8) :
    wstarted_oneshot (wimg σ) (wm_log σ) a t ->
    wbyte_ok σ ak a t' b ->
    b <> nth_byte lock_zero 0 ->
    t' = t.
  Proof. intros Hone [Hv _] Hne. exact (Hone t' b Hv Hne). Qed.

  (** (b) THE LOAD'S OWN GAIN: a non-forwarded plain load of timestamp [t]
      leaves [t ≤ w_vrOld], which is the premise the fence consumes. *)
  Lemma wstarted_read_vrOld (ws : wstate) (a : Z) (t : nat) :
    w_fwd ws = ∅ ->
    (t <= w_vrOld (load_post ws false a t))%nat.
  Proof. intros Hfwd. by apply load_post_vrOld_nofwd. Qed.

  (** (c) THE DELIVERY, at the [fence rw,rw]: everything frozen at a scalar
      view the hart has already READ is delivered to its index.  This is the
      whole reader-side content, and it is one application of
      [WeakInstr.wwp_fence_scl].  ANY pred-R fence does it
      ([WeakFence.acq_pred_r]) — which matters, because the fence xv6's spin
      loop executes is [fence r,rw], not [fence rw,rw]. *)
  Lemma wstarted_deliver_gen P (σ : wmstate) (ws' : wstate) (t : nat)
      (b : barrier_kind) :
    acq_pred_r b ->
    (t <= w_vrOld (wm_ws σ))%nat ->
    wV_fence b σ ws' ->
    monPred_at P (view_scl t) ⊢ vwp_hold P ws'.
  Proof. intros Hb Ht HQ. by apply (wwp_fence_scl_gen P σ ws' t b). Qed.

  Lemma wstarted_deliver P (σ : wmstate) (ws' : wstate) (t : nat) :
    (t <= w_vrOld (wm_ws σ))%nat ->
    wV_fence Barrier_RISCV_rw_rw σ ws' ->
    monPred_at P (view_scl t) ⊢ vwp_hold P ws'.
  Proof. exact (wstarted_deliver_gen P σ ws' t _ acq_pred_r_rw_rw). Qed.

  (** The kernel's own kind: [fence r,rw] at [main+0x18]. *)
  Lemma wstarted_deliver_r P (σ : wmstate) (ws' : wstate) (t : nat) :
    (t <= w_vrOld (wm_ws σ))%nat ->
    wV_fence Barrier_RISCV_r_rw σ ws' ->
    monPred_at P (view_scl t) ⊢ vwp_hold P ws'.
  Proof. exact (wstarted_deliver_gen P σ ws' t _ acq_pred_r_r_rw). Qed.

  (** (d) THE OBSERVATION — the one-shot collapse at the escrow.

      THE READER'S HALF OF THE HANDOFF, and the lemma the racy load is wired
      to.  Read it as: an ADMISSIBLE read of one flag byte
      ([WeakInterp.wbyte_ok], which is exactly what [WeakRacy.wadm] hands out
      per byte) that came back NON-CLEAR read a timestamp at or above the
      escrow's deposit, and the payload is frozen at that deposit.  Both
      halves are needed and neither is enough alone: [T ≤ t] is what makes the
      reader's own [w_vrOld] gain cover the deposit, and the deposit is what
      the [fence rw,rw] delivers.

      The escrow is handed back UNCHANGED — the payload is persistent, as in
      [StartedInv] and for the same reason (every secondary hart takes a copy)
      — which is what makes the spin loop re-entrant.

      [wstarted_img_clear] is the era-image side condition of header (c); the
      log lower bound is free from any [wmstate_interp]
      ([wmstate_interp_log_lb]).  Note what is NOT required: no
      [wlog_wf], no [acc_wf], no view hypothesis, and no log AUTHORITY. *)
  Lemma wstarted_observe (a : Arch.pa) P `{!Persistent P}
      (σ : wmstate) (ak : akinfo) (j t : nat) (b : bv 8) :
    wstarted_img_clear σ a ->
    (j < 4)%nat ->
    wbyte_ok σ ak (acc_addr a j) t b ->
    b <> nth_byte lock_zero 0 ->
    wlog_lb (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wstarted_body a P -∗
    wlat_interp (wm_img σ) (wm_log σ) ∗ wstarted_body a P ∗
      ⌜b = nth_byte lock_one j⌝ ∗
      (∃ T : nat, ⌜(T <= t)%nat⌝ ∗ monPred_at P (view_scl T)).
  Proof.
    intros Himg Hj [Hb _] Hne. iIntros "#Hlbσ Hi Hbody".
    iDestruct "Hbody" as (te v) "[Hw Hhist]".
    iDestruct "Hhist" as (T log0) "(#Hlb0 & %Hcov & %Hlbf & Hdisj)".
    iDestruct (wlog_lb_compare with "Hlb0 Hlbσ") as %Hcmp.
    iDestruct (wlat4_sync_latest_val σ a te v with "Hi Hw") as %Hlv.
    iDestruct "Hdisj" as "[[-> %HT]|(-> & %HT & #HP0)]".
    - (* the flag is still clear, so nothing non-clear is readable at all *)
      iExFalso. iPureIntro.
      exact (wstarted_clear_now (wimg σ) (wm_log σ) log0 a T te j t b
               Hj Himg Hcov HT Hlbf Hcmp Hlv Hb Hne).
    - destruct (wstarted_collapse (wimg σ) (wm_log σ) log0 a T te lock_one j t b
                  Hj Himg Hcov Hlbf Hcmp Hlv (or_intror (conj eq_refl HT)) Hb Hne)
        as [HTle Hbb].
      iFrame "Hi".
      iSplitL "Hw".
      { iExists te, lock_one. iFrame "Hw". iExists T, log0. iFrame "Hlb0".
        iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
        iRight. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
        iExact "HP0". }
      iSplitR; [by iPureIntro|].
      iExists T. iSplitR; [by iPureIntro|]. iExact "HP0".
  Qed.

  (** (e) THE THREE COMPOSED, at the σ altitude: observation, the load's own
      view gain, the fence.  This is the whole reader side of the handoff, and
      what the WP-level waiter (see [WkStartedLoad.v]) instantiates.

      [Hgain] — "the timestamp this load took at byte [j] is covered by the
      successor's [w_vrOld]" — is the racy [lw]'s own ISA content
      (porting guide §2c: the [Q] half is irreducibly per-instruction), and
      [WeakMem.load_post_vrOld_nofwd] / [wstarted_read_vrOld] is what
      discharges it for a hart with an empty forward bank. *)
  Lemma wstarted_reader (a : Arch.pa) P `{!Persistent P}
      (σ σf : wmstate) (ws' : wstate) (ak : akinfo) (j t : nat) (b : bv 8)
      (bk : barrier_kind) :
    wstarted_img_clear σ a ->
    (j < 4)%nat ->
    wbyte_ok σ ak (acc_addr a j) t b ->
    b <> nth_byte lock_zero 0 ->
    (t <= w_vrOld (wm_ws σf))%nat ->
    acq_pred_r bk ->
    wV_fence bk σf ws' ->
    wlog_lb (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wstarted_body a P -∗
    wlat_interp (wm_img σ) (wm_log σ) ∗ wstarted_body a P ∗
      ⌜b = nth_byte lock_one j⌝ ∗ vwp_hold P ws'.
  Proof.
    intros Himg Hj Hok Hne Hgain Hbk HQ. iIntros "#Hlbσ Hi Hbody".
    iDestruct (wstarted_observe a P σ ak j t b Himg Hj Hok Hne
                 with "Hlbσ Hi Hbody") as "(Hi & Hbody & %Hbb & HT)".
    iDestruct "HT" as (T) "[%HTle #HP0]".
    iFrame "Hi Hbody". iSplitR; [by iPureIntro|].
    iApply (wstarted_deliver_gen P σf ws' T bk with "HP0");
      [exact Hbk|lia|exact HQ].
  Qed.

End weak_started.

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
    written once ([wstarted_oneshot]). *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
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

Section weak_started.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P : vProp Σ.

  Definition wstartedN : namespace := nroot .@ "weakstarted".

  (** THE ESCROW, at a known timestamp/value pair ... *)
  Definition wstarted_at (a : Arch.pa) P (t : nat) (v : bv 32) : iProp Σ :=
    (wlat4 a (DfracOwn 1) t v ∗
     (⌜v = lock_zero⌝ ∨ monPred_at P (view_scl t)))%I.

  (** ... and the invariant body: an [iProp], hence objective, hence
      admissible in an [inv]. *)
  Definition wstarted_body (a : Arch.pa) P : iProp Σ :=
    (∃ (t : nat) (v : bv 32), wstarted_at a P t v)%I.

  Definition wstarted_inv (a : Arch.pa) P : iProp Σ :=
    inv wstartedN (wstarted_body a P).

  Global Instance wstarted_inv_persistent a P : Persistent (wstarted_inv a P).
  Proof. apply _. Qed.

  Lemma wstarted_alloc (a : Arch.pa) P (t : nat) E :
    wlat4 a (DfracOwn 1) t lock_zero ={E}=∗ wstarted_inv a P.
  Proof.
    iIntros "Hw". iApply inv_alloc. iNext.
    iExists t, lock_zero. rewrite /wstarted_at. iFrame "Hw".
    iLeft. by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** The WRITER: [fence rw,w] ; [sw a5,0(a4)] with a5 = 1

      Structurally identical to [WeakLock.wrelease_core] — because it IS a
      release: the payload is deposited at the store's own timestamp and the
      escrow's elements are retargeted at the message the step appended. *)
  Lemma wstarted_set (a : Arch.pa) P (tid : option nat) (σ σ' : wmstate) :
    wQ_store tid a lock_one σ σ' ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wstarted_body a P -∗
    vwp_hold P (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wstarted_at a P (S (length (wm_log σ))) lock_one.
  Proof.
    intros (Himg & Hlog & Hle & Hflr) Hbnd.
    iIntros "Hi Hbody HP".
    iDestruct "Hbody" as (t v) "[Hw _]".
    iAssert (monPred_at P (view_scl (S (length (wm_log σ)))))%I with "[HP]" as "HP".
    { by iApply (wwp_release_deposit P σ Hbnd with "HP"). }
    iMod (wlat4_store_gen tid σ σ' a t v lock_one Himg Hlog with "Hi Hw")
      as "[Hi Hw]".
    iModIntro. iFrame "Hi". rewrite /wstarted_at. iFrame "Hw".
    iRight. iExact "HP".
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
      [WeakInstr.wwp_fence_scl]. *)
  Lemma wstarted_deliver P (σ : wmstate) (ws' : wstate) (t : nat) :
    (t <= w_vrOld (wm_ws σ))%nat ->
    wV_fence Barrier_RISCV_rw_rw σ ws' ->
    monPred_at P (view_scl t) ⊢ vwp_hold P ws'.
  Proof. intros Ht HQ. by apply (wwp_fence_scl P σ ws' t). Qed.

  (** (d) THE THREE COMPOSED, off the escrow.  The payload is persistent — as
      in [StartedInv], and for the same reason (every secondary hart takes a
      copy) — so the escrow is handed back UNCHANGED, which is what makes the
      spin loop re-entrant. *)
  Lemma wstarted_reader (a : Arch.pa) P `{!Persistent P}
      (σf : wmstate) (ws' : wstate) (t : nat) (v : bv 32) :
    (t <= w_vrOld (wm_ws σf))%nat ->
    wV_fence Barrier_RISCV_rw_rw σf ws' ->
    v <> lock_zero ->
    wstarted_at a P t v ⊢ wstarted_at a P t v ∗ vwp_hold P ws'.
  Proof.
    intros Ht HQ Hv. rewrite /wstarted_at.
    iIntros "[Hw [%Hz|#HP]]"; [done|].
    iFrame "Hw". iSplitR; [iRight; iExact "HP"|].
    by iApply (wstarted_deliver P σf ws' t Ht HQ with "HP").
  Qed.

End weak_started.

(** * WeakEvDisk.v — the per-node EWP rules for the DISK THREAD (M5 C4a)

    Design: [claude-notes/design/weak-memory-m5.md] ("The language" as
    LANDED, and "The WP side"); the language is [WeakEvLang] §5
    ([edisk_step], eight arms), the device program is [VirtioProg.DM].

    [WeakEvLift] lifts one event of a HART; this file lifts one event of the
    DISK, which since M5 is an ordinary weak-memory agent running
    [VirtioProg.virtio_prog] node by node at its own [wstate].  Every rule
    here is the twin of a [WeakEvLift] rule, with ONE structural difference
    that shapes the whole file:

    ------------------------------------------------------------------------
    (A) THE DISK'S [wstate] IS SYNTAX, NOT GHOST STATE.  [dws] rides in the
        expression [EDisk gen dp dws], so there is no [hart_ws]-like cell to
        agree with and update: the rules simply thread [dws] syntactically.
        AND — this is the surprise worth recording — [WeakGhost.weak_state_interp]
        REQUIRES NOTHING WHATSOEVER OF THE DISK'S VIEW.  Its [ws_bounded]
        conjunct is [∀ c : CPU, ws_bounded (wgws g c) …] and its φ conjunct
        [no_violation (wglog g) (wgws g)] quantifies its floor over harts
        only, so:

          - a disk LOAD owes NO φ payment (it moves [dws], which the
            interpretation does not mention) — where [ewp_ev_load] demands
            [nv_ok] at every floor it raised, [ewp_disk_read] demands
            nothing;
          - a disk STORE owes only what a foreign append owes:
            [WeakGhost.no_violation_dma] (free — the author is [n_disk],
            not a hart), [WeakMem.ws_bounded_mono] for every hart, and
            [wlog_wf] of the appended message.  The C/D/S conjunct of
            [wlat_interp] ([wcds_agree]) is NOT free, and it is left to the
            CLIENT: [ewp_disk_write] hands out [wlat_interp img log] and
            demands [wlat_interp img (log ++ [msg])] back.  See (E) below
            for exactly how awkward that is and why no invariant is invented
            here to hide it;
          - nothing constrains [dws] itself, so no rule takes a
            [ws_bounded dws _] premise.  The one place the client's own
            bookkeeping is unavoidable is READ ENABLEDNESS — see (C).

    ------------------------------------------------------------------------
    (B) THE LATCH ARM, and the plumbing chosen for it.  [edisk_step]'s last
        disjunct — the PLIC latch — is enabled at EVERY [dp]: at any time the
        virtio line may be high and the PLIC gateway may latch it, moving
        [dplic] and leaving the expression alone.  So every rule below must
        cover its own arm AND the latch.

        WHAT WAS REJECTED, and why.  The obvious shape — one extra premise
        [Hlatch : ▷ (∀ p', … -∗ plic_frag p' -∗ EWP (EDisk gen dp dws))]
        alongside the node's own premise — is UNPROVABLE FOR THE CLIENT in
        general: the latch and the node arm are mutually exclusive at
        runtime but their two premises are ∗-separated in the rule, so the
        client would have to pay for BOTH out of the same (linear) device
        resources.  Writing them with ∧ instead is sound but forces the ∧
        through the fupd/▷ structure of every rule, and makes every
        driver-side node proof carry a "and if instead the interrupt was
        latched…" branch.

        WHAT IS DONE INSTEAD: THE LATCH IS ABSORBED INSIDE THE RULES, once,
        by [ewp_edisk_latch] — an internal Löb over the plic state.  A latch
        step consumes nothing but [plic_frag], so the rule re-enters itself
        with [plic_frag p'] and the client's premises UNTOUCHED, and the
        latch never reaches the client's obligations at all.  The price, and
        it is the whole interface cost of the device epoch here, is that a
        client cannot name the plic state it will own at the successor: every
        rule's continuation is quantified over [p0] and receives
        [plic_frag p0] together with the pure witness
        [⌜plic_latched p p0⌝] — the reflexive-transitive closure of "one
        virtio latch" — so nothing is lost except the number of latches that
        fired.  (The per-latch fact [dev_irq_level d virtio_irq_id = true] is
        NOT recorded: it is a fact about the device state at that moment,
        which the closure cannot carry.)

        Two consequences of the absorption, both deliberate:
          - each rule's continuation is ▷-GUARDED (the latch is a real step,
            so the ▷ is available, and the client's own Löb-style device
            loop needs it to close);
          - each rule's continuation is invoked LAZILY, at mask ⊤, AFTER the
            step — not through a ⊤→∅ accessor around it.  The mask-changing
            form is what [ewp_ev_store]/[ewp_ev_load] use so that a client
            may hold an invariant open ACROSS the event; it cannot be used
            here, because such a callback must be invoked BEFORE the arm is
            known (its ▷ is stripped by the step's later) and would then be
            consumed on a latch step.  A client that needs an invariant
            around a device event must therefore open and close it within
            the ⊤-fupd the continuation is given.

    ------------------------------------------------------------------------
    (C) READ ENABLEDNESS.  [eprim_step_disk_reducible] says every node but a
        [DRead] always steps; a [DRead] with no admissible timestamp
        assignment is legitimately stuck, and answering it is the DRIVER's
        obligation ([WeakEvLang] §10).  [ewp_disk_read] therefore takes an
        ENABLEDNESS EXTRACTOR — a persistent [□] wand from the client's own
        device resources [EN] and the machine's [wlat_interp] to the PURE
        fact that some admissible [tvs] exists.  It is □ and pure-concluding
        on purpose: it is applied while the latch loop is still running, so
        it must survive an arbitrary number of latch steps and must not
        consume the interpretation.  This mirrors how [ewp_ev_load] takes its
        witness (there: the first component of the client's callback), moved
        out of the callback because the callback is now lazy.

    ------------------------------------------------------------------------
    (D) NO [DRet DWild] RULE — a deliberate omission.  The wild arm replaces
        the residual program by an ARBITRARY nonempty store chain
        ([dm_wild_chain]); a rule for it would ask the client to prove EWP of
        a chain of stores to addresses it does not own, which is exactly the
        obligation assumption 4 of the M5 ledger says the driver must make
        VACUOUS instead.  A driver proof must show that [DRet DWild] is
        UNREACHABLE — i.e. that every request it publishes has a well-formed
        descriptor chain — and then it never needs a rule here.  ([DWild] is
        reachable only from a [DRet DWild] node, so omitting the rule costs
        nothing at any other node.)

    ------------------------------------------------------------------------
    (E) WHAT A DISK STORE MUST RE-ESTABLISH IN [wlat_interp], stated
        honestly.  [wlat_interp img log] is [wlat_agree (img_z img) log m ∗
        wcds_agree log mc] over two ghost maps.  Appending the disk's message
        moves BOTH: the latest-write map at every byte the message covers,
        and the C/D/S state of those bytes ([wcds_agree] is a fact about the
        WHOLE log, not only about the bytes owned by the appender).  The disk
        is not a hart, so its message is invisible to [nv_byte]'s author
        quantifier — [no_violation] is free — but [wcds_agree] is NOT, and
        the retarget needs the fragments for the bytes written (the
        [WeakStore.wlat4_store_gen] family).  Those fragments belong to the
        DRIVER (they are the DMA target buffer it lent the device), not to
        this file, and there is no invariant here that could hold them
        without pinning the driver's ownership discipline.  So
        [ewp_disk_write] passes the obligation through verbatim: it hands the
        client [wlat_interp img log] and takes [wlat_interp img (log ++
        [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)])] back.  The class
        stamped is [ddev_class dws] — computed, not annotated — so the
        device's release is [WCrel] exactly after its [DFence]. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import VirtioProg.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakLang.
Require Import WeakBridge.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.
Require Import WeakEvLift.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The step relation, split at the latch

    [edisk_step]'s eight disjuncts are the seven PROGRAM arms (start, the
    four node arms, commit/idle) plus the latch.  §4's absorber needs the
    two halves as named predicates. *)

Definition edisk_nolatch (gen : nat) (dp : option (DM dres)) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  (dp = None /\ e' = EDisk gen (Some (virtio_prog (dvirtio (wgdev σ)))) dws
   /\ σ' = σ)
  \/
  (exists pa n aq k tvs,
     dp = Some (DRead pa n aq k) /\
     length tvs = n /\
     read_ok (img_z (wgimg σ)) (wglog σ) dws aq false (pa_z pa) tvs /\
     e' = EDisk gen (Some (k tvs.*2))
            (load_post_run dws aq (pa_z pa) tvs.*1) /\
     σ' = σ)
  \/
  (exists pa bs k,
     dp = Some (DWrite pa bs k) /\ bs <> [] /\
     e' = EDisk gen (Some k)
            (store_post_run dws false (pa_z pa) (length bs)
               (S (length (wglog σ)))) /\
     σ' = ewg_log σ
            (wglog σ ++ [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)]))
  \/
  (exists k,
     dp = Some (DFence k) /\
     e' = EDisk gen (Some k) (fence_post dws true true true true) /\ σ' = σ)
  \/
  (exists delta,
     dp = Some (DRet (DDone delta)) /\ e' = EDisk gen None dws /\
     σ' = ewg_dev σ (set_dvirtio (wgdev σ) (delta (dvirtio (wgdev σ)))))
  \/
  (exists prog',
     dp = Some (DRet DWild) /\ dm_wild_chain prog' /\
     e' = EDisk gen (Some prog') dws /\ σ' = σ)
  \/
  (dp = Some (DRet DIdle) /\ e' = EDisk gen None dws /\ σ' = σ).

Definition edisk_latch_arm (gen : nat) (dp : option (DM dres)) (dws : wstate)
    (σ : wgstate) (e' : eexpr) (σ' : wgstate) : Prop :=
  exists p',
    dev_irq_level (wgdev σ) virtio_irq_id = true /\
    plic_latch (dplic (wgdev σ)) virtio_irq_id = Some p' /\
    e' = EDisk gen dp dws /\
    σ' = ewg_dev σ (set_dplic (wgdev σ) p').

Lemma edisk_step_split gen dp dws σ e' σ' :
  edisk_step gen dp dws σ e' σ' <->
  edisk_nolatch gen dp dws σ e' σ' \/ edisk_latch_arm gen dp dws σ e' σ'.
Proof. rewrite /edisk_step /edisk_nolatch /edisk_latch_arm. tauto. Qed.

Lemma edisk_nolatch_step gen dp dws σ e' σ' :
  edisk_nolatch gen dp dws σ e' σ' -> edisk_step gen dp dws σ e' σ'.
Proof. intros H. by apply edisk_step_split; left. Qed.

(** The record identity the fabric-reading arms need ([wgstate] is a plain
    record, so this is not definitional). *)
Lemma ewg_dev_id σ : ewg_dev σ (wgdev σ) = σ.
Proof. by destruct σ. Qed.

(* ====================================================================== *)
(** ** 2. Opening [weak_state_interp] for a NON-HART author

    The disk's three σ-shapes: the fabric ([ewg_dev]), the log borrowed
    read-only, and the log appended to ([ewg_log]).  None of them touches
    any hart's [wws_auth] — [WeakEvLang.edisk_step_ws] is the language-side
    statement of the same fact — so these accessors are strictly weaker than
    [WeakEvLift.weak_state_interp_mem] and, unlike it, are not indexed by a
    hart at all. *)

Section interp.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma weak_state_interp_dev (σ : wgstate) :
    weak_state_interp σ ⊢ dev_interp (wgdev σ) ∗
      (∀ d' : dev_state, dev_interp d' -∗ weak_state_interp (ewg_dev σ d')).
  Proof.
    rewrite /weak_state_interp /wgen_pin /ewg_dev.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    iIntros "([%Hpow %Hgen0] & %Hbnd & %Hnv & %Hwf & Hgr & $ & Hlog & Hlat & Hws)".
    iIntros (d') "Hd". iFrame "Hgr Hd Hlog Hlat Hws".
    iPureIntro. split_and!; done.
  Qed.

  (** A [dev_interp] borrow that closes at σ itself. *)
  Lemma weak_state_interp_dev_ro (σ : wgstate) :
    weak_state_interp σ ⊢ dev_interp (wgdev σ) ∗
      (dev_interp (wgdev σ) -∗ weak_state_interp σ).
  Proof.
    iIntros "H". iDestruct (weak_state_interp_dev σ with "H") as "[$ Hcl]".
    iIntros "Hd". iDestruct ("Hcl" with "Hd") as "H".
    by iEval (rewrite (ewg_dev_id σ)) in "H".
  Qed.

  (** THE READ-ONLY BORROW: the log authority and the latest-write map,
      handed out and taken back AT THE SAME LOG.  This is all a disk READ
      needs — it changes no σ field at all. *)
  Lemma weak_state_interp_lat (σ : wgstate) :
    weak_state_interp σ ⊢ ⌜wlog_wf (wglog σ)⌝ ∗
      wlog_auth (wglog σ) ∗ wlat_interp (wgimg σ) (wglog σ) ∗
      (wlog_auth (wglog σ) -∗ wlat_interp (wgimg σ) (wglog σ) -∗
         weak_state_interp σ).
  Proof.
    rewrite /weak_state_interp /wgen_pin.
    iIntros "([%Hpow %Hgen0] & %Hbnd & %Hnv & %Hwf & Hgr & Hd & Hlog & Hlat & Hws)".
    iFrame "Hlog Hlat". iSplitR; [by iPureIntro|].
    iIntros "Hlog Hlat". iFrame "Hgr Hd Hlog Hlat Hws".
    iPureIntro. split_and!; done.
  Qed.

  (** THE DMA APPEND.  [ws_bounded] survives by [ws_bounded_mono] (no hart's
      view moved), the φ conjunct by [no_violation_dma] (the author is not a
      hart), [wlog_wf] by [Forall_app].  The [wlat_interp] retarget is the
      CALLER's — header (E). *)
  Lemma weak_state_interp_dma (σ : wgstate) :
    weak_state_interp σ ⊢ ⌜wlog_wf (wglog σ)⌝ ∗
      wlog_auth (wglog σ) ∗ wlat_interp (wgimg σ) (wglog σ) ∗
      (∀ ms : list wmsg, ⌜wlog_wf ms⌝ -∗
         wlog_auth (wglog σ ++ ms) -∗ wlat_interp (wgimg σ) (wglog σ ++ ms) -∗
         weak_state_interp (ewg_log σ (wglog σ ++ ms))).
  Proof.
    rewrite /weak_state_interp /wgen_pin /ewg_log.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    iIntros "([%Hpow %Hgen0] & %Hbnd & %Hnv & %Hwf & Hgr & Hd & Hlog & Hlat & Hws)".
    iFrame "Hlog Hlat". iSplitR; [by iPureIntro|].
    iIntros (ms) "%Hms Hlog Hlat". iFrame "Hgr Hd Hlog Hlat Hws".
    iPureIntro. split_and!.
    - exact Hpow.
    - exact Hgen0.
    - intros c. apply (ws_bounded_mono _ _ _ (Hbnd c)).
      rewrite length_app. lia.
    - exact (no_violation_dma (wglog σ) ms (wgws σ) Hnv Hbnd).
    - by apply Forall_app.
  Qed.

End interp.

(* ====================================================================== *)
(** ** 3. The core lifting rule — the twin of [WeakEvLift.ewp_ecycle] *)

Section core.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma ewp_edisk (gen : nat) (dp : option (DM dres)) (dws : wstate) :
    gen = 0%nat ->
    (∀ σ, weak_state_interp σ ={⊤,∅}=∗
       ⌜exists e' σ', edisk_step gen dp dws σ e' σ'⌝ ∗
       ▷ (∀ e' σ', ⌜edisk_step gen dp dws σ e' σ'⌝ ={∅,⊤}=∗
            weak_state_interp σ' ∗ EWP e' @ ⊤)) -∗
    EWP (EDisk gen dp dws) @ ⊤.
  Proof.
    iIntros (Hgen) "H".
    iApply (wp_lift_step (Λ := weak_ev_lang)); first done.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct (weak_state_interp_pin σ with "Hσ") as %[Hpow Hgen0].
    have Hlive : ethread_live σ gen
      by rewrite /ethread_live Hgen Hgen0; split.
    iMod ("H" $! σ with "Hσ") as "[%Hred Hk]".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (e' & σ' & Hstep).
      exists [], e', σ', []. right; right; left. exists gen, dp, dws.
      split_and!; try reflexivity. left. by split. }
    iIntros (e2 σ2 efs Hstep) "!>".
    apply eprim_step_disk_inv in Hstep as (-> & -> & Harm).
    destruct Harm as [(_ & Hd)|(Hnl & _)]; [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! e2 σ2 with "[//]") as "[$ $]". by iModIntro.
  Qed.

End core.

(* ====================================================================== *)
(** ** 4. THE LATCH ABSORBER (header (B))

    One internal Löb over the plic state, proven ONCE: a rule stated through
    [ewp_edisk_latch] never sees the latch arm. *)

Definition plic_latched : relation plic_state :=
  rtc (fun p1 p2 => plic_latch p1 virtio_irq_id = Some p2).

Global Instance plic_latched_refl : Reflexive plic_latched.
Proof. intros p. apply rtc_refl. Qed.

Section latch.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma ewp_edisk_latch (gen : nat) (dp : option (DM dres)) (dws : wstate)
      (p : plic_state) (EN CONT : iProp Σ) :
    gen = 0%nat ->
    (* ENABLEDNESS, □ and pure-concluding — header (C) *)
    □ (∀ σ : wgstate, EN -∗ weak_state_interp σ -∗
         ⌜exists e' σ', edisk_nolatch gen dp dws σ e' σ'⌝) -∗
    (* THE NODE'S OWN ARM, at whatever plic state the latch loop reached *)
    □ (∀ (p0 : plic_state) (σ : wgstate) (e' : eexpr) (σ' : wgstate),
         ⌜plic_latched p p0⌝ -∗ ⌜edisk_nolatch gen dp dws σ e' σ'⌝ -∗
         plic_frag p0 -∗ EN -∗ CONT -∗ weak_state_interp σ ={⊤}=∗
         weak_state_interp σ' ∗ EWP e' @ ⊤) -∗
    plic_frag p -∗ EN -∗ ▷ CONT -∗
    EWP (EDisk gen dp dws) @ ⊤.
  Proof.
    iIntros (Hgen) "#Hen #Hmain Hp HEN Hcont".
    iAssert (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗ EN -∗
               ▷ CONT -∗ EWP (EDisk gen dp dws) @ ⊤)%I
      with "[]" as "Hgo".
    { iLöb as "IH". iIntros (p0 Hp0) "Hp HEN Hcont".
      iApply (ewp_edisk gen dp dws Hgen). iIntros (σ) "Hσ".
      iAssert (⌜exists e' σ', edisk_nolatch gen dp dws σ e' σ'⌝)%I as %Hred.
      { iApply ("Hen" with "HEN Hσ"). }
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
      iSplitR.
      { iPureIntro. destruct Hred as (e0 & σ0 & Hstep).
        exists e0, σ0. by apply edisk_nolatch_step. }
      iNext. iIntros (e' σ') "%Hstep".
      apply edisk_step_split in Hstep as [Hmain|(p' & Hirq & Hlatch & -> & ->)].
      - iMod "Hmask" as "_".
        iMod ("Hmain" $! p0 σ e' σ' with "[//] [//] Hp HEN Hcont Hσ") as "[$ $]".
        by iModIntro.
      - (* THE LATCH: only [dplic] moves, and nothing but [plic_frag] is
           consumed — so the Löb hypothesis applies with the client's
           premises untouched. *)
        iDestruct (weak_state_interp_dev σ with "Hσ") as "[(Hu & Hpa & Hv) Hcl]".
        iDestruct (plic_agree with "Hpa Hp") as %->.
        iMod (plic_update _ _ p' with "Hpa Hp") as "[Hpa Hp]".
        iMod "Hmask" as "_". iModIntro.
        iSplitL "Hu Hpa Hv Hcl".
        { iApply "Hcl". rewrite /dev_interp /set_dplic /=. iFrame "Hu Hpa Hv". }
        iApply ("IH" $! p' with "[%] Hp HEN [Hcont]").
        + eapply rtc_r; [exact Hp0|exact Hlatch].
        + by iNext. }
    iApply ("Hgo" $! p with "[%] Hp HEN Hcont"). reflexivity.
  Qed.

End latch.

(* ====================================================================== *)
(** ** 5. The per-node rules

    One rule per node of [VirtioProg.DM] plus the start and commit fabric
    arms.  Each is stated through §4's absorber, so NONE of them mentions the
    latch: what the latch costs is the [p0] quantifier and the
    [⌜plic_latched p p0⌝] witness in every continuation (header (B)).

    THERE IS NO RULE FOR [DRet DWild] — header (D). *)

Section rules.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** *** 5a. START ([dp = None]): read the fabric, elaborate the program.

      The client's [virtio_frag v] pins the state the program is elaborated
      from ([virtio_agree]), and is returned untouched — the start arm reads
      the fabric and moves nothing. *)
  Lemma ewp_disk_start (gen : nat) (dws : wstate) (v : virtio_state)
      (p : plic_state) :
    gen = 0%nat ->
    virtio_frag v -∗ plic_frag p -∗
    ▷ (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
         virtio_frag v -∗
         EWP (EDisk gen (Some (virtio_prog v)) dws) @ ⊤) -∗
    EWP (EDisk gen None dws) @ ⊤.
  Proof.
    iIntros (Hgen) "Hv Hp Hcont".
    iApply (ewp_edisk_latch gen None dws p (virtio_frag v)
              (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
                 virtio_frag v -∗
                 EWP (EDisk gen (Some (virtio_prog v)) dws) @ ⊤)%I
              Hgen with "[] [] Hp Hv Hcont").
    - iModIntro. iIntros (σ) "HEN Hσ". iPureIntro.
      do 2 eexists. rewrite /edisk_nolatch. left. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp HEN Hcont Hσ".
      destruct Hstep as [(_ & -> & ->)
                        |[(? & ? & ? & ? & ? & Hdp & _)
                        |[(? & ? & ? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |(Hdp & _)]]]]]]; try discriminate Hdp.
      iDestruct (weak_state_interp_dev_ro σ with "Hσ") as "[(Hu & Hpl & Hva) Hcl]".
      iDestruct (virtio_agree with "Hva HEN") as %->.
      iModIntro. iSplitL "Hu Hpl Hva Hcl".
      { iApply "Hcl". rewrite /dev_interp. iFrame "Hu Hpl Hva". }
      by iApply ("Hcont" with "[//] Hp HEN").
  Qed.

  (** *** 5b. THE DEVICE READ — the racy form, at [dws].

      The twin of [WeakEvLift.ewp_ev_load], with the two differences the
      header records: the continuation is quantified over EVERY read the
      machine admits at the event's own σ (same as the hart), but it owes NO
      φ payment (the interpretation does not constrain the disk's view), and
      the enabledness witness is supplied UP FRONT by [Hen] rather than by
      the callback (header (C)).  [wlat_interp] is lent to the continuation
      unchanged — the read moves no σ field — so that a driver may pin the
      bytes it reads against its own fragments. *)
  Lemma ewp_disk_read (gen : nat) (dws : wstate) (pa : Arch.pa) (n : nat)
      (aq : bool) (kk : list (bv 8) -> DM dres) (p : plic_state)
      (EN : iProp Σ) :
    gen = 0%nat ->
    □ (∀ (img : gmap Arch.pa (bv 8)) (log : list wmsg),
         EN -∗ wlog_lb log -∗ wlat_interp img log -∗
         ⌜exists tvs : list (nat * bv 8), length tvs = n /\
            read_ok (img_z img) log dws aq false (pa_z pa) tvs⌝) -∗
    EN -∗ plic_frag p -∗
    ▷ (∀ (σ : wgstate) (p0 : plic_state) (tvs : list (nat * bv 8)),
         ⌜plic_latched p p0⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗ wlog_lb (wglog σ) -∗
         ⌜length tvs = n⌝ -∗
         ⌜read_ok (img_z (wgimg σ)) (wglog σ) dws aq false (pa_z pa) tvs⌝ -∗
         plic_frag p0 -∗ EN -∗ wlat_interp (wgimg σ) (wglog σ) ={⊤}=∗
         wlat_interp (wgimg σ) (wglog σ) ∗
         EWP (EDisk gen (Some (kk tvs.*2))
                (load_post_run dws aq (pa_z pa) tvs.*1)) @ ⊤) -∗
    EWP (EDisk gen (Some (DRead pa n aq kk)) dws) @ ⊤.
  Proof.
    iIntros (Hgen) "#Hen HEN Hp Hcont".
    iApply (ewp_edisk_latch gen (Some (DRead pa n aq kk)) dws p EN
              (∀ (σ : wgstate) (p0 : plic_state) (tvs : list (nat * bv 8)),
                 ⌜plic_latched p p0⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
                 wlog_lb (wglog σ) -∗ ⌜length tvs = n⌝ -∗
                 ⌜read_ok (img_z (wgimg σ)) (wglog σ) dws aq false
                    (pa_z pa) tvs⌝ -∗
                 plic_frag p0 -∗ EN -∗ wlat_interp (wgimg σ) (wglog σ) ={⊤}=∗
                 wlat_interp (wgimg σ) (wglog σ) ∗
                 EWP (EDisk gen (Some (kk tvs.*2))
                        (load_post_run dws aq (pa_z pa) tvs.*1)) @ ⊤)%I
              Hgen with "[] [] Hp HEN Hcont").
    - iModIntro. iIntros (σ) "HEN Hσ".
      iDestruct (weak_state_interp_lat σ with "Hσ") as "(_ & Hlog & Hlat & _)".
      iDestruct (wlog_snapshot with "Hlog") as "[Hlog #Hlb]".
      iDestruct ("Hen" $! (wgimg σ) (wglog σ) with "HEN Hlb Hlat")
        as %(tvs & Hlen & Hrd).
      iPureIntro. do 2 eexists. rewrite /edisk_nolatch.
      right; left. exists pa, n, aq, kk, tvs. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp HEN Hcont Hσ".
      destruct Hstep as [(Hdp & _)
                        |[(pa0 & n0 & aq0 & k0 & tvs & Hdp & Hlen & Hrd & -> & ->)
                        |[(? & ? & ? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |(Hdp & _)]]]]]]; try discriminate Hdp.
      injection Hdp as <- <- <- <-.
      iDestruct (weak_state_interp_lat σ with "Hσ") as "(%Hwf & Hlog & Hlat & Hcl)".
      iDestruct (wlog_snapshot with "Hlog") as "[Hlog #Hlb]".
      iMod ("Hcont" $! σ p0 tvs with "[//] [//] Hlb [//] [//] Hp HEN Hlat")
        as "[Hlat Hwp]".
      iModIntro. iSplitR "Hwp"; [|iExact "Hwp"].
      iApply ("Hcl" with "Hlog Hlat").
  Qed.

  (** *** 5c. THE DEVICE WRITE — the log append, at [dws].

      The twin of [WeakEvLift.ewp_ev_store].  What the caller supplies is the
      [wlat_interp] RETARGET and nothing else: the φ conjunct is free
      ([WeakGhost.no_violation_dma] — the author is [n_disk], not a hart),
      [ws_bounded] survives by monotonicity because no hart's view moved, and
      the message's [wlog_wf] is the [Hfit] premise (the access does not wrap
      the address space — [WeakLang.wmsg_wf]).  The class stamped is
      [ddev_class dws]: [WCrel] exactly when the disk's own [w_relp] is
      armed, i.e. right after its [DFence]. *)
  Lemma ewp_disk_write (gen : nat) (dws : wstate) (pa : Arch.pa)
      (bs : list (bv 8)) (kk : DM dres) (p : plic_state) :
    gen = 0%nat ->
    bs <> [] ->
    pa_z pa + Z.of_nat (length bs) <= 18446744073709551616 ->
    plic_frag p -∗
    ▷ (∀ (σ : wgstate) (p0 : plic_state),
         ⌜plic_latched p p0⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗ wlog_lb (wglog σ) -∗
         plic_frag p0 -∗ wlat_interp (wgimg σ) (wglog σ) ={⊤}=∗
         wlat_interp (wgimg σ)
           (wglog σ ++ [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)]) ∗
         EWP (EDisk gen (Some kk)
                (store_post_run dws false (pa_z pa) (length bs)
                   (S (length (wglog σ))))) @ ⊤) -∗
    EWP (EDisk gen (Some (DWrite pa bs kk)) dws) @ ⊤.
  Proof.
    iIntros (Hgen Hne Hfit) "Hp Hcont".
    iApply (ewp_edisk_latch gen (Some (DWrite pa bs kk)) dws p emp
              (∀ (σ : wgstate) (p0 : plic_state),
                 ⌜plic_latched p p0⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
                 wlog_lb (wglog σ) -∗
                 plic_frag p0 -∗ wlat_interp (wgimg σ) (wglog σ) ={⊤}=∗
                 wlat_interp (wgimg σ)
                   (wglog σ ++
                    [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)]) ∗
                 EWP (EDisk gen (Some kk)
                        (store_post_run dws false (pa_z pa) (length bs)
                           (S (length (wglog σ))))) @ ⊤)%I
              Hgen with "[] [] Hp [] Hcont").
    - iModIntro. iIntros (σ) "_ Hσ". iPureIntro.
      do 2 eexists. rewrite /edisk_nolatch.
      right; right; left. exists pa, bs, kk. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp _ Hcont Hσ".
      destruct Hstep as [(Hdp & _)
                        |[(? & ? & ? & ? & ? & Hdp & _)
                        |[(pa0 & bs0 & k0 & Hdp & _ & -> & ->)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |(Hdp & _)]]]]]]; try discriminate Hdp.
      injection Hdp as <- <- <-.
      iDestruct (weak_state_interp_dma σ with "Hσ") as "(%Hwf & Hlog & Hlat & Hcl)".
      iDestruct (wlog_snapshot with "Hlog") as "[Hlog #Hlb]".
      iMod (wlog_update (wglog σ)
              [WMsg (pa_z pa) bs (Some n_disk) (ddev_class dws)] with "Hlog")
        as "Hlog".
      iMod ("Hcont" $! σ p0 with "[//] [//] Hlb Hp Hlat") as "[Hlat Hwp]".
      iModIntro. iSplitR "Hwp"; [|iExact "Hwp"].
      iApply ("Hcl" with "[%] Hlog Hlat").
      apply Forall_singleton. rewrite /wmsg_wf /=.
      pose proof (pa_z_range pa). lia.
    - done.
  Qed.

  (** *** 5d. THE DEVICE FENCE — pure, [fence rw,rw] at [dws]. *)
  Lemma ewp_disk_fence (gen : nat) (dws : wstate) (kk : DM dres)
      (p : plic_state) :
    gen = 0%nat ->
    plic_frag p -∗
    ▷ (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
         EWP (EDisk gen (Some kk) (fence_post dws true true true true)) @ ⊤) -∗
    EWP (EDisk gen (Some (DFence kk)) dws) @ ⊤.
  Proof.
    iIntros (Hgen) "Hp Hcont".
    iApply (ewp_edisk_latch gen (Some (DFence kk)) dws p emp
              (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
                 EWP (EDisk gen (Some kk)
                        (fence_post dws true true true true)) @ ⊤)%I
              Hgen with "[] [] Hp [] Hcont").
    - iModIntro. iIntros (σ) "_ Hσ". iPureIntro.
      do 2 eexists. rewrite /edisk_nolatch.
      right; right; right; left. exists kk. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp _ Hcont Hσ".
      destruct Hstep as [(Hdp & _)
                        |[(? & ? & ? & ? & ? & Hdp & _)
                        |[(? & ? & ? & Hdp & _)
                        |[(k0 & Hdp & -> & ->)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |(Hdp & _)]]]]]]; try discriminate Hdp.
      injection Hdp as <-.
      iModIntro. iFrame "Hσ". by iApply ("Hcont" with "[//] Hp").
    - done.
  Qed.

  (** *** 5e. THE COMMIT ([DRet (DDone δ)]): apply the burst's delta to the
      CURRENT fabric state.  The client's [virtio_frag] is what makes "the
      current state" nameable — [virtio_agree] pins it to [v]. *)
  Lemma ewp_disk_commit (gen : nat) (dws : wstate)
      (delta : virtio_state -> virtio_state) (v : virtio_state)
      (p : plic_state) :
    gen = 0%nat ->
    virtio_frag v -∗ plic_frag p -∗
    ▷ (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
         virtio_frag (delta v) -∗ EWP (EDisk gen None dws) @ ⊤) -∗
    EWP (EDisk gen (Some (DRet (DDone delta))) dws) @ ⊤.
  Proof.
    iIntros (Hgen) "Hv Hp Hcont".
    iApply (ewp_edisk_latch gen (Some (DRet (DDone delta))) dws p
              (virtio_frag v)
              (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
                 virtio_frag (delta v) -∗ EWP (EDisk gen None dws) @ ⊤)%I
              Hgen with "[] [] Hp Hv Hcont").
    - iModIntro. iIntros (σ) "_ Hσ". iPureIntro.
      do 2 eexists. rewrite /edisk_nolatch.
      right; right; right; right; left. exists delta. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp HEN Hcont Hσ".
      destruct Hstep as [(Hdp & _)
                        |[(? & ? & ? & ? & ? & Hdp & _)
                        |[(? & ? & ? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(delta0 & Hdp & -> & ->)
                        |[(? & Hdp & _)
                        |(Hdp & _)]]]]]]; try discriminate Hdp.
      injection Hdp as <-.
      iDestruct (weak_state_interp_dev σ with "Hσ") as "[(Hu & Hpl & Hva) Hcl]".
      iDestruct (virtio_agree with "Hva HEN") as %->.
      iMod (virtio_update _ _ (delta (dvirtio (wgdev σ))) with "Hva HEN")
        as "[Hva Hv]".
      iModIntro. iSplitL "Hu Hpl Hva Hcl".
      { iApply ("Hcl" $! (set_dvirtio (wgdev σ) (delta (dvirtio (wgdev σ))))).
        rewrite /dev_interp /set_dvirtio /=. iFrame "Hu Hpl Hva". }
      by iApply ("Hcont" with "[//] Hp Hv").
  Qed.

  (** *** 5f. IDLE ([DRet DIdle]): nothing was pending; back to the start. *)
  Lemma ewp_disk_idle (gen : nat) (dws : wstate) (p : plic_state) :
    gen = 0%nat ->
    plic_frag p -∗
    ▷ (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
         EWP (EDisk gen None dws) @ ⊤) -∗
    EWP (EDisk gen (Some (DRet DIdle)) dws) @ ⊤.
  Proof.
    iIntros (Hgen) "Hp Hcont".
    iApply (ewp_edisk_latch gen (Some (DRet DIdle)) dws p emp
              (∀ p0 : plic_state, ⌜plic_latched p p0⌝ -∗ plic_frag p0 -∗
                 EWP (EDisk gen None dws) @ ⊤)%I
              Hgen with "[] [] Hp [] Hcont").
    - iModIntro. iIntros (σ) "_ Hσ". iPureIntro.
      do 2 eexists. rewrite /edisk_nolatch.
      right; right; right; right; right; right. by split_and!.
    - iModIntro. iIntros (p0 σ e' σ') "%Hlat %Hstep Hp _ Hcont Hσ".
      destruct Hstep as [(Hdp & _)
                        |[(? & ? & ? & ? & ? & Hdp & _)
                        |[(? & ? & ? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |[(? & Hdp & _)
                        |(Hdp & -> & ->)]]]]]]; try discriminate Hdp.
      iModIntro. iFrame "Hσ". by iApply ("Hcont" with "[//] Hp").
    - done.
  Qed.

End rules.

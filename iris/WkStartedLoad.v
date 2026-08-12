(** * WkStartedLoad.v — the [started] WAITER: the racy load through the escrow

    THE COMPOSITION the M3c note at the end of [WeakAcquire.v] asked for, and
    the M4 porting guide §3 calls the one instruction [wp_winstr] cannot run.
    Three landed pieces meet here and nothing else is built:

      - [WeakRacy.wp_wracy_load] — the load rule that quantifies over the
        ADMISSIBLE read results instead of the coherent flat value;
      - [WeakStarted.wstarted_observe] — the escrow's ONE-SHOT COLLAPSE: a
        read that came back non-clear read a timestamp at or above the
        escrow's deposit, and the payload is frozen at that deposit;
      - [WeakAcquire.wwp_fence_step] + [WeakStarted.wstarted_deliver] — the
        [fence rw,rw] that thaws the deposit into the reader's own index.

    ================== THE ONE PREMISE THAT IS NOT FREE ==================

    [wp_wracy_load] hands its caller the WORD [w] the load returned together
    with its per-byte admissibility ([WeakRacy.wadm]), and — separately — the
    certificate's [Q].  It does NOT hand back the timestamps the run read, and
    [Q : wmstate -> wmstate -> Prop] is a relation on STATES, so no [Q] can
    name [w] either.  But the reader needs exactly the pairing: "the timestamp
    at which the byte I READ was admissible is covered by my [w_vrOld]".

    That pairing is [wstarted_gain], and it is a per-instruction ISA
    obligation of the same nature as a decode fact (porting guide §2c).  It is
    a PREMISE here, at the shape that makes it dischargeable: the racy [lw]
    leaf proves it with ALL of [Q], the admissibility, and the caller's own
    [exec] fact at the patched state in hand — and the tie between [Q]'s
    (existentially quantified) word and the rule's [w] is the DESTINATION
    REGISTER, which both pin: [Q] says "the run read some word [u] at
    timestamps [w_vrOld] covers, and [rd] holds [u]", the [exec] fact at
    [WeakRacy.wpatch_st σ a 4 w] says "[rd] holds [w]", and the register
    imprint is injective.  Nothing in [WeakRacy] had to change for that.

    THE OTHER SIDE CONDITION is [WeakStarted.wstarted_img_clear] — the era
    image holds the flag cleared — which the escrow's MINT
    ([WeakStarted.wstarted_alloc]) hands out and which travels as a pure fact
    because [wm_img] is constant along every step.  It is a conjunct the
    caller's own σ-callback returns, exactly like [P σ]. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakExec.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakCert.
Require Import WeakLock.
Require Import WeakStarted.
Require Import WeakRacy.
Require Import WeakAcquire.
Require Import RiscvLang RiscvPtsto RiscvExec.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The load's own gain, and the byte that witnesses a non-clear word *)

(** HISTORICAL NOTE.  This file used to open with a [wstarted_gain]
    definition — "for every byte of the flag word, the timestamp at which the
    byte the load RETURNED was admissible is covered by the successor's read
    floor" — taken as a PREMISE, on the grounds that it is a per-instruction
    ISA obligation of §2c's kind.  It is not: [WeakRacy.wgain] is the same
    statement and [WeakRacy.exec_of_wrun_gain] PROVES it, from the same
    traversal that produces [wadm], for any hart that has not stored to the
    window ([WeakRacy.wunwritten]).  What the leaf still owes is
    [WeakRacy.wreads_win], which carries no weak-memory content at all. *)

(** A word that is not the cleared one differs from it at some byte — the
    witness the collapse is applied at. *)
Lemma bv32_ne_zero_byte (w : bv 32) :
  w <> lock_zero ->
  exists j : nat, (j < 4)%nat /\ nth_byte w j <> nth_byte lock_zero 0.
Proof.
  intros Hne.
  destruct (decide (nth_byte w 0 = nth_byte lock_zero 0)) as [E0|Hb];
    [|exists 0%nat; split; [lia|exact Hb]].
  destruct (decide (nth_byte w 1 = nth_byte lock_zero 0)) as [E1|Hb];
    [|exists 1%nat; split; [lia|exact Hb]].
  destruct (decide (nth_byte w 2 = nth_byte lock_zero 0)) as [E2|Hb];
    [|exists 2%nat; split; [lia|exact Hb]].
  destruct (decide (nth_byte w 3 = nth_byte lock_zero 0)) as [E3|Hb];
    [|exists 3%nat; split; [lia|exact Hb]].
  exfalso. apply Hne. apply (bv_eq_of_bytes (n := 4%N)). intros j Hj.
  assert (Hj4 : (j < 4)%nat) by lia.
  rewrite (nth_byte_clear j Hj4).
  destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
Qed.

Section wp_started_load.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types P : vProp Σ.

(* ====================================================================== *)
(** ** 2. THE RECEIPT: what crosses from the load to the fence

    The deposit, together with the fact that this hart's read floor already
    covers it.  Everything about the ESCROW is gone by then — this is the
    whole reader-side residue of the load, and it is exactly what
    [WeakStarted.wstarted_deliver] / [WeakAcquire.wwp_started_fence_deliver]
    consume.  It is persistent whenever the payload is (which the escrow
    requires anyway: every secondary hart takes a copy). *)

  Definition wstarted_rcpt P (ws : wstate) : iProp Σ :=
    (∃ T : nat, ⌜(T <= w_vrOld ws)%nat⌝ ∗ monPred_at P (view_scl T))%I.

  Global Instance wstarted_rcpt_persistent P `{!Persistent P} ws :
    Persistent (wstarted_rcpt P ws).
  Proof. apply _. Qed.

  (** It survives the steps between the load and the fence: [w_vrOld] only
      grows ([WeakMem.ws_le]), and every step contract in the tree carries
      [ws_le] ([WeakInstr.wstep_post], [WeakRacy.wstep_post_racy]). *)
  Lemma wstarted_rcpt_mono P (ws ws' : wstate) :
    ws_le ws ws' -> wstarted_rcpt P ws -∗ wstarted_rcpt P ws'.
  Proof.
    intros Hle. iIntros "H". iDestruct "H" as (T) "[%HT HP]".
    iExists T. iFrame "HP". iPureIntro.
    destruct Hle as (_ & Hold & _). lia.
  Qed.

  (** ... and any PRED-R fence cashes it.  The kernel's is [fence r,rw]
      ([kernel.asm], [main+0x18] — gcc's [__ATOMIC_ACQUIRE] load fence), not
      [fence rw,rw]; [WeakFence.acq_pred_r] is the property that makes the
      difference invisible here. *)
  Lemma wstarted_rcpt_deliver_gen P (σ : wmstate) (ws' : wstate)
      (b : barrier_kind) :
    acq_pred_r b ->
    wV_fence b σ ws' ->
    wstarted_rcpt P (wm_ws σ) -∗ vwp_hold P ws'.
  Proof.
    intros Hb HQ. iIntros "H". iDestruct "H" as (T) "[%HT HP]".
    by iApply (wstarted_deliver_gen P σ ws' T b Hb HT HQ with "HP").
  Qed.

  Lemma wstarted_rcpt_deliver P (σ : wmstate) (ws' : wstate) :
    wV_fence Barrier_RISCV_rw_rw σ ws' ->
    wstarted_rcpt P (wm_ws σ) -∗ vwp_hold P ws'.
  Proof. exact (wstarted_rcpt_deliver_gen P σ ws' _ acq_pred_r_rw_rw). Qed.

(* ====================================================================== *)
(** ** 3. THE WAITER'S LOAD — one racy [lw] through the escrow

    Read the statement as [WeakRacy.wp_wracy_load] with three changes and
    nothing else, in the shape [WeakAcquire] §3 established for a racy leaf:

      - the caller's callback runs at ⊤∖↑wstartedN (the escrow is open), and
        it borrows the LATEST-WRITE AUTHORITY and hands it straight back — it
        only ever reads it;
      - it no longer has to prove the flag word is IN memory: the escrow's own
        element bundle says so ([WeakLock.wlat4_flat_gen] +
        [WeakRacy.read_bytes_of_bytes]);
      - its post-step continuation receives, besides the rule's own
        [w]/[wadm]/[exec]/[Q], the READ OUTCOME: either the word was the
        cleared one and nothing was gained, or it was not and the RECEIPT has
        been collapsed out of the escrow. *)

  Definition wstarted_ld_cb (a : Arch.pa) P (pc : SailStdpp.Values.mword 64)
      (rak : akinfo) (Pp : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop)
      : iProp Σ :=
    (∀ σ : wmstate,
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑wstartedN, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜Pp σ⌝ ∗
         ⌜wstarted_img_clear σ a⌝ ∗
         ⌜wunwritten (wm_ws σ) a 4⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         (∃ t0 : mstate,
            ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝) ∗
         ▷ (∀ (tick : bool) (σ' : wmstate) (w : bv 32),
              ⌜wadm σ rak a 4 w⌝ -∗
              ⌜exec (riscv_step tick) (wpatch_st σ a 4 w)
               = Some (tt, wpatch_st σ' a 4 w)⌝ -∗
              ⌜wstep_post_racy σ σ'⌝ -∗
              ⌜Q σ σ'⌝ -∗
              (⌜w = lock_zero⌝ ∨ ⌜w ≠ lock_zero⌝ ∗ wstarted_rcpt P (wm_ws σ')) -∗
              |={∅, ⊤ ∖ ↑wstartedN}=> wmstate_rest σ' ∗ WWP Loop))%I.

  (** THE TWO PREMISES THAT REPLACED THE VIEW OBLIGATION.  [ak_coh rak = false]
      says this is a weak-tier access (a coherent fetch/walker read moves no
      view and so gains nothing); [Hreads] says the step READS the window,
      which is the whole per-instruction residue of the old [wstarted_gain]
      and contains no weak-memory content.  The reader's own side condition —
      "I have never stored to the flag" — is [wunwritten], and it comes out of
      the caller's σ-callback like [wstarted_img_clear] does. *)
  Lemma wwp_started_load (a : Arch.pa) P `{!Persistent P}
      (pc : SailStdpp.Values.mword 64) (rak : akinfo)
      (Pp : wmstate -> Prop) (Q : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acc_wf a 4 →
    ak_coh rak = false →
    (∀ σ σ' : wmstate, Q σ σ' → wm_log σ' = wm_log σ) →
    (∀ (tick : bool) (σ : wmstate), Pp σ → wreads_win a 4 tick σ) →
    wracy_cert (fin_to_nat cpu_id) pc a 4 rak wadm_any Pp Q →
    (* φ-upgrade, deliverable A: the flag word is a SYNC window.  The escrow's
       mint ([WeakStarted.wstarted_alloc]) hands this out, and it is what
       [WeakRacy.wp_wracy_load_gain] now demands. *)
    sync_win a 4 -∗
    inv wstartedN (wstarted_body a P) -∗
    wstarted_ld_cb a P pc rak Pp Q -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hacca Hakc Hquiet Hreads Hcert) "#Hsync #Hinv Hk".
    rewrite /wstarted_ld_cb.
    iApply (wp_wracy_load_gain pc a 4 rak wadm_any Pp Q Hgid Haccpc Hacca Hakc
              Hcert with "Hsync").
    iIntros (σ) "Hσ".
    (* the log lower bound the escrow's snapshot is read against — persistent,
       so taking it costs the caller nothing *)
    iDestruct (wmstate_interp_log_lb σ with "Hσ") as "[Hσ #Hlbσ]".
    iDestruct (wmstate_interp_split σ with "Hσ") as "[Hlat Hrest]".
    iDestruct (wmstate_rest_facts with "Hrest") as %[Hbnd Hwf].
    (* open the escrow at ⊤, keep it across the step; the ELEMENT bundle is
       timeless and comes out now — the payload stays under the later *)
    iInv wstartedN as (te v) "(>Hw & Hhist)" "Hclose".
    iDestruct (wlat4_sync_flat_gen σ a te v Hwf Hacca with "Hlat Hw")
      as %[Hflat _].
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & %Himg & %Hun & Hlat & Ht0 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    (* the flag's value is unconstrained: the code branches on it itself *)
    iSplitR; [iPureIntro; apply wadm_filter_any|].
    iSplitR.
    { iPureIntro. exists v.
      exact (read_bytes_of_bytes (wflat (wm_img σ) (wm_log σ)) a 4 v Hflat). }
    iDestruct "Ht0" as (t0) "%Hex0".
    iSplitR; [iExists t0; by iPureIntro|].
    iNext. iIntros (tick σ' w) "%Hadm %Hex %Hpost %HQ %Hgd".
    (* the patch-independence arm cannot happen at a LOAD *)
    assert (Hgain : wgain σ σ' rak a 4 w).
    { destruct Hgd as [Hg|Huni]; [exact Hg|].
      exfalso. exact (Hreads tick σ HP (ex_intro _ σ' Huni)). }
    iAssert (wstarted_body a P) with "[Hw Hhist]" as "Hbody".
    { iExists te, v. iFrame "Hw". iExact "Hhist". }
    (* THE COLLAPSE, in the non-clear arm *)
    iAssert (|==> wlat_interp (wm_img σ) (wm_log σ) ∗ wstarted_body a P ∗
               (⌜w = lock_zero⌝ ∨ ⌜w ≠ lock_zero⌝ ∗ wstarted_rcpt P (wm_ws σ')))%I
      with "[Hbody Hlat]" as ">(Hlat & Hbody & Harm)".
    { destruct (decide (w = lock_zero)) as [->|Hne].
      { iModIntro. iFrame "Hlat Hbody". iLeft. by iPureIntro. }
      destruct (bv32_ne_zero_byte w Hne) as (j & Hj & Hbne).
      destruct (Hgain j ltac:(simpl; lia)) as (t & Hok & Hcov).
      iDestruct (wstarted_observe a P σ rak j t (nth_byte w j)
                   Himg Hj Hok Hbne with "Hlbσ Hlat Hbody")
        as "(Hlat & Hbody & _ & Hrcpt)".
      iDestruct "Hrcpt" as (T) "[%HTle HP0]".
      iModIntro. iFrame "Hlat Hbody". iRight. iSplitR; [by iPureIntro|].
      iExists T. iFrame "HP0". iPureIntro. lia. }
    iMod ("Hcont" $! tick σ' w with "[%] [%] [%] [%] Harm")
      as "[Hrest $]"; [exact Hadm|exact Hex|exact Hpost|exact HQ|].
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iApply (wmstate_interp_split σ'). iFrame "Hrest".
    destruct Hpost as (Himg' & _ & _ & _ & _).
    rewrite Himg' (Hquiet σ σ' HQ). iExact "Hlat".
  Qed.

(* ====================================================================== *)
(** ** 4. THE WAITER'S FENCE — one [fence rw,rw] that cashes the receipt

    [WeakAcquire.wwp_fence_step] with the receipt consumed and the payload
    handed to the continuation AT THE SUCCESSOR'S INDEX.  A fence touches no
    memory, so nothing is borrowed and the mask stays ⊤; the whole
    weak-memory content is the one [WeakStarted.wstarted_deliver]. *)

  Definition wstarted_fence_cb P (pc : SailStdpp.Values.mword 64)
      (Pf : wmstate -> Prop) : iProp Σ :=
    (∀ σ : wmstate,
       wmstate_interp σ ={⊤,∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pc⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pc j)⌝ ∗
         ⌜Pf σ⌝ ∗
         wstarted_rcpt P (wm_ws σ) ∗
         (∃ t0 t1 : mstate,
            ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝ ∗
            ⌜exec (riscv_step true) (wflat_st σ) = Some (tt, t1)⌝ ∗
            ▷ (∀ (tick : bool) (σ' : wmstate),
                 ⌜wstep_post σ σ' (if tick then t1 else t0)⌝ -∗
                 vwp_hold P (wm_ws σ') -∗
                 |={∅,⊤}=> wmstate_interp σ' ∗ WWP Loop)))%I.

  Lemma wwp_started_fence_gen P (pc : SailStdpp.Values.mword 64)
      (Pf : wmstate -> Prop) (b : barrier_kind) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    acq_pred_r b →
    wstep_cert (fin_to_nat cpu_id) pc Pf (wQ_fence b) →
    wstarted_fence_cb P pc Pf -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hb Hcert) "Hk". rewrite /wstarted_fence_cb.
    iApply (wwp_fence_step pc b Pf Hgid Haccpc Hcert).
    iIntros (σ) "Hσ".
    iMod ("Hk" $! σ with "Hσ") as "(%Hpc & %Htext & %HP & Hrcpt & Hc)".
    iDestruct "Hc" as (t0 t1) "(%Hex0 & %Hex1 & Hcont)".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iExists t0, t1.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ') "%Hpost %HQ %HQrelp".
    iApply ("Hcont" $! tick σ' with "[%]"); [exact Hpost|].
    by iApply (wstarted_rcpt_deliver_gen P σ (wm_ws σ') b Hb HQ with "Hrcpt").
  Qed.

  Lemma wwp_started_fence P (pc : SailStdpp.Values.mword 64)
      (Pf : wmstate -> Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc Pf (wQ_fence Barrier_RISCV_rw_rw) →
    wstarted_fence_cb P pc Pf -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert).
    iApply (wwp_started_fence_gen P pc Pf _ Hgid Haccpc acq_pred_r_rw_rw Hcert).
  Qed.

  (** THE KERNEL'S OWN FENCE: [fence r,rw] at [main+0x18]. *)
  Lemma wwp_started_fence_r P (pc : SailStdpp.Values.mword 64)
      (Pf : wmstate -> Prop) :
    gen_id = 0%nat →
    acc_wf pc 4 →
    wstep_cert (fin_to_nat cpu_id) pc Pf (wQ_fence Barrier_RISCV_r_rw) →
    wstarted_fence_cb P pc Pf -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccpc Hcert).
    iApply (wwp_started_fence_gen P pc Pf _ Hgid Haccpc acq_pred_r_r_rw Hcert).
  Qed.

(* ====================================================================== *)
(** ** 5. SMOKE TEST: [lw] ; [fence r,rw], the handoff end to end

    xv6's secondary-hart wait is

      while (__atomic_load_n(&started, __ATOMIC_ACQUIRE) == 0) ;

    which gcc compiles to [lw a5,0(a4) ; fence r,rw ; sext.w ; beqz] with the
    acquire fence INSIDE the loop ([kernel.asm], [main+0x16 .. +0x1e]).  This
    is its LAST iteration composed at the WP altitude: the racy load
    observes a non-clear flag and collapses the escrow into a receipt, the
    fence cashes the receipt, and the payload [P] arrives at the reader's own
    index.  Nothing glues the two steps but [wstep_post] / [wstep_post_racy] —
    the successor of the first is the pre-state of the second, and the caller
    never sees a view (the receipt's transport across the gap is
    [wstarted_rcpt_mono], which is one [ws_le]).

    (An [Example], not a theorem of record: what it checks is that the racy
    load, the escrow's collapse and the fence meet with no adapter.) *)

  Example wwp_started_wait_seq (a : Arch.pa) P `{!Persistent P}
      (pcl pcf : SailStdpp.Values.mword 64) (rak : akinfo)
      (Pl Pf : wmstate -> Prop) (Ql : wmstate -> wmstate -> Prop) :
    gen_id = 0%nat →
    acc_wf pcl 4 →
    acc_wf pcf 4 →
    acc_wf a 4 →
    ak_coh rak = false →
    (∀ σ σ' : wmstate, Ql σ σ' → wm_log σ' = wm_log σ) →
    (∀ (tick : bool) (σ : wmstate), Pl σ → wreads_win a 4 tick σ) →
    wracy_cert (fin_to_nat cpu_id) pcl a 4 rak wadm_any Pl Ql →
    wstep_cert (fin_to_nat cpu_id) pcf Pf (wQ_fence Barrier_RISCV_r_rw) →
    sync_win a 4 -∗
    inv wstartedN (wstarted_body a P) -∗
    (∀ σ : wmstate,
       wlat_interp (wm_img σ) (wm_log σ) -∗
       wmstate_rest σ ={⊤ ∖ ↑wstartedN, ∅}=∗
         ⌜register_lookup PC (wm_regs σ) = pcl⌝ ∗
         ⌜∀ j : nat, (j < 4)%nat → pinned_read σ (acc_addr pcl j)⌝ ∗
         ⌜Pl σ⌝ ∗
         ⌜wstarted_img_clear σ a⌝ ∗
         ⌜wunwritten (wm_ws σ) a 4⌝ ∗
         wlat_interp (wm_img σ) (wm_log σ) ∗
         (∃ t0 : mstate,
            ⌜exec (riscv_step false) (wflat_st σ) = Some (tt, t0)⌝) ∗
         ▷ (∀ (tick : bool) (σ' : wmstate) (w : bv 32),
              ⌜wadm σ rak a 4 w⌝ -∗
              ⌜exec (riscv_step tick) (wpatch_st σ a 4 w)
               = Some (tt, wpatch_st σ' a 4 w)⌝ -∗
              ⌜wstep_post_racy σ σ'⌝ -∗
              ⌜Ql σ σ'⌝ -∗
              (⌜w = lock_zero⌝ ∨ ⌜w ≠ lock_zero⌝ ∗ wstarted_rcpt P (wm_ws σ')) -∗
              |={∅, ⊤ ∖ ↑wstartedN}=>
                wmstate_rest σ' ∗
                (* the CLEARED arm is the spin loop's retry edge and carries
                   no weak-memory content at all; the other one exits to the
                   fence with the receipt in hand *)
                (WWP Loop ∨ wstarted_fence_cb P pcf Pf))) -∗
    WWP Loop.
  Proof.
    iIntros (Hgid Haccl Haccf Hacca Hakc Hquiet Hreads Hcertl Hcertf)
      "#Hsync #Hinv Hk".
    iApply (wwp_started_load a P pcl rak Pl Ql Hgid Haccl Hacca Hakc Hquiet
              Hreads Hcertl with "Hsync Hinv").
    iIntros (σ) "Hlat Hrest".
    iMod ("Hk" $! σ with "Hlat Hrest")
      as "(%Hpc & %Htext & %HP & %Himg & %Hun & Hlat & Ht0 & Hcont)".
    iDestruct "Ht0" as (t0) "%Hex0".
    iModIntro. iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iFrame "Hlat".
    iSplitR; [iExists t0; by iPureIntro|].
    iNext. iIntros (tick σ' w) "%Hadm %Hex %Hpost %HQ Harm".
    iMod ("Hcont" $! tick σ' w with "[%] [%] [%] [%] Harm") as "[$ Hnext]";
      [exact Hadm|exact Hex|exact Hpost|exact HQ|].
    iModIntro. iDestruct "Hnext" as "[Hloop|Hf]"; [iExact "Hloop"|].
    iApply (wwp_started_fence_r P pcf Pf Hgid Haccf Hcertf with "Hf").
  Qed.

End wp_started_load.

(* The escrow/collapse layer is CLOSED under the global context
   ([WeakStarted.wstarted_alloc] / [wstarted_set] / [wstarted_observe] /
   [wstarted_reader], and §§1–2 here); the three WP-level lemmas below name
   [riscv_step] and so carry the five sail platform axioms
   ([plat_term_write] + the reservation quartet), like the rest of the tree. *)
Print Assumptions bv32_ne_zero_byte.

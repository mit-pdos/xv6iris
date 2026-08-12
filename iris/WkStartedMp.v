(** * WkStartedMp.v — xv6's BOOT HANDOFF as a message-passing theorem

    THE EXAMPLE THAT IS NOT A SPINLOCK.  Every fence-mediated transfer proved
    so far in the weak tier has been the lock's release/acquire pair, where the
    acquiring hart's [amoswap.w.aq] does the work with no fence at all
    ([WeakFence.release_acquire_transfer]).  xv6's boot handoff is the other
    shape — plain store, plain load, two ORDINARY fences — and it is the one
    the kernel actually uses to hand every secondary hart the results of hart
    0's initialisation.  [kernel/main.c]:

      volatile static int started = 0;
      ...
        userinit();
        __atomic_store_n(&started, 1, __ATOMIC_RELEASE);      // hart 0
      } else {
        while (__atomic_load_n(&started, __ATOMIC_ACQUIRE) == 0)
          ;                                                   // every other hart
        printk("hart %d starting\n", cpuid());

    which gcc compiles to ([kernel.asm]):

      main+0xac   fence rw,w          main+0x16   lw    a5,0(a4)
      main+0xb0   sw   a4,0(a5)       main+0x18   fence r,rw
                                      main+0x1c   sext.w a5,a5
                                      main+0x1e   beqz  a5,main+0x16

    WHERE THE ORDERING ACTUALLY COMES FROM, in this machine.  Not from the
    writer's [fence rw,w]: promise-free, a store lands at the log's fresh top,
    which dominates the writer's whole index, so the release deposit
    ([WeakFence.release_deposit]) needs no fence at all — the pred-W fence is
    inert here by design (design doc, Decision 1).  ALL of the content is on
    the reader: a plain load gains the timestamp it read only at the BYTE it
    read ([WeakFence.load_byte_gain] — the flag's byte, not the payload's), and
    it is [fence r,rw] that turns that into a SCALAR index gain and so
    delivers the deposit.  §3 makes that precise in both directions: the same
    load with and without the fence, one delivering the payload and one
    provably not.

    Nothing here is new machinery.  §1 is [WeakStarted.wstarted_set], §2 is
    [WeakStarted.wstarted_reader] at [Barrier_RISCV_r_rw] (which it can be
    since [WeakFence.acq_pred_r] — before that the delivery lemmas were stated
    at [rw,rw] only and the kernel's own fence did not fit), and §4 is
    [WeakVProp.wpt_load_rule].  What the file adds is the COMPOSITION, and the
    statement a reader of the kernel would want: the byte a secondary hart
    loads after its acquire fence is the byte hart 0 wrote before its release.

    WHAT IS STILL ABOVE THIS FILE: the per-instruction leaves.  [main] is an
    S-mode function and the weak funnel is M-mode only, so the four waiter
    instructions cannot yet be RUN — that is batch 6c.  Everything below is at
    the σ altitude the leaves would hand it. *)
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
Require Import WkStartedLoad.
Require Import RiscvLang RiscvPtsto RiscvExec.

Local Open Scope Z_scope.

Section mp.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types P : vProp Σ.

(* ====================================================================== *)
(** ** 1. HART 0: the release

    [WeakStarted.wstarted_set] with the escrow repackaged, so the two sides
    compose over the SAME [wstarted_body].  Note the premises: the [sw]'s own
    step effect ([wQ_store]) and the machine invariant [ws_bounded] — and NOT
    a word about the [fence rw,w] that precedes it. *)

  Lemma wstarted_mp_release (a : Arch.pa) P (tid : option nat)
      (σ σ' : wmstate) :
    wQ_store tid a lock_one σ σ' ->
    (* φ-upgrade §1: the [fence rw,w] that precedes the [started] store is
       what keeps the escrow's bundle CLEAN across it. *)
    w_relp (wm_ws σ) = true ->
    ws_bounded (wm_ws σ) (length (wm_log σ)) ->
    wlog_lb (wm_log σ) -∗
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wstarted_body a P -∗
    vwp_hold P (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ wstarted_body a P.
  Proof.
    intros HQ Hrelp Hbnd. iIntros "#Hlb Hi Hbody HP".
    iMod (wstarted_set a P tid σ σ' HQ Hrelp Hbnd with "Hlb Hi Hbody HP")
      as "[Hi Hat]".
    iModIntro. iFrame "Hi". iExists (S (length (wm_log σ))), lock_one.
    iExact "Hat".
  Qed.

(* ====================================================================== *)
(** ** 2. HART k: the withdrawal

    [WeakStarted.wstarted_reader] at the kernel's own fence kind.  Read it as:
    a hart whose plain load of the flag came back NON-CLEAR read a timestamp
    at or above the escrow's deposit, and its [fence r,rw] delivers the
    deposit to its own index.

    THE ONE VIEW PREMISE, [t ≤ w_vrOld (wm_ws σf)], is no longer an assumption
    about the instruction: it is [WeakRacy.wgain], which
    [WeakRacy.exec_of_wrun_gain] PROVES from the model for any hart that has
    not itself stored to the flag ([WeakRacy.wunwritten] — a secondary hart
    never writes [started]).  It used to be [WkStartedLoad.wstarted_gain], a
    per-instruction premise.

    WHY THE TWO SIDES ARE NOT ONE LEMMA.  [wlat_interp] is the authority over
    the latest-write map, so no proposition can hold it at hart 0's state and
    at hart k's later state at once — a lemma quantifying over both would have
    unsatisfiable premises.  The two halves are joined by the machine, and the
    escrow is the only medium: [wstarted_body a P] is under an [inv], hence
    shared, and it is literally the same [P] on both sides.  That IS the
    handoff. *)

  Lemma wstarted_mp_acquire (a : Arch.pa) P `{!Persistent P}
      (σr σf : wmstate) (ws' : wstate)
      (rak : akinfo) (j t : nat) (b : bv 8) :
    (* the racy load came back NON-CLEAR at timestamp [t] *)
    wstarted_img_clear σr a ->
    (j < 4)%nat ->
    wbyte_ok σr rak (acc_addr a j) t b ->
    b <> nth_byte lock_zero 0 ->
    (* the load's own gain, and the acquire fence at main+0x18 *)
    (t <= w_vrOld (wm_ws σf))%nat ->
    wV_fence Barrier_RISCV_r_rw σf ws' ->
    wlog_lb (wm_log σr) -∗
    (wlat_interp (wm_img σr) (wm_log σr) : iProp Σ) -∗
    wstarted_body a P -∗
      wlat_interp (wm_img σr) (wm_log σr) ∗
      wstarted_body a P ∗
      ⌜b = nth_byte lock_one j⌝ ∗
      vwp_hold P ws'.
  Proof.
    intros Himg Hj Hok Hne Hgain HF. iIntros "#Hlb Hi Hbody".
    iApply (wstarted_reader a P σr σf ws' rak j t b Barrier_RISCV_r_rw
              Himg Hj Hok Hne Hgain acq_pred_r_r_rw HF with "Hlb Hi Hbody").
  Qed.

(* ====================================================================== *)
(** ** 3. WHY THE FENCE IS THERE

    Both directions, at the machine's own step functions and on the SAME load:
    a plain load of the flag at the deposited timestamp [T], by a hart with an
    empty forward bank and an empty index.

    (a) WITHOUT the fence the payload does not arrive.  The load raises the
        hart's [w_vrOld] to [T] and its COHERENCE floor at the flag's byte to
        [T] — and nothing else.  The deposit sits at [view_scl T], which is a
        floor at EVERY address; so any address the hart has not touched is
        still at 0, and the deposit is not covered.  That is not a gap in the
        proof: it is the [MP] litmus test's non-SC outcome, and a machine that
        delivered here would be unsound.

    (b) WITH [fence r,rw] it does, because a pred-R fence lifts [w_vrOld] into
        the scalar component of the index ([WeakFence.acq_pred_r]). *)

  Lemma mp_load_alone_does_not_deliver (T : nat) (a : Z) :
    (0 < T)%nat ->
    ¬ (view_scl T ⊑ ws_view (load_post ws_init false a T)).
  Proof.
    intros HT Hle. specialize (Hle (a + 1)%Z).
    rewrite flr_scl_eq flr_ws_view in Hle.
    assert (Hc : coh (load_post ws_init false a T) (a + 1)%Z = 0%nat).
    { rewrite /load_post /load_post_at /coh /=.
      rewrite lookup_insert_ne; [by rewrite lookup_empty|lia]. }
    assert (Hn : w_vrNew (load_post ws_init false a T) = 0%nat) by reflexivity.
    rewrite Hc Hn in Hle. lia.
  Qed.

  Lemma mp_fence_delivers (T : nat) (a : Z) :
    view_scl T
    ⊑ ws_view (barrier_post (load_post ws_init false a T) Barrier_RISCV_r_rw).
  Proof.
    apply view_scl_acq_pred_r; [apply acq_pred_r_r_rw|].
    exact (load_post_vrOld_nofwd ws_init false a T eq_refl).
  Qed.

  (** ... and the same contrast one level up, on the payload itself: what the
      fence turns into an index gain is exactly what makes [vwp_hold P] hold.
      (The [ws_le] is the machine's own "views only grow" between the load and
      the fence — [WeakInstr.wstep_post].) *)
  Lemma mp_payload_arrives P (ws_r : wstate) (T : nat) :
    (T <= w_vrOld ws_r)%nat ->
    monPred_at P (view_scl T)
    ⊢ vwp_hold P (barrier_post ws_r Barrier_RISCV_r_rw).
  Proof.
    intros HT. rewrite /vwp_hold. apply monPred_mono.
    by apply view_scl_acq_pred_r; [apply acq_pred_r_r_rw|].
  Qed.

(* ====================================================================== *)
(** ** 4. THE PAYOFF: the secondary hart's next load reads hart 0's value

    The handoff is only interesting because of what the payload IS.  Take the
    smallest instance — one byte hart 0 wrote and then persisted, which is the
    shape every conjunct of xv6's own [main_deposit] has (it is a persistent
    proposition, so that all seven secondaries may take a copy).  After the
    acquire fence, hart k holds it AT ITS OWN INDEX, and then
    [WeakVProp.wpt_load_rule] collapses its next plain load: every admissible
    timestamp for that byte carries hart 0's value.  No staleness is
    reachable. *)

  Corollary wstarted_mp_byte (a : Arch.pa) (d : Z) (v : bv 8)
      (σr σf σn : wmstate)
      (rak akn : akinfo) (j t t' : nat) (b bn : bv 8) :
    (* --- hart k's racy flag load, non-clear, and its acquire fence --- *)
    wstarted_img_clear σr a ->
    (j < 4)%nat ->
    wbyte_ok σr rak (acc_addr a j) t b ->
    b <> nth_byte lock_zero 0 ->
    (t <= w_vrOld (wm_ws σf))%nat ->
    wV_fence Barrier_RISCV_r_rw σf (wm_ws σn) ->
    (* --- and then a PLAIN load of [d] at some state with the same log,
           returning byte [bn] --- *)
    ak_coh akn = false ->
    wm_img σn = wm_img σr ->
    wm_log σn = wm_log σr ->
    wbyte_ok σn akn d t' bn ->
    wlog_lb (wm_log σr) -∗
    (wlat_interp (wm_img σr) (wm_log σr) : iProp Σ) -∗
    wstarted_body a (d ↦w□ v) -∗
      wlat_interp (wm_img σn) (wm_log σn) ∗
      wstarted_body a (d ↦w□ v) ∗
      ⌜bn = v⌝.
  Proof.
    intros Himg Hj Hok Hne Hgain HF Hcoh Hi' Hl' Hokn.
    iIntros "#Hlb Hi Hbody".
    iDestruct (wstarted_mp_acquire a (d ↦w□ v) σr σf (wm_ws σn) rak j t b
                 Himg Hj Hok Hne Hgain HF with "Hlb Hi Hbody")
      as "(Hi & Hbody & _ & HPr)".
    rewrite -Hi' -Hl'.
    iDestruct (wpt_load_rule σn σn akn d DfracDiscarded v t' bn
                 Hcoh Hokn eq_refl eq_refl ltac:(lia) with "[Hi] HPr")
      as "(%Hv & Hi & _)".
    { by rewrite Hi' Hl'. }
    rewrite Hi' Hl'. iFrame "Hi Hbody". by iPureIntro.
  Qed.

End mp.

(* The whole file is escrow/view arithmetic over the σ altitude: no
   [riscv_step], hence no platform axioms. *)
Print Assumptions mp_load_alone_does_not_deliver.
Print Assumptions mp_fence_delivers.

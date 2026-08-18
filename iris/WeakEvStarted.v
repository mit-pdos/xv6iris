(** * WeakEvStarted.v — the [started] handshake at EVENT granularity (spike S5)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    "expression-resident monad" and "reflective batching is MANDATORY"
    sections); worklist [claude-notes/projects/weak-memory-event-lang.md]
    (deliverable S5).

    THE COMPARISON THIS FILE EXISTS TO MAKE.  The instruction-atomic handshake
    is [WeakAcquire.wwp_started_set] (the publisher) and
    [WkStartedLoad.wwp_started_load] / [wwp_started_fence_r] /
    [wwp_started_wait_seq] (the subscriber), all of them stated as "ONE
    INSTRUCTION, from [WWP Loop] to [WWP Loop], given that instruction's
    certification".  §§1–3 below restate the three INSTRUCTION rules, at the
    same altitude and the same scope, over [WeakEvLang] — "ONE INSTRUCTION, from
    [EWP (ELoop 0 c)] to [EWP (ELoop 0 c)], given that instruction's
    certification" — where the certification is now
    [WeakEvLift.erun_silent]-shaped: a computed silent stretch per gap and one
    memory-event rule per event.  §5 instantiates the publisher's
    certification at the REAL kernel instruction ([main+0xb0],
    [c.sw a4,0(a5)] = 0xc398) by [vm_compute], which is where the design's
    O(1)-per-site claim is tested; §6 is the naive per-node calibration point
    the design asks for, and is an ANTI-PATTERN, not an interface.

    ================== WHAT CARRIES OVER UNCHANGED ==================

    ALL of [WeakStarted]: the escrow ([wstarted_body]/[wstarted_at], the
    one-shot lower bound, [wstarted_alloc]), its writer ([wstarted_set]) and
    its reader ([wstarted_observe]) are σ-ALTITUDE lemmas over
    [WeakInterp.wmstate], and the event language's σ projects to exactly that
    at each hart ([WeakLang.whart_view]).  They are used here VERBATIM — not
    restated, not re-proved, not weakened.  That is the S4 header's finding
    (F3)(d) confirmed at a whole function: the escrow's monotone, snapshot-
    based discipline is granularity-independent.

    ================== WHAT CHANGES, AND WHAT IT COSTS ==================

    (S5-1) THE EVENTS OF ONE INSTRUCTION ARE VISIBLE, so a leaf's premises are
      per-event: the FETCH is an ordinary plain RAM read (measured, §5: this
      model's fetch request classifies as [AK_explicit] plain, NOT as
      [AK_ifetch] — so it takes [ewp_ev_load], the same rule as a racy data
      load, and its text bytes must be justified by [read_ok] at the fetch
      event's own σ).  The caller supplies that justification in the same
      place it supplies [WeakBridge.pinned_read] today, and one conjunct more:
      that every admissible read of the text returns the SAME word (the
      event-granular reading of "the text is pinned"), which is what lets the
      certification's next stretch apply.

    (S5-2) THE ESCROW IS OPENED AROUND ONE EVENT, not around one instruction.
      [WkStartedLoad.wwp_started_load] holds the escrow open across the whole
      instruction (its callback runs at ⊤∖↑wstartedN); here it is opened at
      the data event and closed at the data event, and the fetch — which is a
      memory event too — happens OUTSIDE it.  Finding (F5) confirmed.

    (S5-3) THE INTERFERENCE-STABILITY QUESTION IS ANSWERED BY THE STATEMENT.
      Nothing here mentions the instruction's pre-state: each event's rule is
      at that event's own σ, and the log may have grown in between.  The two
      places the instruction-atomic proof needed the log NOT to move
      ([WeakRacy.wadm_down]'s [wm_log s2 = wm_log s] and
      [WeakInstr.wQ_load_w]'s log-quiet conjunct) have no counterpart here and
      no replacement.  Finding (F3)(a)/(b) confirmed at a whole function. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakLang.
Require Import WeakBridge.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakInstr.
Require Import WeakStore.
Require Import WeakLock.
Require Import WeakStarted.
Require Import WeakRacy.
Require Import WkStartedLoad.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import ColdBoot.
Require Import Kernel.KernelSyms.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.
Require Import WeakEvLift.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The two bridges between the event σ and the escrow's altitude

    Both are definitional: [WeakLang.whart_view] IS the hart's [wmstate], and
    [WeakPromise.read_ok] at a non-coherent, non-exclusive access IS
    [WeakInterp.wbyte_ok] per byte. *)

Lemma whart_view_img (σ : wgstate) (c : CPU) :
  wimg (whart_view σ c) = img_z (wgimg σ).
Proof. reflexivity. Qed.

(** The admissibility of ONE read event, bundled: [WeakEvLift]'s two RAM rules
    carry these three conjuncts separately (they are three [⌜⌝] arguments of
    the callback); a leaf reads better with them named. *)
Definition eread_adm (σ : wgstate) (ws : wstate) (n : N)
    (req : Interface.ReadReq.t n) (w : bv (8 * n))
    (tvs : list (nat * bv 8)) : Prop :=
  length tvs = N.to_nat n /\
  (forall j : nat, (j < N.to_nat n)%nat -> tvs.*2 !! j = Some (nth_byte w j)) /\
  read_ok (img_z (wgimg σ)) (wglog σ) ws
    (ak_sync (classify (Interface.ReadReq.access_kind req))) false
    (pa_z (Interface.ReadReq.pa req)) tvs.

Definition eread_ws (σ : wgstate) (ws : wstate) (n : N)
    (req : Interface.ReadReq.t n) (tvs : list (nat * bv 8)) : wstate :=
  load_post_run ws (ak_sync (classify (Interface.ReadReq.access_kind req)))
    (pa_z (Interface.ReadReq.pa req)) tvs.*1.

Section started_ev.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P : vProp Σ.

  (** THE BRIDGE from the tree's kernel-text resource to [WeakEvLift]'s
      window form.  [WeakInstr.wkernel_text bs] is a big-op of PERSISTENT
      era-image elements [wlat_pointsto (pa_z a) DfracDiscarded 0 b] over an
      [Arch.pa]-keyed map; the log — and hence [WeakEvLift.etext] — is keyed
      at [Z], and [WeakBridge.acc_wf_byte] is the conversion.  This is the
      whole connection between the fetch rule (F7) and the tree's existing
      pinned-text discipline; it is stated HERE rather than in [WeakEvLift]
      so that the event tier keeps no dependency on the superseded
      instruction-atomic files. *)
  Lemma wkernel_text_etext_word (bs : gmap Arch.pa (bv 8)) (pa : Arch.pa)
      (n : N) (w : bv (8 * n)) :
    acc_wf pa n ->
    (forall j : nat, (j < N.to_nat n)%nat ->
       bs !! pa_add pa j = Some (nth_byte w j)) ->
    wkernel_text bs -∗ etext_word (pa_z pa) n w.
  Proof.
    intros Hacc Hdom. iIntros "#Ht". rewrite /etext_word.
    iApply big_sepL_intro. iIntros "!>" (i j Hj).
    apply lookup_seq in Hj as [-> Hlt]. simpl.
    rewrite /etext -/(acc_addr pa i) -(acc_wf_byte pa n i Hacc Hlt).
    by iDestruct (big_sepM_lookup _ _ _ _ (Hdom i Hlt) with "Ht") as "$".
  Qed.

(* ====================================================================== *)
(** ** 1. THE PUBLISHER — [sw a4,0(a5)] with a4 = 1, a5 = &started

    [WeakAcquire.wwp_started_set] at event granularity.  Read the premises in
    three groups: the CERTIFICATION (three cursor equations, all [eq_refl] —
    the stretches are UNEVALUATED COMPOSITIONS, nothing is named), the NODE
    PROJECTIONS (three small [vm_cast_no_check]s: the fetch's request, the
    store's request, and "the tail ends at [Ret]"), and the RESOURCES (the
    escrow, the pinned text, the hart's view with the release fence's
    [w_relp] already set, the register frame, the payload).

    The store event's obligations are discharged HERE, from the escrow, by
    [WeakStarted.wstarted_set] — verbatim, at [whart_view].  The FETCH costs
    ONE application of [WeakEvLift.ewp_ev_seq_fetch] and nothing else: no
    callback, no [read_ok], no φ payment (finding F7's answer). *)

  Lemma ewp_ev_started_set (a : Arch.pa) P (c : CPU) (D : gset register)
      (m : M unit) (ws : wstate) (rs : regstate) (n1 n2 n3 : nat)
      (x1 x2 x3 : ecur)
      (nf : N) (reqf : Interface.ReadReq.t nf) (wf : bv (8 * nf))
      (reqw : Interface.WriteReq.t 4) :
    (* --- the certification: three unevaluated compositions --- *)
    x1 = esil n1 D (rs, m) ->
    x2 = esil n2 D (ecur_read (bv_unsigned wf) x1) ->
    x3 = esil n3 D (ecur_write x2) ->
    (* --- the three nodes, by TOTAL PROJECTION --- *)
    eread_req_at nf x1.2 = Some reqf ->
    ewrite_req_at 4 x2.2 = Some reqw ->
    enode_tag x3.2 = 0%nat ->
    (* --- the fetch node: a plain RAM read, of PINNED TEXT --- *)
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqf)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqf)) = false ->
    (* --- the store node: the flag word --- *)
    dev_addr (Interface.WriteReq.pa reqw) = false ->
    Interface.WriteReq.pa reqw = a ->
    Interface.WriteReq.value reqw = lock_one ->
    acc_wf a 4 ->
    (* --- the release fence ran (φ-upgrade §1, as in [wwp_started_set]) --- *)
    w_relp ws = true ->
    wstarted_inv a P -∗
    etext_word (pa_z (Interface.ReadReq.pa reqf)) nf wf -∗
    hart_ws c ws -∗ ereg_frame c rs D -∗ vwp_hold P ws -∗
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗
         hart_ws c ws' -∗ ereg_frame c x3.1 D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hx1 Hx2 Hx3 Hnf Hnw Htag Hdevf Hcohf Hlatf Hdevw Hpaw Hvalw Hacc
             Hrelp) "#Hinv #Htext Hws Hrf HP Hcont".
    subst x1 x2 x3.
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_fetch 0%nat c D n1 (rs, m) nf reqf wf ws
              eq_refl Hnf Hdevf Hcohf Hlatf with "Htext Hws Hrf").
    iNext. iIntros (ws0) "%Hd0 Hws Hrf".
    set (wsf := efetch_ws ws0
                  (ak_sync (classify (Interface.ReadReq.access_kind reqf)))
                  (pa_z (Interface.ReadReq.pa reqf)) nf).
    have Hle_f : ws_le ws wsf.
    { etrans; [by apply ws_depmove_le|apply efetch_ws_le]. }
    have Hrelpf : w_relp wsf = true.
    { rewrite /wsf efetch_ws_relp. by rewrite (ws_depmove_relp _ _ Hd0). }
    iDestruct (vwp_hold_mono P ws wsf Hle_f with "HP") as "HP".
    (* ---------------- the STORE event ---------------- *)
    iApply (ewp_ev_seq_store 0%nat c D n2
              (ecur_read (bv_unsigned wf) (esil n1 D (rs, m))) 4 reqw wsf
              eq_refl Hnw Hdevw ltac:(done) ltac:(by rewrite Hpaw)
              with "Hws Hrf").
    iIntros (wsf') "%Hdf'". iIntros (σ2) "%Hws2 %Hwf2 %Hbnd2 #Hlb2 Hlat2".
    iDestruct (vwp_hold_mono P wsf wsf' (ws_depmove_le _ _ Hdf') with "HP")
      as "HP".
    iInv wstartedN as "Hbody" "Hclose".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask". iNext.
    iMod "Hmask" as "_".
    (* the φ payment is the escrow's own SYNC window, read off the body
       BEFORE the set ([WeakStore.nv_ok_wlat4_sync]) *)
    iDestruct "Hbody" as (t0 v0) "[Hw0 Hhist]".
    iDestruct (nv_ok_wlat4_sync c (wgimg σ2) (wglog σ2) a t0 v0
                 with "Hlat2 Hw0") as %Hnvok.
    iAssert (wstarted_body a P) with "[Hw0 Hhist]" as "Hbody".
    { iExists t0, v0. iFrame "Hw0". iExact "Hhist". }
    (* the successor's hart state, in the escrow's own vocabulary *)
    set (kcl := wm_class_of (classify (Interface.WriteReq.access_kind reqw))
                  wsf').
    set (msg := wwrite_msg (Some (fin_to_nat c)) kcl
                  (Interface.WriteReq.pa reqw) 4 (Interface.WriteReq.value reqw)).
    (* D3-2: the store's post-view carries the ADDRESS and DATA operand views
       into the forward bank (PARM's [FwdItem]).  The leaf does not know
       them — [ewp_ev_seq_store] hands them over universally quantified — and
       does not need to: every fact it takes off the post-state ([ws_le],
       [wV_store_w]) holds at ANY [va]/[vd]. *)
    set (wsw := fun va vd =>
                  store_post_run_d wsf'
                    (ak_sync (classify (Interface.WriteReq.access_kind reqw)))
                    va vd
                    (pa_z (Interface.WriteReq.pa reqw)) (N.to_nat 4)
                    (S (length (wglog σ2)))).
    set (σm' := fun va vd =>
                  WMState (wgregs σ2 c) (wgimg σ2) (wglog σ2 ++ [msg])
                    (wsw va vd) (wgdev σ2)).
    have Hrelpf' : w_relp wsf' = true.
    { by rewrite (ws_depmove_relp _ _ Hdf'). }
    have HQ : forall va vd,
      wQ_store (Some (fin_to_nat c)) a lock_one (whart_view σ2 c) (σm' va vd).
    { intros va vd. rewrite /wQ_store /wQ_store_w. split_and!.
      - reflexivity.
      - exists kcl. split.
        + rewrite /σm' /msg /= Hpaw Hvalw. reflexivity.
        + intros _. rewrite /kcl. by apply wm_class_of_relp.
      - rewrite /σm' /wsw /=. rewrite Hws2. apply store_post_run_d_le.
      - rewrite /wV_store_w /σm' /wsw /=. intros j Hj.
        rewrite /whart_view /=. rewrite -Hpaw /acc_addr.
        by apply flr_store_post_run_d. }
    have Hrelp2 : w_relp (wm_ws (whart_view σ2 c)) = true.
    { rewrite /whart_view. cbn [wm_ws]. rewrite Hws2. exact Hrelpf'. }
    have Hbnd2' : ws_bounded (wm_ws (whart_view σ2 c))
                    (length (wm_log (whart_view σ2 c))).
    { rewrite /whart_view. cbn [wm_ws wm_log]. rewrite Hws2. exact Hbnd2. }
    iMod (wstarted_set a P (Some (fin_to_nat c)) (whart_view σ2 c)
            (σm' 0%nat 0%nat) (HQ 0%nat 0%nat) Hrelp2 Hbnd2'
            with "[Hlb2] [Hlat2] Hbody [HP]")
      as "[Hlat2 Hat]".
    { rewrite /whart_view. cbn [wm_log]. iExact "Hlb2". }
    { rewrite /whart_view. cbn [wm_img wm_log]. iExact "Hlat2". }
    { rewrite /whart_view. cbn [wm_ws]. rewrite Hws2. iExact "HP". }
    iMod ("Hclose" with "[Hat]") as "_".
    { iNext. iExists (S (length (wglog σ2))), lock_one. iExact "Hat". }
    iModIntro. iSplitR.
    { iPureIntro. intros j Hj. rewrite Hpaw. by apply Hnvok. }
    rewrite /σm' /=. iFrame "Hlat2".
    iIntros (va vd) "Hws Hrf".
    (* ---------------- the TAIL: back to the boundary ---------------- *)
    iApply (ewp_ev_seq_ret 0%nat c D n3
              (ecur_write (esil n2 D
                 (ecur_read (bv_unsigned wf) (esil n1 D (rs, m)))))
              (wsw va vd) eq_refl Htag with "Hws Hrf").
    iIntros (ws3) "%Hd3 Hws Hrf". iApply ("Hcont" $! ws3 with "[%] Hws Hrf").
    etrans; [|by apply ws_depmove_le]. rewrite /wsw.
    etrans; [exact Hle_f|]. etrans; [by apply ws_depmove_le|].
    apply store_post_run_d_le.
  Qed.

(* ====================================================================== *)
(** ** 2. THE SUBSCRIBER'S LOAD — [lw a5,0(a4)] through the escrow

    [WkStartedLoad.wwp_started_load] at event granularity.  The differences
    are exactly the two the header names: the escrow is opened around the DATA
    event only (the fetch happens outside it, at full ⊤), and the read's
    admissibility is stated at the read event's own σ — there is no
    [WeakRacy.wadm_down] and no frozen log.

    RECORDED DEVIATION.  The baseline additionally RELIEVES the caller of
    proving the flag word is in memory (it reads that off the escrow's element
    bundle through [WeakLock.wlat4_sync_flat_gen]).  Here the enabling witness
    is part of the caller's flag callback, like the fetch's.  It is a
    convenience, not weak-memory content: the collapse, the receipt and the
    view gain — everything the handshake turns on — are discharged below. *)

  Definition ev_rcpt P (ws : wstate) : iProp Σ :=
    (∃ T : nat, ⌜(T <= w_vrOld ws)%nat⌝ ∗ monPred_at P (view_scl T))%I.

  Global Instance ev_rcpt_persistent P `{!Persistent P} ws :
    Persistent (ev_rcpt P ws).
  Proof. apply _. Qed.

  Lemma ev_rcpt_mono P (ws ws' : wstate) :
    ws_le ws ws' -> ev_rcpt P ws -∗ ev_rcpt P ws'.
  Proof.
    intros Hle. iIntros "H". iDestruct "H" as (T) "[%HT HP]".
    iExists T. iFrame "HP". iPureIntro.
    pose proof (ws_le_vrOld ws ws' Hle). lia.
  Qed.

  (** The caller's obligation at the FLAG event — the twin of the fetch's, at
      the escrow's mask, with the two side conditions [WkStartedLoad] carries:
      the era image holds the flag cleared, and this hart has never stored to
      it ([WeakRacy.wunwritten], which is what makes the read unforwarded). *)
  Definition ev_flag_cb (c : CPU) (a : Arch.pa) (ws : wstate)
      (req : Interface.ReadReq.t 4) : iProp Σ :=
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤ ∖ ↑wstartedN,∅}=∗
         ⌜exists (w : bv (8 * 4)) tvs, eread_adm σ ws 4 req w tvs⌝ ∗
         ⌜wstarted_img_clear (whart_view σ c) a⌝ ∗
         ⌜wunwritten ws a 4⌝ ∗
         ▷ (∀ (w : bv (8 * 4)) (tvs : list (nat * bv 8)),
              ⌜eread_adm σ ws 4 req w tvs⌝ ={∅,⊤ ∖ ↑wstartedN}=∗
                ⌜forall a0 : Z,
                   (coh ws a0 < coh (eread_ws σ ws 4 req tvs) a0)%nat ->
                   nv_ok (wglog σ) c a0⌝ ∗
                wlat_interp (wgimg σ) (wglog σ)))%I.

  (** D3-2: the receipt arm travels with the view, exactly as [ev_rcpt]
      does — needed because the tail's silent stretch may now move the
      hart's view (PARM's [step_assign] on the load's own [rd]). *)
  Lemma ev_rcpt_arm_mono P `{!Persistent P} (ws ws' : wstate) (w : bv 32) :
    ws_le ws ws' ->
    (⌜w = lock_zero⌝ ∨ ⌜w <> lock_zero⌝ ∗ ev_rcpt P ws) -∗
    (⌜w = lock_zero⌝ ∨ ⌜w <> lock_zero⌝ ∗ ev_rcpt P ws').
  Proof.
    intros Hle. iIntros "[H|[H Hr]]"; [by iLeft|].
    iRight. iFrame "H". by iApply (ev_rcpt_mono P ws ws' Hle).
  Qed.

  Lemma ewp_ev_started_load (a : Arch.pa) P `{!Persistent P} (c : CPU)
      (D : gset register) (m : M unit) (ws : wstate) (rs : regstate)
      (n1 n2 n3 : nat) (x1 x2 : ecur)
      (nf : N) (reqf : Interface.ReadReq.t nf) (wf : bv (8 * nf))
      (reql : Interface.ReadReq.t 4) :
    (* --- the certification: the tail is PARAMETRIC in the word read, and it
       is a composition, not a family of named residuals --- *)
    x1 = esil n1 D (rs, m) ->
    x2 = esil n2 D (ecur_read (bv_unsigned wf) x1) ->
    eread_req_at nf x1.2 = Some reqf ->
    eread_req_at 4 x2.2 = Some reql ->
    (forall w : bv (8 * 4),
       enode_tag (esil n3 D (ecur_read (bv_unsigned w) x2)).2 = 0%nat) ->
    (* --- the fetch node --- *)
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqf)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqf)) = false ->
    (* --- the flag node: a plain (racy) read of the flag word --- *)
    dev_addr (Interface.ReadReq.pa reql) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reql)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reql)) = false ->
    Interface.ReadReq.pa reql = a ->
    wstarted_inv a P -∗
    etext_word (pa_z (Interface.ReadReq.pa reqf)) nf wf -∗
    hart_ws c ws -∗ ereg_frame c rs D -∗
    (∀ ws0 : wstate, ⌜ws_le ws ws0⌝ -∗ ev_flag_cb c a ws0 reql) -∗
    ▷ (∀ (ws' : wstate) (w : bv (8 * 4)), ⌜ws_le ws ws'⌝ -∗
         (⌜w = lock_zero⌝ ∨ ⌜w <> lock_zero⌝ ∗ ev_rcpt P ws') -∗
         hart_ws c ws' -∗
         ereg_frame c (esil n3 D (ecur_read (bv_unsigned w) x2)).1 D -∗
         EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hx1 Hx2 Hnf Hnl Htag Hdevf Hcohf Hlatf Hdevl Hcohl Hlatl Hpal)
      "#Hinv #Htext Hws Hrf Hflag Hcont".
    subst x1 x2.
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_fetch 0%nat c D n1 (rs, m) nf reqf wf ws
              eq_refl Hnf Hdevf Hcohf Hlatf with "Htext Hws Hrf").
    iNext. iIntros (ws0) "%Hd0 Hws Hrf".
    set (wsf0 := efetch_ws ws0
                   (ak_sync (classify (Interface.ReadReq.access_kind reqf)))
                   (pa_z (Interface.ReadReq.pa reqf)) nf).
    have Hle_f0 : ws_le ws wsf0.
    { etrans; [by apply ws_depmove_le|apply efetch_ws_le]. }
    (* ---------------- the FLAG event, escrow open ---------------- *)
    iApply (ewp_ev_seq_load 0%nat c D n2
              (ecur_read (bv_unsigned wf) (esil n1 D (rs, m))) 4 reql wsf0
              eq_refl Hnl Hdevl Hcohl Hlatl with "Hws Hrf").
    iIntros (wsf) "%Hdf". iIntros (σ2) "%Hws2 %Hwf2 %Hbnd2 #Hlb2 Hlat2".
    have Hle_f : ws_le ws wsf.
    { etrans; [exact Hle_f0|by apply ws_depmove_le]. }
    iDestruct ("Hflag" $! wsf with "[//]") as "Hflag".
    iInv wstartedN as "Hbody" "Hclose".
    iMod ("Hflag" $! σ2 with "[//] [//] [//] Hlb2 Hlat2")
      as "(%Hen2 & %Himg & %Hunw & Hfk2)".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hen2 as (w & tvs2 & Hadm). by exists w, tvs2. }
    iNext. iIntros (w tvs2) "%G1 %G2 %G3".
    iMod ("Hfk2" $! w tvs2 with "[%]") as "(%Hpay2 & Hlat2)"; [by split_and!|].
    (* THE COLLAPSE, in the non-clear arm — [WeakStarted.wstarted_observe]
       verbatim, at [whart_view σ2 c] *)
    set (wsl := eread_ws σ2 wsf 4 reql tvs2).
    iAssert (wlat_interp (wgimg σ2) (wglog σ2) ∗ wstarted_body a P ∗
             (⌜w = lock_zero⌝ ∨ ⌜w <> lock_zero⌝ ∗ ev_rcpt P wsl))%I
      with "[Hlat2 Hbody]" as "(Hlat2 & Hbody & Harm)".
    { destruct (decide (w = lock_zero)) as [->|Hne].
      { iFrame "Hlat2 Hbody". iLeft. by iPureIntro. }
      destruct (bv32_ne_zero_byte w Hne) as (j & Hj & Hbne).
      (* the byte's timestamp, out of the read's own admissibility *)
      destruct (lookup_lt_is_Some_2 tvs2 j ltac:(rewrite G1; simpl; lia))
        as [[t b] Ht].
      have Hb : b = nth_byte w j.
      { have := G2 j ltac:(simpl; lia).
        rewrite list_lookup_fmap Ht /=. by intros [= <-]. }
      subst b.
      have Hrd2 : read_ok (img_z (wgimg σ2)) (wglog σ2) (wgws σ2 c)
                    (ak_sync (classify (Interface.ReadReq.access_kind reql)))
                    false (pa_z (Interface.ReadReq.pa reql)) tvs2.
      { rewrite Hws2. exact G3. }
      have Hok0 := read_ok_wbyte_ok σ2 c
                     (classify (Interface.ReadReq.access_kind reql))
                     (pa_z (Interface.ReadReq.pa reql)) tvs2 j t (nth_byte w j)
                     Hcohl Hlatl Hrd2 Ht.
      have Hok : wbyte_ok (whart_view σ2 c)
                   (classify (Interface.ReadReq.access_kind reql))
                   (acc_addr a j) t (nth_byte w j).
      { rewrite /acc_addr -Hpal. exact Hok0. }
      iDestruct (wstarted_observe a P (whart_view σ2 c)
                   (classify (Interface.ReadReq.access_kind reql)) j t
                   (nth_byte w j) Himg Hj Hok Hbne with "Hlb2 [Hlat2] Hbody")
        as "(Hlat2 & Hbody & _ & Hrc)".
      { rewrite /whart_view. cbn [wm_img wm_log]. iExact "Hlat2". }
      iDestruct "Hrc" as (T) "[%HTle #HP0]".
      iFrame "Hbody". iSplitL "Hlat2".
      { rewrite /whart_view. cbn [wm_img wm_log]. iExact "Hlat2". }
      iRight. iSplitR; [by iPureIntro|]. iExists T. iFrame "HP0". iPureIntro.
      (* the load's own gain: the timestamp it read is under its read floor *)
      have Hgain : (t <= w_vrOld wsl)%nat.
      { rewrite /wsl /eread_ws.
        have Hjl : (j < length tvs2.*1)%nat by rewrite length_fmap G1; simpl; lia.
        have Ht1 : tvs2.*1 !!! j = t.
        { rewrite list_lookup_total_fmap; [by rewrite (list_lookup_total_correct tvs2 j (t, nth_byte w j) Ht)|].
          rewrite G1. simpl. lia. }
        have := load_post_run_vrOld wsf
                  (ak_sync (classify (Interface.ReadReq.access_kind reql)))
                  (pa_z (Interface.ReadReq.pa reql)) tvs2.*1 j Hjl
                  ltac:(rewrite -/(acc_addr (Interface.ReadReq.pa reql) j) Hpal;
                        apply (Hunw j ltac:(simpl; lia))).
        rewrite Ht1. lia. }
      lia. }
    iMod ("Hclose" with "[Hbody]") as "_"; [by iNext|].
    iModIntro. iFrame "Hlat2". iSplitR; [iPureIntro; exact Hpay2|].
    iIntros "Hws Hrf".
    (* ---------------- the TAIL ---------------- *)
    iApply (ewp_ev_seq_ret 0%nat c D n3
              (ecur_read (bv_unsigned w)
                 (esil n2 D (ecur_read (bv_unsigned wf) (esil n1 D (rs, m)))))
              wsl eq_refl (Htag w) with "Hws Hrf").
    iIntros (ws3) "%Hd3 Hws Hrf".
    iDestruct (ev_rcpt_arm_mono P wsl ws3 w (ws_depmove_le _ _ Hd3) with "Harm")
      as "Harm".
    iApply ("Hcont" $! ws3 w with "[%] Harm Hws Hrf").
    etrans; [|by apply ws_depmove_le].
    rewrite /wsl /eread_ws. etrans; [exact Hle_f|apply load_post_run_le].
  Qed.

(* ====================================================================== *)
(** ** 3. THE SUBSCRIBER'S FENCE — [fence r,rw], which cashes the receipt

    [WkStartedLoad.wwp_started_fence_r] at event granularity.  A fence
    instruction has TWO events here — its own fetch (a plain RAM read) and the
    barrier — where the instruction-atomic rule had one step and no memory
    content at all; the barrier event itself still carries no φ obligation
    ([WeakEvLift.efence_apply_coh]: a fence moves no coherence floor). *)

  Lemma ewp_ev_started_fence P (c : CPU) (D : gset register)
      (m : M unit) (ws : wstate) (rs : regstate) (n1 n2 n3 : nat)
      (x1 x2 x3 : ecur)
      (nf : N) (reqf : Interface.ReadReq.t nf) (wf : bv (8 * nf))
      (b : barrier_kind) :
    (* --- the certification --- *)
    x1 = esil n1 D (rs, m) ->
    x2 = esil n2 D (ecur_read (bv_unsigned wf) x1) ->
    x3 = esil n3 D (ecur_bar x2) ->
    eread_req_at nf x1.2 = Some reqf ->
    ebar_at x2.2 = Some b ->
    enode_tag x3.2 = 0%nat ->
    ebar_park b = None ->
    (* --- the barrier is a PRED-R fence (the kernel's is [fence r,rw]) --- *)
    acq_pred_r b ->
    (* --- the fetch node --- *)
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqf)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqf)) = false ->
    etext_word (pa_z (Interface.ReadReq.pa reqf)) nf wf -∗
    hart_ws c ws -∗ ereg_frame c rs D -∗ ev_rcpt P ws -∗
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ vwp_hold P ws' -∗
         hart_ws c ws' -∗ ereg_frame c x3.1 D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hx1 Hx2 Hx3 Hnf Hnb Htag Hpark Hacq Hdevf Hcohf Hlatf)
      "#Htext Hws Hrf Hrcpt Hcont".
    subst x1 x2 x3.
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_fetch 0%nat c D n1 (rs, m) nf reqf wf ws
              eq_refl Hnf Hdevf Hcohf Hlatf with "Htext Hws Hrf").
    iNext. iIntros (ws0) "%Hd0 Hws Hrf".
    set (wsf := efetch_ws ws0
                  (ak_sync (classify (Interface.ReadReq.access_kind reqf)))
                  (pa_z (Interface.ReadReq.pa reqf)) nf).
    have Hle_f : ws_le ws wsf.
    { etrans; [by apply ws_depmove_le|apply efetch_ws_le]. }
    iDestruct (ev_rcpt_mono P ws wsf Hle_f with "Hrcpt") as "Hrcpt".
    (* ---------------- the BARRIER event ---------------- *)
    iApply (ewp_ev_seq_barrier 0%nat c D n2
              (ecur_read (bv_unsigned wf) (esil n1 D (rs, m))) b wsf
              eq_refl Hnb with "Hws Hrf").
    iNext. iIntros (ws1) "%Hd1 Hws Hrf".
    iDestruct (ev_rcpt_mono P wsf ws1 (ws_depmove_le _ _ Hd1) with "Hrcpt")
      as "Hrcpt".
    (* the barrier's post-view IS [barrier_post], since nothing is parked *)
    have Hbp : efence_apply ws1 (ebar_now b) = barrier_post ws1 b.
    { rewrite -(efence_barrier_post ws1 b) Hpark. reflexivity. }
    set (wsb := efence_apply ws1 (ebar_now b)).
    have Hle_b : ws_le ws1 wsb by apply efence_apply_le.
    (* THE DELIVERY — [WeakStarted.wstarted_deliver_gen], verbatim *)
    iAssert (vwp_hold P wsb) with "[Hrcpt]" as "HP".
    { iDestruct "Hrcpt" as (T) "[%HT HP0]".
      iApply (wstarted_deliver_gen P (WMState rs ∅ [] ws1 dev0_state) wsb T b
                Hacq HT with "HP0").
      rewrite /wV_fence. cbn [wm_ws]. rewrite /wsb Hbp. reflexivity. }
    rewrite Hpark.
    (* ---------------- the TAIL ---------------- *)
    iApply (ewp_ev_seq_ret 0%nat c D n3
              (ecur_bar (esil n2 D
                 (ecur_read (bv_unsigned wf) (esil n1 D (rs, m)))))
              wsb eq_refl Htag with "Hws Hrf").
    iIntros (ws2) "%Hd2 Hws Hrf".
    iDestruct (vwp_hold_mono P wsb ws2 (ws_depmove_le _ _ Hd2) with "HP")
      as "HP".
    iApply ("Hcont" $! ws2 with "[%] HP Hws Hrf").
    etrans; [|by apply ws_depmove_le].
    etrans; [exact Hle_f|]. etrans; [by apply ws_depmove_le|exact Hle_b].
  Qed.

End started_ev.

(* ====================================================================== *)
(* ====================================================================== *)
(** ** 4. THE TWO-INSTRUCTION COMPOSITION — DELIVERED (it was blocked on F8)

    [WkStartedLoad.wwp_started_wait_seq] chains the waiter's load and its
    acquire fence.  Its event-granular twin was blocked on nothing conceptual
    — §2 hands the receipt out, §3 takes it in, and [ev_rcpt_mono] carries it
    across the gap — but on FORM: chaining at the boundary means [ewp_eloop],
    which quantifies over the tick, so the SECOND instruction's certification
    had to be supplied as a family indexed by the tick AND by the word the
    load returned, i.e. as a family of NAMED RESIDUAL MONADS, which F8 says
    cannot be written.  Under the F8-fixed form the family is a family of
    APPLICATIONS ([y1]/[y2]/[y3] below are functions of [w] and [tick] whose
    bodies are compositions), and the chaining is immediate.

    WHAT IT COSTS: nothing in weak-memory content.  The only genuinely new
    obligation is that the fence's certification be UNIFORM IN THE WORD READ —
    the load writes that word into a register, so the fence instruction's
    stretches run over a register file that depends on it.  That is a true
    fact about the composition (the baseline packages the same uniformity
    inside [wstep_cert]'s ∀-over-states), not an artifact.

    (An [Example], not a theorem of record: what it checks is that the racy
    load, the escrow's collapse and the fence meet with no adapter.) *)

Section wait_seq.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Example ewp_ev_started_wait_seq (a : Arch.pa) (P : vProp Σ)
      `{!Persistent P} (c : CPU) (D : gset register)
      (m : M unit) (ws : wstate) (rs : regstate)
      (n1 n2 n3 k1 k2 k3 : nat)
      (x1 x2 : ecur) (x3 : bv (8 * 4) -> ecur)
      (y1 y2 y3 : bv (8 * 4) -> bool -> ecur)
      (nf : N) (reqf : Interface.ReadReq.t nf) (wf : bv (8 * nf))
      (reql : Interface.ReadReq.t 4)
      (gf : N) (reqg : Interface.ReadReq.t gf) (wg : bv (8 * gf))
      (b : barrier_kind) :
    (* --- INSTRUCTION 1, the racy load: §2's certification --- *)
    x1 = esil n1 D (rs, m) ->
    x2 = esil n2 D (ecur_read (bv_unsigned wf) x1) ->
    (forall w : bv (8 * 4), x3 w = esil n3 D (ecur_read (bv_unsigned w) x2)) ->
    eread_req_at nf x1.2 = Some reqf ->
    eread_req_at 4 x2.2 = Some reql ->
    (forall w : bv (8 * 4), enode_tag (x3 w).2 = 0%nat) ->
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqf)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqf)) = false ->
    dev_addr (Interface.ReadReq.pa reql) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reql)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reql)) = false ->
    Interface.ReadReq.pa reql = a ->
    (* --- INSTRUCTION 2, the acquire fence: §3's certification, UNIFORMLY in
       the word read and in the boundary's tick --- *)
    (forall w tick, y1 w tick = esil k1 D (ecur_loop tick (x3 w))) ->
    (forall w tick,
       y2 w tick = esil k2 D (ecur_read (bv_unsigned wg) (y1 w tick))) ->
    (forall w tick, y3 w tick = esil k3 D (ecur_bar (y2 w tick))) ->
    (forall w tick, eread_req_at gf (y1 w tick).2 = Some reqg) ->
    (forall w tick, ebar_at (y2 w tick).2 = Some b) ->
    (forall w tick, enode_tag (y3 w tick).2 = 0%nat) ->
    ebar_park b = None ->
    acq_pred_r b ->
    dev_addr (Interface.ReadReq.pa reqg) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqg)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqg)) = false ->
    wstarted_inv a P -∗
    etext_word (pa_z (Interface.ReadReq.pa reqf)) nf wf -∗
    etext_word (pa_z (Interface.ReadReq.pa reqg)) gf wg -∗
    hart_ws c ws -∗ ereg_frame c rs D -∗
    (∀ ws0 : wstate, ⌜ws_le ws ws0⌝ -∗ ev_flag_cb c a ws0 reql) -∗
    (* the CLEARED arm is the spin loop's retry edge and carries no
       weak-memory content at all *)
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ hart_ws c ws' -∗
         ereg_frame c (x3 lock_zero).1 D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    (* ... and the other one exits through the fence with the payload *)
    ▷ (∀ (ws' : wstate) (w : bv (8 * 4)) (tick : bool),
         ⌜ws_le ws ws'⌝ -∗ ⌜w <> lock_zero⌝ -∗ vwp_hold P ws' -∗
         hart_ws c ws' -∗ ereg_frame c (y3 w tick).1 D -∗
         EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hx1 Hx2 Hx3 Hnf Hnl Htag Hdevf Hcohf Hlatf Hdevl Hcohl Hlatl Hpal
             Hy1 Hy2 Hy3 Hgf Hgb Hgtag Hpark Hacq Hdevg Hcohg Hlatg)
      "#Hinv #Htf #Htg Hws Hrf Hflag Hclear Hexit".
    iApply (ewp_ev_started_load a P c D m ws rs n1 n2 n3 x1 x2 nf reqf wf reql
              Hx1 Hx2 Hnf Hnl
              ltac:(intros w; by rewrite -Hx3)
              Hdevf Hcohf Hlatf Hdevl Hcohl Hlatl Hpal
              with "Hinv Htf Hws Hrf Hflag").
    iNext. iIntros (ws' w) "%Hle Harm Hws Hrf". rewrite -Hx3.
    iDestruct "Harm" as "[->|[%Hne #Hrcpt]]".
    { by iApply ("Hclear" $! ws' with "[//] Hws Hrf"). }
    (* ---- the boundary: the tick is the language's, not the caller's ---- *)
    iApply (ewp_eloop 0%nat c eq_refl). iNext. iIntros (tick).
    (* ---- INSTRUCTION 2: the fence cashes the receipt ---- *)
    iApply (ewp_ev_started_fence P c D (riscv_step tick) ws' (x3 w).1
              k1 k2 k3 (y1 w tick) (y2 w tick) (y3 w tick) gf reqg wg b
              (Hy1 w tick) (Hy2 w tick) (Hy3 w tick)
              (Hgf w tick) (Hgb w tick) (Hgtag w tick) Hpark Hacq
              Hdevg Hcohg Hlatg with "Htg Hws Hrf Hrcpt").
    iNext. iIntros (ws'') "%Hle' HP Hws Hrf".
    iApply ("Hexit" $! ws'' w tick with "[%] [//] HP Hws Hrf").
    by etrans.
  Qed.

End wait_seq.

(** ** 5. THE CONCRETE INSTANTIATION — [main+0xb0], [c.sw a4,0(a5)] = 0xc398
           (S4 gap 4 / F8: where the O(1)-per-site claim is tested)

    xv6's [started = 1] IS a compressed store ([kernel.asm], [main+0xb0]), and
    this section runs the publisher's certification at it, on the REAL
    post-boot register file ([ColdBoot.cold_regs], the tree's own
    computed-once cold-boot state) with [a5 = &started] and [a4 = 1].

    THE RECIPE, IN THE F8-FIXED FORM.  A certification is a CHAIN OF
    UNEVALUATED COMPOSITIONS on [WeakEvLift.ecur] cursors, and every per-site
    fact is a TOTAL PROJECTION with a SMALL output, closed by one
    [vm_cast_no_check].  Nothing below names a residual monad or a register
    file — [ev_x1], [ev_x2], [ev_x3] are DEFINITIONS OF COMPOSITIONS, not of
    computed values, and the VM only ever runs inside a conversion check.

    WHAT THE MEASUREMENT SHOWS (numbers in the worklist's S5 table): the
    instruction is 107 silent nodes to the fetch, 179 (SYMBOLIC model: +1 for the [InstrAnnounce] node) from the fetch to the
    store, and a short tail — 294 in all — and each stretch is ONE application
    plus one VM-checked equation.  The footprint [ev_D] is computed, not
    guessed: [ev_regs] is a measurement-side collector (it is NOT part of the
    proof interface) that lists the registers a stretch touches. *)

(** *** 5a. The measurement-side scaffolding: a footprint collector *)

Definition esil_node_any (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k => Some (rs, k (register_lookup r rs))
       | Interface.RegWrite r _ v => fun k => Some (register_set r v rs, k tt)
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Definition esil_node_reg (m : M unit) : list register :=
  match m with
  | Interface.Ret _ => []
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead r _ => [r]
      | Interface.RegWrite r _ _ => [r]
      | _ => []
      end
  end.

Fixpoint erun_any (n : nat) (rs : regstate) (m : M unit) : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' => match esil_node_any rs m with
            | Some (rs', m') => erun_any n' rs' m'
            | None => (rs, m)
            end
  end.

Fixpoint erun_regs (n : nat) (rs : regstate) (m : M unit) : list register :=
  match n with
  | 0%nat => []
  | S n' => match esil_node_any rs m with
            | Some (rs', m') => app (esil_node_reg m) (erun_regs n' rs' m')
            | None => []
            end
  end.

(** The steps a stretch actually takes AT THE DECLARED FOOTPRINT — which is
    also the test that the footprint is big enough (a short count means
    [erun_silent] stopped at a register outside [D]). *)
Fixpoint erun_count (n : nat) (D : gset register) (rs : regstate) (m : M unit)
    : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => match esil_node D rs m with
            | Some (rs', m') => S (erun_count n' D rs' m')
            | None => 0%nat
            end
  end.

Definition ecount (n : nat) (D : gset register) (x : ecur) : nat :=
  erun_count n D x.1 x.2.

(** *** 5b. The concrete state: the post-boot file, at [main+0xb0] *)

Definition ev_pc : SailStdpp.Values.mword 64 :=
  SailStdpp.Values.mword_of_int (KernelSyms.main + 0xb0).
Definition ev_flag : Arch.pa := SailStdpp.Values.mword_of_int KernelSyms.started.
Definition ev_word : Z := 0xc398.

(** The fetched word, as the [bv] the certification's resume function wants.
    ([eread_resume] takes a [Z] — the width lives in the node — so the cursor
    chain stays simply typed; [Z_to_bv_bv_unsigned] is the round trip, and
    spelling the cursors with [bv_unsigned ev_wf] keeps every certification
    equation an [eq_refl].) *)
Definition ev_wf : bv 16 := Z_to_bv 16 ev_word.

(** THE BASE REGISTER FILE: the tree's own COLD-BOOT file
    ([ColdBoot.cold_regs], the computed output of the model's ~300-write boot
    chain — PMA regions, PMPs, mstatus, misa all as the machine sets them),
    with the two GPRs the instruction reads set to [&started] and 1 and the PC
    at [main+0xb0].

    IT HAS TO BE THAT FILE, and the alternative is a measured trap: over
    [WpDecodeBridge.dregs] (the small decode-reference file, config CSRs zero)
    the same [riscv_step] takes 141 silent nodes and ends at [Ret] WITHOUT a
    fetch — the run traps, because a file with no PMA regions cannot fetch.
    A "concrete register state" that is not the machine's own is not a
    certification of anything. *)
Definition ev_rs0 : regstate :=
  register_set (R_bitvector_64 nextPC) ev_pc
    (register_set (R_bitvector_64 PC) ev_pc
      (register_set (R_bitvector_64 x15) ev_flag
        (register_set (R_bitvector_64 x14)
           (SailStdpp.Values.mword_of_int 1)
           (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))))).

(** THE FOOTPRINT, collected rather than guessed — a list of register names,
    hence a SMALL readback. *)
Definition ev_c1 : regstate * M unit := erun_any 400 ev_rs0 (riscv_step false).
Definition ev_c2 : regstate * M unit :=
  erun_any 600 ev_c1.1 (eread_resume (bv_unsigned ev_wf) ev_c1.2).
Definition ev_Dl : list register :=
  ltac:(let x := eval vm_compute in
          (app (erun_regs 400 ev_rs0 (riscv_step false))
             (app (erun_regs 600 ev_c1.1
                     (eread_resume (bv_unsigned ev_wf) ev_c1.2))
                  (erun_regs 400 ev_c2.1 (ewrite_resume ev_c2.2)))) in
        exact x).
Definition ev_D : gset register := list_to_set ev_Dl.

(** *** 5c. THE CERTIFICATION, as three unevaluated compositions.

    This is the whole F8 fix at a call site: the three cursors below are
    DEFINITIONS OF APPLICATIONS.  Compare the pre-fix form, which needed
    [erun_silent … = (rs', m')] with [rs'] and [m'] WRITTEN OUT — and could
    not be closed, because the readback of one stretch's residual did not
    finish in 110 s while the same run projected to a number finished in
    0.1 s. *)

Definition ev_x0 : ecur := (ev_rs0, riscv_step false).
Definition ev_x1 : ecur := esil 400 ev_D ev_x0.
Definition ev_x2 : ecur := esil 600 ev_D (ecur_read (bv_unsigned ev_wf) ev_x1).
Definition ev_x3 : ecur := esil 400 ev_D (ecur_write ev_x2).

(** THE TWO REQUESTS, by SMALL READBACK of a total projection.  A request is
    a five-field record over a [bv 64], an access kind, an option and a
    boolean — a value, unlike the continuation the old form forced out. *)
Definition ev_reqf : Interface.ReadReq.t 2 :=
  ltac:(let x := eval vm_compute in (eread_req_at 2 ev_x1.2) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a read node" end).

Definition ev_reqw : Interface.WriteReq.t 4 :=
  ltac:(let x := eval vm_compute in (ewrite_req_at 4 ev_x2.2) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a write node" end).

(** *** 5d. THE MEASUREMENT, as compiled evidence.

    Six facts, each a single VM-checked conversion ([vm_cast_no_check], so the
    kernel rechecks with the VM too rather than with its lazy evaluator). *)

(** (i) THE INSTRUCTION'S EVENT STRUCTURE.  107 silent nodes to the fetch,
    179 more to the store, 8 more to [Ret]: 294 silent nodes, three stretches,
    two memory events, one instruction. *)
Lemma ev_len1 : ecount 400 ev_D ev_x0 = 107%nat.
Proof. vm_cast_no_check (eq_refl 107%nat). Qed.
Lemma ev_len2 : ecount 600 ev_D (ecur_read (bv_unsigned ev_wf) ev_x1) = 179%nat.
Proof. vm_cast_no_check (eq_refl 179%nat). Qed.
Lemma ev_len3 : ecount 400 ev_D (ecur_write ev_x2) = 8%nat.
Proof. vm_cast_no_check (eq_refl 8%nat). Qed.

(** (ii) THE FETCH NODE — and it IS the certification premise §1 takes, not a
    paraphrase of it. *)
Lemma ev_fetch_req : eread_req_at 2 ev_x1.2 = Some ev_reqf.
Proof. vm_cast_no_check (eq_refl (Some ev_reqf)). Qed.

(** ... and finding F7, off the request itself: this model's fetch is an
    ORDINARY PLAIN read (width 2 — the instruction is compressed — at
    [main+0xb0], classifying [(coh, latest, sync) = (false, false, false)]),
    NOT an [AK_ifetch] coherent one.  That is why §5c of [WeakEvLift] exists:
    the rule that makes it cheap is derived from the text's immutability, not
    from the access kind. *)
Lemma ev_fetch_plain :
  classify (Interface.ReadReq.access_kind ev_reqf) = AkInfo false false false.
Proof. vm_cast_no_check (eq_refl (AkInfo false false false)). Qed.
Lemma ev_fetch_pa : pa_z (Interface.ReadReq.pa ev_reqf) = 2147487534.
Proof. vm_cast_no_check (eq_refl 2147487534). Qed.

(** (iii) THE STORE NODE: width 4 at [&started], value 1, plain (the release
    is carried by the hart's [w_relp], set by the [fence rw,w] at [main+0xac]
    — exactly as [WeakStarted]'s writer half says). *)
Lemma ev_store_req : ewrite_req_at 4 ev_x2.2 = Some ev_reqw.
Proof. vm_cast_no_check (eq_refl (Some ev_reqw)). Qed.
Lemma ev_store_pa : Interface.WriteReq.pa ev_reqw = ev_flag.
Proof. vm_cast_no_check (eq_refl ev_flag). Qed.
Lemma ev_store_val : Interface.WriteReq.value ev_reqw = lock_one.
Proof. vm_cast_no_check (eq_refl lock_one). Qed.
Lemma ev_store_plain :
  classify (Interface.WriteReq.access_kind ev_reqw) = AkInfo false false false.
Proof. vm_cast_no_check (eq_refl (AkInfo false false false)). Qed.

(** (iv) THE TAIL ENDS AT [Ret]: the instruction has exactly two memory
    events. *)
Lemma ev_tail_ret : enode_tag ev_x3.2 = 0%nat.
Proof. vm_cast_no_check (eq_refl 0%nat). Qed.

(** The two side conditions the store rule needs, likewise computed. *)
Lemma ev_fetch_ram : dev_addr (Interface.ReadReq.pa ev_reqf) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma ev_store_ram : dev_addr (Interface.WriteReq.pa ev_reqw) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma ev_store_wf : acc_wf ev_flag 4.
Proof. rewrite /acc_wf. apply Z.leb_le. vm_cast_no_check (eq_refl true). Qed.

(** *** 5e. THE WHOLE-STRETCH INSTANTIATION — §1's rule AT THE REAL
    INSTRUCTION, every certification premise discharged.

    This is what F8 blocked and what the form change unblocks: the six
    certification premises of [ewp_ev_started_set] are the three [eq_refl]s
    above and the three VM-checked projections, and the leaf applies with no
    residual and no register file ever written down. *)



(** *** 5e. THE WHOLE-STRETCH INSTANTIATION — §1's rule AT THE REAL
    INSTRUCTION, every certification premise discharged.

    This is what F8 blocked and what the form change unblocks: the six
    certification premises of [ewp_ev_started_set] are three [reflexivity]s
    (the cursor chain) and three VM-checked projections, and the leaf applies
    with no residual and no register file ever written down.

    ONE PROOF-ENGINEERING NOTE, MEASURED AND WORTH KEEPING.  The cursor
    equations must be discharged by a [have … by reflexivity] and PASSED, not
    written as a bare [eq_refl] inside the application: [reflexivity] calls
    CONVERSION (which unfolds the cursor definition, sees the same term and
    stops, 0.003 s), whereas a bare [eq_refl] leaves the problem to the
    ELABORATOR'S UNIFIER, which unfolds [esil] instead and starts LAZILY
    EVALUATING the stretch — 5.3 s for the second equation and unbounded for
    the third.  Same statement, same proof term; only the tactic that builds
    it differs. *)

Section instantiated.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma ewp_ev_started_set_at_main (P : vProp Σ) (c : CPU) (ws : wstate) :
    w_relp ws = true ->
    wstarted_inv ev_flag P -∗
    etext_word (pa_z (Interface.ReadReq.pa ev_reqf)) 2 ev_wf -∗
    hart_ws c ws -∗ ereg_frame c ev_rs0 ev_D -∗ vwp_hold P ws -∗
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗
         hart_ws c ws' -∗ ereg_frame c ev_x3.1 ev_D -∗
         EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c (riscv_step false) None) @ ⊤.
  Proof.
    intros Hrelp.
    have H1 : ev_x1 = esil 400 ev_D (ev_rs0, riscv_step false) by reflexivity.
    have H2 : ev_x2 = esil 600 ev_D (ecur_read (bv_unsigned ev_wf) ev_x1)
      by reflexivity.
    have H3 : ev_x3 = esil 400 ev_D (ecur_write ev_x2) by reflexivity.
    iIntros "#Hinv #Ht Hws Hrf HP Hcont".
    iApply (ewp_ev_started_set ev_flag P c ev_D (riscv_step false) ws ev_rs0
              400 600 400 ev_x1 ev_x2 ev_x3 2 ev_reqf ev_wf ev_reqw
              H1 H2 H3 ev_fetch_req ev_store_req ev_tail_ret
              ev_fetch_ram
              ltac:(by rewrite ev_fetch_plain) ltac:(by rewrite ev_fetch_plain)
              ev_store_ram ev_store_pa ev_store_val ev_store_wf Hrelp
              with "Hinv Ht Hws Hrf HP Hcont").
  Qed.

End instantiated.

(** *** 5f. WHAT THE MEASUREMENT SETTLED (finding F8, RESOLVED)

    THE CLAIM UNDER TEST (design, "reflective batching is MANDATORY"): each
    use of the batched rule is "one application + one vm_compute equation —
    per-site proof terms O(1)".

    WHAT WAS TRUE ALL ALONG.  The COMPUTATION is O(1)-ish and fast: the whole
    instruction is 294 silent nodes in three stretches, and each stretch
    reduces in the VM in ~0.1–0.3 s at the real registers.

    WHAT WAS FALSE AS ORIGINALLY SPECIFIED, and is now fixed.  The equation
    the batched rule first took was [erun_silent n D rs m = (rs', m')], and
    closing it at a real instruction REQUIRES NAMING [m'] — a Sail
    continuation.  Naming it means READING THE VM'S VALUE BACK INTO A TERM,
    and the value is a CLOSURE: its readback normalises the entire rest of
    the instruction under a fresh variable, i.e. it re-does symbolically
    exactly the decode the concrete computation avoided.  MEASURED: the
    readback did NOT FINISH IN 110 s (killed), while the same computation
    projected to a number finished in 0.1 s; and the cold-boot register file
    computes in 0.09 s but reads back in over three minutes.  The
    durable-notes recipe ("compute once into a Definition, then
    [vm_cast_no_check]") does not transfer to a MONAD RESIDUAL, because it
    was written for VALUES.

    THE FIX, and what it cost.  [WeakEvLift] §3b restates the interface over
    TOTAL PROJECTIONS and UNEVALUATED COMPOSITIONS: [ewp_ev_batch] takes NO
    equation at all (its successor is [esil n D x]), the node facts are small
    projections, and the resume functions make the next stretch an
    application.  §§1–3's rules are unchanged in CONTENT — the same events,
    the same escrow, the same φ payments — and §5e above is the certification
    of the real instruction, closed.  The one residual restriction is the
    honest one: COMPUTE over the machine's own register file freely, NEVER
    name the result. *)

(** ** 6. CALIBRATION — the naive per-node proof (THE ANTI-PATTERN)

    The design forbids the per-node interface as the PROOF interface; this
    section puts a number under the prohibition.  Both lemmas advance the SAME
    eight consecutive silent nodes and have the same conclusion; the node
    facts are HYPOTHESES in both, so what is measured is the proof-side cost
    (rule applications, proofmode churn, [Qed] term size) with the reduction
    cost held at zero.  §5's numbers say a real instruction is 297 such nodes,
    so multiply by ~37.

    DO NOT IMITATE [calib_naive_8].  It is here to be measured. *)

Section calib.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma calib_naive_8 (c : CPU) (D : gset register)
      (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : regstate)
      (m0 m1 m2 m3 m4 m5 m6 m7 m8 : M unit) (ws : wstate) :
    esil_node D rs0 m0 = Some (rs1, m1) ->
    esil_node D rs1 m1 = Some (rs2, m2) ->
    esil_node D rs2 m2 = Some (rs3, m3) ->
    esil_node D rs3 m3 = Some (rs4, m4) ->
    esil_node D rs4 m4 = Some (rs5, m5) ->
    esil_node D rs5 m5 = Some (rs6, m6) ->
    esil_node D rs6 m6 = Some (rs7, m7) ->
    esil_node D rs7 m7 = Some (rs8, m8) ->
    hart_ws c ws -∗ ereg_frame c rs0 D -∗
    ▷ (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
         ereg_frame c rs8 D -∗ EWP (ECycle 0%nat c m8 None) @ ⊤) -∗
    EWP (ECycle 0%nat c m0 None) @ ⊤.
  Proof.
    iIntros (H1 H2 H3 H4 H5 H6 H7 H8) "Hws Hrf H".
    iApply (ewp_ev_sil_node 0%nat c D rs0 m0 m1 rs1 _ eq_refl H1
              with "Hws Hrf").
    iNext. iIntros (w1) "%Hd1 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs1 m1 m2 rs2 _ eq_refl H2
              with "Hws Hrf").
    iNext. iIntros (w2) "%Hd2 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs2 m2 m3 rs3 _ eq_refl H3
              with "Hws Hrf").
    iNext. iIntros (w3) "%Hd3 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs3 m3 m4 rs4 _ eq_refl H4
              with "Hws Hrf").
    iNext. iIntros (w4) "%Hd4 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs4 m4 m5 rs5 _ eq_refl H5
              with "Hws Hrf").
    iNext. iIntros (w5) "%Hd5 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs5 m5 m6 rs6 _ eq_refl H6
              with "Hws Hrf").
    iNext. iIntros (w6) "%Hd6 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs6 m6 m7 rs7 _ eq_refl H7
              with "Hws Hrf").
    iNext. iIntros (w7) "%Hd7 Hws Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs7 m7 m8 rs8 _ eq_refl H8
              with "Hws Hrf").
    iNext. iIntros (w8) "%Hd8 Hws Hrf".
    iApply ("H" $! w8 with "[%] Hws Hrf").
    repeat (etrans; [|by eassumption]). reflexivity.
  Qed.

  Lemma calib_batched_8 (c : CPU) (D : gset register) (x : ecur) (ws : wstate) :
    hart_ws c ws -∗ ereg_frame c x.1 D -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_frame c (esil 8 D x).1 D -∗
       EWP (ECycle 0%nat c (esil 8 D x).2 None) @ ⊤) -∗
    EWP (ECycle 0%nat c x.2 None) @ ⊤.
  Proof.
    iIntros "Hws Hrf H".
    by iApply (ewp_ev_batch 0%nat c D 8 x ws eq_refl with "Hws Hrf").
  Qed.

End calib.

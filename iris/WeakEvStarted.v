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

Lemma read_ok_wbyte_ok (σ : wgstate) (c : CPU) (ak : akinfo) (base : Z)
    (tvs : list (nat * bv 8)) (j t : nat) (v : bv 8) :
  ak_coh ak = false -> ak_latest ak = false ->
  read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) (ak_sync ak) false base tvs ->
  tvs !! j = Some (t, v) ->
  wbyte_ok (whart_view σ c) ak (base + Z.of_nat j) t v.
Proof.
  intros Hcoh Hlat Hrd Hj. destruct (Hrd j t v Hj) as (Hb & Hrdbl & _).
  rewrite /wbyte_ok Hcoh /=. split; [exact Hb|]. split; [exact Hrdbl|].
  by rewrite Hlat.
Qed.

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

  (** THE CALLER'S FETCH OBLIGATION.  The event-granular twin of the
      [⌜∀ j < 4, pinned_read σ (acc_addr pc j)⌝] conjunct every
      instruction-atomic leaf callback returns, plus the φ payment for the
      floors the fetch moves.  It is stated at the FETCH EVENT's own σ. *)
  Definition ev_fetch_cb (c : CPU) (n : N) (req : Interface.ReadReq.t n)
      (wf : bv (8 * n)) (ws : wstate) : iProp Σ :=
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
         ⌜exists (w : bv (8 * n)) tvs, eread_adm σ ws n req w tvs⌝ ∗
         ▷ (∀ (w : bv (8 * n)) (tvs : list (nat * bv 8)),
              ⌜eread_adm σ ws n req w tvs⌝ ={∅,⊤}=∗
                (* the text is PINNED: every admissible read returns the
                   certified word *)
                ⌜w = wf⌝ ∗
                ⌜forall a : Z,
                   (coh ws a < coh (eread_ws σ ws n req tvs) a)%nat ->
                   nv_ok (wglog σ) c a⌝ ∗
                wlat_interp (wgimg σ) (wglog σ)))%I.

(* ====================================================================== *)
(** ** 1. THE PUBLISHER — [sw a4,0(a5)] with a4 = 1, a5 = &started

    [WeakAcquire.wwp_started_set] at event granularity.  Read the premises in
    two groups: the CERTIFICATION (three computed stretches — boundary to
    fetch, fetch to store, store to [Ret] — and the shape facts of the two
    nodes, all of them [vm_compute] outputs, see §5), and the RESOURCES (the
    escrow, the hart's view with the release fence's [w_relp] already set, the
    register frame, the payload).

    The store event's obligations are discharged HERE, from the escrow, by
    [WeakStarted.wstarted_set] — verbatim, at [whart_view]. *)

  Lemma ewp_ev_started_set (a : Arch.pa) P (c : CPU) (D : gset register)
      (m : M unit) (ws : wstate) (rs rs1 rs2 rs3 : regstate)
      (n1 n2 n3 : nat)
      (nf : N) (reqf : Interface.ReadReq.t nf)
      (Kf : (bv (8 * nf) * option bool + Arch.abort)%type -> M unit)
      (wf : bv (8 * nf))
      (reqw : Interface.WriteReq.t 4)
      (Kw : (option bool + Arch.abort)%type -> M unit) :
    (* --- the certification --- *)
    erun_silent n1 D rs m = (rs1, Interface.Next (Interface.MemRead nf reqf) Kf) ->
    erun_silent n2 D rs1 (Kf (inl (wf, None)))
      = (rs2, Interface.Next (Interface.MemWrite 4 reqw) Kw) ->
    erun_silent n3 D rs2 (Kw (inl None)) = (rs3, Interface.Ret tt) ->
    (* --- the fetch node: a plain RAM read --- *)
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
    hart_ws c ws -∗ ereg_frame c rs D -∗ vwp_hold P ws -∗
    ev_fetch_cb c nf reqf wf ws -∗
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗
         hart_ws c ws' -∗ ereg_frame c rs3 D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hr1 Hr2 Hr3 Hdevf Hcohf Hlatf Hdevw Hpaw Hvalw Hacc Hrelp)
      "#Hinv Hws Hrf HP Hfetch Hcont".
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_load 0%nat c D n1 rs rs1 m nf reqf Kf ws
              eq_refl Hr1 Hdevf Hcohf Hlatf with "Hws Hrf").
    iIntros (σ) "%Hwseq %Hwf %Hbnd #Hlb Hlat".
    iMod ("Hfetch" $! σ with "[//] [//] [//] Hlb Hlat") as "[%Hen Hfk]".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hen as (w & tvs & Hadm). by exists w, tvs. }
    iNext. iIntros (w tvs) "%H1 %H2 %H3".
    iMod ("Hfk" $! w tvs with "[%]") as "(%Hpin & %Hpay & Hlat)";
      [by split_and!|].
    iModIntro. iFrame "Hlat". iSplitR; [iPureIntro; exact Hpay|].
    iIntros "Hws Hrf". subst w.
    (* ---------------- the STORE event ---------------- *)
    set (wsf := eread_ws σ ws nf reqf tvs).
    have Hle_f : ws_le ws wsf by apply load_post_run_le.
    have Hrelpf : w_relp wsf = true
      by rewrite /wsf /eread_ws load_post_run_relp.
    iDestruct (vwp_hold_mono P ws wsf Hle_f with "HP") as "HP".
    iApply (ewp_ev_seq_store 0%nat c D n2 rs1 rs2 _ 4 reqw Kw wsf
              eq_refl Hr2 Hdevw ltac:(done) ltac:(by rewrite Hpaw)
              with "Hws Hrf").
    iIntros (σ2) "%Hws2 %Hwf2 %Hbnd2 #Hlb2 Hlat2".
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
    set (kcl := wm_class_of (classify (Interface.WriteReq.access_kind reqw)) wsf).
    set (msg := wwrite_msg (Some (fin_to_nat c)) kcl
                  (Interface.WriteReq.pa reqw) 4 (Interface.WriteReq.value reqw)).
    set (wsw := store_post_run wsf
                  (ak_sync (classify (Interface.WriteReq.access_kind reqw)))
                  (pa_z (Interface.WriteReq.pa reqw)) (N.to_nat 4)
                  (S (length (wglog σ2)))).
    set (σm' := WMState (wgregs σ2 c) (wgimg σ2) (wglog σ2 ++ [msg]) wsw
                  (wgdev σ2)).
    have HQ : wQ_store (Some (fin_to_nat c)) a lock_one (whart_view σ2 c) σm'.
    { rewrite /wQ_store /wQ_store_w. split_and!.
      - reflexivity.
      - exists kcl. split.
        + rewrite /σm' /msg /= Hpaw Hvalw. reflexivity.
        + intros _. rewrite /kcl. by apply wm_class_of_relp.
      - rewrite /σm' /wsw /=. rewrite Hws2. apply store_post_run_le.
      - rewrite /wV_store_w /σm' /wsw /=. intros j Hj.
        rewrite /whart_view /=. rewrite -Hpaw /acc_addr.
        by apply flr_store_post_run. }
    have Hrelp2 : w_relp (wm_ws (whart_view σ2 c)) = true.
    { rewrite /whart_view. cbn [wm_ws]. rewrite Hws2. exact Hrelpf. }
    have Hbnd2' : ws_bounded (wm_ws (whart_view σ2 c))
                    (length (wm_log (whart_view σ2 c))).
    { rewrite /whart_view. cbn [wm_ws wm_log]. rewrite Hws2. exact Hbnd2. }
    iMod (wstarted_set a P (Some (fin_to_nat c)) (whart_view σ2 c) σm'
            HQ Hrelp2 Hbnd2' with "[Hlb2] [Hlat2] Hbody [HP]")
      as "[Hlat2 Hat]".
    { rewrite /whart_view. cbn [wm_log]. iExact "Hlb2". }
    { rewrite /whart_view. cbn [wm_img wm_log]. iExact "Hlat2". }
    { rewrite /whart_view. cbn [wm_ws]. rewrite Hws2. iExact "HP". }
    iMod ("Hclose" with "[Hat]") as "_".
    { iNext. iExists (S (length (wglog σ2))), lock_one. iExact "Hat". }
    iModIntro. iSplitR.
    { iPureIntro. intros j Hj. rewrite Hpaw. by apply Hnvok. }
    rewrite /σm' /=. iFrame "Hlat2".
    iIntros "Hws Hrf".
    (* ---------------- the TAIL: back to the boundary ---------------- *)
    iApply (ewp_ev_seq_ret 0%nat c D n3 rs2 rs3 _ tt eq_refl Hr3 with "Hrf").
    iNext. iIntros "Hrf". iApply ("Hcont" $! wsw with "[%] Hws Hrf").
    rewrite /wsw. etrans; [exact Hle_f|apply store_post_run_le].
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

  Lemma ewp_ev_started_load (a : Arch.pa) P `{!Persistent P} (c : CPU)
      (D : gset register) (m : M unit) (ws : wstate)
      (rs rs1 rs2 : regstate) (rs3 : bv (8 * 4) -> regstate)
      (n1 n2 n3 : nat)
      (nf : N) (reqf : Interface.ReadReq.t nf)
      (Kf : (bv (8 * nf) * option bool + Arch.abort)%type -> M unit)
      (wf : bv (8 * nf))
      (reql : Interface.ReadReq.t 4)
      (Kl : (bv (8 * 4) * option bool + Arch.abort)%type -> M unit) :
    (* --- the certification: the tail is PARAMETRIC in the word read --- *)
    erun_silent n1 D rs m = (rs1, Interface.Next (Interface.MemRead nf reqf) Kf) ->
    erun_silent n2 D rs1 (Kf (inl (wf, None)))
      = (rs2, Interface.Next (Interface.MemRead 4 reql) Kl) ->
    (forall w : bv (8 * 4),
       erun_silent n3 D rs2 (Kl (inl (w, None))) = (rs3 w, Interface.Ret tt)) ->
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
    hart_ws c ws -∗ ereg_frame c rs D -∗
    ev_fetch_cb c nf reqf wf ws -∗
    (∀ ws0 : wstate, ⌜ws_le ws ws0⌝ -∗ ev_flag_cb c a ws0 reql) -∗
    ▷ (∀ (ws' : wstate) (w : bv (8 * 4)), ⌜ws_le ws ws'⌝ -∗
         (⌜w = lock_zero⌝ ∨ ⌜w <> lock_zero⌝ ∗ ev_rcpt P ws') -∗
         hart_ws c ws' -∗ ereg_frame c (rs3 w) D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hr1 Hr2 Hr3 Hdevf Hcohf Hlatf Hdevl Hcohl Hlatl Hpal)
      "#Hinv Hws Hrf Hfetch Hflag Hcont".
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_load 0%nat c D n1 rs rs1 m nf reqf Kf ws
              eq_refl Hr1 Hdevf Hcohf Hlatf with "Hws Hrf").
    iIntros (σ) "%Hwseq %Hwf %Hbnd #Hlb Hlat".
    iMod ("Hfetch" $! σ with "[//] [//] [//] Hlb Hlat") as "[%Hen Hfk]".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hen as (w & tvs & Hadm). by exists w, tvs. }
    iNext. iIntros (w tvs) "%H1 %H2 %H3".
    iMod ("Hfk" $! w tvs with "[%]") as "(%Hpin & %Hpay & Hlat)";
      [by split_and!|].
    iModIntro. iFrame "Hlat". iSplitR; [iPureIntro; exact Hpay|].
    iIntros "Hws Hrf". subst w.
    set (wsf := eread_ws σ ws nf reqf tvs).
    have Hle_f : ws_le ws wsf by apply load_post_run_le.
    iDestruct ("Hflag" $! wsf with "[//]") as "Hflag".
    (* ---------------- the FLAG event, escrow open ---------------- *)
    iApply (ewp_ev_seq_load 0%nat c D n2 rs1 rs2 _ 4 reql Kl wsf
              eq_refl Hr2 Hdevl Hcohl Hlatl with "Hws Hrf").
    iIntros (σ2) "%Hws2 %Hwf2 %Hbnd2 #Hlb2 Hlat2".
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
    iApply (ewp_ev_seq_ret 0%nat c D n3 rs2 (rs3 w) _ tt eq_refl (Hr3 w)
              with "Hrf").
    iNext. iIntros "Hrf". iApply ("Hcont" $! wsl w with "[%] Harm Hws Hrf").
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
      (m : M unit) (ws : wstate) (rs rs1 rs2 rs3 : regstate) (n1 n2 n3 : nat)
      (nf : N) (reqf : Interface.ReadReq.t nf)
      (Kf : (bv (8 * nf) * option bool + Arch.abort)%type -> M unit)
      (wf : bv (8 * nf))
      (b : barrier_kind) (Kb : unit -> M unit) :
    (* --- the certification --- *)
    erun_silent n1 D rs m = (rs1, Interface.Next (Interface.MemRead nf reqf) Kf) ->
    erun_silent n2 D rs1 (Kf (inl (wf, None)))
      = (rs2, Interface.Next (Interface.Barrier b) Kb) ->
    ebar_park b = None ->
    erun_silent n3 D rs2 (Kb tt) = (rs3, Interface.Ret tt) ->
    (* --- the barrier is a PRED-R fence (the kernel's is [fence r,rw]) --- *)
    acq_pred_r b ->
    (* --- the fetch node --- *)
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind reqf)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind reqf)) = false ->
    hart_ws c ws -∗ ereg_frame c rs D -∗ ev_rcpt P ws -∗
    ev_fetch_cb c nf reqf wf ws -∗
    ▷ (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗ vwp_hold P ws' -∗
         hart_ws c ws' -∗ ereg_frame c rs3 D -∗ EWP (ELoop 0%nat c) @ ⊤) -∗
    EWP (ECycle 0%nat c m None) @ ⊤.
  Proof.
    iIntros (Hr1 Hr2 Hpark Hr3 Hacq Hdevf Hcohf Hlatf)
      "Hws Hrf Hrcpt Hfetch Hcont".
    (* ---------------- the FETCH event ---------------- *)
    iApply (ewp_ev_seq_load 0%nat c D n1 rs rs1 m nf reqf Kf ws
              eq_refl Hr1 Hdevf Hcohf Hlatf with "Hws Hrf").
    iIntros (σ) "%Hwseq %Hwf %Hbnd #Hlb Hlat".
    iMod ("Hfetch" $! σ with "[//] [//] [//] Hlb Hlat") as "[%Hen Hfk]".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hen as (w & tvs & Hadm). by exists w, tvs. }
    iNext. iIntros (w tvs) "%H1 %H2 %H3".
    iMod ("Hfk" $! w tvs with "[%]") as "(%Hpin & %Hpay & Hlat)";
      [by split_and!|].
    iModIntro. iFrame "Hlat". iSplitR; [iPureIntro; exact Hpay|].
    iIntros "Hws Hrf". subst w.
    set (wsf := eread_ws σ ws nf reqf tvs).
    have Hle_f : ws_le ws wsf by apply load_post_run_le.
    iDestruct (ev_rcpt_mono P ws wsf Hle_f with "Hrcpt") as "Hrcpt".
    (* ---------------- the BARRIER event ---------------- *)
    iApply (ewp_ev_seq_barrier 0%nat c D n2 rs1 rs2 _ b Kb wsf
              eq_refl Hr2 with "Hws Hrf").
    iNext. iIntros "Hws Hrf".
    (* the barrier's post-view IS [barrier_post], since nothing is parked *)
    have Hbp : efence_apply wsf (ebar_now b) = barrier_post wsf b.
    { rewrite -(efence_barrier_post wsf b) Hpark. reflexivity. }
    set (wsb := efence_apply wsf (ebar_now b)).
    have Hle_b : ws_le wsf wsb by apply efence_apply_le.
    (* THE DELIVERY — [WeakStarted.wstarted_deliver_gen], verbatim *)
    iAssert (vwp_hold P wsb) with "[Hrcpt]" as "HP".
    { iDestruct "Hrcpt" as (T) "[%HT HP0]".
      iApply (wstarted_deliver_gen P (WMState rs ∅ [] wsf dev0_state) wsb T b
                Hacq HT with "HP0").
      rewrite /wV_fence. cbn [wm_ws]. rewrite /wsb Hbp. reflexivity. }
    rewrite Hpark.
    (* ---------------- the TAIL ---------------- *)
    iApply (ewp_ev_seq_ret 0%nat c D n3 rs2 rs3 _ tt eq_refl Hr3 with "Hrf").
    iNext. iIntros "Hrf". iApply ("Hcont" $! wsb with "[%] HP Hws Hrf").
    etrans; [exact Hle_f|exact Hle_b].
  Qed.

End started_ev.

(* ====================================================================== *)
(* ====================================================================== *)
(** ** 4. THE TWO-INSTRUCTION COMPOSITION — NOT DELIVERED, and why

    [WkStartedLoad.wwp_started_wait_seq] (an [Example], not a theorem of
    record) chains the waiter's load and fence.  Its event-granular twin is
    blocked on nothing conceptual — §2 hands the receipt out and §3 takes it
    in, and [ev_rcpt_mono] carries it across the gap — but on FORM: chaining at
    the boundary means [ewp_eloop], which quantifies over the tick, so the
    fence instruction's certification has to be supplied for BOTH values of
    [tick] as a family (a dependent record over [reqf]'s width).  That is
    exactly the shape F8's form change removes, since under it the
    certification is a composition of applications rather than a bundle of
    named terms.  Deferred to the interface change, with the note that the
    composition costs no weak-memory content: §2's exit edge and §3's entry
    edge already meet. *)

(* ====================================================================== *)
(** ** 5. THE CONCRETE INSTANTIATION — [main+0xb0], [c.sw a4,0(a5)] = 0xc398
           (S4 gap 4: where the O(1)-per-site claim is tested)

    xv6's [started = 1] IS a compressed store ([kernel.asm], [main+0xb0]), and
    this section runs the publisher's certification at it, on the REAL
    post-boot register file ([ColdBoot.cold_regs], the tree's own
    computed-once cold-boot state) with [a5 = &started] and [a4 = 1].

    THE RECIPE, and it is the durable-notes one verbatim: compute each stretch
    ONCE into its own [Definition] ([erun_silent]'s residual monad is a Sail
    continuation — naming it is what keeps every later mention a shallow
    conversion), then tie it to the model with ONE [vm_cast_no_check].  A
    plain [vm_compute; reflexivity] would leave the kernel's LAZY evaluator to
    redo the whole stretch at [Qed].

    WHAT THE MEASUREMENT SHOWS (numbers in the worklist's S5 table): the
    instruction is 107 silent nodes to the fetch, 178 from the fetch to the
    store, and a short tail — 285+ nodes in all — and each stretch is ONE
    application plus one VM-checked equation.  The footprint [ev_D] is
    computed, not guessed: [ev_regs] is a measurement-side collector (it is
    NOT part of the proof interface) that lists the registers a stretch
    touches. *)

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

(** The read answer a certification supplies at a read event. *)
Definition eresume_z (v : Z) (m : M unit) : option (M unit) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> option (M unit) with
       | Interface.MemRead n req => fun k =>
           Some (k (inl (Z_to_bv (8 * n) v, None)))
       | _ => fun _ => None
       end) k
  | _ => None
  end.

(** *** 5b. Node-kind projections with SMALL outputs

    Every fact this section states about the real instruction is a projection
    whose value is a number, a boolean or a 64-bit word — never the residual
    monad.  THAT RESTRICTION IS THE SECTION'S MAIN FINDING; see 5e. *)

Definition enode_tag (m : M unit) : nat :=
  match m with
  | Interface.Ret _ => 0
  | Interface.Next oc _ =>
      match oc with
      | Interface.MemRead _ _ => 1
      | Interface.MemWrite _ _ => 2
      | Interface.Barrier _ => 3
      | Interface.Choose _ => 4
      | _ => 5
      end
  end.

Definition eread_facts (m : M unit) : option (N * Z * bool * bool * bool) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> _ with
       | Interface.MemRead n req => fun _ =>
           let a := classify (Interface.ReadReq.access_kind req) in
           Some (n, pa_z (Interface.ReadReq.pa req),
                 ak_coh a, ak_latest a, ak_sync a)
       | _ => fun _ => None
       end) k
  | _ => None
  end.

Definition ewrite_facts (m : M unit) : option (N * Z * Z * bool * bool) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> _ with
       | Interface.MemWrite n req => fun _ =>
           let a := classify (Interface.WriteReq.access_kind req) in
           Some (n, pa_z (Interface.WriteReq.pa req),
                 bv_unsigned (Interface.WriteReq.value req),
                 ak_latest a, ak_sync a)
       | _ => fun _ => None
       end) k
  | _ => None
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

(** *** 5c. The concrete state: the post-boot file, at [main+0xb0] *)

Definition ev_pc : SailStdpp.Values.mword 64 :=
  SailStdpp.Values.mword_of_int (KernelSyms.main + 0xb0).
Definition ev_flag : Arch.pa := SailStdpp.Values.mword_of_int KernelSyms.started.
Definition ev_word : Z := 0xc398.

(** THE BASE REGISTER FILE: the tree's own COLD-BOOT file
    ([ColdBoot.cold_regs], the computed output of the model's ~300-write boot
    chain — PMA regions, PMPs, mstatus, misa all as the machine sets them),
    with the two GPRs the instruction reads set to [&started] and 1 and the PC
    at [main+0xb0].

    IT HAS TO BE THAT FILE, and the alternative is a measured trap: over
    [WpDecodeBridge.dregs] (the small decode-reference file, config CSRs zero)
    the same [riscv_step] takes 141 silent nodes and ends at [Ret] WITHOUT a
    fetch — the run traps, because a file with no PMA regions cannot fetch.  A
    "concrete register state" that is not the machine's own is not a
    certification of anything. *)
Definition ev_rs0 : regstate :=
  register_set (R_bitvector_64 nextPC) ev_pc
    (register_set (R_bitvector_64 PC) ev_pc
      (register_set (R_bitvector_64 x15) ev_flag
        (register_set (R_bitvector_64 x14)
           (SailStdpp.Values.mword_of_int 1)
           (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))))).

(** *** 5d. THE MEASUREMENT, as compiled evidence.

    Three stretches, three residuals, all computed by the VM and checked by
    the kernel's VM at [Qed] ([vm_cast_no_check]).  Nothing below names a
    residual monad. *)

(* stretch 1: the boundary to the FETCH event.  [erun_any] is the collector's
   footprint-free stepper; [erun_count] below re-runs the same stretch AT THE
   DECLARED FOOTPRINT, which is what a proof would use. *)
Definition ev_s1 : regstate * M unit := erun_any 400 ev_rs0 (riscv_step false).
Definition ev_m1 : M unit :=
  match eresume_z ev_word ev_s1.2 with
  | Some m => m
  | None => Interface.Ret tt
  end.
Definition ev_s2 : regstate * M unit := erun_any 600 ev_s1.1 ev_m1.
Definition ev_m2 : M unit :=
  match ev_s2.2 with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> M unit with
       | Interface.MemWrite _ _ => fun k => k (inl None)
       | _ => fun _ => Interface.Ret tt
       end) k
  | _ => Interface.Ret tt
  end.
Definition ev_s3 : regstate * M unit := erun_any 400 ev_s2.1 ev_m2.

(** THE FOOTPRINT, collected rather than guessed — a list of register names,
    hence a SMALL readback. *)
Definition ev_Dl : list register :=
  ltac:(let x := eval vm_compute in
          (app (erun_regs 400 ev_rs0 (riscv_step false))
             (app (erun_regs 600 ev_s1.1 ev_m1)
                  (erun_regs 400 ev_s2.1 ev_m2))) in
        exact x).
Definition ev_D : gset register := list_to_set ev_Dl.

(** (i) THE INSTRUCTION'S EVENT STRUCTURE.  107 silent nodes to the fetch,
    178 more to the store, 8 more to [Ret]: 293 silent nodes, three stretches,
    two memory events, one instruction. *)
Lemma ev_len1 : erun_count 400 ev_D ev_rs0 (riscv_step false) = 107%nat.
Proof. vm_cast_no_check (eq_refl 107%nat). Qed.
Lemma ev_len2 : erun_count 600 ev_D ev_s1.1 ev_m1 = 178%nat.
Proof. vm_cast_no_check (eq_refl 178%nat). Qed.
Lemma ev_len3 : erun_count 400 ev_D ev_s2.1 ev_m2 = 8%nat.
Proof. vm_cast_no_check (eq_refl 8%nat). Qed.

(** (ii) THE FETCH IS AN ORDINARY PLAIN RAM READ — width 2 (the instruction
    is compressed) at [main+0xb0], and its access kind classifies with
    [ak_coh = false].  So it takes [WeakEvLift.ewp_ev_load], the SAME rule a
    racy data load takes, and the design's "instruction fetch is declared
    coherent" (Decision 6) is NOT what this model emits. *)
Lemma ev_fetch_node :
  eread_facts ev_s1.2 = Some (2%N, 2147487534, false, false, false).
Proof.
  vm_cast_no_check (eq_refl (Some (2%N, 2147487534, false, false, false))).
Qed.

(** (iii) THE STORE IS THE FLAG WORD: width 4 at [&started], value 1, plain
    (the release is carried by the hart's [w_relp], set by the [fence rw,w]
    at [main+0xac] — exactly as [WeakStarted]'s writer half says). *)
Lemma ev_store_node :
  ewrite_facts ev_s2.2 = Some (4%N, 2147525168, 1, false, false).
Proof. vm_cast_no_check (eq_refl (Some (4%N, 2147525168, 1, false, false))). Qed.

(** (iv) THE TAIL ENDS AT [Ret]: the instruction has exactly two memory
    events. *)
Lemma ev_tail_ret : enode_tag ev_s3.2 = 0%nat.
Proof. vm_cast_no_check (eq_refl 0%nat). Qed.

(** *** 5e. WHAT THE MEASUREMENT REFUTES, and the form change it prescribes

    THE CLAIM UNDER TEST (design, "reflective batching is MANDATORY"): each
    use of the batched rule is "one application + one vm_compute equation —
    per-site proof terms O(1)".

    WHAT IS TRUE.  The COMPUTATION is O(1)-ish and fast: the whole
    instruction is 297 silent nodes in three stretches, and each stretch
    reduces in the VM in ~0.1–0.3 s at the real registers (the lemmas above
    are exactly those runs, VM-checked at [Qed] too).

    WHAT IS FALSE AS SPECIFIED.  The equation the batched rule
    ([WeakEvLift.ewp_ev_batch]) takes is
    [erun_silent n D rs m = (rs', m')], and CLOSING IT AT A REAL INSTRUCTION
    REQUIRES NAMING [m'] — the residual Sail continuation.  Naming it means
    READING THE VM'S VALUE BACK INTO A TERM, and the value is a CLOSURE: its
    readback normalises the entire rest of the instruction under a fresh
    variable, i.e. it re-does symbolically exactly the decode the concrete
    computation avoided ([WpDecodeBridge]'s header: symbolic decode is 4–11 s
    per instruction — and readback is worse, because it is eager and total).
    MEASURED: [let x := eval vm_compute in (erun_silent … ).2 in exact x] at
    this instruction DID NOT FINISH IN 110 s (killed); the same computation
    projected to a NUMBER finishes in 0.1 s.  The durable-notes recipe
    ("compute once into a Definition, then [vm_cast_no_check]") therefore does
    NOT transfer to this interface: it was written for values (a [regstate], an
    [mstate]), and a monad residual is not one.

    A SECOND MEASUREMENT ISOLATES THE CULPRIT AS THE READBACK, NOT THE
    REGISTER FILE: over the cold-boot file the stretch COMPUTES in ~0.09 s
    (the lemmas above are those runs) while READING BACK the same run's pair
    did not finish in 3 minutes.  Compute over the machine's own file freely;
    never name the result.

    THE PRESCRIBED FORM CHANGE (not attempted here; it is the post-spike
    interface work, and it is small).  The rules must consume the residual
    through TOTAL PROJECTIONS instead of by syntactic matching, so that no
    call site ever writes one down:

      - the stretch is named by its own unevaluated application
        ([(erun_silent n D rs m).1] / [.2]), so the "equation" is
        [surjective_pairing] and costs nothing;
      - the node's shape and payload are SMALL projections
        ([enode_tag], [eread_facts], [ewrite_facts] above are already in this
        form) discharged by one [vm_cast_no_check] each;
      - the successor expression is a total resume function applied to the
        residual ([eresume_z]'s shape), so the next stretch is
        [erun_silent n2 D (erun_silent n1 …).1 (eresume … (erun_silent n1 …).2)]
        — a composition of applications, never a literal.

    Under that form every per-site obligation has a small output and the O(1)
    claim holds; §§1–4's rules are unaffected in CONTENT (the same events, the
    same escrow, the same φ payments) — only the way the certification is
    handed to them changes.  That is why the S5 lemmas above are stated
    against [erun_silent … = (rs', <node>)]: it is the readable form, and it
    is the form the projection version derives in one rewrite. *)


(* ====================================================================== *)
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
      (m0 m1 m2 m3 m4 m5 m6 m7 m8 : M unit) :
    esil_node D rs0 m0 = Some (rs1, m1) ->
    esil_node D rs1 m1 = Some (rs2, m2) ->
    esil_node D rs2 m2 = Some (rs3, m3) ->
    esil_node D rs3 m3 = Some (rs4, m4) ->
    esil_node D rs4 m4 = Some (rs5, m5) ->
    esil_node D rs5 m5 = Some (rs6, m6) ->
    esil_node D rs6 m6 = Some (rs7, m7) ->
    esil_node D rs7 m7 = Some (rs8, m8) ->
    ereg_frame c rs0 D -∗
    ▷ (ereg_frame c rs8 D -∗ EWP (ECycle 0%nat c m8 None) @ ⊤) -∗
    EWP (ECycle 0%nat c m0 None) @ ⊤.
  Proof.
    iIntros (H1 H2 H3 H4 H5 H6 H7 H8) "Hrf H".
    iApply (ewp_ev_sil_node 0%nat c D rs0 m0 m1 rs1 eq_refl H1 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs1 m1 m2 rs2 eq_refl H2 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs2 m2 m3 rs3 eq_refl H3 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs3 m3 m4 rs4 eq_refl H4 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs4 m4 m5 rs5 eq_refl H5 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs5 m5 m6 rs6 eq_refl H6 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs6 m6 m7 rs7 eq_refl H7 with "Hrf").
    iNext. iIntros "Hrf".
    iApply (ewp_ev_sil_node 0%nat c D rs7 m7 m8 rs8 eq_refl H8 with "Hrf").
    iNext. iIntros "Hrf". by iApply "H".
  Qed.

  Lemma calib_batched_8 (c : CPU) (D : gset register) (rs0 rs8 : regstate)
      (m0 m8 : M unit) :
    erun_silent 8 D rs0 m0 = (rs8, m8) ->
    ereg_frame c rs0 D -∗
    (ereg_frame c rs8 D -∗ EWP (ECycle 0%nat c m8 None) @ ⊤) -∗
    EWP (ECycle 0%nat c m0 None) @ ⊤.
  Proof.
    iIntros (Hrun) "Hrf H".
    by iApply (ewp_ev_batch 0%nat c D 8 m0 m8 rs0 rs8 eq_refl Hrun with "Hrf").
  Qed.

End calib.

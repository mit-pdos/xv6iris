(* ===================================================================== *)
(*  UShLineAtHold.v -- THE FOUR SEAM LEMMAS OF [UShLine.v] AT THE LINK   *)
(*  RECORD, AND WITH A LINEAR FRAME (lane INIT-FILE).                    *)
(*                                                                       *)
(*  [UShLine.v] states most of its seam at [LinkRec.LinkRec] already --  *)
(*  [UShLine.ush_mid_at], [ush_mid_wc_read_t_at], [ush_wb_read_holds_at],*)
(*  [ush_read_recv_leaf_holds_at] -- but four of its laws were left at   *)
(*  the ECHO era's CONCRETE residue ([UShLine.rd_res]) and so have no    *)
(*  form the FILE application can use.  This file supplies the missing   *)
(*  four in the landed shape: [lk_rres L] for the residue, [lk_T L] for  *)
(*  the taint, nothing else changed, and the proofs are the originals'.  *)
(*                                                                       *)
(*    [ush_mid_of_at]      -> [ush_mid_of_at_L]                          *)
(*    [ush_at_of_mid_taint]-> [ush_at_of_mid_taint_L]                    *)
(*    [ush_at_of_mid_wb]   -> [ush_at_of_mid_wb_L]                       *)
(*    [ush_posb_of_lend]   -> [ush_posb_of_lend_L]                       *)
(*                                                                       *)
(*  ...AND THE SECOND HALF OF THE SEAM, ruling H': sh's file-era         *)
(*  credential families are the echo-shaped credential WITH THE DEED     *)
(*  conjoined, a LINEAR conjunct, and the four laws above take [Wc] and  *)
(*  [Wb] as parameters only.  So each has a [_hold] corollary at the     *)
(*  framed family -- [fun I => Wb I * Hold I], and, where ruling H'      *)
(*  needs the era's boot state as a shared index, [fun I => exists s0,   *)
(*  Wb s0 I * Hold s0 I].  The two side conditions [UShLine.ush_wc_inp]  *)
(*  and [ush_wb_inp] survive the frame because they are READ-BACKS, and  *)
(*  that is what [UShLineHold.v] measures; this file only spends it.     *)
(*                                                                       *)
(*  A LEAF FILE, like [UShLineHold.v]: nothing above reads it yet.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import LineWords.
Require Import EchoOut.
Require Import FileState.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import CtxIdDefs.
Require Import FsCfg.
Require Import UserConsole.        (* [upos] / [upos_a] / [ucons_pay] *)
Require Import UkRun.              (* [uk_names] / [ukn_pay] *)
Require Import UkSh.               (* [ush_at] / [ush_lease] / [ush_posb] *)
Require UkInit.                    (* [init_rd]: the exit family *)
Require Import LinkRec.            (* [lk_T] / [lk_rres] *)
Require Import UShLine.
Require Import UShLineHold.        (* the read-back framing measurement *)
Local Open Scope Z_scope.

Section UShLineAtHold.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.

  Context (L : LinkRec Σ).

  (* =================================================================== *)
  (*  1  THE PAYLOAD COMES APART INTO THE PIECES, AT THE RECORD          *)
  (* =================================================================== *)
  Lemma ush_mid_of_at_L (γ : echo_gn)
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    ⊢ UkSh.ush_at N γp n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I.
  Proof using .
    intro Hpay. rewrite /UkSh.ush_at /UkSh.ush_lease.
    iIntros "[Hpos Hlease]". iEval (rewrite Hpay /ucons_pay) in "Hlease".
    iDestruct "Hlease" as "[Hl | #HT]"; last first.
    { iExists (replicate n wl_nl).
      iSplitR; [ iPureIntro; apply length_replicate | ].
      iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
      iExists n. iFrame "Hpos". rewrite Hpay.
      iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    rewrite /ush_rd_x_at /UkInit.init_rd /UkInit.init_rd_cred.
    iDestruct "Hcred" as "[Hcred _]".
    iDestruct "Hcred" as (v I) "([%Hlen %Hrest] & #Hpin & Hdl & #HE & #Hres & Hrp)".
    iExists I. iSplitR; [ by iPureIntro | ].
    iLeft. rewrite /ush_mid_at Hlen. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres Hrp".
  Qed.

  (* ...and the same with the DEED conjoined to the banner-owed family:
     [Wb] is a parameter here and nothing in the proof looks at it. *)
  Lemma ush_mid_of_at_L_hold (γ : echo_gn)
      (Wb Hold : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun I : list (bv 8) => Wb I ∗ Hold I)%I) ->
    ⊢ UkSh.ush_at N γp n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I.
  Proof using .
    exact (ush_mid_of_at_L γ (fun I : list (bv 8) => Wb I ∗ Hold I)%I
             N γp n).
  Qed.

  Lemma ush_mid_of_at_L_hold_ex (γ : echo_gn)
      (Wb Hold : FileState.fstate -> list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun I : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 I ∗ Hold s0 I)%I) ->
    ⊢ UkSh.ush_at N γp n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_lease N γp (lk_T L) (ush_mid_at (lk_rres L) γ γp) I.
  Proof using .
    exact (ush_mid_of_at_L γ
             (fun I : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 I ∗ Hold s0 I)%I N γp n).
  Qed.

  (* =================================================================== *)
  (*  2  THE PIECES GO BACK TOGETHER UNDER THE TAINT                     *)
  (* =================================================================== *)
  Lemma ush_at_of_mid_taint_L (γ : echo_gn)
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    ⊢ lk_T L -∗ ush_mid_at (lk_rres L) γ γp I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intro Hpay. rewrite /ush_mid_at /UkSh.ush_at.
    iIntros "#HT (Hpos & _ & _ & _)". iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_taint with "HT").
  Qed.

  Lemma ush_at_of_mid_taint_L_hold (γ : echo_gn)
      (Wb Hold : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) => Wb J ∗ Hold J)%I) ->
    ⊢ lk_T L -∗ ush_mid_at (lk_rres L) γ γp I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    exact (ush_at_of_mid_taint_L γ (fun J : list (bv 8) => Wb J ∗ Hold J)%I
             N γp I).
  Qed.

  Lemma ush_at_of_mid_taint_L_hold_ex (γ : echo_gn)
      (Wb Hold : FileState.fstate -> list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I) ->
    ⊢ lk_T L -∗ ush_mid_at (lk_rres L) γ γp I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    exact (ush_at_of_mid_taint_L γ
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I N γp I).
  Qed.

  (* =================================================================== *)
  (*  3  ...AND AT A BOUNDARY, WITH THE BANNER-OWED CREDENTIAL           *)
  (* =================================================================== *)
  Lemma ush_at_of_mid_wb_L (γ : echo_gn)
      (Wb : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    ush_wb_inp γ (lk_T L) Wb ->
    ⊢ ush_mid_at (lk_rres L) γ γp I -∗ Wb I -∗ UkSh.ush_at N γp (length I).
  Proof using .
    intros Hpay Hwbi. iIntros "Hmid Hb".
    iDestruct (Hwbi I with "Hb") as "[Hb Hrd]".
    iDestruct "Hrd" as "[[_ %Hrest] | #HT]"; last first.
    { iApply (ush_at_of_mid_taint_L γ Wb N γp I Hpay with "HT Hmid"). }
    iEval (rewrite /ush_mid_at) in "Hmid".
    iDestruct "Hmid" as "(Hpos & Hpa & Hrd0 & Hcred)".
    rewrite /UkSh.ush_at. iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_tok fsc_cons γp (lk_T L)
              (ush_rd_x_at (lk_rres L) γ Wb) (length I) (-1)
              with "Hrd0 Hpa [Hcred Hb]").
    rewrite /ush_rd_x_at /UkInit.init_rd /UkInit.init_rd_cred /ush_rd_pin_at.
    iSplitR "Hb"; last first.
    { iExists I. iSplitR; [ by iPureIntro | ]. iExact "Hb". }
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres & Hrp)".
    iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hdl HE Hres Hrp".
  Qed.

  (* ...AND THE FRAME.  [ush_wb_inp] is a read-back, so the deed rides
     through it untouched ([UShLineHold.ush_wb_inp_hold]); the law itself
     never looks inside [Wb]. *)
  Lemma ush_at_of_mid_wb_L_hold (γ : echo_gn)
      (Wb Hold : list (bv 8) -> iProp Σ) (N : uk_names Σ) (γp : gname)
      (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) => Wb J ∗ Hold J)%I) ->
    ush_wb_inp γ (lk_T L) Wb ->
    ⊢ ush_mid_at (lk_rres L) γ γp I -∗ (Wb I ∗ Hold I) -∗
      UkSh.ush_at N γp (length I).
  Proof using .
    intros Hpay Hwbi.
    exact (ush_at_of_mid_wb_L γ (fun J : list (bv 8) => Wb J ∗ Hold J)%I
             N γp I Hpay (ush_wb_inp_hold γ (lk_T L) Wb Hold Hwbi)).
  Qed.

  Lemma ush_at_of_mid_wb_L_hold_ex (γ : echo_gn)
      (Wb Hold : FileState.fstate -> list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (I : list (bv 8)) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I) ->
    (forall s0 : FileState.fstate, ush_wb_inp γ (lk_T L) (Wb s0)) ->
    ⊢ ush_mid_at (lk_rres L) γ γp I -∗
      (∃ s0 : FileState.fstate, Wb s0 I ∗ Hold s0 I) -∗
      UkSh.ush_at N γp (length I).
  Proof using .
    intros Hpay Hwbi.
    exact (ush_at_of_mid_wb_L γ
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I N γp I Hpay
             (ush_wb_inp_ex γ (lk_T L) Wb Hold Hwbi)).
  Qed.

  (* =================================================================== *)
  (*  4  THE ENTRY LAW: WHAT /init LENDS ITS CHILD, AT THE RECORD        *)
  (* =================================================================== *)
  Lemma ush_posb_of_lend_L (γ : echo_gn) (N : uk_names Σ) (γp : gname)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L) (ush_rd_x_at (lk_rres L) γ Wb) ->
    ush_wc_inp γ (lk_T L) Wc ->
    ush_wb_inp γ (lk_T L) Wb ->
    ⊢ upos γp n -∗
      ucons_pay fsc_cons γp (lk_T L) (ush_rd_pin_at (lk_rres L) γ) (-1) -∗
      ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
       ∨ lk_T L) -∗
      UkSh.ush_posb N γp (lk_T L) Wc Wb (ush_mid_at (lk_rres L) γ γp)
        l 0%nat.
  Proof using .
    intros Hpay Hwci Hwbi. rewrite /ucons_pay.
    iAssert (□ (lk_T L -∗ upos γp n -∗
               UkSh.ush_posb N γp (lk_T L) Wc Wb
                 (ush_mid_at (lk_rres L) γ γp) l 0%nat))%I
      as "#Htaint".
    { iModIntro. iIntros "#HT Hpos".
      iApply (UkSh.ush_posb_taint N γp (lk_T L) Wc Wb
                (ush_mid_at (lk_rres L) γ γp) l 0%nat with "HT [Hpos]").
      rewrite /UkSh.ush_pos /UkSh.ush_at. iExists n. iFrame "Hpos".
      rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
    iIntros "Hpos Hl [Hwc | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hwc" as (I) "[%Hlen Hwc]".
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    iDestruct "Hcred" as (v I0) "([%Hlen0 %Hrest] & #Hpin & Hdl & #HE & #Hres & Hrp)".
    iAssert (UkSh.ush_wcp Wc Wb l I 0%nat
             ∗ ((∃ v' : era_pins, era_pin γ (S gen_id) v' ∗ inp_lb v' I)
                ∨ lk_T L))%I
      with "[Hwc]" as "[Hwc Hrd]".
    { iEval (rewrite /UkSh.ush_wcp) in "Hwc".
      iDestruct "Hwc" as "[[%Hrow Hc] | [%Hrow Hb]]".
      - iDestruct (Hwci I 0%nat with "Hc") as "[Hc Hr]".
        iSplitR "Hr"; [ | iExact "Hr" ].
        rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
        iExact "Hc".
      - iDestruct (Hwbi I with "Hb") as "[Hb Hr]".
        iSplitR "Hr".
        + rewrite /UkSh.ush_wcp. iRight. iSplitR; [ by iPureIntro | ].
          iExact "Hb".
        + iDestruct "Hr" as "[[Hrv _] | #HT]";
            [ iLeft; iExact "Hrv" | iRight; iExact "HT" ]. }
    iDestruct "Hrd" as "[Hrd | #HT]"; last first.
    { iApply ("Htaint" with "HT Hpos"). }
    iDestruct "Hrd" as (v') "[#Hpin' #HE']".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iDestruct (inp_lb_agree v I0 I ltac:(lia) with "HE HE'") as %<-.
    iApply (UkSh.ush_posb_of_wc N γp (lk_T L) Wc Wb
              (ush_mid_at (lk_rres L) γ γp) l 0%nat I0 Hrest
              with "[Hpos Hpa Hrd0 Hdl Hrp] Hwc").
    rewrite /ush_mid_at Hlen0. iFrame "Hpos Hpa Hrd0".
    iExists v. iFrame "Hpin Hdl HE Hres Hrp".
  Qed.

  (* ...AND THE FRAME.  Both side conditions are read-backs, and [Wc] /
     [Wb] reach the law only through [UkSh.ush_wcp] and [UkSh.ush_posb],
     which are abstract in them. *)
  Lemma ush_posb_of_lend_L_hold (γ : echo_gn) (N : uk_names Σ) (γp : gname)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb Hold : list (bv 8) -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) => Wb J ∗ Hold J)%I) ->
    ush_wc_inp γ (lk_T L) Wc ->
    ush_wb_inp γ (lk_T L) Wb ->
    ⊢ upos γp n -∗
      ucons_pay fsc_cons γp (lk_T L) (ush_rd_pin_at (lk_rres L) γ) (-1) -∗
      ((∃ I : list (bv 8), ⌜length I = n⌝
          ∗ UkSh.ush_wcp (fun (J : list (bv 8)) (p : nat) => Wc J p ∗ Hold J)%I
              (fun J : list (bv 8) => Wb J ∗ Hold J)%I l I 0%nat)
       ∨ lk_T L) -∗
      UkSh.ush_posb N γp (lk_T L)
        (fun (J : list (bv 8)) (p : nat) => Wc J p ∗ Hold J)%I
        (fun J : list (bv 8) => Wb J ∗ Hold J)%I
        (ush_mid_at (lk_rres L) γ γp) l 0%nat.
  Proof using .
    intros Hpay Hwci Hwbi.
    exact (ush_posb_of_lend_L γ N γp
             (fun (J : list (bv 8)) (p : nat) => Wc J p ∗ Hold J)%I
             (fun J : list (bv 8) => Wb J ∗ Hold J)%I l n Hpay
             (ush_wc_inp_hold γ (lk_T L) Wc Hold Hwci)
             (ush_wb_inp_hold γ (lk_T L) Wb Hold Hwbi)).
  Qed.

  Lemma ush_posb_of_lend_L_hold_ex (γ : echo_gn) (N : uk_names Σ)
      (γp : gname)
      (Wc : FileState.fstate -> list (bv 8) -> nat -> iProp Σ)
      (Wb : FileState.fstate -> list (bv 8) -> iProp Σ)
      (Hold : FileState.fstate -> list (bv 8) -> iProp Σ)
      (l : list fdstate) (n : nat) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T L)
          (ush_rd_x_at (lk_rres L) γ
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I) ->
    (forall s0 : FileState.fstate, ush_wc_inp γ (lk_T L) (Wc s0)) ->
    (forall s0 : FileState.fstate, ush_wb_inp γ (lk_T L) (Wb s0)) ->
    ⊢ upos γp n -∗
      ucons_pay fsc_cons γp (lk_T L) (ush_rd_pin_at (lk_rres L) γ) (-1) -∗
      ((∃ I : list (bv 8), ⌜length I = n⌝
          ∗ UkSh.ush_wcp
              (fun (J : list (bv 8)) (p : nat) =>
                 ∃ s0 : FileState.fstate, Wc s0 J p ∗ Hold s0 J)%I
              (fun J : list (bv 8) =>
                 ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I l I 0%nat)
       ∨ lk_T L) -∗
      UkSh.ush_posb N γp (lk_T L)
        (fun (J : list (bv 8)) (p : nat) =>
           ∃ s0 : FileState.fstate, Wc s0 J p ∗ Hold s0 J)%I
        (fun J : list (bv 8) =>
           ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I
        (ush_mid_at (lk_rres L) γ γp) l 0%nat.
  Proof using .
    intros Hpay Hwci Hwbi.
    exact (ush_posb_of_lend_L γ N γp
             (fun (J : list (bv 8)) (p : nat) =>
                ∃ s0 : FileState.fstate, Wc s0 J p ∗ Hold s0 J)%I
             (fun J : list (bv 8) =>
                ∃ s0 : FileState.fstate, Wb s0 J ∗ Hold s0 J)%I l n Hpay
             (ush_wc_inp_ex γ (lk_T L) Wc Hold Hwci)
             (ush_wb_inp_ex γ (lk_T L) Wb Hold Hwbi)).
  Qed.

End UShLineAtHold.

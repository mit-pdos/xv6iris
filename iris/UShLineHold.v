(* ===================================================================== *)
(*  UShLineHold.v -- THE SEAM'S TWO INPUT READINGS, WITH A LINEAR FRAME   *)
(*  (lane INIT-FILE, the measurement ruling H' asked for first).          *)
(*                                                                       *)
(*  [UShLine.ush_wc_inp] and [ush_wb_inp] are the two side conditions     *)
(*  [UShLine.ush_posb_of_lend] and [ush_at_of_mid_wb] spend, and they     *)
(*  are the pair lane INIT-FILE's findings called load-bearing: sh's      *)
(*  file-era families are the echo-shaped credential with the DEED        *)
(*  conjoined, and nothing in the tree carried a linear conjunct through  *)
(*  a credential law.                                                     *)
(*                                                                       *)
(*  MEASURED, AND IT IS A FRAME AND NOT A DESIGN CHANGE.  Both readings   *)
(*  are READ-BACKS -- the credential goes in and the SAME credential      *)
(*  comes back beside a persistent fact -- so a conjunct that is not      *)
(*  looked at rides through untouched.  The four lemmas below are the     *)
(*  whole cost: two for the plain shape [Wc I p * Hold I], two for the    *)
(*  one ruling H' fixes ([exists s0, Wc s0 I p * Hold s0 I], the era's    *)
(*  boot state as a shared index).                                       *)
(*                                                                       *)
(*  A LEAF FILE, not the bottom of [UShLine.v]: the program stream is     *)
(*  live above that file, and these four add nothing it reads.           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import EchoOut.
Require Import FileState.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import CtxIdDefs.
Require Import UShLine.
Local Open Scope Z_scope.

Section UShLineHold.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.

  (* ---- the plain shape: one linear conjunct beside the credential ---- *)
  Lemma ush_wc_inp_hold (γ : echo_gn) (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ) :
    ush_wc_inp γ T Wc ->
    ush_wc_inp γ T (fun (I : list (bv 8)) (p : nat) => Wc I p ∗ Hold I)%I.
  Proof using .
    intros Hw I p. iIntros "[Hc Hh]".
    iPoseProof (Hw I p) as "Hr".
    iDestruct ("Hr" with "Hc") as "[Hc $]". iFrame "Hc Hh".
  Qed.

  Lemma ush_wb_inp_hold (γ : echo_gn) (T : iProp Σ)
      (Wb : list (bv 8) -> iProp Σ)
      (Hold : list (bv 8) -> iProp Σ) :
    ush_wb_inp γ T Wb ->
    ush_wb_inp γ T (fun I : list (bv 8) => Wb I ∗ Hold I)%I.
  Proof using .
    intros Hw I. iIntros "[Hc Hh]".
    iPoseProof (Hw I) as "Hr".
    iDestruct ("Hr" with "Hc") as "[Hc $]". iFrame "Hc Hh".
  Qed.

  (* ---- ...AND THE SHAPE RULING H' FIXES: the era's boot state as a
          SHARED INDEX between the credential and the hold ---- *)
  Lemma ush_wc_inp_ex (γ : echo_gn) (T : iProp Σ)
      (Wc : fstate -> list (bv 8) -> nat -> iProp Σ)
      (Hold : fstate -> list (bv 8) -> iProp Σ) :
    (forall s0 : fstate, ush_wc_inp γ T (Wc s0)) ->
    ush_wc_inp γ T
      (fun (I : list (bv 8)) (p : nat) =>
         ∃ s0 : fstate, Wc s0 I p ∗ Hold s0 I)%I.
  Proof using .
    intros Hw I p. iIntros "H". iDestruct "H" as (s0) "[Hc Hh]".
    iPoseProof (Hw s0 I p) as "Hr".
    iDestruct ("Hr" with "Hc") as "[Hc $]". iExists s0. iFrame "Hc Hh".
  Qed.

  Lemma ush_wb_inp_ex (γ : echo_gn) (T : iProp Σ)
      (Wb : fstate -> list (bv 8) -> iProp Σ)
      (Hold : fstate -> list (bv 8) -> iProp Σ) :
    (forall s0 : fstate, ush_wb_inp γ T (Wb s0)) ->
    ush_wb_inp γ T
      (fun I : list (bv 8) => ∃ s0 : fstate, Wb s0 I ∗ Hold s0 I)%I.
  Proof using .
    intros Hw I. iIntros "H". iDestruct "H" as (s0) "[Hc Hh]".
    iPoseProof (Hw s0 I) as "Hr".
    iDestruct ("Hr" with "Hc") as "[Hc $]". iExists s0. iFrame "Hc Hh".
  Qed.

End UShLineHold.

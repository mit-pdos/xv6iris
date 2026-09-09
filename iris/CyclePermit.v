(* CyclePermit.v -- the UNCOUNTED cycle permit for the two stock trace       *)
(*  predicates (claude-notes/projects/liveness.md, D4).                      *)
(*                                                                          *)
(*  [RiscvPtsto.gen_cert] carries [cycle_permit_any]: for every hart, the   *)
(*  client's authorisation of a cycle announcement that leaves the hart's   *)
(*  fuel at [Any].  It is the boot client's to supply, exactly as the UART  *)
(*  thread's permit is ([WpUart.uart_obs_permit]), and the two stock trace  *)
(*  predicates pay it here: the trivial slot by moving the history, a      *)
(*  ledger by its client's own cycle wand.  A leaf beside [WpUart], below   *)
(*  the boot cone.                                                          *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import RiscvPtsto.

Section cycle_permit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* the trivial slot: the client's half moves and nothing is known *)
  Lemma cycle_permit_any_triv :
    riscv_obs_pred = obs_pred_triv ->
    obs_inv -∗ cycle_permit_any.
  Proof.
    intros Heq. iIntros "#Hoinv".
    rewrite /cycle_permit_any /cycle_permit_any_at. iIntros (c).
    rewrite /cycle_permit_at. iIntros "!>" (σ h) "%Hwf Hsi Hauth Hfuel".
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_pred_triv) in "HP".
    iDestruct "HP" as (h') ">Hfrag".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    iMod (obs_update _
            (h ++ [ObsCycle c (register_lookup PC σ.(sregs)) σ.(mdev)])%list
            with "Hauth Hfrag") as "[Hauth Hfrag]".
    iMod ("Hclose" with "[Hfrag]") as "_".
    { iNext. rewrite Heq /obs_pred_triv. iExists _. iExact "Hfrag". }
    iModIntro. iFrame "Hsi Hauth Hfuel".
  Qed.

  (* a ledger: the client's cycle wand, at a mask that lets it open the
     crash invariant too, as its UART wands may *)
  Lemma cycle_permit_any_ledger (R : list mobs -> iProp Σ)
      (HRt : forall h, Timeless (R h))
      (Heq : riscv_obs_pred = obs_ledger R)
      (Hcyc : ⊢ □ (∀ (h : list mobs) (c : CPU) (pc : SailStdpp.Values.mword 64)
                     (d : dev_state),
                  ⌜trace_shape h true⌝ -∗ R h ={⊤ ∖ ↑obsN}=∗
                  R (h ++ [ObsCycle c pc d])%list)) :
    obs_inv -∗ cycle_permit_any.
  Proof.
    iIntros "#Hoinv". iPoseProof Hcyc as "#Hcyc".
    rewrite /cycle_permit_any /cycle_permit_any_at. iIntros (c).
    rewrite /cycle_permit_at. iIntros "!>" (σ h) "%Hwf Hsi Hauth Hfuel".
    destruct Hwf as (Hsh & _ & _).
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_ledger) in "HP".
    iDestruct "HP" as (h') "[>Hfrag >HR]".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    iMod ("Hcyc" $! h c (register_lookup PC σ.(sregs)) σ.(mdev)
            with "[//] HR") as "HR".
    iMod (obs_update _
            (h ++ [ObsCycle c (register_lookup PC σ.(sregs)) σ.(mdev)])%list
            with "Hauth Hfrag") as "[Hauth Hfrag]".
    iMod ("Hclose" with "[Hfrag HR]") as "_".
    { iNext. rewrite Heq /obs_ledger. iExists _. iFrame. }
    iModIntro. iFrame "Hsi Hauth Hfuel".
  Qed.
End cycle_permit.

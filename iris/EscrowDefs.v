(* ============================================================================
   OPTION A (reordered iput) -- the imark-FREE escrow tokens, keyed on the
   ambient registry gname [icfg_reg].  Below InodeRegion so [ireg_slot]'s
   pending arm can carry [region_pending].  Ported from the validated
   EscrowRegionA.v de-risk; the escrow BODY (which mentions [imark]) lives in
   EscrowInode.v, above InodeRegion.
   ========================================================================== *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.algebra Require Import excl dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map mono_nat own invariants.
Require Import RiscvPtsto.
Require Import IcacheRef.

Notation ST_EMPTY := 0%nat.
Notation ST_FILLED := 1%nat.
Notation ST_REDEEMED := 2%nat.

Section EscrowDefs.
  Context `{!riscvGS Σ, !icacheG Σ}.
  Context `{ICFG : icfg}.

  (* the one-shot "deposit happened" flag (mono_natG is ambient from riscvGS) *)
  Definition committedA (ge : gname) : iProp Σ := mono_nat_lb_own ge ST_FILLED.
  Global Instance committedA_persistent ge : Persistent (committedA ge).
  Proof. rewrite /committedA. apply _. Qed.
  Global Instance committedA_timeless ge : Timeless (committedA ge).
  Proof. rewrite /committedA. apply _. Qed.

  (* the exclusive redemption ticket (icacheG's [icache_tickG]) *)
  Definition redeem_ticketA (gr : gname) : iProp Σ := own gr (Excl ()).
  Global Instance redeem_ticketA_timeless gr : Timeless (redeem_ticketA gr).
  Proof. rewrite /redeem_ticketA. apply _. Qed.
  Lemma redeem_ticketA_excl gr : redeem_ticketA gr -∗ redeem_ticketA gr -∗ False.
  Proof.
    rewrite /redeem_ticketA. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    exfalso. exact (exclusive_l (Excl ()) (Excl ()) Hv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE CORPSE LEDGER's ELEMENT (durable-disk lane C-7)                 *)
  (* ------------------------------------------------------------------ *)
  (* One row per inum in the pool's IN-TRANSITION index, at the ambient
     [IcacheRef.icfg_pcrp].  The AUTHORITY is a conjunct of
     [IcacheEscrow.ipool_body] (so the commit reads every row with no lock
     taken); THIS is the element the freeing walk carries from the +0x94 park
     ([IcacheEscrow.ipool_put_corpse]) to the off-lock deposit
     ([EscrowDeposit.ireg_free_deposit_au]) -- across the release of the
     itable lock, which is why the ledger is a [ghost_map] and not a paired
     [ghost_var] like [IcacheEscrow.ipool_tkey]: the element ALONE locates
     the row.  [Xv6Cameras.icorpse] says what each value parks. *)
  Definition crp_elem (z : Z) (v : icorpse) : iProp Σ :=
    (z ↪[icfg_pcrp] v)%I.

  Global Instance crp_elem_timeless z v : Timeless (crp_elem z v).
  Proof. rewrite /crp_elem. apply _. Qed.

  (* two elements at one inum are absurd: the ledger is exclusive per key,
     which is what makes the element a walk's private handle. *)
  Lemma crp_elem_excl z v1 v2 : crp_elem z v1 -∗ crp_elem z v2 -∗ False.
  Proof.
    rewrite /crp_elem. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_valid_own in Hv. exact (Qp.not_add_le_l 1 1 Hv).
  Qed.

  (* the per-inum registry element (icacheG's [icache_regG], over [icfg_reg]).
     A pending slot holds the HALF region-side; the pool's pending_free arm
     holds the other half; a non-pending/boot-free inum's FULL element rides
     the pool's imark/alloc arm, where it refutes the pending branch at
     [ireg_claim_au] by fraction overflow. *)
  Definition reg_half (z : Z) (ge gr : gname) : iProp Σ :=
    (z ↪[icfg_reg]{# (1/2)} (ge, gr))%I.
  Definition reg_full (z : Z) (ge gr : gname) : iProp Σ :=
    (z ↪[icfg_reg] (ge, gr))%I.

  Global Instance reg_half_timeless z ge gr : Timeless (reg_half z ge gr).
  Proof. rewrite /reg_half. apply _. Qed.
  Global Instance reg_full_timeless z ge gr : Timeless (reg_full z ge gr).
  Proof. rewrite /reg_full. apply _. Qed.

  (* two halves agree on the escrow name pair -- forces the redeemer's pool
     ticket and the region's committed to name the SAME escrow *)
  Lemma reg_half_agree z ge1 gr1 ge2 gr2 :
    reg_half z ge1 gr1 -∗ reg_half z ge2 gr2 -∗ ⌜ge1 = ge2 /\ gr1 = gr2⌝.
  Proof.
    rewrite /reg_half. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. split; congruence.
  Qed.

  (* THE ireg_claim_au REFUTATION: a full element and any half of the SAME key
     exceed fraction 1 -- impossible.  ialloc holds [reg_full z] for the inum
     it claims (rijoined from the redeem, or read from the pool's imark arm for
     a boot-free inum), so the pending arm's [reg_half] is refuted here. *)
  Lemma reg_full_half_False z ge gr ge' gr' :
    reg_full z ge gr -∗ reg_half z ge' gr' -∗ False.
  Proof.
    rewrite /reg_full /reg_half. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
    exact (Qp.not_add_le_l 1 (1/2) Hv).
  Qed.

  Lemma reg_join z ge gr :
    reg_half z ge gr -∗ reg_half z ge gr -∗ reg_full z ge gr.
  Proof.
    rewrite /reg_full /reg_half. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own Qp.div_2. iExact "H".
  Qed.

  (* the inverse of [reg_join]: the off-lock deposit splits the marked slot's
     whole [reg_full] into the structural half (stays in the pending arm) and
     the [region_pending] half. *)
  Lemma reg_split z ge gr :
    reg_full z ge gr -∗ reg_half z ge gr ∗ reg_half z ge gr.
  Proof.
    rewrite /reg_full /reg_half. iIntros "H".
    iEval (rewrite -{1}(Qp.div_2 1)) in "H".
    iDestruct "H" as "[H1 H2]". iFrame.
  Qed.

  (* the region-side pending payload: reg_half (½ of the registry element) +
     committed (persistent).  [esc_inv] (not Timeless) rides the POOL side, so
     this stays Timeless and [ireg_body]'s [iInv .. as ">"] is unaffected. *)
  Definition region_pending (z : Z) : iProp Σ :=
    (∃ ge gr, reg_half z ge gr ∗ committedA ge)%I.
  Global Instance region_pending_timeless z : Timeless (region_pending z).
  Proof. rewrite /region_pending. apply _. Qed.

End EscrowDefs.

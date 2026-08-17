(* ============================================================================
   OPTION A (reordered iput) -- the per-inum ESCROW BODY (mentions [imark], so
   above InodeRegion) + [pool_pending] (the pool's pending_free arm).  Ported
   from the validated EscrowRegionA.v de-risk; keyed on [icfg_reg] via
   [EscrowDefs].
   ========================================================================== *)

From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap.
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat own.
Require Import RiscvPtsto.
Require Import IcacheRef.
Require Import EscrowDefs.
Require Import InodeRegion.

Section EscrowInode.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  (* the per-inum one-shot escrow body, over the REAL [InodeRegion.imark].
     FILLED holds the escrowed marker; REDEEMED holds the spent ticket. *)
  Definition escA_body (ge gr γi : gname) (z : Z) : iProp Σ :=
    ( mono_nat_auth_own ge 1 ST_EMPTY
    ∨ (mono_nat_auth_own ge 1 ST_FILLED ∗ InodeRegion.imark γi z)
    ∨ (mono_nat_auth_own ge 1 ST_REDEEMED ∗ redeem_ticketA gr) )%I.

  Definition escAN (z : Z) : namespace := (nroot .@ "icescA") .@ z.
  Definition escA_inv (ge gr γi : gname) (z : Z) : iProp Σ :=
    inv (escAN z) (escA_body ge gr γi z).
  Global Instance escA_inv_persistent ge gr γi z :
    Persistent (escA_inv ge gr γi z).
  Proof. rewrite /escA_inv. apply _. Qed.

  (* minted at iput+0x86 (before itable.lock release): fresh escrow, EMPTY,
     with its exclusive ticket.  The deposit that fills it happens later, at
     the off-lock ifree. *)
  Lemma escA_alloc E γi z :
    ⊢ |={E}=> ∃ ge gr, escA_inv ge gr γi z ∗ redeem_ticketA gr.
  Proof.
    iIntros.
    iMod (mono_nat_own_alloc ST_EMPTY) as (ge) "[Hauth _]".
    iMod (own_alloc (Excl ())) as (gr) "Htick"; [done|].
    iMod (inv_alloc (escAN z) _ (escA_body ge gr γi z) with "[Hauth]")
      as "#Hinv".
    { iNext. iLeft. iExact "Hauth". }
    iModIntro. iExists ge, gr. iFrame "Hinv Htick".
  Qed.

  (* the off-lock ifree deposits the region marker; out comes [committed] *)
  Lemma escA_deposit E ge gr γi z :
    ↑escAN z ⊆ E →
    escA_inv ge gr γi z -∗ InodeRegion.imark γi z ={E}=∗ committedA ge.
  Proof.
    iIntros (HE) "#Hinv Hmk".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody" as "[Hauth | [[Hauth Hmk2] | [Hauth Htick]]]".
    - iMod (mono_nat_own_update ST_FILLED with "Hauth") as "[Hauth #Hlb]".
      { lia. }
      iMod ("Hcl" with "[Hauth Hmk]") as "_".
      { iNext. iRight; iLeft. iFrame "Hauth Hmk". }
      iModIntro. iExact "Hlb".
    - iExFalso. iApply (InodeRegion.imark_excl with "Hmk Hmk2").
    - iDestruct (mono_nat_lb_own_get with "Hauth") as "#Hlb2".
      iMod ("Hcl" with "[Hauth Htick]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick". }
      iModIntro.
      iApply (mono_nat_lb_own_le ST_FILLED with "Hlb2"). lia.
  Qed.

  (* the redeemer's ticket + the region's committed recover the marker *)
  Lemma escA_redeem E ge gr γi z :
    ↑escAN z ⊆ E →
    escA_inv ge gr γi z -∗ redeem_ticketA gr -∗ committedA ge
      ={E}=∗ InodeRegion.imark γi z.
  Proof.
    iIntros (HE) "#Hinv Htick #Hcom".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody" as "[Hauth | [[Hauth Hmk] | [Hauth Htick2]]]".
    - iDestruct (mono_nat_lb_own_valid with "Hauth Hcom") as %[_ Hle]. lia.
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick". }
      iModIntro. iExact "Hmk".
    - iExFalso. iApply (redeem_ticketA_excl with "Htick Htick2").
  Qed.

  (* THE POOL's pending_free arm: the persistent escrow invariant, the
     exclusive ticket, and the pool's half of the registry element (the other
     half rides the region's PENDING arm; they agree via [reg_half_agree]). *)
  (* OPTION A (b)(ii): the pool's pending arm carries the PERSISTENT commit
     witness [committedA] and the redeem ticket, i.e. everything the itable
     free pool needs to REDEEM this entry to an [imark] pool-locally (no
     [ireg_inv]).  It deliberately does NOT hold a [reg_half]: the registry
     half stays on the region side / in [ireg_body], so a recycle/fill of a
     genuine pending entry leaves nothing to dispose.  Walk-stable. *)
  Definition pool_pending (γi : gname) (z : Z) : iProp Σ :=
    (∃ ge gr, escA_inv ge gr γi z ∗ committedA ge ∗ redeem_ticketA gr)%I.
  (* NOT Timeless: [escA_inv] is an [inv].  Wherever [ipool_shape] must stay
     Timeless, its pending arm is opened without the [>] later-strip. *)

End EscrowInode.

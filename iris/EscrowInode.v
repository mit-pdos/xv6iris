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
  (* ---- THE FREEZE TOKEN RIDES THE ESCROW (iclaim-ledger.md §3.16, A⁗) ---

     The EMPTY state carries [ifreeze_post z] and the FILLED one
     [ifreeze_off z], and that ONE placement does three jobs at once:

     (a) it gives [IcacheEscrow.pool_await] its refuter back.  IIIa parked
         [ifreeze_post] in the pool's await arm itself, and A⁗ cannot: the
         phase fragment has to stay reachable by the OFF-LOCK deposit at
         iput+0xba, which runs after the pool bundle has gone back under the
         itable lock at +0x94.  Here it is reachable from both sides -- the
         deposit opens [escAN z] anyway, and a RECYCLER peeling the await arm
         opens it too and finds the standing freeze, which its licence then
         refutes ([IgetLic.iname_freeze_off]: a licence puts the column at
         [FrzOff], §2.6's table).  §1.3's original design, at last buildable.
     (b) it retires the token at the one instant the free path's type-0 write
         lands: [escA_deposit] hands [ifreeze_post] OUT to
         [EscrowDeposit.ireg_free_deposit_au] (which steps the column back to
         [FrzOff]) and takes the returned [ifreeze_off] IN, so the deposit
         needs no token premise from the walk at all.
     (c) it re-arms the pool: [escA_redeem] hands the [ifreeze_off] to
         whoever converts the await arm to [imark], which is exactly the
         token [IcacheEscrow.ipool_shape]'s ordinary arms owe.
     REDEEMED holds neither: by then the token is in the peeler's hand and
     the pool entry is an ordinary one. *)
  (* ...AND THE DEPOSIT TICKET [gd], the third gname (§3.16).  It is the
     freer's proof that ITS deposit has not run: minted with the escrow,
     carried in the freer's own hand from iput+0x8a to the off-lock ifree at
     +0xba, and PARKED here by the deposit itself.  Without it the deposit
     cannot rule the REDEEMED arm out -- [imark] refutes FILLED but a peeler
     has already carried the marker away by REDEEMED -- and with it both bad
     arms die on one [Excl] apiece.  It is the ordinary "this one-shot has not
     fired" token; [redeem_ticketA]'s RA, at a second name. *)
  Definition escA_body (ge gr gd γi : gname) (z : Z) : iProp Σ :=
    ( (mono_nat_auth_own ge 1 ST_EMPTY ∗ ifreeze_post z)
    ∨ (mono_nat_auth_own ge 1 ST_FILLED ∗ InodeRegion.imark γi z
       ∗ ifreeze_off z ∗ redeem_ticketA gd)
    ∨ (mono_nat_auth_own ge 1 ST_REDEEMED ∗ redeem_ticketA gr
       ∗ redeem_ticketA gd) )%I.

  Definition escAN (z : Z) : namespace := (nroot .@ "icescA") .@ z.
  Definition escA_inv (ge gr gd γi : gname) (z : Z) : iProp Σ :=
    inv (escAN z) (escA_body ge gr gd γi z).
  Global Instance escA_inv_persistent ge gr gd γi z :
    Persistent (escA_inv ge gr gd γi z).
  Proof. rewrite /escA_inv. apply _. Qed.

  (* minted at iput+0x86 (before itable.lock release): fresh escrow, EMPTY,
     with its exclusive ticket.  The deposit that fills it happens later, at
     the off-lock ifree. *)
  Lemma escA_alloc E γi z :
    (* THE STANDING FREEZE GOES IN AT THE MINT (§3.16): iput's last close has
       just stepped the column to [FrzPost], and this is where the fragment
       lives until the off-lock deposit retires it. *)
    ifreeze_post z ={E}=∗ ∃ ge gr gd,
      escA_inv ge gr gd γi z ∗ redeem_ticketA gr ∗ redeem_ticketA gd.
  Proof.
    iIntros "Hfz".
    iMod (mono_nat_own_alloc ST_EMPTY) as (ge) "[Hauth _]".
    iMod (own_alloc (Excl ())) as (gr) "Htick"; [done|].
    iMod (own_alloc (Excl ())) as (gd) "Hdep"; [done|].
    iMod (inv_alloc (escAN z) _ (escA_body ge gr gd γi z) with "[Hauth Hfz]")
      as "#Hinv".
    { iNext. iLeft. iFrame "Hauth Hfz". }
    iModIntro. iExists ge, gr, gd. iFrame "Hinv Htick Hdep".
  Qed.

  (* the off-lock ifree deposits the region marker; out comes [committed] *)
  (* THE DEPOSIT IS NOW A SWAP (§3.16): the marker and the RETIRED token go
     in, the STANDING one comes out.  Its caller
     ([EscrowDeposit.ireg_free_deposit_au]) is what turns one into the other,
     so the two halves of this exchange are one atomic step at the region. *)
  (* THE DEPOSIT, AS AN ACCESSOR (iclaim-ledger.md §3.16).  The off-lock
     ifree needs the standing [ifreeze_post] BEFORE it can step the region's f
     column, and it needs the resulting [ifreeze_off] to be back in the escrow
     afterwards -- so the escrow is HELD OPEN across the region step rather
     than handed a wand, and the depositor's own ticket is what rules out the
     two arms in which the token is no longer here. *)
  Lemma escA_deposit_acc E ge gr gd γi z :
    ↑escAN z ⊆ E →
    escA_inv ge gr gd γi z -∗ redeem_ticketA gd
      ={E, E ∖ ↑escAN z}=∗
      ifreeze_post z ∗
      (InodeRegion.imark γi z -∗ ifreeze_off z
         ={E ∖ ↑escAN z, E}=∗ committedA ge).
  Proof.
    iIntros (HE) "#Hinv Hdep".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[[Hauth Hfz] | [(Hauth & Hmk2 & Hoff2 & Hd2) | (Hauth & Htick & Hd2)]]".
    - iModIntro. iFrame "Hfz". iIntros "Hmk Hoff".
      iMod (mono_nat_own_update ST_FILLED with "Hauth") as "[Hauth #Hlb]".
      { lia. }
      iMod ("Hcl" with "[Hauth Hmk Hoff Hdep]") as "_".
      { iNext. iRight; iLeft. iFrame "Hauth Hmk Hoff Hdep". }
      iModIntro. iExact "Hlb".
    - iExFalso. iApply (redeem_ticketA_excl with "Hdep Hd2").
    - iExFalso. iApply (redeem_ticketA_excl with "Hdep Hd2").
  Qed.

  (* the redeemer's ticket + the region's committed recover the marker *)
  Lemma escA_redeem E ge gr gd γi z :
    ↑escAN z ⊆ E →
    escA_inv ge gr gd γi z -∗ redeem_ticketA gr -∗ committedA ge
      ={E}=∗ InodeRegion.imark γi z ∗ ifreeze_off z.
  Proof.
    iIntros (HE) "#Hinv Htick #Hcom".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[[Hauth _] | [(Hauth & Hmk & Hoff & Hd) | (Hauth & Htick2 & _)]]".
    - iDestruct (mono_nat_lb_own_valid with "Hauth Hcom") as %[_ Hle]. lia.
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick Hd]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick Hd". }
      iModIntro. iFrame "Hmk Hoff".
    - iExFalso. iApply (redeem_ticketA_excl with "Htick Htick2").
  Qed.

  (* ...AND THE AWAIT ARM's PEEL (iclaim-ledger.md §3.16 / §1.3): a recycler
     or a fill that reaches an inum iput is still freeing has NO
     [committedA] -- the deposit has not run -- so it cannot redeem.  What it
     gets instead is the STANDING freeze the escrow is holding, which its own
     LICENCE refutes at the region ([IgetLic.iname_freeze_off]).  The token is
     borrowed and given straight back, so the refuter pays nothing for it. *)
  Lemma escA_await_peel E ge gr gd γi z (P : iProp Σ) :
    ↑escAN z ⊆ E →
    escA_inv ge gr gd γi z -∗ redeem_ticketA gr -∗
    (* the refuter's OWN resource (in practice the peeler's licence), carried
       through so the SUCCESS branch does not lose it to the wand's closure *)
    P -∗
    (* THE REFUTER, handed in as a wand: "no freeze stands at this inum".
       Its discharge is the caller's LICENCE ([IgetLic.iname_freeze_off] --
       §2.6's table, at whichever of the five constructors the caller
       presented), which needs [↑iregN] and nothing this escrow holds, so the
       mask is the peel's own minus this one namespace. *)
    (P -∗ ifreeze_post z ={E ∖ ↑escAN z}=∗ False)
      ={E}=∗ P ∗ InodeRegion.imark γi z ∗ ifreeze_off z.
  Proof.
    iIntros (HE) "#Hinv Htick HP Href".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[[Hauth Hfz] | [(Hauth & Hmk & Hoff & Hd) | (Hauth & Htick2 & _)]]".
    - iMod ("Href" with "HP Hfz") as "[]".
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick Hd]") as "_".
      { iNext. iRight; iRight. iFrame "Hauth Htick Hd". }
      iModIntro. iFrame "HP Hmk Hoff".
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
    (∃ ge gr gd, escA_inv ge gr gd γi z ∗ committedA ge ∗ redeem_ticketA gr)%I.
  (* NOT Timeless: [escA_inv] is an [inv].  Wherever [ipool_shape] must stay
     Timeless, its pending arm is opened without the [>] later-strip. *)

End EscrowInode.

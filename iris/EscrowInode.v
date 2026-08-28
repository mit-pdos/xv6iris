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
(* [FsState.top_frag] / [FsBytesGamma.fs_gamma_L] -- the era's abstract value,
   which the EMPTY arm carries from iput's mint at +0x8a to the off-lock
   deposit (durable-disk C-3c).  Both are already below [InodeRegion]; named
   here because a [Require Import] in a sibling does not put its constants in
   scope.  [fsTopG] itself is an [Xv6G.xv6G] member.
   IMPORTED BEFORE [IcacheRef], for the reason [InodeRegion]'s own preamble
   gives: [FsState] re-exports [FsStateLink]'s [link_auth] and
   [FsStateDefs]'s [byte_range], both of which have live twins below, and
   the LAST import wins. *)
Require Import FsBlocks.
Require Import FsState.
Require Import FsBytesGamma.
Require Import IcacheRef.
Require Import DirViewLend. (* N-4 PHASE B: the arm rides [dv_ride], not [dv_hold] *)
Require Import EscrowDefs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Section EscrowInode.
  Context `{!riscvGS Σ, !xv6G Σ}.
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
         token [IcacheEscrow.ipool_shape_np]'s ordinary arms owe.
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
  (* RULING G' (iclaim-ledger.md §6''): the escrow is INDEXED by the regime
     arm its freezer lent.  It has to be: the standing [ifreeze_post] lives
     here between iput+0x8a and the off-lock deposit, and it is that token's
     agreement with the region's f column that tells the deposit which arm to
     hand back.  The index is carried by the walk (in [redeem_ticketA gd]'s
     company) from the mint to the deposit, so the tie is structural. *)
  (* ---- AND THE ERA'S ABSTRACT VALUE RIDES THE EMPTY ARM (C-3c) --------

     Supplier (D) of [FsCollect]'s collection needs a FREE inum's [top_frag]
     to be parked WITH its record, i.e. region-side ([InodeRegion.ireg_top_park]).
     The one mover that creates a free record is iput's off-lock deposit
     ([EscrowDeposit.ireg_free_deposit_au]), and the fragment it must park is
     the one the freed PAYLOAD carried -- which the walk gives up at +0x94,
     when it parks the pool entry, twenty instructions before the deposit.
     So the fragment travels the same road the standing freeze does: in HERE,
     at the mint, and out again at the deposit's own opening.  It is the
     [ifreeze_post] argument verbatim, and for the same reason (this file's
     (a)/(b) above): the EMPTY arm is the one place both ends can reach. *)
  (* ---- WHAT THE FILLED ARM HOLDS SINCE durable-disk C-7 ---------------

     NOT the region marker any more: [InodeRegion.imark] is what the commit's
     collection needs at a freed-but-unrecycled inum (it refutes the region
     slot's own MARKED arm and leaves the free bundle on the PENDING one),
     and this escrow is an [inv] behind the itable spinlock, so the commit
     cannot reach it.  The marker therefore rides the CORPSE LEDGER, whose
     authority is a conjunct of [IcacheEscrow.ipool_body]; what stands in its
     place here is that ledger row's ELEMENT at [CrpDep].

     THE SWAP IS WHAT TIES THE TWO ONE-SHOTS TOGETHER, and that is its whole
     point.  This escrow and the ledger both record "has the deposit run",
     and a recycler that peels the escrow must be able to conclude the
     ledger's state from it: it does, because the element it gets back here
     agrees with the ledger's authority by [ghost_map_lookup]
     ([IcacheEscrow.ipool_take_lend]).  Without the swap the two state
     machines are untied and the recycle cannot produce the marker at all. *)
  Definition escA_body (γfs : fs_names) (ge gr gd : gname) (z : Z)
      (rg : frzidx) : iProp Σ :=
    ( (mono_nat_auth_own ge 1 ST_EMPTY ∗ ifreeze_post rg z
       ∗ (∃ n : fs_node, top_frag (fs_gamma_L γfs) z n))
    ∨ (mono_nat_auth_own ge 1 ST_FILLED ∗ crp_elem z CrpDep
       ∗ ifreeze_off z ∗ redeem_ticketA gd)
    ∨ (mono_nat_auth_own ge 1 ST_REDEEMED ∗ redeem_ticketA gr
       ∗ redeem_ticketA gd) )%I.

  Definition escAN (z : Z) : namespace := (nroot .@ "icescA") .@ z.
  Definition escA_inv (γfs : fs_names) (ge gr gd : gname) (z : Z)
      (rg : frzidx) : iProp Σ :=
    inv (escAN z) (escA_body γfs ge gr gd z rg).
  Global Instance escA_inv_persistent γfs ge gr gd z rg :
    Persistent (escA_inv γfs ge gr gd z rg).
  Proof. rewrite /escA_inv. apply _. Qed.

  (* minted at iput+0x86 (before itable.lock release): fresh escrow, EMPTY,
     with its exclusive ticket.  The deposit that fills it happens later, at
     the off-lock ifree. *)
  Lemma escA_alloc E γfs z rg :
    (* THE STANDING FREEZE GOES IN AT THE MINT (§3.16): iput's last close has
       just stepped the column to [FrzPost], and this is where the fragment
       lives until the off-lock deposit retires it. *)
    ifreeze_post rg z -∗
    (* ...AND THE FREED PAYLOAD'S ABSTRACT VALUE (durable-disk C-3c), which
       the walk hands over here instead of parking it in the pool's await
       arm; the deposit takes it out again and ties it region-side. *)
    (∃ n : fs_node, top_frag (fs_gamma_L γfs) z n) ={E}=∗ ∃ ge gr gd,
      escA_inv γfs ge gr gd z rg ∗ redeem_ticketA gr ∗ redeem_ticketA gd.
  Proof.
    iIntros "Hfz Htop".
    iMod (mono_nat_own_alloc ST_EMPTY) as (ge) "[Hauth _]".
    iMod (own_alloc (Excl ())) as (gr) "Htick"; [done|].
    iMod (own_alloc (Excl ())) as (gd) "Hdep"; [done|].
    iMod (inv_alloc (escAN z) _ (escA_body γfs ge gr gd z rg)
            with "[Hauth Hfz Htop]") as "#Hinv".
    { iApply bi.later_intro. iLeft. iFrame "Hauth Hfz Htop". }
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
  (* ...AND WHAT IT TAKES BACK IS THE LEDGER'S ELEMENT (durable-disk C-7):
     the depositor updates its corpse row from [CrpPre] to [CrpDep] -- parking
     [InodeRegion.imark] there in place of the freeing transaction's share --
     and hands the element it gets back to this escrow, where it stands until
     a recycler peels the arm. *)
  Lemma escA_deposit_acc E γfs ge gr gd z rg :
    ↑escAN z ⊆ E →
    escA_inv γfs ge gr gd z rg -∗ redeem_ticketA gd
      ={E, E ∖ ↑escAN z}=∗
      ifreeze_post rg z ∗ (∃ n : fs_node, top_frag (fs_gamma_L γfs) z n) ∗
      (crp_elem z CrpDep -∗ ifreeze_off z
         ={E ∖ ↑escAN z, E}=∗ committedA ge).
  Proof.
    iIntros (HE) "#Hinv Hdep".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[(Hauth & Hfz & Htop) | [(Hauth & Hmk2 & Hoff2 & Hd2) | (Hauth & Htick & Hd2)]]".
    - iModIntro. iFrame "Hfz Htop". iIntros "Hmk Hoff".
      iMod (mono_nat_own_update ST_FILLED with "Hauth") as "[Hauth #Hlb]".
      { lia. }
      iMod ("Hcl" with "[Hauth Hmk Hoff Hdep]") as "_".
      { iApply bi.later_intro. iRight; iLeft. iFrame "Hauth Hmk Hoff Hdep". }
      iModIntro. iExact "Hlb".
    - iExFalso. iApply (redeem_ticketA_excl with "Hdep Hd2").
    - iExFalso. iApply (redeem_ticketA_excl with "Hdep Hd2").
  Qed.

  (* the redeemer's ticket + the region's committed recover the marker *)
  Lemma escA_redeem E γfs ge gr gd z rg :
    ↑escAN z ⊆ E →
    escA_inv γfs ge gr gd z rg -∗ redeem_ticketA gr -∗ committedA ge
      ={E}=∗ crp_elem z CrpDep ∗ ifreeze_off z.
  Proof.
    iIntros (HE) "#Hinv Htick #Hcom".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[(Hauth & _ & _) | [(Hauth & Hmk & Hoff & Hd) | (Hauth & Htick2 & _)]]".
    - iDestruct (mono_nat_lb_own_valid with "Hauth Hcom") as %[_ Hle]. lia.
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick Hd]") as "_".
      { iApply bi.later_intro. iRight; iRight. iFrame "Hauth Htick Hd". }
      iModIntro. iFrame "Hmk Hoff".
    - iExFalso. iApply (redeem_ticketA_excl with "Htick Htick2").
  Qed.

  (* ...AND THE AWAIT ARM's PEEL (iclaim-ledger.md §3.16 / §1.3): a recycler
     or a fill that reaches an inum iput is still freeing has NO
     [committedA] -- the deposit has not run -- so it cannot redeem.  What it
     gets instead is the STANDING freeze the escrow is holding, which its own
     LICENCE refutes at the region ([IgetLic.iname_freeze_off]).  The token is
     borrowed and given straight back, so the refuter pays nothing for it. *)
  Lemma escA_await_peel E γfs ge gr gd z rg (P : iProp Σ) :
    ↑escAN z ⊆ E →
    escA_inv γfs ge gr gd z rg -∗ redeem_ticketA gr -∗
    (* the refuter's OWN resource (in practice the peeler's licence), carried
       through so the SUCCESS branch does not lose it to the wand's closure *)
    P -∗
    (* THE REFUTER, handed in as a wand: "no freeze stands at this inum".
       Its discharge is the caller's LICENCE ([IgetLic.iname_freeze_off] --
       §2.6's table, at whichever of the five constructors the caller
       presented), which needs [↑iregN] and nothing this escrow holds, so the
       mask is the peel's own minus this one namespace. *)
    (P -∗ ifreeze_post rg z ={E ∖ ↑escAN z}=∗ False)
      ={E}=∗ P ∗ crp_elem z CrpDep ∗ ifreeze_off z.
  Proof.
    iIntros (HE) "#Hinv Htick HP Href".
    iInv "Hinv" as ">Hbody" "Hcl".
    iDestruct "Hbody"
      as "[(Hauth & Hfz & _) | [(Hauth & Hmk & Hoff & Hd) | (Hauth & Htick2 & _)]]".
    - iMod ("Href" with "HP Hfz") as "[]".
    - iMod (mono_nat_own_update ST_REDEEMED with "Hauth") as "[Hauth _]".
      { lia. }
      iMod ("Hcl" with "[Hauth Htick Hd]") as "_".
      { iApply bi.later_intro. iRight; iRight. iFrame "Hauth Htick Hd". }
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
  (* ...AND THE CONTENTS HOLD, UNTIED (namei-pinned-lookup.md §9 W2).  Every
     arm an UNCACHED inum's pool bundle can stand on carries the inum's
     [dv_hold]: the tie to the bytes exists only where the bytes do
     ([ipool_alloc], [ic_loaded]), so a byte-less arm holds the element at a
     forgotten value and the next fill sets it.  Without it this arm's redeem
     to an [imark] would have to conjure the hold.
     N-5.2A: and the per-FILE contents hold beside it, untied for the same
     reason and carried the same way (namei-pinned-lookup.md §13). *)
  Definition pool_pending (γfs : fs_names) (z : Z) : iProp Σ :=
    (∃ ge gr gd (rg : frzidx),
       escA_inv γfs ge gr gd z rg ∗ committedA ge ∗ redeem_ticketA gr ∗
       (∃ e, dv_ride z e) ∗ (∃ b, fv_ride z b))%I.
  (* NOT Timeless: [escA_inv] is an [inv].  Wherever the pool row must stay
     Timeless, its pending arm is opened without the [>] later-strip. *)

End EscrowInode.

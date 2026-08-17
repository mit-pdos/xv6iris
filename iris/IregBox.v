(* ======================================================================= *)
(*  IregBox.v -- THE CLAIM BOX'S EXCLUSION LEMMAS (T1), AND THE THREE       *)
(*  FLANKS OF [SpecCreateFreshTy.create_fresh_ty].                          *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS.

    [SpecCreateFreshTy]'s axiom is the one assumed fact in the fs tree, and
    eight probes have now certified that no ghost-side route retires it
    (claude-notes/design/fs-fragments.md section 7, walls indexed at 7.0,
    the station-exhaustion certificate at 7.10.6).  What those probes DID
    establish is a reduction: the axiom's content is bounded by a window of
    three instructions inside [ialloc], and everything on either side of
    that window is provable TODAY.  This file is that "everything else",
    machine-checked, so the axiom's header can cite lemma names rather than
    paragraphs.

    THE THREE FLANKS, and what each one is:

      PRE-BRELSE (phase 1, [ialloc]+0x9a .. +0xa0).  The claimant holds the
      dinode block's [fs_L] half from its [bread] to its [brelse].  Every
      region mover -- [ireg_claim_au], [ireg_write_au], [ireg_write_link],
      [ireg_write_unlink], [ireg_free_au] -- hands its caller the REGION's
      half and demands it back at new bytes, so firing one requires holding
      the other half.  Two halves are the whole element, so a third fraction
      anywhere is a contradiction: [fsL_block_exclusive].  While the claim
      is in the claimant's buffer window, NO foreign mover at ANY of that
      block's sixteen inums can fire.

      POST-IGET (phase 3, from [ialloc]'s [iget] onward).  create holds an
      icache reference to the slot.  [iput]'s free path is gated on
      [ip->ref == 1], which the model reads as the slot's count being one
      ([IcacheInv.iref_lookup]'s third conjunct, REF-1).  A second reference
      forces the count to two: [iref_two_not_ref1].  So while create's
      reference lives, no foreign [iput] can reach its free at all.

      THE BOX ITSELF (T1).  While the claim box stands -- the region's IN
      arm at a nonzero type -- the record fragment is INSIDE the region, so
      nothing else in the system holds it: no client [dinode_at], no pool
      bundle, no loaded entry, and no live directory record names the inum.
      The box is therefore exited by exactly one mover, [ireg_withdraw],
      whose sole gate is the marker.  [ireg_box_excl],
      [ireg_claim_box_freeze], [ireg_box_no_payload].

    WHAT IS LEFT AFTER THE THREE, AND IT IS THE AXIOM.  Phase 2 -- from
    [brelse]'s return at [ialloc]+0xa4 to the [jal iget] at +0xaa -- is the
    one interval in which the claimant holds NOTHING revocable: no buffer
    fraction, no reference, no fragment, only the region's own arm, which is
    not a resource it holds.  T1 says the box is frozen WHILE IT STANDS; it
    cannot say the box that create's [ilock] withdraws is create's own box,
    because a foreign filler's [ireg_withdraw] is machine-legal there and a
    ghost cannot forbid it (fs-fragments.md 7.4.4, 7.6.2, 7.10.6).  That
    residue is [create_fresh_ty], and the reduction is stated at the head of
    [SpecCreateFreshTy.v].

    THE "EVERY FREE PASSES THROUGH A FILL" CHAIN, AND ITS HONEST FORM.  At
    the C level the fact is about a bit: [iput]'s free path tests
    [ip->valid], and [ip->valid] is set in exactly one place, [ilock]'s
    fill.  THE MODEL DOES NOT NEED THE BIT, and stating it over the bit
    would be strictly weaker.  [ireg_free_au] takes ONE caller-side
    resource, [dinode_at gi inum dn] -- a full-fraction region fragment --
    and at a box that fragment is in the region: [ireg_claim_box_freeze]
    refutes any client copy and [ireg_box_no_payload] refutes the two
    payloads it could have been parked in.  So "no free without a fill" is
    a custody theorem about the fragment, not a control-flow claim about a
    word, and it is proved here without reference to [i_valid] at all.
    The delta is recorded because it is the sharper statement, not a
    weakening: the fragment is a strictly stronger carrier than the bit
    (the bit is per-ENTRY and dies at eviction; the fragment is per-INUM
    and is conserved -- fs-fragments.md 7.7's conservation law).

    HOME.  The three [ireg_*] lemmas belong in [InodeRegion.v] and the
    first flank in [FsBlocks.v]; they are here for [IregLinkNz.v]'s and
    [IregDirBit.v]'s reason -- both of those files sit under ~350
    dependents and an additive lemma inside either costs that cone on every
    iteration (durable-notes, "the rebuild cone is the dev-loop cost").
    Fold the three leaves back together at a milestone.  Nothing in this
    file is consumed by any proof yet: it is the formal content the
    probes owed, landed so that a ninth attempt starts from lemma
    statements instead of from prose. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.algebra Require Import auth gmap frac excl numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants own ghost_map.
Require Import SailStdpp.Values.
Require Import RiscvPtsto.
Require Import WpLock.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.

Local Open Scope Z_scope.

Section IregBoxPure.

  (* ------------------------------------------------------------------ *)
  (*  THE BOX'S SHAPE AND ITS COUNT -- pure, and this is all of T1 that   *)
  (*  is pure                                                            *)
  (* ------------------------------------------------------------------ *)

  (* [ireg_in d] is [type = 0 \/ fresh_shape d] and [fresh_shape] INCLUDES
     [type <> 0], so the two sub-cases of the IN arm are disjoint and a
     nonzero type picks the right one.  This is why T1 needs no new clause:
     the claim box IS the IN arm read at a nonzero type. *)
  Lemma ireg_box_fresh (d : dinode) :
    ireg_in d -> bv_unsigned (di_type d) <> 0 -> fresh_shape d.
  Proof. intros [H0 | Hf] Hnz; [exfalso; exact (Hnz H0) | exact Hf]. Qed.

  (* ...and (L1) at [nlink = 0] collapses the ledger's whole ternary sum:
     NO LIVE DIRECTORY RECORD NAMES A CLAIM BOX, of any flavour. *)
  Lemma ireg_box_w0 (d : dinode) (w : nat) :
    ireg_in d -> bv_unsigned (di_type d) <> 0 -> ireg_link_ok d w ->
    w = 0%nat.
  Proof.
    intros Hin Hnz Hlok.
    exact (ireg_wle_zero (bv_unsigned (di_nlink d)) w (proj1 Hlok)
             (fresh_shape_nlink d (ireg_box_fresh d Hin Hnz))).
  Qed.

End IregBoxPure.

Section IregBox.
  Context `{!riscvGS Σ, !lockG Σ, !icacheG Σ, !irefslotG Σ,
            !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !logG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

  (* ------------------------------------------------------------------ *)
  (*  T1 -- THE CLAIM-BOX FREEZE                                          *)
  (* ------------------------------------------------------------------ *)

  (* THE DICHOTOMY AT A NONZERO-TYPE SLOT, and it is T1's formal content.

     A slot whose record has a nonzero type is in exactly one of two
     states, and the region's own arm decides which:

       OUT -- the record is CHECKED OUT (a pool bundle, an [ic_loaded], a
              critical section's hand) and the region holds the MARKER;
       IN  -- the record is a CLAIM BOX, and then [fresh_shape] holds, the
              ledger's sum is zero so no [ilink] of ANY flavour names the
              inum, and no client anywhere holds the record fragment.

     Stated as a disjunction rather than under an IN-ness hypothesis
     because IN-ness is not nameable from outside the region: the arm is
     the region's own existential and the marker -- the one witness that
     picks it -- is in the pool at a claim box, behind the itable spinlock
     [ialloc] does not hold (fs-fragments.md 7.4.3).  A caller that holds a
     [dinode_at] at the inum lands in the LEFT disjunct by its own
     fragment, which is exactly the reading [ireg_free_au] performs.

     THE THREE REFUTATIONS ARE THE PROBES' "box-exclusion" (7.6.1), and it
     costs neither a licence enumeration nor a new invariant clause. *)
  Lemma ireg_box_excl (gi : gname) (z : Z) (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    ireg_slot gi z d -∗
      imark gi z
      ∨ (⌜fresh_shape d⌝
         ∗ (∀ fl : option (option Z), ilink_fl fl z -∗ False)
         ∗ (∀ (inum : bv 32) (dn : dinode),
              ⌜bv_unsigned inum = z⌝ -∗ dinode_at gi inum dn -∗ False)).
  Proof.
    iIntros (Hnz)
      "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & Hla & %Hlok & %Hrt &
         %Hdir & %Hwl0 & %Hpar & #Hdisj) [Hep Harm]]".
    iDestruct "Harm" as "[[Harm _] | Hpend]"; [|iDestruct "Hpend" as "(%Ht0p & _ & _)"; exfalso; exact (Hnz Ht0p)].
    iDestruct "Harm" as "[[%Hin Hfrg] | [%Ht2 Hmk]]"; last first.
    { iLeft. iExact "Hmk". }
    iRight.
    assert (Hfr : fresh_shape d) by exact (ireg_box_fresh d Hin Hnz).
    assert (Hw0 : (wl + wdu + wdt = 0)%nat)
      by exact (ireg_box_w0 d (wl + wdu + wdt) Hin Hnz Hlok).
    iSplitR; [iPureIntro; exact Hfr |].
    iSplitL "Hla".
    { iIntros (fl) "Hfl".
      iDestruct (link_wsum_ge with "Hla Hfl") as %Hge.
      iPureIntro. lia. }
    iIntros (inum dn) "%Hk Hdn".
    iApply (dinode_at_excl gi inum d dn with "[Hfrg] Hdn").
    rewrite /dinode_at Hk. iExact "Hfrg".
  Qed.

  (* THE MOVER-BY-MOVER REFUTATION, from the box's fragment alone.

     Six movers act on a region slot.  At a box, five of them are refuted
     and the sixth is the withdraw:

       [ireg_claim_au]      premise [di_type (ds !!! islot inum) = 0], and
                            [ireg_couple] pins that record to the box's own
                            -- refuted by the FIRST conjunct below;
       [ireg_write_au]      \
       [ireg_write_link]     >  each takes [dinode_at gi inum dn] --
       [ireg_write_unlink]  /   refuted by the SECOND;
       [ireg_free_au]       likewise, and this is the free-requires-fill
                            chain's model-level form (see the header);
       [ireg_withdraw]      gated on [imark gi z] ALONE.  NOT refutable:
                            the marker is outside the region at a box and
                            the region is name-blind about who holds it.
                            That is T2, and T2 is the axiom.

     So a claim box is exited by [ireg_withdraw] and by nothing else -- and
     [imark_excl] makes that exit unique, which is the sharpest true form
     of "the first fill picks the fragment up". *)
  Lemma ireg_claim_box_freeze (gi : gname) (z : Z) (d : dinode)
      (inum : bv 32) :
    bv_unsigned inum = z ->
    fresh_shape d ->
    z ↪[gi] d -∗
      ⌜bv_unsigned (di_type d) <> 0⌝
      ∗ (∀ dn : dinode, dinode_at gi inum dn -∗ False).
  Proof.
    intros Hk Hfr. iIntros "Hfrg".
    iSplitR; [iPureIntro; exact (proj1 Hfr) |].
    iIntros (dn) "Hdn".
    iApply (dinode_at_excl gi inum d dn with "[Hfrg] Hdn").
    rewrite /dinode_at Hk. iExact "Hfrg".
  Qed.

  (* NO PAYLOAD NAMES A BOX -- section 16.4's exhaustiveness argument,
     discharged WITHOUT the itable.

     [IcacheEscrow.ipool_alloc] and [IcacheEscrow.ic_loaded] each carry a
     [dinode_at gi inum _], so at a claim box neither can exist at that
     inum: no pool bundle holds it, no cache entry is LOADED at it, and
     therefore every [ilock] that reaches it must take the FILL arm.
     Section 16.4 argues this informally as a uniqueness claim about the
     whole itable -- which needs the itable spinlock -- and it is instead a
     one-line ghost consequence of the fragment's exclusivity.

     Stated with [∧] rather than [∗]: the two refutations are a CHOICE, not
     a pair, so one box fragment answers both. *)
  Lemma ireg_box_no_payload (gfs : fs_names) (gi : gname) (cov : gset Z)
      (logstart : Z) (z : Z) (d : dinode) (inum : mword 32) :
    bv_unsigned inum = z ->
    fresh_shape d ->
    z ↪[gi] d -∗
      (ipool_alloc gfs gi cov logstart inum -∗ False)
      ∧ (∀ (k : nat) (dn : dinode) (bm : blkmap),
           ic_loaded gfs gi cov logstart k inum dn bm -∗ False).
  Proof.
    intros Hk Hfr. iIntros "Hfrg".
    iDestruct (ireg_claim_box_freeze gi z d inum Hk Hfr with "Hfrg")
      as "[_ Hno]".
    iSplit.
    - iIntros "(%dn0 & %bm0 & %data0 & _ & _ & _ & _ & _ & _ & Hdn & _ & _)".
      iApply ("Hno" with "Hdn").
    - iIntros (k dn bm)
        "(%data & _ & _ & _ & _ & _ & _ & Hdn & _ & _ & _ & _)".
      iApply ("Hno" with "Hdn").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  FLANK 1 -- PHASE 1, THE BUFFER HALF                                 *)
  (* ------------------------------------------------------------------ *)

  (* THE HONEST FORMAL CONTENT OF "THE BUFFER SERIALISES THE REGION"
     (fs-fragments.md 7.2.4, phase 1).

     [fsblock] is a HALF of the logged view's [ghost_map] element, so two
     of them are the whole element and a third fraction of any size is
     invalid.  The composition works because the licence is a FRACTION, not
     a handle.

     WHY IT REFUTES A FOREIGN MOVER.  Every region mover opens
     [ireg_inv], hands its caller the region's half of the dinode block,
     and demands it back at NEW bytes -- and a [ghost_map] element is only
     updatable at the full fraction, so the caller must be holding the
     other half.  At the two fupds that matter ([ireg_withdraw]'s, which
     already uses [ghost_map_elem_agree] on exactly this pair, and
     [ireg_free_au]'s) the firing thread therefore holds BOTH halves.  A
     claimant inside its own bread/brelse window holds a half of the same
     block.  Hence: while [ialloc] holds the buffer, NO foreign claim,
     write, link, unlink or free can fire at ANY of that block's sixteen
     inums.

     HOME is [FsBlocks.v], beside [blk_own_excl]; see the file header. *)
  Lemma fsL_block_exclusive (gfs : fs_names) (b : Z)
      (bs bs' bs'' : list (bv 8)) (dq : dfrac) :
    fsblock gfs b bs -∗ fsblock gfs b bs' -∗ b ↪[fs_L gfs]{dq} bs'' -∗ False.
  Proof.
    rewrite /fsblock. iIntros "H1 H2 H3".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H12 _]".
    iDestruct (ghost_map_elem_valid_2 with "H12 H3") as %[Hv _].
    exfalso. rewrite dfrac_op_own Qp.half_half in Hv.
    exact (exclusive_l (DfracOwn 1) dq Hv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  FLANK 2 -- PHASE 3, THE REFERENCE                                   *)
  (* ------------------------------------------------------------------ *)

  (* NO FOREIGN REF-1 WHILE A SECOND REFERENCE LIVES (fs-fragments.md
     7.2.4 phase 3, 7.6.4).

     [iput]'s free path is gated on [ip->ref == 1 && ip->valid &&
     ip->nlink == 0].  The model reads the first conjunct through
     [IcacheInv.iref_lookup], whose third component is REF-1 EXCLUSIVITY:
     at count one the reader's [q] is the WHOLE outstanding share, so no
     other reference exists.  Its refutational form is what create needs:
     two reference fragments at one slot force the count to two
     ([IcacheInv.iref_frag_two_lookup]), so a slot at count ONE cannot
     carry two -- i.e. while create's own reference lives, NO other thread
     can be at REF-1 on that entry, hence none can enter the free.

     create's carrier is [IcacheRef.inode_ref_gen] (and the
     [inode_ref_short_gen] the span's allocated arm returns), whose first
     component is an [iref_frag]; this is stated at [iref_frag] because
     that is the component the authority answers to and because an escrow
     arm's parked reference has only the bare form
     (claude-notes/projects/iput-acquiresleep.md).

     THIS IS GENUINE ABSENCE, not a counter bound, which is why section
     20.15's standing objection (ii) does not apply to it -- and it is also
     why it does not retire the axiom: it speaks only from [iget] onward,
     and the claimant holds no reference at all before that. *)
  Lemma iref_two_not_ref1 (M : gmap nat (Qp * positive)) (k : nat)
      (q1 q2 qt : Qp) :
    M !! k = Some (qt, 1%positive) ->
    itable_half M -∗ iref_frag k q1 -∗ iref_frag k q2 -∗ False.
  Proof.
    intros HM. iIntros "Ha H1 H2".
    iDestruct (iref_frag_two_lookup with "Ha H1 H2")
      as %(qt' & n & HM' & Hn).
    exfalso. rewrite HM in HM'. injection HM' as Hqt Hn1.
    rewrite -Hn1 in Hn. cbn in Hn. lia.
  Qed.

End IregBox.

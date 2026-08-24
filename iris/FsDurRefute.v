(* FsDurRefute.v -- THE TWO WALLS THE HOME-VIEW ACCESSOR RULING RUNS INTO,
   as machine-checked statements rather than as prose.

   Design of record: claude-notes/design/fs-state.md sections 4 and 4.5;
   worklist claude-notes/projects/durable-disk.md, item 3a'.

   The ruling of 2026-08-24 makes durable write permission the CLIENT's
   per-block accessor: for a write of home block [b] with new bytes [bs'],
   the [log_write] AU's payload-step premise is discharged by a basic update
   whose witness opens [P_wf], extracts block [b]'s home-view fragments,
   moves them beside the lent byte authority, and re-establishes [P_wf].
   [P_wf] is the STANDALONE structured predicate -- roughly
   [exists S, top auth * top fragments * fs_state Gamma_D S * an in-transit
   bin] -- with no completeness clause and no index by the committed map.

   Two things in this file are what that design has to answer, and neither
   is a proof difficulty: each is a statement about what a resource can
   possibly say.

   (A) THE CHAIN HAS NO TARGET STATE AT A [bfree].  The accessors are
       composed IN WRITE ORDER and each one has to hand back a whole [P_wf],
       so every intermediate durable byte map must be described by some
       [fs_state Gamma_D S].  It is not: [FsStateBitmap.free_pool] owns
       every block whose bitmap bit reads FREE, while
       [FsStateInode.inl_blk_dom] makes an inode own every block its RECORD
       names -- and xv6 clears the bitmap bit one [log_write] BEFORE it
       writes the record that stops naming the block ([itrunc] calls
       [bfree] on each address and only then runs [iupdate]).  Between the
       two writes the block has two owners, so no [S] describes the disk.
       [fs_state_stale_free_False] is that fact.  Note the asymmetry: the
       ALLOCATING direction is fine -- at [balloc] the bit is set first and
       the block leaves the pool with nothing yet claiming it, which is
       exactly what the in-transit bin absorbs.  The bin cannot help here,
       because the conflict is between two conjuncts of [fs_state] that
       BOTH claim the block; adding an owner is not what is wanted.

   (B) THE ACCESSOR FORCES [P_wf] TO OWN THE BLOCK, AT EVERY INDEX.  The
       AU's premise is quantified over BOTH of the log's parked indices
       ([SpecLogWrite]: [forall D0 Dc, Psi D0 Dc ==* Psi D0 (<[b := bs]> Dc)]),
       so a supplier owes the accessor UNIFORMLY in the durable byte map.
       [dstep_block_forces_ownership] is the block-level reading of
       fs-state.md section 4's [step_forces_the_element]: any [Q] that
       supports the move at one of block [b]'s bytes is incompatible with an
       outside holder of that byte, i.e. [Q] must own block [b] itself.  The
       ruled [P_wf] owns a home block only through whichever conjunct
       happens to hold it, and which conjunct that is depends on the index,
       so no clause of it discharges the obligation uniformly -- which is
       the completeness demand the ruling set out to avoid.

   Nothing here is about [P_wf]'s current body: (A) is a fact about
   [FsState.fs_state] alone and (B) is a fact about an arbitrary [Q]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map.
Require Import BioDefs.
Require Import FsImg.        (* [sb_size] -- the pool's block count       *)
Require Import RiscvPtsto.     (* [fs_dur_names] -- Gamma_D's two gnames   *)
Require Import LogDefs.        (* [fs_dbytes]                              *)
Require Import FsDurBytes.     (* [fs_gamma_D], [blk_owned_dbelems]        *)
Require Import FsState.

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  (A)  THE CHAIN HAS NO TARGET STATE AT A [bfree]                       *)
(* ===================================================================== *)

Section ChainStates.
  Context {Σ : gFunctors}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types S : fs_state_rec.

  (* AN INODE'S OWN BLOCK IS MARKED USED.  This is not a maintained clause
     anywhere -- it is read off the [∗] between [fs_inodes] and the free
     pool, exactly as fs-state.md section 0 says such a fact should be. *)
  Lemma fs_state_inode_block_used Γ (Hex : phi_excl Γ) S i n k bs :
    fss_inodes S !! i = Some n ->
    fn_blk n !! k = Some bs ->
    0 <= fn_naddr n k < sb_size (fss_sb S) ->
    fs_state Γ S -∗ ⌜fn_naddr n k ∈ fss_used S⌝.
  Proof.
    intros Hi Hk Hrng.
    rewrite /fs_state /fs_inodes /free_bitmap /free_bitmap_at.
    iIntros "(_ & Hin & Hbm & Hpool)".
    iDestruct (big_sepM_lookup _ _ i n Hi with "Hin") as "Hio".
    rewrite /inode_owned /inode_phi.
    iDestruct "Hio" as "((_ & Hb & _) & _)".
    iDestruct (big_sepM_lookup _ _ k bs Hk with "Hb") as "Hblk".
    iApply (free_pool_used Γ Hex (sb_size (fss_sb S)) (fss_used S)
              (fn_naddr n k) bs Hrng with "Hpool Hblk").
  Qed.

  (* THE MID-CHAIN STATE OF A [bfree] IS UNSATISFIABLE.  [itrunc] runs
     [bfree(ip->addrs[i])] -- which [log_write]s the BITMAP block with the
     bit cleared -- and only afterwards zeroes [ip->addrs[i]] in memory and
     [iupdate]s the record.  So between those two log writes the committed
     view has the bit clear while the on-disk record still names the block,
     and this says there is no [S] at all for that view: the pool claims the
     block because its bit reads free, the inode claims it because its
     record names it ([inl_blk_dom] is an IFF), and one block cannot have
     two owners.

     The two escapes, and why the ruling closes both:
     - keep the block in the inode and NOT in the pool: impossible, the
       pool's ownership is a FUNCTION of the used set, and the used set is
       pinned by the bitmap block's bytes (the auth agrees with
       [free_bitmap]'s own [blk_owned]);
     - drop inode [i] from [fss_inodes S] altogether, parking its record and
       its blocks in the bin: this is what the fixed per-inum EXISTENCE
       WITNESSES forbid (the durable inode table's domain is the fixed
       geometry), and it would also break the commit's conclusion, which
       says the durable [fs_state] stands at the batch's logged values. *)
  Lemma fs_state_stale_free_False Γ (Hex : phi_excl Γ) S i n k bs :
    fss_inodes S !! i = Some n ->
    fn_blk n !! k = Some bs ->
    0 <= fn_naddr n k < sb_size (fss_sb S) ->
    fn_naddr n k ∉ fss_used S ->
    fs_state Γ S -∗ False.
  Proof.
    intros Hi Hk Hrng Hnu.
    iIntros "HS".
    iDestruct (fs_state_inode_block_used Γ Hex S i n k bs Hi Hk Hrng
                 with "HS") as %Hin.
    iPureIntro. exact (Hnu Hin).
  Qed.

End ChainStates.

(* ===================================================================== *)
(*  (B)  THE ACCESSOR FORCES [P_wf] TO OWN THE BLOCK                      *)
(* ===================================================================== *)

Section AccessorOwnership.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ}.

  (* fs-state.md section 4's [step_forces_the_element], read at ONE BLOCK
     of the durable byte view.  [Q] is arbitrary -- in particular it may be
     any candidate [P_wf], with or without an index, with or without a bin.

     Read it as: whoever can write block [b] durably OWNS block [b]
     durably.  The accessor design does not escape that; what it changes is
     only WHERE the ownership sits (inside [P_wf] rather than in the
     writer's hand).  So a supplier owes "[P_wf] owns block [b]" at every
     index the AU quantifies over, and the ruled [P_wf] -- which owns a
     home block through whichever of [fs_state]'s conjuncts happens to hold
     it -- has no clause that says so. *)
  Lemma dstep_block_forces_ownership (g : gname) (Γd : fs_dur_names)
      (Q : iProp Σ) (D : gmap Z (list (bv 8)))
      (b : Z) (bs bs' : list (bv 8)) (k : nat) (v v' : bv 8) :
    dbytes_ok D ->
    D !! b = Some bs ->
    (length bs' <= BSIZE)%nat ->
    bs !! k = Some v ->
    bs' !! k = Some v' ->
    v <> v' ->
    (ghost_map_auth g 1 (fs_dbytes D) -∗ Q ==∗
       ghost_map_auth g 1 (fs_dbytes (<[b := bs']> D)) ∗ Q) -∗
    ghost_map_auth g 1 (fs_dbytes D) -∗
    blk_owned (fs_gamma_D g Γd) b bs -∗
    Q ==∗ False.
  Proof.
    intros Hok HbD Hlen' Hk Hk' Hne.
    iIntros "Hstep Ha Hblk HQ".
    (* the element of block [b] at offset [k], out of the block's run *)
    iAssert ((b * Z.of_nat BSIZE + Z.of_nat k) ↪[g] v)%I with "[Hblk]"
      as "Hel".
    { rewrite /blk_owned /byte_range /fs_gamma_D. cbn [fsΦ].
      iDestruct "Hblk" as "[_ Hrun]".
      iDestruct (big_sepL_lookup _ _ k v Hk with "Hrun") as "Hel".
      assert (Hz : b * BSIZE_z + 0 + Z.of_nat k
                   = b * Z.of_nat BSIZE + Z.of_nat k).
      { rewrite dbytes_stride. change BSIZE_z with 1024. lia. }
      rewrite Hz. iExact "Hel". }
    (* what the step's TARGET map says at that address *)
    assert (Hok' : dbytes_ok (<[b := bs']> D))
      by exact (dbytes_ok_insert_2 D b bs' Hok Hlen').
    assert (Hnew : fs_dbytes (<[b := bs']> D)
                     !! (b * Z.of_nat BSIZE + Z.of_nat k) = Some v')
      by exact (fs_dbytes_lookup (<[b := bs']> D) b bs' k v' Hok'
                  (lookup_insert _ _ _) Hk').
    iMod ("Hstep" with "Ha HQ") as "[Ha _]".
    iDestruct (ghost_map_lookup with "Ha Hel") as %Hlk.
    rewrite Hnew in Hlk. iPureIntro. congruence.
  Qed.

End AccessorOwnership.

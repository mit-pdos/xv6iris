(* FsAbsSeam.v -- LANE A ITEM (iii): THE HOP SEAM, PROVEN WHERE BOTH GHOSTS
   LIVE -- AND THE ONE RESOURCE THE LANDED FIRE DOES NOT LEND.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A, item (iii)
   ("the dview retirement").  Design of record:
   claude-notes/design/fs-syscall-specs.md v3.

   THE ASK.  [FsAbs]'s pinned walk ([apn_walk]) is stated at an ABSTRACTED
   lend [F] and needs one law of it -- what the walk lends at [d] agrees with
   what a client holds at [d].  The landed ghost-trace namei
   ([SpecNameiTr.nx_hop], proven by [ProofNamexTr]) fires each hop by lending
   [DirViewG.dv_half d dqv ents], and [nx_hop] IS [FsAbs.ax_hop dv_half] on
   the nose.  So the whole of item (iii) is: can that law be discharged at
   [F := dv_half], with the client's carrier being [FsAbs.nview] (a reading of
   [FsState.top_frag_q])?

   WHAT IS IN THIS FILE, AND WHAT IT SETTLES.

   1. THE TIE IS PURE, AND IT IS ALREADY LANDED.  Every payload arm carries
      [dv_ride z (dv_of dn data)] and [top_frag ... (era_node dn bm data)]
      SIDE BY SIDE at the same [(dn, bm, data)] -- [IcacheEscrow.ic_loaded]
      (via [ic_loaded_flat_body]), [ic_rd_arm], [ipool_alloc] -- and
      [FsStateEra.dir_entries_era_node] says the two readings are ONE
      function: [dv_of_dir_entries] below.  Nothing had to be invented and
      no landed contract moved.

   2. THE LAW [lend_agrees] ASKS FOR IS THE WRONG ONE.  It concludes
      [an_node a = ADir ents] -- i.e. the lend must prove the pinned node is
      a DIRECTORY -- and no payload can: [dv_half] rides a FILE too, where
      [dv_of] is determined garbage (DirViewG's header) while [dir_entries]
      is the empty map.  [FsAbs.lend_reads] is the honest law (IF the pinned
      node reads as a directory THEN its entry map is the lent one), the walk
      supplies the directory-ness itself out of [arun], and [FsAbs]'s
      section 4a' re-proves the package at it.  [dv_top_seam] below is that
      law, discharged from the two payload conjuncts at ANY pair of shares.

   3. A CLIENT CANNOT HOLD [nview] AT ALL TODAY -- and that, not the tie, is
      what blocks item (iii).  [ic_loaded] and [ipool_alloc] carry the era
      leg at [DfracOwn 1], hence [top_frag] WHOLE, so an [FsAbs.apn_pin]
      against a live inum is refuted outright ([ic_loaded_nview_excl],
      [ipool_alloc_nview_excl], [apn_pin_loaded_excl]).  The one arm that
      sheds is the READ arm ([ic_rd_arm], residue 3/4, the read-locking
      [ilock]'s quarter being the client's) -- and there the law IS
      discharged: [dv_lend_arm_reads] proves [lend_reads] for a concrete
      lend, and [apn_walk_arm] is the pinned-walk package fired at it.  That
      is a real instantiation of section 3's functional corollary at a
      [top_frag]-agreeing lend, which is what item (iii) asked for.  And the
      pin is satisfiable at that arm and only there: [inode_rd_era_nview]
      says a read-locking [ilock]'s withdrawn quarter IS an [nview] share.

   4. WHAT IS THEREFORE STILL MISSING, precisely: namei's fire lends
      [dv_half] ALONE.  [ProofNamexTr]'s fire point holds the arm's contents
      ([Hdview]) and the era fragment ([Hfview]'s second conjunct, since
      durable-disk 2b-inode-3) at that instant, but [nx_hop]'s statement --
      which R10 freezes -- passes only the first through the caller's fupd.
      A client-side hop therefore receives nothing about the top map, and
      cannot receive it: namex's [ilock] takes the WRITE arm, so not even the
      read arm's 3/4 residue is in the escrow to be opened.  Closing item
      (iii) needs ONE of:
        (a) a producer of a client-held [top_frag_q] share that survives a
            write-arm checkout -- i.e. [ic_loaded]/[ipool_alloc] carrying the
            leg at 3/4 with a client's quarter outstanding.  Note what that
            costs: a share BLOCKS every retag ([InodeRegion.ireg_top_retag]
            needs the whole element), so such a lend must be CANCELLABLE, and
            a cancellable pin is exactly the [DirViewLend] machinery the
            column was to retire -- and exactly the divergence arm v3 ruled
            out.  This is a payload decision, not a spec-layer one.
        (b) a second walk that lends the era fragment beside the contents
            (a new Spec/Proof/Link triple over [ProofNamexTr]'s 4990 lines).

   BINDERS.  [IcacheEscrow]'s own list, verbatim: the BUNDLE [xv6G] and never
   a member (durable-notes, "ONE BUNDLE PER GHOST CLASS" -- [icacheG],
   [fsTopG] and [fsLinkG] are all members, and [FsAbs]'s own lemmas take them
   from it).  [FsAbs] is REQUIRED LAST so its [Require Export FsState] is the
   one that wins on the [FsState*] stack's shadowed names. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.      (* [riscvGS]                                  *)
Require Import DinodeEnc.       (* [dinode], [di_type], [di_size]             *)
Require Import DirView.         (* [T_DIR_z], [dir_nrec]                      *)
Require Import FsTree.          (* [fname], [dir_view]                        *)
Require Import BioDefs.
Require Import InodeInv.        (* [blkmap]                                   *)
Require Import InodeLock.       (* [inode_ok]                                 *)
Require Import IrefSlots.       (* [irefslotG]                                *)
Require Import FsBlocks.        (* [fs_names]                                 *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the LIVE Gamma               *)
Require Import FsStateEra.      (* [era_node], [dir_entries_era_node]         *)
Require Import IcacheRef.       (* [icfg]                                     *)
Require Import DirViewLend.     (* [dv_ride]                                  *)
Require Import IcacheEscrow.    (* Require Export's DirViewG; the three arms  *)
Require Import Xv6G.            (* the bundle                                 *)
Require Import FsAbs.           (* LAST: [nview], [abs_of], [lend_reads]      *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE HALF: [dv_of] IS [dir_entries], ON A PAYLOAD NODE        *)
(* ===================================================================== *)

(* [FsStateEra.dir_entries_era_node] read at the [DirViewG] spelling: the two
   side conditions are [inode_ok] conjuncts, so every payload arm has them in
   the same [Hiok] its other clauses come out of, and the directory guard is
   the one the walk has already tested. *)
Lemma dv_of_dir_entries (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  dir_entries (era_node dn bm data) = dv_of dn data.
Proof.
  intros (_ & _ & _ & _ & Hsz & Hh & _) Hd.
  rewrite /fn_is_dir /fn_type era_node_rec in Hd.
  by rewrite (dir_entries_era_node dn bm data Hh Hsz) Hd.
Qed.

(* ...and the same fact as the ABSTRACT NODE's arm, which is the form the
   lend law's conclusion is stated in. *)
Lemma abs_of_era_dir (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  an_node (abs_of (era_node dn bm data)) = ADir (dv_of dn data).
Proof.
  intros Hok Hd.
  by rewrite (abs_of_dir _ Hd) (dv_of_dir_entries cov logstart dn bm data Hok Hd).
Qed.

Section FsAbsSeam.
  (* [IcacheEscrow]'s binder list, verbatim (header). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

  (* =================================================================== *)
  (*  2.  THE SEAM: the two payload conjuncts against a lent [dv_half]    *)
  (*      and a client-held [nview]                                       *)
  (* =================================================================== *)

  (* The shares are ARBITRARY on both ghosts ([dqp] is what the arm keeps of
     the contents, [dqt] what it keeps of the era fragment), so this one
     statement serves every arm: the loaded arm at (1, 1), the read arm at
     (1, 3/4), and any future shed.  Agreement on each ghost separately is
     all it uses; the bridge between them is section 1. *)
  Lemma dv_top_seam (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (inum : mword 32) (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (dqp dqt dq : dfrac) (q : Qp)
      (ents e : gmap fname Z) (a : anode) :
    inode_ok cov logstart dn bm data ->
    dv_half (bv_unsigned inum) dqp (dv_of dn data) -∗
    top_frag_q (fs_gamma_L γfs) dqt (bv_unsigned inum) (era_node dn bm data) -∗
    dv_half (bv_unsigned inum) dq ents -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗
    ⌜an_node a = ADir e -> e = ents⌝.
  Proof.
    intros Hok. iIntros "Hdvp Htp Hdv Hn".
    iDestruct (dv_agree with "Hdvp Hdv") as %<-.
    iDestruct (nview_frag with "Hn") as (n) "[Hnf %Han]".
    iDestruct (top_frag_q_agree with "Htp Hnf") as %<-.
    iPureIntro. intros He. rewrite -Han in He.
    destruct (abs_of_dir_inv _ _ He) as [Hdir ->].
    exact (dv_of_dir_entries cov logstart dn bm data Hok Hdir).
  Qed.

  (* =================================================================== *)
  (*  3.  THE ARM WHERE A SHARE IS LEGITIMATELY OUTSTANDING               *)
  (* =================================================================== *)

  (* THE LEND, AS A CLIENT WOULD MEET IT: the read arm's residue beside the
     lent contents.  It is [dv_half] with the arm carried along -- which is
     precisely the resource [SpecNameiTr.nx_hop] does NOT pass through the
     caller's fupd (header, point 4). *)
  Definition dv_lend_arm (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (d : Z) (dq : dfrac) (ents : gmap fname Z) : iProp Σ :=
    (∃ inum : mword 32,
       ⌜bv_unsigned inum = d⌝ ∗
       ic_rd_arm γfs γi cov logstart inum ∗ dv_half d dq ents)%I.

  Lemma dv_lend_arm_reads (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) :
    lend_reads (fs_gamma_L γfs) (dv_lend_arm γfs γi cov logstart).
  Proof.
    intros d dq ents q a e. rewrite /dv_lend_arm /ic_rd_arm.
    iIntros "HF Hn". iDestruct "HF" as (inum Hd) "[Harm Hdv]". subst d.
    iDestruct "Harm" as (dn bm data) "(%Hok & _ & _ & _ & _ & Hleg & Hride & _)".
    iDestruct (ic_inode_leg_open with "Hleg") as "[_ Hown]".
    iDestruct (inode_owned_era_to_q with "Hown") as "(_ & _ & _ & Htp)".
    iAssert (∃ dqp, dv_half (bv_unsigned inum) dqp (dv_of dn data))%I
      with "[Hride]" as (dqp) "Hdvp".
    { rewrite /dv_ride. iDestruct "Hride" as "[H | [H _]]";
        [iExists (DfracOwn 1) | iExists (DfracOwn (3/4))]; iExact "H". }
    iDestruct (dv_top_seam γfs cov logstart inum dn bm data dqp
                 (DfracOwn (3/4)) dq q ents e a Hok with "Hdvp Htp Hdv Hn")
      as %Hres.
    by iPureIntro.
  Qed.

  (* THE ONE PRODUCER OF A CLIENT-HELD [nview] IN THE LANDED TREE, and it is
     the other half of the read arm: what a read-locking [ilock] withdraws
     ([IcacheEscrow.ic_rd_held] carries [inode_rd_era] at a quarter) IS a
     carrier share, on the nose.  So [apn_pin] is satisfiable -- for an inum
     the client HAS READ-LOCKED, and for no other.  The byte legs come back
     beside it because a read-locker needs them to call [readi]. *)
  Lemma inode_rd_era_nview (γfs : fs_names) (q : Qp) (inum : mword 32)
      (n : fs_node) :
    inode_rd_era γfs (DfracOwn q) inum n -∗
      inode_dat_q (fs_gamma_L γfs) (DfracOwn q) n
      ∗ nview (fs_gamma_L γfs) q (bv_unsigned inum) (abs_of n).
  Proof.
    rewrite /inode_rd_era. iIntros "[$ Ht]". by iApply nview_of_frag.
  Qed.

  (* ...AND THE PACKAGE, FIRED AT IT.  This is [FsAbs.apn_walk_rd] at a
     CONCRETE lend whose agreement law is a theorem about the landed payload:
     a client that holds an [nview] share of every directory on the path gets
     the cursor at the root, the hop family the trace contract asks for, and
     the walk's answer as [apath_at] -- with no miss arm and no divergence
     arm.  Section 3's functional corollary, at the campaign's carrier. *)
  Lemma apn_walk_arm (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (q : Qp) (av : aview) (root : Z) (ps : list fname)
      (ds : list Z) :
    arun av root ps ds ->
    apn_pins (fs_gamma_L γfs) q av ds ps 0%nat -∗
      apn_P (fs_gamma_L γfs) q av ds ps 0%nat root
      ∗ ax_hops_from (dv_lend_arm γfs γi cov logstart)
          (apn_P (fs_gamma_L γfs) q av ds ps) apn_Pmiss ps 0%nat
      ∗ (∀ iL : Z, apn_P (fs_gamma_L γfs) q av ds ps (length ps) iL -∗
                     ⌜apath_at av root ps = Some iL⌝).
  Proof.
    intros Hr.
    iApply (apn_walk_rd (fs_gamma_L γfs) q av
              (dv_lend_arm γfs γi cov logstart) root ps ds
              (dv_lend_arm_reads γfs γi cov logstart) Hr).
  Qed.

  (* =================================================================== *)
  (*  4.  ...AND WHY THE WRITE ARM CANNOT BE THE ONE                      *)
  (* =================================================================== *)

  (* THE REFUTATION.  [ic_loaded] carries the era leg at [DfracOwn 1], so it
     carries [top_frag] WHOLE; a client-held [nview] share of that inum is
     not merely unavailable, it is inconsistent.  This is what stops the
     package above from being instantiated against namei's own fire, whose
     directory is checked out on the WRITE arm at the fire instant. *)
  Lemma ic_loaded_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (a : anode) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    iIntros "Hl Hn".
    iDestruct (ic_loaded_open with "Hl") as (data)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* ...and the same at the POOL row, which is where an allocated inum's
     element parks when no cache slot holds it -- so the refutation covers
     every allocated inum, cached or not. *)
  Lemma ipool_alloc_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (q : Qp) (a : anode) :
    ipool_alloc γfs γi cov logstart inum -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    rewrite /ipool_alloc. iIntros "Hp Hn".
    iDestruct "Hp" as (dn0 bm0 data0) "(_ & _ & _ & _ & _ & Hleg & _ & _)".
    iDestruct (ic_inode_leg_open with "Hleg") as "[_ Hown]".
    iDestruct (inode_owned_era_to_q with "Hown") as "(_ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* the same statement in the walk package's own vocabulary: a PIN cannot be
     held against a loaded payload *)
  Lemma apn_pin_loaded_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (av : aview) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    apn_pin (fs_gamma_L γfs) q av (bv_unsigned inum) -∗ False.
  Proof.
    iIntros "Hl Hp". rewrite /apn_pin. iDestruct "Hp" as (a) "[_ Hn]".
    iApply (ic_loaded_nview_excl with "Hl Hn").
  Qed.

End FsAbsSeam.

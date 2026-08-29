(* FsAbsCreateFire.v -- the create AU's SUCCESS FIRE AT A NON-DIRECTORY
   CHILD, and the [T_FILE] row reading that instantiates it.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the T_FILE
   create-AU carry).  A NEW LEAF rather than an append to
   [FsAbsMknodFire.v], for the mirror's reason the campaign's other leaves
   record ([FsAbsNpar], [FsAbsPins], [FsAbsStart], [FsAbsOpenFire]): the
   build mirror forbids touching a tracked file.  Fuse the fire leaves when
   one of them is next edited.

   ==== WHY THIS FILE EXISTS ============================================

   [FsAbsMknodFire.mkf_acre_fire] is PINNED at [ADev ma mi] in exactly one
   place: it discharges the delta's collapse with
   [SpecSysMknodAU.delta_create_dev], the "under [cre_pre] with a DEVICE
   child, the fused delta IS the one-row parent insert" lemma.  Reading
   that lemma's proof shows the device-ness is not used -- what is used is
   that the child is NOT A DIRECTORY, which is what makes
   [SpecSysMknodAU.acre_bump] zero (so the parent's count does not move)
   and what makes [cre_pre_ne] separate parent from child (so the child's
   insert is the identity on its already-minted row).

   So the two lemmas below are the [ADev]-free restatements:

     [caf_delta_create_nondir]  -- [delta_create_dev] at any non-[ADir] [c]
     [caf_acre_fire]            -- [mkf_acre_fire] at any non-[ADir] [c]

   and [caf_child_file] is the [T_FILE] instance of the minted child's row
   ([FsAbsMknodFire.mkf_child_dev]'s twin): [SpecCreate.create_made T_FILE
   major minor] reads as [AFile []] at nlink 1, because that record's size
   is zero and [fn_file_bytes] of a zero-size node is [file_bytes _ 0 = []]
   -- the same arithmetic [FsAbsOpenFire.opf_trunc_bytes] does at itrunc's
   own zeroing.

   R10: neither [FsAbsMknodFire] nor [SpecSysMknodAU] moves.  The device
   fire keeps its own name and its own proof; a caller that wants the
   device instance is not asked to route through the general form.

   BINDERS: [FsAbsMknodFire]'s section list VERBATIM (which is
   [SpecSysMknodAU]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve
   only through its fields (SpecCreate's header: a standalone [icfg] beside
   [fileG] gives two instance paths and the propositions print identically
   while failing to unify). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsTree.           (* [fname], [file_bytes]                   *)
Require Import PathElems.
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import InodeInv.
Require Import InodeLock.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheEscrow.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecCreate.       (* [create_made], [T_FILE]                 *)
Require Import SpecSysMknodAU.   (* [delta_create], [cre_pre], [acre_bump]  *)
Require Import FsAbsEra.
Require Import FsAbsMknodFire.   (* [acre_commit_at], [mkf_abs_of_dir]      *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import       *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA'S COLLAPSE AT A NON-DIRECTORY CHILD (pure)              *)
(* ===================================================================== *)

(* [acre_bump] is zero at everything but a directory: the parent's count
   moves only when the child's ".." takes a token. *)
Lemma caf_acre_bump_nondir (c : absnode) :
  (forall e, c <> ADir e) -> acre_bump c = 0%nat.
Proof.
  intros Hc. destruct c as [bs | ents | ma mi]; [reflexivity | | reflexivity].
  exfalso. exact (Hc ents eq_refl).
Qed.

(* [SpecSysMknodAU.delta_create_dev] with the device-ness dropped: under
   [cre_pre] at a NON-DIRECTORY child the fused delta IS the one-row parent
   insert.  The child's own insert is the identity on the row [cre_pre]'s
   third conjunct already observes, and [cre_pre_ne] is what keeps the two
   inserts from being at the same key. *)
Lemma caf_delta_create_nondir (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  (forall e, c <> ADir e) ->
  cre_pre av d nm ents nl i c ->
  delta_create d nm i c av
  = <[d := MkAnode (ADir (<[nm := i]> ents)) nl]> av.
Proof.
  intros Hc Hp.
  assert (Hne : d <> i) by exact (cre_pre_ne av d nm ents nl i c Hp Hc).
  destruct Hp as (Hd & Hnm & Hi).
  rewrite /delta_create Hd /= (caf_acre_bump_nondir c Hc) Nat.add_0_r.
  rewrite (insert_commute _ i d); [| congruence].
  by rewrite (insert_id av i (MkAnode c 1%nat) Hi).
Qed.

(* ===================================================================== *)
(*  2.  THE MINTED CHILD'S ROW AT [T_FILE]                                *)
(* ===================================================================== *)

(* [SpecSysMknodAU.abs_of_create_dev]'s twin.  Three readings, each off
   [create_made]'s own fields: the type is not [T_DIR_z] (so the row is not
   an [ADir]) and IS [T_FILE_z] (so it is an [AFile]); the size is zero, so
   the byte list is [file_bytes _ 0 = []]; the count is one. *)
Lemma caf_abs_of_create_file (n : fs_node) (major minor : mword 16) :
  fn_rec n = create_made T_FILE major minor ->
  abs_of n = MkAnode (AFile []) 1%nat.
Proof.
  intros Hr.
  assert (Hnd : fn_is_dir n = false).
  { rewrite /fn_is_dir /fn_type Hr. by apply bool_decide_eq_false_2. }
  assert (Hfl : fn_type n = FsImg.T_FILE_z)
    by (rewrite /fn_type Hr; reflexivity).
  assert (Hbytes : fn_file_bytes n = []).
  { rewrite /fn_file_bytes /fn_size Hr. reflexivity. }
  assert (Hnl : fn_nlink n = 1%nat)
    by (rewrite /fn_nlink Hr; reflexivity).
  rewrite /abs_of Hnl. f_equal.
  change (abs_node n) with (an_node (abs_of n)).
  by rewrite (abs_of_file n Hnd Hfl) Hbytes.
Qed.

(* ...and at the era node, which is the shape a walk holds
   ([FsAbsMknodFire.mkf_child_dev]'s spelling). *)
Lemma caf_child_file (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (major minor : mword 16) :
  dn = create_made T_FILE major minor ->
  abs_of (era_node dn bm data) = MkAnode (AFile []) 1%nat.
Proof.
  intros ->. apply (caf_abs_of_create_file _ major minor).
  by rewrite era_node_rec.
Qed.

Section CreateFire.
  (* [FsAbsMknodFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  3.  THE SUCCESS FIRE AT A NON-DIRECTORY CHILD                       *)
  (* =================================================================== *)

  (* [FsAbsMknodFire.mkf_acre_fire] with [ADev ma mi] replaced by an
     arbitrary non-[ADir] [c]: same premises, same [ghost_map_update], same
     one [ftopN] critical section with the caller's two phases on either
     side of it, same payout.  The device instance is [mkf_acre_fire]
     itself and is NOT rerouted through this (R10). *)
  Lemma caf_acre_fire (γfs : fs_names) (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ⊆ E ->
    (forall e, c <> ADir e) ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode c 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) ∅ c Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i c⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hc Hloc Hdir Hnone Habsp' Habsc.
    iIntros "#Hi Hcm Hfp Hfc".
    (* the same re-spelling [mkf_acre_fire] does, and for the same reason:
       [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot
       solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hfc") as %Hlkc.
    assert (Hpre : cre_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) i c).
    { rewrite /cre_pre. split_and!.
      - by rewrite (abs_view_lookup I d np Hlkp) (mkf_abs_of_dir np Hdir).
      - exact Hnone.
      - by rewrite (abs_view_lookup I i nc Hlkc) Habsc. }
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_create d nm i c (abs_view I)).
    { rewrite (abs_view_insert I d np') Habsp'.
      by rewrite (caf_delta_create_nondir (abs_view I) d nm (dir_entries np)
                    (fn_nlink np) i c Hc Hpre). }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I d i nm (dir_entries np) (fn_nlink np)
            with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update np' with "Hta Hfp") as "[Hta Hfp]".
    iMod ("Hph2" $! (<[d := np']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = d)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hfp Hfc". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [AFile []] instance, which is the one the T_FILE create-AU fires:
     a file child is never an [ADir]. *)
  Lemma caf_acre_fire_file (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = None ->
    abs_of np' = MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np) ->
    abs_of nc = MkAnode (AFile []) 1%nat ->
    ftop_inv γfs -∗
    acre_commit_at (fs_gamma_L γfs) ∅ (AFile []) Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i (AFile [])⌝
          ∗ Φ av d nm i.
  Proof.
    intros HE Hloc Hdir Hnone Habsp' Habsc.
    iIntros "Hi Hcm Hfp Hfc".
    iApply (caf_acre_fire γfs E (AFile []) Φ d i nm dqc np np' nc HE
              ltac:(intros e Hc; discriminate Hc)
              Hloc Hdir Hnone Habsp' Habsc with "Hi Hcm Hfp Hfc").
  Qed.

End CreateFire.

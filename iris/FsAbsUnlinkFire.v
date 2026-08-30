(* FsAbsUnlinkFire.v -- THE UNLINK AU's FOUR FIRE POINTS, discharged
   against the invariant, plus the reading bridges [SpecSysUnlinkAU]'s
   header owes its prover (items 1 and 2).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the unlink
   AU prover).  A NEW LEAF rather than an append to [FsAbsMknodFire.v] /
   [FsStateEra.v], for the mirror's reason every other campaign leaf
   records ([FsAbsNpar], [FsAbsPins], [FsAbsCreateFire]): the build mirror
   forbids touching a tracked file.  Fuse when those are next edited.

   ==== THE FOUR FIRES ==================================================

   The mold is [FsAbsMknodFire.mkf_acre_fire] / [mkf_dlookup_fire]: one
   step each, [ftopN] opened and closed inside, the row read off the
   FIRING FUNCTION'S OWN era fragment (sys_unlink holds [dp]'s from W2's
   ilock and [ip]'s from W3's, both inside [IcacheEscrow.ic_loaded], so
   no seam is needed at any of the four instants).

     [uf_uent_fire]  INSTANT 1, fused with the PARENT-row retag.  Replaces
        the [InodeRegion.ireg_top_retag] the landed walk performs at the
        zeroing (W5-FILE) resp. after [iupdate(dp)] (W5-DIR): same
        premise ([inode_local] of the new record), same payout (the moved
        fragment), plus the caller's two phases inside the one critical
        section.  It reads the TARGET's row too -- [unl_pre]'s last three
        conjuncts are about [ip] -- off a SECOND, read-only fragment,
        which the walk has held since W3.  That is what makes the two
        instants read as one delta later ([delta_unlink_split]).
     [uf_utgt_fire]  INSTANT 2, fused with the TARGET-row retag after
        [wp_iupdate_unlink].  One fragment, one phase pair, the count
        lowered by one.
     [uf_dmiss_fire]  the MISS observation ([dmiss_commit_at]), read-only,
        at dirlookup's miss under the parent's lock.
     [uf_dex_fire]  the FOUND observation ([FsAbsMknodFire.dlookup_commit_at],
        reused) at the isdirempty refusal, where BOTH locks are held --
        so the ONE [av] the fire returns carries the parent's row, the
        entry, the target's dir row AND its non-dots witness, which is
        exactly arm (iii-c)'s shape.

   NOTHING ABOUT THE LINK RA CROSSES THIS FILE.  [FsStateEra.ent_toks_unlink],
   [IregLinkNz.ireg_tok_nz] and [SpecIupdate.wp_iupdate_unlink] stay where
   the landed walk already calls them; the fires sit BESIDE those steps and
   take no token, exactly as the statement's item 4 rules ("the ledger
   stays below the abstraction").

   ==== THE READING BRIDGES =============================================

   [uf_parent_row] is the [abs_of] wrap of the LANDED
   [FsStateEra.dir_entries_unlink_eq] (the delete-side half): a zeroed
   record keeps its type, so the row stays an [ADir], and its count moves
   only by the dir arm's own [dp->nlink--].  [uf_nlink_row] is the
   count-lowered bridge at both iupdates -- ProofSysUnlink's [su_setnl_*]
   congruences restated ABSTRACTLY, over "a record that differs in
   [di_nlink] alone", because [su_setnl] itself lives in a proof file and
   a leaf may not depend on one.

   [uf_dots_only] and [uf_not_dots_only] are THE ISDIREMPTY BRIDGE, both
   directions.  Forward: the loop's harvest [DirView.dir_dots_only] (every
   live record's name is a dot name) becomes [SpecSysUnlinkAU.dots_only] of
   the entry map, through [FsTree.dir_view_lookup_rec] -- every key of the
   view comes from a live record inside the count.  Backward: ONE live
   record at index >= 2 refutes it, through [DirView.dir_dots_ix] (records
   0 and 1 ARE the dots) and [FsTree.dir_names_unique] (so a third live
   record cannot share their names) and [FsTree.dir_view_live] (so its name
   really is IN the view).  The backward direction is arm (iii-c)'s
   witness and the forward one is [unl_pre]'s last conjunct.

   BINDERS: [SpecSysUnlinkAU]'s section list VERBATIM -- [fileG] is bound
   and [icacheG]/[icfg] resolve only through its fields (SpecCreate's
   header: a standalone [icfg] beside [fileG] gives two instance paths and
   the propositions print identically while failing to unify). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z], [dir_dots_only], [dir_dots_ix] *)
Require Import FsTree.           (* [fname], [dir_view], [dir_names_unique]   *)
Require Import FsBlocks.         (* [fs_names]                               *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                             *)
Require Import BioDefs.          (* [BSIZE]                                  *)
Require Import InodeInv.         (* [blk_holes_zero], [MAXFILE]              *)
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes [SpecSysUnlinkAU]'s section list names, IMPORTED
   rather than inherited ([FsAbsMknodFire]'s banner: [Require Import] does
   not re-import a required file's own imports, and an unbound [fileG] in a
   [`{! ...}] binder is silently generalised into a variable). *)
Require Import FdSlots.          (* [fdslotG]                                *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]    *)
Require Import ProcAvail.        (* [pavG]                                   *)
Require Import FsStateInode.     (* [fn_*], [dir_entries]                    *)
Require Import FsStateEra.       (* [era_node], [dir_entries_era_node]       *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]      *)
Require Import Xv6G.
Require Import SpecSysMknodAU.   (* [abs_view_insert]                        *)
Require Import FsAbsMknodFire.   (* [dlookup_commit_at], [mkf_abs_of_dir]    *)
Require Import SpecSysUnlinkAU.  (* the statement this file's fires serve    *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                  *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE READING BRIDGES                                          *)
(* ===================================================================== *)

(* ---- ITEM 2a: THE PARENT'S ROW AT THE ZEROING ------------------------ *)

(* The real half -- [dir_entries] of the zeroed record IS [delete nm] of the
   old one -- is ALREADY LANDED as [FsStateEra.dir_entries_unlink_eq], so
   this lemma takes that equation as a premise and does the [abs_of]
   arithmetic around it.  Generic over nodes: on the FILE arm [dec] is 0
   and the count does not move at all; on the DIR arm [dec] is 1 and the
   count is the one [dp->nlink--] stored. *)
Lemma uf_parent_row (n n' : fs_node) (nm : fname) (dec : nat) :
  fn_is_dir n' = true ->
  (fn_nlink n' = fn_nlink n - dec)%nat ->
  dir_entries n' = delete nm (dir_entries n) ->
  abs_of n'
  = MkAnode (ADir (delete nm (dir_entries n))) (fn_nlink n - dec)%nat.
Proof.
  intros Hdir Hnl Hents.
  by rewrite (mkf_abs_of_dir n' Hdir) Hents Hnl.
Qed.

(* ---- ITEM 2b: THE COUNT-LOWERED ROW AT EITHER iupdate ---------------- *)

(* [su_setnl] moves [di_nlink] ALONE, and every field [abs_node] reads --
   the type (hence the arm), the size and the data (hence [dir_entries] and
   [fn_file_bytes]), the device numbers -- rides.  Stated over the five
   field equations rather than over [su_setnl] itself, which lives in a
   proof file. *)
Lemma uf_abs_node_nlink (dn dn' : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  di_type dn' = di_type dn ->
  di_size dn' = di_size dn ->
  di_major dn' = di_major dn ->
  di_minor dn' = di_minor dn ->
  abs_node (era_node dn' bm data) = abs_node (era_node dn bm data).
Proof.
  intros Hty Hsz Hmaj Hmin.
  assert (Hty' : fn_type (era_node dn' bm data)
                 = fn_type (era_node dn bm data))
    by (rewrite /fn_type !era_node_rec Hty //).
  assert (Hsz' : fn_size (era_node dn' bm data)
                 = fn_size (era_node dn bm data))
    by (rewrite /fn_size !era_node_rec Hsz //).
  assert (Hdat : fn_data (era_node dn' bm data)
                 = fn_data (era_node dn bm data)) by reflexivity.
  rewrite /abs_node /fn_is_dir /dir_entries /fn_is_dir /fn_nrec
          /fn_file_bytes /fn_major /fn_minor.
  rewrite Hty' Hsz' Hdat !era_node_rec Hmaj Hmin. reflexivity.
Qed.

Lemma uf_nlink_row (dn dn' : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  di_type dn' = di_type dn ->
  di_size dn' = di_size dn ->
  di_major dn' = di_major dn ->
  di_minor dn' = di_minor dn ->
  (fn_nlink (era_node dn' bm data)
   = fn_nlink (era_node dn bm data) - 1)%nat ->
  abs_of (era_node dn' bm data)
  = MkAnode (an_node (abs_of (era_node dn bm data)))
            (fn_nlink (era_node dn bm data) - 1)%nat.
Proof.
  intros Hty Hsz Hmaj Hmin Hnl.
  rewrite /abs_of /=.
  by rewrite (uf_abs_node_nlink dn dn' bm data Hty Hsz Hmaj Hmin) Hnl.
Qed.

(* ---- ITEM 2c: THE ISDIREMPTY BRIDGE, FORWARD ------------------------- *)

Lemma uf_dots_only (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  blk_holes_zero bm data ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_type dn) = T_DIR_z ->
  dir_dots_only dn data ->
  dots_only (dir_entries (era_node dn bm data)).
Proof.
  intros Hh Hb Hty Hdo nm Hsome.
  rewrite (dir_entries_era_node dn bm data Hh Hb)
          (bool_decide_eq_true_2 _ Hty) in Hsome.
  destruct Hsome as [z Hz].
  destruct (dir_view_lookup_rec _ _ _ _ Hz) as (k & Hk & Hlive & Hnm & _).
  destruct (Hdo k Hk Hlive) as [Hd | Hd].
  - left. rewrite -Hnm /dir_bname Hd. symmetry.
    exact FsStateEra.DOT_dot_name.
  - right. rewrite -Hnm /dir_bname Hd. symmetry.
    exact FsStateEra.DOTDOT_dotdot.
Qed.

(* ---- ITEM 2d: THE ISDIREMPTY BRIDGE, BACKWARD (arm iii-c's witness) --- *)

Lemma uf_not_dots_only (self : Z) (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (k : nat) :
  blk_holes_zero bm data ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_type dn) = T_DIR_z ->
  bv_unsigned (di_nlink dn) <> 0 ->
  dir_dots_ix self dn data ->
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))) ->
  (2 <= k)%nat ->
  (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
  dir_live data k ->
  ~ dots_only (dir_entries (era_node dn bm data)).
Proof.
  intros Hh Hb Hty Hnz Hdix Hu H2k Hk Hlive Hdo.
  destruct (Hdix Hty Hnz)
    as (Hnrec2 & Hlv0 & _ & Hname0 & Hlv1 & Hname1).
  assert (Hents : dir_entries (era_node dn bm data)
                  = dir_view data (dir_nrec (bv_unsigned (di_size dn)))).
  { rewrite (dir_entries_era_node dn bm data Hh Hb)
            (bool_decide_eq_true_2 _ Hty) //. }
  assert (Hlk : dir_view data (dir_nrec (bv_unsigned (di_size dn)))
                  !! dir_bname data k
                = Some (bv_unsigned (dir_inum data k)))
    by exact (dir_view_live data _ k Hu Hk Hlive).
  assert (Hin : is_Some (dir_entries (era_node dn bm data)
                           !! dir_bname data k))
    by (rewrite Hents Hlk; by eexists).
  destruct (Hdo (dir_bname data k) Hin) as [Hc | Hc].
  - assert (Hb0 : dir_bname data 0%nat = dir_bname data k).
    { rewrite Hc /dir_bname Hname0. exact FsStateEra.DOT_dot_name. }
    assert (Hz0 : (0%nat = k)) by (apply (Hu 0%nat k); [lia | lia | done..]).
    lia.
  - assert (Hb1 : dir_bname data 1%nat = dir_bname data k).
    { rewrite Hc /dir_bname Hname1. exact FsStateEra.DOTDOT_dotdot. }
    assert (Hz1 : (1%nat = k)) by (apply (Hu 1%nat k); [lia | lia | done..]).
    lia.
Qed.

(* ===================================================================== *)
(*  2.  THE FOUR FIRE POINTS, [ftopN] OPENED AND CLOSED                   *)
(* ===================================================================== *)

Section UnlinkFire.
  (* [SpecSysUnlinkAU]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The two read-only observations                                *)
  (* ------------------------------------------------------------------ *)

  (* THE MISS, at dirlookup's [None] under the parent's lock.
     [mkf_dlookup_fire]'s shape at the ABSENT entry.  The row comes off the
     firing function's own era fragment, so the fragment goes straight
     back. *)
  Lemma uf_dmiss_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Φ : aview -> Z -> fname -> iProp Σ)
      (d : Z) (nm : fname) (n : fs_node) :
    ↑ftopN ⊆ E ->
    fn_is_dir n = true ->
    dir_entries n !! nm = None ->
    ftop_inv γfs -∗
    dmiss_commit_at (fs_gamma_L γfs) ∅ Φ -∗
    top_frag_q (fs_gamma_L γfs) dq d n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq d n
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))⌝
          ∗ ⌜dir_entries n !! nm = None⌝
          ∗ Φ av d nm.
  Proof.
    intros HE Hdir Hnm. iIntros "#Hi Hcm Hf".
    (* [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot solve
       [γtop ?Γ =?= fs_top γfs], so the fragment is put in the body's own
       spelling before the invariant is opened -- exactly what
       [InodeRegion.ireg_top_retag] does at its own retag. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! d
                   = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))).
    { by rewrite (abs_view_lookup I d n Hlk) (mkf_abs_of_dir n Hdir). }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I d nm (dir_entries n) (fn_nlink n)
            with "[//] [//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* THE FOUND OBSERVATION AT THE ISDIREMPTY REFUSAL.  Both locks are held,
     so ONE [av] carries the parent's row, the entry, the target's dir row
     and its non-dots witness -- arm (iii-c)'s four pure conjuncts at a
     single instant. *)
  Lemma uf_dex_fire (γfs : fs_names) (E : coPset) (dqd dqt : dfrac)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d t : Z) (nm : fname) (nd nt : fs_node) :
    ↑ftopN ⊆ E ->
    fn_is_dir nd = true ->
    dir_entries nd !! nm = Some t ->
    fn_is_dir nt = true ->
    ~ dots_only (dir_entries nt) ->
    ftop_inv γfs -∗
    dlookup_commit_at (fs_gamma_L γfs) ∅ Φ -∗
    top_frag_q (fs_gamma_L γfs) dqd d nd -∗
    top_frag_q (fs_gamma_L γfs) dqt t nt ={E}=∗
      top_frag_q (fs_gamma_L γfs) dqd d nd
      ∗ top_frag_q (fs_gamma_L γfs) dqt t nt
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries nd)) (fn_nlink nd))⌝
          ∗ ⌜dir_entries nd !! nm = Some t⌝
          ∗ ⌜av !! t = Some (MkAnode (ADir (dir_entries nt)) (fn_nlink nt))⌝
          ∗ ⌜~ dots_only (dir_entries nt)⌝
          ∗ Φ av d nm t.
  Proof.
    intros HE Hdird Hnm Hdirt Hne. iIntros "#Hi Hcm Hfd Hft".
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfd") as %Hlkd.
    iDestruct (ghost_map_lookup with "Hta Hft") as %Hlkt.
    assert (Hrowd : abs_view I !! d
                    = Some (MkAnode (ADir (dir_entries nd)) (fn_nlink nd))).
    { by rewrite (abs_view_lookup I d nd Hlkd) (mkf_abs_of_dir nd Hdird). }
    assert (Hrowt : abs_view I !! t
                    = Some (MkAnode (ADir (dir_entries nt)) (fn_nlink nt))).
    { by rewrite (abs_view_lookup I t nt Hlkt) (mkf_abs_of_dir nt Hdirt). }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I d t nm (dir_entries nd) (fn_nlink nd)
            with "[//] [//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hfd Hft". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  INSTANT 1 -- the parent row, fused with its retag             *)
  (* ------------------------------------------------------------------ *)

  (* Replaces [InodeRegion.ireg_top_retag] at the parent: same premise
     ([inode_local] of the flushed record), same payout (the moved
     fragment), plus the caller's two phases on either side of the
     [ghost_map_update] INSIDE the one [ftopN] critical section (the
     statement's "the pair is ONE instant to every other party").

     The TARGET's fragment is only READ -- [unl_pre]'s last three conjuncts
     are about [ip], whose lock the walk has held since W3 -- and comes
     back untouched.  [dec] is [unl_dec] of the target's own node, so the
     FILE arm instantiates it at 0 and the DIR arm at 1. *)
  Lemma uf_uent_fire (γfs : fs_names) (E : coPset) (dqt : dfrac)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d t : Z) (nm : fname) (dec : nat) (np np' nt : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = Some t ->
    nm <> DOT ->
    nm <> DOTDOT ->
    (1 <= fn_nlink np)%nat ->
    (1 <= fn_nlink nt)%nat ->
    (forall es, an_node (abs_of nt) = ADir es -> dots_only es) ->
    unl_dec (an_node (abs_of nt)) = dec ->
    abs_of np'
      = MkAnode (ADir (delete nm (dir_entries np))) (fn_nlink np - dec)%nat ->
    ftop_inv γfs -∗
    uent_commit_at (fs_gamma_L γfs) ∅ Φ -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqt t nt ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqt t nt
      ∗ ∃ av : aview,
          ⌜unl_pre av d nm (dir_entries np) (fn_nlink np) t (abs_of nt)⌝
          ∗ Φ av d nm t.
  Proof.
    intros HE Hloc Hdir Hnm HnD HnDD Hnlp Hnlt Hdots Hdec Habsp'.
    iIntros "#Hi Hcm Hfp Hft".
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hft") as %Hlkt.
    assert (Hrowp : abs_view I !! d
                    = Some (MkAnode (ADir (dir_entries np)) (fn_nlink np))).
    { by rewrite (abs_view_lookup I d np Hlkp) (mkf_abs_of_dir np Hdir). }
    assert (Hrowt : abs_view I !! t = Some (abs_of nt))
      by exact (abs_view_lookup I t nt Hlkt).
    assert (Hpre : unl_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) t (abs_of nt)).
    { rewrite /unl_pre. split_and!.
      - exact Hrowp.
      - exact Hnm.
      - exact HnD.
      - exact HnDD.
      - exact Hnlp.
      - exact Hrowt.
      - exact Hnlt.
      - exact Hdots. }
    (* the parent half collapses to the ONE-ROW insert, and the insert's
       reading is the flushed record's own row *)
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_unl_ent d nm dec (abs_view I)).
    { rewrite (abs_view_insert I d np') Habsp'.
      rewrite /delta_unl_ent Hrowp /=. reflexivity. }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I d t nm (dir_entries np) (fn_nlink np) (abs_of nt)
            with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update np' with "Hta Hfp") as "[Hta Hfp]".
    iMod ("Hph2" $! (<[d := np']> I) with "[%] Hta") as "[Hta HΦ]".
    { by rewrite Hdelta Hdec. }
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = d)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hfp Hft". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  INSTANT 2 -- the target row, fused with its retag             *)
  (* ------------------------------------------------------------------ *)

  (* [wp_iupdate_unlink] has flushed [ip] at its lowered count; this is the
     abstract half of the same move.  The pre-state row it hands back is
     the one the ret-0 arm pins ([av1 !! t = Some a]) -- true because the
     target's fragment has been in the walk's custody since W3, so nothing
     could move it between the two instants. *)
  Lemma uf_utgt_fire (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> iProp Σ) (t : Z) (nt nt' : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local t nt' ->
    (1 <= fn_nlink nt)%nat ->
    abs_of nt' = MkAnode (an_node (abs_of nt)) (fn_nlink nt - 1)%nat ->
    ftop_inv γfs -∗
    utgt_commit_at (fs_gamma_L γfs) ∅ Φ -∗
    top_frag (fs_gamma_L γfs) t nt ={E}=∗
      top_frag (fs_gamma_L γfs) t nt'
      ∗ ∃ av : aview, ⌜av !! t = Some (abs_of nt)⌝ ∗ Φ av t.
  Proof.
    intros HE Hloc Hnl Habs'. iIntros "#Hi Hcm Hf".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! t = Some (abs_of nt))
      by exact (abs_view_lookup I t nt Hlk).
    assert (Hdelta : abs_view (<[t := nt']> I)
                     = delta_unl_tgt t (abs_view I)).
    { rewrite (abs_view_insert I t nt') Habs'.
      rewrite /delta_unl_tgt Hrow. reflexivity. }
    iMod (fupd_mask_subseteq ∅) as "Hcl2"; [set_solver |].
    iMod ("Hcm" $! I t (abs_of nt) with "[//] [%] Hta") as "[Hta Hph2]".
    { exact Hnl. }
    iMod (ghost_map_update nt' with "Hta Hf") as "[Hta Hf]".
    iMod ("Hph2" $! (<[t := nt']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[t := nt']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = t)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

End UnlinkFire.

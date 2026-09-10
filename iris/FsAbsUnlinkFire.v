(* FsAbsUnlinkFire.v -- THE UNLINK AU's FOUR FIRE POINTS, discharged
   against the invariant, plus the reading bridges [SysUnlinkDefs]'s
   header owes its prover (items 1 and 2).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the unlink
   AU prover).  A NEW LEAF rather than an append to [FsAbsMknodFire.v] /
   [FsStateEra.v], for the mirror's reason every other campaign leaf
   records ([FsAbsNpar], [FsAbsPins], [FsAbsCreateFire]): the build mirror
   forbids touching a tracked file.  Fuse when those are next edited.

   ==== THE FOUR FIRES ==================================================

   The mold is [FsAbsMknodFire.caf_acre_fire] / [mkf_dlookup_fire]: one
   step each, [ftopN] opened and closed inside, the row read off the
   FIRING FUNCTION'S OWN era fragment (sys_unlink holds [dp]'s from W2's
   ilock and [ip]'s from W3's, both inside [IcacheEscrow.ic_loaded], so
   no seam is needed at any of the four instants).

     [uf_uent_fire]  INSTANT 1, fused with the PARENT-row retag.  Replaces
        the [InodeRegion.ireg_top_retag_*] the landed walk performs at the
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
   count-lowered bridge at both iupdates -- ProofSysUnlinkPure's [su_setnl_*]
   congruences restated ABSTRACTLY, over "a record that differs in
   [di_nlink] alone", because [su_setnl] itself lives in a proof file and
   a leaf may not depend on one.

   [uf_dots_only] and [uf_not_dots_only] are THE ISDIREMPTY BRIDGE, both
   directions.  Forward: the loop's harvest [DirView.dir_dots_only] (every
   live record's name is a dot name) becomes [SysUnlinkDefs.dots_only] of
   the entry map, through [FsTree.dir_view_lookup_rec] -- every key of the
   view comes from a live record inside the count.  Backward: ONE live
   record at index >= 2 refutes it, through [DirView.dir_dots_ix] (records
   0 and 1 ARE the dots) and [FsTree.dir_names_unique] (so a third live
   record cannot share their names) and [FsTree.dir_view_live] (so its name
   really is IN the view).  The backward direction is arm (iii-c)'s
   witness and the forward one is [unl_pre]'s last conjunct.

   BINDERS: [SysUnlinkDefs]'s section list VERBATIM -- [fileG] is bound
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
(* the three binder classes [SysUnlinkDefs]'s section list names, IMPORTED
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
Require Import FsAbsDelta.   (* [abs_view_insert]                        *)
Require Import FsAbsMknodFire.   (* [dlookup_commit_at], [mkf_abs_of_dir]    *)
Require Import SysUnlinkDefs.  (* the statement this file's fires serve    *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule)                  *)

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
  (fn_nlink n - dec)%nat <> 0%nat ->
  dir_entries n' = delete nm (dir_entries n) ->
  abs_of n'
  = Some (MkAnode (ADir (delete nm (dir_entries n))) (fn_nlink n - dec)%nat).
Proof.
  intros Hdir Hnl Hpos Hents.
  by rewrite (mkf_abs_of_dir n' Hdir ltac:(rewrite Hnl; exact Hpos)) Hents Hnl.
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

(* ...at a TYPED record (E2-V): the type rides, so the lowered node READS
   as the old node's row at the lowered count.  Stated on [abs_row] with
   the type beside it (E2-V2): whether the lowered node still has a VIEW
   row is the count's business -- [uf_utgt_fire] decides it. *)
Lemma uf_nlink_row (dn dn' : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> 0 ->
  di_type dn' = di_type dn ->
  di_size dn' = di_size dn ->
  di_major dn' = di_major dn ->
  di_minor dn' = di_minor dn ->
  (fn_nlink (era_node dn' bm data)
   = fn_nlink (era_node dn bm data) - 1)%nat ->
  fn_type (era_node dn' bm data) <> 0
  /\ abs_row (era_node dn' bm data)
     = MkAnode (an_node (abs_row (era_node dn bm data)))
               (fn_nlink (era_node dn bm data) - 1)%nat.
Proof.
  intros Hnz Hty Hsz Hmaj Hmin Hnl. split.
  - rewrite /fn_type era_node_rec Hty. exact Hnz.
  - rewrite /abs_row /=.
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
  (* [SysUnlinkDefs]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The two read-only observations                                *)
  (* ------------------------------------------------------------------ *)

  (* THE MISS, at dirlookup's [None] under the parent's lock.
     [mkf_dlookup_fire]'s shape at the ABSENT entry.  The row comes off the
     firing function's own era fragment, so the fragment goes straight
     back. *)
  Lemma uf_dmiss_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ))
      (d : Z) (nm : fname) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    fn_is_dir n = true ->
    dir_entries n !! nm = None ->
    ftop_inv γfs -∗
    pf_at (dmiss_commit_at (fs_gamma_L γfs) appE) Fmiss -∗
    top_frag_q (fs_gamma_L γfs) dq d n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq d n
      ∗ ∃ av : aview,
          ⌜arow_at av d (MkAnode (ADir (dir_entries n)) (fn_nlink n))⌝
          ∗ ⌜dir_entries n !! nm = None⌝
          ∗ Fmiss.(pf_recv) av d nm.
  Proof.
    intros HE Hdir Hnm. iIntros "#Hi Hcm Hf".
    (* THE PIECE IS SPENT: the fire eliminates to the AU side. *)
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    (* [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot solve
       [γtop ?Γ =?= fs_top γfs], so the fragment is put in the body's own
       spelling before the invariant is opened -- exactly what
       [InodeRegion.ireg_top_retag_*] does at its own retag. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    (* the parent's row is stated on the COUNT (E2-V2): at a MISS nothing
       pins the parent live -- nameiparent released it, and an empty
       directory may have been removed before this lock *)
    assert (Hrow : arow_at (abs_view I) d
                     (MkAnode (ADir (dir_entries n)) (fn_nlink n))).
    { rewrite -(abs_row_dir_eq n Hdir).
      exact (abs_view_arow I d n Hlk (fn_is_dir_typed n Hdir)). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
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
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d t : Z) (nm : fname) (nd nt : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    fn_is_dir nd = true ->
    fn_nlink nd <> 0%nat ->
    dir_entries nd !! nm = Some t ->
    fn_is_dir nt = true ->
    fn_nlink nt <> 0%nat ->
    ~ dots_only (dir_entries nt) ->
    ftop_inv γfs -∗
    pf_at (dlookup_commit_at (fs_gamma_L γfs) appE) Fex -∗
    top_frag_q (fs_gamma_L γfs) dqd d nd -∗
    top_frag_q (fs_gamma_L γfs) dqt t nt ={E}=∗
      top_frag_q (fs_gamma_L γfs) dqd d nd
      ∗ top_frag_q (fs_gamma_L γfs) dqt t nt
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries nd)) (fn_nlink nd))⌝
          ∗ ⌜dir_entries nd !! nm = Some t⌝
          ∗ ⌜av !! t = Some (MkAnode (ADir (dir_entries nt)) (fn_nlink nt))⌝
          ∗ ⌜~ dots_only (dir_entries nt)⌝
          ∗ Fex.(pf_recv) av d nm t.
  Proof.
    intros HE Hdird Hnld Hnm Hdirt Hnlt Hne. iIntros "#Hi Hcm Hfd Hft".
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfd") as %Hlkd.
    iDestruct (ghost_map_lookup with "Hta Hft") as %Hlkt.
    assert (Hrowd : abs_view I !! d
                    = Some (MkAnode (ADir (dir_entries nd)) (fn_nlink nd))).
    { by rewrite (abs_view_lookup_of I d nd Hlkd) (mkf_abs_of_dir nd Hdird Hnld). }
    assert (Hrowt : abs_view I !! t
                    = Some (MkAnode (ADir (dir_entries nt)) (fn_nlink nt))).
    { by rewrite (abs_view_lookup_of I t nt Hlkt) (mkf_abs_of_dir nt Hdirt Hnlt). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
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

  (* Replaces [InodeRegion.ireg_top_retag_*] at the parent: same premise
     ([inode_local] of the flushed record), same payout (the moved
     fragment), plus the caller's two phases on either side of the
     [ghost_map_update] INSIDE the one [ftopN] critical section (the
     statement's "the pair is ONE instant to every other party").

     The TARGET's fragment is only READ -- [unl_pre]'s last three conjuncts
     are about [ip], whose lock the walk has held since W3 -- and comes
     back untouched.  [dec] is [unl_dec] of the target's own node, so the
     FILE arm instantiates it at 0 and the DIR arm at 1. *)
  Lemma uf_uent_fire (γfs : fs_names) (E : coPset) (dqt : dfrac)
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d t : Z) (nm : fname) (dec : nat) (np np' nt : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    dir_entries np !! nm = Some t ->
    nm <> DOT ->
    nm <> DOTDOT ->
    (1 <= fn_nlink np)%nat ->
    (1 <= fn_nlink nt)%nat ->
    (forall es, an_node (abs_row nt) = ADir es -> dots_only es) ->
    unl_dec (an_node (abs_row nt)) = dec ->
    abs_of np'
      = Some (MkAnode (ADir (delete nm (dir_entries np))) (fn_nlink np - dec)%nat) ->
    fn_type nt <> 0 ->
    ftop_inv γfs -∗ app_inv γfs -∗
    pf_at (uent_commit_at (fs_gamma_L γfs) appE) Fent -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqt t nt ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqt t nt
      ∗ ∃ av : aview,
          ⌜unl_pre av d nm (dir_entries np) (fn_nlink np) t (abs_row nt)⌝
          ∗ Fent.(pf_recv) av d nm t.
  Proof.
    intros HE Hloc Hdir Hnm HnD HnDD Hnlp Hnlt Hdots Hdec Habsp' Hnzt.
    iIntros "#Hi #Hai Hcm Hfp Hft".
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hft") as %Hlkt.
    assert (Hrowp : abs_view I !! d
                    = Some (MkAnode (ADir (dir_entries np)) (fn_nlink np))).
    { by rewrite (abs_view_lookup_of I d np Hlkp)
                 (mkf_abs_of_dir np Hdir ltac:(lia)). }
    assert (Hrowt : abs_view I !! t = Some (abs_row nt))
      by exact (abs_view_lookup_live I t nt Hlkt Hnzt ltac:(lia)).
    assert (Hpre : unl_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) t (abs_row nt)).
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
    { rewrite (abs_view_insert I d np' _ Habsp').
      rewrite /delta_unl_ent Hrowp /=. reflexivity. }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I d t nm (dir_entries np) (fn_nlink np) (abs_row nt)
            with "[//] Hta") as "(Hta & Hstep & Hph2)".
    (* THE MOVE, at the whole authority: the application's half comes out
       of [appN] beside its claim, which the caller's step re-establishes
       under the later ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I d np np' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hfp") as "[Hta Hfp]".
    { iIntros (_) "Hp". iApply (app_step_at d I _ np' with "Hstep Hp").
      by rewrite Hdelta Hdec. }
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
  (* THE MASK SIDE CONDITION, ONCE.  Every [uf_*_fire] call site at [⊤]
     spliced this as [ltac:(solve_ndisj)], and an [ltac:] in argument
     position is priced by the DEPTH of its call site rather than by its goal
     (claude-notes/optimization.md, "inline [ltac:] in argument position") --
     under a [uf_utgt_fire] whose own arguments spell a nested bitvector word
     three times, that was seconds per site.  The fact is CLOSED, so it
     belongs in a lemma proved where the context is empty. *)
  Lemma uf_nd_top : (↑ftopN ∪ ↑appN : coPset) ⊆ ⊤.
  Proof. solve_ndisj. Qed.

  Lemma uf_utgt_fire (γfs : fs_names) (E : coPset)
      (Ftgt : pfam Σ (aview -> Z -> iProp Σ)) (t : Z) (nt nt' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local t nt' ->
    (1 <= fn_nlink nt)%nat ->
    fn_type nt' <> 0
    /\ abs_row nt' = MkAnode (an_node (abs_row nt)) (fn_nlink nt - 1)%nat ->
    fn_type nt <> 0 ->
    ftop_inv γfs -∗ app_inv γfs -∗
    pf_at (utgt_commit_at (fs_gamma_L γfs) appE) Ftgt -∗
    top_frag (fs_gamma_L γfs) t nt ={E}=∗
      top_frag (fs_gamma_L γfs) t nt'
      ∗ ∃ av : aview, ⌜av !! t = Some (abs_row nt)⌝ ∗ Ftgt.(pf_recv) av t.
  Proof.
    intros HE Hloc Hnl Habs' Hnzt. iIntros "#Hi #Hai Hcm Hf".
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! t = Some (abs_row nt))
      by exact (abs_view_lookup_live I t nt Hlk Hnzt ltac:(lia)).
    (* the counted insert IS the delta (E2-V2): at the last link the row
       leaves the view, else it stays at the lowered count *)
    assert (Hdelta : abs_view (<[t := nt']> I)
                     = delta_unl_tgt t (abs_view I)).
    { destruct Habs' as [Hnz' Hrow'].
      rewrite (abs_view_insert_row I t nt' _ Hnz' Hrow')
              (delta_unl_tgt_unfold _ _ _ Hrow) /=.
      reflexivity. }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I t (abs_row nt) with "[//] [%] Hta") as "(Hta & Hstep & Hph2)".
    { exact Hnl. }
    (* THE MOVE, at the whole authority: the application's half comes out
       of [appN] beside its claim, which the caller's step re-establishes
       under the later ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I t nt nt' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "Hp". iApply (app_step_at t I _ nt' Hdelta with "Hstep Hp"). }
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

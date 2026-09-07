(* FsAbsLinkFire.v -- THE sys_link CONTRACT'S FIRE POINTS, discharged
   against the invariant, plus the two reading bridges [SpecSysLink]'s
   three commits owe their prover (round E2, lane E2-L).

   Worklist: claude-notes/projects/app-round-e2.md section 4 and the lane
   brief in app-round-e2-briefs.md.  A NEW LEAF rather than an append to
   [FsAbsUnlinkFire.v] / [FsStateEra.v], for the mirror's reason every
   other campaign leaf records ([FsAbsNpar], [FsAbsPins], [FsAbsCreateFire],
   [FsAbsUnlinkFire]): the build mirror forbids touching a tracked file.

   ==== THERE ARE THREE INSTANTS AND ONLY TWO NEW FIRES ================

   sys_link moves the abstract state three times (SpecSysLink.v's own
   header): the target's count UP before any name exists, the parent's
   entry, and -- on every route to [bad:] -- the target's count back DOWN.
   The third is [FsAbsDelta.delta_link_untgt], which IS
   [FsAbsDelta.delta_unl_tgt] on the nose, so its commit is
   [SpecSysUnlinkAU.utgt_commit_at] and its fire is
   [FsAbsUnlinkFire.uf_utgt_fire], REUSED VERBATIM at
   [ProofSysLinkTails.sl_tail_bad]'s retag.  Nothing about the undo is
   restated here; cloning it would be the cross-product the guiding
   principle forbids.

     [lf_tgt_fire]  INSTANT 1, fused with the retag the landed walk
        performs after [wp_iupdate_link] (site #28, ProofSysLink.v).
        [uf_utgt_fire]'s mold at [+1]: same premise ([inode_local] of the
        flushed record), same payout (the moved fragment), plus the
        caller's two phases inside the one [ftopN] critical section.  The
        row it reports is COUNTED ([FsAbsDefs.arow_at]): sys_link has no
        [ip->nlink == 0] guard, so the target may be an unlinked-but-open
        file with no row at all and the bump RESURRECTS it -- one insert
        either way ([FsAbsDelta]'s header, lane E2-D's deviation).
     [lf_ent_fire]  INSTANT 2, fused with the retag at [dirlink]'s append
        (site #29).  [uf_uent_fire]'s parent half at an INSERT rather than
        a delete, and with no second fragment: [unl_pre]'s target conjuncts
        have no twin here, because instant 1 already gave the walk its own
        receipt for the target.

   ==== THE READING BRIDGES ============================================

   [lf_nlink_row] is [FsAbsUnlinkFire.uf_nlink_row] at [+1] -- the
   count-raised row at the [iupdate], stated over "a record that differs in
   [di_nlink] alone" so a leaf never depends on a proof file's [sl_setnl]
   congruences; it reuses [uf_abs_node_nlink], which is exactly that
   statement and is direction-free.

   [lf_parent_row] is the [abs_of] wrap of the LANDED
   [FsStateEra.dir_entries_dirlink_ins] (the insert-side half): a dirlink
   keeps the type and the count, so the parent's row stays an [ADir] at the
   old count with one more name.  ITS [inum <> 0] PREMISE IS WHY LANE
   E2-L0 HAD TO LAND FIRST: a dirent whose inum is zero IS a free slot
   ([DirView.dir_live]), so a zero target would leave the view unchanged
   and the delta would be false of the machine.  [IcacheHeld.inode_held]
   now carries [0 < bv_unsigned inum] and [lf_inum_nz] is the one-line
   bridge to [bv_0 16].

   BINDERS: [SpecSysUnlinkAU]'s section list VERBATIM, which is also
   [SpecSysLink]'s -- [fileG] is bound and [icacheG]/[icfg]/[fscfg] resolve
   only through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirentEnc.       (* [de_of_name], [dirent_bytes], [nonul]     *)
Require Import DirView.          (* [T_DIR_z], [dir_nrec], [dir_slot]        *)
Require Import FsTree.           (* [fname], [file_byte]                     *)
Require Import FsBlocks.         (* [fs_names]                               *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                             *)
Require Import BioDefs.          (* [BSIZE]                                  *)
Require Import InodeInv.         (* [blk_holes_zero], [MAXFILE]              *)
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s banner: [Require Import] does not re-import
   a required file's own imports, and an unbound [fileG] in a [`{! ...}]
   binder is silently generalised into a variable). *)
Require Import FdSlots.          (* [fdslotG]                                *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]    *)
Require Import ProcAvail.        (* [pavG]                                   *)
Require Import FsStateInode.     (* [fn_*], [dir_entries]                    *)
Require Import FsStateEra.       (* [era_node], [dir_entries_dirlink_ins]    *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]      *)
Require Import Xv6G.
Require Import FsAbsDelta.       (* [delta_link_tgt]/[delta_link_ent]        *)
Require Import FsAbsUnlinkFire.  (* [uf_abs_node_nlink], [uf_utgt_fire]      *)
Require Import SpecSysLink.      (* the statement this file's fires serve    *)
Require Import AppInv.           (* [appN]/[appE]: the commit mask           *)
Require Import FsAbsDefs.        (* LAST (FsAbs's own rule)                  *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE READING BRIDGES                                          *)
(* ===================================================================== *)

(* ---- the era node's type, once ------------------------------------- *)

Lemma lf_era_type (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  fn_type (era_node dn bm data) = bv_unsigned (di_type dn).
Proof. rewrite /fn_type era_node_rec //. Qed.

Lemma lf_era_not_dir (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z ->
  fn_is_dir (era_node dn bm data) = false.
Proof.
  intros Hnd. rewrite /fn_is_dir lf_era_type.
  exact (bool_decide_eq_false_2 _ Hnd).
Qed.

(* a dirent's inum is a [bv 16] and a ZERO one is a FREE SLOT
   ([DirView.dir_live]); [IcacheHeld.inode_held] carries the positivity
   since lane E2-L0, and this is the one-line bridge (round E2-L0's whole
   point) *)
Lemma lf_inum_nz (v : bv 16) : bv_unsigned v <> 0 -> v <> bv_0 16.
Proof. intros Hnz Hc. apply Hnz. rewrite Hc. apply bv_0_unsigned. Qed.

(* ---- THE COUNT-RAISED ROW AT [wp_iupdate_link] ---------------------- *)

(* [FsAbsUnlinkFire.uf_nlink_row] at [+1].  [sl_incnl] moves [di_nlink]
   ALONE, and every field [abs_node] reads -- the type (hence the arm), the
   size and the data, the device numbers -- rides; [uf_abs_node_nlink] is
   that statement and is direction-free, so only the count arithmetic
   differs. *)
Lemma lf_nlink_row (dn dn' : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> 0 ->
  di_type dn' = di_type dn ->
  di_size dn' = di_size dn ->
  di_major dn' = di_major dn ->
  di_minor dn' = di_minor dn ->
  (fn_nlink (era_node dn' bm data)
   = fn_nlink (era_node dn bm data) + 1)%nat ->
  fn_type (era_node dn' bm data) <> 0
  /\ abs_row (era_node dn' bm data)
     = MkAnode (an_node (abs_row (era_node dn bm data)))
               (fn_nlink (era_node dn bm data) + 1)%nat.
Proof.
  intros Hnz Hty Hsz Hmaj Hmin Hnl. split.
  - rewrite lf_era_type Hty. exact Hnz.
  - rewrite /abs_row /=.
    by rewrite (uf_abs_node_nlink dn dn' bm data Hty Hsz Hmaj Hmin) Hnl.
Qed.

(* ...and what that row does to the VIEW: the counted insert IS
   [delta_link_tgt] at the observed row.  A raised count is never zero, so
   the [arow_at]-shaped insert never takes the delete arm. *)
Lemma lf_tgt_delta (I : gmap Z fs_node) (t : Z) (n n' : fs_node) :
  fn_type n' <> 0 ->
  abs_row n' = MkAnode (an_node (abs_row n)) (fn_nlink n + 1)%nat ->
  abs_view (<[t := n']> I) = delta_link_tgt t (abs_row n) (abs_view I).
Proof.
  intros Hnz' Hrow'.
  rewrite (abs_view_insert_row I t n' _ Hnz' Hrow').
  case_decide as Hz; [cbn [an_nlink] in Hz; lia |].
  rewrite /delta_link_tgt. reflexivity.
Qed.

(* ---- THE PARENT'S ROW AT THE APPEND --------------------------------- *)

(* The real half -- [dir_entries] of the appended record IS the old map
   with one more name -- is ALREADY LANDED as
   [FsStateEra.dir_entries_dirlink_ins], so this lemma takes that lemma's
   premises and does the [abs_of] arithmetic around it.  [tot] is
   [SpecDirlink]'s reported byte count, sixteen on the arm that actually
   wrote a record (the no-write arm moves nothing and stays on
   [ireg_top_retag_same]). *)
Lemma lf_parent_row (dn dn' : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8))
    (inum : bv 16) (s : fname) (nrec k0 tot : nat) :
  nrec = dir_nrec (bv_unsigned (di_size dn)) ->
  k0 = dir_slot data nrec ->
  tot = 16%nat ->
  (length s <= 14)%nat -> nonul s ->
  inum <> bv_0 16 ->
  bv_unsigned (di_type dn) = T_DIR_z ->
  di_type dn' = di_type dn ->
  di_nlink dn' = di_nlink dn ->
  bv_unsigned (di_nlink dn) <> 0 ->
  bv_unsigned (di_size dn')
    = Z.max (bv_unsigned (di_size dn)) (Z.of_nat (16 * k0 + tot)) ->
  (forall x : nat,
     file_byte data' x
     = if decide ((16 * k0 <= x)%nat /\ (x < 16 * k0 + tot)%nat)
       then dirent_bytes (de_of_name inum s) !!! (x - 16 * k0)%nat
       else file_byte data x) ->
  dir_first data nrec s = None ->
  blk_holes_zero bm data -> blk_holes_zero bm' data' ->
  bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  bv_unsigned (di_size dn') <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  abs_of (era_node dn' bm' data')
  = Some (MkAnode
            (ADir (<[s := bv_unsigned inum]>
                     (dir_entries (era_node dn bm data))))
            (fn_nlink (era_node dn bm data))).
Proof.
  intros Hnrec Hk0 Htot Hlen Hs Hnz Hty Hty' Hnl Hnlz Hsz Hrng Hnone
         Hh Hh' Hb Hb'.
  subst tot.
  assert (Hents := dir_entries_dirlink_ins dn dn' bm bm' data data' inum s
                     nrec k0 Hnrec Hk0 Hlen Hs Hnz Hty Hty' Hsz Hrng Hnone
                     Hh Hh' Hb Hb').
  assert (Hdir' : fn_is_dir (era_node dn' bm' data') = true).
  { rewrite /fn_is_dir lf_era_type Hty'.
    exact (bool_decide_eq_true_2 _ Hty). }
  assert (Hnleq : fn_nlink (era_node dn' bm' data')
                  = fn_nlink (era_node dn bm data)).
  { rewrite /fn_nlink !era_node_rec Hnl. reflexivity. }
  assert (Hnl0 : fn_nlink (era_node dn' bm' data') <> 0%nat).
  { rewrite Hnleq /fn_nlink era_node_rec.
    pose proof (bv_unsigned_in_range _ (di_nlink dn)) as Hr.
    clear -Hnlz Hr. lia. }
  by rewrite (abs_of_dir _ Hdir' Hnl0) Hents Hnleq.
Qed.

(* ===================================================================== *)
(*  2.  THE TWO FIRE POINTS, [ftopN] OPENED AND CLOSED                    *)
(* ===================================================================== *)

Section LinkFire.
  (* [SpecSysLink]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  INSTANT 1 -- the target's count up, fused with its retag      *)
  (* ------------------------------------------------------------------ *)

  (* Replaces the [InodeRegion.ireg_top_retag_auto] the landed walk performs
     after [wp_iupdate_link] (site #28): same premise ([inode_local] of the
     flushed record), same payout (the moved fragment), plus the caller's
     two phases on either side of the [ghost_map_update] INSIDE the one
     [ftopN] critical section.

     The row it reports is the COUNTED one: [ip]'s lock is held here, so the
     record is the machine's to know, but whether the VIEW has that row is
     the count's business ([arow_at]) -- and sys_link, unlike unlink, never
     tests the count. *)
  Lemma lf_tgt_fire (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) (t : Z) (nt nt' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local t nt' ->
    fn_type nt <> 0 ->
    link_tgt_ok (an_node (abs_row nt)) ->
    fn_type nt' <> 0
    /\ abs_row nt' = MkAnode (an_node (abs_row nt)) (fn_nlink nt + 1)%nat ->
    ftop_inv γfs -∗ app_inv γfs -∗
    ltgt_commit_at (fs_gamma_L γfs) appE Φ -∗
    top_frag (fs_gamma_L γfs) t nt ={E}=∗
      top_frag (fs_gamma_L γfs) t nt'
      ∗ ∃ av : aview,
          ⌜arow_at av t (abs_row nt)⌝
          ∗ ⌜link_tgt_ok (an_node (abs_row nt))⌝
          ∗ Φ av t (abs_row nt).
  Proof.
    intros HE Hloc Hnzt Hok Habs'. iIntros "#Hi #Hai Hcm Hf".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : arow_at (abs_view I) t (abs_row nt))
      by exact (abs_view_arow I t nt Hlk Hnzt).
    assert (Hsome : is_Some (I !! t)) by (by eexists).
    assert (Hdelta : abs_view (<[t := nt']> I)
                     = delta_link_tgt t (abs_row nt) (abs_view I))
      by exact (lf_tgt_delta I t nt nt' (proj1 Habs') (proj2 Habs')).
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I t (abs_row nt) with "[//] [//] [//] Hta")
      as "(Hta & Hstep & Hph2)".
    (* THE MOVE, at the whole authority: the application's half comes out
       of [appN] beside its claim, which the caller's step re-establishes
       under the later ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I t nt nt' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at t I _ nt' Hdelta with "Hstep Hp"). }
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
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  INSTANT 2 -- the parent's entry, fused with its retag         *)
  (* ------------------------------------------------------------------ *)

  (* [FsAbsUnlinkFire.uf_uent_fire]'s parent half at an INSERT.  One
     fragment: the target's conjuncts have no twin here, because instant 1
     gave the walk its own receipt.  The parent is LIVE -- the orphan guard
     at +0x84 (xv6 f60ff58) refused an [nlink = 0] parent -- which is what
     puts its row in the view at all. *)
  Lemma lf_ent_fire (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d t : Z) (nm : fname) (np np' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    fn_nlink np <> 0%nat ->
    dir_entries np !! nm = None ->
    abs_of np'
      = Some (MkAnode (ADir (<[nm := t]> (dir_entries np))) (fn_nlink np)) ->
    ftop_inv γfs -∗ app_inv γfs -∗
    lent_commit_at (fs_gamma_L γfs) appE Φ -∗
    top_frag (fs_gamma_L γfs) d np ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries np)) (fn_nlink np))⌝
          ∗ ⌜dir_entries np !! nm = None⌝
          ∗ Φ av d nm t.
  Proof.
    intros HE Hloc Hdir Hnl Hnm Habsp'. iIntros "#Hi #Hai Hcm Hf".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrowp : abs_view I !! d
                    = Some (MkAnode (ADir (dir_entries np)) (fn_nlink np)))
      by (by rewrite (abs_view_lookup_of I d np Hlk) (abs_of_dir np Hdir Hnl)).
    (* the parent half IS the delta: one insert at a row the view has *)
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_link_ent d nm t (abs_view I)).
    { rewrite (abs_view_insert I d np' _ Habsp').
      rewrite (delta_link_ent_dir _ d nm t (dir_entries np) (fn_nlink np) Hrowp).
      reflexivity. }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I d t nm (dir_entries np) (fn_nlink np)
            with "[//] [//] Hta") as "(Hta & Hstep & Hph2)".
    iMod (app_top_update appE γfs I d np np' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at d I _ np' Hdelta with "Hstep Hp"). }
    iMod ("Hph2" $! (<[d := np']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = d)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  INSTANT 3 -- the undo, WHICH IS UNLINK'S TARGET FIRE          *)
  (* ------------------------------------------------------------------ *)

  (* [FsAbsUnlinkFire.uf_utgt_fire], reused verbatim at
     [ProofSysLinkTails.sl_tail_bad]'s retag.  Its [1 <= fn_nlink nt]
     premise holds there because the [ip->nlink++] at +0x5e paid for a link
     that no [dirlink] filed, and [IregLinkNz.ireg_tok_nz] reads that count
     back off the fragment the tail is about to spend.  No lemma here. *)

End LinkFire.

(* ===================================================================== *)
(* UkTreeRead.v -- THE READ SIDE OF AN OWNED SUBTREE: open, and read.     *)
(*                                                                       *)
(* design/user-tree.md section 4 item 1, lane TL-3 deliverable 2.  The    *)
(* stable corollaries a FROZEN DEED buys, each one an INSTANCE of a       *)
(* landed member plus the claim's own agreement -- never a second proof   *)
(* against the code (design/fs-syscall-specs.md section 2: “a corollary   *)
(* of the AU form + agreement”).  Nothing here opens a kernel invariant   *)
(* or holds a kernel ghost; the ONE thing a program brings is             *)
(* [AppTree.tree_pin], read through [TreeObs].                           *)
(*                                                                       *)
(*  open  -- at a path that resolves INSIDE the deed's subtree to a FILE, *)
(*           the descriptor the call returns is on EXACTLY that node      *)
(*           ([FdSlots.FdInode ino]), or the call returned -1, or the     *)
(*           application is tainted.  Section 3.                          *)
(*  read  -- at that descriptor, what lands in the program's buffer are   *)
(*           EXACTLY the bytes the deed's tree records for that node.     *)
(*           Section 4.                                                   *)
(*                                                                       *)
(* WHAT IS *NOT* HERE, and why (the lane's STOP rule -- a finding is      *)
(* worth as much as a lemma).  Section 5 records chdir and fstat.         *)
(*                                                                       *)
(* AND WHAT IS DELIBERATELY NOT HERE: anything that MOVES the tree.       *)
(* O_TRUNC is a write, so every open below is at [om_trunc vom = false];  *)
(* the write side waits on the owner's ruling (design section 5, TL-2's   *)
(* finding 1: an owner's own move is a ghost-map UPDATE, which the        *)
(* update-free reading of [AppInv.app_step] could not pay; TL-3W's        *)
(* two-phase move is the answer, and lane SEAM-I's update is not).        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserCwd.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import UmodeArith.         (* [moi_small] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import UkReadRows.
Require Import UkReadFile.         (* the read leaf, and its [read_arms] reading *)
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import UConsOpen.          (* [xfam_open] and the two key-level rows:
                                      TOP-LEVEL there and ECHO-FREE (the
                                      section's echo classes are not used by
                                      them), so nothing echo rides in here *)
Require Import SpecFileread.
Require Import SpecSysRead.
Require Import SysReadDefs.        (* [ard_count] / [ard_pre] *)
Require Import SysOpenDefs.        (* [open_au_plain_at], [open_fd_rcpt], the
                                      omode readings *)
Require Import SpecSysOpen.        (* [open_receipt] / [open_receipt_plain] *)
Require Import ArgPath.            (* [arg_path_of] / [arg_path_of_uniq] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import PathElems.
Require Import FsTree.
Require Import InodeInv.           (* [MAXFILE] *)
Require Import BioDefs.            (* [BSIZE] *)
Require Import UserPtTree.         (* [uptd]: the table the read's -1 reason is at *)
Require Import FsAbsReadFire.      (* [aread_commit_at] / [read_arms] *)
Require Import OffGv.              (* [off_ret_keep]: the commit's answer *)
Require Import FsAbsEra.
Require Import TreeView.
Require Import AppTree.
Require Import TreeObs.
Require Import PinnedObs.
Require Import FsAbsDefs.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

Section UkTreeRead.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  open's BUNDLE, AT A CONTENT PIN                                 *)
  (*                                                                      *)
  (*  [PinnedOpen.pinned_open_bundle] with [PinnedObs.pin_resolves_at]    *)
  (*  replaced by the absnode pin [pin_resolves_abs] (PinnedObs section   *)
  (*  10): a claim about the NAMESPACE pins a row's content, never its    *)
  (*  link count.  It belongs beside its twin in [PinnedOpen.v] and lives *)
  (*  here so that no landed file moves for this lane.                    *)
  (* =================================================================== *)
  Lemma tree_open_bundle_abs (γfs : fs_names) (Pin : aview -> Prop)
      (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (nd : absnode)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    om_create vom = false ->
    om_trunc vom = false ->
    pin_resolves_abs Pin cw pl hops ino nd ->
    arg_path_of M pv pl ->
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) Farm Fun Fok Fex (pobs_Fo Pin T) Ft.
  Proof using .
    intros Hcr Htr Hres Hpath. iIntros "#Hcl #Hinv".
    iDestruct (pinned_obs_abs γfs Pin T (pobs_Pmiss T) cw pl hops ino nd Hres
                 with "[] Hcl Hinv") as "(Hw & Ho & _)";
      [ iApply pobs_miss_taint_Pmiss | ].
    rewrite /open_in Hcr /open_au_plain_at. iFrame "Ho".
    iSplitL "Hw".
    { iIntros (pl') "%Hpath'".
      rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath). iExact "Hw". }
    iApply (open_trunc_piece_none _ vom _ Ft Htr).
  Qed.

  (* =================================================================== *)
  (*  2.  open's RECEIPT, READ AT A FILE PIN                              *)
  (*                                                                      *)
  (*  [PinnedOpen.pinned_open_dev] one node-kind over, and the same       *)
  (*  three-way collapse: the device and directory arms are REFUTED by    *)
  (*  the terminal identification, and the file arm's descriptor is on    *)
  (*  the inum the walk's own cursor names -- which is the pin's, which   *)
  (*  is the node the owner's TREE records at that path.                  *)
  (* =================================================================== *)
  Lemma tree_open_recv_file (γfs : fs_names) (Pin : aview -> Prop)
      (T : iProp Σ) `{!Persistent T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z)
      (bs : list (bv 8))
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    pin_resolves_abs Pin cw pl hops ino (AFile bs) ->
    arg_path_of M pv pl ->
    om_trunc vom = false ->
    open_receipt_plain OffParked (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) Ft sts r fdv' -∗
      (* the walk missed, or the call failed after it: nothing moved *)
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝)
       (* ...OR THE DESCRIPTOR IS ON EXACTLY THE PINNED NODE *)
       ∨ (∃ γo : gname,
            ⌜open_fd_rcpt (om_readable vom) (om_writable vom)
               (FdInode ino γo OffParked) sts r fdv'⌝)
       (* ...or the application is tainted *)
       ∨ T).
  Proof using .
    intros Hres Hpath Htr. iIntros "Hrc". rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & _) | Hok]".
    { iLeft. iPureIntro. exact (conj Hr Hfd). }
    iDestruct "Hok" as (pl' av i) "(%Hpath' & HP & Harm)".
    rewrite (arg_path_of_uniq M pv pl' pl Hpath' Hpath).
    (* no O_TRUNC, so the cursor is whole ([SpecSysOpen.cur_kept]) *)
    iEval (rewrite /cur_kept Htr) in "HP".
    iDestruct "Harm" as "[Hdev | [Hfile | Hdir]]".
    - (* DEVICE: refuted at a file pin *)
      iDestruct "Hdev" as (ma mi nl) "(%Hrow & _ & Hrecv & _ & _)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (AFile bs)
                   av i (MkAnode (ADev ma mi) nl) Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. cbn [an_node] in Hnode. discriminate Hnode.
    - (* FILE: the identification names the INUM, which is the whole
         corollary -- the descriptor is on the node the tree records *)
      iDestruct "Hfile" as (bs0 nl) "(%Hrow & Hrecv & _ & Hfdr)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (AFile bs)
                   av i (MkAnode (AFile bs0) nl) Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [Hi _]. subst i.
      iDestruct "Hfdr" as (γo) "[%Hfdr _]".
      iRight. iLeft. iExists γo. iPureIntro. exact Hfdr.
    - (* DIRECTORY: refuted the same way *)
      iDestruct "Hdir" as (ents nl) "(%Hrow & _ & Hrecv & _ & _)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (AFile bs)
                   av i (MkAnode (ADir ents) nl) Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. cbn [an_node] in Hnode. discriminate Hnode.
  Qed.

  (* =================================================================== *)
  (*  3.  THE open COROLLARY, AT THE U TIER                                *)
  (* =================================================================== *)

  (* THE DEPOSIT, out of the deed: [UConsOpen.cons_sup_console]'s shape at
     the tree claim.  The heap is LENT, which is what lets the path reading
     ([ArgPath.arg_path_of] at the trapping key's own image) be discharged
     from the caller's persistent view of its own rodata. *)
  Definition tree_open_fam (T : iProp Σ) (Pin : aview -> Prop)
      (hops : list Z) (Q : Z -> iProp Σ) : sfam :=
    xfam_open OffParked (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T)
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I)) Q.

  Lemma tree_open_sup (N : uk_names Σ) (c : tree_fixed) (r : tree_names)
      (g : gname) (root d i : Z) (t : ttree) (bs : list (bv 8))
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (* the path the caller passes, read off its own image *)
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    (* ...and the PURE fact that it resolves inside the owner's own tree *)
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile bs) ->
    tree_pin r g root t -∗ app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    udepwf_at N m pc USYS_open
      (tree_open_fam (tree_taint c) (fun v => subtree v root = Some t)
         (resolve_hops t d pl) (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hp Hstart Hd Hres.
    iIntros "#Hpin #Hinv #Hro".
    iDestruct (tree_pin_claim_law c r g root t Heq with "Hpin") as "#Hcl".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (tree_open_fam (tree_taint c) (fun v => subtree v root = Some t)
                 (resolve_hops t d pl) (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx)
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [tree_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (tree_open_bundle_abs fsc_fs (fun v => subtree v root = Some t)
              (tree_taint c) cw pl (resolve_hops t d pl) i (AFile bs)
              M pv (m !!! Regidx a1_idx) _ _ _ _ _ Hcr Htr
              (tree_pin_resolves_file root d i t bs cw pl Hp Hstart Hd Hres)
              (Hpath M Hsro) with "Hcl Hinv").
  Qed.

  (* THE TIE, and it is the whole reason this corollary is USABLE: the
     LEDGER says which descriptor came back (the caller's own ledger
     decides it -- [UserFd.ualloc]) and the RECEIPT says what that
     descriptor is ON.  They speak about the same resume view, so at the
     slot the call wrote the two spellings agree and the handle the caller
     keeps is at the pinned node.  [UInitConsK]'s console block is this at
     [FdDevice CONSOLE]; the arithmetic lemmas are [UConsOpen]'s. *)
  Lemma tree_open_fd_tie (l sts fdv' : list fdstate) (rv : mword 64)
      (rb wb : bool) (i : Z) (γo : gname) (omo : offmode)
      (fd : nat) (rd wr : bool)
      (ty : fdtype) :
    length sts = NOFILE ->
    rv = (mword_of_int (Z.of_nat fd) : mword 64) ->
    (fd < NOFILE)%nat ->
    fdv' = <[fd := FdOpen rd wr ty]> sts ->
    open_fd_rcpt rb wb (FdInode i γo omo) sts rv fdv' ->
    FdOpen rd wr ty = FdOpen rb wb (FdInode i γo omo).
  Proof using .
    intros Hlen Hrv Hlt Hfdv (fd0 & Hr0 & Hcl0 & Hfdv0).
    assert (Hlt0 : (fd0 < NOFILE)%nat).
    { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
    assert (Hfdeq : fd = fd0)
      by exact (init_cons_moi_nat_inj fd fd0 Hlt Hlt0
                  (eq_trans (eq_sym Hrv) Hr0)).
    subst fd0.
    assert (Hfdlt : (fd < length sts)%nat) by (rewrite Hlen; exact Hlt).
    assert (Hins : <[fd := FdOpen rd wr ty]> sts
                   = <[fd := FdOpen rb wb (FdInode i γo omo)]> sts)
      by exact (eq_trans (eq_sym Hfdv) Hfdv0).
    pose proof (list_lookup_insert sts fd (FdOpen rd wr ty) Hfdlt) as Hl1.
    pose proof (list_lookup_insert sts fd
                  (FdOpen rb wb (FdInode i γo omo)) Hfdlt) as Hl2.
    rewrite Hins in Hl1. rewrite Hl2 in Hl1. congruence.
  Qed.

  (* ---- THE COROLLARY ITSELF, at [UkRunSys.wp_uk_ecall_open_recv_img] --
     "open a path inside my subtree and what comes back is a HANDLE ON THE
     NODE MY TREE RECORDS THERE".  Three arms and no fourth: the call
     returned -1 and the ledger is back untouched; the caller holds
     [UserFd.ualloc] at a descriptor whose type is [FdInode i] -- which is
     exactly what [wp_uk_tree_read_learns] below consumes; or the
     application is tainted and some ledger comes back. *)
  Lemma wp_uk_ecall_open_own (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname)
      (root d i cw : Z) (t : ttree) (bs : list (bv 8))
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile bs) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    tree_pin r g root t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back, untouched *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)
        (* ...OR THE HANDLE, ON EXACTLY THE NODE THE TREE RECORDS *)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdInode i γo OffParked)))
        (* ...or the application is tainted, and SOME ledger comes back *)
        ∨ (ustd_any (ukn_fd N) ∗ tree_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hp Hstart Hd Hres.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hpin #Hinv Hcont".
    iDestruct (tree_open_sup N c r g root d i t bs Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Htr Hp Hstart Hd Hres with "Hpin Hinv Hro") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (tree_open_fam (tree_taint c) (fun v => subtree v root = Some t)
                 (resolve_hops t d pl) (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (tree_open_fam (tree_taint c)
                    (fun v => subtree v root = Some t)
                    (resolve_hops t d pl) (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iDestruct (tree_open_recv_file fsc_fs (fun v => subtree v root = Some t)
                 (tree_taint c) cw pl (resolve_hops t d pl) i bs
                 (uvis_M W) pv (m !!! Regidx a1_idx) _ (uvis_fd W) rv fdv'
                 (tree_pin_resolves_file root d i t bs cw pl Hp Hstart Hd Hres)
                 (Hpath (uvis_M W) Himg) Htr with "Hrc") as "Hans".
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr %Hfdv] | [Hok | #HT]]"; last first.
    { (* the taint: whatever the ledger arm is, SOME ledger comes back *)
      iRight. iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd". }
    - (* THE NODE: the receipt's type meets the ledger's number *)
      iDestruct "Hok" as (γo) "%Hrcpt".
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
        assert (Hlt0 : (fd0 < NOFILE)%nat).
        { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1 & _).
      rewrite (tree_open_fd_tie l (uvis_fd W) fdv' rv
                 (om_readable (m !!! Regidx a1_idx))
                 (om_writable (m !!! Regidx a1_idx)) i γo OffParked fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iLeft. iExists fd, γo. iFrame "Hal". iPureIntro.
      exact (conj Hr1 Hlt1).
    - (* the call failed: the ledger comes back untouched *)
      iLeft. iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  4.  THE read COROLLARY: the bytes a descriptor on a pinned node      *)
  (*      delivers ARE the tree's                                          *)
  (*                                                                      *)
  (*  [UkReadFile]'s leaf takes the caller's own observation commit        *)
  (*  ([FsAbsReadFire.aread_commit_at]) and hands its receipt back inside  *)
  (*  the content post.  The landed supplier of that commit is a HELD      *)
  (*  SHARE ([aread_commit_at_pinned_self] at [FsAbs.nview]) -- which a    *)
  (*  verified program does not have (EX-2).  This is the supplier out of  *)
  (*  the APPLICATION'S CLAIM instead: the fire opens [AppInv.app_inv]     *)
  (*  inside its own fupd, reads the deed's law against the very map the   *)
  (*  kernel lent it, and the receipt is the claim's own pure reading.     *)
  (*  [PinnedObs.pobs_aopen] is the same three lines at open's commit.     *)
  (* =================================================================== *)

  (* the receipt: what the claim says of the view the read observed *)
  Definition tree_read_recv (Pin : aview -> Prop) (T : iProp Σ)
      : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    pfam_triv (fun (av : aview) (_ : nat) (_ : anode) (_ : nat) =>
                 (⌜Pin av⌝ ∨ T)%I).

  Lemma tree_read_piece (γfs : fs_names) (Pin : aview -> Prop) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (i : Z) (γo : gname) :
    □ (∀ v : aview, app_pred app_run v -∗
                      app_pred app_run v ∗ (⌜Pin v⌝ ∨ T)) -∗
    app_inv γfs -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) (tree_read_recv Pin T).
  Proof using .
    iIntros "#Hcl #Hinv". rewrite /tree_read_recv. iApply pf_at_triv.
    rewrite /aread_commit_at. iIntros (I off a d) "%Hpre Hka Hoff".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom & #Hx)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I) ∗ (⌜Pin (abs_view I)⌝ ∨ T)))%I
      with "[Hp]" as "Hpc".
    { iNext. iApply ("Hcl" with "Hp"). }
    iDestruct "Hpc" as "[Hp Hc]".
    iMod "Hc".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka".
    iSplitL "Hoff"; [iApply (off_ret_of_link with "Hoff") |]. iExact "Hc".
  Qed.

  (* ...AND THE ARMS, READ.  [UkReadFile.read_arms_file_learn] with the
     held share replaced by the claim: the observed row is the pinned
     node's because the CLAIM says so at the very view the kernel read it
     in, and from there the count and the bytes are the landed post's. *)
  Lemma read_arms_tree_learn (Γ := fs_gamma_L fsc_fs) (Pin : aview -> Prop)
      (T : iProp Σ) (i : Z) (γo : gname) (P : uptd) (n : Z) (bs0 : list (bv 8))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64)
      (k : nat) (g : nat -> bv 8) :
    (forall v : aview, Pin v -> exists q : nat,
       v !! i = Some (MkAnode (AFile bs0) q)) ->
    (forall j : nat, (j < k)%nat ->
       uint (add_vec_int addr (Z.of_nat j)) = (uint addr + Z.of_nat j)%Z) ->
    (forall j : nat, (j < k)%nat ->
       M' !! uint (add_vec_int addr (Z.of_nat j)) = Some (g j)) ->
    (Z.to_nat n <= k)%nat ->
    read_arms Γ i γo P n (tree_read_recv Pin T) r M' addr -∗
    ((⌜r = (mword_of_int (-1) : mword 64)⌝
      ∨ (∃ off : nat,
           ⌜Z.to_nat (bv_unsigned r)
            = ard_count (Z.to_nat n) off (length bs0)⌝ ∗
           ⌜forall j : nat, (j < Z.to_nat (bv_unsigned r))%nat ->
              g j = bs0 !!! (off + j)%nat⌝))
     ∨ T).
  Proof using .
    intros Hpin Hlin Himg Hnk.
    rewrite /read_arms /read_post_ok /read_post_fail.
    iIntros "[Hok | [%Hm1 _]]"; last first.
    { iLeft. iLeft. by iPureIntro. }
    iDestruct "Hok" as (av off a d) "(%Hpre & %Hn & %Htie & %Hdr & %Hbytes & Hc)".
    iEval (rewrite /tree_read_recv /pfam_triv /=) in "Hc".
    iDestruct "Hc" as "[%HP | HT]"; last first.
    { iRight. iExact "HT". }
    destruct Hpre as (Hrow & _ & Hsz).
    destruct (Hpin av HP) as (q & Hav).
    assert (Hab : a = MkAnode (AFile bs0) q)
      by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    subst a. cbn [an_node] in Htie, Hbytes.
    cbn [anode_size_ok an_node] in Hsz.
    apply Nat2Z.inj_le in Hsz. rewrite Nat2Z.inj_mul in Hsz.
    change (Z.of_nat MAXFILE) with 268 in Hsz.
    change (Z.of_nat BSIZE) with 1024 in Hsz.
    iLeft. iRight. iExists off.
    assert (Hdc : d = ard_count (Z.to_nat n) off (length bs0)).
    { assert (Hbu : bv_unsigned r
                    = Z.of_nat (ard_count (Z.to_nat n) off (length bs0))).
      { rewrite Htie. apply moi_small.
        pose proof (ard_count_sub (Z.to_nat n) off (length bs0)) as Hle.
        unfold Z64. lia. }
      lia. }
    iPureIntro. split.
    { rewrite -Hdr Nat2Z.id. exact Hdc. }
    intros j Hj.
    assert (Hjd : (j < d)%nat) by (rewrite -Hdr Nat2Z.id in Hj; lia).
    assert (Hdk : (d <= k)%nat).
    { pose proof (ard_count_le (Z.to_nat n) off (length bs0)) as Hle. lia. }
    pose proof (Hbytes ltac:(intros i0 Hi0; apply Hlin; lia) j Hjd) as HM.
    pose proof (Himg j ltac:(lia)) as HG.
    rewrite HM in HG. by injection HG.
  Qed.

  (* ---- THE CONSUMER TEST: cat, AT A KNOWN TREE ------------------------
     [UkReadFile.wp_uk_cat_read_learns] with the held share replaced by a
     FROZEN DEED: a program that owns a subtree, holds a descriptor on a
     node of it, and reads -- and LEARNS that what landed in its buffer are
     the bytes its own tree records.  No application-level fs pin, and no
     claim about any row outside its subtree. *)
  Lemma wp_uk_tree_read_learns (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : tree_fixed) (r : tree_names) (gn : gname)
      (root d : Z) (t : ttree) (bs : list (bv 8)) (pl : list (bv 8))
      (cw : Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* THE PURE FACT THE DEED CASHES: this path, inside my tree, names the
       node my descriptor is on, and the tree records these bytes there *)
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile bs) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for reading on inode i" *)
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    (* THE DEED, FROZEN *)
    tree_pin r gn root t -∗
    app_inv fsc_fs -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝
         ∨ (∃ off : nat,
              ⌜Z.to_nat (bv_unsigned rv)
               = ard_count (Z.to_nat cnt) off (length bs)⌝ ∗
              ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                 gb j = bs !!! (off + j)%nat⌝))
        ∨ tree_taint c) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcapk Hfdv Hfdlt Hal4 Hp Hstart Hd Hres.
    iIntros "#Hi Hrun Hufdh #Hpin #Hinv Hbuf Hcont".
    iDestruct (tree_pin_claim_law c r gn root t Heq with "Hpin") as "#Hcl".
    iDestruct (tree_read_piece fsc_fs (fun v => subtree v root = Some t)
                 (tree_taint c) i γo with "Hcl Hinv") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo
                 (tree_read_recv (fun v => subtree v root = Some t)
                    (tree_taint c)) with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N)
                 (tree_read_recv (fun v => subtree v root = Some t)
                    (tree_taint c))) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' rv dd gb W M' fdv' cw' cs')
      "%Hdd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N)
                    (tree_read_recv (fun v => subtree v root = Some t)
                       (tree_taint c))) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 rv M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(_ & _ & _ & Hcore)".
    rewrite Hkey.
    rewrite /fileread_extra_core /=.
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (read_arms_tree_learn (fun v => subtree v root = Some t)
                 (tree_taint c) i γo P cnt bs rv M' (m !!! Regidx a1_idx) k gb
                 (fun v HP => proj2 (tree_pin_resolves_file root d i t bs cw pl
                                       Hp Hstart Hd Hres) v HP)
                 Hlin Himg ltac:(lia) with "Hcore") as "Hlearn".
    iApply ("Hcont" $! h' rv gb with "Hufdh Hlearn Hrun Hbuf").
  Qed.

  (* =================================================================== *)
  (*  5.  WHAT THE DEED DOES *NOT* BUY, AND EXACTLY WHY (the STOP rule)    *)
  (*                                                                      *)
  (*  chdir.  The corollary the brief asked for -- “chdir into a directory *)
  (*  of [t] and the cwd lands at the resolved inum” -- is NOT landable on *)
  (*  the leaves as they stand, for TWO independent reasons, and the       *)
  (*  second is the deeper:                                                *)
  (*    (i)  THE U-TIER LEAF DROPS THE RECEIPT.  The kernel HAS one        *)
  (*         ([SpecSysChdir.chdir_receipt], whose success arm is exactly   *)
  (*         [cw' = i] beside the walk's cursor at [i] and the observed    *)
  (*         directory row), and [UexecExecInst]'s branch 9 pays it at the *)
  (*         U key.  But [UkRunSys.wp_uk_ecall_chdir] takes the FAMILY-    *)
  (*         FREE deposit [UkRun.udepw] and binds the post as [_], exactly *)
  (*         as [wp_uk_ecall_open] did before lane OPEN-PIN.  The fix is a *)
  (*         [wp_uk_ecall_chdir_recv] on [wp_uk_ecall_open_recv]'s mould   *)
  (*         (a [udepwf_at] premise, the post kept, the cwd row handed     *)
  (*         over) -- a kernel-leaf lane, not a read-side corollary.       *)
  (*    (ii) AND THE DEPOSIT WOULD NOT BE PAYABLE AT A PIN ANYWAY.         *)
  (*         chdir's bundle ([SpecSysChdir.chdir_au_pre]) owes the walk in *)
  (*         the [∀ pl] form ([SysOpenDefs.namei_walk_pre_era]), and a pin *)
  (*         answers the walk at ONE path -- at any other path its cursor  *)
  (*         is simply false ([PinnedObs.v]'s own note: “chdir and unlink  *)
  (*         still carry the [∀ pl] form and need that seam first”).  So   *)
  (*         chdir needs the ONE-PATH seam before any claim, tree or       *)
  (*         console, can answer it.                                       *)
  (*                                                                       *)
  (*  fstat.  There is no U-tier leaf at all: [UkRunSys]'s leaves are      *)
  (*  exit/fork/exec/open/read/write/close/dup/pipe/chdir/kill/wait/sbrk   *)
  (*  and the quiet row, and fstat (8) goes through the quiet leaf, which  *)
  (*  drops the post.  [UexecExecInst]'s own list says which numbers pay a *)
  (*  post and 8 is not among them -- so there is nothing to instantiate,  *)
  (*  and "the size of a file of my subtree" is a corollary with no        *)
  (*  carrier yet.  (The tree itself HAS the answer: [tv_nodes t !! i] is  *)
  (*  the node, and its [AFile bs] carries [length bs].)                   *)
  (*                                                                       *)
  (*  A DIRECTORY'S CONTENT.  [TreeObs]'s pin is at a row the projection   *)
  (*  is the identity on -- a file or a device -- because the tree HIDES   *)
  (*  the dots: at a directory the claim pins [hide_dots e] and the        *)
  (*  kernel's row carries [e].  Every corollary about a directory row's   *)
  (*  ENTRY MAP (an open at O_RDONLY that reads dirents, fstat on a        *)
  (*  directory) therefore needs a dots-tolerant identification first.     *)
  (* =================================================================== *)

End UkTreeRead.

(* ===================================================================== *)
(* UInitTreeCons.v -- /INIT'S CONSOLE SETUP AT THE TREE CLAIM (lane TL-7, *)
(* deliverable D2; design/user-tree.md section 9.5(5), first bullet).     *)
(*                                                                       *)
(* [UInitConsK.v] pays /init's three console leaves out of ECHO's console *)
(* ledger.  This file pays them out of the TREE CLAIM'S OWN DEED, and     *)
(* nothing else: the credential /init carries through its console dance   *)
(* is [AppTree.tree_own r g ROOTINO t] -- I own the whole namespace at    *)
(* the root and it is exactly [t] -- and every arm hands it back as the   *)
(* deed, never as the taint.  That is what makes the tree claim's LIVE    *)
(* arm cover mknod("/console") and the two opens, so the taint is minted  *)
(* only at the banner ([UInitTree.tree_kinit_ban_law]).                   *)
(*                                                                       *)
(*   1  THE FIRST OPEN, WHICH MISSES.  [UInitCons.init_cons_abs_law] --   *)
(*      holding K, every view the claim holds of has no console and K     *)
(*      comes back -- is [TreeObs.tree_own_claim_law] at the deed, with   *)
(*      the pure step [tree_cons_absent]: a subtree whose ROOT has no     *)
(*      `console` entry is a view whose root has none.  The leaf itself   *)
(*      is [UInitConsK.init_open_absent_leaf_holds] VERBATIM -- it is     *)
(*      claim-generic and takes the law as its only application premise.  *)
(*                                                                       *)
(*   2  open AT A DEVICE INSIDE THE OWNED SUBTREE.  [UkTreeRead] lands    *)
(*      the corollary at a FILE node ([wp_uk_ecall_open_own]); the        *)
(*      console is a DEVICE, so its receipt reading is the one node kind  *)
(*      over ([PinnedOpen.pinned_open_dev] at the absnode pin) and the    *)
(*      descriptor that comes back is [FdSlots.FdDevice ma].              *)
(*                                                                       *)
(*   3  /INIT'S SECOND open, at that corollary and at its own literal.    *)
(*                                                                       *)
(*   4  /INIT'S MKNOD, at [UkTreeCreate.tree_mknod_sup]: the deed        *)
(*      goes in live and comes back either MOVED (the console is in the   *)
(*      tree now) or untouched.  On the moved arm the deed is FROZEN      *)
(*      ([AppTree.tree_freeze]) and spent on the second open's leaf --    *)
(*      /init never moves the namespace again, so the trade costs it      *)
(*      nothing and buys the [box]-shaped claim law a walk needs.         *)
(*                                                                       *)
(*   5  [tree_init_cons_leaves]: the pair /init carries from its entry.   *)
(*                                                                       *)
(* WHAT IS NOT HERE, and it is a named limit rather than an oversight:    *)
(* the HIT arm of the dance ([UkInit.init_cons_hit], UkInit.v:535) at an  *)
(* era whose namespace ALREADY has /console.  That arm wants              *)
(* [UkInit.uki_mknod_hit_leaf] (UkInit.v:499) -- a CREDENTIAL-FREE and    *)
(* box-shaped mknod, i.e. "this call fails" proved with no live deed in   *)
(* hand -- and the tree's mknod corollary needs the LIVE deed, which a    *)
(* box cannot carry.  Echo pays that arm from its persistent FLAG; the    *)
(* tree's flag is the deed, and a deed is not persistent.  So a           *)
(* verified-/init theorem built on this file reads at an era whose        *)
(* namespace has no /console yet, and any other era takes the at-boot arm *)
(* ([UTreeAdequacy.tree_Hinit_boot]) -- until someone prices a            *)
(* frozen-pin this-mknod-fails corollary in [UkTreeCreate.v].             *)
(* THE DEPOSIT INSTANCE IS WRITTEN DOWN AND NOT RESOLVED.  /init runs at  *)
(* [UexecExecInst.uprogSG_free] ([UInitBoot.v]'s ruling), and             *)
(* [UkTreeRead.wp_uk_ecall_open_own] / [UkTreeCreate.wp_uk_ecall_mknod_own] *)
(* are pinned at [uprogSG_gen] through their [UkRun.urun] -- the two      *)
(* records are not convertible, and a walk at one applying a corollary at *)
(* the other WEDGES rather than failing (durable-notes).  So the two      *)
(* ecall walks here are re-derived from the PS-FREE pieces (the two       *)
(* suppliers, the receipt readings and [UInitConsK]'s dispatcher rows)    *)
(* with the instance named on every PS-indexed head.  A section binder    *)
(* for PS in either tree file wedges ITS OWN compile (measured).          *)
(* [UkRun.udepwf_at] is SG-indexed and takes no PS; only [urun] and the   *)
(* [wp_uk_*] leaves do.                                                  *)
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
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UCodeInit UkInit.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UConsOpen.          (* [xfam_open] and the two key-level rows *)
Require Import UkTreeRead.         (* the tree's read side: open at a FILE *)
Require Import UkTreeCreate.       (* the tree's mknod corollary *)
Require Import SysOpenDefs.
Require Import SpecSysOpen.
Require Import SpecSysMknod.       (* [mknod_arms] / [mknod_post_ok] *)
Require Import ArgPath.
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBlocks.
Require Import FsBytesGamma.
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PathElems.
Require Import FsTree.
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsConsPin.          (* [cons_absent] / [cons_path] *)
Require Import PinnedObs.
Require Import TreeView.
Require Import AppTree.
Require Import TreeObs.
Require Import UInitFd.
Require Import UInitCons.
Require Import UInitConsK.
Require Import CtxIdDefs.
Require FsImg.
Require User.InitSyms.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE PURE STEP: A SUBTREE WITHOUT `console` IS A VIEW WITHOUT ONE   *)
(*                                                                       *)
(*  [TreeView.npath_nclose] and [npath_tview] say that on PROPER names    *)
(*  the owner's own tree walks exactly as the view does, so a walk the    *)
(*  TREE answers with [None] is a walk the VIEW answers with [None].  At  *)
(*  the one-element path `console` that is [FsConsPin.cons_absent]        *)
(*  verbatim.                                                            *)
(* ===================================================================== *)

Lemma cons_path_proper : fs_proper cons_path.
Proof.
  rewrite /cons_path /fs_proper. repeat constructor; discriminate.
Qed.

Lemma tree_cons_absent (t : ttree) (av : aview) :
  npath (tv_nodes t) FsImg.ROOTINO cons_path = None ->
  subtree av FsImg.ROOTINO = Some t ->
  cons_absent av.
Proof.
  intros Hn Ht.
  rewrite (subtree_nodes_eq av FsImg.ROOTINO t Ht) /subtree_nodes in Hn.
  rewrite (npath_nclose (tview av) FsImg.ROOTINO cons_path FsImg.ROOTINO
             cons_path_proper (nreach_refl (tview av) FsImg.ROOTINO)) in Hn.
  rewrite (npath_tview av FsImg.ROOTINO cons_path cons_path_proper) in Hn.
  rewrite /cons_absent. rewrite /cons_path apath_at_cons in Hn.
  destruct (astep av FsImg.ROOTINO fname_console) as [c |] eqn:E;
    [| reflexivity ].
  rewrite (apath_at_nil av c) in Hn. discriminate Hn.
Qed.

(* ...and the DECIDABLE side condition a consumer computes on its own
   tree: "my namespace has no `console` at its root". *)
Definition tree_no_console (t : ttree) : Prop :=
  npath (tv_nodes t) FsImg.ROOTINO cons_path = None.

Section UInitTreeCons.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UkTreeCreate.v]'s note): no local
     [Context {SG}] / [Context {PS}], and no local
     [ghost_varG Σ (gset gname)] -- the canonical field instance is what
     every landed [UkRun.urun] in scope carries. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* =================================================================== *)
  (*  1.  THE ABSENCE LAW, AT THE DEED                                    *)
  (* =================================================================== *)

  Lemma tree_cons_abs_law (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_no_console t ->
    ⊢ init_cons_abs_law (tree_taint c) (tree_own r g FsImg.ROOTINO t).
  Proof using .
    intros Heq Hnc. rewrite /init_cons_abs_law /init_cons_pin_law.
    iDestruct (tree_own_claim_law c r Heq) as "#Hl".
    iIntros "!>" (v) "Hk Hp".
    iDestruct ("Hl" $! v g FsImg.ROOTINO t with "Hk Hp")
      as "(Hp & Hk & [%Hs | HT])".
    - iFrame "Hp Hk". iLeft. iPureIntro.
      exact (tree_cons_absent t v Hnc Hs).
    - iFrame "Hp Hk". iRight. iExact "HT".
  Qed.

  (* ...AND THE LEAF, WHICH IS [UInitConsK]'s VERBATIM.  The first open's
     discharge names no application at all beyond this law, which is the
     whole point of stating it that way. *)
  Lemma tree_open_absent_leaf_holds (N : uk_names Σ) (c : tree_fixed)
      (r : tree_names) (g : gname) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_no_console t ->
    app_inv fsc_fs -∗
    □ UkInit.uki_open_absent_leaf (PS := uprogSG_free) N (tree_taint c)
        (tree_own r g FsImg.ROOTINO t).
  Proof using .
    intros Heq Hnc. iIntros "#Hinv".
    iApply (init_open_absent_leaf_holds N (tree_taint c)
              (tree_own r g FsImg.ROOTINO t)
              ltac:(apply _) ltac:(apply _) ltac:(apply _)
              with "[] Hinv").
    iApply (tree_cons_abs_law c r g t Heq Hnc).
  Qed.

  (* =================================================================== *)
  (*  2.  open AT A DEVICE INSIDE THE OWNED SUBTREE                       *)
  (*                                                                     *)
  (*  [UkTreeRead.tree_open_recv_file] at the other node kind, and        *)
  (*  [PinnedOpen.pinned_open_dev]'s collapse: the file and directory     *)
  (*  arms are REFUTED by the terminal identification and the device      *)
  (*  arm's descriptor is on the major the owner's tree records.          *)
  (* =================================================================== *)
  Lemma tree_open_recv_dev (γfs : fs_names) (Pin : aview -> Prop)
      (T : iProp Σ) `{!Persistent T}
      (cw : Z) (pl : list (bv 8)) (hops : list Z) (ino : Z) (ma mi : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (rv : mword 64) (fdv' : list fdstate) :
    pin_resolves_abs Pin cw pl hops ino (ADev ma mi) ->
    arg_path_of M pv pl ->
    om_trunc vom = false ->
    open_receipt_plain OffParked (fs_gamma_L γfs) γfs cw M pv vom
      (pobs_P T hops) (pobs_Pmiss T) (pobs_Fo Pin T) Ft sts rv fdv' -∗
      ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝)
       ∨ ⌜open_fd_rcpt (om_readable vom) (om_writable vom) (FdDevice ma)
             sts rv fdv'⌝
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
    - (* THE DEVICE: the identification names the major *)
      iDestruct "Hdev" as (ma' mi' nl') "(%Hrow & %Hnd & Hrecv & Ht & %Hfdr)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (ADev ma mi)
                   av i (MkAnode (ADev ma' mi') nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. cbn [an_node] in Hnode.
      injection Hnode; intros Hmi Hma. subst ma' mi'.
      iRight. iLeft. iPureIntro. exact Hfdr.
    - (* A FILE: refuted at a device pin *)
      iDestruct "Hfile" as (bs0 nl') "(%Hrow & Hrecv & _ & _)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (ADev ma mi)
                   av i (MkAnode (AFile bs0) nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. cbn [an_node] in Hnode. discriminate Hnode.
    - (* A DIRECTORY: refuted the same way *)
      iDestruct "Hdir" as (ents nl') "(%Hrow & _ & Hrecv & _ & _)".
      iDestruct (pobs_node_abs Pin T cw pl hops ino (ADev ma mi)
                   av i (MkAnode (ADir ents) nl') Hres with "HP Hrecv")
        as "[%Hid | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      destruct Hid as [_ Hnode]. cbn [an_node] in Hnode. discriminate Hnode.
  Qed.

  (* THE DEPOSIT, out of a FROZEN deed: [UkTreeRead.tree_open_sup] at a
     device node. *)
  Lemma tree_open_sup_dev (N : uk_names Σ) (c : tree_fixed) (r : tree_names)
      (g : gname) (root d i : Z) (t : ttree) (ma mi : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, ADev ma mi) ->
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
              (tree_taint c) cw pl (resolve_hops t d pl) i (ADev ma mi)
              M pv (m !!! Regidx a1_idx) _ _ _ _ _ Hcr Htr
              (tree_pin_resolves_dev root d i t ma mi cw pl Hp Hstart Hd Hres)
              (Hpath M Hsro) with "Hcl Hinv").
  Qed.

  (* ---- AND THE COROLLARY: "open a DEVICE my tree records, and the
     descriptor is on that device's major".  [UkTreeRead.
     wp_uk_ecall_open_own] one node kind over. ---- *)
  Lemma wp_uk_ecall_open_dev_own (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname)
      (root d i cw : Z) (t : ttree) (ma mi : Z)
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
    resolves_from t d pl = Some (i, ADev ma mi) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun (PS := uprogSG_free) N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    tree_pin r g root t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l)
        ∨ (∃ fd : nat,
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdDevice ma)))
        ∨ (ustd_any (ukn_fd N) ∗ tree_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun (PS := uprogSG_free) N h' (<[Regidx a0_idx := rv]> m)
         (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hp Hstart Hd Hres.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hpin #Hinv Hcont".
    iDestruct (tree_open_sup_dev N c r g root d i t ma mi Img pv m pc pl cw
                 Heq Hpath Ha0 Hcr Htr Hp Hstart Hd Hres
                 with "Hpin Hinv Hro") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img (PS := uprogSG_free) N h m pc l avail
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
    iDestruct (tree_open_recv_dev fsc_fs (fun v => subtree v root = Some t)
                 (tree_taint c) cw pl (resolve_hops t d pl) i ma mi
                 (uvis_M W) pv (m !!! Regidx a1_idx) _ (uvis_fd W) rv fdv'
                 (tree_pin_resolves_dev root d i t ma mi cw pl
                    Hp Hstart Hd Hres)
                 (Hpath (uvis_M W) Himg) Htr with "Hrc") as "Hans".
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr %Hfdv] | [%Hrcpt | #HT]]"; last first.
    { iRight. iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd". }
    - (* THE DEVICE: the receipt's type meets the ledger's number *)
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
        assert (Hlt0 : (fd0 < NOFILE)%nat).
        { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1 & _).
      (* the two spellings of the resume view agree at the slot the call
         wrote, so the receipt's TYPE is the ledger's ([UkTreeRead.
         tree_open_fd_tie] at the device row) *)
      destruct Hrcpt as (fd0 & Hr0 & Hcl0 & Hfdv0).
      assert (Hlt0 : (fd0 < NOFILE)%nat).
      { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
      assert (Hfdeq : fd = fd0)
        by exact (init_cons_moi_nat_inj fd fd0 Hlt1 Hlt0
                    (eq_trans (eq_sym Hr1) Hr0)).
      subst fd0.
      assert (Hfdlt : (fd < length (uvis_fd W))%nat)
        by (rewrite Hlen; exact Hlt1).
      assert (Hst : FdOpen rd wr ty
                    = FdOpen (om_readable (m !!! Regidx a1_idx))
                             (om_writable (m !!! Regidx a1_idx))
                             (FdDevice ma)).
      { assert (Hins : <[fd := FdOpen rd wr ty]> (uvis_fd W)
                       = <[fd := FdOpen (om_readable (m !!! Regidx a1_idx))
                                   (om_writable (m !!! Regidx a1_idx))
                                   (FdDevice ma)]> (uvis_fd W))
          by exact (eq_trans (eq_sym Hfdv1) Hfdv0).
        pose proof (list_lookup_insert (uvis_fd W) fd (FdOpen rd wr ty) Hfdlt)
          as Hl1.
        pose proof (list_lookup_insert (uvis_fd W) fd
                      (FdOpen (om_readable (m !!! Regidx a1_idx))
                         (om_writable (m !!! Regidx a1_idx))
                         (FdDevice ma)) Hfdlt) as Hl2.
        rewrite Hins in Hl1. rewrite Hl2 in Hl1. congruence. }
      rewrite Hst.
      iRight. iLeft. iExists fd. iFrame "Hal". iPureIntro.
      exact (conj Hr1 Hlt1).
    - (* the call failed: the ledger comes back untouched *)
      iLeft. iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  3.  /INIT'S SECOND open, AT THE DEVICE ITS OWN MKNOD CREATED        *)
  (*                                                                     *)
  (*  [UInitConsK.init_open_console_leaf_holds] at the tree claim: the    *)
  (*  same three instructions of usys.S, with section 2's corollary in    *)
  (*  the middle in place of echo's pinned bundle.  The credential is a   *)
  (*  FROZEN deed, which is what a [box]-shaped leaf needs -- /init never *)
  (*  moves the namespace after its mknod, so the trade costs it nothing. *)
  (* =================================================================== *)
  Lemma tree_open_console_leaf_holds (N : uk_names Σ) (c : tree_fixed)
      (r : tree_names) (g : gname) (t : ttree) (i : Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    resolves_from t FsImg.ROOTINO init_cons_pl = Some (i, ADev CONSOLE 0) ->
    tree_pin r g FsImg.ROOTINO t -∗ app_inv fsc_fs -∗
    □ UkInit.uki_open_console_leaf (PS := uprogSG_free) N (tree_taint c)
        init_cons_fd.
  Proof using .
    intros Heq Hdd Hres. iIntros "#Hpin #Hinv !>".
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd Hcont".
    destruct Hargs as [Ha0 Ha1].
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli (PS := uprogSG_free) N h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3b2 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3b2 : mword 64) 2
                 = mword_of_int 0x3b4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0x3b4  ecall, at the DEVICE the owner's tree records ---- *)
    iApply (wp_uk_ecall_open_dev_own N h1 m1 (mword_of_int 0x3b4) ufd_l0 avail
              c r g FsImg.ROOTINO FsImg.ROOTINO i FsImg.ROOTINO t CONSOLE 0
              UCodeInit.init_ro (mword_of_int 0x970) init_cons_pl
              Heq
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              (fun M H => init_cons_path_of M H)
              Ha0'
              ltac:(rewrite Ha1'; exact init_cons_om2_create)
              ltac:(rewrite Ha1';
                    exact (proj2 (om_rdwr_plain _ init_cons_om2_arg)))
              ltac:(rewrite init_cons_path_elems; exact cons_path_proper)
              init_cons_start Hdd Hres
              with "[] [] Hrun Hcwd Hstd Hpin Hinv").
    { iApply (uis_init_3b4 with "Hcode"). }
    { iApply (init_rodata_img with "Hro"). }
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret) "Hans Hcwd Hrun".
    (* ---- 0x3b8  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr (PS := uprogSG_free) N h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr Hstd] | [Hal | [Hany #HT]]]".
    - (* the call failed: the ledger is back untouched *)
      iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExact "Hstd".
    - (* THE CONSOLE: the receipt's type is the ledger's, and the LEDGER
         decides the number -- which at an all-closed table is 0 *)
      iDestruct "Hal" as (fd) "[%Hb Hal]". destruct Hb as [Hr1 Hlt1].
      assert (Hmodes : om_readable (m1 !!! Regidx a1_idx) = true
                       /\ om_writable (m1 !!! Regidx a1_idx) = true).
      { rewrite Ha1'. exact (om_rdwr_modes _ init_cons_om2_arg). }
      destruct Hmodes as [Hrd Hwr].
      iEval (rewrite Hrd Hwr) in "Hal".
      iDestruct (ufd_alloc0 (ukn_fd N) init_cons_fd fd with "Hal")
        as "[%Hfd0 Hstd]".
      subst fd. iLeft. iFrame "Hstd". iPureIntro. rewrite Hr1. reflexivity.
    - iRight. iRight. iFrame "HT". iExact "Hany".
  Qed.

  (* =================================================================== *)
  (*  4.  /INIT'S MKNOD, AT THE OWNER'S OWN MOVE                          *)
  (*                                                                     *)
  (*  [UInitConsK.init_mknod_leaf_holds] at the tree claim, and the ONE   *)
  (*  place /init's own write pays a step of the claim.  The deed goes in *)
  (*  LIVE and comes back either moved -- and is then frozen and spent on *)
  (*  the second open's leaf -- or untouched, in which case the second    *)
  (*  open is the dead one again and fd 0 stays closed.                   *)
  (*                                                                     *)
  (*  [Cns] IS [True] AT THIS CLAIM: the credential /init hands the shell *)
  (*  it execs is echo's reading of the console's state, and a tree       *)
  (*  application makes no console claim at all.                         *)
  (* =================================================================== *)

  (* the two pure readings of the owner's own tree the leaf runs on *)
  Lemma tree_root_no_console (t : ttree) (e : gmap fname Z) :
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    e !! fname_console = None ->
    tree_no_console t.
  Proof using .
    intros Hd He.
    assert (Hs : nstep (tv_nodes t) FsImg.ROOTINO fname_console = None)
      by (rewrite /nstep /nents Hd /=; exact He).
    rewrite /tree_no_console /cons_path npath_cons Hs //.
  Qed.

  Lemma tree_top_ins_root (t : ttree) (e : gmap fname Z) (i : Z) :
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    i <> FsImg.ROOTINO ->
    tv_nodes (top_ins FsImg.ROOTINO fname_console i (ADev CONSOLE 0) t)
      !! FsImg.ROOTINO
    = Some (ADir (<[fname_console := i]> e)).
  Proof using .
    intros Hd Hne. cbn [tv_nodes top_ins].
    apply (tedge_ins_lookup_at _ FsImg.ROOTINO fname_console i e).
    by rewrite lookup_insert_ne.
  Qed.

  Lemma tree_top_ins_resolves (t : ttree) (e : gmap fname Z) (i : Z) :
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    i <> FsImg.ROOTINO ->
    resolves_from (top_ins FsImg.ROOTINO fname_console i (ADev CONSOLE 0) t)
      FsImg.ROOTINO init_cons_pl = Some (i, ADev CONSOLE 0).
  Proof using .
    intros Hd Hne.
    assert (Hs : nstep (tv_nodes (top_ins FsImg.ROOTINO fname_console i
                                     (ADev CONSOLE 0) t))
                   FsImg.ROOTINO fname_console = Some i).
    { rewrite /nstep /nents (tree_top_ins_root t e i Hd Hne) /=.
      apply lookup_insert. }
    assert (Hi : tv_nodes (top_ins FsImg.ROOTINO fname_console i
                             (ADev CONSOLE 0) t) !! i
                 = Some (ADev CONSOLE 0)).
    { cbn [tv_nodes top_ins].
      rewrite (tedge_ins_lookup_ne _ FsImg.ROOTINO fname_console i i Hne).
      apply lookup_insert. }
    rewrite /resolves_from init_cons_path_elems /cons_path npath_cons Hs.
    cbn [npath]. by rewrite Hi.
  Qed.

  Lemma tree_top_ins_dom (t : ttree) (e : gmap fname Z) (i : Z) :
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    i <> FsImg.ROOTINO ->
    FsImg.ROOTINO
      ∈ dom (tv_nodes (top_ins FsImg.ROOTINO fname_console i
                         (ADev CONSOLE 0) t)).
  Proof using .
    intros Hd Hne. apply elem_of_dom.
    exists (ADir (<[fname_console := i]> e)).
    exact (tree_top_ins_root t e i Hd Hne).
  Qed.

  Lemma tree_mknod_leaf_holds (N : uk_names Σ) (c : tree_fixed)
      (r : tree_names) (g : gname) (t : ttree) (e : gmap fname Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    e !! fname_console = None ->
    app_inv fsc_fs -∗
    □ UkInit.uki_mknod_leaf (PS := uprogSG_free) N (tree_taint c)
        (tree_own r g FsImg.ROOTINO t) True%I init_cons_fd.
  Proof using .
    intros Heq Hd He.
    assert (Hdd : FsImg.ROOTINO ∈ dom (tv_nodes t))
      by (apply elem_of_dom; by exists (ADir e)).
    iIntros "#Hinv !>".
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hown Hcont".
    destruct Hargs as (Ha0 & Ha1 & Ha2).
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hmknod & _ & _ & _ & _ & _ & _).
    rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (wp_uk_cli (PS := uprogSG_free) N h m (mword_of_int 0x3ba)
              (mword_of_int 17 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ba with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ba : mword 64) 2
                 = mword_of_int 0x3bc)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 17 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 1 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    assert (Ha2' : m1 !!! Regidx a2_idx = (mword_of_int 0 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha2. }
    (* ---- 0x3bc  ecall -- the RECEIPT-KEEPING quiet leaf, at the deed *)
    iApply (wp_uk_ecall_quiet_recv_img (PS := uprogSG_free) N h1 m1
              (mword_of_int 0x3bc) 17 avail
              (tree_mknod_fam c r g t CONSOLE 0 (ukn_pay N)) FsImg.ROOTINO
              UCodeInit.init_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 17 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [Hown]").
    { iApply (uis_init_3bc with "Hcode"). }
    { iApply (init_rodata_img with "Hro"). }
    { iApply (tree_mknod_sup N c r g t CONSOLE 0 FsImg.ROOTINO
                UCodeInit.init_ro (mword_of_int 0x970) m1 (mword_of_int 0x3bc)
                init_cons_pl Heq (fun M H => init_cons_path_of M H) Ha0'
                ltac:(rewrite Ha1'; exact init_cons_dev_major)
                ltac:(rewrite Ha2'; exact init_cons_dev_minor)
                init_cons_np_elems init_cons_start Hdd
                with "Hinv [] Hown").
      iApply (init_rodata_img with "Hro"). }
    assert (E1 : add_vec_int (mword_of_int 0x3bc : mword 64) 4
                 = mword_of_int 0x3c0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W cs') "%Himg %Hk0 %Hk1 %Hk2 %Hcw Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W) (mword_of_int 0x970 : mword 64)
                      init_cons_pl)
      by exact (init_cons_path_of (uvis_M W) Himg).
    iDestruct (spost_at_mknod_elim_at uslot
                 (tree_mknod_fam c r g t CONSOLE 0 (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int 0x970) CONSOLE 0
                 ret (uvis_M W) (uvis_fd W) FsImg.ROOTINO cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1 Ha1'; exact init_cons_dev_major)
                 ltac:(rewrite Hk2 Ha2'; exact init_cons_dev_minor)
                 with "Hpost") as "Harms".
    (* ---- 0x3c0  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr (PS := uprogSG_free) N h2 m2 (mword_of_int 0x3c0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3c0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply fupd_wp_triv.
    iAssert (|={⊤}=> UkInit.uki_mknod_out (PS := uprogSG_free) N
                       (tree_taint c) True%I init_cons_fd)%I
      with "[Harms]" as ">Hout".
    { rewrite /mknod_arms.
      cbn [tree_mknod_fam xfam_tree nf_P nf_Pmiss nf_Farm nf_Fun nf_Fok nf_Fex].
      iDestruct "Harms" as "[[_ Hok] | [_ Hfail]]".
      - (* THE MOVE COMMITTED: the deed records the device, and the frozen
           deed is what the second open's leaf runs on *)
        iDestruct (tree_mknod_ok_recv c r g t CONSOLE 0 (uvis_M W)
                     (mword_of_int 0x970) init_cons_pl fname_console
                     Hpath init_cons_last with "Hok") as "[Hm | #HT]";
          last first.
        { iModIntro. rewrite /UkInit.uki_mknod_out.
          iRight. iRight. iExact "HT". }
        iDestruct "Hm" as (i) "[%Hne Hown]".
        iMod (tree_freeze r g FsImg.ROOTINO _ with "Hown") as "#Hpin".
        iDestruct (tree_open_console_leaf_holds N c r g
                     (top_ins FsImg.ROOTINO fname_console i (ADev CONSOLE 0) t)
                     i Heq (tree_top_ins_dom t e i Hd Hne)
                     (tree_top_ins_resolves t e i Hd Hne)
                     with "Hpin Hinv") as "#Hlf".
        iModIntro. rewrite /UkInit.uki_mknod_out. iLeft.
        iSplitR; [ iExact "Hlf" | done ].
      - (* THE CALL FAILED: the deed comes straight back, and the second
           open is the dead one again *)
        iDestruct (tree_mknod_fail_recv c r g t CONSOLE 0 FsImg.ROOTINO
                     (uvis_M W) (mword_of_int 0x970) with "Hfail")
          as "[Hown | #HT]"; last first.
        { iModIntro. rewrite /UkInit.uki_mknod_out.
          iRight. iRight. iExact "HT". }
        iDestruct (tree_open_absent_leaf_holds N c r g t Heq
                     (tree_root_no_console t e Hd He) with "Hinv") as "#Habs".
        iModIntro. rewrite /UkInit.uki_mknod_out. iRight. iLeft.
        iExists (tree_own r g FsImg.ROOTINO t). iFrame "Habs Hown". }
    iModIntro.
    iApply ("Hcont" $! h3 ret with "Hout Hcwd Hrun").
  Qed.

  (* =================================================================== *)
  (*  5.  THE PAIR /init CARRIES FROM ITS ENTRY                           *)
  (* =================================================================== *)
  Lemma tree_init_cons_leaves (N : uk_names Σ) (c : tree_fixed)
      (r : tree_names) (g : gname) (t : ttree) (e : gmap fname Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    e !! fname_console = None ->
    app_inv fsc_fs -∗
    UkInit.init_cons_leaves (PS := uprogSG_free) N (tree_taint c)
      (tree_own r g FsImg.ROOTINO t) True%I init_cons_fd.
  Proof using .
    intros Heq Hd He. iIntros "#Hinv".
    rewrite /UkInit.init_cons_leaves. iSplitR.
    - iApply (tree_open_absent_leaf_holds N c r g t Heq
                (tree_root_no_console t e Hd He) with "Hinv").
    - iApply (tree_mknod_leaf_holds N c r g t e Heq Hd He with "Hinv").
  Qed.

End UInitTreeCons.

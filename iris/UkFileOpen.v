(* ===================================================================== *)
(* UkFileOpen.v -- THE FILE APPLICATION'S U-TIER COROLLARIES (lane       *)
(* F-OPEN-2, deliverable 3).                                             *)
(*                                                                       *)
(* [UkTreeRead.v] is the mould at the TREE claim's frozen pin and         *)
(* [UkTreeCreate.v] at its owner's move; this file is the two of them at  *)
(* [AppFile]'s DEED, through [FileOpen.v]'s suppliers.  Nothing here      *)
(* opens a kernel invariant or holds a kernel ghost: every lemma is a     *)
(* landed U-tier leaf plus one of [FileOpen]'s bundles and one of its     *)
(* receipt readers.                                                      *)
(*                                                                       *)
(*   [wp_uk_ecall_open_read_deed]   open(`f`, O_RDONLY) at a PRESENT      *)
(*        deed: the descriptor that comes back is on the deed's OWN INUM  *)
(*        and BOTH fractions come home.  [FileOpen.file_open_plain_au] /  *)
(*        [file_open_recv_file].                                         *)
(*   [wp_uk_ecall_open_miss_deed]   the same call at an ABSENT deed: the  *)
(*        call returns -1, the ledger is untouched, and the fraction      *)
(*        comes home ([FileOpen.file_open_miss_au] / [_recv], lane        *)
(*        F-OPEN-2's seam 2).                                            *)
(*   [wp_uk_read_deed_learns]       read at that descriptor: what lands   *)
(*        in the buffer are EXACTLY the bytes the deed records.           *)
(*        [FileOpen.file_read_piece] / [file_read_arms_learn].            *)
(*                                                                       *)
(* THE LEAF IS A VISIBLE PARAMETER, deliberately.  Every corollary here   *)
(* is stated over [UkRunSys.wp_uk_ecall_open_recv_img] /                  *)
(* [UkReadFile.wp_uk_ecall_read_file], the PARKED-offset members; lane    *)
(* OFF-HAND's held-offset twins ([wp_uk_ecall_open_recv_img_held],        *)
(* [_read_file_held]) are the same statements with the leaf swapped and   *)
(* [UserOff.uoff] added to the post, so each corollary below is           *)
(* re-instantiated by changing exactly one application.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
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
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import UkReadRows.
Require Import UserPtTree.         (* [uva_wmapped]: the read's -1 reason, and
                                      the mapped row that refutes it *)
Require Import UkReadFile.
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import UserOff.             (* [foff_pub]: the publish's handed half *)
Require Import UConsOpen.          (* [xfam_open] and the ledger arms *)
Require Import UkTreeRead.         (* [tree_open_fd_tie]: the ledger/receipt tie *)
Require Import SpecFileread.
Require Import SpecSysRead.
Require Import SysReadDefs.
Require Import SysOpenDefs.
Require Import SpecSysOpen.
Require Import ArgPath.
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import PathElems.
Require Import FsTree.
Require Import FsImgCheck.         (* [fname_f] *)
Require Import FsAbsEra.
Require Import PinnedObs.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import AppFileCons.      (* [file_cons_cred]: the console credential over [option Z] *)
Require Import FileOpen.
Require Import FsImg.              (* re-IMPORTED late, as FileOpen does *)
Require Import FsAbsDefs.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

Section UkFileOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* GENERIC IN THE PROGRAM-DEPOSIT INSTANCE (PROGRAM-STREAM stretch 13,
     defect 4): with no binder every [urun] here was at the ambient
     [uprogSG_gen], whose [udep] only an out-of-spec run supplies, so a
     verified shell (at [uprogSG_free]) could not exec cat.  A caller that
     resolves ambiently still gets [uprogSG_gen], exactly as before. *)
  (* SPELLED [UexecSG.uprogSG]: with the class not imported here, a bare
     [uprogSG] under the backtick is silently GENERALISED into a fresh
     variable and [PS] gets the wrong type (measured 2026-09-22). *)
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  0.  THE LEDGER A TAINTED OPEN HANDS BACK (lane CAT-GEOM-2).         *)
  (*                                                                     *)
  (*  The taint disjunct of every deed corollary below used to be         *)
  (*  [UserFd.ustd_any] -- "SOME ledger" -- and that is strictly weaker   *)
  (*  than what the leaf has in hand: [UConsOpen.uk_open_fd_arm] says     *)
  (*  either the call FAILED and the ledger is UNTOUCHED, or it ALLOCATED *)
  (*  and the ledger is untouched beside the new handle whenever the      *)
  (*  caller's own standard streams are all open                          *)
  (*  ([UserFd.ualloc_hi]).  A program that writes a DIAGNOSTIC after a   *)
  (*  tainted open needs exactly that and [ustd_any] does not give it:    *)
  (*  it does not say the program's fd 2 is still the console.  So the    *)
  (*  arm keeps the disjunction, minus the two kernel-side lists the      *)
  (*  caller cannot name.                                                *)
  (* =================================================================== *)
  Definition uk_open_taint_fd (gf : gname) (l : list fdstate) (r : mword 64)
    : iProp Σ :=
    ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
        ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
         /\ (fd < NOFILE)%nat
         (* ...AND IT IS NOT A PIPE (SUP-ONE's U2, kept on this arm by
            lane CAT-GEOM-4): the leaf exports it, and a payer that means
            to CLOSE the handle a tainted open returned needs exactly
            this ([UkCat.kcat_cldep_nopipe]). *)
         /\ fdst_nopipe (FdOpen rd wr t)⌝ ∗ ualloc gf l fd (FdOpen rd wr t))
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ustd gf l))%I.

  Lemma uk_open_taint_fd_of_arm (gf : gname) (l sts fdv' : list fdstate)
      (r : mword 64) :
    uk_open_fd_arm gf l sts fdv' r -∗ uk_open_taint_fd gf l r.
  Proof using .
    rewrite /uk_open_fd_arm /uk_open_taint_fd.
    iIntros "[Hal | [%Hb Hstd]]".
    - iDestruct "Hal" as (fd rd wr t) "[%Hb' Hal]".
      iLeft. iExists fd, rd, wr, t. iFrame "Hal". iPureIntro.
      destruct Hb' as (H1 & H2 & _ & H4). exact (conj H1 (conj H2 H4)).
    - iRight. iFrame "Hstd". iPureIntro. exact (proj1 Hb).
  Qed.

  (* ...AND THE READING A PROGRAM WHOSE STANDARD STREAMS ARE ALL OPEN
     MAKES OF IT: the ledger comes home on BOTH sub-arms, because
     [fdalloc] could not have landed on one of them
     ([UserFd.ualloc_hi]).  The new handle is dropped. *)
  Lemma uk_open_taint_fd_std (gf : gname) (l : list fdstate) (r : mword 64) :
    fd_lowest_closed l = None ->
    uk_open_taint_fd gf l r -∗ ustd gf l.
  Proof using .
    intros Hnone. rewrite /uk_open_taint_fd.
    iIntros "[Hal | [_ $]]".
    iDestruct "Hal" as (fd rd wr t) "[_ Hal]".
    iDestruct (ualloc_hi gf l fd (FdOpen rd wr t) Hnone with "Hal")
      as "(_ & $ & _)".
  Qed.

  (* =================================================================== *)
  (*  1.  open(`f`, O_RDONLY) AT A PRESENT DEED                           *)
  (* =================================================================== *)

  Definition file_open_fam (omo : offmode) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (Q : Z -> iProp Σ) : sfam :=
    xfam_open omo
      (pobs_P_lin (file_taint c) [ROOTINO; i] (fdq r q1 (Some (i, bs))))
      (pobs_Pmiss (file_taint c))
      (file_open_recv c r q2 (Some (i, bs)))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I)) Q.

  Lemma file_open_sup (N : uk_names Σ) (omo : offmode) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    udepwf_at N m pc USYS_open (file_open_fam omo c r q1 q2 i bs (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hinv #Hro Hd1 Hd2".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_open_fam omo c r q1 q2 i bs (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (file_open_plain_au fsc_fs c r q1 q2 i bs cw M pv
              (m !!! Regidx a1_idx) pl _ Heq (Hpath M Hsro) Hel Hst Htr
              with "Hinv Hd1 Hd2").
  Qed.

  (* ---- THE COROLLARY: "open `f` and the handle is on the inum MY DEED
     names, with both fractions back".  Three arms and no fourth. *)
  Lemma wp_uk_ecall_open_read_deed (N : uk_names Σ) (omo : offmode) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched, and so are both
           fractions *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...OR THE HANDLE, ON THE DEED'S OWN INUM *)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdInode i γo omo)) ∗
             (* ...AND THE HALF THE PUBLISH HANDED OUT (kernel stream, L4):
                nothing at mode PARK, [UserOff.uoff γo 0] at mode HAND. *)
             foff_pub omo γo ∗
             fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...or the application is tainted, and the LEDGER comes back
           (lane CAT-GEOM-2): either untouched, or beside a handle
           [UserFd.ualloc_hi] takes off it *)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd1 Hd2 Hcont".
    iDestruct (file_open_sup N omo c r q1 q2 i bs Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Htr Hel Hst with "Hinv Hro Hd1 Hd2") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (file_open_fam omo c r q1 q2 i bs (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_open_fam omo c r q1 q2 i bs (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_recv_file fsc_fs c r omo q1 q2 i bs cw (uvis_M W) pv
            (m !!! Regidx a1_idx) pl _ (uvis_fd W) rv fdv'
            (Hpath (uvis_M W) Himg) Hel Hst Htr with "Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hd1 & Hd2) | [Hok | #HT]]"; last first.
    { iRight. iRight. iFrame "HT".
      iApply (uk_open_taint_fd_of_arm (ukn_fd N) l (uvis_fd W) fdv' rv
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd". }
    - iDestruct "Hok" as (γo) "(%Hrcpt & Hpub & Hd1 & Hd2)".
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
                 (om_writable (m !!! Regidx a1_idx)) i γo omo fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iLeft. iExists fd, γo. iFrame "Hal Hpub Hd1 Hd2". iPureIntro.
      exact (conj Hr1 Hlt1).
    - iLeft. iFrame "Hd1 Hd2". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  2.  open(`f`, O_RDONLY) AT AN ABSENT DEED                           *)
  (*                                                                      *)
  (*  cat's `cannot open` branch, as a THEOREM: at [s = None] the walk     *)
  (*  misses and the success fold collapses, so there is no descriptor     *)
  (*  arm at all -- and (lane F-OPEN-2's seam 2) the fraction the walk was *)
  (*  paid with comes home.                                               *)
  (* =================================================================== *)

  Definition file_miss_fam (c : file_fixed) (r : file_names) (q : Qp)
      (Q : Z -> iProp Σ) : sfam :=
    xfam_open OffParked
      (pobs_P_dead_lin (file_taint c) (fdq r q None) ROOTINO)
      (pobs_Pmiss_ref (file_taint c) (fdq r q None))
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I))
      (* the truncate's receipt at an ABSENT deed is the TAINT: the
         terminal permit is paid out of it ([PinnedOpen.pobs_dead_trunc_piece],
         lane TRUNC-PERMIT), so the miss leaves take any mode *)
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => file_taint c)) Q.

  Lemma file_miss_sup (N : uk_names Σ) (c : file_fixed) (r : file_names)
      (q : Qp) (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile)
      (pc : mword 64) (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    fdq r q None -∗
    udepwf_at N m pc USYS_open (file_miss_fam c r q (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Hel Hst. iIntros "#Hinv #Hro Hd".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_miss_fam c r q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (file_open_miss_au fsc_fs c r q cw M pv (m !!! Regidx a1_idx) pl
              _ _ _ _ Heq (Hpath M Hsro) Hel Hst Hcr with "Hinv Hd").
  Qed.

  Lemma wp_uk_ecall_open_miss_deed (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q None -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q None)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd Hcont".
    iDestruct (file_miss_sup N c r q Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Hel Hst with "Hinv Hro Hd") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (file_miss_fam c r q (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_miss_fam c r q (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_miss_recv fsc_fs c r OffParked q cw (uvis_M W) pv
            (m !!! Regidx a1_idx) pl _ (uvis_fd W) rv fdv'
            (Hpath (uvis_M W) Himg) Hel with "Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hd) | #HT]".
    - iLeft. iFrame "Hd". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iFrame "HT".
      iApply (uk_open_taint_fd_of_arm (ukn_fd N) l (uvis_fd W) fdv' rv
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  3.  read AT THAT DESCRIPTOR: the bytes ARE the deed's               *)
  (* =================================================================== *)

  Lemma wp_uk_read_deed_learns (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jo : option Z)
      (bs : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE: "fd is open for reading on the deed's own inode" *)
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    (* THE DEED, at a fraction, and the console flag the claim's legs read *)
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       (((⌜rv = (mword_of_int (-1) : mword 64)⌝
          ∨ (∃ off : nat,
               ⌜Z.to_nat (bv_unsigned rv)
                = ard_count (Z.to_nat cnt) off (length bs)⌝ ∗
               ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                  gb j = bs !!! (off + j)%nat⌝))
         ∗ fdq r q (Some (i, bs)))
        ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh #Hm #Hinv Hd Hbuf Hcont".
    iDestruct (file_read_piece fsc_fs c r q jo (Some (i, bs)) i γo Heq
                 with "Hinv Hm Hd") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo
                 (file_read_recv c r q jo (Some (i, bs))) with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N)
                 (file_read_recv c r q jo (Some (i, bs)))) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' rv dd gb W M' fdv' cw' cs')
      "%Hdd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N)
                    (file_read_recv c r q jo (Some (i, bs)))) W
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
    iDestruct (file_read_arms_learn c r q jo i bs γo P cnt rv M'
                 (m !!! Regidx a1_idx) k gb Hlin Himg ltac:(lia)
                 with "Hcore") as "Hlearn".
    iApply ("Hcont" $! h' rv gb with "Hufdh Hlearn Hrun Hbuf").
  Qed.

  (* ...AND AT A NON-NEGATIVE COUNT THERE IS NO -1 ARM AT ALL (lane
     READ-RELAY, deliverable 2).  This is what CAT-WALK's read arm applies:
     cat asks for 512 bytes into a buffer it owns, so the only -1 the
     kernel could answer -- readi's copyout faulting -- names a byte of
     THAT buffer the process cannot be written at, and the leaf's own
     mapped row says every byte of it can be.  The program pays nothing
     new: the row comes out of [wp_uk_ecall_read_file] beside the resume
     image, and the ONE added premise is [0 <= cnt], which kills fileread's
     sign guard -- the other, and now only other, -1.  So cat's
     "cat: read error" tail is unreachable, and the alternative [RCReadErr]
     design/app-file.md section 5.3 (c) declined to add stays out. *)
  Lemma wp_uk_read_deed_learns_mapped (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jo : option Z)
      (bs : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (0 <= cnt)%Z ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffParked)) -∗
       (* THE COUNT'S BOUND, ON BOTH ARMS (lane OFF-LINK, for CAT-ENTRY-2):
          a read of [cnt] bytes returns at most [cnt] whether the deed's
          receipt came back as content or as the taint, which is what
          [UCatKernel.cat_w_of_link] refutes its short write with. *)
       ⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat cnt)%nat⌝ -∗
       (((∃ off : nat,
            ⌜Z.to_nat (bv_unsigned rv)
             = ard_count (Z.to_nat cnt) off (length bs)⌝ ∗
            ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
               gb j = bs !!! (off + j)%nat⌝)
         ∗ fdq r q (Some (i, bs)))
        ∨ (fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcnt0 Hcapk Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh #Hm #Hinv Hd Hbuf Hcont".
    iDestruct (file_read_piece fsc_fs c r q jo (Some (i, bs)) i γo Heq
                 with "Hinv Hm Hd") as "Hau".
    iDestruct (udepwf_st_read_file N m pc wb i γo
                 (file_read_recv c r q jo (Some (i, bs))) with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_file N h m pc cnt k f avail
              (read_file_fam (ukn_pay N)
                 (file_read_recv c r q jo (Some (i, bs)))) fd
              (FdOpen true wb (FdInode i γo OffParked))
              Hn Hcnt Hcapk Hfdv Hfdlt Hal4 with "Hi Hrun Hsb Hufdh Hbuf").
    iIntros (h' rv dd gb W M' fdv' cw' cs')
      "%Hdd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N)
                    (file_read_recv c r q jo (Some (i, bs)))) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 rv M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hperm & %Hwf & %Hlazy & Hcore)".
    (* THE MAPPED ROW, straight out of the leaf's own hand *)
    assert (Hmap : forall j : nat, (j < k)%nat ->
              uva_wmapped P
                (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))))
      by (intros j Hj; exact (Hnf P j Hwf Hperm (Hlazy Hlz) Hj)).
    rewrite Hkey.
    rewrite /fileread_extra_core /=.
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (file_read_arms_learn_mapped c r q jo i bs γo P cnt rv M'
                 (m !!! Regidx a1_idx) k gb Hlin Himg Hcnt0 ltac:(lia) Hmap
                 with "Hcore") as "[%Hbnd Hlearn]".
    iApply ("Hcont" $! h' rv gb with "Hufdh [%] Hlearn Hrun Hbuf").
    exact Hbnd.
  Qed.

  (* ...AND THE SAME LEAF AT ANY HANDLE [D] THAT NAMES THE DESCRIPTOR'S
     STATE against the key's table -- the one read walk's own agreement
     premise ([UkRunSys.wp_uk_ecall_read_at]).  Two instances: the tail
     handle ([UserFd.ufd], the corollary below, as [UkCatDeed] and
     [UkFileDev.file_read] take it) and the LEDGER at a standard slot
     ([UserFd.ustd], [UkFileDev.file_read_std]: a held input whose open
     landed in a closed standard slot, lane leaf-payers). *)
  Lemma wp_uk_read_deed_learns_held_at (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jo : option Z)
      (bs : list (bv 8)) (p : nat) (D : iProp Σ) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (0 <= cnt)%Z ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall fdv : list fdstate,
       ufd_auth (ukn_fd N) fdv -∗ D -∗
       ⌜fd_st_of_key (m !!! Regidx a0_idx) fdv = FdOpen true wb (FdInode i γo OffHeld)⌝) ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    D -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    (* the program's own half, at the position it believes the file is at *)
    UserOff.uoff γo p -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       D -∗
       (* THE COUNT'S BOUND, ON BOTH ARMS (lane OFF-LINK, for CAT-ENTRY-2):
          a read of [cnt] bytes returns at most [cnt] whether the deed's
          receipt came back as content or as the taint, which is what
          [UCatKernel.cat_w_of_link] refutes its short write with. *)
       ⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat cnt)%nat⌝ -∗
       ((⌜Z.to_nat (bv_unsigned rv)
          = ard_count (Z.to_nat cnt) p (length bs)⌝ ∗
         ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
            gb j = bs !!! (p + j)%nat⌝ ∗
         UserOff.uoff γo (p + Z.to_nat (bv_unsigned rv))%nat ∗
         fdq r q (Some (i, bs)))
        ∨ (UserOff.uoff γo p ∗ fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcnt0 Hcapk Hal4 Hag.
    iIntros "#Hbr #Hrb #Hi Hrun HD #Hm #Hinv Hd Hu Hbuf Hcont".
    iDestruct (file_read_piece_adv fsc_fs c r q jo (Some (i, bs)) i γo p Heq
                 with "Hbr Hrb Hinv Hm Hd Hu") as "Hau".
    iDestruct (udepwf_st_read_file_held N m pc wb i γo
                 (file_read_recv_hand c r q jo (Some (i, bs)) γo p)
                 with "Hau") as "Hsb".
    iApply (wp_uk_ecall_read_at N h m pc cnt k f avail
              (read_file_fam (ukn_pay N)
                 (file_read_recv_hand c r q jo (Some (i, bs)) γo p)) D
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv
                          = FdOpen true wb (FdInode i γo OffHeld))
              Hn Hcnt Hcapk Hal4 Hag with "Hi Hrun [Hsb] HD Hbuf").
    { rewrite /udepwf_st /udepwf_K. iExact "Hsb". }
    iIntros (h' rv dd gb W M' fdv' cw' cs')
      "%Hdd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive HD Hpost Hrun Hbuf".
    cbv beta in Hkey.
    iDestruct (spost_at_read_elim uslot
                 (xfam_rdf (ukn_pay N)
                    (file_read_recv_hand c r q jo (Some (i, bs)) γo p)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W)
                 rv M' fdv' cw' cs' H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (P) "(%Hperm & %Hwf & %Hlazy & Hcore)".
    (* THE MAPPED ROW, straight out of the leaf's own hand *)
    assert (Hmap : forall j : nat, (j < k)%nat ->
              uva_wmapped P
                (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))))
      by (intros j Hj; exact (Hnf P j Hwf Hperm (Hlazy Hlz) Hj)).
    rewrite Hkey.
    rewrite /fileread_extra_core /=.
    assert (Hc2 : sys_rw_count (m !!! Regidx a2_idx) = cnt)
      by (rewrite /sys_rw_count /trunc32; exact Hcnt).
    rewrite Hc2.
    iDestruct (file_read_arms_learn_mapped_hand c r q jo i bs γo p P cnt rv M'
                 (m !!! Regidx a1_idx) k gb Hlin Himg Hcnt0 ltac:(lia) Hmap
                 with "Hcore") as "[%Hbnd Hlearn]".
    iApply ("Hcont" $! h' rv gb with "HD [%] Hlearn Hrun Hbuf").
    exact Hbnd.
  Qed.

  Lemma wp_uk_read_deed_learns_held (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (cnt : Z) (k : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) (i : Z) (γo : gname)
      (c : file_fixed) (r : file_names) (q : Qp) (jo : option Z)
      (bs : list (bv 8)) (p : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_read ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32) = cnt ->
    (0 <= cnt)%Z ->
    (Z.to_nat cnt <= k)%nat ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    fdq r q (Some (i, bs)) -∗
    (* the program's own half, at the position it believes the file is at *)
    UserOff.uoff γo p -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (rv : mword 64) (gb : nat -> bv 8),
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
       (* THE COUNT'S BOUND, ON BOTH ARMS (lane OFF-LINK, for CAT-ENTRY-2):
          a read of [cnt] bytes returns at most [cnt] whether the deed's
          receipt came back as content or as the taint, which is what
          [UCatKernel.cat_w_of_link] refutes its short write with. *)
       ⌜(Z.to_nat (bv_unsigned rv) <= Z.to_nat cnt)%nat⌝ -∗
       ((⌜Z.to_nat (bv_unsigned rv)
          = ard_count (Z.to_nat cnt) p (length bs)⌝ ∗
         ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
            gb j = bs !!! (p + j)%nat⌝ ∗
         UserOff.uoff γo (p + Z.to_nat (bv_unsigned rv))%nat ∗
         fdq r q (Some (i, bs)))
        ∨ (UserOff.uoff γo p ∗ fdq r q (Some (i, bs)) ∗ file_taint c)) -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hcnt Hcnt0 Hcapk Hfdv Hfdlt Hal4.
    apply (wp_uk_read_deed_learns_held_at N h m pc cnt k f avail fd wb i γo c r q jo bs p
             (UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo OffHeld)))
             Heq Hn Hcnt Hcnt0 Hcapk Hal4
             (ufd_key_agree N fd (FdOpen true wb (FdInode i γo OffHeld))
                (m !!! Regidx a0_idx) Hfdv Hfdlt)).
  Qed.


  (* =================================================================== *)
  (*  4.  open(`f`, O_WRONLY|O_CREATE|O_TRUNC) AT THE DEED                *)
  (*                                                                      *)
  (*  THE REDIRECT CHILD'S OWN CALL (sh.c:395, mode [0x601]), as a U-tier *)
  (*  corollary: [UkTreeCreate.wp_uk_ecall_open_create_own] is the mould  *)
  (*  and [FileOpen.file_open_create_au] / [file_open_create_recv] are    *)
  (*  the two halves it is built from.  ONE DEED IN (the bundle supplies  *)
  (*  its own truncate piece at every mode -- lane F-OPEN-3), and the     *)
  (*  two outcomes [file_open_create_recv] folds the receipt into come    *)
  (*  out as two arms here, in [UkShRedirAns.ush_open_ans2]'s shape: a    *)
  (*  descriptor at a type [redir_K] pins -- an INODE with `f` present    *)
  (*  and EMPTY at it, or the taint -- and [-1] with the deed home.       *)
  (*                                                                      *)
  (*  THE LEAF IS A VISIBLE PARAMETER here exactly as in sections 1-3:    *)
  (*  the corollary is stated over [UkRunSys.wp_uk_ecall_open_recv_img],  *)
  (*  the PARKED-offset member, so lane OFF-HAND-5's held twin            *)
  (*  ([wp_uk_ecall_open_recv_img_held]) re-instantiates it by changing   *)
  (*  exactly one application and adding [UserOff.uoff] to the post.      *)
  (* =================================================================== *)

  (* The deposit's family for a CREATE-mode open.  [UConsOpen.xfam_open]
     fills row 15's read-only slots and [UkTreeCreate.xfam_tree] its create
     legs, but NEITHER reaches [of_Fex] or [of_Ft] -- the file claim is the
     first application that answers at the exists observation and at the
     truncate, so it needs its own filling.  Every other row stays inert. *)
  Definition xfam_fcreate (omo : offmode) (P : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Q : Z -> iProp Σ) : sfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       (* row 15, at O_CREATE and O_TRUNC: the walk cursor, create's four
          legs, the exists observation and the truncate *)
       of_P     := P;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := Farm;
       of_Fun   := Fun;
       of_Fok   := Fok;
       of_Fex   := Fex;
       of_Fo    := Fo;
       of_Ft    := Ft;
       of_om    := omo;
       wf_Q     := fun _ => True%I;
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       kf_lend  := emp%I;
       kf_xpay  := Q;
       rf_ret   := fun _ _ => True%I;
       rf_in    := fun _ => True%I;
       rf_pq    := fun _ => True%I;
       rf_pqe   := fun _ _ => True%I;
       wf_Qe    := fun _ _ => True%I;
       cl_P     := True%I |}.

  Definition file_create_fam (omo : offmode) (c : file_fixed) (r : file_names)
      (jo : option Z)
      (n : nat) (s : dst) (g : gname) (Q : Z -> iProp Σ) : sfam :=
    xfam_fcreate omo (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I)
      (file_arm_fam c r jo s g) (file_unarm_fam c r s g)
      (file_cre_fam c r jo s g) (file_dlk_fam c r n s g)
      (file_odlk_fam c r n s g)
      (file_trunc_fam c r s) Q.

  (* THE LEDGER TIE, at ANY descriptor type.  [UkTreeRead.tree_open_fd_tie]
     is this at [FdInode]; the create's F-OK admits a found DEVICE too
     ([FileOpen]'s section 6, second hole), so this file needs the tie
     where the type is a parameter.  The proof reads nothing of it. *)
  Lemma file_open_fd_tie (sts fdv' : list fdstate) (rv : mword 64)
      (rb wb : bool) (t : fdtype) (fd : nat) (rd wr : bool) (ty : fdtype) :
    length sts = NOFILE ->
    rv = (mword_of_int (Z.of_nat fd) : mword 64) ->
    (fd < NOFILE)%nat ->
    fdv' = <[fd := FdOpen rd wr ty]> sts ->
    open_fd_rcpt rb wb t sts rv fdv' ->
    FdOpen rd wr ty = FdOpen rb wb t.
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
                   = <[fd := FdOpen rb wb t]> sts)
      by exact (eq_trans (eq_sym Hfdv) Hfdv0).
    pose proof (list_lookup_insert sts fd (FdOpen rd wr ty) Hfdlt) as Hl1.
    pose proof (list_lookup_insert sts fd (FdOpen rb wb t) Hfdlt) as Hl2.
    rewrite Hins in Hl1. rewrite Hl2 in Hl1. congruence.
  Qed.

  (* THE PAYLOAD THE 0x601 CALL'S FD ARM HANDS THE ROUND, AT THE
     DESCRIPTOR'S TYPE -- the name lane SH-ROUND instantiates
     [UkShRedirAns.ush_open_call2]'s [K] at (its [Kf] is
     [FileOpen.file_open_pay], unchanged).  ONE ARM AND THE TAINT: the
     descriptor is on an INODE and `f` is present and EMPTY there.  The
     device is gone (lane F-OPEN-6, [FileOpen.file_dev_refute] at the
     permit's named EXISTS branch); the taint sits OUTSIDE the type
     equation because a tainted claim promises nothing about the file
     system and cannot refute the kernel's [FdDevice] arm. *)
  Definition redir_K (omo : offmode) (c : file_fixed) (r : file_names)
      (ty : fdtype) : iProp Σ := file_open_fd_K omo c r ty.

  (* THE DEPOSIT: the 0x601 bundle, from one deed. *)
  Lemma file_create_sup (N : uk_names Σ) (omo : offmode) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (s : dst) (g : gname)
      (ls : list wordline) (ws : wordline) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗
    file_cons_cred c r jo -∗ fl_lb c ls -∗
    esc_key c r n s g -∗ fesc_res r s g -∗
    udepwf_at N m pc USYS_open (file_create_fam omo c r jo n s g (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Hnp Hstart Hlast Hin Hokw.
    iIntros "#Hinv #Hro #Hm #Hlb #Hwit Hres".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_create_fam omo c r jo n s g (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_create_fam xfam_fcreate of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (file_open_create_au fsc_fs c r jo n s g ls ws cw M pv
              (m !!! Regidx a1_idx) pl Heq (Hpath M Hsro) Hnp Hstart Hlast
              Hin Hokw with "Hinv Hm Hlb Hwit Hres").
  Qed.

  (* ---- THE COROLLARY: "close 1, then open `f` at 0x601, from the deed".
     THREE arms, and the second is the one the redirect round runs on: a
     descriptor on an INODE, WITH `f` PRESENT AND EMPTY AT THAT INODE --
     and nothing else (lane F-OPEN-5).  F-OPEN-3's "or the deed unmoved"
     disjunct is GONE: the escrow inside the claim ([AppFile]'s section
     2a) lets the create's [dirlookup] observation read the claim's own
     value AT ITS OWN VIEW, which at an ABSENT deed contradicts the found
     entry.  The third arm is the found DEVICE create's F-OK admits; it
     too now reports `f` present and empty at a row of the claim's own
     (the claim's reading at the OPEN's observation instant refutes the
     device outright on the permit's EXISTS branch), so the call's whole
     non-failing outcome is ONE sentence about the deed.
     [FileOpen.file_open_pay] is still the [-1] payload lane SH-ROUND
     instantiates [UkShRedirAns.ush_open_ans2]'s [Kf] at.

     THE DEED GOES IN WHOLE and is PARKED HERE, not by the caller: this
     wrapper opens the escrow before the call ([AppFile.file_escrow_park])
     and closes it after (inside [FileOpen.file_open_create_recv]), so
     nothing of the escrow protocol is visible above this line. *)
  Lemma wp_uk_ecall_open_create_deed (N : uk_names Σ) (omo : offmode) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (jo : option Z) (s : dst)
      (ls : list wordline) (ws : wordline) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    om_trunc (m !!! Regidx a1_idx) = true ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    file_cons_cred c r jo -∗
    fl_lb c ls -∗
    fown r s -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched and the deed
           comes home -- unmoved, or at the entry a create that fired
           before the failure left standing, or the taint *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ file_open_pay c r s)
        (* ...OR THE HANDLE, AND IT IS ONE ARM (lane F-OPEN-6): the
           descriptor's type is whatever the kernel installed and
           [redir_K] says what that is -- an INODE with `f` empty at it,
           or the taint.  The found-DEVICE arm create's F-OK admits is
           refuted at the permit's named EXISTS branch and has no arm of
           its own any more. *)
        ∨ (∃ (fd : nat) (ty : fdtype),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx)) ty) ∗
             redir_K omo c r ty)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hnp Hstart Hlast Hin Hokw.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv #Hm #Hlb Hown Hcont".
    (* THE PARK: the deed's half goes into the claim, and what comes out
       is the ticket, the one-shot token and the ledger key *)
    iApply fupd_wp.
    iMod (file_escrow_park fsc_fs c r s ⊤ ltac:(set_solver) Heq
            with "Hinv Hown") as (n g) "(#Hkey & Htok & Htk)".
    iModIntro.
    iAssert (fesc_res r s g) with "[Htk Htok]" as "Hres".
    { rewrite /fesc_res. iFrame "Htk Htok". }
    iDestruct (file_create_sup N omo c r jo n s g ls ws cw Img pv m pc pl Heq Hpath
                 Ha0 Hcr Hnp Hstart Hlast Hin Hokw
                 with "Hinv Hro Hm Hlb Hkey Hres") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (file_create_fam omo c r jo n s g (ukn_pay N)) cw Img Hn Hal4
              with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_create_fam omo c r jo n s g (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_create_fam xfam_fcreate of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_create_recv fsc_fs c omo r jo n s g cw (uvis_M W) pv
                 (m !!! Regidx a1_idx) pl (uvis_fd W) rv fdv' ⊤
                 ltac:(set_solver) Htr
                 ltac:(exact (Hpath (uvis_M W) Himg))
                 Hlast Heq with "Hinv Hkey Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hpay) | Hfdarm]".
    - (* THE CALL FAILED *)
      iLeft. iFrame "Hpay". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - (* THE HANDLE.  The receipt names the type the kernel installed and
         [redir_K] is what the claim says about it. *)
      iDestruct "Hfdarm" as (t0) "[%Hrcpt Hpay]".
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
        assert (Hlt0 : (fd0 < NOFILE)%nat).
        { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1 & _).
      rewrite (file_open_fd_tie (uvis_fd W) fdv' rv
                 (om_readable (m !!! Regidx a1_idx))
                 (om_writable (m !!! Regidx a1_idx))
                 t0 fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iExists fd, t0. iFrame "Hal". rewrite /redir_K.
      iFrame "Hpay". iPureIntro. exact (conj Hr1 Hlt1).
  Qed.


  (* =================================================================== *)
  (*  5.  THE SAME THREE OPENS AT A PATH THAT LIVES IN HEAP DATA          *)
  (*      (lane CAT-WALK-2, K1).                                          *)
  (*                                                                      *)
  (*  Sections 1, 2 and 4 read the path argument off [utext_img] -- the   *)
  (*  TEXT half -- which is exactly the X-and-NOT-W pages.  cat's path is *)
  (*  [argv[1]] and the redirect child's is sh's line buffer: both are    *)
  (*  heap DATA, so neither can discharge a [utext] premise and no        *)
  (*  cat-side or sh-side file can work around it.                        *)
  (*                                                                      *)
  (*  [UkRunSys.uimg_view] is the row itself, boxed -- whatever I hold,  *)
  (*  it lets the key's own image be read at [Img].  The three suppliers  *)
  (*  and the three corollaries below are sections 1/2/4 verbatim with    *)
  (*  that in place of [utext_img] -- THE BODIES ARE UNCHANGED, only      *)
  (*  which persistent view supplies [uimg_sub] moves -- and the [_d]     *)
  (*  members are one application each at the DATA image                  *)
  (*  ([UserHeap.ubyteq … DfracDiscarded], the argv's own bytes).  The    *)
  (*  text members stay where they are: sections 1/2/4 are untouched.     *)
  (* =================================================================== *)

  Lemma file_open_sup_v (N : uk_names Σ) (omo : offmode) (c : file_fixed) (r : file_names)
      (q1 q2 : Qp) (i : Z) (bs : list (bv 8))
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ uimg_view N Img -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    udepwf_at N m pc USYS_open (file_open_fam omo c r q1 q2 i bs (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hinv #Hro Hd1 Hd2".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (uimg_view_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_open_fam omo c r q1 q2 i bs (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (file_open_plain_au fsc_fs c r q1 q2 i bs cw M pv
              (m !!! Regidx a1_idx) pl _ Heq (Hpath M Hsro) Hel Hst Htr
              with "Hinv Hd1 Hd2").
  Qed.

  Lemma file_miss_sup_v (N : uk_names Σ) (c : file_fixed) (r : file_names)
      (q : Qp) (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile)
      (pc : mword 64) (pl : list (bv 8)) (cw : Z) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    app_inv fsc_fs -∗ uimg_view N Img -∗
    fdq r q None -∗
    udepwf_at N m pc USYS_open (file_miss_fam c r q (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Hel Hst. iIntros "#Hinv #Hro Hd".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (uimg_view_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_miss_fam c r q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (file_open_miss_au fsc_fs c r q cw M pv (m !!! Regidx a1_idx) pl
              _ _ _ _ Heq (Hpath M Hsro) Hel Hst Hcr with "Hinv Hd").
  Qed.

  Lemma file_create_sup_v (N : uk_names Σ) (omo : offmode) (c : file_fixed) (r : file_names)
      (jo : option Z) (n : nat) (s : dst) (g : gname)
      (ls : list wordline) (ws : wordline) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    app_inv fsc_fs -∗ uimg_view N Img -∗
    file_cons_cred c r jo -∗ fl_lb c ls -∗
    esc_key c r n s g -∗ fesc_res r s g -∗
    udepwf_at N m pc USYS_open (file_create_fam omo c r jo n s g (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Hnp Hstart Hlast Hin Hokw.
    iIntros "#Hinv #Hro #Hm #Hlb #Hwit Hres".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (uimg_view_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (file_create_fam omo c r jo n s g (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [file_create_fam xfam_fcreate of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (file_open_create_au fsc_fs c r jo n s g ls ws cw M pv
              (m !!! Regidx a1_idx) pl Heq (Hpath M Hsro) Hnp Hstart Hlast
              Hin Hokw with "Hinv Hm Hlb Hwit Hres").
  Qed.

  Lemma wp_uk_ecall_open_read_deed_v (N : uk_names Σ) (omo : offmode) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    uimg_view N Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched, and so are both
           fractions *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...OR THE HANDLE, ON THE DEED'S OWN INUM *)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdInode i γo omo)) ∗
             (* ...AND THE HALF THE PUBLISH HANDED OUT (kernel stream, L4):
                nothing at mode PARK, [UserOff.uoff γo 0] at mode HAND. *)
             foff_pub omo γo ∗
             fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...or the application is tainted, and the LEDGER comes back
           (lane CAT-GEOM-2): either untouched, or beside a handle
           [UserFd.ualloc_hi] takes off it *)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd1 Hd2 Hcont".
    iDestruct (file_open_sup_v N omo c r q1 q2 i bs Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Htr Hel Hst with "Hinv Hro Hd1 Hd2") as "Hsb".
    iApply (wp_uk_ecall_open_recv_gimg N h m pc l avail
              (file_open_fam omo c r q1 q2 i bs (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_open_fam omo c r q1 q2 i bs (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_open_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_recv_file fsc_fs c r omo q1 q2 i bs cw (uvis_M W) pv
            (m !!! Regidx a1_idx) pl _ (uvis_fd W) rv fdv'
            (Hpath (uvis_M W) Himg) Hel Hst Htr with "Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hd1 & Hd2) | [Hok | #HT]]"; last first.
    { iRight. iRight. iFrame "HT".
      iApply (uk_open_taint_fd_of_arm (ukn_fd N) l (uvis_fd W) fdv' rv
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd". }
    - iDestruct "Hok" as (γo) "(%Hrcpt & Hpub & Hd1 & Hd2)".
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
                 (om_writable (m !!! Regidx a1_idx)) i γo omo fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iLeft. iExists fd, γo. iFrame "Hal Hpub Hd1 Hd2". iPureIntro.
      exact (conj Hr1 Hlt1).
    - iLeft. iFrame "Hd1 Hd2". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  Lemma wp_uk_ecall_open_miss_deed_v (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    uimg_view N Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q None -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q None)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Hel Hst.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv Hd Hcont".
    iDestruct (file_miss_sup_v N c r q Img pv m pc pl cw Heq Hpath
                 Ha0 Hcr Hel Hst with "Hinv Hro Hd") as "Hsb".
    iApply (wp_uk_ecall_open_recv_gimg N h m pc l avail
              (file_miss_fam c r q (ukn_pay N))
              cw Img Hn Hal4 with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_miss_fam c r q (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_miss_fam xfam_open of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_miss_recv fsc_fs c r OffParked q cw (uvis_M W) pv
            (m !!! Regidx a1_idx) pl _ (uvis_fd W) rv fdv'
            (Hpath (uvis_M W) Himg) Hel with "Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hd) | #HT]".
    - iLeft. iFrame "Hd". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iFrame "HT".
      iApply (uk_open_taint_fd_of_arm (ukn_fd N) l (uvis_fd W) fdv' rv
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* THE DEPOSIT INSTANCE IS THIS LEMMA'S OWN (the PROGRAM STREAM), and it
     is a PER-LEMMA binder and not a section variable -- [UEchoFile]'s
     header says why: a section variable of a class type is a LOCAL
     INSTANCE and the elaboration of this file explodes.  Left ambient, the
     [urun]s below are at [UexecExecInst.uprogSG_gen] and sh's redirect
     child, which runs at [uprogSG_free], cannot apply them; a landed
     caller that resolves ambiently gets [uprogSG_gen] exactly as before. *)
  Lemma wp_uk_ecall_open_create_deed_v `{PSx : uprogSG Σ}
      (N : uk_names Σ) (omo : offmode) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (jo : option Z) (s : dst)
      (ls : list wordline) (ws : wordline) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    om_trunc (m !!! Regidx a1_idx) = true ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    uimg_view N Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    file_cons_cred c r jo -∗
    fl_lb c ls -∗
    fown r s -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched and the deed
           comes home -- unmoved, or at the entry a create that fired
           before the failure left standing, or the taint *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ file_open_pay c r s)
        (* ...OR THE HANDLE, AND IT IS ONE ARM (lane F-OPEN-6): the
           descriptor's type is whatever the kernel installed and
           [redir_K] says what that is -- an INODE with `f` empty at it,
           or the taint.  The found-DEVICE arm create's F-OK admits is
           refuted at the permit's named EXISTS branch and has no arm of
           its own any more. *)
        ∨ (∃ (fd : nat) (ty : fdtype),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx)) ty) ∗
             redir_K omo c r ty)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hnp Hstart Hlast Hin Hokw.
    iIntros "#Hi #Hro Hrun Hcwd Hstd #Hinv #Hm #Hlb Hown Hcont".
    (* THE PARK: the deed's half goes into the claim, and what comes out
       is the ticket, the one-shot token and the ledger key *)
    iApply fupd_wp.
    iMod (file_escrow_park fsc_fs c r s ⊤ ltac:(set_solver) Heq
            with "Hinv Hown") as (n g) "(#Hkey & Htok & Htk)".
    iModIntro.
    iAssert (fesc_res r s g) with "[Htk Htok]" as "Hres".
    { rewrite /fesc_res. iFrame "Htk Htok". }
    iDestruct (file_create_sup_v N omo c r jo n s g ls ws cw Img pv m pc pl Heq Hpath
                 Ha0 Hcr Hnp Hstart Hlast Hin Hokw
                 with "Hinv Hro Hm Hlb Hkey Hres") as "Hsb".
    iApply (wp_uk_ecall_open_recv_gimg (PS := PSx) N h m pc l avail
              (file_create_fam omo c r jo n s g (ukn_pay N)) cw Img Hn Hal4
              with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (file_create_fam omo c r jo n s g (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [file_create_fam xfam_fcreate of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    iApply fupd_wp.
    iMod (file_open_create_recv fsc_fs c omo r jo n s g cw (uvis_M W) pv
                 (m !!! Regidx a1_idx) pl (uvis_fd W) rv fdv' ⊤
                 ltac:(set_solver) Htr
                 ltac:(exact (Hpath (uvis_M W) Himg))
                 Hlast Heq with "Hinv Hkey Hrc") as "Hans".
    iModIntro.
    iApply ("Hcont" $! h' rv with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & %Hfdv & Hpay) | Hfdarm]".
    - (* THE CALL FAILED *)
      iLeft. iFrame "Hpay". iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' rv Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - (* THE HANDLE.  The receipt names the type the kernel installed and
         [redir_K] is what the claim says about it. *)
      iDestruct "Hfdarm" as (t0) "[%Hrcpt Hpay]".
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
        assert (Hlt0 : (fd0 < NOFILE)%nat).
        { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1 & _).
      rewrite (file_open_fd_tie (uvis_fd W) fdv' rv
                 (om_readable (m !!! Regidx a1_idx))
                 (om_writable (m !!! Regidx a1_idx))
                 t0 fd rd wr ty
                 Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
      iRight. iExists fd, t0. iFrame "Hal". rewrite /redir_K.
      iFrame "Hpay". iPureIntro. exact (conj Hr1 Hlt1).
  Qed.

  Lemma wp_uk_ecall_open_read_deed_d (N : uk_names Σ) (omo : offmode) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q1 q2 : Qp)
      (i : Z) (bs : list (bv 8)) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N) DfracDiscarded a b) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q1 (Some (i, bs)) -∗ fdq r q2 (Some (i, bs)) -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched, and so are both
           fractions *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...OR THE HANDLE, ON THE DEED'S OWN INUM *)
        ∨ (∃ (fd : nat) (γo : gname),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx))
                       (FdInode i γo omo)) ∗
             (* ...AND THE HALF THE PUBLISH HANDED OUT (kernel stream, L4):
                nothing at mode PARK, [UserOff.uoff γo 0] at mode HAND. *)
             foff_pub omo γo ∗
             fdq r q1 (Some (i, bs)) ∗ fdq r q2 (Some (i, bs)))
        (* ...or the application is tainted, and the LEDGER comes back
           (lane CAT-GEOM-2): either untouched, or beside a handle
           [UserFd.ualloc_hi] takes off it *)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst.
    iIntros "#Hi #Hdi Hrun Hcwd Hstd #Hinv Hd1 Hd2 Hcont".
    iApply (wp_uk_ecall_open_read_deed_v N omo h m pc l avail c r q1 q2 i bs cw Img pv pl
              Heq Hn Hal4 Hpath Ha0 Hcr Htr Hel Hst
              with "Hi [] Hrun Hcwd Hstd Hinv Hd1 Hd2 Hcont").
    iApply (uimg_view_data N Img with "Hdi").
  Qed.

  Lemma wp_uk_ecall_open_miss_deed_d (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = false ->
    path_elems pl = [fname_f] ->
    um_start_of cw pl = ROOTINO ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N) DfracDiscarded a b) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    fdq r q None -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ fdq r q None)
        ∨ (uk_open_taint_fd (ukn_fd N) l rv ∗ file_taint c)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Hel Hst.
    iIntros "#Hi #Hdi Hrun Hcwd Hstd #Hinv Hd Hcont".
    iApply (wp_uk_ecall_open_miss_deed_v N h m pc l avail c r q cw Img pv pl
              Heq Hn Hal4 Hpath Ha0 Hcr Hel Hst
              with "Hi [] Hrun Hcwd Hstd Hinv Hd Hcont").
    iApply (uimg_view_data N Img with "Hdi").
  Qed.

  Lemma wp_uk_ecall_open_create_deed_d `{PSx : uprogSG Σ}
      (N : uk_names Σ) (omo : offmode) (h : CpuId)
      (m : regfile) (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : file_fixed) (r : file_names) (jo : option Z) (s : dst)
      (ls : list wordline) (ws : wordline) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    om_trunc (m !!! Regidx a1_idx) = true ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    list_basics.last (path_elems pl) = Some fname_f ->
    ws ∈ ls -> EchoDisc.line_ok ws ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ([∗ map] a ↦ b ∈ Img, ubyteq (ukn_d N) DfracDiscarded a b) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    app_inv fsc_fs -∗
    file_cons_cred c r jo -∗
    fl_lb c ls -∗
    fown r s -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* the call failed: the ledger is back untouched and the deed
           comes home -- unmoved, or at the entry a create that fired
           before the failure left standing, or the taint *)
        (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗ ustd (ukn_fd N) l
         ∗ file_open_pay c r s)
        (* ...OR THE HANDLE, AND IT IS ONE ARM (lane F-OPEN-6): the
           descriptor's type is whatever the kernel installed and
           [redir_K] says what that is -- an INODE with `f` empty at it,
           or the taint. *)
        ∨ (∃ (fd : nat) (ty : fdtype),
             ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
              /\ (fd < NOFILE)%nat⌝ ∗
             ualloc (ukn_fd N) l fd
               (FdOpen (om_readable (m !!! Regidx a1_idx))
                       (om_writable (m !!! Regidx a1_idx)) ty) ∗
             redir_K omo c r ty)) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hnp Hstart Hlast Hin Hokw.
    iIntros "#Hi #Hdi Hrun Hcwd Hstd #Hinv #Hm #Hlb Hown Hcont".
    iApply (wp_uk_ecall_open_create_deed_v (PSx := PSx)
              N omo h m pc l avail c r jo s ls ws cw Img pv pl
              Heq Hn Hal4 Hpath Ha0 Hcr Htr Hnp Hstart Hlast Hin Hokw
              with "Hi [] Hrun Hcwd Hstd Hinv Hm Hlb Hown Hcont").
    iApply (uimg_view_data N Img with "Hdi").
  Qed.

End UkFileOpen.

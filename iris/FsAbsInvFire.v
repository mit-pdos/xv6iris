(* FsAbsInvFire.v -- THE GENERIC DISCHARGERS: every AU bundle an fs-syscall
   contract asks its caller for, satisfied by a client that knows nothing
   about the abstract state, at receipts that say nothing.

   WHAT THIS IS FOR.  The AU contracts ([SysOpenDefs], [SpecSysMknod],
   [SysUnlinkDefs], [SpecSysRead]/[SpecFileread], [SpecSysWrite]/
   [SpecFilewrite], [SpecCreate]) take, beside the
   landed frame, a bundle of caller-supplied fupds: the walk premise (one
   [ax_hop] per path element, fired at the era lend) and the commits (one
   per linearization instant, handed the kernel's HALF of the abstract
   map's authority -- app-instances.md section 2).  A consumer that wants
   to run a syscall WITHOUT learning anything about the abstract state --
   the dispatch, today -- still has to supply that bundle.  Each lemma
   below supplies one piece, with every receipt [True] and every cursor
   [True]: the read-kind commits hand the lent half straight back; the
   write-kind commits hand it back with THE CALLER'S STEP beside the
   phase-2 fupd.

   THE STEP, AND WHERE A CLIENT THAT KNOWS NOTHING GETS IT.  A write-kind
   shape owes [AppInv.app_step]: "the application's claim about the
   pre-view survives the delta" (app-instances.md section 7).  A client that
   answers for NO abstract state pays it out of [AppInv.app_sup], the
   SUPPLY: the application's claim held of every view, which is exactly what
   makes every delta free ([AppInv.app_step_acc], one line, no side
   condition).  So every write-kind discharger below takes the supply -- a
   PERSISTENT CREDENTIAL, born at boot and carried down the trap round -- and
   NO invariant at all: it opens nothing, and it needs neither the row to
   exist nor the mask to admit [appN].  A VERIFIED program pays the same
   [app_step] from its own deposit instead, at its own families; these
   lemmas are what the DISPATCHER hands the contracts in the meantime, and
   what the deposit class's supply law is proved from
   ([UexecExecInst]).

   THE MASK.  Every commit is at [appE] = [↑appN] ([AppInv]'s note).  The
   read/write dischargers open NOTHING of their own: the offset shadow is
   lent and returned unmoved (the piece-shape rule), and the kernel's fire
   lemma advances it out of the descriptor row's [OffGv.off_user_inv]. *)
(* Require block: SysOpenDefs.v's, VERBATIM (durable-notes: trimmed imports
   have OOM'd the build, and a class name that is not in scope silently becomes
   a section VARIABLE), plus this file's own lines. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import FileInvDefs.               (* [is_ftable], [fnode] *)
Require Import ProcInv.
Require Import SpecSysOpen.     (* sys_open's ONE contract: [open_in], the
                                   key its input is stated at *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   would shadow the superblock CELL
                                   ADDRESSES the frame below threads *)
Require Import SysMknodDefs.  (* [delta_create], [cre_pre],
                                   [npar_elems], [abs_view_insert] *)
Require Import SysWriteDefs.  (* [wchunks]: the chain's node count, and
                                   the splice algebra it re-exports *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
Require Import FsAbsEraMknod.   (* [npar_walk_pre_era], [npar_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
(* ...and this file's own: the other commit definitions and the invariant.
   FsAbs stays LAST (its own rule), so these go above the block's tail. *)
Require Import SysOpenDefs.      (* [aopen/atrunc_commit_at], [namei_walk_pre_era], [open_au_pre_*] *)
Require Import SpecSysChdir.       (* [chdir_au_pre]: the walk premise + open's commit *)
Require Import SpecSysMknod.       (* [mknod_au_pre]: the one contract's bundle *)
Require Import SysUnlinkDefs.    (* [uent/utgt/dmiss_commit_at] *)
Require Import SpecSysUnlink.      (* [unlink_au_pre]: the one contract's bundle *)
Require Import SpecSysLink.        (* [link_commits] (round E2, lane E2-L) *)
Require Import FsAbsReadFire.      (* [aread_commit_at] *)
Require Import FsAbsWriteFire.     (* [awrite_full_at], [awrite_chain] *)
Require Import AppInv.             (* [appN]/[appE], [app_sup], [app_step_acc]: the supply and the step it pays *)
Require Import FsAbsDefs.          (* [abs_view_lookup_is_Some] *)
Require Import FsCfg.              (* [fscfg]: the fs configuration is AMBIENT *)
Require Import UartSentLoc.        (* [uart_sent_nil]: the free trace seed *)
Require Import SpecFilewrite.      (* [filewrite_in]: the one keyed input *)
Require Import SpecFileread.       (* [fileread_in]: read's keyed input *)
Require Import SpecSysRead.        (* in the require block; the dischargers
                                      are stated at the BARE descriptor state *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section FsAbsInvFire.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (*  1.  The walk premises: every hop says yes, every cursor is [True]   *)
  (* ------------------------------------------------------------------ *)

  (* the trivial hop family is [FsAbsEra.ax_hops_triv], and the trivial
     [ep_start] is [ep_start_triv] beside it: they live there because
     [SpecCreate]'s own bundle unit needs them and sits below this file. *)

  Lemma fsabs_open_walk (γfs : fs_names) (cw : Z) :
    ⊢ namei_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /namei_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply ax_hops_triv.
  Qed.

  Lemma fsabs_mknod_walk (γfs : fs_names) (cw : Z) :
    ⊢ npar_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /npar_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply ax_hops_triv.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  The commits, one lemma per shape                                *)
  (* ------------------------------------------------------------------ *)

  (* the read-kind commits hand the lent half straight back and open
     nothing *)
  (* ...each at the TRIVIAL PAIR, which is the shape the bundles take a
     piece in: the AU conjoined with its refund, both trivial. *)
  Lemma fsabs_aopen Γ :
    ⊢ pf_at (aopen_commit_at Γ appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iApply pf_at_triv. rewrite /aopen_commit_at. iIntros (I i a) "%Hi Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dlookup Γ :
    ⊢ pf_at (dlookup_commit_at Γ appE) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iApply pf_at_triv. rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dmiss Γ :
    ⊢ pf_at (dmiss_commit_at Γ appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iApply pf_at_triv. rewrite /dmiss_commit_at. iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* the write-kind commits owe the step: paid out of the SUPPLY, the
     credential a client that answers for no abstract state runs on *)
  Lemma fsabs_atrunc (γfs : fs_names) :
    app_sup -∗
    pf_at (atrunc_commit_at (fs_gamma_L γfs) appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (atrunc_commit_at_unit γfs appE with "Hsup").
  Qed.

  Lemma fsabs_acre (γfs : fs_names) (c : absnode) :
    app_sup -∗
    pf_at (acre_commit_at (fs_gamma_L γfs) appE c) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (acre_commit_at_unit γfs appE c with "Hsup").
  Qed.

  (* CREATE'S CHILD LEGS (round E2, lane E2-C): the arm and the unarm, both
     unfired, at the trivial families -- what the dispatcher's mknod and
     open(O_CREATE) arms hand the AU create. *)
  Lemma fsabs_child (γfs : fs_names) (c : absnode) :
    app_sup -∗
    cre_child_unfired (fs_gamma_L γfs) c (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /cre_child_unfired.
    iSplitR.
    { iApply pf_at_triv.
      iApply (aarm_commit_at_unit γfs appE c with "Hsup"). }
    iApply pf_at_triv.
    iApply (aunarm_commit_at_unit γfs appE with "Hsup").
  Qed.

  Lemma fsabs_uent (γfs : fs_names) :
    app_sup -∗
    pf_at (uent_commit_at (fs_gamma_L γfs) appE) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (uent_commit_at_unit γfs appE with "Hsup").
  Qed.

  Lemma fsabs_utgt (γfs : fs_names) :
    app_sup -∗
    pf_at (utgt_commit_at (fs_gamma_L γfs) appE) (pfam_triv (fun _ _ => True%I)).
  Proof.
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (utgt_commit_at_unit γfs appE with "Hsup").
  Qed.

  (* THE READ AND WRITE COMMITS LEND THE OFFSET TOO (OffGv.v), AND TAKE IT
     BACK UNMOVED: the piece-shape rule (design/fs-syscall-specs.md section
     4) forbids a piece from asking its client to return a kernel-owned
     ghost moved, so the advance is the kernel fire lemma's
     ([FsAbsReadFire.arf_read_fire], [FsAbsWriteFire.wrf_awrite_fire]/
     [wrf_apart_fire]), out of the descriptor row's own [off_user_inv].
     What that buys here is the whole point of the ARM: the dischargers
     below need NO offset resource, so read's and write's bundles are
     payable at every key from nothing. *)

  (* READ'S ONE PIECE, at the trivial receipt AND the trivial refund: the
     conjunction the unified contract's inode arm takes ([AU /\ R]), so the
     kernel may eliminate to either side.  FROM NOTHING. *)
  Lemma fsabs_aread Γ (i : Z) (γo : gname) :
    ⊢ pf_at (aread_commit_at Γ appE i γo) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iApply pf_at_triv. iApply aread_commit_at_unit.
  Qed.

  Lemma fsabs_awrite_chain (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k cnt : nat) :
    app_sup -∗
    awrite_chain (fs_gamma_L γfs) appE i γo M ua (fun _ => True%I) k cnt.
  Proof.
    iIntros "#Hsup".
    iApply (awrite_chain_unit γfs appE i γo M ua k cnt with "Hsup").
  Qed.

  (* READ'S WHOLE INPUT, at the trivial receipt and the trivial refund, AND
     AT A BARE DESCRIPTOR STATE -- which is the form the ARM's deposit class
     needs: a process's key names its descriptor STATES
     ([SpecArgfd.fd_st_of_key]) and never the kernel's [ofile] pointer
     array, so the discharger cannot be stated at [SpecArgfd.sys_fd_st].
     The dispatcher's arm bridges the two with
     [SpecArgfd.sys_fd_st_of_key].

     IT COSTS ITS CLIENT NOTHING AT ALL, at every key: read's one piece
     lends the offset shadow and takes it back unmoved, so no descriptor
     row and no offset invariant is needed, and no application step is paid
     -- a read moves no row.  This is what makes read's bundle payable by
     an arbitrary user process under the ARM. *)
  Lemma fsabs_fileread_in (st : fdstate) :
    ⊢ fileread_in st (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    rewrite /fileread_in.
    destruct st as [| rb wb ty]; [done |].
    destruct rb; [| done].
    destruct ty as [i γo | | ma]; [| done | done].
    iApply (fsabs_aread (fs_gamma_L fsc_fs) i γo).
  Qed.



  (* WRITE'S WHOLE INPUT, at the trivial cursor and the free seed, and at a
     BARE descriptor state for [fsabs_fileread_in]'s reason.

     THE CONSOLE ARM IS FREE: the devsw pin left the input for
     FILEWRITE/SYSWRITE's Coq premise list (a dispatcher discharges it by
     [reflexivity] off [fwn_wp fn = devsw_write_val]), so what is left is
     the trace seed, and that is the unit of the mono-list algebra
     ([UartSentLoc.uart_sent_nil]).  THE INODE ARM needs no offset resource
     any more: the chain's nodes take the shadow back unmoved.  So this
     input is payable at EVERY key out of the application step alone --
     which is what the ARM asks of it.

     BUPD-SHAPED, not fupd: the ARM's minting law is a basic update
     ([UexecSG.v]'s header -- the trace seed is the mono-list algebra's unit
     and belongs to the LAW's modality, not to a supplier), and the console
     arm's seed is the only thing here that needs one at all. *)
  Lemma fsabs_filewrite_in (st : fdstate) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64) :
    app_sup -∗ |==> filewrite_in st n M ua (fun _ => True%I) [].
  Proof.
    iIntros "#Hsup".
    rewrite /filewrite_in.
    destruct st as [| rb wb ty]; [by iModIntro |].
    destruct wb; [| by iModIntro].
    destruct ty as [i γo | | ma].
    - iModIntro.
      iApply (fsabs_awrite_chain fsc_fs i γo M ua 0%nat (wchunks n)
                with "Hsup").
    - by iModIntro.
    - case_decide as Hc; [| by iModIntro].
      iMod (uart_sent_nil fsc_uart) as "#Hseed". iModIntro. iExact "Hseed".
  Qed.



  (* ------------------------------------------------------------------ *)
  (*  3.  The bundles the sealed contracts take, at the live Γ            *)
  (* ------------------------------------------------------------------ *)

  Lemma fsabs_open_pre_plain (γfs : fs_names) (cw : Z) :
    app_sup -∗
    open_au_pre_plain (fs_gamma_L γfs) γfs cw (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /open_au_pre_plain.
    iSplitR; [iApply fsabs_open_walk |].
    iSplitR; [iApply fsabs_aopen | iApply (fsabs_atrunc with "Hsup")].
  Qed.

  (* ...and the fs-facing half of exec's AU bundle
     ([SpecSysExec.sys_exec_au_pre] minus its slot wand), which is open's
     walk and open's commit at [True] -- what [UexecExecMint] mints the
     process's exec bundle out of.  Read-kind only, so nothing of the
     application's is needed. *)
  Lemma fsabs_exec_half Γ (γfs : fs_names) (cw : Z) :
    ⊢ namei_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      ∗ pf_at (aopen_commit_at Γ appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen].
  Qed.

  Lemma fsabs_open_pre_create (γfs : fs_names) (cw : Z) :
    app_sup -∗
    open_au_pre_create (fs_gamma_L γfs) γfs cw (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /open_au_pre_create.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hsup") |].
    iSplitR; [iApply fsabs_dlookup |].
    iSplitR; [iApply fsabs_aopen |].
    iSplitR; [iApply (fsabs_atrunc with "Hsup") | iApply (fsabs_child with "Hsup")].
  Qed.

  (* ...AND THE ONE INPUT sys_open's contract takes, at the key the code
     branches on: the dispatcher hands this and never chooses an arm
     itself ([SpecSysOpen.open_in]). *)
  Lemma fsabs_open_in (γfs : fs_names) (cw : Z) (vom : mword 64) :
    app_sup -∗
    open_in (fs_gamma_L γfs) γfs cw vom (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /open_in. destruct (om_create vom).
    - iApply (fsabs_open_pre_create with "Hsup").
    - iApply (fsabs_open_pre_plain with "Hsup").
  Qed.

  Lemma fsabs_mknod_pre (γfs : fs_names) (cw : Z) (ma mi : Z) :
    app_sup -∗
    mknod_au_pre (fs_gamma_L γfs) γfs cw ma mi (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /mknod_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hsup") |].
    iSplitR; [iApply fsabs_dlookup | iApply (fsabs_child with "Hsup")].
  Qed.

  (* ...and chdir's (lane C3): open's walk premise at any start beside
     open's plain commit -- what the dispatcher's chdir arm hands the AU
     contract at the True families *)
  Lemma fsabs_chdir_pre Γ (γfs : fs_names) (cw : Z) :
    ⊢ chdir_au_pre Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    rewrite /chdir_au_pre.
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen].
  Qed.

  (* LINK'S THREE LEGS (round E2, lane E2-L).  Unlike the AU bundles there
     is no walk premise here: [wp_sys_link_sconf] is the LANDED contract
     strengthened in place (ruling Q-c), so its two walks stay behind
     [SpecNamei]/[SpecNameiparent] and only the commits cross.  The bundle's
     own [_unit] proof lives in [SpecSysLink] beside the definitions; this
     is the [fsabs_*]-family name the dispatcher's link arm reads. *)
  Lemma fsabs_link_pre (γfs : fs_names) :
    app_sup -∗
    link_commits (fs_gamma_L γfs) (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ => True%I)).
  Proof. iIntros "#Hsup". iApply (link_commits_unit γfs with "Hsup"). Qed.

  Lemma fsabs_unlink_pre (γfs : fs_names) (cw : Z) :
    app_sup -∗
    unlink_au_pre (fs_gamma_L γfs) γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /unlink_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_uent with "Hsup") |].
    iSplitR; [iApply (fsabs_utgt with "Hsup") |].
    iSplitR; [iApply fsabs_dlookup | iApply fsabs_dmiss].
  Qed.

End FsAbsInvFire.

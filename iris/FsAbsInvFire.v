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
Require Import SysWriteDefs.  (* [wchunks]: the chain's node count, and
                                   the splice algebra it re-exports *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
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
Require Import SpecConsolewrite.   (* [cons_out_chain_of_licence]: the
                                      generic write's console arm, paid out
                                      of the supply's OUTPUT LICENCE *)
Require Import UserPerm.   (* [uperm], [perm_of] -- RULING WR-TB *)
Require Import SpecFilewrite.      (* [filewrite_in]: the one keyed input *)
Require Import SpecFileread.       (* [fileread_in]: read's keyed input *)
Require Import PipeQueue.          (* [pipe_rpay_taint] / [pipe_wpay_taint]: the pipe arms' price, paid by [RiscvPtsto.app_taint] *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Import Defs.
Require Import CtxIdDefs.

Local Open Scope Z_scope.

Section FsAbsInvFire.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  (* the era's generation: [SpecFileread.fileread_in]'s console arm is
     era-indexed since lane CONS-IO milestone C ([WpUart.cons_read_pay] at
     [S gen_id]), and [SpecFilewrite.filewrite_in]'s is too. *)
  Context `{GEN : GenId}.

  (* ------------------------------------------------------------------ *)
  (*  1.  The walk premises: every hop says yes, every cursor is [True]   *)
  (* ------------------------------------------------------------------ *)

  (* the trivial hop family is [FsAbsEra.ax_hops_triv], and the trivial
     [ep_start] is [ep_start_triv] beside it: they live there because
     [SpecCreate]'s own bundle unit needs them and sits below this file. *)

  Lemma fsabs_open_walk (γfs : fs_names) (cw : Z) :
    ⊢ namei_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof using .
    rewrite /namei_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply ax_hops_triv.
  Qed.

  Lemma fsabs_mknod_walk (γfs : fs_names) (cw : Z) :
    ⊢ npar_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof using .
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
  Proof using .
    iApply pf_at_triv. rewrite /aopen_commit_at. iIntros (I i a) "%Hi Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dlookup Γ :
    ⊢ pf_at (dlookup_commit_at Γ appE) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    iApply pf_at_triv. rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dmiss Γ :
    ⊢ pf_at (dmiss_commit_at Γ appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iApply pf_at_triv. rewrite /dmiss_commit_at. iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* the write-kind commits owe the step: paid out of the SUPPLY, the
     credential a client that answers for no abstract state runs on *)
  Lemma fsabs_atrunc (γfs : fs_names) :
    app_sup -∗
    pf_at (atrunc_commit_at (fs_gamma_L γfs) appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (atrunc_commit_at_unit γfs appE with "Hsup").
  Qed.

  (* ...and the GUARDED trunc piece open's bundles actually take: at
     [om_trunc vom = false] nothing is owed and the supply is not even
     read.  This is the tightening's payoff on the generic side -- the
     piece is now payable more easily, never less. *)
  (* THE PERMIT IS FREE HERE (lane F-OPEN-3), exactly as [Pd] is below: a
     family that answers at EVERY file row answers at the permitted one
     and never reads the permit ([SysOpenDefs.open_trunc_piece_of_all]),
     so the generic supply is one line at whatever permit the bundle it
     is handed to carries. *)
  Lemma fsabs_trunc_piece (γfs : fs_names) (vom : mword 64)
      (Kt : Z -> iProp Σ) :
    app_sup -∗
    open_trunc_piece (fs_gamma_L γfs) vom Kt (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup".
    iApply open_trunc_piece_of_all. iApply (fsabs_atrunc with "Hsup").
  Qed.

  (* [Pd] IS FREE HERE (lane TL-3K): the generic application ignores the
     parent cursor, so it discharges the commit at whatever cursor the
     bundle it is being handed to carries. *)
  Lemma fsabs_acre (γfs : fs_names) (c : absnode) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ)) :
    app_sup -∗
    pf_at (acre_commit_at (fs_gamma_L γfs) appE c Pd Farm)
      (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (acre_commit_at_unit γfs appE c Pd Farm with "Hsup").
  Qed.

  (* CREATE'S CHILD LEGS (round E2, lane E2-C): the arm and the unarm, both
     unfired, at the trivial families -- what the dispatcher's mknod and
     open(O_CREATE) arms hand the AU create. *)
  Lemma fsabs_child (γfs : fs_names) (c : absnode) :
    app_sup -∗
    cre_child_unfired (fs_gamma_L γfs) c (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)).
  Proof using .
    iIntros "#Hsup". rewrite /cre_child_unfired.
    iSplitR.
    { iApply pf_at_triv.
      iApply (aarm_commit_at_unit γfs appE c with "Hsup"). }
    iApply pf_at_triv.
    iApply (aunarm_of_arm_unit γfs appE _ with "Hsup").
  Qed.

  Lemma fsabs_uent (γfs : fs_names) (Pd : Z -> iProp Σ) :
    app_sup -∗
    pf_at (uent_commit_at (fs_gamma_L γfs) appE Pd)
      (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup". iApply pf_at_triv.
    iApply (uent_commit_at_unit γfs appE Pd with "Hsup").
  Qed.

  Lemma fsabs_utgt (γfs : fs_names) :
    app_sup -∗
    pf_at (utgt_commit_at (fs_gamma_L γfs) appE) (pfam_triv (fun _ _ => True%I)).
  Proof using .
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
  Proof using .
    iApply pf_at_triv. iApply aread_commit_at_unit.
  Qed.

  Lemma fsabs_awrite_chain (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k cnt : nat) :
    app_sup -∗
    awrite_chain (fs_gamma_L γfs) appE i γo M ua n (fun _ => True%I) k cnt.
  Proof using .
    iIntros "#Hsup".
    iApply (awrite_chain_unit γfs appE i γo M ua n k cnt with "Hsup").
  Qed.

  (* READ'S WHOLE INPUT, at the trivial receipt and the trivial refund, AND
     AT A BARE DESCRIPTOR STATE -- which is the form the ARM's deposit class
     needs: a process's key names its descriptor STATES
     ([FdSlots.fd_st_of_key]) and never the kernel's [ofile] pointer
     array, so the discharger cannot be stated at [SpecArgfd.sys_fd_st].
     The dispatcher's arm bridges the two with
     [SpecArgfd.sys_fd_st_of_key].

     IT COSTS ITS CLIENT NOTHING AT ALL, at every key: read's one piece
     lends the offset shadow and takes it back unmoved, so no descriptor
     row and no offset invariant is needed, and no application step is paid
     -- a read moves no row.  This is what makes read's bundle payable by
     an arbitrary user process under the ARM. *)
  (* ...AND THE CONSOLE ARM IS PAID FROM THE SUPPLY ITSELF (app-echo.md,
     lane CONS-CURSOR, C3, and the LEASE ruling).  A read of the console
     takes [ConsoleInv.cons_acc fsc_cons app_rdcred Rd] -- ONE ARM, two
     disjuncts -- and this is the TAINTED one: the caller hands in the
     credential it already holds, which is [app_sup] itself (the left arm
     of [AppInv.app_rdcred]), and owes [Rd]
     at every position, which at the generic family's [fun _ _ => True] is
     free.

     THAT IS WHY THE ARM IS NOT AN EXCLUSIVE TOKEN.  The law below is a
     FIELD of [UexecSG]'s class ([xv6_sbundle_of_supply_ne]), stated at
     [□ ssupply], and has to hold at EVERY number for an arbitrary program:
     a console arm demanding the reader token would not merely be
     unprovable there -- taken as a [□] premise it is INCONSISTENT (open it
     three times and hold [ghost_var γ (1/2) _] thrice), which would make
     every generic corollary vacuous while the audit still printed the
     thirteen.  So the arm is payable from a PERSISTENT credential, and the
     one the generic slot already runs on is the one it takes. *)
  (* AT AN ARBITRARY PAYLOAD [P] (app-echo.md, "SH-LINE RULING", R1).
     read's input is a wand from the caller's exit payload, and the
     generic family's is [True] ([UexecSG.sexit_pay_pt]) -- but the same
     proof pays at ANY [P], and has to: a leaf re-keys the family it mints
     at its OWN payload, which for a program with a real one is linear.
     Nothing is duplicated: what the console arm owes is [∀ cur dc, |==>
     P ∗ True], and a [∀] over a constant is that constant -- the caller
     takes its [P] back at ONE position, the one the read landed on. *)
  (* ...AND THE CONSOLE LICENCE PAYS THE CONSOLE ARM'S SECOND HALF (lane
     CONS-IO, milestone B, B4).  Read's console deposit carries the
     boundary's read link as well as the ring's payment, and the licence
     that pays it comes off the TAINT ([WpUart.cons_licence_of_taint],
     lane SUP-ONE; it used to be a third conjunct of
     [UexecExecInst.xv6_ssupply]) -- which since the redesign is the
     port's ONE licence, good for any event -- so this arm costs the
     generic process nothing new: it claims nothing about what came in
     ([rf_in] at [fun _ => True]) and the licence hands over a link at any
     [ws] whatever. *)
  (* ...AND THE PIPE ARM IS PAID BY THE TAINT (design/pipe.md, "The byte
     queue"): the generic process holds no fragment of any pipe, so its
     read disconnects the pipe's ghost state at the application's taint --
     the kill credential, which the supply already carries. *)
  (* ...AND THE LICENCE IS THE TAINT'S (lane SUP-ONE): it was a premise
     here, carried in the generic supply beside the taint; it is now the
     interface's own law ([RiscvPtsto.ai_lic],
     [WpUart.cons_licence_of_taint]) and is read off the credential the
     pipe arm already takes. *)
  Lemma fsabs_fileread_in (st : fdstate) (n : Z) (P : iProp Σ) :
    app_sup -∗ app_taint -∗
    fileread_in st n (pfam_triv (fun _ _ _ _ => True%I))
                     (fun _ _ => True%I) (fun _ => True%I)
                     (fun _ => True%I) (fun _ _ => True%I) P.
  Proof using .
    rewrite /fileread_in. iIntros "#Hsup #Htaint HP".
    iDestruct (WpUart.cons_licence_of_taint with "Htaint") as "#Hilic".
    destruct st as [| rb wb ty]; [iExact "HP" |].
    destruct rb; [| iExact "HP"].
    destruct ty as [i γo om | γp | ma].
    - (* the inode arm at the row's mode (lane OFF-LINK-4): at a HELD row
         the generic tier has no [UserOff.uoff] to lend and takes the RIGHT
         arm -- the same commit beside the taint it already holds *)
      destruct om as [|].
      + iFrame "HP". iApply (fsabs_aread (fs_gamma_L fsc_fs) i γo).
      + iFrame "HP". iRight. iSplitL; [| iExact "Htaint"].
        iApply (fsabs_aread (fs_gamma_L fsc_fs) i γo).
    - iFrame "HP". by iApply pipe_rpay_taint.
    - case_decide; [| iExact "HP"].
      iSplitL "HP".
      + iApply (ConsoleInv.cons_acc_cred fsc_cons app_rdcred
                  (fun (_ _ : nat) => (P ∗ True)%I)).
        * rewrite /ConsoleInv.cons_dirty_cred. iModIntro.
          by iApply app_rdcred_of_sup.
        * iIntros (cur dc). iModIntro. by iFrame "HP".
      + iApply (WpUart.cons_read_pay_triv with "Hilic").
  Qed.



  (* WRITE'S WHOLE INPUT, at the trivial cursor and the free seed, and at a
     BARE descriptor state for [fsabs_fileread_in]'s reason.

     THE CONSOLE ARM IS NOT FREE ANY MORE (lane OUT-FUPD; see the note on
     [fsabs_filewrite_in] below): the devsw pin left the input for
     FILEWRITE/SYSWRITE's Coq premise list (a dispatcher discharges it by
     [reflexivity] off [fwn_wp fn = devsw_write_val]), and what is left is
     the OUTPUT CHAIN, paid out of the supply's licence.  THE INODE ARM
     needs no offset resource
     any more: the chain's nodes take the shadow back unmoved.  So this
     input is payable at EVERY key out of the application step alone --
     which is what the ARM asks of it.

     BUPD-SHAPED, not fupd: the ARM's minting law is a basic update
     ([UexecSG.v]'s header -- the trace seed is the mono-list algebra's unit
     and belongs to the LAW's modality, not to a supplier), and the console
     arm's seed is the only thing here that needs one at all. *)
  (* ...AND THE CONSOLE ARM IS NO LONGER FREE (lane OUT-FUPD).  It used to
     be the trace seed [WpUart.uart_sent γu []], the mono-list unit,
     mintable by anyone.  Under the resource claim the point of the whole
     lane is that the kernel can say WHO may write, so an arbitrary
     process's [write(2)] on the console is paid out of the OUTPUT LICENCE
     -- and the application sets that licence's price.  IT IS NOT A
     PREMISE HERE ANY MORE (lane SUP-ONE): the price is a law of the
     application's interface ([RiscvPtsto.ai_lic]), so the TAINT this
     lemma already takes for the pipe arm buys the licence too
     ([WpUart.cons_licence_of_taint]). *)
  Lemma fsabs_filewrite_in (st : fdstate) (n : Z)
      (pmv : gmap (mword 27) uperm) (sz : Z) (lz : bool)
      (M : gmap Z (bv 8)) (ua : mword 64) :
    app_sup -∗ app_taint -∗
    |==> filewrite_in pmv sz lz st n M ua (fun _ => True%I) (fun _ _ => True%I).
  Proof using .
    iIntros "#Hsup #Htaint".
    iDestruct (cons_licence_of_taint with "Htaint") as "#Hlic".
    rewrite /filewrite_in.
    destruct st as [| rb wb ty]; [by iModIntro |].
    destruct wb; [| by iModIntro].
    destruct ty as [i γo om | γp | ma].
    - (* THE INODE ARM, keyed on the row's offset mode (lane OFF-LINK-4).
         At a PARKED row the supply builds the chain as it always did; at a
         HELD one the generic tier has no [UserOff.uoff] to lend and takes
         the RIGHT arm -- the same chain beside the taint it already holds
         (the survey's Fact A).  That is the owner's principle at this
         coupling, and it is why a held descriptor costs the generic proof
         nothing. *)
      destruct om as [|]; iModIntro.
      + iApply (fsabs_awrite_chain fsc_fs i γo M ua n 0%nat (wchunks n)
                  with "Hsup").
      + rewrite /filewrite_in_held. iRight. iSplitR; [| iExact "Htaint"].
        iApply (fsabs_awrite_chain fsc_fs i γo M ua n 0%nat (wchunks n)
                  with "Hsup").
    - (* the pipe arm: the taint *)
      iModIntro. by iApply pipe_wpay_taint.
    - iModIntro. iApply (cons_out_chain_of_licence with "Hlic").
  Qed.



  (* ------------------------------------------------------------------ *)
  (*  3.  The bundles the sealed contracts take, at the live Γ            *)
  (* ------------------------------------------------------------------ *)

  (* AT THE PATH THE CALLER PASSED.  The generic family answers the walk at
     EVERY string ([fsabs_open_walk]), which is strictly more than the
     one-path bundle asks for, so the instance is
     [SysOpenDefs.open_au_pre_plain_of_all] and nothing else. *)
  Lemma fsabs_open_pre_plain (γfs : fs_names) (cw : Z) (pl : list (bv 8))
      (vom : mword 64) :
    app_sup -∗
    open_au_pre_plain (fs_gamma_L γfs) γfs cw pl vom (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup".
    iApply (open_au_pre_plain_of_all with "[] [] []");
      [ iApply fsabs_open_walk | iApply fsabs_aopen
      | iApply (fsabs_trunc_piece with "Hsup") ].
  Qed.

  (* ...and the fs-facing half of exec's AU bundle
     ([SpecSysExec.sys_exec_au_pre] minus its slot wand), which is open's
     walk and open's commit at [True] -- what [UexecExecMint] mints the
     process's exec bundle out of.  Read-kind only, so nothing of the
     application's is needed. *)
  Lemma fsabs_exec_half Γ (γfs : fs_names) (cw : Z) :
    ⊢ namei_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      ∗ pf_at (aopen_commit_at Γ appE) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen].
  Qed.

  Lemma fsabs_open_pre_create (γfs : fs_names) (cw : Z) (pl : list (bv 8))
      (Nm : FsTree.fname -> Prop) (vom : mword 64) :
    app_sup -∗
    open_au_pre_create (fs_gamma_L γfs) γfs cw pl Nm vom (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup".
    iApply (open_au_pre_create_of_all with "[] [] [] [] [] []");
      [ iApply fsabs_mknod_walk | iApply (fsabs_acre with "Hsup")
      | iApply fsabs_dlookup | iApply fsabs_aopen
      | iApply (fsabs_trunc_piece with "Hsup") | iApply (fsabs_child with "Hsup") ].
  Qed.

  (* ...AND THE ONE INPUT sys_open's contract takes, at the key the code
     branches on: the dispatcher hands this and never chooses an arm
     itself ([SpecSysOpen.open_in]). *)
  (* ...at the READING of trapframe argument 0: the generic family owes the
     bundle at whatever string the process's image holds there, and since
     it owes the walk at EVERY string the guard is simply dropped. *)
  Lemma fsabs_open_in (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64) :
    app_sup -∗
    open_in (fs_gamma_L γfs) γfs cw M pv vom (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup". rewrite /open_in. destruct (om_create vom).
    - iApply (open_au_create_at_of_all with "[] [] [] [] [] []");
        [ iApply fsabs_mknod_walk | iApply (fsabs_acre with "Hsup")
        | iApply fsabs_dlookup | iApply fsabs_aopen
        | iApply (fsabs_trunc_piece with "Hsup") | iApply (fsabs_child with "Hsup") ].
    - iApply (open_au_plain_at_of_all with "[] [] []");
        [ iApply fsabs_open_walk | iApply fsabs_aopen
        | iApply (fsabs_trunc_piece with "Hsup") ].
  Qed.

  Lemma fsabs_mknod_pre (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z) :
    app_sup -∗
    mknod_au_at (fs_gamma_L γfs) γfs cw M pv ma mi (fun _ _ => True%I)
      (fun _ _ => True%I) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup".
    iApply (mknod_au_at_of_all with "[] [] [] []");
      [ iApply fsabs_mknod_walk | iApply (fsabs_acre with "Hsup")
      | iApply fsabs_dlookup | iApply (fsabs_child with "Hsup") ].
  Qed.

  (* ...and chdir's (lane C3): open's walk premise at any start beside
     open's plain commit -- what the dispatcher's chdir arm hands the AU
     contract at the True families *)
  Lemma fsabs_chdir_pre Γ (γfs : fs_names) (cw : Z) :
    ⊢ chdir_au_pre Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
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
  Proof using . iIntros "#Hsup". iApply (link_commits_unit γfs with "Hsup"). Qed.

  (* ...AT THE SYSCALL TIER (lane TL-3C, item (M)): unlink's bundle is now
     path-fixed under the reading of argument 0, and the generic family
     tracks nothing, so it owes the walk at EVERY string and
     [unlink_au_at_of_all] instantiates that to the guarded form. *)
  Lemma fsabs_unlink_pre (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv : mword 64) :
    app_sup -∗
    unlink_au_at (fs_gamma_L γfs) γfs cw M pv (fun _ _ => True%I) (fun _ _ => True%I)
      (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    iIntros "#Hsup".
    iApply (unlink_au_at_of_all (fs_gamma_L γfs) γfs cw M pv
              with "[] [Hsup] [Hsup] [] []").
    - iApply fsabs_mknod_walk.
    - iApply (fsabs_uent with "Hsup").
    - iApply (fsabs_utgt with "Hsup").
    - iApply fsabs_dlookup.
    - iApply fsabs_dmiss.
  Qed.

End FsAbsInvFire.

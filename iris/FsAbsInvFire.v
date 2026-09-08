(* FsAbsInvFire.v -- THE GENERIC DISCHARGERS: every AU bundle an fs-syscall
   contract asks its caller for, satisfied by a client that knows nothing
   about the abstract state, at receipts that say nothing.

   WHAT THIS IS FOR.  The AU contracts ([SpecSysOpenAU], [SpecSysMknod],
   [SpecSysUnlinkAU], [SpecSysRead]/[SpecFileread], [SpecSysWrite]/
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
   pre-view survives the delta" (app-instances.md section 7).  At an
   arbitrary application record nothing is trivial -- and nothing has to
   be: the application PARKS a license in its own invariant
   ([AppInv.app_auto], the BLANKET PROMISE that its claim survives every
   one-row move), and a commit fires at [appE] with that invariant closed,
   so the discharger opens it INSIDE its own fupd, reads the license
   [▷]-shaped and persistent ([app_step_acc]) and pays.  It is the ONLY
   thing the license is still spent on: every view move on a dispatched path
   is an AU fire or a [_step], and the two movers outside a fire are
   [_same].  What changes in lane L2 is only WHO pays -- the process's
   payload, per syscall -- and the shapes do not move.  So every discharger below takes
   [AppInv.app_inv] and NO invariant of its own: the client copy this file
   used to re-sync ([FsAbsInv], deleted) is gone with its license.

   THE MASK.  Every commit is at [appE] = [↑appN] ([AppInv]'s note); the
   read/write dischargers ALSO open the process's offset shadow
   ([OffGv.off_user_inv], under [appN]) inside the commit. *)
(* Require block: SpecSysOpenAU.v's, VERBATIM (durable-notes: trimmed imports
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
Require Import FsTree.          (* [fname] *)
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   would shadow the superblock CELL
                                   ADDRESSES the frame below threads *)
Require Import SpecSysMknodAU.  (* [delta_create], [cre_pre],
                                   [mknod_parent_elems], [abs_view_insert] *)
Require Import SpecSysWriteAU.  (* [wchunks]: the chain's node count, and
                                   the splice algebra it re-exports *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
(* ...and this file's own: the other commit definitions and the invariant.
   FsAbs stays LAST (its own rule), so these go above the block's tail. *)
Require Import SpecSysOpenAU.      (* [aopen/atrunc_commit_at], [open_walk_pre_era], [open_au_pre_*] *)
Require Import SpecSysChdir.       (* [chdir_au_pre]: the walk premise + open's commit *)
Require Import SpecSysMknod.       (* [mknod_au_pre]: the one contract's bundle *)
Require Import SpecSysUnlinkAU.    (* [uent/utgt/dmiss_commit_at] *)
Require Import SpecSysUnlink.      (* [unlink_au_pre]: the one contract's bundle *)
Require Import SpecSysLink.        (* [link_commits] (round E2, lane E2-L) *)
Require Import FsAbsReadFire.      (* [aread_commit_at] *)
Require Import FsAbsWriteFire.     (* [awrite_full_at], [awrite_chain] *)
Require Import OffGv.              (* [off_user_inv], the process's half *)
Require Import AppInv.             (* [app_inv], [appN]/[appE], [app_step_acc]: the parked license *)
Require Import FsAbsDefs.          (* [abs_view_lookup_is_Some] *)
Require Import FsCfg.              (* [fscfg]: the fs configuration is AMBIENT *)
Require Import ConsoleInv.         (* [devsw_write_val_console]: the cell's pin *)
Require Import UartSentLoc.        (* [uart_sent_nil]: the free trace seed *)
Require Import SpecFilewrite.      (* [filewrite_in]: the one keyed input *)
Require Import SpecArgfd.          (* [sys_fd_st]: the descriptor-state key *)
Require Import SpecFileread.       (* [fileread_in]: read's keyed input *)
Require Import SpecSysRead.        (* [sys_read_in] *)
Require Import SpecSysWrite.       (* [sys_write_in] *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
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
    ⊢ open_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /open_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply ax_hops_triv.
  Qed.

  Lemma fsabs_mknod_walk (γfs : fs_names) (cw : Z) :
    ⊢ mknod_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /mknod_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply ax_hops_triv.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  The commits, one lemma per shape                                *)
  (* ------------------------------------------------------------------ *)

  (* the read-kind commits hand the lent half straight back and open
     nothing *)
  Lemma fsabs_aopen Γ :
    ⊢ aopen_commit_at Γ appE (fun _ _ _ => True%I).
  Proof.
    rewrite /aopen_commit_at. iIntros (I i a) "%Hi Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dlookup Γ :
    ⊢ dlookup_commit_at Γ appE (fun _ _ _ _ => True%I).
  Proof.
    rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_dmiss Γ :
    ⊢ dmiss_commit_at Γ appE (fun _ _ _ => True%I).
  Proof.
    rewrite /dmiss_commit_at. iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* the write-kind commits owe the step: paid out of the parked license,
     read off the application's invariant inside the commit's own fupd *)
  Lemma appN_appE : ↑appN ⊆ appE.
  Proof. rewrite /appE. done. Qed.

  Lemma fsabs_atrunc (γfs : fs_names) :
    app_inv γfs -∗ atrunc_commit_at (fs_gamma_L γfs) appE (fun _ _ _ => True%I).
  Proof. iIntros "#Hai". iApply (atrunc_commit_at_unit γfs appE appN_appE with "Hai"). Qed.

  Lemma fsabs_acre (γfs : fs_names) (c : absnode) :
    app_inv γfs -∗ acre_commit_at (fs_gamma_L γfs) appE c (fun _ _ _ _ => True%I).
  Proof. iIntros "#Hai". iApply (acre_commit_at_unit γfs appE c appN_appE with "Hai"). Qed.

  (* CREATE'S CHILD LEGS (round E2, lane E2-C): the arm and the unarm, both
     unfired, at the trivial families -- what the dispatcher's mknod and
     open(O_CREATE) arms hand the AU create. *)
  Lemma fsabs_child (γfs : fs_names) (c : absnode) :
    app_inv γfs -∗
    cre_child_unfired (fs_gamma_L γfs) c (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /cre_child_unfired.
    iSplitR; [iApply (aarm_commit_at_unit γfs appE c appN_appE with "Hai") |].
    iApply (aunarm_commit_at_unit γfs appE appN_appE with "Hai").
  Qed.

  Lemma fsabs_uent (γfs : fs_names) :
    app_inv γfs -∗ uent_commit_at (fs_gamma_L γfs) appE (fun _ _ _ _ => True%I).
  Proof. iIntros "#Hai". iApply (uent_commit_at_unit γfs appE appN_appE with "Hai"). Qed.

  Lemma fsabs_utgt (γfs : fs_names) :
    app_inv γfs -∗ utgt_commit_at (fs_gamma_L γfs) appE (fun _ _ => True%I).
  Proof. iIntros "#Hai". iApply (utgt_commit_at_unit γfs appE appN_appE with "Hai"). Qed.

  (* THE READ AND WRITE COMMITS TAKE THE OFFSET TOO (OffGv.v): a process
     whose half of the descriptor's offset shadow lives in the existential
     [off_user_inv] -- the generic user-mode process, whose descriptor rows
     carry exactly that ([FdSlots.foff_row]) -- opens it INSIDE the commit,
     at the commit's own mask ([foffN] sits under [appN] for this), and
     lets the kernel's half go anywhere. *)
  Lemma foffN_appE : ↑foffN ⊆ appE.
  Proof. rewrite /appE /appN /foffN. solve_ndisj. Qed.

  (* READ'S ONE PIECE, at the trivial receipt AND the trivial refund: the
     conjunction the unified contract's inode arm takes ([AU /\ R]), so the
     kernel may eliminate to either side. *)
  Lemma fsabs_aread Γ (i : Z) (γo : gname) :
    off_user_inv γo -∗
    (aread_commit_at Γ appE i γo (fun _ _ _ _ => True%I) ∧ True).
  Proof.
    iIntros "#Hoinv". iSplit; [| done]. rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iMod (off_user_inv_move appE γo _ (Z.of_nat (off + d)) foffN_appE
            with "Hoinv Hk") as "Hk".
    iModIntro. by iFrame "Ha Hk".
  Qed.

  Lemma fsabs_awrite_chain (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (k cnt : nat) :
    app_inv γfs -∗ off_user_inv γo -∗
    awrite_chain (fs_gamma_L γfs) appE i γo M ua (fun _ => True%I) k cnt.
  Proof.
    iIntros "#Hai #Hoinv".
    iInduction cnt as [| cnt] "IH" forall (k).
    { rewrite awrite_chain_0. done. }
    rewrite awrite_chain_S. iSplit; [done |]. iSplit.
    - rewrite /awrite_full_at. iIntros (I off bs bs0 nl) "%Hpre %Hby Ha Hk".
      iMod (app_step_acc_view appE γfs i I _ appN_appE
              (delta_write_absent (abs_view I) i off bs) with "Hai") as "Hstep".
      iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'".
      iMod (off_user_inv_move appE γo _ (Z.of_nat (off + length bs)) foffN_appE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Ha' Hk". iApply "IH".
    - (* the PARTIAL arm is a state fire too now (round E2, lane E2-W):
         same two phases as the full arm, at the run the short chunk landed,
         with the offset advanced by the COUNT rather than by the run *)
      rewrite /awrite_part_at.
      iIntros (I off r bs bs0 nl) "%Hpre %Hr %Hgap %Hby Ha Hk".
      iMod (app_step_acc_view appE γfs i I _ appN_appE
              (delta_write_absent (abs_view I) i off bs) with "Hai") as "Hstep".
      iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'".
      iMod (off_user_inv_move appE γo _ (Z.of_nat (off + r)) foffN_appE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Ha' Hk". iApply "IH".
  Qed.

  (* SYS_READ'S WHOLE INPUT, at the trivial receipt and the trivial refund
     -- what the DISPATCHER hands the ONE [SpecSysRead.SYSREAD] contract in
     place of the three forms it used to choose between.  Keyed on the same
     pure function the contract's arms are ([SpecArgfd.sys_fd_st]).

     IT COSTS THE DISPATCHER NOTHING IT DOES NOT ALREADY THREAD: read's one
     piece needs only the offset invariant, and that comes off the
     descriptor bundle's own persistent row family ([FdSlots.foff_row] at an
     [FdInode] IS [OffGv.off_user_inv]).  No application step is paid -- a
     read moves no row. *)
  Lemma fsabs_sys_read_in (γfd : gname) (V : pprivate) (v : mword 64)
      (sts : list fdstate) :
    fd_frags γfd sts -∗
      fd_frags γfd sts ∗
      sys_read_in V v sts (fun _ _ _ _ => True%I) True%I.
  Proof.
    iIntros "Hfr".
    (* the row family is PERSISTENT, so the bundle goes straight back: this
       syscall moves no descriptor. *)
    iAssert (foff_rows sts ∗ fd_frags γfd sts)%I with "[Hfr]"
      as "[#Hrows Hfr]".
    { rewrite /fd_frags. iDestruct "Hfr" as "(%Hl & Hs & #Hr)".
      iSplitR; [iExact "Hr" |]. iSplitR; [by iPureIntro |].
      iFrame "Hs". iExact "Hr". }
    iFrame "Hfr".
    rewrite /sys_read_in /fileread_in.
    destruct (sys_fd_st v (pv_ofile V) sts) as [| rb wb ty] eqn:Hst; [done |].
    destruct rb; [| done].
    destruct ty as [i γo | | ma]; [| done | done].
    destruct (sys_fd_st_open _ _ _ _ _ _ Hst) as (fd & fv & Hafd & Hrow).
    iDestruct (foff_rows_lookup _ _ _ Hrow with "Hrows") as "#Hoinv".
    iApply (fsabs_aread (fs_gamma_L fsc_fs) i γo with "Hoinv").
  Qed.

  (* SYS_WRITE'S WHOLE INPUT, at the trivial cursor and the free seed --
     what the DISPATCHER hands the ONE [SpecSysWrite.SYSWRITE] contract in
     place of the three it used to choose between.  It is keyed on the same
     pure function the contract's arms are ([SpecArgfd.sys_fd_st]), so
     the dispatcher's [destruct] is on THE KEY and not on a choice of
     contract.

     THE CONSOLE ARM IS CONSTRUCTIBLE FROM WHAT THE DISPATCHER HOLDS, and
     that is the thing worth checking before the walk is written: the devsw
     pin is the [fwn_wp fn = devsw_write_val] equation every consumer of
     this cone already discharges by [reflexivity], read at [CONSOLE]; the
     trace seed is free ([UartSentLoc.uart_sent_nil] mints [uart_sent γu []]
     from the unit of the mono-list algebra).  THE INODE ARM's offset
     invariant comes off the descriptor bundle's own persistent row family
     ([FdSlots.foff_row] at an [FdInode] IS [OffGv.off_user_inv]), so the
     dispatcher needs no resource it does not already thread. *)
  Lemma fsabs_sys_write_in (fn : fwrite_names) (E : coPset) (γfd : gname)
      (V : pprivate) (v : mword 64) (sts : list fdstate) (n : Z)
      (M : gmap Z (bv 8)) (ua : mword 64) :
    ↑appN ⊆ E ->
    fwn_wp fn = ConsoleInv.devsw_write_val ->
    app_inv fsc_fs -∗ fd_frags γfd sts ={E}=∗
      fd_frags γfd sts ∗
      sys_write_in fn V v sts n M ua (fun _ => True%I) [].
  Proof.
    intros HE Hwp. iIntros "#Hai Hfr".
    (* the row family is PERSISTENT, so the bundle goes straight back: this
       syscall moves no descriptor. *)
    iAssert (foff_rows sts ∗ fd_frags γfd sts)%I with "[Hfr]"
      as "[#Hrows Hfr]".
    { rewrite /fd_frags. iDestruct "Hfr" as "(%Hl & Hs & #Hr)".
      iSplitR; [iExact "Hr" |]. iSplitR; [by iPureIntro |].
      iFrame "Hs". iExact "Hr". }
    iFrame "Hfr".
    rewrite /sys_write_in /filewrite_in.
    destruct (sys_fd_st v (pv_ofile V) sts) as [| rb wb ty] eqn:Hst;
      [by iModIntro |].
    destruct wb; [| by iModIntro].
    destruct ty as [i γo | | ma].
    - destruct (sys_fd_st_open _ _ _ _ _ _ Hst) as (fd & fv & Hafd & Hrow).
      iDestruct (foff_rows_lookup _ _ _ Hrow with "Hrows") as "#Hoinv".
      iModIntro.
      iApply (fsabs_awrite_chain fsc_fs i γo M ua 0%nat (wchunks n)
                with "Hai Hoinv").
    - by iModIntro.
    - case_decide as Hc; [| by iModIntro].
      iMod (uart_sent_nil fsc_uart) as "#Hseed".
      iModIntro. iSplitR; [| iExact "Hseed"].
      iPureIntro. rewrite Hwp Hc. exact ConsoleInv.devsw_write_val_console.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  The bundles the sealed contracts take, at the live Γ            *)
  (* ------------------------------------------------------------------ *)

  Lemma fsabs_open_pre_plain (γfs : fs_names) (cw : Z) :
    app_inv γfs -∗
    open_au_pre_plain (fs_gamma_L γfs) γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /open_au_pre_plain.
    iSplitR; [iApply fsabs_open_walk |].
    iSplitR; [iApply fsabs_aopen | iApply (fsabs_atrunc with "Hai")].
  Qed.

  (* ...and the fs-facing half of exec's AU bundle
     ([SpecSysExecAU.sys_exec_au_pre] minus its slot wand), which is open's
     walk and open's commit at [True] -- what [UexecExecMint] mints the
     process's exec bundle out of.  Read-kind only, so nothing of the
     application's is needed. *)
  Lemma fsabs_exec_half Γ (γfs : fs_names) (cw : Z) :
    ⊢ open_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      ∗ aopen_commit_at Γ appE (fun _ _ _ => True%I).
  Proof.
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen].
  Qed.

  Lemma fsabs_open_pre_create (γfs : fs_names) (cw : Z) :
    app_inv γfs -∗
    open_au_pre_create (fs_gamma_L γfs) γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /open_au_pre_create.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hai") |].
    iSplitR; [iApply fsabs_dlookup |].
    iSplitR; [iApply fsabs_aopen |].
    iSplitR; [iApply (fsabs_atrunc with "Hai") | iApply (fsabs_child with "Hai")].
  Qed.

  (* ...AND THE ONE INPUT sys_open's contract takes, at the key the code
     branches on: the dispatcher hands this and never chooses an arm
     itself ([SpecSysOpen.open_in]). *)
  Lemma fsabs_open_in (γfs : fs_names) (cw : Z) (vom : mword 64) :
    app_inv γfs -∗
    open_in (fs_gamma_L γfs) γfs cw vom (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /open_in. destruct (om_create vom).
    - iApply (fsabs_open_pre_create with "Hai").
    - iApply (fsabs_open_pre_plain with "Hai").
  Qed.

  Lemma fsabs_mknod_pre (γfs : fs_names) (cw : Z) (ma mi : Z) :
    app_inv γfs -∗
    mknod_au_pre (fs_gamma_L γfs) γfs cw ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /mknod_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hai") |].
    iSplitR; [iApply fsabs_dlookup | iApply (fsabs_child with "Hai")].
  Qed.

  (* ...and chdir's (lane C3): open's walk premise at any start beside
     open's plain commit -- what the dispatcher's chdir arm hands the AU
     contract at the True families *)
  Lemma fsabs_chdir_pre Γ (γfs : fs_names) (cw : Z) :
    ⊢ chdir_au_pre Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ => True%I).
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
    app_inv γfs -∗
    link_commits (fs_gamma_L γfs) (fun _ _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ => True%I).
  Proof. iIntros "#Hai". iApply (link_commits_unit γfs with "Hai"). Qed.

  Lemma fsabs_unlink_pre (γfs : fs_names) (cw : Z) :
    app_inv γfs -∗
    unlink_au_pre (fs_gamma_L γfs) γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /unlink_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_uent with "Hai") |].
    iSplitR; [iApply (fsabs_utgt with "Hai") |].
    iSplitR; [iApply fsabs_dlookup | iApply fsabs_dmiss].
  Qed.

End FsAbsInvFire.

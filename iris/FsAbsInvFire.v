(* FsAbsInvFire.v -- THE GENERIC DISCHARGERS: every AU bundle an fs-syscall
   contract asks its caller for, satisfied by a client that knows nothing
   about the abstract state, at receipts that say nothing.

   WHAT THIS IS FOR.  The AU contracts ([SpecSysOpenAU], [SpecSysMknodAUEra],
   [SpecSysUnlinkAU], [SpecSysReadAU]/[SpecFilereadAU], [SpecSysWriteAU]/
   [SpecFilewriteAU], [SpecCreateAU]/[SpecCreateAUF]) take, beside the
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
   ([AppInv.app_auto], the moves it admits from anyone; round A: every
   one-row move), and a commit fires at [appE] with that invariant closed,
   so the discharger opens it INSIDE its own fupd, reads the license
   [▷]-shaped and persistent ([app_step_acc]) and pays.  That is the same
   license the non-AU movers pay with ([InodeRegion.ireg_top_retag_auto]);
   what changes in round B is only WHO pays -- the process's payload, per
   syscall -- and the shapes do not move.  So every discharger below takes
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
Require Import SpecSysOpen.     (* the landed contract this file states a
                                   parallel form beside; [K_sys_open],
                                   [sys_open_slots] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsTree.          (* [fname] *)
Require Import FsStateDefs.
Require Import FsBytesGamma.   (* [fs_gamma_L]: the live Γ *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   would shadow the superblock CELL
                                   ADDRESSES the frame below threads *)
Require Import SpecSysMknodAU.  (* [delta_create], [cre_pre],
                                   [mknod_parent_elems], [abs_view_insert] *)
Require Import SpecSysWriteAU.  (* [delta_write] + the splice algebra the
                                   mint justification below is cut from *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
(* ...and this file's own: the other commit definitions and the invariant.
   FsAbs stays LAST (its own rule), so these go above the block's tail. *)
Require Import SpecSysOpenAU.      (* [aopen/atrunc_commit_at], [open_walk_pre_era], [open_au_pre_*] *)
Require Import SpecSysChdirAU.     (* [chdir_au_pre]: the walk premise + open's commit (lane C3) *)
Require Import SpecSysMknodAUEra.  (* [mknod_au_pre_era] *)
Require Import SpecSysUnlinkAU.    (* [uent/utgt/dmiss_commit_at], [unlink_au_pre] *)
Require Import FsAbsReadFire.      (* [aread_commit_at] *)
Require Import FsAbsWriteFire.     (* [awrite_full_at], [awrite_chain] *)
Require Import OffGv.              (* [off_user_inv], the process's half *)
Require Import AppCfg.             (* [app_pred], [app_run]: the claim the steps are about *)
Require Import AppInv.             (* [app_inv], [appN]/[appE], [app_step_acc]: the parked license *)
Require Import FsAbsDefs.          (* [abs_view_lookup_is_Some] *)
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

  Lemma fsabs_hops (F : Z -> dfrac -> gmap fname Z -> iProp Σ)
      (ps : list fname) (n : nat) :
    ⊢ ax_hops_from F (fun _ _ => True%I) (fun _ _ => True%I) ps n.
  Proof.
    rewrite /ax_hops_from. iApply big_sepL_intro.
    iIntros "!>" (j s _). rewrite /ax_hop.
    iIntros (d ents dqv) "_ Hl". iModIntro. iFrame "Hl".
    by destruct (ents !! s).
  Qed.

  Lemma fsabs_open_walk (γfs : fs_names) (cw : Z) :
    ⊢ open_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /open_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply fsabs_hops.
  Qed.

  Lemma fsabs_mknod_walk (γfs : fs_names) (cw : Z) :
    ⊢ mknod_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /mknod_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply fsabs_hops.
  Qed.

  Lemma fsabs_ep_start (γfs : fs_names) (cw : Z) (pl : list (bv 8)) :
    ⊢ ep_start γfs cw (fun _ _ => True%I) (fun _ _ => True%I) pl.
  Proof.
    rewrite /ep_start. iIntros (r) "_". iModIntro.
    iSplit; [done |]. rewrite /ep_hops_from. iApply fsabs_hops.
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

  Lemma fsabs_aread Γ (i : Z) (γo : gname) :
    off_user_inv γo -∗
    aread_commit_at Γ appE i γo (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hoinv". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iMod (off_user_inv_move appE γo _ (Z.of_nat (off + d)) foffN_appE
            with "Hoinv Hk") as "Hk".
    iModIntro. by iFrame "Ha Hk".
  Qed.

  Lemma fsabs_awrite_chain (γfs : fs_names) (i : Z) (γo : gname) (k cnt : nat) :
    app_inv γfs -∗ off_user_inv γo -∗
    awrite_chain (fs_gamma_L γfs) appE i γo (fun _ _ _ _ => True%I) k cnt.
  Proof.
    iIntros "#Hai #Hoinv".
    iInduction cnt as [| cnt] "IH" forall (k).
    { rewrite awrite_chain_0. done. }
    rewrite awrite_chain_S. iSplit.
    - rewrite /awrite_full_at. iIntros (I off bs bs0 nl) "%Hpre Ha Hk".
      iMod (app_step_acc appE γfs i I _ appN_appE
              (abs_view_lookup_is_Some I i _ (proj1 Hpre)) with "Hai") as "Hstep".
      iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'".
      iMod (off_user_inv_move appE γo _ (Z.of_nat (off + length bs)) foffN_appE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Ha' Hk". iSplitR; [done |]. iApply "IH".
    - rewrite /awrite_part_at. iIntros (off d) "Hk".
      iMod (off_user_inv_move appE γo _ (Z.of_nat (off + d)) foffN_appE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Hk". iApply "IH".
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
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /open_au_pre_create.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hai") |].
    iSplitR; [iApply fsabs_dlookup |].
    iSplitR; [iApply fsabs_aopen | iApply (fsabs_atrunc with "Hai")].
  Qed.

  Lemma fsabs_mknod_pre_era (γfs : fs_names) (cw : Z) (ma mi : Z) :
    app_inv γfs -∗
    mknod_au_pre_era (fs_gamma_L γfs) γfs cw ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hai". rewrite /mknod_au_pre_era.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply (fsabs_acre with "Hai") | iApply fsabs_dlookup].
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

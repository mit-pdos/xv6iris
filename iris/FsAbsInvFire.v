(* FsAbsInvFire.v -- THE DISCHARGERS: every AU bundle an fs-syscall
   contract asks its caller for, satisfied out of [FsAbsInv.fsabs_inv]
   alone, at receipts that say nothing.

   WHAT THIS IS FOR.  The AU contracts ([SpecSysOpenAU], [SpecSysMknodAUEra],
   [SpecSysUnlinkAU], [SpecSysReadAU]/[SpecFilereadAU], [SpecSysWriteAU]/
   [SpecFilewriteAU], [SpecCreateAU]/[SpecCreateAUF]) take, beside the
   landed frame, a bundle of caller-supplied fupds: the walk premise (one
   [ax_hop] per path element, fired at the era lend) and the commits (one
   per linearization instant, handed the kernel's [γtop] authority).  A
   consumer that wants to run a syscall WITHOUT learning anything about
   the abstract state -- the dispatch, today -- still has to supply that
   bundle.  Each lemma below supplies one piece, with every receipt
   [True] and every cursor [True], out of the application-side invariant:
   the fupd opens [fsabsN], overwrites the client copy with the map the
   kernel lent (phase 1: the pre-map; phase 2: the post-map), and closes.

   WHY OPEN THE INVARIANT AT ALL, when the receipts are [True].  Because
   this is the seam an application-specific body strengthens: when
   [fsabs_body] says something about [av], THESE are the fupds that have
   to re-establish it at every fire point, and they already stand at the
   right mask, on the right map, at the right instant.  Nothing else in
   the tree has to learn where the fire points are.

   THE MASK.  Every commit is at [fsabsE] = [↑fsabsN] (FsAbsInv's note);
   [iInv fsabsN] inside a [={↑fsabsN}=∗] leaves the mask at [∅], which
   is what the [FsAbs*Fire] lemmas fire the commit under.

   THE LICENSE (claude-notes/design/applications.md section 2).  The body
   carries the application conjunct [FsAbsInv.fsabs_ok] of the copy's
   map, so overwriting the copy has to re-establish it at the new map.
   Every discharger and every bundle below therefore takes, beside the
   invariant, the application's LICENSE [FsAbsInv.fsabs_lic] -- the
   persistent wand "the copy may be re-synced to any map" -- and pays
   with it ([fsabs_set], through [fsabs_body_later_lic_set]).  Read-kind and
   write-kind commits alike: all of them re-sync, and under the ruled
   delta-free license that is exactly what is paid for.  The dispatcher
   holds both out of [FirstTok.fsabs_env]. *)
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
Require Import FsStateDefs.    (* [fs_gamma_L]: the live Γ *)
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
Require Import FsAbsInv.
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Section FsAbsInvFire.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ Γc : fs_view_names Σ.

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

  (* the one ghost move, packaged: open, overwrite the copy under the
     license, close.  The body is NOT timeless (its application conjunct
     is an arbitrary iProp, applications.md section 2), so it is moved
     UNDER the later: [FsAbsInv.fsabs_body_later_lic_set] strips the two
     timeless conjuncts, replaces the map on them and applies the license
     under [▷]. *)
  Lemma fsabs_set Γc (I : gmap Z fs_node) :
    fsabs_inv Γc -∗ fsabs_lic -∗ |={↑fsabsN}=> True.
  Proof.
    iIntros "#Hinv #Hlic". rewrite /fsabs_inv.
    iInv fsabsN as "Hbody" "Hclose".
    iMod (fsabs_body_later_lic_set Γc I with "Hlic Hbody") as "Hbody".
    iMod ("Hclose" with "Hbody") as "_". done.
  Qed.

  Lemma fsabs_aopen Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ aopen_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /aopen_commit_at /fsabsE.
    iIntros (I i a) "%Hi Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_atrunc Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ atrunc_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /atrunc_commit_at /fsabsE.
    iIntros (I i bs0 nl) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_dlookup Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ dlookup_commit_at Γ fsabsE (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /dlookup_commit_at /fsabsE.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_acre Γ Γc (c : absnode) :
    fsabs_inv Γc -∗ fsabs_lic -∗ acre_commit_at Γ fsabsE c (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /acre_commit_at /fsabsE.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_uent Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ uent_commit_at Γ fsabsE (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /uent_commit_at /fsabsE.
    iIntros (I d t nm ents nl a) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_utgt Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ utgt_commit_at Γ fsabsE (fun _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /utgt_commit_at /fsabsE.
    iIntros (I t a) "%Ht %Hnl Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_dmiss Γ Γc :
    fsabs_inv Γc -∗ fsabs_lic -∗ dmiss_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /dmiss_commit_at /fsabsE.
    iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  (* THE READ AND WRITE COMMITS TAKE THE OFFSET TOO (OffGv.v): a process
     whose half of the descriptor's offset shadow lives in the existential
     [off_user_inv] -- the generic user-mode process, whose descriptor rows
     carry exactly that ([FdSlots.foff_row]) -- opens it INSIDE the commit,
     at the commit's own mask ([foffN] sits under [fsabsN] for this), and
     lets the kernel's half go anywhere. *)
  Lemma foffN_fsabsE : ↑foffN ⊆ fsabsE.
  Proof. rewrite /fsabsE /fsabsN /foffN. solve_ndisj. Qed.

  Lemma fsabs_aread Γ Γc (i : Z) (γo : gname) :
    fsabs_inv Γc -∗ fsabs_lic -∗ off_user_inv γo -∗
    aread_commit_at Γ fsabsE i γo (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic #Hoinv". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
    iMod (off_user_inv_move fsabsE γo _ (Z.of_nat (off + d)) foffN_fsabsE
            with "Hoinv Hk") as "Hk".
    iModIntro. by iFrame "Ha Hk".
  Qed.

  Lemma fsabs_awrite_chain Γ Γc (i : Z) (γo : gname) (k cnt : nat) :
    fsabs_inv Γc -∗ fsabs_lic -∗ off_user_inv γo -∗
    awrite_chain Γ fsabsE i γo (fun _ _ _ _ => True%I) k cnt.
  Proof.
    iIntros "#Hinv #Hlic #Hoinv".
    iInduction cnt as [| cnt] "IH" forall (k).
    { rewrite awrite_chain_0. done. }
    rewrite awrite_chain_S. iSplit.
    - rewrite /awrite_full_at. iIntros (I off bs bs0 nl) "%Hpre Ha Hk".
      iMod (fsabs_set Γc I with "Hinv Hlic") as "_".
      iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
      iMod (fsabs_set Γc I' with "Hinv Hlic") as "_".
      iMod (off_user_inv_move fsabsE γo _ (Z.of_nat (off + length bs)) foffN_fsabsE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Ha' Hk". iSplitR; [done |]. iApply "IH".
    - rewrite /awrite_part_at. iIntros (off d) "Hk".
      iMod (off_user_inv_move fsabsE γo _ (Z.of_nat (off + d)) foffN_fsabsE
              with "Hoinv Hk") as "Hk".
      iModIntro. iFrame "Hk". iApply "IH".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  The bundles the sealed contracts take                           *)
  (* ------------------------------------------------------------------ *)

  Lemma fsabs_open_pre_plain Γ Γc (γfs : fs_names) (cw : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    open_au_pre_plain Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /open_au_pre_plain.
    iSplitR; [iApply fsabs_open_walk |].
    iSplitR; [iApply fsabs_aopen; done | iApply fsabs_atrunc; done].
  Qed.

  (* ...and the fs-facing half of exec's AU bundle
     ([SpecSysExecAU.sys_exec_au_pre] minus its slot wand), which is open's
     walk and open's commit at [True] -- what [UexecExecMint] mints the
     process's exec bundle out of. *)
  Lemma fsabs_exec_half Γ Γc (γfs : fs_names) (cw : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    open_walk_pre_era γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
    ∗ aopen_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic".
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen; done].
  Qed.

  Lemma fsabs_open_pre_create Γ Γc (γfs : fs_names) (cw : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    open_au_pre_create Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /open_au_pre_create.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_acre; done |].
    iSplitR; [iApply fsabs_dlookup; done |].
    iSplitR; [iApply fsabs_aopen; done | iApply fsabs_atrunc; done].
  Qed.

  Lemma fsabs_mknod_pre_era Γ Γc (γfs : fs_names) (cw : Z) (ma mi : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    mknod_au_pre_era Γ γfs cw ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /mknod_au_pre_era.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_acre; done | iApply fsabs_dlookup; done].
  Qed.

  (* ...and chdir's (lane C3): open's walk premise at any start beside
     open's plain commit -- what the dispatcher's chdir arm hands the AU
     contract at the True families *)
  Lemma fsabs_chdir_pre Γ Γc (γfs : fs_names) (cw : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    chdir_au_pre Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /chdir_au_pre.
    iSplitR; [iApply fsabs_open_walk | iApply fsabs_aopen; done].
  Qed.

  Lemma fsabs_unlink_pre Γ Γc (γfs : fs_names) (cw : Z) :
    fsabs_inv Γc -∗ fsabs_lic -∗
    unlink_au_pre Γ γfs cw (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv #Hlic". rewrite /unlink_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_uent; done |].
    iSplitR; [iApply fsabs_utgt; done |].
    iSplitR; [iApply fsabs_dlookup; done | iApply fsabs_dmiss; done].
  Qed.

End FsAbsInvFire.

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
   is what the [FsAbs*Fire] lemmas fire the commit under. *)
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
Require Import SpecSysMknodAUEra.  (* [mknod_au_pre_era] *)
Require Import SpecSysUnlinkAU.    (* [uent/utgt/dmiss_commit_at], [unlink_au_pre] *)
Require Import FsAbsReadFire.      (* [aread_commit_at] *)
Require Import FsAbsWriteFire.     (* [awrite_commit_at], [awrite_commits_at] *)
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

  Lemma fsabs_open_walk (γfs : fs_names) :
    ⊢ open_walk_pre_era γfs (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /open_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply fsabs_hops.
  Qed.

  Lemma fsabs_mknod_walk (γfs : fs_names) :
    ⊢ mknod_walk_pre_era γfs (fun _ _ => True%I) (fun _ _ => True%I).
  Proof.
    rewrite /mknod_walk_pre_era. iIntros (pl r) "_". iModIntro.
    iSplit; [done |]. iApply fsabs_hops.
  Qed.

  Lemma fsabs_ep_start (γfs : fs_names) (pl : list (bv 8)) :
    ⊢ ep_start γfs (fun _ _ => True%I) (fun _ _ => True%I) pl.
  Proof.
    rewrite /ep_start. iIntros (r) "_". iModIntro.
    iSplit; [done |]. rewrite /ep_hops_from. iApply fsabs_hops.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  The commits, one lemma per shape                                *)
  (* ------------------------------------------------------------------ *)

  (* the one ghost move, packaged: open, overwrite the copy, close *)
  Lemma fsabs_set Γc (I : gmap Z fs_node) :
    fsabs_inv Γc -∗ |={↑fsabsN}=> True.
  Proof.
    iIntros "#Hinv". rewrite /fsabs_inv.
    iInv fsabsN as ">Hbody" "Hclose".
    iMod (fsabs_body_set Γc I with "Hbody") as "Hbody".
    iMod ("Hclose" with "Hbody") as "_". done.
  Qed.

  Lemma fsabs_aopen Γ Γc :
    fsabs_inv Γc -∗ aopen_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /aopen_commit_at /fsabsE.
    iIntros (I i a) "%Hi Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_atrunc Γ Γc :
    fsabs_inv Γc -∗ atrunc_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /atrunc_commit_at /fsabsE.
    iIntros (I i bs0 nl) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_dlookup Γ Γc :
    fsabs_inv Γc -∗ dlookup_commit_at Γ fsabsE (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /dlookup_commit_at /fsabsE.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_acre Γ Γc (c : absnode) :
    fsabs_inv Γc -∗ acre_commit_at Γ fsabsE c (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /acre_commit_at /fsabsE.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_uent Γ Γc :
    fsabs_inv Γc -∗ uent_commit_at Γ fsabsE (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /uent_commit_at /fsabsE.
    iIntros (I d t nm ents nl a) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_utgt Γ Γc :
    fsabs_inv Γc -∗ utgt_commit_at Γ fsabsE (fun _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /utgt_commit_at /fsabsE.
    iIntros (I t a) "%Ht %Hnl Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_dmiss Γ Γc :
    fsabs_inv Γc -∗ dmiss_commit_at Γ fsabsE (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /dmiss_commit_at /fsabsE.
    iIntros (I d nm ents nl) "%Hd %Hnm Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_aread Γ Γc (i : Z) :
    fsabs_inv Γc -∗ aread_commit_at Γ fsabsE i (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /aread_commit_at /fsabsE.
    iIntros (I off a) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. by iFrame "Ha".
  Qed.

  Lemma fsabs_awrite Γ Γc (i : Z) (k : nat) :
    fsabs_inv Γc -∗ awrite_commit_at Γ fsabsE i k (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /awrite_commit_at /fsabsE.
    iIntros (I off bs bs0 nl) "%Hpre Ha".
    iMod (fsabs_set Γc I with "Hinv") as "_".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'".
    iMod (fsabs_set Γc I' with "Hinv") as "_".
    iModIntro. by iFrame "Ha'".
  Qed.

  Lemma fsabs_awrites Γ Γc (i : Z) (lo cnt : nat) :
    fsabs_inv Γc -∗
    awrite_commits_at Γ fsabsE i (fun _ _ _ _ => True%I) lo cnt.
  Proof.
    iIntros "#Hinv". rewrite /awrite_commits_at.
    iApply big_sepL_intro. iIntros "!>" (j k _). iApply fsabs_awrite. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  The bundles the sealed contracts take                           *)
  (* ------------------------------------------------------------------ *)

  Lemma fsabs_open_pre_plain Γ Γc (γfs : fs_names) :
    fsabs_inv Γc -∗
    open_au_pre_plain Γ γfs (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /open_au_pre_plain.
    iSplitR; [iApply fsabs_open_walk |].
    iSplitR; [iApply fsabs_aopen; done | iApply fsabs_atrunc; done].
  Qed.

  Lemma fsabs_open_pre_create Γ Γc (γfs : fs_names) :
    fsabs_inv Γc -∗
    open_au_pre_create Γ γfs (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I)
      (fun _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /open_au_pre_create.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_acre; done |].
    iSplitR; [iApply fsabs_dlookup; done |].
    iSplitR; [iApply fsabs_aopen; done | iApply fsabs_atrunc; done].
  Qed.

  Lemma fsabs_mknod_pre_era Γ Γc (γfs : fs_names) (ma mi : Z) :
    fsabs_inv Γc -∗
    mknod_au_pre_era Γ γfs ma mi (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /mknod_au_pre_era.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_acre; done | iApply fsabs_dlookup; done].
  Qed.

  Lemma fsabs_unlink_pre Γ Γc (γfs : fs_names) :
    fsabs_inv Γc -∗
    unlink_au_pre Γ γfs (fun _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ => True%I)
      (fun _ _ _ _ => True%I) (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hinv". rewrite /unlink_au_pre.
    iSplitR; [iApply fsabs_mknod_walk |].
    iSplitR; [iApply fsabs_uent; done |].
    iSplitR; [iApply fsabs_utgt; done |].
    iSplitR; [iApply fsabs_dlookup; done | iApply fsabs_dmiss; done].
  Qed.

End FsAbsInvFire.

(* ====================================================================== *)
(*  FsEchoPin.v -- THE ERA-0 /echo PINS, THE /init PAIR REPLAYED FOR ECHO  *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.  [FsInitPin.v] proved, about era 0's durable map
    [era0_D] and about EVERY abstract state that map denotes, that

      the PATH PIN     ["init"] resolves, in the root directory, to inum 7
      the CONTENT PIN  inum 7's row is [MkAnode (AFile init_bytes) 1]
      the WALK         [arun av ROOTINO ["init"] [ROOTINO; 7]] -- exactly
                       the premise [FsAbsPins.apr_walk] takes

    and [FsInitPinBoot.v] identified the map a BOOT founds its file system
    at with [era0_D].  [FsShPin.v] is those three sentences for the SHELL,
    at inum 13 with [ElfUser.sh_elf]'s bytes; THIS FILE IS THE SAME THREE
    SENTENCES FOR ECHO, at inum 4 with [ElfUser.echo_elf]'s bytes, plus
    the transport corollaries -- and it is written, like [FsShPin], to
    REUSE both files rather than to restate them.

    WHY IT IS WANTED.  The shell's job at the console line "echo hello
    world" is [exec("echo")], and a verified shell answers kexec's
    contract for echo out of its own pins, so the lemma names below are
    that bundle's inputs -- deliberately [FsShPin]'s shapes with [sh]
    replaced by [echo] throughout.  The application's own claim
    ([AppEcho.echo_fs_pure]) carries [era0_echo_pins] beside /init's and
    /sh's.

    WHAT IS REUSED, AND WHY NOTHING IS RESTATED.
      - [FsInitPin] section 1's [img_*] lemmas ([img_astep_root],
        [img_apath_root], [img_abs_file], [img_dur_node]) were stated at an
        ARBITRARY [(P, sb)] precisely so that only the LITERAL corollaries
        pay for a computation.  Echo is a third literal corollary and pays
        exactly its own two [vm_eq]s (section 2), nothing more.
      - [FsInitPin]'s [era0_D], [era0_arow], [era0_dur_root],
        [era0_root_row], [node_at_nondir] and [nfile_inj] are cited.
      - [FsInitPinBoot]'s [era0_boot_snap_ok] / [era0_recovery_D] /
        [era0_lend_D] / [era0_dblk_full] carry section 4's transport with
        no new reasoning about the boot at all: they say "the era-0 map is
        [era0_D]", which is a fact about the map and not about which file
        pins what inside it.
      - No landed statement moves.  This file is a FOURTH LEAF over the
        same cone ([FsInitPinBoot]'s, which is [FsInitPin]'s), required by
        nothing below it.

    THE TWO MEASURED TRAPS, both inherited and both respected here.
      (1) [FsInitPin] section 3's PERFORMANCE RULE.  [Some (NFile _)] must
          be injected AT VARIABLES: an [injection]/[exact] against an
          equation one of whose sides is the file's literal does not
          finish, because conversion is free to unfold [FsTree.file_bytes],
          which is QUADRATIC in the file size.  Echo is 35,592 bytes.
          [nfile_inj] is CITED from [FsInitPin] (it is already proved at
          variables) and section 2's instance closes by transitivity
          through [node_at], where both sides are the same term
          syntactically and the kernel compares nothing.  Likewise
          [Some_inj], never [injection], in section 5.
      (2) [FsInitPinBoot]'s LEAF-RULE trap: in an [FsImgCheck]-consumer
          leaf, [set_solver] is UPSTREAM's (the [FastSetSolver] override is
          a [Tactic Notation] and needs IMPORT, which the intermediate
          [Require Import]s break), and one [set_solver] closing [b ∉ ∅]
          beside the 1,999-element [fsimg_cov] literal cost that file
          3.2 s -> 3 m 49 s.  THIS FILE CONTAINS NO [set_solver]: the one
          place that would want one is inside [era0_boot_map] /
          [era0_dblk_full], which are CITED, not re-proved.

    WHAT IS NOT CLAIMED.  Nothing here says echo is still at inum 4 after
    any write: every sentence is about [era0_D], the map era 0's durable
    extent IS, or is hedged behind the era-0 disk equation
    [fs_blocks dk = fsimg_P] that [SystemAdequacy]'s power-on takes.      *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

(* [FsShPin.v]'s import block, VERBATIM and in its order (the ghost classes
   first, so the file-system stack's names win over the block layer's twins
   -- durable-notes.md).  Every module here is already on
   [FsInitPinBoot]'s cone, so no cone anywhere grows. *)
Require Import Xv6Cameras.
Require Import FsState.
Require Import BioDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import FsTree.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsDurSyscall.
Require Import FsCfgBoot.
Require Import SystemAdequacy.
Require Import FsImgDisk.
Require Import FsImgCheck.     (* [fname_echo], [fsimg_echo_path],
                                  [fsimg_echo_type], [fsimg_echo_at]     *)
Require Import FsImg.
Require Import FsAbs.          (* LAST (FsAbs's own rule)               *)
Require Import FsInitPin.      (* [era0_D], the [img_*] layer, [nfile_inj],
                                  [node_at_nondir], [era0_root_row]     *)
Require Import FsInitPinBoot.  (* [era0_boot_snap_ok], [era0_recovery_D],
                                  [era0_lend_D], [era0_dblk_full]       *)

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], which is [Local] there and in [FsInitPin]:
   the cast is built directly rather than reduced twice
   (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ====================================================================== *)
(*  1.  ECHO'S THREE NAMES, AND ITS DURABLE ROW                            *)
(*                                                                        *)
(*  [ECHO_INO] is READ OFF THE IMAGE, not chosen: [FsImgCheck.             *)
(*  fsimg_echo_path] -- which this file cites and does not re-run -- says  *)
(*  "echo" resolves, in the root directory, to 4.  [echo_bytes] is the     *)
(*  tracked raw, so every [ElfUser] theorem about [echo_elf]               *)
(*  (well-formedness, the file-backed image [EchoInstrs.echo_bytes ∪       *)
(*  EchoData.echo_data], the entry) is a theorem about the bytes pinned    *)
(*  below -- that is [FsImgCheck.fsimg_echo_ok]'s chain, and               *)
(*  [echo_bytes_elf] is the one line that joins it to this file.           *)
(* ====================================================================== *)

Definition ECHO_INO : Z := 4.
Definition echo_path : list fname := [fname_echo].
Definition echo_bytes : list (bv 8) := ElfUser.echo_elf.

(* THE TIE TO THE ELF LAYER.  [FsInitPin] names /init's bytes as
   [init_bytes] and [FsShPin] names the shell's as [sh_bytes]; no file
   names one for echo, so [echo_bytes] is defined fresh here and this is
   its join. *)
Lemma echo_bytes_elf : echo_bytes = ElfUser.echo_elf.
Proof. reflexivity. Qed.

(* THE DURABLE ROW.  [FsInitPin.img_dur_node] at echo's inum: era 0's map
   denotes the image's node there, at every state it denotes. *)
Lemma era0_dur_echo :
  dur_node era0_D ECHO_INO (img_node fsimg_P fsimg_sb ECHO_INO).
Proof.
  apply (img_dur_node FsImgDisk.fsimg_dk XV6_DISK_BYTES fsimg_sb fsimg_nib
           fsimg_cov ECHO_INO fsimg_image_wf).
  cbv [ECHO_INO fsimg_nib]. lia.
Qed.

(* ====================================================================== *)
(*  2.  THE LITERAL IMAGE'S TWO READINGS, AT ECHO                          *)
(*                                                                        *)
(*  The only sentences in this file that compute, and each decodes ONE     *)
(*  inode record out of the image's inode block -- the same cost           *)
(*  [FsImgCheck.fsimg_echo_type] pays.  NO file's contents are forced: the *)
(*  bytes come in through [fsimg_echo_at], which [FsImgCheck] already      *)
(*  proved and which is CITED.                                             *)
(* ====================================================================== *)

Lemma fsimg_echo_size :
  bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb ECHO_INO)) = 35592.
Proof. vm_eq. Qed.

Lemma fsimg_echo_nlink :
  Z.to_nat (bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb ECHO_INO)))
  = 1%nat.
Proof. vm_eq. Qed.

(* ...so /echo is LINKED, which is what its row needs *)
Lemma fsimg_echo_nlink_nz :
  bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb ECHO_INO)) <> 0.
Proof.
  intros Hz. pose proof fsimg_echo_nlink as H1. rewrite Hz in H1.
  simpl in H1. discriminate H1.
Qed.

(* echo is an eighth of what a file may hold; [FsInitPin.maxfile_bytes] is
   the bound, cited *)
Lemma fsimg_echo_size_bound :
  bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb ECHO_INO))
  <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof. rewrite fsimg_echo_size maxfile_bytes. lia. Qed.

(* the two side conditions of [FsInitPin.node_at_nondir] at echo, hoisted
   to top-level lemmas so the instance below passes them as ARGUMENTS and
   never opens a side goal beside the big term (durable-notes: hoist). *)
Lemma fsimg_echo_type_nz :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb ECHO_INO)) <> 0.
Proof. cbv [ECHO_INO]. rewrite fsimg_echo_type. cbv [T_FILE_z]. lia. Qed.

Lemma fsimg_echo_type_nd :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb ECHO_INO)) <> T_DIR_z.
Proof.
  cbv [ECHO_INO]. rewrite fsimg_echo_type. cbv [T_FILE_z T_DIR_z]. lia.
Qed.

(* THE FILE'S BYTES, off [FsImgCheck]'s own equality.  [FsInitPin] section
   3's performance rule, applied: [nfile_inj] is already proved AT
   VARIABLES there, and the instance closes by transitivity through
   [node_at], where both sides are the SAME term syntactically -- so the
   35,592-byte literal is never entered. *)
Lemma fsimg_echo_file_bytes :
  file_bytes (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb ECHO_INO))
    (Z.to_nat (bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb ECHO_INO))))
  = echo_bytes.
Proof.
  apply nfile_inj.
  transitivity (node_at fsimg_P fsimg_sb ECHO_INO).
  - symmetry.
    exact (node_at_nondir fsimg_P fsimg_sb ECHO_INO
             fsimg_echo_type_nz fsimg_echo_type_nd).
  - exact fsimg_echo_at.
Qed.

(* THE IMAGE'S /echo ROW, as an abstract node.  This is the CONTENT PIN's
   whole content, with no state and no map in it yet. *)
Lemma fsimg_echo_abs :
  abs_of (img_node fsimg_P fsimg_sb ECHO_INO)
  = Some (MkAnode (AFile echo_bytes) 1%nat).
Proof.
  rewrite (img_abs_file fsimg_P fsimg_sb ECHO_INO fsimg_echo_type
             fsimg_echo_size_bound fsimg_echo_nlink_nz).
  rewrite fsimg_echo_file_bytes fsimg_echo_nlink. reflexivity.
Qed.

(* ====================================================================== *)
(*  3.  THE TWO PINS AND THE WALK -- PURE IN [era0_D]                      *)
(*                                                                        *)
(*  [FsInitPin] section 4's route (b), replayed: each is quantified over   *)
(*  EVERY [S] the era-0 map denotes, so none names the state the boot mint *)
(*  happened to found at, and none can be invalidated by anything -- they  *)
(*  are facts about a fixed [gmap], hence persistent for free.             *)
(* ====================================================================== *)

(* ---- THE PATH PIN --------------------------------------------------- *)

Theorem era0_echo_path_pin (S : fs_state_rec) :
  snap_ok S era0_D ->
  apath_at (abs_view (fss_inodes S)) FsImg.ROOTINO echo_path = Some ECHO_INO.
Proof.
  intros HS.
  apply (img_apath_root fsimg_P fsimg_sb _ fname_echo ECHO_INO fsimg_wf_ok).
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_root_row S HS).
  - exact fsimg_echo_path.
Qed.

(* ---- THE CONTENT PIN ------------------------------------------------ *)

Theorem era0_echo_content_pin (S : fs_state_rec) :
  snap_ok S era0_D ->
  abs_view (fss_inodes S) !! ECHO_INO = Some (MkAnode (AFile echo_bytes) 1%nat).
Proof.
  intros HS.
  rewrite (era0_arow S ECHO_INO _ HS era0_dur_echo) fsimg_echo_abs.
  reflexivity.
Qed.

(* ---- THE WALK ------------------------------------------------------- *)

(*  [FsAbsPins.apr_walk] takes exactly one pure premise about the abstract
    state: [FsAbs.arun av root ps ds], the list of inums the walk visits.
    At era 0, for echo, that list is [[ROOTINO; 4]].  *)
Theorem era0_echo_arun (S : fs_state_rec) :
  snap_ok S era0_D ->
  arun (abs_view (fss_inodes S)) FsImg.ROOTINO echo_path
       [FsImg.ROOTINO; ECHO_INO].
Proof.
  intros HS.
  (* [eapply]: [ARun_cons]'s hop target [c] is not in its conclusion, so it
     is fixed by the TAIL run ([ARun_nil] at [[ECHO_INO]]) and read back
     into the hop's goal ([FsInitPin.era0_init_arun]'s note). *)
  eapply ARun_cons; [| apply ARun_nil].
  rewrite (img_astep_root fsimg_P fsimg_sb _ fname_echo fsimg_wf_ok).
  - exact fsimg_echo_path.
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_root_row S HS).
Qed.

(* ====================================================================== *)
(*  4.  THE THREE AS ONE NAME, AND THE BOOT TRANSPORT                      *)
(*                                                                        *)
(*  [FsInitPinBoot] section 1's packaging and sections 2-3's transport,    *)
(*  replayed at echo.  Every transport lemma below is CITED from there:    *)
(*  the identification "the map this boot founds at IS [era0_D]" is a fact *)
(*  about the map, so it serves /echo's pins as it serves /init's, and     *)
(*  this file adds no reasoning about the boot at all.                     *)
(* ====================================================================== *)

Definition era0_echo_pins (av : aview) : Prop :=
  (* the PATH pin: "echo" resolves, in the root, to inum 4 *)
  apath_at av FsImg.ROOTINO echo_path = Some ECHO_INO
  (* the CONTENT pin: inum 4 holds [echo_elf]'s bytes, at nlink 1 *)
  /\ av !! ECHO_INO = Some (MkAnode (AFile echo_bytes) 1%nat)
  (* ...and the WALK, which is exactly [FsAbsPins.apr_walk]'s premise *)
  /\ arun av FsImg.ROOTINO echo_path [FsImg.ROOTINO; ECHO_INO].

(* the one composition point with section 3: everything below reduces to
   producing this lemma's premise at the boot's own state *)
Lemma era0_echo_pins_of_snap (S : fs_state_rec) :
  snap_ok S era0_D -> era0_echo_pins (abs_view (fss_inodes S)).
Proof.
  intros HS. split; [exact (era0_echo_path_pin S HS) |].
  split; [exact (era0_echo_content_pin S HS) | exact (era0_echo_arun S HS)].
Qed.

(* ---- 4a.  ROUTE (A): THE MINT'S OWN BUNDLE -------------------------- *)

(*  [FsCfgBoot.fs_boot_snap_wf] is literally the premise
    [BootShared.boot_shared_alloc] takes; [FsInitPinBoot.era0_boot_snap_ok]
    turns it, plus the era-0 disk equation, into [snap_ok S era0_D].      *)
Theorem era0_boot_echo_pins (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec)
    (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  era0_echo_pins (abs_view (fss_inodes S)).
Proof.
  intros Hb Hdk Hcov.
  exact (era0_echo_pins_of_snap S
           (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)).
Qed.

(* ---- 4b.  ROUTE (B): THE CRASH PREDICATE'S EPOCH -------------------- *)

(*  [SystemAdequacy.xv6_boot_era] starts from [FsCrash.P_fs_lend]'s epoch,
    not from the bundle; [FsInitPinBoot.era0_recovery_D] names the map that
    epoch recovers to.                                                    *)
Theorem era0_recovery_echo_pins (dk : Z -> bv 8) (D : gmap Z (list (bv 8)))
    (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  era0_echo_pins (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. apply era0_echo_pins_of_snap.
  assert (HD : D = era0_D).
  { apply era0_recovery_D. rewrite -Hdk. exact Hrec. }
  rewrite -HD. exact HS.
Qed.

(* ---- 4c.  CRASH BEFORE ECHO EVER RUNS -- and it costs nothing.
   [fs_recovery] is a function of the PHYSICAL disk alone, so "nothing
   committed" is spelled as "the re-boot's disk still carries the image's
   bytes", and [FsInitPinBoot.era0_lend_D] gives back the same map.  What
   PROVES that an uncommitted era leaves the durable extent alone is the
   WAL's own crash argument; it is consumed here as [Hdk'].              *)
Corollary era0_reboot_echo_pins (dk dk' : Z -> bv 8)
    (D D' : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  fs_blocks dk' = fs_blocks dk ->
  fs_recovery (fs_blocks dk') D' fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D' ->
  D' = D /\ D' = era0_D /\ era0_echo_pins (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec Hdk' Hrec' HS'.
  rewrite Hdk' in Hrec'.
  destruct (era0_lend_D dk D' D Hdk Hrec' Hrec) as [Heq Hera].
  split; [exact Heq |]. split; [exact Hera |].
  exact (era0_recovery_echo_pins dk D' S Hdk Hrec' HS').
Qed.

(* ====================================================================== *)
(*  5.  THE RESOURCE FORMS                                                 *)
(*                                                                        *)
(*  [FsInitPin] section 6 and [FsInitPinBoot] section 4, at echo.  ALL ARE *)
(*  NON-DESTRUCTIVE: the conclusion is pure, so the authority (or the      *)
(*  snapshot) is handed straight back and nothing is spent.                *)
(* ====================================================================== *)

(* ---- 5a.  AT THE LENT EPOCH, which is what [BootShared]'s caller holds
   before the mint runs.  [era0_dblk_full] is [FsInitPinBoot]'s, cited. *)
Section Era0EchoEpoch.
  (* [FsDurSnap.v]'s own [Section Snap] binder list, verbatim. *)
  Context `{!DiskImg.diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  Lemma fs_snap_era0_echo_pins (g gl gt : gname) (S : fs_state_rec) :
    fs_snap (FsDurBytes.snap_gamma g gl gt) g era0_D S -∗
      ⌜era0_echo_pins (abs_view (fss_inodes S))⌝
      ∗ fs_snap (FsDurBytes.snap_gamma g gl gt) g era0_D S.
  Proof.
    iIntros "H".
    iDestruct (fs_snap_read_ok_keep _ _ _ _ _ era0_dblk_full with "H")
      as "[%Hok H]".
    iFrame "H". iPureIntro. exact (era0_echo_pins_of_snap S Hok).
  Qed.
End Era0EchoEpoch.

(* ---- 5b.  AT THE FOUNDED AUTHORITY, which is what a consumer INSIDE the
   era holds.  [FsCfgSnap.fs_cfg_alloc_snap] founds [γtop] at
   [fss_inodes S], so [abs_view (fss_inodes S)] is the founded
   [FsAbs.astate]'s view on the nose ([FsInitPin]'s section "WHY THE
   SNAPSHOT STATE IS THE RIGHT PLACE TO STAND"). *)
Section Era0EchoLive.
  (* [FsAbs.v]'s own binder list, verbatim: [fsLinkG]/[fsTopG] are [xv6G]
     MEMBERS and this file binds the members, never the bundle. *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* THE PINS AT A [snap_ok] STATE, authority handed straight back. *)
  Lemma astate_era0_echo_pins Γ (S : fs_state_rec) :
    snap_ok S era0_D ->
    astate Γ (abs_view (fss_inodes S)) -∗
      astate Γ (abs_view (fss_inodes S))
      ∗ ⌜era0_echo_pins (abs_view (fss_inodes S))⌝.
  Proof.
    intros HS. iIntros "Hst". iFrame "Hst". iPureIntro.
    exact (era0_echo_pins_of_snap S HS).
  Qed.

  (* ...and off the boot's own bundle, so the consumer (the pinned-exec
     gate: sh's [exec("echo")]) owes only the era-0 disk equation. *)
  Lemma astate_era0_boot_echo_pins Γ (dk : Z -> bv 8) (ndisk : nat)
      (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
      (cov : gset Z) :
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    fs_blocks dk = fsimg_P ->
    cov = fsimg_cov ->
    astate Γ (abs_view (fss_inodes S)) -∗
      astate Γ (abs_view (fss_inodes S))
      ∗ ⌜era0_echo_pins (abs_view (fss_inodes S))⌝.
  Proof.
    intros Hb Hdk Hcov. iIntros "Hst". iFrame "Hst". iPureIntro.
    exact (era0_boot_echo_pins dk ndisk S Pb sb nib cov Hb Hdk Hcov).
  Qed.

  (* THE CONTENT PIN AS AN AGREEMENT: a client-held share of inum 4 IS
     echo's bytes.  [FsAbs.astate_nview] is the agreement; the pin
     supplies the row.  [Some_inj], NOT [injection] -- section "THE TWO
     MEASURED TRAPS" (1): the row carries the 35,592-byte literal. *)
  Lemma nview_era0_echo Γ (S : fs_state_rec) (q : Qp) (a : anode) :
    snap_ok S era0_D ->
    astate Γ (abs_view (fss_inodes S)) -∗ nview Γ q ECHO_INO a -∗
      ⌜a = MkAnode (AFile echo_bytes) 1%nat⌝.
  Proof.
    intros HS. iIntros "Hst Hn".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    iPureIntro.
    rewrite (era0_echo_content_pin S HS) in Hav.
    apply Some_inj in Hav. symmetry. exact Hav.
  Qed.

  Lemma nview_era0_boot_echo Γ (dk : Z -> bv 8) (ndisk : nat)
      (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
      (cov : gset Z) (q : Qp) (a : anode) :
    fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
    fs_blocks dk = fsimg_P ->
    cov = fsimg_cov ->
    astate Γ (abs_view (fss_inodes S)) -∗ nview Γ q ECHO_INO a -∗
      ⌜a = MkAnode (AFile echo_bytes) 1%nat⌝.
  Proof.
    intros Hb Hdk Hcov. iIntros "Hst Hn".
    iApply (nview_era0_echo Γ S q a
              (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)
              with "Hst Hn").
  Qed.

End Era0EchoLive.

(* ====================================================================== *)
(*  6.  THE AUDIT                                                          *)
(*                                                                        *)
(*  The same three commands [FsShPin] leaves commented out, for the same   *)
(*  reason: the assumption set of every name here is the ELEVEN ROCQ       *)
(*  KERNEL PRIMITIVES ([PrimInt63.*], [PrimString.*]) that the image's     *)
(*  [PrimString] literal drags into any sentence that reads the disk.  NO  *)
(*  logical axiom, NO [Admitted], and nothing this file adds: the image    *)
(*  facts are computations and the transport is citation, so nothing       *)
(*  axiomatic CAN enter.  Checked on the mirror, not on every build.       *)
(*                                                                        *)
(*    Print Assumptions era0_echo_path_pin.                               *)
(*    Print Assumptions era0_echo_content_pin.                            *)
(*    Print Assumptions era0_echo_arun.                                   *)
(* ====================================================================== *)

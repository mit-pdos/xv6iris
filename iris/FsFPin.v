(* ====================================================================== *)
(*  FsFPin.v -- `f` IS NOT IN THE IMAGE: era 0's root directory holds no   *)
(*  entry named `f`, at every abstract state era 0's durable map denotes.  *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.  The FILE application
    (claude-notes/design/app-file.md) claims about ONE file at the root,
    `f`, and its era-0 state is ABSENT: mkfs packs the five verified
    binaries and no `f`.  That is exactly [FsConsPin]'s shape for the
    console device node -- the console is not in the image either -- so
    this file is [FsConsPin] sections 1-2 at another name, and nothing
    more: the delta algebra that moves the state ([FsConsPin] section 5,
    generalised over the name) is already there, and the application's
    own two-state claim lives in [AppFile].

    WHY IT IS ITS OWN FILE.  It is not about cat ([FsCatPin]) and it is
    not part of the pure pins conjunction ([FileFsPure.file_fs_pure]):
    the claim carries the f-state as a GHOST (a deed), and this sentence
    is what the era-0 mint discharges its `absent` arm with.  One
    [vm_eq], on the scan [FsImgCheck.fsimg_path_root] already names.

    THE COST.  [FsImgCheck.fsimg_path_root] is the FORM TO COMPUTE WITH
    (the file's own header rule, and user-tree.md §8.1's): ONE
    [DirView.dir_first] scan of the root's records, no [dir_view] (which
    is [O(nrec^2)] and, at this image, quarter-hour material), no tree
    and no file contents.  A MISS scans all of the root's records rather
    than stopping early -- which is the identical computation
    [FsConsPin.fsimg_console_path] already pays for `console`.          *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.

(* [FsConsPin.v]'s import block minus everything only its sections 3-5
   want: this file states one absence and transports it. *)
Require Import FsState.
Require Import FsTree.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsCfgBoot.
Require Import FsBootParams.    (* [fsimg_cov]                            *)
Require Import FsImgDisk.
Require Import FsImgCheck.      (* [fname_f], [fsimg_path_root_blk]       *)
Require Import FsImg.
Require Import FsAbsDefs.       (* [astep]/[apath_at]/[abs_view]          *)
Require Import FsInitPin.       (* [era0_D], [img_astep_root],
                                   [era0_root_row]                        *)
Require Import FsInitPinBoot.   (* [era0_recovery_D], [era0_boot_snap_ok] *)

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], [Local] there and in every consumer leaf. *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ====================================================================== *)
(*  1.  THE NAME, AND THE IMAGE'S ANSWER                                   *)
(* ====================================================================== *)

Definition f_path : list fname := [fname_f].

(* THE ONE COMPUTATION: no `f` in the root directory of mkfs's image. *)
Lemma fsimg_f_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_f] = None.
Proof. rewrite fsimg_path_root_blk. vm_eq. Qed.

(* ...and `f` is none of the five names the image DOES hold.  Decidable
   at the literals, and what the delta lemmas want at the root's entry
   map (a create/arm/unarm at another name leaves this state alone). *)
Lemma fname_f_ne_init : fname_f <> fname_init.
Proof. vm_compute. discriminate. Qed.
Lemma fname_f_ne_sh : fname_f <> fname_sh.
Proof. vm_compute. discriminate. Qed.
Lemma fname_f_ne_echo : fname_f <> fname_echo.
Proof. vm_compute. discriminate. Qed.
Lemma fname_f_ne_cat : fname_f <> fname_cat.
Proof. vm_compute. discriminate. Qed.
Lemma fname_f_ne_sync : fname_f <> fname_sync.
Proof. vm_compute. discriminate. Qed.

(* ====================================================================== *)
(*  2.  ABSENT, AND THE TWO TRANSPORTS                                     *)
(*                                                                        *)
(*  Stated at [astep] (one hop out of the root) rather than at            *)
(*  [apath_at], for [FsConsPin.cons_absent]'s reason: that is the form    *)
(*  the claim's deltas move.  [f_absent_apath] is the reading.            *)
(* ====================================================================== *)

Definition f_absent (av : aview) : Prop :=
  astep av FsImg.ROOTINO fname_f = None.

(* NO SSREFLECT REWRITE IN THIS FILE.  [FsConsPin]'s twin of this proof is
   spelled [rewrite /f_path ...], which needs the [iris.proofmode] import
   that file carries for its own [iProp] sections; this one has no [iProp]
   in it and stays a pure leaf, so the two rewrites below are the stock
   tactic's. *)
Lemma f_absent_apath (av : aview) :
  f_absent av -> apath_at av FsImg.ROOTINO f_path = None.
Proof.
  unfold f_path, f_absent. intros H.
  rewrite apath_at_cons, H. reflexivity.
Qed.

(* THE ERA-0 STATE, at every state era 0's map denotes. *)
Theorem era0_f_absent (S : fs_state_rec) :
  snap_ok S era0_D -> f_absent (abs_view (fss_inodes S)).
Proof.
  intros HS. unfold f_absent.
  rewrite (img_astep_root fsimg_P fsimg_sb _ fname_f fsimg_wf_ok).
  - exact fsimg_f_path.
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_root_row S HS).
Qed.

(* ...and the two transports, [FsConsPin]'s verbatim: the identification
   "the map this boot founds at IS [era0_D]" is a fact about the MAP, so
   it serves this state as it serves the pins. *)
Theorem era0_boot_f_absent (dk : Z -> bv 8) (ndisk : nat)
    (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  f_absent (abs_view (fss_inodes S)).
Proof.
  intros Hb Hdk Hcov.
  exact (era0_f_absent S
           (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)).
Qed.

Theorem era0_recovery_f_absent (dk : Z -> bv 8)
    (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  f_absent (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. apply era0_f_absent.
  assert (HD : D = era0_D).
  { apply era0_recovery_D. rewrite <- Hdk. exact Hrec. }
  rewrite <- HD. exact HS.
Qed.

(* ====================================================================== *)
(*  3.  THE AUDIT                                                          *)
(*                                                                        *)
(*    Print Assumptions era0_f_absent.                                    *)
(*    Print Assumptions era0_recovery_f_absent.                           *)
(*                                                                        *)
(*  = the eleven Rocq kernel primitives ([PrimInt63.*], [PrimString.*])   *)
(*  the image's literal drags into any sentence that reads the disk, and  *)
(*  nothing else.                                                          *)
(* ====================================================================== *)

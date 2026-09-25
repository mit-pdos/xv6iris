(* ====================================================================== *)
(* FileFsPure.v -- THE FILE APPLICATION'S PURE FILE-SYSTEM CLAIM.          *)
(*                                                                        *)
(* [file_fs_pure] alone: the echo application's three era-0 pins, plus     *)
(* /cat's and /grep's.  It owns nothing -- that is the whole point of its being pure   *)
(* ([EchoFsPure.v]'s note, and [AppEcho.v]'s) -- so it needs only the pin  *)
(* files that state its conjuncts.                                        *)
(*                                                                        *)
(* WHY IT IS THE ECHO CONJUNCTION PLUS ONE, rather than a fourth pin       *)
(* spelled out here: the file application runs the echo application's      *)
(* console side verbatim at a projection (claude-notes/design/             *)
(* app-file.md §2), so everything that consumed [echo_fs_pure] must go on  *)
(* consuming it -- [file_fs_pure_echo] is that projection, and it is what  *)
(* lets sh's landed record ([UInitSh]'s [init_sh_slot_core]) be            *)
(* re-instantiated without restating a single pin.                        *)
(*                                                                        *)
(* WHAT IS NOT HERE.  `f` itself: the file's state is a GHOST (the deed of *)
(* design §2), not a pure fact about the view, and era 0's `f` is ABSENT   *)
(* -- which is [FsFPin.era0_f_absent], a sentence about a name the image   *)
(* does NOT hold and therefore not one of the pins.                       *)
(* ====================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.

Require Import FsInitPinBoot.      (* [era0_pins], [era0_recovery_pins]  *)
Require Import FsShPin.            (* [era0_sh_pins]                     *)
Require Import FsEchoPin.          (* [era0_echo_pins]                   *)
Require Import FsCatPin.           (* [era0_cat_pins]                    *)
Require Import FsGrepPin.          (* [era0_grep_pins]                   *)
Require Import EchoFsPure.         (* [echo_fs_pure]                     *)
Require Import FsAbsDefs.          (* [aview]                            *)
Require Import FsState.            (* [fs_state_rec] / [fss_inodes]      *)
Require Import FsCrash.            (* [fs_blocks] / [fs_recovery]        *)
Require Import FsDurSnap.          (* [snap_ok]                          *)
Require Import FsImgDisk.          (* [fsimg_P]                          *)
Require Import FsBootParams.       (* [fsimg_cov]                        *)
Require Import FsImgCheck.         (* [fsimg_sb]                         *)
Require Import FsImg.              (* [sb_logstart]                      *)

(* /init, /sh, /echo, /cat and /grep are the image's, path and content, on the
   abstract state's VIEW.  Per-inum rather than "the map is the image's"
   on purpose: the durable snapshot pins a state per inum and no whole-map
   equality exists (fs-syscall-specs.md lane D, gap (3)).  This half of
   the claim is PURE -- it owns nothing -- so it is a [Prop] and the
   predicate embeds it. *)
Definition file_fs_pure (av : aview) : Prop :=
  echo_fs_pure av /\ era0_cat_pins av /\ era0_grep_pins av.

(* THE PROJECTION every landed consumer of the echo claim reads. *)
Lemma file_fs_pure_echo (av : aview) : file_fs_pure av -> echo_fs_pure av.
Proof. intros [H _]. exact H. Qed.

Lemma file_fs_pure_cat (av : aview) : file_fs_pure av -> era0_cat_pins av.
Proof. intros [_ [H _]]. exact H. Qed.

(* /grep's pins (claude-notes/design/grep-pipes.md, cut G6): a pipeline
   stage `grep w` execs /grep out of them, as `cat` execs /cat *)
Lemma file_fs_pure_grep (av : aview) : file_fs_pure av -> era0_grep_pins av.
Proof. intros [_ [_ H]]. exact H. Qed.

(* THE PINS AT THE MAP A BOOT FOUNDS ITS FILE SYSTEM AT, when the disk is
   mkfs's image -- the four pin files' transport theorems, read together.
   [AppEcho.echo_fs_era0]'s statement at [file_fs_pure]; the echo half is
   re-derived from the same three transports rather than cited from
   [AppEcho], which would put the whole echo application (and, through it,
   [FsConsPin] and [EchoOut]) in front of this leaf for nothing. *)
Lemma file_fs_era0 (dk : Z -> bv 8) (D : gmap Z (list (bv 8)))
    (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  file_fs_pure (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. split.
  - split; [exact (era0_recovery_pins dk D S Hdk Hrec HS) |].
    split.
    + exact (era0_recovery_sh_pins dk D S Hdk Hrec HS).
    + exact (era0_recovery_echo_pins dk D S Hdk Hrec HS).
  - split.
    + exact (era0_recovery_cat_pins dk D S Hdk Hrec HS).
    + exact (era0_recovery_grep_pins dk D S Hdk Hrec HS).
Qed.

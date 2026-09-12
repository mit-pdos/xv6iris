(* ====================================================================== *)
(*  FsConsPin.v -- THE CONSOLE DEVICE NODE: the two states its inum can be *)
(*  in, the era-0 state (ABSENT -- mkfs made no device node), and the      *)
(*  pure delta algebra a create/arm/unarm/trunc moves them by.             *)
(*                                                                        *)
(*  WHY THIS FILE IS NOT [FsShPin.v]'s FOURTH COPY.  /init, /sh and /echo  *)
(*  are IN the tracked image, so each of their pins is a fact about        *)
(*  [FsInitPin.era0_D] and nothing ever moves it.  The console is NOT in   *)
(*  the image: `mkfs` creates no device inode and the root holds no        *)
(*  `console` entry (section 2 computes both), so /init's own              *)
(*  `mknod(`console`, CONSOLE, 0)` is what creates it, at an inum `ialloc` *)
(*  chooses at run time.  The application's claim about the console is     *)
(*  therefore TWO-STATE -- absent, or present AT AN INUM -- and this file  *)
(*  holds the two states, their transport across the deltas the syscalls   *)
(*  perform, and nothing in [iProp].                                       *)
(*                                                                        *)
(*  §1  the name, the path, the node                                       *)
(*  §2  ERA 0 IS ABSENT, off the tracked image, with the boot transport    *)
(*  §3  the states, and reading a present state as a PIN                   *)
(*  §4  THE FILE PIN, GENERALISED: [file_pin nm ino bs] is [FsInitPin.     *)
(*      era0_pins], [era0_sh_pins] and [era0_echo_pins]  *)
(*      at three names -- so the delta lemmas below are proved ONCE and    *)
(*      applied three times, rather than written out per binary            *)
(*      (durable-notes: a hoist proposed because two near-duplicates      *)
(*      cannot see each other is usually a generalization in disguise).    *)
(*  §5  THE DELTAS: what an arm, a create, an unarm and a truncation do to *)
(*      a file pin and to the console's two states.                        *)
(*                                                                        *)
(*  WHAT §5 FOUND, and it is the lane's central finding: the ARM and the   *)
(*  CREATE legs preserve every pin with NO side condition the commit does  *)
(*  not already carry, while the UNARM and the TRUNC legs need [i <> ino]  *)
(*  -- and [FsAbsCreateFire.aunarm_commit_at] / [SysOpenDefs.              *)
(*  atrunc_commit_at] quantify [i] over EVERY row at nlink 1 / EVERY file  *)
(*  row, which is exactly the shape /sh's row has.  The side conditions    *)
(*  are stated as premises here and the friction is reported rather than   *)
(*  papered over.                                                          *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

(* [FsEchoPin.v]'s import block, in its order, with [FsAbsDelta] appended
   for section 5's deltas and [ConsoleInv] for the ONE constant the device
   node's major is ([ConsoleInv.CONSOLE]; spelling a second literal 1 here
   would be a second source of truth). *)
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
Require Import FsImgCheck.     (* [fsimg_byte], [fsimg_path_root]        *)
Require Import FsImg.
Require Import FsAbs.          (* LAST of the fs stack (FsAbs's own rule) *)
Require Import FsInitPin.      (* [era0_D], [img_astep_root], [era0_root_row] *)
Require Import FsInitPinBoot.  (* [era0_recovery_D], [era0_boot_snap_ok]  *)
Require Import FsShPin.        (* [SH_INO] / [sh_path] / [era0_sh_pins]   *)
Require Import FsEchoPin.      (* [ECHO_INO] / [echo_path] / [era0_echo_pins] *)
Require Import FsAbsDelta.     (* [delta_create]/[delta_arm]/[delta_unarm]/
                                  [delta_trunc], [cre_pre]               *)
Require Import ConsoleInv.     (* [CONSOLE]                              *)

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], [Local] there and in every consumer leaf:
   the cast is built directly rather than reduced twice
   (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ====================================================================== *)
(*  1.  THE NAME, THE PATH, THE NODE                                       *)
(*                                                                        *)
(*  THERE IS NO INUM HERE, and that is the whole difference from the four  *)
(*  binaries' pin files: the console's inum does not exist until /init     *)
(*  creates it, so it is a BOUND VARIABLE of section 3 and a ghost of the  *)
(*  application's claim ([AppEcho.cons_made]), never a constant.           *)
(* ====================================================================== *)

(* `console`, spelled the way [FsImgCheck]'s four names are *)
Definition fname_console : fname :=
  [fsimg_byte 0x63; fsimg_byte 0x6f; fsimg_byte 0x6e; fsimg_byte 0x73;
   fsimg_byte 0x6f; fsimg_byte 0x6c; fsimg_byte 0x65].

Definition cons_path : list fname := [fname_console].

(* THE NODE /init's mknod creates: major [CONSOLE], minor 0, ONE link.
   [SysMknodDefs.dev_arg] of init's own argument words is what ties the
   two numbers to this literal ([FsAbsMknodFire.mkf_dev_arg]). *)
Definition cons_dev : anode := MkAnode (ADev CONSOLE 0) 1%nat.

(* ====================================================================== *)
(*  2.  ERA 0 IS ABSENT                                                    *)
(*                                                                        *)
(*  ONE computation, and it is [FsImgCheck.fsimg_path_root]'s: one         *)
(*  [dir_first] scan of the root's records for `console`, which finds      *)
(*  nothing.  No file's contents are forced and no inode record is         *)
(*  decoded -- so this is the CHEAP half of the image evidence, and there  *)
(*  is no expensive half: the claim below says nothing about the image's   *)
(*  inode types (see the header's §5 note and [cons_present_at], which     *)
(*  does not claim the console is the image's ONLY device node -- nothing  *)
(*  consumes that, and an inode-region-wide type sweep would be a second   *)
(*  whole-image computation for it).                                      *)
(* ====================================================================== *)

Lemma fsimg_console_path :
  path_at (tree_of_disk fsimg_P fsimg_sb) ROOTINO [fname_console] = None.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

(* ...and `console` is not one of the four names the image DOES hold: the
   four inequalities the delta lemmas of section 5 need at the root's
   entry map.  Decidable at the literals. *)
Lemma fname_console_ne_init : fname_console <> fname_init.
Proof. vm_compute. discriminate. Qed.
Lemma fname_console_ne_sh : fname_console <> fname_sh.
Proof. vm_compute. discriminate. Qed.
Lemma fname_console_ne_echo : fname_console <> fname_echo.
Proof. vm_compute. discriminate. Qed.

(* ====================================================================== *)
(*  3.  THE TWO STATES                                                     *)
(* ====================================================================== *)

(* ABSENT: the root directory has no `console` entry.  Stated at [astep]
   (one hop out of the root) rather than at [apath_at], because that is
   the form section 5's deltas move; [cons_absent_apath] is the reading.

   NOT `and the view holds no device node anywhere`: that clause was in
   the lane's first design and is REFUTED by the mknod sequence itself --
   [ialloc] ARMS the child (a device row appears at a fresh inum) BEFORE
   [dirlink] writes the parent's entry, so between the two fires the view
   has a device node and no console entry, and a claim carrying the clause
   would be unprovable at that instant.  Nothing consumes uniqueness. *)
Definition cons_absent (av : aview) : Prop :=
  astep av FsImg.ROOTINO fname_console = None.

Lemma cons_absent_apath (av : aview) :
  cons_absent av -> apath_at av FsImg.ROOTINO cons_path = None.
Proof. intros H. rewrite /cons_path apath_at_cons /cons_absent in H |- *. by rewrite H. Qed.

(* PRESENT AT [i]: `console` resolves, in the root, to [i]; [i]'s row is
   the console device at one link; and the walk that gets there is
   [[ROOTINO; i]].  The three conjuncts of [era0_sh_pins] at a
   BOUND inum and a device node -- so [PinnedObs.pin_resolves_at] is one
   [split_and!] over it ([cons_pin_resolves_at] below). *)
Definition cons_present_at (i : Z) (av : aview) : Prop :=
  apath_at av FsImg.ROOTINO cons_path = Some i
  /\ av !! i = Some cons_dev
  /\ arun av FsImg.ROOTINO cons_path [FsImg.ROOTINO; i].

(* the step form, which is what the deltas move *)
Lemma cons_present_astep (i : Z) (av : aview) :
  cons_present_at i av -> astep av FsImg.ROOTINO fname_console = Some i.
Proof.
  intros (Hp & _ & _). rewrite /cons_path apath_at_cons in Hp.
  destruct (astep av FsImg.ROOTINO fname_console) as [c |] eqn:E;
    [| discriminate Hp].
  rewrite (apath_at_nil av c) in Hp. by injection Hp as ->.
Qed.

(* ...and back: the entry and the row are the whole state, the run is
   their consequence *)
Lemma cons_present_of_parts (i : Z) (av : aview) :
  astep av FsImg.ROOTINO fname_console = Some i ->
  av !! i = Some cons_dev ->
  cons_present_at i av.
Proof.
  intros Hst Hrow. split_and!.
  - rewrite /cons_path apath_at_cons Hst. exact (apath_at_nil av i).
  - exact Hrow.
  - eapply ARun_cons; [exact Hst | apply ARun_nil].
Qed.

(* THE STATE'S OWN INUM LIST, computed from the view: [[]] when the
   console is absent and [[i]] when it is present at [i].  This is what the
   application's transport allocates its fresh flag AT -- it has to choose
   the new flag's value before it may look at which arm the claim is in
   (the claim sits under a later and the allocation is an update), and the
   view decides the value on its own. *)
Definition cons_inum (av : aview) : list Z :=
  match apath_at av FsImg.ROOTINO cons_path with
  | None => []
  | Some i => [i]
  end.

Lemma cons_inum_absent (av : aview) : cons_absent av -> cons_inum av = [].
Proof. intros H. rewrite /cons_inum (cons_absent_apath av H). reflexivity. Qed.

Lemma cons_inum_present (i : Z) (av : aview) :
  cons_present_at i av -> cons_inum av = [i].
Proof. intros (Hp & _ & _). rewrite /cons_inum Hp. reflexivity. Qed.

(* THE ERA-0 STATE, at every state era 0's map denotes. *)
Theorem era0_cons_absent (S : fs_state_rec) :
  snap_ok S era0_D -> cons_absent (abs_view (fss_inodes S)).
Proof.
  intros HS. rewrite /cons_absent.
  rewrite (img_astep_root fsimg_P fsimg_sb _ fname_console fsimg_wf_ok).
  - exact fsimg_console_path.
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_root_row S HS).
Qed.

(* ...and the two transports [FsShPin] §4 states for the pins, replayed:
   the identification `the map this boot founds at IS [era0_D]` is a fact
   about the MAP, so it serves this state as it serves the pins. *)
Theorem era0_boot_cons_absent (dk : Z -> bv 8) (ndisk : nat)
    (S : fs_state_rec) (Pb : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_boot_snap_wf dk ndisk S Pb sb nib cov ->
  fs_blocks dk = fsimg_P ->
  cov = fsimg_cov ->
  cons_absent (abs_view (fss_inodes S)).
Proof.
  intros Hb Hdk Hcov.
  exact (era0_cons_absent S
           (era0_boot_snap_ok dk ndisk S Pb sb nib cov Hb Hdk Hcov)).
Qed.

Theorem era0_recovery_cons_absent (dk : Z -> bv 8)
    (D : gmap Z (list (bv 8))) (S : fs_state_rec) :
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D ->
  cons_absent (abs_view (fss_inodes S)).
Proof.
  intros Hdk Hrec HS. apply era0_cons_absent.
  assert (HD : D = era0_D).
  { apply era0_recovery_D. rewrite -Hdk. exact Hrec. }
  rewrite -HD. exact HS.
Qed.

(* ====================================================================== *)
(*  4.  THE FILE PIN, GENERALISED                                          *)
(*                                                                        *)
(*  [FsInitPinBoot.era0_pins], [era0_sh_pins] and                   *)
(*  [era0_echo_pins] are the SAME three sentences at three       *)
(*  names, three inums and three byte lists.  Section 5's delta lemmas are *)
(*  about those three sentences and about nothing else, so they are proved *)
(*  here once over the generalisation and applied three times by the       *)
(*  application's own step ([AppEcho.echo_fs_pure]).                        *)
(* ====================================================================== *)

Definition file_pin (nm : fname) (ino : Z) (bs : list (bv 8)) (av : aview)
    : Prop :=
  apath_at av FsImg.ROOTINO [nm] = Some ino
  /\ av !! ino = Some (MkAnode (AFile bs) 1%nat)
  /\ arun av FsImg.ROOTINO [nm] [FsImg.ROOTINO; ino].

(* the three instances, each a [reflexivity] on the [Prop]: the landed
   names ARE this one, and no consumer has to know that. *)
Lemma file_pin_init (av : aview) :
  file_pin fname_init INIT_INO init_bytes av <-> era0_pins av.
Proof. rewrite /file_pin /era0_pins /init_path. reflexivity. Qed.

Lemma file_pin_sh (av : aview) :
  file_pin fname_sh SH_INO sh_bytes av
  <-> era0_sh_pins av.
Proof. rewrite /file_pin /era0_sh_pins /sh_path. reflexivity. Qed.

Lemma file_pin_echo (av : aview) :
  file_pin fname_echo ECHO_INO echo_bytes av
  <-> era0_echo_pins av.
Proof.
  rewrite /file_pin /era0_echo_pins /echo_path. reflexivity.
Qed.

(* the step form, as [cons_present_astep] is for the console *)
Lemma file_pin_astep (nm : fname) (ino : Z) (bs : list (bv 8)) (av : aview) :
  file_pin nm ino bs av -> astep av FsImg.ROOTINO nm = Some ino.
Proof.
  intros (Hp & _ & _). rewrite apath_at_cons in Hp.
  destruct (astep av FsImg.ROOTINO nm) as [c |] eqn:E; [| discriminate Hp].
  rewrite (apath_at_nil av c) in Hp. by injection Hp as ->.
Qed.

Lemma file_pin_of_parts (nm : fname) (ino : Z) (bs : list (bv 8)) (av : aview) :
  astep av FsImg.ROOTINO nm = Some ino ->
  av !! ino = Some (MkAnode (AFile bs) 1%nat) ->
  file_pin nm ino bs av.
Proof.
  intros Hst Hrow. split_and!.
  - rewrite apath_at_cons Hst. exact (apath_at_nil av ino).
  - exact Hrow.
  - eapply ARun_cons; [exact Hst | apply ARun_nil].
Qed.

(* A PINNED ROOT IS A DIRECTORY, and it is what every delta lemma below
   uses to place [ROOTINO] against the inum the delta touches. *)
Lemma file_pin_root_dir (nm : fname) (ino : Z) (bs : list (bv 8))
    (av : aview) :
  file_pin nm ino bs av ->
  exists (ents : gmap fname Z) (nl : nat),
    av !! FsImg.ROOTINO = Some (MkAnode (ADir ents) nl) /\ ents !! nm = Some ino.
Proof.
  intros Hp. pose proof (file_pin_astep nm ino bs av Hp) as Hst.
  rewrite /astep /aents in Hst.
  destruct (av !! FsImg.ROOTINO) as [a |] eqn:Ha; [| discriminate Hst].
  rewrite /= /anode_ents in Hst.
  destruct a as [n nl]. destruct n as [b | ents | ma mi]; try discriminate Hst.
  exists ents, nl. split; [reflexivity | exact Hst].
Qed.

Lemma cons_present_root_dir (i : Z) (av : aview) :
  cons_present_at i av ->
  exists (ents : gmap fname Z) (nl : nat),
    av !! FsImg.ROOTINO = Some (MkAnode (ADir ents) nl)
    /\ ents !! fname_console = Some i.
Proof.
  intros Hp. pose proof (cons_present_astep i av Hp) as Hst.
  rewrite /astep /aents in Hst.
  destruct (av !! FsImg.ROOTINO) as [a |] eqn:Ha; [| discriminate Hst].
  rewrite /= /anode_ents in Hst.
  destruct a as [n nl]. destruct n as [b | ents | ma mi]; try discriminate Hst.
  exists ents, nl. split; [reflexivity | exact Hst].
Qed.

(* ====================================================================== *)
(*  5.  THE DELTAS                                                         *)
(*                                                                        *)
(*  Each of the four legs a mknod / open bundle carries, against a file    *)
(*  pin and against the console's two states.  The premises are the ones   *)
(*  the corresponding COMMIT carries ([FsAbsCreateFire.aarm_commit_at] /   *)
(*  [acre_commit_at_gen] / [aunarm_commit_at], [SysOpenDefs.               *)
(*  atrunc_commit_at]) -- except where they are NOT, which is the point:   *)
(*  [i <> ino] on the unarm and the trunc is a premise no commit supplies. *)
(* ====================================================================== *)

(* ---- 5a.  THE ARM: a DEVICE row appears at a fresh inum -------------- *)

(* The arm's commit carries [abs_view I !! i = None], and that is all the
   two lemmas below need: a row the view does not have is neither a pin's
   inum nor the root. *)
Lemma file_pin_arm (nm : fname) (ino : Z) (bs : list (bv 8))
    (i : Z) (ma mi : Z) (av : aview) :
  av !! i = None ->
  file_pin nm ino bs av ->
  file_pin nm ino bs (delta_arm i (ADev ma mi) av).
Proof.
  intros Hfree Hp.
  destruct (file_pin_root_dir nm ino bs av Hp) as (ents & nl & Hroot & Hnm).
  destruct Hp as (_ & Hrow & _).
  assert (Hne_root : i <> FsImg.ROOTINO) by (intros ->; by rewrite Hroot in Hfree).
  assert (Hne_ino : i <> ino) by (intros ->; by rewrite Hrow in Hfree).
  apply file_pin_of_parts.
  - rewrite /astep /aents /delta_arm lookup_insert_ne; [| congruence].
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite /delta_arm lookup_insert_ne; [exact Hrow | congruence].
Qed.

Lemma cons_absent_arm (i : Z) (ma mi : Z) (av : aview) :
  cons_absent av -> cons_absent (delta_arm i (ADev ma mi) av).
Proof.
  intros Habs. rewrite /cons_absent /astep /aents /delta_arm.
  destruct (decide (i = FsImg.ROOTINO)) as [-> | Hne].
  - rewrite lookup_insert /= /anode_ents /=. reflexivity.
  - rewrite lookup_insert_ne; [| congruence]. exact Habs.
Qed.

Lemma cons_present_arm (j : Z) (i : Z) (ma mi : Z) (av : aview) :
  av !! i = None ->
  cons_present_at j av -> cons_present_at j (delta_arm i (ADev ma mi) av).
Proof.
  intros Hfree Hp.
  destruct (cons_present_root_dir j av Hp) as (ents & nl & Hroot & Hnm).
  destruct Hp as (_ & Hrow & _).
  assert (Hne_root : i <> FsImg.ROOTINO) by (intros ->; by rewrite Hroot in Hfree).
  assert (Hne_j : i <> j) by (intros ->; by rewrite Hrow in Hfree).
  apply cons_present_of_parts.
  - rewrite /astep /aents /delta_arm lookup_insert_ne; [| congruence].
    rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite /delta_arm lookup_insert_ne; [exact Hrow | congruence].
Qed.

(* ---- 5b.  THE CREATE: the parent gains an entry --------------------- *)

(* [FsAbsDelta.delta_create_dev] collapses the fused delta at a DEVICE
   child to the ONE-ROW PARENT INSERT (the child's row is already there --
   the arm put it there), so every lemma below is about the row at [d] and
   nothing else.  [cre_pre]'s middle conjunct -- the new name is NOT in the
   parent's entry map -- is what keeps a pinned name from being
   overwritten, and it is the create commit's own premise. *)
Lemma file_pin_create (nm : fname) (ino : Z) (bs : list (bv 8))
    (d : Z) (nmn : fname) (ents : gmap fname Z) (nl : nat) (i : Z)
    (ma mi : Z) (av : aview) :
  cre_pre av d nmn ents nl i (ADev ma mi) ->
  file_pin nm ino bs av ->
  file_pin nm ino bs (delta_create d nmn i (ADev ma mi) av).
Proof.
  intros Hpre Hp.
  pose proof Hpre as (Hd & Hfresh & Hchild).
  destruct (file_pin_root_dir nm ino bs av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow & _).
  assert (Hd_ino : d <> ino)
    by (intros ->; rewrite Hrow in Hd; discriminate Hd).
  rewrite (delta_create_dev av d nmn ents nl i ma mi Hpre).
  apply file_pin_of_parts.
  - rewrite /astep /aents.
    destruct (decide (d = FsImg.ROOTINO)) as [-> | Hdne].
    + rewrite lookup_insert /= /anode_ents /=.
      rewrite Hroot in Hd. injection Hd as Hents Hnl. subst rents.
      rewrite lookup_insert_ne; [exact Hnm |].
      intros <-. by rewrite Hnm in Hfresh.
    + rewrite lookup_insert_ne; [| congruence].
      rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite lookup_insert_ne; [exact Hrow | congruence].
Qed.

(* THE STEP THE LANE EXISTS FOR: at the ROOT, under the name `console`,
   with a [CONSOLE] device child, the state moves ABSENT -> PRESENT at the
   inum the create chose. *)
Lemma cons_state_mknod (ents : gmap fname Z) (nl : nat) (i : Z) (av : aview) :
  cre_pre av FsImg.ROOTINO fname_console ents nl i (ADev CONSOLE 0) ->
  cons_present_at i (delta_create FsImg.ROOTINO fname_console i
                       (ADev CONSOLE 0) av).
Proof.
  intros Hpre. pose proof Hpre as (Hd & Hfresh & Hchild).
  assert (Hi_root : i <> FsImg.ROOTINO)
    by (intros ->; rewrite Hd in Hchild; discriminate Hchild).
  rewrite (delta_create_dev av FsImg.ROOTINO fname_console ents nl i
             CONSOLE 0 Hpre).
  apply cons_present_of_parts.
  - rewrite /astep /aents lookup_insert /= /anode_ents /=.
    apply lookup_insert.
  - rewrite lookup_insert_ne; [| congruence].
    rewrite /cons_dev. exact Hchild.
Qed.

(* ...and the create that is NOT the console's leaves the state where it
   was.  BOTH arms are needed by the application's step, because the
   create commit fires at whatever [(d, nm)] the CALL reached and the
   claim has to survive either. *)
Lemma cons_absent_create_other (d : Z) (nmn : fname) (ents : gmap fname Z)
    (nl : nat) (i : Z) (ma mi : Z) (av : aview) :
  cre_pre av d nmn ents nl i (ADev ma mi) ->
  (d <> FsImg.ROOTINO \/ nmn <> fname_console) ->
  cons_absent av -> cons_absent (delta_create d nmn i (ADev ma mi) av).
Proof.
  intros Hpre Hother Habs. pose proof Hpre as (Hd & _ & _).
  rewrite (delta_create_dev av d nmn ents nl i ma mi Hpre).
  rewrite /cons_absent /astep /aents.
  destruct (decide (d = FsImg.ROOTINO)) as [-> | Hdne].
  - rewrite lookup_insert /= /anode_ents /=.
    rewrite /cons_absent /astep /aents Hd /= /anode_ents /= in Habs.
    rewrite lookup_insert_ne; [exact Habs |].
    intros ->. destruct Hother as [Hc | Hc]; [exact (Hc eq_refl) | exact (Hc eq_refl)].
  - rewrite lookup_insert_ne; [| congruence]. exact Habs.
Qed.

Lemma cons_present_create_other (j : Z) (d : Z) (nmn : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (ma mi : Z) (av : aview) :
  cre_pre av d nmn ents nl i (ADev ma mi) ->
  cons_present_at j av ->
  cons_present_at j (delta_create d nmn i (ADev ma mi) av).
Proof.
  intros Hpre Hp. pose proof Hpre as (Hd & Hfresh & _).
  destruct (cons_present_root_dir j av Hp) as (rents & rnl & Hroot & Hnm).
  destruct Hp as (_ & Hrow & _).
  assert (Hd_j : d <> j)
    by (intros ->; rewrite Hrow in Hd; discriminate Hd).
  rewrite (delta_create_dev av d nmn ents nl i ma mi Hpre).
  apply cons_present_of_parts.
  - rewrite /astep /aents.
    destruct (decide (d = FsImg.ROOTINO)) as [-> | Hdne].
    + rewrite lookup_insert /= /anode_ents /=.
      rewrite Hroot in Hd. injection Hd as Hents Hnl. subst rents.
      rewrite lookup_insert_ne; [exact Hnm |].
      (* the console's own name cannot be the created one: [cre_pre] says
         the parent's map does not have it, and the present state says it
         does *)
      intros ->. by rewrite Hnm in Hfresh.
    + rewrite lookup_insert_ne; [| congruence].
      rewrite Hroot /= /anode_ents /=. exact Hnm.
  - rewrite lookup_insert_ne; [exact Hrow | congruence].
Qed.

(* ---- 5c.  THE UNARM AND THE TRUNC: the two that need a premise the
   commit does not carry.

   [delta_unarm i] DELETES the row at [i] and [delta_trunc i] empties the
   file at [i].  A pin at [ino] survives either exactly when [i <> ino] --
   and the two commits quantify [i] over EVERY view row at nlink 1
   ([FsAbsCreateFire.aunarm_commit_at]) and EVERY view row that is a file
   ([SysOpenDefs.atrunc_commit_at]).  /sh's row is a file at nlink 1.  So
   the premises below are honest and neither commit supplies them: that is
   this lane's friction, reported rather than hidden.  A caller holding
   [AppInv.app_sup] -- the credential that says its claim holds of EVERY
   view -- pays both steps without them, which is why no landed proof has
   met this.

   THE TWO ROW LEMMAS FIRST: a row the delta does not touch is the row it
   was.  The console's row is a DEVICE and the root's is a DIRECTORY, so
   [delta_trunc] -- which moves a FILE row -- is the identity at both
   whatever [i] is, and only the FILE pin needs [i <> ino]. *)

Lemma delta_unarm_lookup_ne (av : aview) (i k : Z) :
  k <> i -> delta_unarm i av !! k = av !! k.
Proof. intros Hne. rewrite /delta_unarm. by rewrite lookup_delete_ne. Qed.

Lemma delta_trunc_lookup_ne (av : aview) (i k : Z) :
  k <> i -> delta_trunc i av !! k = av !! k.
Proof.
  intros Hne. rewrite /delta_trunc.
  destruct (av !! i) as [a |] eqn:Hi; [| reflexivity].
  destruct (an_node a) eqn:Ha; [| reflexivity | reflexivity].
  by rewrite lookup_insert_ne.
Qed.

Lemma delta_trunc_nonfile (av : aview) (i k : Z) (n : absnode) (nl : nat) :
  av !! k = Some (MkAnode n nl) ->
  (forall bs : list (bv 8), n <> AFile bs) ->
  delta_trunc i av !! k = av !! k.
Proof.
  intros Hk Hn.
  destruct (decide (k = i)) as [-> | Hne]; [| by apply delta_trunc_lookup_ne].
  rewrite /delta_trunc Hk /=.
  destruct n as [bs | e | ma mi];
    [exfalso; exact (Hn bs eq_refl) | congruence | congruence].
Qed.

Lemma file_pin_unarm (nm : fname) (ino : Z) (bs : list (bv 8))
    (i : Z) (av : aview) :
  i <> ino -> i <> FsImg.ROOTINO ->
  file_pin nm ino bs av -> file_pin nm ino bs (delta_unarm i av).
Proof.
  intros Hne Hroot Hp.
  destruct (file_pin_root_dir nm ino bs av Hp) as (rents & rnl & Hr & Hnm).
  destruct Hp as (_ & Hrow & _).
  apply file_pin_of_parts.
  - rewrite /astep /aents (delta_unarm_lookup_ne av i FsImg.ROOTINO
                             ltac:(congruence)).
    rewrite Hr /= /anode_ents /=. exact Hnm.
  - rewrite (delta_unarm_lookup_ne av i ino ltac:(congruence)). exact Hrow.
Qed.

Lemma cons_absent_unarm (i : Z) (av : aview) :
  cons_absent av -> cons_absent (delta_unarm i av).
Proof.
  intros Habs. rewrite /cons_absent /astep /aents /delta_unarm.
  destruct (decide (i = FsImg.ROOTINO)) as [-> | Hne].
  - by rewrite lookup_delete /=.
  - rewrite lookup_delete_ne; [exact Habs | congruence].
Qed.

Lemma cons_present_unarm (j : Z) (i : Z) (av : aview) :
  i <> j -> i <> FsImg.ROOTINO ->
  cons_present_at j av -> cons_present_at j (delta_unarm i av).
Proof.
  intros Hne Hroot Hp.
  destruct (cons_present_root_dir j av Hp) as (rents & rnl & Hr & Hnm).
  destruct Hp as (_ & Hrow & _).
  apply cons_present_of_parts.
  - rewrite /astep /aents (delta_unarm_lookup_ne av i FsImg.ROOTINO
                             ltac:(congruence)).
    rewrite Hr /= /anode_ents /=. exact Hnm.
  - rewrite (delta_unarm_lookup_ne av i j ltac:(congruence)). exact Hrow.
Qed.

Lemma file_pin_trunc (nm : fname) (ino : Z) (bs : list (bv 8))
    (i : Z) (av : aview) :
  i <> ino ->
  file_pin nm ino bs av -> file_pin nm ino bs (delta_trunc i av).
Proof.
  intros Hne Hp.
  destruct (file_pin_root_dir nm ino bs av Hp) as (rents & rnl & Hr & Hnm).
  destruct Hp as (_ & Hrow & _).
  apply file_pin_of_parts.
  - rewrite /astep /aents
      (delta_trunc_nonfile av i FsImg.ROOTINO (ADir rents) rnl Hr
         ltac:(intros bs' Hc; discriminate Hc)).
    rewrite Hr /= /anode_ents /=. exact Hnm.
  - rewrite (delta_trunc_lookup_ne av i ino ltac:(congruence)). exact Hrow.
Qed.

Lemma delta_trunc_aents (av : aview) (i d : Z) :
  aents (delta_trunc i av) d = aents av d \/ aents (delta_trunc i av) d = None.
Proof.
  destruct (decide (d = i)) as [-> | Hne]; last first.
  { left. rewrite /aents (delta_trunc_lookup_ne av i d Hne). reflexivity. }
  destruct (av !! i) as [a |] eqn:Hi; last first.
  { left. rewrite /delta_trunc Hi. reflexivity. }
  destruct a as [n nl]. destruct n as [bs | e | ma mi].
  - right. rewrite /aents /delta_trunc Hi /= lookup_insert /= /anode_ents /=.
    reflexivity.
  - left. rewrite /delta_trunc Hi /=. reflexivity.
  - left. rewrite /delta_trunc Hi /=. reflexivity.
Qed.

Lemma cons_absent_trunc (i : Z) (av : aview) :
  cons_absent av -> cons_absent (delta_trunc i av).
Proof.
  intros Habs. rewrite /cons_absent /astep in Habs |- *.
  destruct (delta_trunc_aents av i FsImg.ROOTINO) as [He | He];
    rewrite He; [exact Habs | reflexivity].
Qed.

Lemma cons_present_trunc (j : Z) (i : Z) (av : aview) :
  cons_present_at j av -> cons_present_at j (delta_trunc i av).
Proof.
  intros Hp.
  destruct (cons_present_root_dir j av Hp) as (rents & rnl & Hr & Hnm).
  destruct Hp as (_ & Hrow & _). rewrite /cons_dev in Hrow.
  (* THE ONE OF THE FOUR THAT NEEDS NO SIDE CONDITION: the truncation
     moves a FILE row; the console's is a DEVICE and the root's is a
     DIRECTORY. *)
  apply cons_present_of_parts.
  - rewrite /astep /aents
      (delta_trunc_nonfile av i FsImg.ROOTINO (ADir rents) rnl Hr
         ltac:(intros bs' Hc; discriminate Hc)).
    rewrite Hr /= /anode_ents /=. exact Hnm.
  - rewrite (delta_trunc_nonfile av i j (ADev CONSOLE 0) 1%nat Hrow
               ltac:(intros bs' Hc; discriminate Hc)).
    exact Hrow.
Qed.

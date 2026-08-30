(* ====================================================================== *)
(*  FsInitPin.v -- THE ERA-0 /init PINS, RE-DERIVED ON THE ABSTRACT STATE  *)
(*  (fs-syscall-specs lane P; the port the banner at the top of            *)
(*   claude-notes/projects/namei-pinned-lookup.md asks for)                *)
(* ====================================================================== *)

(*  WHAT THIS FILE IS.  The namei-pinned-lookup campaign once proved two
    facts about era 0 and handed them out of the boot mint as GHOSTS:

      the PATH PIN     namei("/init") resolves, in the root directory, to
                       inode 7                     ([FsCfgBoot.dv_pin])
      the CONTENT PIN  inode 7 holds the image's bytes for inode 7, which
                       are [ElfUser.init_elf]      ([FsCfgBoot.fv_pin])

    Durable-disk lane E-unpin took both off the boot chain and DELETED the
    mint that produced them ([FsCfgBoot.fs_cfg_alloc]; the era's file system
    is founded from the durable SNAPSHOT now, [FsCfgSnap.fs_cfg_alloc_snap],
    at every era including era 0).  The owner's ruling was right and this
    file does not undo it: what is re-derived below is not "the disk is
    mkfs's image" -- which is false after any write -- but the strictly
    weaker, and true, sentence

        AT ERA 0, whose durable map D IS the mkfs image
        ([SystemAdequacy.fsimg_snap_ok]), every state that map denotes has
        /init at inum 7 with init_elf's bytes.

    THE (a)/(b) CHOICE, per lane P's charter.  Everything in sections 1-5 is
    ROUTE (b): a PURE fact about [era0_D] alone, quantified over EVERY
    snapshot state [S] with [snap_ok S era0_D].  Those are eternal for era
    0's D -- nothing can invalidate a fact about a fixed map -- and they are
    persistent for free ([FsDurSyscall]'s discipline: a certificate is a
    [Prop], never a share).  Only section 6 is ROUTE (a): two live-view
    corollaries stated against [FsAbs.astate]/[FsAbs.nview], for a consumer
    that holds the founded authority rather than the map.  They are consumed
    AT THE BOOT INSTANT and say nothing about any later state.

    WHY THE SNAPSHOT STATE IS THE RIGHT PLACE TO STAND.  The boot mint
    founds the era's γtop map AT THE SNAPSHOT'S OWN TABLE: the snapshot
    mint ([FsCfgSnap.fs_cfg_alloc_snap], which
    [BootShared.boot_shared_alloc] runs at EVERY era) reaches
    [FsState.fs_boot_alloc_root_slack] AT [fss_inodes S], so the authority
    [FsAbs.astate] reads is [ghost_map_auth (γtop Γ) 1 (fss_inodes S)] and
    the founded abstract view is [abs_view (fss_inodes S)] on the nose.  A
    fact about [abs_view (fss_inodes S)] for EVERY [S] over [era0_D] is
    therefore a fact about the view the era boots with, with no ghost in it.

    WHAT IS DELIBERATELY NOT HERE.  No [dv_pin]/[fv_pin] and no lend: those
    were cancellable borrows of a payload column, and the abstract state has
    its own pin story ([FsAbsPins.apr_pins], lane A(iii)).  Section 5's
    [era0_init_arun] is the composition point: it is exactly the [arun]
    premise [FsAbsPins.apr_walk] takes, so a client holding one [nview] share
    per hop gets [apath_at ... = Some 7] out of the walk with no image
    reasoning of its own.  NOTHING IS RE-ENABLED: the boot chain is not
    touched by this file, and no file requires it.

    THE LEAF RULE ([FsImgCheck.v]'s header, and [NameiInitPinned.v]'s
    precedent): this file requires [FsImgCheck], so it is an image-check
    CONSUMER and must stay a leaf.  [SystemAdequacy] already requires
    [FsImgCheck] (SystemAdequacy.v:68), so nothing new enters any cone.     *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

(* the ghost classes first, so the file-system stack's names win over the
   block layer's twins that arrive through them (durable-notes.md, "AND
   WHERE THAT IMPORT COLLIDES, PUT IT EARLY") *)
Require Import Xv6Cameras.      (* [fsTopG] / [fsLinkG] -- IMPORTED         *)
Require Import FsState.         (* [fs_state_rec], [fss_inodes]             *)

Require Import BioDefs.         (* [BSIZE]                                  *)
Require Import DinodeEnc.       (* [di_type] / [di_size] / [di_nlink]       *)
Require Import DirView.         (* [T_DIR_z]                                *)
Require Import InodeInv.        (* [MAXFILE]: [FsDurImg.img_node_file_byte]'s
                                   own bound                                *)
Require Import FsTree.          (* [fname], [file_bytes], [path_at]         *)
Require Import IcacheEscrow.    (* [region_inums_spec]                      *)
Require Import FsCrash.         (* [fs_blocks], [fs_restrict]-side names    *)
Require Import FsDurSnap.       (* [snap_ok]                                *)
Require Import FsDurSyscall.    (* [snap_holds], [dur_node], [dur_node_*]   *)
Require Import FsCfgBoot.       (* [img_node], [img_nodes_lookup],
                                   [fs_boot_image_wf]                       *)
Require Import FsDurImg.        (* [img_snap_ok], [img_state],
                                   [img_root_entries], [img_node_file_byte] *)
Require Import SystemAdequacy.  (* [fsimg_snap_ok], [fsimg_nib], [fsimg_cov] *)
Require Import FsImgDisk.       (* [fsimg_P]                                *)
Require Import FsImgCheck.      (* [fsimg_sb], [fname_init],
                                   [fsimg_init_path], [fsimg_init_at]       *)
Require Import FsImg.           (* [ROOTINO], [tree_of_disk], [fs_dinode] --
                                   AFTER [InodeInv], so [ROOTINO] means the
                                   [Z]; every use below is qualified anyway  *)
Require Import FsAbs.           (* LAST (FsAbs's own rule): [abs_of],
                                   [abs_view], [apath_at], [astate]         *)

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], which is [Local] there: the cast is built
   directly rather than reduced twice (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ====================================================================== *)
(*  1.  THE TWO IMAGE READINGS OF [abs_of], AT AN ARBITRARY IMAGE          *)
(*                                                                        *)
(*  Stated at an ARBITRARY [(P, sb)] so that the literal-image corollaries *)
(*  of section 4 are the only sentences that pay for a computation --      *)
(*  [NameiInitPinned.dv_of_path_at]'s discipline, kept.                     *)
(* ====================================================================== *)

(* ---- 1a.  A DIRECTORY: one hop at the abstract view IS one hop in the
   image's tree reading.

   Both sides are literally [DirView.dir_first]'s scan: [FsTree.dir_view_lookup]
   on the left (through [FsDurImg.img_root_entries], which is [dir_entries] at
   the image's root), [FsImg.path_at_disk_dir] on the right.  This is
   [NameiInitPinned.dv_of_path_at] restated at [FsAbs]'s [astep] instead of at
   the deleted [dv_pin]'s [dv_of]. *)
Lemma img_astep_root (P : Z -> list (bv 8)) (sb : fs_sb) (av : aview)
    (f : fname) :
  fsimg_wf P sb = true ->
  0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb ->
  av !! FsImg.ROOTINO = Some (abs_of (img_node P sb FsImg.ROOTINO)) ->
  astep av FsImg.ROOTINO f = path_at (tree_of_disk P sb) FsImg.ROOTINO [f].
Proof.
  intros Hwf Hran Hav.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb FsImg.ROOTINO)) = T_DIR_z)
    by exact (fs_root_wf_type P sb (fsimg_wf_root P sb Hwf)).
  assert (Hdir : fn_is_dir (img_node P sb FsImg.ROOTINO) = true).
  { rewrite /fn_is_dir /fn_type. by apply bool_decide_eq_true_2. }
  rewrite /astep /aents Hav /= /anode_ents (abs_of_dir _ Hdir) /=.
  rewrite (img_root_entries P sb Hwf) dir_view_lookup.
  rewrite (path_at_disk_dir P sb FsImg.ROOTINO f Hran Hty).
  reflexivity.
Qed.

(* ...and the same fact as ONE COMPLETED HOP of [apath_at]. *)
Lemma img_apath_root (P : Z -> list (bv 8)) (sb : fs_sb) (av : aview)
    (f : fname) (c : Z) :
  fsimg_wf P sb = true ->
  0 <= FsImg.ROOTINO < FsImg.sb_ninodes sb ->
  av !! FsImg.ROOTINO = Some (abs_of (img_node P sb FsImg.ROOTINO)) ->
  path_at (tree_of_disk P sb) FsImg.ROOTINO [f] = Some c ->
  apath_at av FsImg.ROOTINO [f] = Some c.
Proof.
  intros Hwf Hran Hav Hp.
  rewrite apath_at_cons (img_astep_root P sb av f Hwf Hran Hav) Hp.
  exact (apath_at_nil av c).
Qed.

(* ---- 1b.  A FILE: the node's [fn_file_bytes] IS the image's own byte
   reading.  [FsDurImg.img_node_file_byte] one byte at a time, with the
   size bound doing the only arithmetic ([fn_data] is partial above the
   allocated slots, and [file_bytes] only ever consults below the size). *)
Lemma img_file_bytes (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  bv_unsigned (di_size (fs_dinode P sb z)) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  fn_file_bytes (img_node P sb z)
  = file_bytes (fs_data_of P (fs_dinode P sb z))
      (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb z)))).
Proof.
  intros Hsz.
  pose proof (proj1 (bv_unsigned_in_range _ (di_size (fs_dinode P sb z))))
    as H0.
  assert (Hm : (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb z)))
                <= MAXFILE * BSIZE)%nat).
  { apply Nat2Z.inj_le. rewrite (Z2Nat.id _ H0).
    rewrite Nat2Z.inj_mul. exact Hsz. }
  assert (Hs : fn_size (img_node P sb z)
               = bv_unsigned (di_size (fs_dinode P sb z))) by reflexivity.
  rewrite /fn_file_bytes Hs /file_bytes.
  apply list_eq. intros k. rewrite !list_lookup_fmap.
  destruct (seq 0 (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb z)))) !! k)
    as [x |] eqn:E; [| reflexivity].
  apply lookup_seq in E as [-> Hlt]. simpl. f_equal.
  apply img_node_file_byte. lia.
Qed.

(* ...and the ABSTRACT NODE at a file inum, which is what the content pin's
   consumer reads: the whole row, bytes and nlink. *)
Lemma img_abs_file (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  bv_unsigned (di_type (fs_dinode P sb z)) = T_FILE_z ->
  bv_unsigned (di_size (fs_dinode P sb z)) <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  abs_of (img_node P sb z)
  = MkAnode
      (AFile (file_bytes (fs_data_of P (fs_dinode P sb z))
                (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb z))))))
      (Z.to_nat (bv_unsigned (di_nlink (fs_dinode P sb z)))).
Proof.
  intros Hty Hsz.
  assert (Hft : fn_type (img_node P sb z) = T_FILE_z) by exact Hty.
  assert (Hnd : fn_is_dir (img_node P sb z) = false).
  { rewrite /fn_is_dir. apply bool_decide_eq_false_2.
    rewrite Hft. cbv [T_FILE_z T_DIR_z]. lia. }
  assert (Hnode : abs_node (img_node P sb z)
                  = AFile (file_bytes (fs_data_of P (fs_dinode P sb z))
                             (Z.to_nat
                                (bv_unsigned (di_size (fs_dinode P sb z)))))).
  { rewrite /abs_node Hnd.
    destruct (decide (fn_type (img_node P sb z) = T_FILE_z)) as [_ | Hc];
      [f_equal; exact (img_file_bytes P sb z Hsz) | exfalso; exact (Hc Hft)]. }
  rewrite /abs_of Hnode. reflexivity.
Qed.

(* ====================================================================== *)
(*  2.  THE ERA-0 PREMISE, AND THE DURABLE ROW IT PINS                     *)
(*                                                                        *)
(*  THE PREMISE'S EXACT LANDED SPELLING is [SystemAdequacy.fsimg_snap_ok]  *)
(*  -- [snap_ok (img_state fsimg_P fsimg_sb fsimg_nib) (fs_restrict        *)
(*  fsimg_P (fs_home_set fsimg_cov (sb_logstart fsimg_sb)))] -- which is   *)
(*  [FsDurImg.img_snap_ok] at [SystemAdequacy.fsimg_image_wf].  It is the  *)
(*  ONE equation about the INITIAL machine that [SystemAdequacy]'s header  *)
(*  allows itself, and it is what makes era 0's [D] the mkfs image.        *)
(* ====================================================================== *)

(* ---- 2a.  the generic move: an image inum's node IS the durable table's,
   at whatever state the map denotes.  [FsDurSyscall.dur_node_of_snap]
   against [img_snap_ok]; [snap_node_det] is what makes the [S] it was
   proved at irrelevant. *)
Lemma img_dur_node (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (nib : nat)
    (cov : gset Z) (z : Z) :
  fs_boot_image_wf dk ndisk sb nib cov ->
  0 <= z < 16 * Z.of_nat nib ->
  dur_node (fs_restrict (fs_blocks dk)
              (fs_home_set cov (FsImg.sb_logstart sb)))
           z (img_node (fs_blocks dk) sb z).
Proof.
  intros Hwf Hz.
  pose proof (img_snap_ok dk ndisk sb nib cov Hwf) as Hok.
  assert (Hnibq : Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1)
    by (destruct Hwf as (_ & _ & _ & _ & _ & H & _); exact H).
  apply (dur_node_of_snap (img_state (fs_blocks dk) sb nib) _ z).
  - exact Hok.
  - simpl. rewrite <- Hnibq. exact Hz.
  - simpl. apply img_nodes_lookup, region_inums_spec. exact Hz.
Qed.

(* ---- 2b.  ERA 0's OWN MAP, named once ------------------------------- *)

Definition era0_D : gmap Z (list (bv 8)) :=
  fs_restrict fsimg_P (fs_home_set fsimg_cov (FsImg.sb_logstart fsimg_sb)).

Lemma era0_snap_holds : snap_holds era0_D.
Proof.
  exists (img_state fsimg_P fsimg_sb fsimg_nib). exact fsimg_snap_ok.
Qed.

(* the two inums the pins name.  [INIT_INO] is read off
   [FsImgCheck.fsimg_init_path]: "init" resolves, in the root, to 7. *)
Definition INIT_INO : Z := 7.
Definition init_path : list fname := [fname_init].
Definition init_bytes : list (bv 8) := ElfUser.init_elf.

Lemma era0_dur_root :
  dur_node era0_D FsImg.ROOTINO (img_node fsimg_P fsimg_sb FsImg.ROOTINO).
Proof.
  apply (img_dur_node FsImgDisk.fsimg_dk XV6_DISK_BYTES fsimg_sb fsimg_nib
           fsimg_cov FsImg.ROOTINO fsimg_image_wf).
  cbv [FsImg.ROOTINO fsimg_nib]. lia.
Qed.

Lemma era0_dur_init :
  dur_node era0_D INIT_INO (img_node fsimg_P fsimg_sb INIT_INO).
Proof.
  apply (img_dur_node FsImgDisk.fsimg_dk XV6_DISK_BYTES fsimg_sb fsimg_nib
           fsimg_cov INIT_INO fsimg_image_wf).
  cbv [INIT_INO fsimg_nib]. lia.
Qed.

(* ...and the row at an ARBITRARY state the map denotes, which is the form
   the abstract view is read through. *)
Lemma era0_row (S : fs_state_rec) (z : Z) (n : fs_node) :
  snap_ok S era0_D -> dur_node era0_D z n -> fss_inodes S !! z = Some n.
Proof. intros HS Hd. exact (Hd S HS). Qed.

Lemma era0_arow (S : fs_state_rec) (z : Z) (n : fs_node) :
  snap_ok S era0_D -> dur_node era0_D z n ->
  abs_view (fss_inodes S) !! z = Some (abs_of n).
Proof.
  intros HS Hd. exact (abs_view_lookup _ z n (era0_row S z n HS Hd)).
Qed.

(* ====================================================================== *)
(*  3.  THE LITERAL IMAGE'S TWO READINGS                                   *)
(*                                                                        *)
(*  The only sentences in this file that compute.  Each decodes ONE inode  *)
(*  record out of the image's inode block -- the same cost                 *)
(*  [FsImgCheck.fsimg_init_type] pays -- and NO file's contents are        *)
(*  forced: the bytes come in through [fsimg_init_at], which               *)
(*  [FsImgCheck] already proved and which is CITED, not re-run.            *)
(* ====================================================================== *)

Lemma fsimg_init_size :
  bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb INIT_INO)) = 35976.
Proof. vm_eq. Qed.

Lemma fsimg_init_nlink :
  Z.to_nat (bv_unsigned (di_nlink (fs_dinode fsimg_P fsimg_sb INIT_INO)))
  = 1%nat.
Proof. vm_eq. Qed.

Lemma maxfile_bytes : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432.
Proof. vm_eq. Qed.

Lemma fsimg_init_size_bound :
  bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb INIT_INO))
  <= Z.of_nat MAXFILE * Z.of_nat BSIZE.
Proof. rewrite fsimg_init_size maxfile_bytes. lia. Qed.

(* THE FILE'S BYTES, off [FsImgCheck]'s own equality.  [node_at] at a
   non-directory live record IS [file_bytes] of the image's data function
   ([FsImg.node_at_live] + [FsTree.node_of]'s else-branch), so
   [fsimg_init_at] -- "[node_at fsimg_P fsimg_sb 7 = Some (NFile
   ElfUser.init_elf)]" -- reads directly as the byte list. *)
Lemma node_at_nondir (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> T_DIR_z ->
  node_at P sb i
  = Some (NFile (file_bytes (fs_data_of P (fs_dinode P sb i))
                   (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb i)))))).
Proof.
  intros H0 Hd. rewrite (node_at_live P sb i H0) /node_of.
  destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z))
    as [Hc | _]; [exfalso; exact (Hd Hc) | reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE ONE PERFORMANCE RULE THIS FILE HAD TO LEARN, MEASURED               *)
(*                                                                        *)
(*  [Some (NFile _)] IS INJECTIVE -- AND IT MUST BE PROVED AT VARIABLES.    *)
(*  Closing the /init instance DIRECTLY, by [injection] on or [exact]       *)
(*  against an equation one of whose sides is the 35,976-byte literal,      *)
(*  DOES NOT FINISH.  Both spellings were measured on the mirror with       *)
(*  [coqc -time] and truncation probes: sections 1-2 compile in 35 s and    *)
(*  every sentence up to and including [node_at_nondir] is 0.00 s, while a  *)
(*  file ending at this lemma ran past 15 minutes in either spelling.  The  *)
(*  reason is [FsImgCheck.v]'s header rule: conversion is free to unfold    *)
(*  [FsTree.file_bytes] rather than the projection, and [file_bytes] is     *)
(*  QUADRATIC in the file size and rebuilds the block once per byte -- at   *)
(*  58 kB, that header says, the computation does not terminate usefully.   *)
(*                                                                        *)
(*  AT VARIABLES [b], [b'] the same proof is ONE IOTA STEP: the variable is *)
(*  rigid, so the projection is the only thing conversion CAN unfold, and   *)
(*  no file's contents are ever entered.  The instance below then closes by *)
(*  transitivity through [node_at] -- where both sides are the SAME term    *)
(*  syntactically, so the kernel compares nothing.                          *)
(* ---------------------------------------------------------------------- *)

Definition nfile_bytes (o : option fsnode) : list (bv 8) :=
  match o with Some (NFile b) => b | _ => [] end.

Lemma nfile_inj (b b' : list (bv 8)) :
  Some (NFile b) = Some (NFile b') -> b = b'.
Proof. intros H. exact (f_equal nfile_bytes H). Qed.

(* the two side conditions of [node_at_nondir] at /init, hoisted to
   top-level lemmas so the instance below can pass them as ARGUMENTS and
   never open a side goal beside the big term (durable-notes: hoist). *)
Lemma fsimg_init_type_nz :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb INIT_INO)) <> 0.
Proof. cbv [INIT_INO]. rewrite fsimg_init_type. cbv [T_FILE_z]. lia. Qed.

Lemma fsimg_init_type_nd :
  bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb INIT_INO)) <> T_DIR_z.
Proof.
  cbv [INIT_INO]. rewrite fsimg_init_type. cbv [T_FILE_z T_DIR_z]. lia.
Qed.

Lemma fsimg_init_file_bytes :
  file_bytes (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb INIT_INO))
    (Z.to_nat (bv_unsigned (di_size (fs_dinode fsimg_P fsimg_sb INIT_INO))))
  = init_bytes.
Proof.
  apply nfile_inj.
  transitivity (node_at fsimg_P fsimg_sb INIT_INO).
  - symmetry.
    exact (node_at_nondir fsimg_P fsimg_sb INIT_INO
             fsimg_init_type_nz fsimg_init_type_nd).
  - exact fsimg_init_at.
Qed.

(* THE IMAGE'S /init ROW, as an abstract node.  This is the CONTENT PIN's
   whole content, with no state and no map in it yet. *)
Lemma fsimg_init_abs :
  abs_of (img_node fsimg_P fsimg_sb INIT_INO)
  = MkAnode (AFile init_bytes) 1%nat.
Proof.
  rewrite (img_abs_file fsimg_P fsimg_sb INIT_INO fsimg_init_type
             fsimg_init_size_bound).
  rewrite fsimg_init_file_bytes fsimg_init_nlink. reflexivity.
Qed.

(* ====================================================================== *)
(*  4.  THE TWO PINS -- ROUTE (b), PURE IN [era0_D]                        *)
(*                                                                        *)
(*  Each is quantified over EVERY [S] the era-0 map denotes, so neither    *)
(*  names the state the boot mint happened to found at, and neither can be *)
(*  invalidated by anything: they are facts about a fixed [gmap].          *)
(* ====================================================================== *)

(* ---- THE PATH PIN --------------------------------------------------- *)

Theorem era0_init_path_pin (S : fs_state_rec) :
  snap_ok S era0_D ->
  apath_at (abs_view (fss_inodes S)) FsImg.ROOTINO init_path = Some INIT_INO.
Proof.
  intros HS.
  apply (img_apath_root fsimg_P fsimg_sb _ fname_init INIT_INO fsimg_wf_ok).
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_arow S FsImg.ROOTINO _ HS era0_dur_root).
  - exact fsimg_init_path.
Qed.

(* ---- THE CONTENT PIN ------------------------------------------------ *)

Theorem era0_init_content_pin (S : fs_state_rec) :
  snap_ok S era0_D ->
  abs_view (fss_inodes S) !! INIT_INO = Some (MkAnode (AFile init_bytes) 1%nat).
Proof.
  intros HS.
  rewrite (era0_arow S INIT_INO _ HS era0_dur_init) fsimg_init_abs.
  reflexivity.
Qed.

(* ...and the root's row, which the path pin consumed and which a caller
   that wants to keep walking needs in its own right. *)
Theorem era0_root_row (S : fs_state_rec) :
  snap_ok S era0_D ->
  abs_view (fss_inodes S) !! FsImg.ROOTINO
  = Some (abs_of (img_node fsimg_P fsimg_sb FsImg.ROOTINO)).
Proof. intros HS. exact (era0_arow S FsImg.ROOTINO _ HS era0_dur_root). Qed.

(* ====================================================================== *)
(*  5.  THE ERA-WALK INSTANTIATION                                         *)
(*                                                                        *)
(*  [FsAbsPins.apr_walk] -- lane A(iii)'s LIVE replacement for the deleted *)
(*  [DirViewPin.wp_namei_pinned] -- takes exactly one pure premise about   *)
(*  the abstract state: [FsAbs.arun av root ps ds], the list of inums the  *)
(*  walk visits.  At era 0 that list is [[ROOTINO; 7]], and this is it.    *)
(*  A client holding one [nview] share per hop gets                        *)
(*  [apath_at av ROOTINO ["init"] = Some 7] out of the walk with no image  *)
(*  reasoning of its own.                                                  *)
(* ====================================================================== *)

Theorem era0_init_arun (S : fs_state_rec) :
  snap_ok S era0_D ->
  arun (abs_view (fss_inodes S)) FsImg.ROOTINO init_path
       [FsImg.ROOTINO; INIT_INO].
Proof.
  intros HS.
  (* [eapply]: [ARun_cons]'s hop target [c] is not in its conclusion, so it
     is fixed by the TAIL run ([ARun_nil] at [[INIT_INO]]) and read back
     into the hop's goal. *)
  eapply ARun_cons; [| apply ARun_nil].
  rewrite (img_astep_root fsimg_P fsimg_sb _ fname_init fsimg_wf_ok).
  - exact fsimg_init_path.
  - cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]. lia.
  - exact (era0_root_row S HS).
Qed.

(* ====================================================================== *)
(*  6.  ROUTE (a): THE SAME TWO PINS AT THE FOUNDED LIVE VIEW              *)
(*                                                                        *)
(*  For a consumer that holds the boot mint's authority rather than the    *)
(*  map.  [FsCfgSnap.v:1006] founds [γtop] at [fss_inodes S], so the       *)
(*  founded [FsAbs.astate] is [astate Γ (abs_view (fss_inodes S))] and     *)
(*  these two are the section-4 pins read through it.  THEY ARE TIMELESS   *)
(*  AND CONSUMED AT THE BOOT INSTANT: an [astate] is the exclusive         *)
(*  authority, so holding one is already knowing the era has not moved.    *)
(* ====================================================================== *)

Section Era0Live.
  (* [FsAbs.v]'s own binder list, verbatim: [fsLinkG]/[fsTopG] are [xv6G]
     MEMBERS and this file binds the members, never the bundle. *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* THE PATH PIN, live.  The authority is handed straight back: the pin is
     a fact about the map it carries, so nothing is spent. *)
  Lemma astate_era0_init_path Γ (S : fs_state_rec) :
    snap_ok S era0_D ->
    astate Γ (abs_view (fss_inodes S)) -∗
      astate Γ (abs_view (fss_inodes S))
      ∗ ⌜apath_at (abs_view (fss_inodes S)) FsImg.ROOTINO init_path
         = Some INIT_INO⌝.
  Proof.
    intros HS. iIntros "Hst". iFrame "Hst". iPureIntro.
    exact (era0_init_path_pin S HS).
  Qed.

  (* THE CONTENT PIN, live: a client-held share of inum 7 IS /init's bytes.
     [FsAbs.astate_nview] is the agreement; the pin supplies the row. *)
  Lemma nview_era0_init Γ (S : fs_state_rec) (q : Qp) (a : anode) :
    snap_ok S era0_D ->
    astate Γ (abs_view (fss_inodes S)) -∗ nview Γ q INIT_INO a -∗
      ⌜a = MkAnode (AFile init_bytes) 1%nat⌝.
  Proof.
    intros HS. iIntros "Hst Hn".
    iDestruct (astate_nview with "Hst Hn") as %Hav.
    iPureIntro.
    rewrite (era0_init_content_pin S HS) in Hav.
    (* [Some_inj], NOT [injection]: see section 3's performance rule -- the
       row carries [init_bytes] and [injection] would normalise it. *)
    apply Some_inj in Hav. symmetry. exact Hav.
  Qed.

End Era0Live.

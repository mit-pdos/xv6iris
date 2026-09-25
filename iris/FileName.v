(* ===================================================================== *)
(*  FileName.v -- THE CLASS OF USER FILE NAMES and the five laws every     *)
(*  layer above it may use (cut W0; design of record:                     *)
(*  claude-notes/design/filenames.md section 0).                          *)
(*                                                                        *)
(*  The owner ruled that the file model widens from the one name `f` to  *)
(*  a CLASS of user files such as `*.txt`, and NOT the image's binaries   *)
(*  (so `cat /sh` is never admitted).  A class is a predicate on names;   *)
(*  nothing above this file reads a class's definition, only the laws:    *)
(*                                                                        *)
(*    L1 (lexable)          nonempty, every byte a [fn_byte] -- an         *)
(*                          alphanumeric or the dot; so no blank, slash,  *)
(*                          NUL, dollar, newline or sh symbol;            *)
(*    L2 (stored verbatim)  shorter than [DIRSIZ], so the name stays on   *)
(*                          skipelem's NUL-terminated branch;             *)
(*    L3 (not a system name) none of [sys_names]: the dots, the console   *)
(*                          node /init creates, the pinned binaries;      *)
(*    L4 (absent from the image) no name of the mkfs root is in the       *)
(*                          class -- ONE computation over the root block, *)
(*                          the same form as [TreeImg.img_root_inj_ok];   *)
(*    L5 (decidable)        the [Decision] instance [name_laws] is        *)
(*                          indexed by, which also keeps the input        *)
(*                          discipline decidable.                        *)
(*                                                                        *)
(*  THREE INSTANCES, each with every law proved:                          *)
(*    [txt_name]  `stem.txt` for an alphanumeric stem of at most nine     *)
(*                bytes -- THE MODEL'S CLASS ([FileDisc.uname] is it,     *)
(*                cut W4; its syntax is [FileClass], its laws           *)
(*                [txt_laws] here);                                       *)
(*    [f_name]    the one name [fname_f], the class before cut W4;       *)
(*    [one_name]  one alphanumeric byte (62 names, `f` among them), the   *)
(*                fallback the dot did not need.                         *)
(*                                                                        *)
(*  Each instance is decided by a boolean over [bv_unsigned] ([alnumb],   *)
(*  [bytes_eqb]) so that L3 and L4 are closed by the virtual machine      *)
(*  without unfolding any stdpp decision procedure.                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import LineWords.       (* [wl_alnum], [wl_word], [fn_byte] *)
Require Export FileClass.       (* the class [txt_name] and its deciders *)
Require Import DirentEnc.       (* [DIRSIZ] *)
Require Import FsTree.          (* [fname], [DOT], [DOTDOT] *)
Require Import FsImgCheck.      (* [fsimg_byte], the pinned names, [fname_f] *)
Require Import FsConsPin.       (* [fname_console] *)
Require Import TreeImg.         (* [img_root_ents] *)
Require Import FsState.         (* [fs_state_rec], [fss_inodes] *)
Require Import FsStateInode.    (* [dir_entries] *)
Require Import FsCrash.         (* [fs_blocks], [fs_recovery] *)
Require Import FsDurSnap.       (* [snap_ok] *)
Require Import FsImgDisk.       (* [fsimg_P] *)
Require Import FsBootParams.    (* [fsimg_cov] *)
Require Import FsCfgBoot.       (* [img_node] *)
Require Import FsAbsDefs.       (* [astep], [abs_view], [abs_row_dir] *)
Require Import FsInitPin.       (* [era0_D], [era0_root_row], [fsimg_root_dir] *)
Require Import FsInitPinBoot.   (* [era0_recovery_D] *)
Require FsImg.                  (* [ROOTINO] *)
From stdpp Require Import ssreflect.
Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], [Local] there and in every consumer leaf:
   the cast is built directly rather than reduced twice
   (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ===================================================================== *)
(*  1.  THE ALPHABET AND THE SYSTEM NAMES                                 *)
(* ===================================================================== *)

(* the alphabet [fn_byte] is [LineWords]', the class's syntax
   [FileClass]'s *)

(* the names a user file may never take: the two every directory has,
   the console node /init makes, and the binaries the claim pins *)
Definition sys_names : list fname :=
  [DOT; DOTDOT; fname_console;
   fname_init; fname_sh; fname_echo; fname_cat; fname_sync; fname_grep].

(* ===================================================================== *)
(*  2.  THE LAWS                                                          *)
(* ===================================================================== *)

Record name_laws (P : fname -> Prop) `{!forall N, Decision (P N)} : Prop :=
  MkNameLaws {
    nl_lex : forall N, P N -> N <> [] /\ Forall fn_byte N;          (* L1 *)
    nl_len : forall N, P N -> (length N < DIRSIZ)%nat;               (* L2 *)
    nl_sys : forall N, P N -> N ∉ sys_names;                         (* L3 *)
    nl_img : map_Forall (fun nm _ => ~ P nm) img_root_ents           (* L4 *)
  }.
(* L5 is the [Decision] instance the record is indexed by. *)

(* ===================================================================== *)
(*  3.  BOOLEAN DECIDERS OVER [bv_unsigned]                               *)
(* ===================================================================== *)

(* [alnumb], [bytes_eqb], [wordb] and their specs are [FileClass]'s *)

(* a class is excluded from a finite name list by one boolean sweep *)
Lemma not_in_of_forallb (P : fname -> Prop) (p : fname -> bool) (l : list fname) :
  (forall N, P N -> p N = true) ->
  forallb (fun N => negb (p N)) l = true ->
  forall N, P N -> N ∉ l.
Proof using.
  intros Hp Hl N HN Hin. apply elem_of_list_In in Hin.
  rewrite List.forallb_forall in Hl. specialize (Hl N Hin).
  rewrite (Hp N HN) in Hl. discriminate.
Qed.

(* and from a map's domain by one sweep of its association list *)
Lemma map_Forall_of_forallb (P : fname -> Prop) (p : fname -> bool)
    (m : gmap fname Z) :
  (forall N, P N -> p N = true) ->
  forallb (fun kv : fname * Z => negb (p kv.1)) (map_to_list m) = true ->
  map_Forall (fun nm _ => ~ P nm) m.
Proof using.
  intros Hp Hl nm z Hnm HP.
  assert (Hin : In (nm, z) (map_to_list m))
    by (apply elem_of_list_In; by apply elem_of_map_to_list).
  rewrite List.forallb_forall in Hl. specialize (Hl _ Hin). cbn in Hl.
  rewrite (Hp nm HP) in Hl. discriminate.
Qed.

(* ===================================================================== *)
(*  4.  THE CLASS BEFORE CUT W4: THE ONE NAME [fname_f]                   *)
(* ===================================================================== *)

Definition f_name (N : fname) : Prop := N = fname_f.

Global Instance f_name_dec N : Decision (f_name N).
Proof using. rewrite /f_name. apply _. Defined.

Definition f_nameb (N : fname) : bool := bytes_eqb N fname_f.

Lemma f_nameb_of (N : fname) : f_name N -> f_nameb N = true.
Proof using. intros ->. by apply bytes_eqb_spec. Qed.

Lemma f_sys_ok : forallb (fun N => negb (f_nameb N)) sys_names = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma f_img_ok :
  forallb (fun kv : fname * Z => negb (f_nameb kv.1)) (map_to_list img_root_ents)
  = true.
Proof using. vm_eq. Qed.

Lemma f_laws : name_laws f_name.
Proof using.
  split.
  - intros N ->. split; [rewrite /fname_f; discriminate |].
    apply Forall_singleton. apply fn_byte_of_alnumb. vm_compute. reflexivity.
  - intros N ->. rewrite /fname_f /DIRSIZ /=. lia.
  - exact (not_in_of_forallb f_name f_nameb sys_names f_nameb_of f_sys_ok).
  - exact (map_Forall_of_forallb f_name f_nameb img_root_ents f_nameb_of f_img_ok).
Qed.

(* ===================================================================== *)
(*  5.  THE MODEL'S CLASS: `stem.txt`                                     *)
(* ===================================================================== *)

(* [txt_ext], [txt_name], [txt_nameb] and [txt_name_dec] are [FileClass]'s *)

Lemma txt_sys_ok : forallb (fun N => negb (txt_nameb N)) sys_names = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma txt_img_ok :
  forallb (fun kv : fname * Z => negb (txt_nameb kv.1))
    (map_to_list img_root_ents) = true.
Proof using. vm_eq. Qed.

Lemma txt_laws : name_laws txt_name.
Proof using.
  split.
  - intros N HN. exact (txt_lex N HN).
  - intros N HN. rewrite /DIRSIZ. exact (txt_len N HN).
  - exact (not_in_of_forallb txt_name txt_nameb sys_names txt_nameb_of txt_sys_ok).
  - exact (map_Forall_of_forallb txt_name txt_nameb img_root_ents
             txt_nameb_of txt_img_ok).
Qed.

(* ===================================================================== *)
(*  6.  THE FALLBACK: ONE ALPHANUMERIC BYTE                               *)
(* ===================================================================== *)

Definition one_name (N : fname) : Prop := exists b, N = [b] /\ wl_alnum b.

Definition one_nameb (N : fname) : bool :=
  match N with [b] => alnumb b | _ => false end.

Lemma one_nameb_spec (N : fname) : one_nameb N = true <-> one_name N.
Proof using.
  rewrite /one_nameb /one_name. split.
  - destruct N as [| b [| c N]]; try discriminate.
    intros H. exists b. split; [reflexivity | by apply alnumb_spec].
  - intros (b & -> & Hb). by apply alnumb_spec.
Qed.

Global Instance one_name_dec N : Decision (one_name N).
Proof using.
  destruct (one_nameb N) eqn:E.
  - left. by apply one_nameb_spec.
  - right. intros H. apply one_nameb_spec in H. congruence.
Defined.

Lemma one_nameb_of (N : fname) : one_name N -> one_nameb N = true.
Proof using. apply one_nameb_spec. Qed.

Lemma one_sys_ok : forallb (fun N => negb (one_nameb N)) sys_names = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma one_img_ok :
  forallb (fun kv : fname * Z => negb (one_nameb kv.1))
    (map_to_list img_root_ents) = true.
Proof using. vm_eq. Qed.

Lemma one_laws : name_laws one_name.
Proof using.
  split.
  - intros N (b & -> & Hb). split; [discriminate |].
    apply Forall_singleton. by left.
  - intros N (b & -> & _). rewrite /DIRSIZ /=. lia.
  - exact (not_in_of_forallb one_name one_nameb sys_names one_nameb_of one_sys_ok).
  - exact (map_Forall_of_forallb one_name one_nameb img_root_ents
             one_nameb_of one_img_ok).
Qed.

(* the class before cut W4 lies inside the fallback: `f` is one
   alphanumeric byte *)
Lemma f_name_one (N : fname) : f_name N -> one_name N.
Proof using. intros ->. apply one_nameb_spec. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  7.  WHAT THE LAWS SAY TO A LAYER ABOVE                                *)
(*                                                                        *)
(*  L3 read as the disequalities the delta legs ask for, and L4 read at   *)
(*  the view every era 0 founds at: no class name is in the root.  Both   *)
(*  are stated for ANY class with the laws, so the claim above never     *)
(*  reads a class's definition.                                          *)
(* ===================================================================== *)

Section Laws.
  Context (P : fname -> Prop) `{!forall N, Decision (P N)} (HL : name_laws P).

  Lemma nl_ne_sys (N M : fname) : P N -> M ∈ sys_names -> N <> M.
  Proof using HL. intros HN HM ->. exact (nl_sys P HL M HN HM). Qed.

  Lemma nl_ne_dot (N : fname) : P N -> N <> DOT.
  Proof using HL. intros HN. apply (nl_ne_sys N DOT HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_dotdot (N : fname) : P N -> N <> DOTDOT.
  Proof using HL. intros HN. apply (nl_ne_sys N DOTDOT HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_console (N : fname) : P N -> N <> fname_console.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_console HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_init (N : fname) : P N -> N <> fname_init.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_init HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_sh (N : fname) : P N -> N <> fname_sh.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_sh HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_echo (N : fname) : P N -> N <> fname_echo.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_echo HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_cat (N : fname) : P N -> N <> fname_cat.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_cat HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_sync (N : fname) : P N -> N <> fname_sync.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_sync HN). rewrite /sys_names. set_solver. Qed.
  Lemma nl_ne_grep (N : fname) : P N -> N <> fname_grep.
  Proof using HL. intros HN. apply (nl_ne_sys N fname_grep HN). rewrite /sys_names. set_solver. Qed.
End Laws.

(* the root's hop, at a view whose root row is a directory record's *)
Lemma astep_root_of_row (av : aview) (n : fs_node) (N : fname) :
  av !! FsImg.ROOTINO = Some (abs_row n) -> fn_is_dir n = true ->
  astep av FsImg.ROOTINO N = dir_entries n !! N.
Proof using.
  intros Hav Hd. rewrite /astep /aents Hav /= /anode_ents (abs_row_dir _ Hd) /=.
  reflexivity.
Qed.

(* ERA 0'S ROOT IS THE IMAGE'S: one hop reads [img_root_ents] *)
Lemma era0_astep_root (S : fs_state_rec) (N : fname) :
  snap_ok S era0_D ->
  astep (abs_view (fss_inodes S)) FsImg.ROOTINO N = img_root_ents !! N.
Proof using.
  intros HS.
  rewrite (astep_root_of_row _ _ N (era0_root_row S HS) fsimg_root_dir).
  by rewrite img_root_ents_eq.
Qed.

(* L4 AT ERA 0: no name of a lawful class is in the root *)
Lemma era0_class_absent (P : fname -> Prop) `{!forall N, Decision (P N)}
    (S : fs_state_rec) (N : fname) :
  name_laws P -> snap_ok S era0_D -> P N ->
  astep (abs_view (fss_inodes S)) FsImg.ROOTINO N = None.
Proof using.
  intros HL HS HN. rewrite (era0_astep_root S N HS).
  destruct (img_root_ents !! N) as [z |] eqn:Hz; [| reflexivity].
  exfalso. exact (nl_img P HL N z Hz HN).
Qed.

(* ...at every map a recovery from mkfs's image founds at *)
Lemma era0_recovery_class_absent (P : fname -> Prop) `{!forall N, Decision (P N)}
    (dk : Z -> bv 8) (D : gmap Z (list (bv 8))) (S : fs_state_rec) (N : fname) :
  name_laws P ->
  fs_blocks dk = fsimg_P ->
  fs_recovery (fs_blocks dk) D fsimg_cov (FsImg.sb_logstart fsimg_sb) ->
  snap_ok S D -> P N ->
  astep (abs_view (fss_inodes S)) FsImg.ROOTINO N = None.
Proof using.
  intros HL Hdk Hrec HS HN. apply (era0_class_absent P S N HL); [| exact HN].
  assert (HD : D = era0_D).
  { apply era0_recovery_D. rewrite <- Hdk. exact Hrec. }
  rewrite <- HD. exact HS.
Qed.

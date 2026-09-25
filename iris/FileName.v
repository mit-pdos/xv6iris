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
(*    [f_name]    the class in use today, the one name [fname_f];         *)
(*    [txt_name]  `stem.txt` for an alphanumeric stem of at most nine     *)
(*                bytes -- the class the widening lands at;               *)
(*    [one_name]  one alphanumeric byte (62 names, `f` among them), the   *)
(*                fallback if the dot does not go through the sh walks.  *)
(*                                                                        *)
(*  Each instance is decided by a boolean over [bv_unsigned] ([alnumb],   *)
(*  [bytes_eqb]) so that L3 and L4 are closed by the virtual machine      *)
(*  without unfolding any stdpp decision procedure.                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import gmap list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import LineWords.       (* [wl_alnum], [wl_word] *)
Require Import DirentEnc.       (* [DIRSIZ] *)
Require Import FsTree.          (* [fname], [DOT], [DOTDOT] *)
Require Import FsImgCheck.      (* [fsimg_byte], the pinned names, [fname_f] *)
Require Import FsConsPin.       (* [fname_console] *)
Require Import TreeImg.         (* [img_root_ents] *)
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

(* the dot, spelled the way [FsTree.DOT] spells it *)
Definition fn_dot : bv 8 := fsimg_byte 0x2e.

Definition fn_byte (b : bv 8) : Prop := wl_alnum b \/ b = fn_dot.

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

Definition alnumb (b : bv 8) : bool :=
  let z := bv_unsigned b in
  ((48 <=? z) && (z <=? 57)) || ((65 <=? z) && (z <=? 90))
  || ((97 <=? z) && (z <=? 122)).

Lemma alnumb_spec (b : bv 8) : alnumb b = true <-> wl_alnum b.
Proof using.
  rewrite /alnumb /wl_alnum.
  rewrite !orb_true_iff !andb_true_iff !Z.leb_le. tauto.
Qed.

Fixpoint bytes_eqb (u v : list (bv 8)) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => Z.eqb (bv_unsigned a) (bv_unsigned b) && bytes_eqb u' v'
  | _, _ => false
  end.

Lemma bytes_eqb_spec (u v : list (bv 8)) : bytes_eqb u v = true <-> u = v.
Proof using.
  revert v. induction u as [| a u IH]; intros [| b v]; cbn.
  - done.
  - split; [discriminate | intros H; discriminate H].
  - split; [discriminate | intros H; discriminate H].
  - rewrite andb_true_iff Z.eqb_eq IH -bv_eq. split.
    + by intros [-> ->].
    + by intros [= -> ->].
Qed.

Definition wordb (w : list (bv 8)) : bool :=
  match w with [] => false | _ => forallb alnumb w end.

Lemma wordb_spec (w : list (bv 8)) : wordb w = true <-> wl_word w.
Proof using.
  rewrite /wordb /wl_word. destruct w as [| b w].
  - split; [discriminate | by intros []].
  - rewrite List.forallb_forall -List.Forall_forall. split.
    + intros H. split; [discriminate |].
      eapply Forall_impl; [exact H | intros x Hx; by apply alnumb_spec].
    + intros [_ H]. eapply Forall_impl; [exact H | intros x Hx; by apply alnumb_spec].
Qed.

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

Lemma fn_byte_of_alnumb (b : bv 8) : alnumb b = true -> fn_byte b.
Proof using. intros H. left. by apply alnumb_spec. Qed.

(* ===================================================================== *)
(*  4.  THE CLASS IN USE TODAY: THE ONE NAME [fname_f]                    *)
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
(*  5.  THE WIDENED CLASS: `stem.txt`                                     *)
(* ===================================================================== *)

Definition txt_ext : fname :=
  [fn_dot; fsimg_byte 0x74; fsimg_byte 0x78; fsimg_byte 0x74].

Definition txt_name (N : fname) : Prop :=
  exists stem, N = stem ++ txt_ext /\ wl_word stem /\ (length stem <= 9)%nat.

Definition txt_nameb (N : fname) : bool :=
  Nat.leb 5 (length N) && Nat.leb (length N) 13
  && bytes_eqb (drop (length N - 4) N) txt_ext
  && wordb (take (length N - 4) N).

Lemma txt_nameb_spec (N : fname) : txt_nameb N = true <-> txt_name N.
Proof using.
  rewrite /txt_nameb /txt_name.
  rewrite !andb_true_iff !Nat.leb_le bytes_eqb_spec wordb_spec.
  split.
  - intros [[[H5 H13] Hd] Hw]. exists (take (length N - 4) N).
    split_and!; [| exact Hw | rewrite length_take; lia].
    by rewrite -Hd take_drop.
  - intros (stem & -> & Hw & Hl).
    pose proof (wl_word_pos stem Hw) as Hpos.
    rewrite length_app /=.
    replace (length stem + 4 - 4)%nat with (length stem) by lia.
    rewrite drop_app_length take_app_length.
    split_and!; [lia | lia | reflexivity | exact Hw].
Qed.

Global Instance txt_name_dec N : Decision (txt_name N).
Proof using.
  destruct (txt_nameb N) eqn:E.
  - left. by apply txt_nameb_spec.
  - right. intros H. apply txt_nameb_spec in H. congruence.
Defined.

Lemma txt_nameb_of (N : fname) : txt_name N -> txt_nameb N = true.
Proof using. apply txt_nameb_spec. Qed.

Lemma txt_sys_ok : forallb (fun N => negb (txt_nameb N)) sys_names = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma txt_img_ok :
  forallb (fun kv : fname * Z => negb (txt_nameb kv.1))
    (map_to_list img_root_ents) = true.
Proof using. vm_eq. Qed.

Lemma txt_ext_bytes : Forall fn_byte txt_ext.
Proof using.
  constructor; [by right |].
  do 3 (constructor; [apply fn_byte_of_alnumb; vm_compute; reflexivity |]).
  constructor.
Qed.

Lemma txt_laws : name_laws txt_name.
Proof using.
  split.
  - intros N (stem & -> & [Hne Hw] & _). split.
    + by destruct stem.
    + apply Forall_app. split; [| exact txt_ext_bytes].
      eapply Forall_impl; [exact Hw | intros b Hb; by left].
  - intros N (stem & -> & _ & Hl). rewrite length_app /= /DIRSIZ. lia.
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

(* the class in use today lies inside the fallback: `f` is one
   alphanumeric byte *)
Lemma f_name_one (N : fname) : f_name N -> one_name N.
Proof using. intros ->. apply one_nameb_spec. vm_compute. reflexivity. Qed.

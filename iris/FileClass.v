(* ===================================================================== *)
(*  FileClass.v -- THE MODEL'S CLASS OF USER FILE NAMES, `stem.txt`       *)
(*  (cut W4; design of record: claude-notes/design/filenames.md          *)
(*  section 0).                                                          *)
(*                                                                        *)
(*  The owner ruled that the file model widens from the one name `f` to  *)
(*  a class of user files such as `*.txt`, and NOT the image's binaries. *)
(*  This file is the class and its two SYNTACTIC laws, over nothing but   *)
(*  the word vocabulary, so that the pure model ([FileDisc.uname]) can   *)
(*  be stated at it without loading the image:                            *)
(*                                                                        *)
(*    [txt_name N]  N is an alphanumeric stem of one to nine bytes, then  *)
(*                  the four bytes `.txt`;                                *)
(*    [txt_lex]     L1: N is an [fn_word] (nonempty, alphanumerics and   *)
(*                  the dot, so no blank, slash, NUL or sh symbol);       *)
(*    [txt_len]     L2: N is shorter than DIRSIZ (fourteen);              *)
(*    [txt_name_dec] L5, by a boolean over [bv_unsigned].                 *)
(*                                                                        *)
(*  L3 (no system name) and L4 (absent from the mkfs root) read the       *)
(*  image, and are [FileName.txt_laws].                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.       (* [wl_alnum], [wl_word], [fn_byte], [fn_word] *)
From stdpp Require Import ssreflect.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  BOOLEAN DECIDERS OVER [bv_unsigned]                               *)
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

Lemma fn_byte_of_alnumb (b : bv 8) : alnumb b = true -> fn_byte b.
Proof using. intros H. left. by apply alnumb_spec. Qed.

(* ===================================================================== *)
(*  2.  THE CLASS                                                         *)
(* ===================================================================== *)

Definition txt_ext : list (bv 8) :=
  [fn_dot; Z_to_bv 8 0x74; Z_to_bv 8 0x78; Z_to_bv 8 0x74].

Definition txt_name (N : list (bv 8)) : Prop :=
  exists stem, N = stem ++ txt_ext /\ wl_word stem /\ (length stem <= 9)%nat.

Definition txt_nameb (N : list (bv 8)) : bool :=
  Nat.leb 5 (length N) && Nat.leb (length N) 13
  && bytes_eqb (drop (length N - 4) N) txt_ext
  && wordb (take (length N - 4) N).

Lemma txt_nameb_spec (N : list (bv 8)) : txt_nameb N = true <-> txt_name N.
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

Lemma txt_nameb_of (N : list (bv 8)) : txt_name N -> txt_nameb N = true.
Proof using. apply txt_nameb_spec. Qed.

(* ===================================================================== *)
(*  3.  THE TWO SYNTACTIC LAWS                                            *)
(* ===================================================================== *)

Lemma txt_ext_bytes : Forall fn_byte txt_ext.
Proof using.
  constructor; [by right |].
  do 3 (constructor; [apply fn_byte_of_alnumb; vm_compute; reflexivity |]).
  constructor.
Qed.

(* L1 *)
Lemma txt_lex (N : list (bv 8)) : txt_name N -> fn_word N.
Proof using.
  intros (stem & -> & [Hne Hw] & _). split.
  - by destruct stem.
  - apply Forall_app. split; [| exact txt_ext_bytes].
    eapply Forall_impl; [exact Hw | intros b Hb; by left].
Qed.

(* L2 *)
Lemma txt_len (N : list (bv 8)) : txt_name N -> (length N < 14)%nat.
Proof using. intros (stem & -> & _ & Hl). rewrite length_app /=. lia. Qed.

(* the class is inhabited, by computation: `a.txt` *)
Definition txt_a : list (bv 8) := Z_to_bv 8 97 :: txt_ext.

Lemma txt_a_name : txt_name txt_a.
Proof using. apply txt_nameb_spec. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  4.  EVERY PREFIX OF A CLASS NAME COMPLETES IN THE CLASS                *)
(*                                                                        *)
(*  by one of six fixed suffixes.  The union's decider reads a name only  *)
(*  as far as a wire shows it ([UnionDecU.gcands]): a diagnostic cut off  *)
(*  mid-name is some class name's, and this says which six to try.       *)
(* ===================================================================== *)
Definition txt_sfx : list (list (bv 8)) :=
  [drop 4 txt_ext; drop 3 txt_ext; drop 2 txt_ext; drop 1 txt_ext; txt_ext; txt_a].

Lemma txt_prefix_complete (w g : list (bv 8)) :
  txt_name g -> w `prefix_of` g -> exists z, z ∈ txt_sfx /\ txt_name (w ++ z).
Proof using.
  intros (stem & -> & [Hne Hw] & Hl) [r Hr].
  assert (Hwt : w = take (length w) (stem ++ txt_ext)) by (rewrite Hr take_app_length; reflexivity).
  assert (Hlen : (length w <= length stem + 4)%nat).
  { apply (f_equal length) in Hr. rewrite !length_app in Hr. cbn in Hr. lia. }
  rewrite take_app in Hwt.
  destruct (decide (length w <= length stem)%nat) as [Hle | Hgt].
  - replace (length w - length stem)%nat with 0%nat in Hwt by lia.
    rewrite take_0 app_nil_r in Hwt.
    destruct w as [| b w'].
    + exists txt_a. split; [do 5 apply elem_of_list_further; apply elem_of_list_here |].
      exact txt_a_name.
    + exists txt_ext. split; [do 4 apply elem_of_list_further; apply elem_of_list_here |].
      exists (b :: w'). split; [reflexivity |]. split; [split; [discriminate |] | lia].
      rewrite Hwt. apply Forall_take. exact Hw.
  - rewrite (take_ge stem) in Hwt; [| lia].
    set (k := (length w - length stem)%nat) in *.
    exists (drop k txt_ext). split.
    + assert (Hk : (1 <= k <= 4)%nat) by lia.
      destruct k as [| [| [| [| [| k]]]]]; try lia;
        repeat first [ apply elem_of_list_here | apply elem_of_list_further ].
    + exists stem. split; [| split; [split; [exact Hne | exact Hw] | exact Hl]].
      rewrite Hwt -app_assoc take_drop. reflexivity.
Qed.

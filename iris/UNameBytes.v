(* ===================================================================== *)
(*  UNameBytes.v -- THE BYTE LAYOUTS AROUND A CLASS NAME OF ANY LENGTH    *)
(*  (cut W3; claude-notes/design/filenames.md section 4).  Pure list     *)
(*  facts, no law: the redirect suffix sh reads, the refused open's       *)
(*  diagnostic `open N failed` it prints, and the line `cat N`.  Split    *)
(*  from [UNamePath] (which reads the class laws) so the lexer tier,      *)
(*  a pure file, can import it.                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.        (* [sb], [nlb], [u_prompt] *)
Require FileDisc.
From stdpp Require Import ssreflect.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S2  THE BYTE LAYOUTS AROUND A NAME OF ANY LENGTH                       *)
(* ===================================================================== *)

(* the redirect suffix ' ' '>' ' ' then the name *)
Lemma suf_gt_len (nm : list (bv 8)) : length (FileDisc.suf_gt nm) = (3 + length nm)%nat.
Proof using. unfold FileDisc.suf_gt. rewrite length_app. reflexivity. Qed.

Lemma suf_gt_0 (nm : list (bv 8)) : FileDisc.suf_gt nm !!! 0%nat = wl_sp.
Proof using.
  unfold FileDisc.suf_gt. rewrite (wl_lta_app_l _ nm 0%nat); [| simpl; lia].
  apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma suf_gt_1 (nm : list (bv 8)) : FileDisc.suf_gt nm !!! 1%nat = Z_to_bv 8 62.
Proof using.
  unfold FileDisc.suf_gt. rewrite (wl_lta_app_l _ nm 1%nat); [| simpl; lia].
  apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma suf_gt_2 (nm : list (bv 8)) : FileDisc.suf_gt nm !!! 2%nat = wl_sp.
Proof using.
  unfold FileDisc.suf_gt. rewrite (wl_lta_app_l _ nm 2%nat); [| simpl; lia].
  apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma suf_gt_name (nm : list (bv 8)) (j : nat) :
  FileDisc.suf_gt nm !!! (3 + j)%nat = nm !!! j.
Proof using.
  unfold FileDisc.suf_gt. exact (wl_lta_app_r (sb " > "%string) nm j).
Qed.

(* `open N failed\n` then the prompt, as one list: the format's two
   windows around the name *)
Definition openfail_pre : list (bv 8) := sb "open "%string.
Definition openfail_suf : list (bv 8) := sb " failed"%string ++ nlb.

Lemma alt_openfailN_eq (nm : list (bv 8)) :
  FileDisc.alt_openfailN nm = openfail_pre ++ nm ++ openfail_suf ++ u_prompt.
Proof using.
  unfold FileDisc.alt_openfailN, FileDisc.dg_openN, wl_line, wl_body.
  cbn [wl_tail].
  rewrite -!app_assoc. cbn [app]. rewrite -?app_assoc. reflexivity.
Qed.

Lemma alt_openfailN_len (nm : list (bv 8)) :
  length (FileDisc.alt_openfailN nm) = (13 + length nm + length u_prompt)%nat.
Proof using.
  rewrite alt_openfailN_eq !length_app.
  unfold openfail_pre, openfail_suf, nlb. simpl. lia.
Qed.

(* the three windows of the diagnostic *)
Lemma alt_openfailN_w1 (nm : list (bv 8)) (p : nat) :
  (p < 5)%nat -> FileDisc.alt_openfailN nm !!! p = openfail_pre !!! p.
Proof using.
  intros Hp. rewrite alt_openfailN_eq. apply wl_lta_app_l. exact Hp.
Qed.

Lemma alt_openfailN_arg (nm : list (bv 8)) (j : nat) :
  (j < length nm)%nat -> FileDisc.alt_openfailN nm !!! (5 + j)%nat = nm !!! j.
Proof using.
  intros Hj. rewrite alt_openfailN_eq.
  replace (5 + j)%nat with (length openfail_pre + j)%nat by reflexivity.
  rewrite (wl_lta_app_r openfail_pre _ j).
  apply wl_lta_app_l. exact Hj.
Qed.

Lemma alt_openfailN_w2 (nm : list (bv 8)) (i : nat) :
  (i < 8)%nat ->
  FileDisc.alt_openfailN nm !!! (5 + length nm + i)%nat = openfail_suf !!! i.
Proof using.
  intros Hi. rewrite alt_openfailN_eq.
  replace (5 + length nm + i)%nat with (length openfail_pre + (length nm + i))%nat
    by (change (length openfail_pre) with 5%nat; lia).
  rewrite (wl_lta_app_r openfail_pre _ (length nm + i)).
  rewrite (wl_lta_app_r nm _ i).
  apply wl_lta_app_l. exact Hi.
Qed.

(* the line [cat N]: its words, its length, its first four bytes *)
Definition cat_pre : list (bv 8) := sb "cat "%string.

Lemma cat_line_bytes (nm : list (bv 8)) :
  FileDisc.line_bytes (FileDisc.LCat nm) = cat_pre ++ nm ++ [wl_nl].
Proof using.
  unfold FileDisc.line_bytes, FileDisc.line_body, FileDisc.cmd_cat, wl_body.
  cbn [wl_tail].
  rewrite -!app_assoc. cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma cat_line_len (nm : list (bv 8)) :
  length (FileDisc.line_bytes (FileDisc.LCat nm)) = (5 + length nm)%nat.
Proof using.
  rewrite cat_line_bytes !length_app. unfold cat_pre. simpl. lia.
Qed.

Lemma cat_line_head (nm : list (bv 8)) (j : nat) :
  (j < 4)%nat -> FileDisc.line_bytes (FileDisc.LCat nm) !!! j = cat_pre !!! j.
Proof using. intros Hj. rewrite cat_line_bytes. apply wl_lta_app_l. exact Hj. Qed.

Lemma cat_ws_line (nm : list (bv 8)) :
  wl_line (FileDisc.uline_ws (FileDisc.LCat nm)) = FileDisc.line_bytes (FileDisc.LCat nm).
Proof using. reflexivity. Qed.

(* the diagnostic's own length, the prompt taken off: what the paid walk's
   block length is *)
Lemma alt_openfailN_nlen (nm : list (bv 8)) :
  (length (FileDisc.alt_openfailN nm) - 2 = 13 + length nm)%nat.
Proof using. rewrite alt_openfailN_len. change (length u_prompt) with 2%nat. lia. Qed.

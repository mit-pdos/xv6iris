(* ===================================================================== *)
(*  UNamePath.v -- WHAT THE PROGRAM TIER READS OFF A CLASS NAME (cut W3;  *)
(*  design of record: claude-notes/design/filenames.md section 4).        *)
(*                                                                        *)
(*  The handler, the entries and sh's redirect walks are stated at ANY    *)
(*  name [nm] of the model's class [FileDisc.uname], and they may use     *)
(*  only what [FileName.txt_laws] (L1-L5) gives:                          *)
(*                                                                        *)
(*    S1  the path facts the open leaves ask for -- the name is its own   *)
(*        one element, with no parent prefix, resolved from the cwd, and  *)
(*        carries no NUL -- all off L1 (no slash, no NUL, nonempty) and   *)
(*        L2 (shorter than DIRSIZ, so skipelem does not truncate);        *)
(*    S2  the byte layouts sh prints and reads around a name of ANY       *)
(*        length: the redirect suffix, the refused open's diagnostic      *)
(*        `open N failed`, the line `cat N` -- pure list facts, no law;   *)
(*    S4  cat's argv [cat N] is exec'able: a class name is a word of     *)
(*        name bytes by L1 ([LineWords.fn_word]; cut W4 retired the      *)
(*        non-law that it was alphanumeric).                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list gmap bitvector.definitions.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import LineWords.
Require Import EchoDisc.        (* [sb], [nlb], [u_prompt], [line_max] *)
Require Import DirentEnc.       (* [DIRSIZ] *)
Require Import FsTree.          (* [fname] *)
Require Import PathElems.       (* [path_elems], [skipelem], [SLASH] *)
Require Import ArgPath.         (* [arg_path_shape] *)
Require Import FsAbsEra.        (* [np_elems], [um_start_of] *)
Require Import FileName.        (* [name_laws], [txt_laws] *)
Require FileDisc ExecWords.
Require Export UNameBytes.   (* S2, the byte layouts: a pure file below this one *)
From stdpp Require Import ssreflect.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1  THE PATH FACTS, OFF L1 AND L2                                     *)
(* ===================================================================== *)

(* [fn_byte_val] is [LineWords]' *)

Lemma fn_byte_not_slash (b : bv 8) : fn_byte b -> b <> SLASH.
Proof using.
  intros Hb ->. apply fn_byte_val in Hb.
  assert (E : bv_unsigned SLASH = 47) by (by vm_compute). lia.
Qed.

Lemma fn_byte_not_nul (b : bv 8) : fn_byte b -> b <> (mword_of_int 0 : mword 8).
Proof using.
  intros Hb Heq. apply fn_byte_val in Hb.
  assert (E : bv_unsigned b = 0) by (rewrite Heq; by vm_compute). lia.
Qed.

(* a slash-free, nonempty name of at most 14 bytes is its own one element *)
Lemma pe_elem_rest_ns (p : list (bv 8)) : noslash p -> pe_elem p = p /\ pe_rest p = [].
Proof using.
  induction p as [| b p IH]; intros Hp; [done |].
  unfold noslash in Hp. apply Forall_cons_1 in Hp as [Hb Hp].
  rewrite (pe_elem_ne b p Hb) (pe_rest_ne b p Hb).
  destruct (IH Hp) as [-> ->]. done.
Qed.

Lemma skipelem_name (p : list (bv 8)) :
  p <> [] -> noslash p -> (length p <= 14)%nat -> skipelem p = Some (p, []).
Proof using.
  intros Hne Hns Hl. unfold skipelem.
  assert (Hsk : pe_skip p = p).
  { pose proof (pe_skip_app_ns p [] Hns Hne) as H. by rewrite !app_nil_r in H. }
  destruct (pe_elem_rest_ns p Hns) as [He Hr].
  rewrite Hsk He Hr (take_ge p 14); [| exact Hl].
  destruct p as [| b r]; [done | reflexivity].
Qed.

Section UName.
  Context (nm : fname) (Hu : FileDisc.uname nm).

  Lemma uname_lex : nm <> [] /\ Forall fn_byte nm.
  Proof using Hu. exact (nl_lex txt_name txt_laws nm Hu). Qed.

  Lemma uname_len : (length nm < DIRSIZ)%nat.
  Proof using Hu. exact (nl_len txt_name txt_laws nm Hu). Qed.

  Lemma uname_pos : (0 < length nm)%nat.
  Proof using Hu.
    destruct uname_lex as [Hne _]. destruct nm; [done | cbn; lia].
  Qed.

  Lemma uname_byte (j : nat) (b : bv 8) : nm !! j = Some b -> fn_byte b.
  Proof using Hu.
    intros Hj. destruct uname_lex as [_ Hall].
    exact (Forall_lookup_1 _ _ _ _ Hall Hj).
  Qed.

  Lemma uname_noslash : noslash nm.
  Proof using Hu.
    destruct uname_lex as [_ Hall]. unfold noslash.
    eapply Forall_impl; [exact Hall | exact fn_byte_not_slash].
  Qed.

  Lemma uname_path_shape : arg_path_shape nm.
  Proof using Hu.
    split.
    - pose proof uname_len as Hl. unfold DIRSIZ in Hl.
      assert (E : (2 ^ 31 = 2147483648)%Z) by reflexivity. lia.
    - intros j b Hj. exact (fn_byte_not_nul b (uname_byte j b Hj)).
  Qed.

  Lemma uname_skipelem : skipelem nm = Some (nm, []).
  Proof using Hu.
    destruct uname_lex as [Hne _].
    apply (skipelem_name nm Hne uname_noslash).
    pose proof uname_len as Hl. unfold DIRSIZ in Hl. lia.
  Qed.

  Lemma uname_path_elems : path_elems nm = [nm].
  Proof using Hu. exact (skipelem_is_last nm nm [] uname_skipelem eq_refl). Qed.

  Lemma uname_np_elems : np_elems nm = [].
  Proof using Hu. unfold np_elems. rewrite uname_path_elems. reflexivity. Qed.

  Lemma uname_last : list_basics.last (path_elems nm) = Some nm.
  Proof using Hu. rewrite uname_path_elems. reflexivity. Qed.

  Lemma uname_start (cw : Z) : um_start_of cw nm = cw.
  Proof using Hu.
    unfold um_start_of. case_decide as Hs; [| reflexivity].
    exfalso. exact (fn_byte_not_slash SLASH (uname_byte 0 SLASH Hs) eq_refl).
  Qed.

End UName.

(* ===================================================================== *)
(*  S4  THE LINE [cat N] AS AN ARGV: its two words exec at any class name *)
(*  (the name a word of name bytes by L1, short by L2)                    *)
(* ===================================================================== *)
Lemma cat_words_exec_ok (nm : list (bv 8)) :
  FileDisc.uname nm -> ExecWords.exec_ok [FileDisc.fd_w_cat; nm].
Proof using.
  intros Hu. pose proof (uname_len nm Hu) as Hl.
  unfold DIRSIZ in Hl. unfold ExecWords.exec_ok. split_and!.
  - constructor; [apply (bool_decide_unpack _); vm_compute; exact I |].
    constructor; [exact (uname_lex nm Hu) | constructor].
  - cbn [length]. lia.
  - cbn [length]. lia.
  - unfold wl_line, wl_body. cbn [wl_tail]. rewrite app_nil_r.
    rewrite !length_app. cbn [length].
    change (length FileDisc.fd_w_cat) with 3%nat. unfold line_max. lia.
Qed.

(* ...and its first word is /cat's path, whatever the name *)
Lemma cat_words_head (nm : list (bv 8)) :
  [FileDisc.fd_w_cat; nm] !!! 0%nat = FsImgCheck.fname_cat.
Proof using. by vm_compute. Qed.

(* cat's diagnostic at a class name is short (L2) *)
Lemma catopen_short (nm : list (bv 8)) :
  FileDisc.uname nm -> (Z.of_nat (length (FileDisc.dg_catopenN nm)) < 2 ^ 31)%Z.
Proof using.
  intros Hu. pose proof (uname_len nm Hu) as Hl. unfold DIRSIZ in Hl.
  unfold FileDisc.dg_catopenN. rewrite !length_app.
  match goal with |- context [length (sb ?x)] =>
    let v := eval vm_compute in (length (sb x)) in change (length (sb x)) with v end.
  change (length nlb) with 1%nat.
  assert (E : (2 ^ 31 = 2147483648)%Z) by reflexivity. lia.
Qed.

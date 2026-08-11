(* PathElems.v -- the PATH GRAMMAR: skipelem's decomposition of a path into
   elements, as a pure function on byte lists.

   The [PrintkFmt.v] precedent: a pure model of what a loop CONSUMES is what
   makes the loop's contract statable.  namex has no [skipelem] symbol -- gcc
   inlined it -- so this file models the inlined loop directly, and every
   clause below is read off namex's instruction stream rather than off fs.c:

     namex+0xe4  lbu a5,0(s1) ; bne a5,s3,0xf6 ; addi s1,s1,1 ;
                 lbu a5,0(s1) ; beq a5,s3,0xec           (s3 = 47 = '/')
                                       ==>  while( *path == '/' ) path++
     namex+0xf6  beqz a5,0x130         ==>  if( *path == 0 ) return 0  [None]
     namex+0x104 mv s2,s1 ; addi s2,s2,1 ; lbu a5,0(s2) ;
                 addi a4,a5,-47 ; beqz a4,0x8c ; bnez a5,0x106
                                       ==>  s = path;
                                            while( *s != '/' && *s != 0 ) s++
     namex+0x8c  sub a2,s2,s1 ; sext.w s10,a2 ; bge s8,s10,0x11c   (s8 = 13)
                                       ==>  len = s - path; len <= 13 ?
     namex+0x98  mv a2,s9 (=14) ; mv a1,s1 ; mv a0,s5 ; jal MEMMOVE
                                       ==>  len >= DIRSIZ: copy 14 bytes and
                                            write NO terminator
     namex+0x11c sext.w a2,a2 ; mv a1,s1 ; mv a0,s5 ; jal MEMMOVE ;
                 add s10,s10,s5 ; sb zero,0(s10)
                                       ==>  len < DIRSIZ: copy len bytes and
                                            name[len] = 0
     namex+0xa2  mv s1,s2   /  +0x12c  mv s1,s2
                                       ==>  path = s -- THE REST IS TAKEN
                                            AFTER THE FULL ELEMENT, never
                                            after the 14-byte truncation
     namex+0xa4  lbu a5,0(s1) ; bne a5,s3,0xb6 ; addi s1,s1,1 ; ...
                                       ==>  skipelem's TRAILING while( *path
                                            == '/') path++ -- so the returned
                                            rest has NO leading slash, which
                                            is exactly what namex+0xc8's
                                            [nameiparent && *path == 0] test
                                            then reads

   A path is modelled as the list of its CONTENT bytes -- the C string's NUL
   terminator is the end of the list, so "*path == 0" is "the list is empty".
   (Nothing in the model mentions NUL; the bridge to the buffer that HOLDS the
   path is the caller's, and [Forall (<> NUL)] on the list is the hypothesis
   that transports to the element -- see [skipelem_nonul].)

   THE TRUNCATION IS FAITHFUL: [skipelem] returns [take 14] of the element it
   scanned, while the rest resumes after the WHOLE element.  A 20-byte path
   component therefore yields a 14-byte name AND consumes 20 bytes, which is
   the (silently lossy) behaviour of xv6 that a directory lookup then sees.

   [skipelem] is total and structurally simple, but [path_elems] recurses on
   the REST, which is smaller only by a measure -- so it is defined with FUEL
   and the fuel is then shown irrelevant ([path_elems_unfold] is the law every
   consumer uses; the fuel never appears in a statement again).

   iris-FREE and ssreflect-free, like [DirentEnc.v], whose NUL/name vocabulary
   it reuses (a path element IS a canonical name: [skipelem_name_view] hands
   namex's memmove'd buffer straight to [DirentEnc.bname]).                *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import DirentEnc.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* The separator, and the three scanners the inlined loop performs.         *)
(* ---------------------------------------------------------------------- *)

(* namex+0x3c: [li s3,47] *)
Definition SLASH : bv 8 := (mword_of_int 47 : mword 8).

Definition noslash (l : list (bv 8)) : Prop := Forall (fun b => b <> SLASH) l.

(* while( *path == '/' ) path++ *)
Fixpoint pe_skip (p : list (bv 8)) : list (bv 8) :=
  match p with
  | [] => []
  | b :: p' => if bool_decide (b = SLASH) then pe_skip p' else b :: p'
  end.

(* the element: bytes up to the next '/' (or the end of the string) *)
Fixpoint pe_elem (p : list (bv 8)) : list (bv 8) :=
  match p with
  | [] => []
  | b :: p' => if bool_decide (b = SLASH) then [] else b :: pe_elem p'
  end.

(* ...and what is left, starting AT that '/' *)
Fixpoint pe_rest (p : list (bv 8)) : list (bv 8) :=
  match p with
  | [] => []
  | b :: p' => if bool_decide (b = SLASH) then b :: p' else pe_rest p'
  end.

(* a path with no leading separator -- the shape [pe_skip] produces and the
   shape namex's [*path == 0] test is applied to *)
Definition pe_norm (p : list (bv 8)) : Prop := pe_skip p = p.

(* THE MODEL: element (truncated at DIRSIZ) and rest (NOT truncated, and with
   the trailing separators already skipped). *)
Definition skipelem (p : list (bv 8)) : option (list (bv 8) * list (bv 8)) :=
  match pe_skip p with
  | [] => None
  | _ :: _ => Some (take 14 (pe_elem (pe_skip p)), pe_skip (pe_rest (pe_skip p)))
  end.

(* ---------------------------------------------------------------------- *)
(* The scanners' laws.                                                     *)
(* ---------------------------------------------------------------------- *)

Lemma pe_skip_slash (p : list (bv 8)) : pe_skip (SLASH :: p) = pe_skip p.
Proof. simpl. rewrite bool_decide_true by reflexivity. reflexivity. Qed.

Lemma pe_skip_ne (b : bv 8) (p : list (bv 8)) :
  b <> SLASH -> pe_skip (b :: p) = b :: p.
Proof. intros Hb. simpl. rewrite bool_decide_false by exact Hb. reflexivity. Qed.

Lemma pe_skip_length (p : list (bv 8)) : (length (pe_skip p) <= length p)%nat.
Proof.
  induction p as [|b p IH]; [reflexivity|]. simpl.
  destruct (bool_decide (b = SLASH)); simpl; lia.
Qed.

Lemma pe_skip_head (p : list (bv 8)) (b : bv 8) (q : list (bv 8)) :
  pe_skip p = b :: q -> b <> SLASH.
Proof.
  revert b q. induction p as [|c p IH]; intros b q H; [discriminate|].
  simpl in H. destruct (bool_decide (c = SLASH)) eqn:Hc.
  - exact (IH b q H).
  - apply bool_decide_eq_false in Hc. injection H. intros _ He.
    rewrite <- He. exact Hc.
Qed.

Lemma pe_skip_idem (p : list (bv 8)) : pe_skip (pe_skip p) = pe_skip p.
Proof.
  destruct (pe_skip p) as [|b q] eqn:E; [reflexivity|].
  apply pe_skip_ne. exact (pe_skip_head p b q E).
Qed.

Lemma pe_skip_norm (p : list (bv 8)) : pe_norm (pe_skip p).
Proof. unfold pe_norm. apply pe_skip_idem. Qed.

Lemma pe_norm_nil (p : list (bv 8)) : pe_norm p -> pe_skip p = [] -> p = [].
Proof. unfold pe_norm. intros Hn Hs. rewrite <- Hn. exact Hs. Qed.

(* the element and the rest partition the path *)
Lemma pe_elem_rest (p : list (bv 8)) : pe_elem p ++ pe_rest p = p.
Proof.
  induction p as [|b p IH]; [reflexivity|]. simpl.
  destruct (bool_decide (b = SLASH)); [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma pe_elem_rest_length (p : list (bv 8)) :
  (length (pe_elem p) + length (pe_rest p))%nat = length p.
Proof. rewrite <- (pe_elem_rest p) at 3. rewrite length_app. reflexivity. Qed.

Lemma pe_elem_noslash (p : list (bv 8)) : noslash (pe_elem p).
Proof.
  unfold noslash. induction p as [|b p IH]; [constructor|]. simpl.
  destruct (bool_decide (b = SLASH)) eqn:Hb; [constructor|].
  apply bool_decide_eq_false in Hb. constructor; [exact Hb | exact IH].
Qed.

Lemma pe_elem_ne (b : bv 8) (p : list (bv 8)) :
  b <> SLASH -> pe_elem (b :: p) = b :: pe_elem p.
Proof. intros Hb. simpl. rewrite bool_decide_false by exact Hb. reflexivity. Qed.

Lemma pe_rest_ne (b : bv 8) (p : list (bv 8)) :
  b <> SLASH -> pe_rest (b :: p) = pe_rest p.
Proof. intros Hb. simpl. rewrite bool_decide_false by exact Hb. reflexivity. Qed.

(* a sub-list property (in practice "contains no NUL") passes to both *)
Lemma pe_elem_Forall (P : bv 8 -> Prop) (p : list (bv 8)) :
  Forall P p -> Forall P (pe_elem p).
Proof.
  induction 1 as [|b p Hb Hp IH]; [constructor|]. simpl.
  destruct (bool_decide (b = SLASH)); [constructor|].
  constructor; [exact Hb | exact IH].
Qed.

Lemma pe_rest_Forall (P : bv 8 -> Prop) (p : list (bv 8)) :
  Forall P p -> Forall P (pe_rest p).
Proof.
  induction 1 as [|b p Hb Hp IH]; [constructor|]. simpl.
  destruct (bool_decide (b = SLASH)); [constructor; assumption | exact IH].
Qed.

Lemma pe_skip_Forall (P : bv 8 -> Prop) (p : list (bv 8)) :
  Forall P p -> Forall P (pe_skip p).
Proof.
  induction 1 as [|b p Hb Hp IH]; [constructor|]. simpl.
  destruct (bool_decide (b = SLASH)); [exact IH | constructor; assumption].
Qed.

(* scanning past a separator-free prefix *)
Lemma pe_skip_app_ns (u v : list (bv 8)) :
  noslash u -> u <> [] -> pe_skip (u ++ v) = u ++ v.
Proof.
  unfold noslash. intros Hu Hne. destruct u as [|b u]; [exfalso; apply Hne; reflexivity|].
  inversion Hu as [|xb xu Hb Hus]; subst.
  rewrite <- app_comm_cons. apply pe_skip_ne. exact Hb.
Qed.

Lemma pe_elem_app_ns (u v : list (bv 8)) :
  noslash u -> pe_elem (u ++ v) = u ++ pe_elem v.
Proof.
  unfold noslash. induction 1 as [|b u Hb Hu IH]; [reflexivity|].
  rewrite <- app_comm_cons, pe_elem_ne by exact Hb. rewrite IH. reflexivity.
Qed.

Lemma pe_rest_app_ns (u v : list (bv 8)) :
  noslash u -> pe_rest (u ++ v) = pe_rest v.
Proof.
  unfold noslash. induction 1 as [|b u Hb Hu IH]; [reflexivity|].
  rewrite <- app_comm_cons, pe_rest_ne by exact Hb. exact IH.
Qed.

(* ...and a tail that is empty or starts at a separator is its own rest *)
Definition pe_at_sep (v : list (bv 8)) : Prop :=
  v = [] \/ exists v', v = SLASH :: v'.

Lemma pe_elem_at_sep (v : list (bv 8)) : pe_at_sep v -> pe_elem v = [].
Proof.
  intros [->|[v' ->]]; [reflexivity|].
  simpl. rewrite bool_decide_true by reflexivity. reflexivity.
Qed.

Lemma pe_rest_at_sep (v : list (bv 8)) : pe_at_sep v -> pe_rest v = v.
Proof.
  intros [->|[v' ->]]; [reflexivity|].
  simpl. rewrite bool_decide_true by reflexivity. reflexivity.
Qed.

Lemma pe_rest_at_sep_gen (p : list (bv 8)) : pe_at_sep (pe_rest p).
Proof.
  unfold pe_at_sep. induction p as [|b p IH]; [left; reflexivity|]. simpl.
  destruct (bool_decide (b = SLASH)) eqn:Hb; [| exact IH].
  apply bool_decide_eq_true in Hb. right. exists p. rewrite Hb. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* skipelem: the two unfoldings, and the master split law.                 *)
(* ---------------------------------------------------------------------- *)

Lemma skipelem_none (p : list (bv 8)) : pe_skip p = [] -> skipelem p = None.
Proof. intros H. unfold skipelem. rewrite H. reflexivity. Qed.

Lemma skipelem_some (p : list (bv 8)) :
  pe_skip p <> [] ->
  skipelem p = Some (take 14 (pe_elem (pe_skip p)), pe_skip (pe_rest (pe_skip p))).
Proof.
  intros Hne. unfold skipelem.
  destruct (pe_skip p) as [|b q] eqn:E; [exfalso; apply Hne; reflexivity|].
  reflexivity.
Qed.

Lemma skipelem_nil : skipelem [] = None.
Proof. apply skipelem_none. reflexivity. Qed.

Lemma skipelem_slash (p : list (bv 8)) : skipelem (SLASH :: p) = skipelem p.
Proof. unfold skipelem. rewrite pe_skip_slash. reflexivity. Qed.

Lemma skipelem_None_iff (p : list (bv 8)) : skipelem p = None <-> pe_skip p = [].
Proof.
  split.
  - intros H. destruct (pe_skip p) as [|b q] eqn:E; [reflexivity|].
    rewrite (skipelem_some p ltac:(rewrite E; discriminate)) in H. discriminate.
  - apply skipelem_none.
Qed.

(* THE SPLIT LAW.  Everything below is an instance of it: given the path's
   decomposition into a separator-free element [u] and a tail [v] that is
   empty or starts at a separator, skipelem truncates the ELEMENT at 14 and
   returns the tail with its separators skipped -- the rest is measured from
   the end of the FULL element. *)
Lemma skipelem_split (u v : list (bv 8)) :
  noslash u -> u <> [] -> pe_at_sep v ->
  skipelem (u ++ v) = Some (take 14 u, pe_skip v).
Proof.
  intros Hu Hne Hv.
  assert (Hs : pe_skip (u ++ v) = u ++ v) by (apply pe_skip_app_ns; assumption).
  rewrite (skipelem_some (u ++ v) ltac:(rewrite Hs; intros Hc;
             apply Hne; destruct u; [reflexivity | discriminate])).
  rewrite Hs, (pe_elem_app_ns u v Hu), (pe_rest_app_ns u v Hu).
  rewrite (pe_elem_at_sep v Hv), (pe_rest_at_sep v Hv), app_nil_r.
  reflexivity.
Qed.

(* the three components of a successful step, without unfolding anything *)
Lemma skipelem_inv (p e r : list (bv 8)) :
  skipelem p = Some (e, r) ->
  pe_skip p <> [] /\ e = take 14 (pe_elem (pe_skip p))
  /\ r = pe_skip (pe_rest (pe_skip p)).
Proof.
  intros H.
  destruct (pe_skip p) as [|b q] eqn:E.
  { rewrite (skipelem_none p E) in H. discriminate. }
  rewrite (skipelem_some p ltac:(rewrite E; discriminate)) in H.
  injection H as He Hr.
  split; [discriminate |]. split; congruence.
Qed.

(* the element is nonempty, at most DIRSIZ long, and separator free *)
Lemma skipelem_elem_wf (p e r : list (bv 8)) :
  skipelem p = Some (e, r) ->
  e <> [] /\ (length e <= 14)%nat /\ noslash e.
Proof.
  intros H. apply skipelem_inv in H as [Hne [He Hr]].
  destruct (pe_skip p) as [|b q] eqn:E; [exfalso; apply Hne; reflexivity |].
  rewrite (pe_elem_ne b q (pe_skip_head p b q E)) in He.
  split; [| split].
  - rewrite He. simpl. discriminate.
  - rewrite He, length_take. lia.
  - rewrite He. unfold noslash. apply Forall_take.
    constructor; [exact (pe_skip_head p b q E) | apply pe_elem_noslash].
Qed.

(* a NUL-free path yields a NUL-free element: the hypothesis that carries the
   C-string model through to [DirentEnc]'s name vocabulary *)
Lemma skipelem_nonul (p e r : list (bv 8)) :
  Forall (fun b => b <> NUL) p -> skipelem p = Some (e, r) ->
  nonul e /\ Forall (fun b => b <> NUL) r.
Proof.
  intros Hp H. apply skipelem_inv in H as [_ [He Hr]].
  pose proof (pe_skip_Forall _ p Hp) as Hq.
  split.
  - rewrite He. unfold nonul. apply Forall_take, pe_elem_Forall, Hq.
  - rewrite Hr. apply pe_skip_Forall, pe_rest_Forall, Hq.
Qed.

(* the rest carries no leading separator -- what namex's [*path == 0] test
   after the TRAILING slash skip depends on *)
Lemma skipelem_rest_norm (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> pe_norm r.
Proof.
  intros H. apply skipelem_inv in H as [_ [_ Hr]].
  rewrite Hr. apply pe_skip_norm.
Qed.

(* THE MEASURE the loop induction needs *)
Lemma skipelem_decr (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> (length r < length p)%nat.
Proof.
  intros H. apply skipelem_inv in H as [Hne [He Hr]].
  destruct (pe_skip p) as [|b q] eqn:E; [exfalso; apply Hne; reflexivity |].
  pose proof (pe_skip_length p) as Hlq. rewrite E in Hlq.
  pose proof (pe_elem_rest_length (b :: q)) as Hsplit.
  rewrite (pe_elem_ne b q (pe_skip_head p b q E)) in Hsplit.
  pose proof (pe_skip_length (pe_rest (b :: q))) as Hlr.
  rewrite !length_cons in Hsplit. rewrite length_cons in Hlq.
  rewrite Hr. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The element LIST of a path.                                             *)
(* ---------------------------------------------------------------------- *)

Fixpoint path_elems_fuel (n : nat) (p : list (bv 8)) : list (list (bv 8)) :=
  match n with
  | 0%nat => []
  | S n' => match skipelem p with
            | None => []
            | Some (e, r) => e :: path_elems_fuel n' r
            end
  end.

Definition path_elems (p : list (bv 8)) : list (list (bv 8)) :=
  path_elems_fuel (length p) p.

Lemma path_elems_fuel_indep (n : nat) :
  forall (m : nat) (p : list (bv 8)),
    (length p <= n)%nat -> (length p <= m)%nat ->
    path_elems_fuel n p = path_elems_fuel m p.
Proof.
  induction n as [|n IH]; intros m p Hn Hm.
  - assert (Hp : p = []) by (apply nil_length_inv; lia). subst p.
    destruct m as [|m]; [reflexivity|].
    cbn [path_elems_fuel]. rewrite skipelem_nil. reflexivity.
  - destruct m as [|m].
    { assert (Hp : p = []) by (apply nil_length_inv; lia). subst p.
      cbn [path_elems_fuel]. rewrite skipelem_nil. reflexivity. }
    cbn [path_elems_fuel].
    destruct (skipelem p) as [[e r]|] eqn:Hs; [|reflexivity].
    pose proof (skipelem_decr p e r Hs) as Hd.
    rewrite (IH m r ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(* THE law every consumer uses; the fuel never appears again. *)
Lemma path_elems_unfold (p : list (bv 8)) :
  path_elems p =
  match skipelem p with
  | None => []
  | Some (e, r) => e :: path_elems r
  end.
Proof.
  unfold path_elems at 1.
  destruct (length p) as [|k] eqn:Hlp.
  - assert (Hp : p = []) by (apply nil_length_inv; lia). subst p.
    rewrite skipelem_nil. reflexivity.
  - cbn [path_elems_fuel].
    destruct (skipelem p) as [[e r]|] eqn:Hs; [|reflexivity].
    pose proof (skipelem_decr p e r Hs) as Hd. rewrite Hlp in Hd.
    unfold path_elems. rewrite (path_elems_fuel_indep k (length r) r);
      [reflexivity | lia | lia].
Qed.

Lemma path_elems_None (p : list (bv 8)) :
  skipelem p = None -> path_elems p = [].
Proof. intros H. rewrite path_elems_unfold, H. reflexivity. Qed.

Lemma path_elems_Some (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> path_elems p = e :: path_elems r.
Proof. intros H. rewrite path_elems_unfold, H. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The corner cases, stated as facts.                                      *)
(* ---------------------------------------------------------------------- *)

(* the empty path has no elements *)
Lemma path_elems_nil : path_elems [] = [].
Proof. apply path_elems_None, skipelem_nil. Qed.

(* "/" -- and "///..." -- have no elements either *)
Lemma path_elems_slashes (n : nat) : path_elems (replicate n SLASH) = [].
Proof.
  apply path_elems_None, skipelem_none.
  induction n as [|n IH]; [reflexivity|].
  rewrite replicate_S, pe_skip_slash. exact IH.
Qed.

Lemma path_elems_root : path_elems [SLASH] = [].
Proof. exact (path_elems_slashes 1). Qed.

(* leading separators are absorbed, one at a time (hence any number) *)
Lemma path_elems_slash (p : list (bv 8)) :
  path_elems (SLASH :: p) = path_elems p.
Proof.
  rewrite (path_elems_unfold (SLASH :: p)), skipelem_slash,
    <- path_elems_unfold. reflexivity.
Qed.

(* a path IS the elements of its normalisation *)
Lemma path_elems_skip (p : list (bv 8)) : path_elems (pe_skip p) = path_elems p.
Proof.
  rewrite (path_elems_unfold (pe_skip p)), (path_elems_unfold p).
  unfold skipelem. rewrite pe_skip_idem. reflexivity.
Qed.

Lemma path_elems_nil_iff (p : list (bv 8)) :
  path_elems p = [] <-> pe_skip p = [].
Proof.
  rewrite path_elems_unfold. split.
  - intros H. destruct (skipelem p) as [[e r]|] eqn:Hs.
    + discriminate.
    + apply skipelem_None_iff. exact Hs.
  - intros H. rewrite (skipelem_none p H). reflexivity.
Qed.

(* ...so for a NORMALISED path (which every rest is), "no elements left" is
   literally "the string is empty" -- the test namex+0xc8 performs *)
Lemma path_elems_nil_norm (p : list (bv 8)) :
  pe_norm p -> (path_elems p = [] <-> p = []).
Proof.
  intros Hn. rewrite path_elems_nil_iff. split.
  - intros H. apply pe_norm_nil; assumption.
  - intros ->. reflexivity.
Qed.

Lemma skipelem_rest_nil_iff (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> (r = [] <-> path_elems r = []).
Proof.
  intros H. rewrite (path_elems_nil_norm r (skipelem_rest_norm p e r H)).
  reflexivity.
Qed.

(* a trailing separator changes nothing *)
Lemma pe_skip_snoc_nil (x : list (bv 8)) :
  pe_skip x = [] -> pe_skip (x ++ [SLASH]) = [].
Proof.
  induction x as [|b x IH]; intros H; [reflexivity|]. simpl in H |- *.
  destruct (bool_decide (b = SLASH)); [exact (IH H) | discriminate].
Qed.

Lemma pe_skip_snoc_ne (x : list (bv 8)) :
  pe_skip x <> [] -> pe_skip (x ++ [SLASH]) = pe_skip x ++ [SLASH].
Proof.
  induction x as [|b x IH]; intros H; [exfalso; apply H; reflexivity|].
  simpl in H |- *.
  destruct (bool_decide (b = SLASH)); [exact (IH H) | reflexivity].
Qed.

Lemma pe_elem_snoc_slash (x : list (bv 8)) :
  pe_elem (x ++ [SLASH]) = pe_elem x.
Proof.
  induction x as [|b x IH].
  - simpl. rewrite bool_decide_true by reflexivity. reflexivity.
  - simpl. destruct (bool_decide (b = SLASH)); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma pe_rest_snoc_nil (x : list (bv 8)) :
  pe_rest x = [] -> pe_rest (x ++ [SLASH]) = [SLASH].
Proof.
  induction x as [|b x IH]; intros H.
  - simpl. rewrite bool_decide_true by reflexivity. reflexivity.
  - simpl in H |- *. destruct (bool_decide (b = SLASH)); [discriminate | exact (IH H)].
Qed.

Lemma pe_rest_snoc_ne (x : list (bv 8)) :
  pe_rest x <> [] -> pe_rest (x ++ [SLASH]) = pe_rest x ++ [SLASH].
Proof.
  induction x as [|b x IH]; intros H; [exfalso; apply H; reflexivity|].
  simpl in H |- *.
  destruct (bool_decide (b = SLASH)); [reflexivity | exact (IH H)].
Qed.

Lemma path_elems_snoc_slash_aux (n : nat) :
  forall p : list (bv 8), (length p <= n)%nat ->
    path_elems (p ++ [SLASH]) = path_elems p.
Proof.
  induction n as [|n IH]; intros p Hn.
  { assert (Hp : p = []) by (apply nil_length_inv; lia). subst p.
    rewrite app_nil_l, path_elems_root, path_elems_nil. reflexivity. }
  destruct (pe_skip p) as [|b q] eqn:E.
  { rewrite (path_elems_None p (skipelem_none p E)).
    apply path_elems_None, skipelem_none, pe_skip_snoc_nil, E. }
  assert (Hne : pe_skip p <> []) by (rewrite E; discriminate).
  rewrite (path_elems_Some p _ _ (skipelem_some p Hne)).
  assert (Hne' : pe_skip (p ++ [SLASH]) <> [])
    by (rewrite (pe_skip_snoc_ne p Hne), E; discriminate).
  rewrite (path_elems_Some _ _ _ (skipelem_some _ Hne')).
  rewrite (pe_skip_snoc_ne p Hne), pe_elem_snoc_slash. f_equal.
  (* the two rests differ by at most the trailing separator *)
  destruct (decide (pe_rest (pe_skip p) = [])) as [Hr|Hr].
  - rewrite (pe_rest_snoc_nil (pe_skip p) Hr), Hr, pe_skip_slash. reflexivity.
  - rewrite (pe_rest_snoc_ne (pe_skip p) Hr).
    destruct (decide (pe_skip (pe_rest (pe_skip p)) = [])) as [Hs|Hs].
    + rewrite Hs, (pe_skip_snoc_nil _ Hs). reflexivity.
    + rewrite (pe_skip_snoc_ne _ Hs).
      pose proof (skipelem_decr p _ _ (skipelem_some p Hne)) as Hd.
      apply IH. lia.
Qed.

Lemma path_elems_snoc_slash (p : list (bv 8)) :
  path_elems (p ++ [SLASH]) = path_elems p.
Proof. apply (path_elems_snoc_slash_aux (length p)). lia. Qed.

(* AN ELEMENT AT MOST 14 LONG IS COPIED WHOLE; a longer one is TRUNCATED and
   the rest still resumes after all of it. *)
Lemma skipelem_short (u v : list (bv 8)) :
  noslash u -> u <> [] -> (length u <= 14)%nat -> pe_at_sep v ->
  skipelem (u ++ v) = Some (u, pe_skip v).
Proof.
  intros Hu Hne Hlen Hv.
  rewrite (skipelem_split u v Hu Hne Hv), take_ge by exact Hlen. reflexivity.
Qed.

Lemma skipelem_exact14 (u v : list (bv 8)) :
  noslash u -> length u = 14%nat -> pe_at_sep v ->
  skipelem (u ++ v) = Some (u, pe_skip v).
Proof.
  intros Hu Hlen Hv. apply skipelem_short; [exact Hu | | lia | exact Hv].
  intros Hc. rewrite Hc in Hlen. discriminate.
Qed.

Lemma skipelem_long (u v : list (bv 8)) :
  noslash u -> (14 <= length u)%nat -> pe_at_sep v ->
  skipelem (u ++ v) = Some (take 14 u, pe_skip v)
  /\ length (take 14 u) = 14%nat.
Proof.
  intros Hu Hlen Hv.
  assert (Hne : u <> []) by (intros Hc; rewrite Hc in Hlen; simpl in Hlen; lia).
  split.
  - apply skipelem_split; assumption.
  - rewrite length_take. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* namei vs nameiparent: all the elements, or all but the last plus it.    *)
(* ---------------------------------------------------------------------- *)

Lemma list_snoc_inv {A : Type} (l : list A) :
  l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  induction l as [|a l IH]; [left; reflexivity|].
  right. destruct IH as [Hl|[l' [x Hl]]].
  - exists [], a. rewrite Hl. reflexivity.
  - exists (a :: l'), x. rewrite Hl. reflexivity.
Qed.

(* nameiparent's split -- all the elements but the last, plus the last, which
   is the name namex leaves in the caller's buffer.  Stated as a RELATION
   rather than computed: the decomposition itself is all a proof needs, and it
   is unique ([nameiparent_uniq]). *)
Definition nameiparent_of (p : list (bv 8)) (es : list (list (bv 8)))
    (e : list (bv 8)) : Prop := path_elems p = es ++ [e].

Lemma nameiparent_exists (p : list (bv 8)) :
  path_elems p <> [] -> exists es e, nameiparent_of p es e.
Proof.
  intros H. unfold nameiparent_of.
  destruct (list_snoc_inv (path_elems p)) as [Hnil|[es [e He]]].
  - exfalso. apply H, Hnil.
  - exists es, e. exact He.
Qed.

Lemma nameiparent_uniq (p : list (bv 8)) (es1 es2 : list (list (bv 8)))
    (e1 e2 : list (bv 8)) :
  nameiparent_of p es1 e1 -> nameiparent_of p es2 e2 -> es1 = es2 /\ e1 = e2.
Proof.
  unfold nameiparent_of. intros H1 H2. rewrite H1 in H2.
  apply app_inj_tail in H2 as [Hes He]. split; [exact Hes | exact He].
Qed.

(* the loop's two exits, in the form the induction consumes: the last element
   is the one whose REST is empty *)
Lemma skipelem_is_last (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> r = [] -> path_elems p = [e].
Proof.
  intros H Hr. rewrite (path_elems_Some p e r H), Hr, path_elems_nil.
  reflexivity.
Qed.

Lemma skipelem_not_last (p e r : list (bv 8)) :
  skipelem p = Some (e, r) -> r <> [] ->
  path_elems p = e :: path_elems r /\ path_elems r <> [].
Proof.
  intros H Hr. split; [exact (path_elems_Some p e r H) |].
  intros Hc.
  apply Hr, (proj1 (path_elems_nil_norm r (skipelem_rest_norm p e r H))), Hc.
Qed.

(* ---------------------------------------------------------------------- *)
(* The bridge to the NAME buffer: what namex's memmove leaves behind.      *)
(* ---------------------------------------------------------------------- *)

(* skipelem's two branches -- [memmove(name, s, 14)] with no terminator, and
   [memmove(name, s, len); name[len] = 0] -- have the SAME canonical view, and
   it is the element.  This is what makes namecmp's contract ([DirentEnc.
   namecmp_bridge]) speak about the path element rather than about bytes. *)
Lemma skipelem_name_view (p e r : list (bv 8)) (f : nat -> bv 8) :
  Forall (fun b => b <> NUL) p ->
  skipelem p = Some (e, r) ->
  (forall j, (j < length e)%nat -> f j = e !!! j) ->
  ((length e < 14)%nat -> f (length e) = NUL) ->
  bname 14 f = e.
Proof.
  intros Hp Hs Hf Hstop.
  destruct (skipelem_elem_wf p e r Hs) as [_ [Hlen _]].
  destruct (skipelem_nonul p e r Hp Hs) as [Hne _].
  apply bname_of_buf; assumption.
Qed.

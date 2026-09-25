(* FileState.v -- THE FILE APPLICATION'S STATE VOCABULARY, pure and tiny.

   Design of record: claude-notes/design/app-file.md section 1.  This file
   is the four definitions BOTH the pure model ([FileDisc.v]) and the claim
   ([AppFile.v]) read, and nothing else -- it exists so that the claim does
   not import the session model's cone and the model does not import the
   claim's.

     [fstate]       the file's STATE: absent, or present with these bytes.
                    THE STATE IS THE CONTENT and not a (words, subset)
                    pair: the content is a function of the abstract view,
                    which is what lets the claim's transport allocate the
                    copy's ghost at the view's own value outside the later
                    (design section 2); the words and the subset live in
                    the alternative that produced it.
     [echo_chunks]  the byte runs echo's [write]s put on its fd 1, one per
                    call -- each argument, a single blank between, a
                    newline after the last ([user/echo.c]).
     [sel_ok]       a chunk subset: strictly increasing indices into the
                    chunk list.
     [subseq]       the concatenation of the selected chunks.  With every
                    chunk landed it is [wl_line (drop 1 ws)], the line
                    minus its command name -- exactly the echo
                    application's good alternative. *)
From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import Sorted.
From stdpp Require Import gmap list list_numbers sorting bitvector.definitions.
Require Import LineWords.       (* [wl_sp], [wl_nl], [wl_line], [wl_body] *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(* ====================================================================== *)
(*  1.  THE STATE                                                          *)
(* ====================================================================== *)

(* THE STATE IS A MAP from file names to contents (cut W1 of
   claude-notes/design/filenames.md): the files of the name class that
   exist, each with its bytes.  An absent name is an absent file.  Which
   names may appear is the model's [FileDisc.fstate_ok] (the class
   [FileDisc.uname]); this file fixes the representation only. *)
Definition fstate : Type := gmap (list (bv 8)) (list (bv 8)).

(* THE ONE NAME the claim's deed still speaks of (the byte [f]):
   [FileDisc.fname_f] is this constant, and [AppFile.dst_content] files
   the deed's content under it.  Kept here because the claim does not
   import the model's cone. *)
Definition fname_m : list (bv 8) := [Z_to_bv 8 102].

(* the one-name state an option content denotes: the bridge from the
   deed's [option] to the model's map *)
Definition fst_of (o : option (list (bv 8))) : fstate :=
  match o with None => ∅ | Some bs => {[fname_m := bs]} end.

Lemma fst_of_lookup (o : option (list (bv 8))) : fst_of o !! fname_m = o.
Proof using. destruct o as [bs |]; cbn [fst_of]; [apply lookup_singleton | apply lookup_empty]. Qed.

Lemma fst_of_lookup_ne (o : option (list (bv 8))) (N : list (bv 8)) :
  N <> fname_m -> fst_of o !! N = None.
Proof using.
  intros HN. destruct o as [bs |]; cbn [fst_of];
    [apply lookup_singleton_ne; congruence | apply lookup_empty].
Qed.

(* ====================================================================== *)
(*  2.  ECHO'S CHUNKS                                                      *)
(* ====================================================================== *)

(* [echo_args_chunks args] for the arguments AFTER the command name:
   a1, " ", a2, " ", ..., an, "\n".  At no arguments echo writes nothing
   (the loop does not run), which the discipline excludes (a line has at
   least two words) but the definition need not. *)
Fixpoint echo_args_chunks (args : list (list (bv 8))) : list (list (bv 8)) :=
  match args with
  | [] => []
  | [a] => [a; [wl_nl]]
  | a :: rest => a :: [wl_sp] :: echo_args_chunks rest
  end.

Definition echo_chunks (ws : list (list (bv 8))) : list (list (bv 8)) :=
  echo_args_chunks (drop 1 ws).

(* every chunk is non-empty when every argument is: that is what makes
   the decomposition of a content into chunks unique, which nothing here
   needs yet and a strengthening will *)
Lemma echo_args_chunks_nonnil (args : list (list (bv 8))) :
  Forall (fun a => a <> []) args ->
  Forall (fun c => c <> []) (echo_args_chunks args).
Proof.
  induction args as [| a rest IH]; intros Hf; [constructor |].
  apply Forall_cons_1 in Hf as [Ha Hrest].
  destruct rest as [| b rest'].
  - cbn. repeat constructor; [exact Ha | discriminate].
  - cbn [echo_args_chunks]. constructor; [exact Ha |].
    constructor; [discriminate | exact (IH Hrest)].
Qed.

(* ====================================================================== *)
(*  3.  SUBSETS AND THEIR CONCATENATION                                    *)
(* ====================================================================== *)

(* a subset of chunk indices: strictly increasing, all in range *)
Definition sel_ok (cs : list (list (bv 8))) (sel : list nat) : Prop :=
  StronglySorted lt sel /\ Forall (fun j => j < length cs) sel.

Global Instance sel_ok_dec cs sel : Decision (sel_ok cs sel).
Proof. rewrite /sel_ok. apply _. Defined.

Definition subseq (cs : list (list (bv 8))) (sel : list nat) : list (bv 8) :=
  concat ((fun j => cs !!! j) <$> sel).

Lemma subseq_nil cs : subseq cs [] = [].
Proof. reflexivity. Qed.

Lemma subseq_snoc cs sel j : subseq cs (sel ++ [j]) = subseq cs sel ++ cs !!! j.
Proof. rewrite /subseq fmap_app concat_app. cbn. by rewrite app_nil_r. Qed.

Lemma sel_ok_nil cs : sel_ok cs [].
Proof. split; constructor. Qed.

Lemma StronglySorted_lt_snoc (sel : list nat) (j : nat) :
  StronglySorted lt sel -> Forall (fun i => i < j) sel ->
  StronglySorted lt (sel ++ [j]).
Proof.
  induction sel as [| a sel IH]; intros Hs Hlt; cbn.
  { repeat constructor. }
  apply StronglySorted_inv in Hs as [Hs Ha].
  apply Forall_cons_1 in Hlt as [Haj Hlt].
  constructor; [exact (IH Hs Hlt) |].
  apply Forall_app. split; [exact Ha | by repeat constructor].
Qed.

Lemma sel_ok_snoc cs sel j :
  sel_ok cs sel -> j < length cs -> Forall (fun i => i < j) sel ->
  sel_ok cs (sel ++ [j]).
Proof.
  intros [Hs Hr] Hj Hlt. split; [exact (StronglySorted_lt_snoc sel j Hs Hlt) |].
  apply Forall_app. split; [exact Hr | by repeat constructor].
Qed.

(* the full selection: every chunk, in order *)
Definition sel_all (cs : list (list (bv 8))) : list nat := seq 0 (length cs).

Lemma StronglySorted_lt_seq (n m : nat) : StronglySorted lt (seq n m).
Proof.
  revert n. induction m as [| m IH]; intros n; cbn; constructor; [apply IH |].
  apply Forall_forall. intros j Hj. apply elem_of_seq in Hj. lia.
Qed.

Lemma sel_all_ok cs : sel_ok cs (sel_all cs).
Proof.
  rewrite /sel_ok /sel_all. split; [apply StronglySorted_lt_seq |].
  apply Forall_forall. intros j Hj. apply elem_of_seq in Hj. lia.
Qed.

Lemma fmap_lookup_total_seq (cs : list (list (bv 8))) :
  (fun j => cs !!! j) <$> seq 0 (length cs) = cs.
Proof.
  apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < length cs)) as [Hi | Hi].
  - rewrite lookup_seq_lt; [| exact Hi]. cbn.
    destruct (lookup_lt_is_Some_2 cs i Hi) as [x Hx].
    by rewrite list_lookup_total_alt Hx.
  - rewrite lookup_seq_ge; [| lia]. by rewrite lookup_ge_None_2; [| lia].
Qed.

Lemma subseq_all cs : subseq cs (sel_all cs) = concat cs.
Proof. by rewrite /subseq /sel_all fmap_lookup_total_seq. Qed.

(* every chunk landed IS the echo application's good alternative: the line
   minus its command name *)
(* ====================================================================== *)
(*  2b.  WHICH CHUNK IS WHICH (lane KERNEL-STREAM, item 4)                 *)
(*                                                                        *)
(*  echo's payment recursion walks ARGUMENTS; the deed's cursor walks      *)
(*  CHUNKS.  These four lemmas are the dictionary: argument [q] of the     *)
(*  tail is chunk [2q], the separator or newline after it is chunk         *)
(*  [2q + 1], and there are exactly [2 * |args|] of them.                  *)
(* ====================================================================== *)

Lemma echo_args_chunks_length (args : list (list (bv 8))) :
  args <> [] -> length (echo_args_chunks args) = (2 * length args)%nat.
Proof.
  induction args as [| a args IH]; [ done | ]. intros _.
  destruct args as [| a' args']; [ reflexivity | ].
  cbn [echo_args_chunks length]. cbn [length] in IH.
  rewrite (IH ltac:(discriminate)). cbn [length]. lia.
Qed.

Lemma echo_args_chunks_word (args : list (list (bv 8))) (q : nat) :
  (q < length args)%nat ->
  echo_args_chunks args !! (2 * q)%nat = args !! q.
Proof.
  revert q. induction args as [| a args IH]; intros q Hq;
    [ cbn in Hq; lia | ].
  destruct q as [| q'].
  - destruct args as [| a' args']; reflexivity.
  - destruct args as [| a' args']; [ cbn in Hq; lia | ].
    replace (2 * S q')%nat with (S (S (2 * q'))) by lia.
    cbn [echo_args_chunks lookup list_lookup].
    cbn [length] in Hq. apply IH. cbn [length]. lia.
Qed.

Lemma echo_args_chunks_sep (args : list (list (bv 8))) (q : nat) :
  (S q < length args)%nat ->
  echo_args_chunks args !! (2 * q + 1)%nat = Some [wl_sp].
Proof.
  revert q. induction args as [| a args IH]; intros q Hq;
    [ cbn in Hq; lia | ].
  destruct q as [| q'].
  - destruct args as [| a' args']; [ cbn in Hq; lia | reflexivity ].
  - destruct args as [| a' args']; [ cbn in Hq; lia | ].
    replace (2 * S q' + 1)%nat with (S (S (2 * q' + 1))) by lia.
    cbn [echo_args_chunks lookup list_lookup].
    cbn [length] in Hq. apply IH. cbn [length]. lia.
Qed.

Lemma echo_args_chunks_nl (args : list (list (bv 8))) (q : nat) :
  S q = length args ->
  echo_args_chunks args !! (2 * q + 1)%nat = Some [wl_nl].
Proof.
  revert q. induction args as [| a args IH]; intros q Hq;
    [ cbn in Hq; lia | ].
  destruct q as [| q'].
  - destruct args as [| a' args']; [ reflexivity | cbn in Hq; lia ].
  - destruct args as [| a' args']; [ cbn in Hq; lia | ].
    replace (2 * S q' + 1)%nat with (S (S (2 * q' + 1))) by lia.
    cbn [echo_args_chunks lookup list_lookup].
    cbn [length] in Hq. apply IH. cbn [length]. lia.
Qed.

Lemma echo_args_chunks_concat (args : list (list (bv 8))) :
  args <> [] -> concat (echo_args_chunks args) = wl_line args.
Proof.
  induction args as [| a rest IH]; intros Hne; [done |].
  destruct rest as [| b rest'].
  - cbn. rewrite app_nil_r. by rewrite /wl_line /wl_body /=.
  - cbn [echo_args_chunks concat]. rewrite IH; [| discriminate].
    rewrite /wl_line /wl_body wl_tail_cons /wl_body. by simplify_list_eq.
Qed.

Lemma subseq_all_line (ws : list (list (bv 8))) :
  drop 1 ws <> [] ->
  subseq (echo_chunks ws) (sel_all (echo_chunks ws)) = wl_line (drop 1 ws).
Proof. intros H. rewrite subseq_all. exact (echo_args_chunks_concat (drop 1 ws) H). Qed.

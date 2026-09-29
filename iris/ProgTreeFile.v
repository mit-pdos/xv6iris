(* ===================================================================== *)
(* ProgTreeFile.v -- echo conforms at a FILE: the line's chunks, each     *)
(* landing or not (the file application records a file as the chunks of  *)
(* a line that landed, [FileState.echo_chunks]).  Its own file so that    *)
(* [ProgTree] stays below the application's pure model.                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import FileState ProgTree.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ---- echo at a file: the chunks, each landing or not ------------------ *)

Lemma echo_word_conforms_m (w : bytes) (rest_c : list bytes) files (rest : proc) :
  w <> [] ->
  conforms (pipe_env (DOutM rest_c) files) rest ->
  conforms (pipe_env (DOutM (w :: rest_c)) files) (Vis (EWrite 1 w) (fun _ => rest)).
Proof.
  intros Hne Hrest.
  eapply cf_write_m with (d := 0%nat) (rest := rest_c); [exact Hne | fdlk | done | |];
    rewrite pipe_env_set; exact Hrest.
Qed.

Lemma echo_words_conforms_m (ws : list bytes) files (rest : proc) :
  ws <> [] -> Forall (fun w => w <> []) ws ->
  conforms (pipe_env (DOutM []) files) rest ->
  conforms (pipe_env (DOutM (FileState.echo_args_chunks ws)) files) (echo_words ws rest).
Proof.
  revert rest. induction ws as [| w r IH]; intros rest Hne Hnn Hrest; [done |].
  apply Forall_cons_1 in Hnn as [Hw Hr].
  destruct r as [| w' r'].
  - simpl. apply echo_word_conforms_m; [exact Hw |].
    apply echo_word_conforms_m; [discriminate | exact Hrest].
  - simpl. apply echo_word_conforms_m; [exact Hw |].
    apply echo_word_conforms_m; [discriminate |].
    apply IH; [done | exact Hr | exact Hrest].
Qed.

Theorem echo_file_conforms (argv : list bytes) files :
  drop 1 argv <> [] -> Forall (fun w => w <> []) (drop 1 argv) ->
  conforms (pipe_env (DOutM (FileState.echo_chunks argv)) files) (echo_tree argv).
Proof.
  intros Hne Hnn. unfold echo_tree, FileState.echo_chunks.
  apply echo_words_conforms_m; [exact Hne | exact Hnn |].
  apply pipe_env_exit. reflexivity.
Qed.

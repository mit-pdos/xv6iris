(* ===================================================================== *)
(*  ExecWords.v -- A WORD LIST SH CAN EXEC                                *)
(*                                                                       *)
(*  [EchoDisc.line_ok] is the ECHO application's input discipline: the    *)
(*  words are words, THE COMMAND IS /echo WITH AT LEAST ONE ARGUMENT,     *)
(*  there are fewer of them than sh's MAXARGS and the line fits           *)
(*  [getcmd]'s buffer.  Almost nothing that reads sh's EXEC node -- the   *)
(*  tokens, the argument vector the kernel copies, the room the push      *)
(*  needs -- uses the second conjunct: those are facts about THE NODE SH  *)
(*  BUILT, whatever program it names.  They were nevertheless all stated  *)
(*  at [line_ok], so a consumer at another command ([cat f]) inherited a  *)
(*  premise that is FALSE at its own line, and the pipe campaign twinned  *)
(*  the lemmas at its one-word [cat] rather than reuse them               *)
(*  (claude-notes/projects/app-file-findings/PROGRAM-STREAM.md, stretch   *)
(*  11, defect 1).                                                        *)
(*                                                                       *)
(*  [exec_ok] is [line_ok] WITHOUT the command: what every such lemma     *)
(*  actually spends.  The general lemmas are named [<lemma>_x]; the       *)
(*  [line_ok] statements stay, verbatim, as their corollaries through     *)
(*  [line_ok_exec_ok], so no consumer moves.                              *)
(*                                                                       *)
(*  A NEW LEAF FILE, per durable-notes: [EchoDisc] is under every         *)
(*  application, and nothing here needs to be.                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import base list bitvector.definitions.
From stdpp Require Import ssreflect.
Require Import LineWords.
Require Import EchoDisc.

(* the words are words of NAME bytes ([LineWords.fn_wf], cut W4): an
   argv may carry a file name of the class, `a.txt`, and the dot is
   neither a blank nor one of sh's metacharacters, so the lexer reads it
   exactly as it reads an alphanumeric word *)
Definition exec_ok (ws : list (list (bv 8))) : Prop :=
  fn_wf ws
  /\ (0 < length ws)%nat
  /\ (length ws < 10)%nat
  /\ (length (wl_line ws) < line_max)%nat.

Global Instance exec_ok_dec ws : Decision (exec_ok ws).
Proof. rewrite /exec_ok. apply _. Defined.

Lemma exec_ok_wf ws : exec_ok ws -> fn_wf ws.
Proof. by intros (H & _ & _ & _). Qed.

Lemma exec_ok_pos ws : exec_ok ws -> (0 < length ws)%nat.
Proof. by intros (_ & H & _ & _). Qed.

Lemma exec_ok_lt10 ws : exec_ok ws -> (length ws < 10)%nat.
Proof. by intros (_ & _ & H & _). Qed.

Lemma exec_ok_len ws : exec_ok ws -> (length (wl_line ws) < line_max)%nat.
Proof. by intros (_ & _ & _ & H). Qed.

(* [EchoDisc.line_ok_at]'s twin: a word read back through [!!] *)
Lemma exec_ok_at ws i :
  exec_ok ws -> (i < length ws)%nat -> ws !! i = Some (ws !!! i).
Proof.
  intros _ Hi. destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
  by rewrite Hw list_lookup_total_alt Hw.
Qed.

(* THE ECHO DISCIPLINE IS AN INSTANCE *)
Lemma line_ok_exec_ok ws : line_ok ws -> exec_ok ws.
Proof.
  intro Hok. split_and!;
    [ exact (wl_wf_fn ws (line_ok_wf ws Hok)) | exact (line_ok_pos ws Hok)
    | exact (line_ok_lt10 ws Hok) | exact (line_ok_len ws Hok) ].
Qed.

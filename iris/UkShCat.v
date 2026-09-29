(* ===================================================================== *)
(* UkShCat.v -- THE PIPE LINE'S RIGHT COMMAND, `cat`, AS A VALUE, and the *)
(* finding that made its word-list reading vacuous.                      *)
(*                                                                        *)
(* WHAT THIS FILE WAS, AND WHAT IT IS (lane user-once, C2).  It was       *)
(* [UkShEcho.v]'s twin: sh's EXEC arm at the one command the pipe line's  *)
(* right side spells, with the three things that differ from echo's --   *)
(* one token instead of a word list, no [EchoDisc.line_ok], and "cat" in  *)
(* the exec-failed diagnostic -- each re-walked.  All three are           *)
(* PARAMETERS of the one arm [UkShEcho.wp_kshr_exec_x_at] (the fd row     *)
(* [Fd1], the words [ws] read at the command's own base through          *)
(* [echo_argv_bytes], the diagnostic's alternative [dg]; its line premise *)
(* is [exec_ok], not [line_ok]), and the union's pipe stages apply THAT   *)
(* arm for cat at the shifted base ([UShPipesStage]: [s0 + co] and        *)
(* [fun j => gs (co + j)]).  So the twin arm, its supply and its           *)
(* diagnostic instance had no consumer and are gone; what stays is the    *)
(* command as a value (S1: [cmd_cat], [cat_toks], [cat_cmd],              *)
(* [cat_argv_bytes], read by [PipesCut] and the pipe nodes) and the       *)
(* anti-vacuity finding (S5), which is the note on why [line_ok] is not a *)
(* parameter of the arm.                                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import UmodeAbi.
Require Import UserHeap.
Require Import UkShRun.
Require Import UkShMain.
Require Import EchoDisc.
Require Import UkShPipeLex.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(* S1  THE RIGHT COMMAND, AS A VALUE.                                     *)
(*                                                                        *)
(* [UkShPipeLex.ush_line_toks_holds_pipe]'s fifth conjunct: the right     *)
(* command's token list is the SINGLETON                                  *)
(*   [(length (wl_body ws) + 3, length (wl_body ws) + 3 + length right)]  *)
(* and [UShPipeChild.wp_kshm_child_pipe_paid] hands the right child       *)
(* [UExec (ush_args s0 G [(S (S gp), ge)])] at that pair.  So the         *)
(* command below is that node at an ABSTRACT token [(a, b)], and the      *)
(* pipeline's is the instance at [right := ushq_cat] (three bytes).       *)
(* ===================================================================== *)

(* the command name the pipeline's right side spells, and its length *)
Definition cmd_cat : list (bv 8) := UkShPipeLex.ushq_cat.

Lemma cmd_cat_len : length cmd_cat = 3%nat.
Proof using . exact UkShPipeLex.ushq_cat_len. Qed.

Definition cat_toks (a b : nat) : list (nat * nat) := [(a, b)].

Definition cat_cmd (a b : nat) (s0 : Z) (g : nat -> bv 8) : ushcmd :=
  UExec (UkShMain.ush_args s0 g (cat_toks a b)).

Lemma cat_cmd_args_length (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  length (UkShMain.ush_args s0 g (cat_toks a b)) = 1%nat.
Proof using . rewrite UkShMain.ush_args_length. reflexivity. Qed.

(* ---- the argv BYTES, as a pure premise ------------------------------ *)
(* [UkShEcho.echo_argv_bytes] at the one token: the command's three bytes
   are "cat" and the cut's NUL sits at the token's end.  The LENGTH
   equation is a CONJUNCT and not a side premise, on [EchoDisc.line_ok]'s
   own pattern -- a reading that carried the bytes but left [b] free could
   be satisfied at a [b] the walk cannot use. *)
Definition cat_argv_bytes (a b : nat) (g : nat -> bv 8) : Prop :=
  b = (a + length cmd_cat)%nat
  /\ (forall j : nat, (j < length cmd_cat)%nat ->
        g (a + j)%nat = cmd_cat !!! j)
  /\ g b = ubyte0.

Lemma cat_argv_bytes_end (a b : nat) (g : nat -> bv 8) :
  cat_argv_bytes a b g -> b = (a + 3)%nat.
Proof using .
  intros (Hb & _ & _). rewrite Hb cmd_cat_len. reflexivity.
Qed.

Lemma cat_toks_lookup (a b : nat) :
  cat_toks a b !! 0%nat = Some (a, b).
Proof using . reflexivity. Qed.

Lemma cat_cmd_args_lookup (a b : nat) (s0 : Z) (g : nat -> bv 8) :
  b = (a + 3)%nat ->
  UkShMain.ush_args s0 g (cat_toks a b) !! 0%nat
  = Some (UArg (s0 + Z.of_nat a) 3%nat (fun j : nat => g (a + j)%nat)).
Proof using .
  intro Hb.
  rewrite (UkShMain.ush_args_lookup s0 g (cat_toks a b) 0%nat (a, b)
             (cat_toks_lookup a b)).
  cbn [fst snd]. rewrite Hb.
  replace (a + 3 - a)%nat with 3%nat by lia. reflexivity.
Qed.

(* ---- the pipe line's own cut satisfies the reading ------------------- *)
(* [UkShPipeRound.ushq_cut_ok_right]'s twin on the BYTE side: the cut
   [nulterminate]'s PIPE row leaves is transparent inside the right
   command's word (every argument token of the LEFT command ends below the
   '|', which is below the right word's base) and is the terminator at its
   end.  Spelled at [UkShParseCmd]'s fold so that this file does not
   depend on [UkShPipeRound]. *)


(* ===================================================================== *)
(* S5  THE ANTI-VACUITY WITNESS, AND THE LANE'S FINDING                   *)
(*                                                                        *)
(* [UCatPipe.pcat_image_entry] -- design section 5.3's landed (E) half,   *)
(* and the lemma this lane was told to plug its supply into -- takes      *)
(*                                                                        *)
(*     line_ok ws  ->  ...  ->  length ws = 1%nat  ->  ...                *)
(*                                                                        *)
(* and [EchoDisc.line_ok] contains [2 <= length ws] (it must: echo prints *)
(* nothing at argc 1, durable-notes' degenerate-member rule).  So the     *)
(* premise set is contradictory, the entry is VACUOUSLY true and no       *)
(* caller can ever apply it.  One line says so, and it is what a          *)
(* premise-threading lane cannot tell from a satisfiable one.             *)
(* ===================================================================== *)
Lemma cat_line_premises_absurd (ws : list (list (bv 8))) :
  line_ok ws -> length ws = 1%nat -> False.
Proof using .
  intros Hok H1. pose proof (line_ok_ge2 ws Hok). lia.
Qed.

(* ...and the same sentence at the OTHER conjunct, so that a repair that
   only relaxes the count is seen to be insufficient: an admissible line's
   first word is "echo", and cat's is "cat". *)
Lemma cat_line_head_absurd (ws : list (list (bv 8))) :
  line_ok ws -> ws !! 0%nat = Some cmd_cat -> False.
Proof using .
  intros Hok Hhd.
  pose proof (line_ok_head ws Hok) as He. rewrite Hhd in He.
  vm_compute in He. discriminate He.
Qed.

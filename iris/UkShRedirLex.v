(* ===================================================================== *)
(* UkShRedirLex.v -- the LEXER's redirect facts, lane SH-REDIR             *)
(* (design/app-file.md SS5.1, deliverable 1).                              *)
(*                                                                        *)
(* [UkShParseLex.wp_kshp_peek] is already FULLY GENERAL: it takes no       *)
(* [ushp_no_symbols] and its answer is the computed                        *)
(* [ushp_peek_res len f k tlen tf].  So peek's "<>" TABLE HIT -- the fact  *)
(* that makes [parseredirs]' loop turn -- is a PURE lemma and not a walk,  *)
(* the mirror image of [UkShParseLex.ushp_peek_res_sym] (the fact that     *)
(* makes it not turn).  Both are about [ushp_find] over the literal at     *)
(* [ushp_T_redir] = 0x12f0, which is the two bytes "<>".                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UkShParse.
Require Import UkShParseLex.
Local Open Scope Z_scope.

(* [strchr] HITS a table one of whose bytes is the one looked for --
   [UkShParseLex.ushp_find_none]'s converse. *)
Lemma ushp_find_some (n i : nat) (f : nat -> bv 8) (c : bv 8) (j : nat) :
  (i <= j < i + n)%nat -> f j = c ->
  exists k : nat, ushp_find n i f c = Some k.
Proof.
  revert i. induction n as [| n IH ]; intros i Hij Hfj; [ lia | ].
  cbn [ushp_find].
  destruct (bool_decide (f i = c)) eqn:Hb; [ exists i; reflexivity | ].
  apply (IH (S i)); [ | exact Hfj ].
  destruct (Nat.eq_dec i j) as [ He | Hne ].
  - exfalso. apply bool_decide_eq_false in Hb. apply Hb. rewrite He. exact Hfj.
  - lia.
Qed.

(* ...so a peek INSIDE the line for a table that contains the byte at the
   cursor answers 1. *)
Lemma ushp_peek_res_hit (len : nat) (f : nat -> bv 8) (k tlen : nat)
    (tf : nat -> bv 8) (j : nat) :
  (k < len)%nat -> (j < tlen)%nat -> tf j = f k ->
  ushp_peek_res len f k tlen tf = 1.
Proof.
  intros Hk Hj Htf. unfold ushp_peek_res.
  rewrite (bool_decide_eq_true_2 _ Hk).
  destruct (ushp_find_some tlen 0%nat tf (f k) j ltac:(lia) Htf) as [ q Hq ].
  rewrite Hq. reflexivity.
Qed.

(* THE REDIRECT BYTE, read off the dump rather than written down: entry 1
   of the literal at [ushp_T_redir] is '>'. *)
Lemma ushp_T_redir_gt : ushp_lit ushp_T_redir 1%nat = Z_to_bv 8 62.
Proof. vm_compute. reflexivity. Qed.

Lemma ushp_T_redir_lt : ushp_lit ushp_T_redir 0%nat = Z_to_bv 8 60.
Proof. vm_compute. reflexivity. Qed.

(* ...and the fact [parseredirs]' guard turns on for the line `... > f'.  *)
Lemma ushp_peek_redir_hit (len : nat) (f : nat -> bv 8) (k : nat) :
  (k < len)%nat -> f k = Z_to_bv 8 62 ->
  ushp_peek_res len f k 2 (ushp_lit ushp_T_redir) = 1.
Proof.
  intros Hk Hf.
  apply (ushp_peek_res_hit len f k 2 (ushp_lit ushp_T_redir) 1%nat Hk
           ltac:(lia)).
  rewrite ushp_T_redir_gt. rewrite Hf. reflexivity.
Qed.

(* ...and '>' IS a symbol byte, which is why [ushp_no_symbols] refutes the
   redirect shape and a new premise is owed for it. *)
Lemma ushp_gt_is_sym : ushp_is_sym (Z_to_bv 8 62) = true.
Proof. vm_compute. reflexivity. Qed.

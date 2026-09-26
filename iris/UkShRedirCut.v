(* ===================================================================== *)
(* UkShRedirCut.v -- THE REDIRECT LINE'S CUT, in its landed spelling      *)
(* (user-once A3b).                                                       *)
(*                                                                        *)
(* [nulterminate] on `echo w1 .. wn > file' zeroes every argument's end   *)
(* byte (its EXEC arm, [UkShParseCmd.ushp_nulfold]) and the file name's   *)
(* (its REDIR arm, one [ushp_setb]).  Since A2d the general spelling is   *)
(* [UkShParser.ushp_zero_at (ref_nulcut t)]; this one is what the         *)
(* redirect seam, body and child STATE ([UkShRedirSeam], [UkShRedirBody], *)
(* [UkShRedirChild]), and [UkShParser.ushp_nulfold_zero_at] plus          *)
(* [ushp_zero_at_snoc] rewrite it into the general one.  It lived in the  *)
(* redirect parser shell [UkShRedirPc], which A3b deleted.                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.        (* [ubyte0] *)
Require Import UkShParse.
Require Import UkShParseCmd.    (* [ushp_setb] / [ushp_nulfold] / [ushp_ext] *)
Local Open Scope Z_scope.

(* the line after the parse: every argument's end byte cut to NUL by
   [nulterminate]'s EXEC arm, and the file name's by its REDIR arm *)
Definition ushs_nulcut (args : list (nat * nat)) (len : nat)
    (f : nat -> bv 8) (fe : nat) : nat -> bv 8 :=
  ushp_setb (ushp_nulfold args (ushp_ext len f)) fe ubyte0.

Lemma ushs_nulcut_arg (args : list (nat * nat)) (len : nat)
    (f : nat -> bv 8) (fe : nat) (i : nat) (tk : nat * nat) :
  args !! i = Some tk -> ushs_nulcut args len f fe (snd tk) = ubyte0.
Proof using .
  intro Hi. unfold ushs_nulcut, ushp_setb.
  destruct (Nat.eqb (snd tk) fe); [ reflexivity | ].
  exact (ushp_nulfold_hit args (ushp_ext len f) i tk Hi).
Qed.

Lemma ushs_nulcut_file (args : list (nat * nat)) (len : nat)
    (f : nat -> bv 8) (fe : nat) :
  ushs_nulcut args len f fe fe = ubyte0.
Proof using .
  unfold ushs_nulcut, ushp_setb. rewrite Nat.eqb_refl. reflexivity.
Qed.

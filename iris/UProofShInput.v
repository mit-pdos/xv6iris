(* UProofShInput.v -- the GLUE between the parser's general contracts and
   the concrete theorem.

   USpecShParse.v states [peek], [gettoken] and the four [parse*] over an
   arbitrary buffer [bs] and an arbitrary tokenization [toks] related by the
   inductive [sh_tokens].  The theorem (USpecSh.wp_sh_start_body) is about
   ONE buffer: the eighteen bytes `echo Hello world!\n' that [gets] leaves
   behind.  Everything here discharges the parser's premises AT that buffer
   and computes what its postconditions then say -- so this file is what
   turns "the parser records the token boundaries" into "the exec names
   ("echo", ["echo"; "Hello"; "world!"])".

   It is all PURE: no weakest precondition, no protocol, no image.  That is
   deliberate -- the tokenization model is a place where a plausible-looking
   definition can be quietly WRONG (off by one at a separator, or at the
   trailing newline), and the cheapest way to find that out is to compute it
   on the real input rather than to discover it inside a WP proof. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import UmodeAbi.
Require Import UCodeSh USpecSh USpecShParse.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The buffer, and its tokenization.                                   *)
(*                                                                        *)
(*   offset  0123456789...                                                *)
(*           echo Hello world!\n                                          *)
(*           ^^^^ ^^^^^ ^^^^^^                                            *)
(*           0..4 5..10  11..17                                           *)
(*                                                                        *)
(* The trailing newline is whitespace, so scanning ends exactly at 18 and  *)
(* [ShTokNil] applies at offset 17 -- NOT at 18.  That asymmetry is the    *)
(* one place this model could plausibly have been off by one.             *)
(* ===================================================================== *)

Definition sh_echo_toks : list (nat * nat) := [(0, 4); (5, 10); (11, 17)]%nat.

Lemma sh_echo_input_len : length sh_echo_input = 18%nat.
Proof. reflexivity. Qed.

Lemma sh_echo_tokens : sh_tokens sh_echo_input 0%nat sh_echo_toks.
Proof.
  cbv [sh_echo_toks].
  (* "echo" *)
  change (0, 4)%nat with (0 + 0, 0 + 0 + 4)%nat.
  apply ShTokCons; [ vm_compute; lia | ].
  (* "Hello" *)
  change (0 + 0 + 4)%nat with 4%nat.
  change (5, 10)%nat with (4 + 1, 4 + 1 + 5)%nat.
  apply ShTokCons; [ vm_compute; lia | ].
  (* "world!" *)
  change (4 + 1 + 5)%nat with 10%nat.
  change (11, 17)%nat with (10 + 1, 10 + 1 + 6)%nat.
  apply ShTokCons; [ vm_compute; lia | ].
  (* and the trailing newline is skipped, landing exactly on |bs| *)
  change (10 + 1 + 6)%nat with 17%nat.
  apply ShTokNil. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 The premises the parser's contracts impose on the buffer.           *)
(* ===================================================================== *)

Lemma sh_echo_no_symbols : sh_no_symbols sh_echo_input.
Proof.
  intros j b Hj.
  (* eighteen concrete bytes; [list_lookup] pins each one *)
  repeat (destruct j as [|j]; [ vm_compute in Hj; injection Hj as <-;
                                vm_compute; reflexivity | ]).
  vm_compute in Hj. discriminate.
Qed.

Lemma sh_echo_no_nul :
  forall (j : nat) (b : bv 8), sh_echo_input !! j = Some b -> b <> ubyte0.
Proof.
  intros j b Hj.
  repeat (destruct j as [|j]; [ vm_compute in Hj; injection Hj as <-;
                                vm_compute; discriminate | ]).
  vm_compute in Hj. discriminate.
Qed.

(* what [nulterminate] needs: every token is a non-empty range inside [bs] *)
Lemma sh_echo_toks_sep :
  forall (i : nat) (t : nat * nat), sh_echo_toks !! i = Some t ->
    (fst t < snd t <= length sh_echo_input)%nat.
Proof.
  intros i t Hi.
  repeat (destruct i as [|i]; [ vm_compute in Hi; injection Hi as <-;
                                vm_compute; lia | ]).
  vm_compute in Hi. discriminate.
Qed.

Lemma sh_echo_toks_len : length sh_echo_toks = 3%nat.
Proof. reflexivity. Qed.

Lemma sh_echo_toks_ne : (0 < length sh_echo_toks < 10)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(* §3 THE PAYOFF: what the recorded boundaries spell.                      *)
(*                                                                        *)
(* [parsecmd]'s postcondition is [uexec_args] at                           *)
(*   path = sh_tok_bytes bs (default (0,0) (toks !! 0))                    *)
(*   args = sh_tok_bytes bs <$> toks                                       *)
(* and the theorem's [Q] is at [sh_echo_path] / [sh_echo_argv].  These two  *)
(* lemmas are the identification, and they are the reason the theorem says  *)
(* what it appears to say.                                                 *)
(* ===================================================================== *)

Lemma sh_echo_path_eq :
  sh_tok_bytes sh_echo_input (default (0, 0)%nat (sh_echo_toks !! 0%nat))
    = sh_echo_path.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_echo_argv_eq :
  sh_tok_bytes sh_echo_input <$> sh_echo_toks = sh_echo_argv.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* §4 The lexer's static tables are DERIVABLE from the image.             *)
(*                                                                        *)
(* [sh_tables_ok] is carried as a separate premise by the lexer and parser *)
(* contracts, and by [wp_sh_main_body] -- but [wp_sh_start_body] does not  *)
(* carry it, only [sh_img_sub].  So the start -> main step needs this      *)
(* derivation, and it is not optional.                                    *)
(*                                                                        *)
(* It is also worth having for its own sake.  A premise that RESTATES      *)
(* something the image already fixes can silently disagree with it -- ask  *)
(* for tables the program does not have and every contract downstream      *)
(* becomes unusable at its call site, with nothing in the build to say so  *)
(* (see UProofShHeap.v's D5/D6).  Deriving it makes that impossible: the   *)
(* bytes come from the dump.  For the record, they are                     *)
(*   0x2000: 3c 7c 3e 26 3b 28 29 00   "<|>&;()"                          *)
(*   0x2008: 20 09 0d 0a 0b 00         " \t\r\n\v"                        *)
(* ===================================================================== *)

Lemma sh_img_tables (M : gmap Z (bv 8)) : sh_data_sub M -> sh_tables_ok M.
Proof.
  intros Hd. split; split.
  - intros j b Hj.
    repeat (destruct j as [|j];
            [ vm_compute in Hj; injection Hj as <-;
              apply Hd; vm_compute; reflexivity | ]).
    vm_compute in Hj. discriminate.
  - apply Hd. vm_compute. reflexivity.
  - intros j b Hj.
    repeat (destruct j as [|j];
            [ vm_compute in Hj; injection Hj as <-;
              apply Hd; vm_compute; reflexivity | ]).
    vm_compute in Hj. discriminate.
  - apply Hd. vm_compute. reflexivity.
Qed.

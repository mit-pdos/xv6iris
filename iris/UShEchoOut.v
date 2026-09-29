(* ===================================================================== *)
(*  UShEchoOut.v -- WHAT SH OWES ECHO'S OUTPUT                            *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane IO-LEAF, M3.)       *)
(*                                                                       *)
(*  [UEchoOut.echo_uexec_slot_at] -- echo's entry at the era's stage --   *)
(*  carries premises echo itself cannot know, because they are facts      *)
(*  about the process that EXEC'd it.  One of them is its argument        *)
(*  vector: [UEchoOut.echo_out_argv ws] says argc is the line's word      *)
(*  count and that [argv[i]] is word [i] of the line, spelled against the *)
(*  ERA's alternative ([EchoDisc.line_alts_of ws !!! 0]) rather than      *)
(*  against the shell's lexer -- so that                                  *)
(*  nothing in [UEchoOut] depends on which parser produced the vector.    *)
(*                                                                       *)
(*  THIS FILE IS THE OTHER HALF OF THAT SENTENCE.  sh's parser pins the   *)
(*  arguments to [wl_line ws] ([UShEcho.echo_key_args], off               *)
(*  the exec channel's [SpecKexec.kexec_image_ok]), and the era's         *)
(*  alternative is the SAME BYTES one word on: the output is              *)
(*  [wl_line (drop 1 ws)], the line minus its command name.  So the       *)
(*  bridge is two applications of [LineWords.wl_line_word]                *)
(*  and nothing else, and it is a file of its own because it is the ONE   *)
(*  place where the shell's reading of the line and the claim's reading   *)
(*  of the transcript are the same bytes -- [UShEcho.v] sits below        *)
(*  [UEchoOut.v] and cannot name it.                                      *)
(*                                                                       *)
(*  WHAT IS STILL OWED at [echo_uexec_slot_at]: the child's fd 1 is the   *)
(*  console ([take NSTD (uvis_fd W) !! 1]).  The exec channel carries the *)
(*  table verbatim ([kexec_image_ok]'s [uvis_fd W' = sts]), so that one   *)
(*  is a fact about SH's table and travels with the entry lend -- lane    *)
(*  IO-LEAF, M3b, which is blocked (see the lane note).                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import FdSlots.
Require Import UmodeAbi.          (* [ubyte0] *)
Require Import UserHeap.          (* [uarg] / [ua_len] / [ua_bytes] *)
Require Import UexecSlot.         (* [uvis] and its fields *)
Require Import SpecKexec.         (* [kexec_image_ok] *)
Require Import ElfUser.           (* [echo_elf] *)
Require Import LineWords.         (* [wl_line] / [wl_off] / [wl_line_word] *)
Require Import EchoDisc.          (* [line_ok] / [out_cur] / [line_alts_of] *)
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] *)
Require Import UkShEcho.          (* [echo_off] / [echo_alen] *)
Require Import UShEcho.           (* [echo_key_args] *)
Require Import UEchoOut.          (* [echo_out_argv] *)
(* as in EchoDisc / UEchoOut: the Sail imports leave string_scope on top *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1  THE BRIDGE, IN ONE SENTENCE                                       *)
(*                                                                       *)
(*  The good alternative opens with [wl_line] of the line's TAIL, so the *)
(*  alternative's byte where the OUTPUT puts word [i] and the line's byte *)
(*  where the INPUT puts it are the same byte of the same word -- twice   *)
(*  [LineWords.wl_line_word] and nothing else.  This used to be two       *)
(*  five-way case analyses over the literal's offsets.                    *)
(*                                                                       *)
(*  (The alternative continues past the output with the prompt sh writes  *)
(*  once it has reaped, which is why the lookup needs the bound.)         *)
(* ===================================================================== *)
Lemma echo_alt0_word (ws : list (list (bv 8))) (i j : nat)
    (w : list (bv 8)) :
  (1 <= i)%nat -> ws !! i = Some w -> (j < length w)%nat ->
  line_alts_of ws !!! 0%nat !! (out_cur ws i + j)%nat
  = Some (wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat).
Proof.
  intros Hi Hw Hj.
  assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
    by (rewrite ws_drop; [exact Hw | exact Hi]).
  rewrite (alt0_out ws (out_cur ws i + j)%nat
             (out_cur_lt ws i w j Hi Hw (Nat.lt_le_incl _ _ Hj))).
  rewrite /out_cur.
  destruct (lookup_lt_is_Some_2 (wl_line (drop 1 ws))
              (wl_off 0%nat (drop 1 ws) (i - 1)%nat + j)%nat
              ltac:(exact (wl_off_lt_line (drop 1 ws) (i - 1)%nat w j
                             Hd (Nat.lt_le_incl _ _ Hj)))) as [b Hb].
  rewrite Hb. f_equal.
  rewrite <- (list_lookup_total_correct _ _ _ Hb).
  rewrite (wl_line_word (drop 1 ws) (i - 1)%nat w j Hd Hj).
  rewrite /UkShEcho.echo_off.
  by rewrite (wl_line_word ws i w j Hw Hj).
Qed.

(* ===================================================================== *)
(*  S2  THE BRIDGE                                                        *)
(* ===================================================================== *)
Lemma echo_out_argv_of_key_args (ws : list (list (bv 8)))
    (M : gmap Z (bv 8)) (av : Z) (argcn : nat) :
  argcn = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     ua_len (echo_arg M av i) = length (ws !!! i)
     /\ forall j : nat, (j < length (ws !!! i))%nat ->
          ua_bytes (echo_arg M av i) j
          = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat) ->
  UEchoOut.echo_out_argv ws (echo_args M av argcn).
Proof.
  intros -> Hk. rewrite /UEchoOut.echo_out_argv.
  split; [ exact (echo_args_length M av (length ws)) | ].
  intros i g Hi1 Hg.
  assert (Hilt : (i < length ws)%nat)
    by (apply lookup_lt_Some in Hg; rewrite echo_args_length in Hg; lia).
  rewrite (echo_args_lookup M av (length ws) i Hilt) in Hg.
  injection Hg as <-.
  destruct (Hk i Hilt) as [Hlen Hb].
  split; [ exact Hlen | ].
  intros j Hj. rewrite Hlen in Hj.
  rewrite (Hb j Hj).
  exact (echo_alt0_word ws i j (ws !!! i) Hi1
           (UEchoOut.ws_at ws i Hilt) Hj).
Qed.

(* ...AND OFF THE EXEC CHANNEL, which is the form the entry constructor
   will take it at: what sh hands the kernel is the node its parser built
   ([UkShEcho.echo_argv_bytes]), what the kernel hands back is the image
   ([SpecKexec.kexec_image_ok]), and [UShEcho.echo_key_args_holds] is the
   step between them. *)
Lemma echo_out_argv_of_image (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W : uvis) :
  line_ok ws ->
  kexec_image_ok ElfUser.echo_elf na alen afun sts W ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  (forall i j : nat, (i < length ws)%nat ->
     (j < UkShEcho.echo_alen ws i)%nat ->
     afun i j = wl_line ws !!! (UkShEcho.echo_off ws i + j)%nat) ->
  UEchoOut.echo_out_argv ws
    (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))).
Proof.
  intros Hokws Hok Hna Halen Hafun. subst na.
  (* the general reading's ONE side condition, at this line: no byte exec
     pushed is a NUL, because every one of them is the line's own *)
  assert (Hno : forall i j : nat, (i < length ws)%nat ->
            (j < alen i)%nat -> afun i j <> ubyte0).
  { intros i j Hi Hj. rewrite (Halen i Hi) in Hj.
    rewrite (Hafun i j Hi Hj).
    exact (UShEcho.line_nonul ws _ Hokws
             (UkShEcho.echo_off_lt ws i j Hokws Hi
                (Nat.lt_le_incl _ _ Hj))). }
  destruct (UShEcho.echo_key_args_holds (length ws) alen afun sts W
              Hok Hno) as [Hargc Hk].
  apply (echo_out_argv_of_key_args ws (uvis_M W) (uvis_av W)
           (Z.to_nat (uvis_argc W)) Hargc).
  intros i Hi. destruct (Hk i Hi) as [Hl Hb].
  split; [ rewrite Hl; exact (Halen i Hi) | ].
  intros j Hj. rewrite (Hb j ltac:(rewrite (Halen i Hi); exact Hj)).
  exact (Hafun i j Hi Hj).
Qed.

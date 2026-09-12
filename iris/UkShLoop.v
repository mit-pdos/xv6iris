(* ===================================================================== *)
(* UkShLoop.v -- WHAT THE COMMAND LOOP HAS TO CARRY, once main's body is  *)
(* walked.                                                                *)
(*                                                                        *)
(* [UkSh.ush_loop_head] carries the five constants, the descriptor        *)
(* promise and the line buffer, and hands its walk [16 + n].  That was    *)
(* enough for stages 1-2, which stop at the blank-line test.  main's body *)
(* needs three more things and a bigger frame, and this file states them  *)
(* once so that the [cd] arm and the FORK arm meet at the same interface: *)
(*                                                                        *)
(*   the two static lexer tables at 0x2000 / 0x2008 -- the parser reads   *)
(*     them on every line and never writes them;                          *)
(*   the allocator's untouched first-call state ([freep] = 0, [base]) --  *)
(*     see the note in iris/UkShFork.v: the PARENT never calls malloc, so *)
(*     an untouched state going round the loop is the control flow and    *)
(*     not a weakening;                                                    *)
(*   the break [usz γs sz], which the child's [sbrk] moves in ITS copy of *)
(*     the address space and not in the parent's;                          *)
(*                                                                        *)
(* and [16 + (80 + n)] rather than [16 + n]: fork1's own 2 words, the     *)
(* diagnostic subtree's 28, the parser's 60 and the runner's 8.  The      *)
(* [cd] arm's 26 (fprintf's frame) fits inside the same 80.               *)
(*                                                                        *)
(* NOTHING HERE IS PROVED -- it is two definitions and the one-line       *)
(* accessor that turns the data half into what the allocator's contract   *)
(* asks for.  It is a file of its own only so that both arms can be       *)
(* stated against it without one of them requiring the other.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UserHeap UkRun.
Require Import FdSlots UserFd.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShMalloc.
Require Import TsoCtx.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
Require Import UserConsole.  (* [upos] -- sh's half of the console position pair *)
(* ===================================================================== *)
(* THE DISCIPLINED LINE LEXES (lane SH-LINE 2b, L3).                      *)
(*                                                                        *)
(* [UkShFork.ushf_lexable] was "every line the user could type lexes",     *)
(* which is false.  This is the true replacement: the ONE line the read's  *)
(* receipt delivers ([UkSh.ush_line_is] -- the buffer at [k] holds         *)
(* [EchoDisc.echo_line]) has no symbol byte and tokenises into fewer than  *)
(* ten tokens.  A CLOSED computation at the literal, so no assumption      *)
(* about user input survives it; [UConsLine.ush_echo_tokens] is the        *)
(* computation and E4 ([UkShEcho.ush_line_toks_holds]) is the stronger     *)
(* form with the token list named.                                        *)
(*                                                                        *)
(* IT LIVES HERE because it is the LOWEST file that sees both halves:      *)
(* [UkSh.ush_line_is] (the line) and [UkShParse.ushp_*] (the lexer).       *)
(* [UkShFork] takes it as a premise and must not reach for [UConsLine],    *)
(* whose cone (init's catalogs, the application's invariant) has no        *)
(* business in a proofmode-heavy walk file. *)
(* ===================================================================== *)
Definition ush_line_lexable : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    UkSh.ush_line_is f k len ->
    ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ exists toks : list (nat * nat),
         ushp_tokens len (fun j : nat => f (k + j)%nat) 0 toks
         /\ (length toks < 10)%nat.

Section UkShLoop.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* [Xv6Cameras.uartGhostG] and the POSITION's ghost name, which
     [UkSh.ush_pstate] carries as its fourth conjunct (app-echo.md,
     "SH-LINE RULING"): this walk never reads the number, but the resource
     travels through every lemma that carries the process state. *)
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* the DATA a turn of the loop needs and does not create.  [8208] is
     [freep] (0x2010) and [8328] is [base] (0x2088) -- the two literals
     [UkShMalloc.ushm_fresh] unfolds to. *)
  (* AT A BARE DATA NAME, not at the record's: a forked child assembles
     this at ITS name out of the mirrored fragments, so [UkShFork.ushf_pay]
     -- a [gname -> gname -> gname] payload family -- has to be able to
     write it down. *)
  Definition ushl_dat (g : gname) : iProp Σ :=
    (ustr g DfracDiscarded ushp_whitespace 5 ushp_ws_f ∗
     ustr g DfracDiscarded ushp_symbols 7 ushp_sym_f ∗
     uword g 8208 (mword_of_int 0) ∗
     (∃ fb : nat -> bv 8, ubytes g 8328 16 fb))%I.

  Lemma ushl_fresh_of_dat (sz : Z) :
    ushl_dat γd -∗ usz γs sz -∗
      UkShMalloc.ushm_fresh N sz ∗
      ustr γd DfracDiscarded ushp_whitespace 5 ushp_ws_f ∗
      ustr γd DfracDiscarded ushp_symbols 7 ushp_sym_f.
  Proof.
    iIntros "(Hws & Hsy & Hfp & Hbase) Hsz".
    rewrite /UkShMalloc.ushm_fresh. iFrame "Hfp Hbase Hsz Hws Hsy".
  Qed.

  (* the loop head, at the resources and the budget main's body forces on
     it -- i.e. what [UkSh.ush_loop_head] has to become *)
  Definition ushl_head (l : list fdstate) (sz : Z) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ UkSh.ush_regs m ⌝ -∗
       (* ...and the row the console preamble established (lane SH-OPEN):
          fd 0 is the console device, or it is closed.  PURE, and carried
          unchanged by the whole of the command loop. *)
       ⌜ UkSh.ush_fd0p l ⌝ -∗
       UkSh.ush_pstate N γp l -∗
       ushl_dat γd -∗ usz γs sz -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x938) (16 + (80 + n)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* [UkSh.ush_rest]'s opaque [R], AT THIS SHELL.  The re-cut left [R] a
     parameter precisely so that this line -- which mentions the parser's
     tables and the allocator's cells -- does not have to live in
     iris/UkSh.v.  The break rides with them: [usz] is not bytes, so it is
     not part of [ushl_dat], but a turn carries it all the same. *)
  Definition ushl_R (sz : Z) : iProp Σ := (ushl_dat γd ∗ usz γs sz)%I.

  (* ...and then [UkSh.ush_loop_head] AT that [R] IS [ushl_head]: the same
     four binders, the same budget ([UkSh.ush_Dbody] is 80), and the two
     halves of [ushl_R] uncurried. *)
  Lemma ushl_head_of_R (l : list fdstate) (sz : Z) :
    UkSh.ush_loop_head N γp (ushl_R sz) l -∗ ushl_head l sz.
  Proof.
    iIntros "H" (h m f n) "%Hregs %Hfd0 Hstd Hdat Hsz Hbuf Hrun".
    iApply ("H" $! h m f n with "[%//] [%//] Hstd [$Hdat $Hsz] Hbuf Hrun").
  Qed.

End UkShLoop.

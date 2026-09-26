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
(* and [16 + (ush_Dbody + n)] rather than [16 + n]: fork1's own 2 words,  *)
(* diagnostic subtree's 28, the parser's 60 and the runner's 8.  The      *)
(* [cd] arm's 26 (fprintf's frame) fits inside the same room, and the     *)
(* REDIRECT line's parse takes eight more than the symbol-free one (lane   *)
(* SH-CHILD-2), which is why [UkSh.ush_Dbody] is 88 and not 80.            *)
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
Require Import UkShParseSym.
Require Import LineWords.
Require Import UkShRedirLine.
Require Import UkShMalloc.
Require Import CtxIdDefs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
(* ===================================================================== *)
(* THE DISCIPLINED LINE LEXES (lane SH-LINE 2b, L3).                      *)
(*                                                                        *)
(* [UkShFork.ushf_lexable] was "every line the user could type lexes",     *)
(* which is false.  This is the true replacement: the line the read's      *)
(* receipt delivers ([UkSh.ush_line_is] -- the buffer at [k] holds         *)
(* [wl_line ws] for an ADMISSIBLE word list) has no symbol byte and        *)
(* tokenises into fewer than ten tokens.  Not a computation at a literal   *)
(* any more but a fact about every admissible line, off [EchoDisc.line_ok] *)
(* and [UkShWords]; E4 ([UkShEcho.ush_line_toks_holds]) is the stronger    *)
(* form with the token list named.                                        *)
(*                                                                        *)
(* IT LIVES HERE because it is the LOWEST file that sees both halves:      *)
(* [UkSh.ush_line_is] (the line) and [UkShParse.ushp_*] (the lexer).       *)
(* [UkShFork] takes it as a premise and must not reach for [UConsLine],    *)
(* whose cone (init's catalogs, the application's invariant) has no        *)
(* business in a proofmode-heavy walk file. *)
(* ===================================================================== *)
Definition ush_line_lexable : Prop :=
  forall (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat),
    UkSh.ush_line_is ws f k len ->
    ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ exists toks : list (nat * nat),
         ushp_tokens len (fun j : nat => f (k + j)%nat) 0 toks
         /\ (length toks < 10)%nat.

(* ===================================================================== *)
(* THE SECOND LEXABLE PREDICATE (lane SH-PARSE-2, design SS5.1).           *)
(*                                                                        *)
(* [ush_line_lexable] CANNOT simply grow to admit the redirect line.       *)
(* [UkShRedirLine.ushs_line_is_nosym] proves why: a line [UkSh.ush_line_is] *)
(* describes never carries a symbol byte, because it carries               *)
(* [EchoDisc.line_ok], hence [LineWords.wl_wf], hence every buffer byte is  *)
(* alphanumeric, a blank or the newline.  Weakening this predicate's       *)
(* CONCLUSION to "no symbols OR the redirect shape" would add a right      *)
(* disjunct unreachable from its own premise, and the child's redirect arm *)
(* would be vacuous.                                                       *)
(*                                                                        *)
(* So the redirect line gets its OWN positional predicate                  *)
(* ([UkShRedirLine.ushs_line_is]) and its own lexability [Prop], and a     *)
(* widened premise is the CONJUNCTION of the two rather than a disjunction *)
(* inside one.  The first conjunct below is derivable                      *)
(* ([UkShRedirLine.ushs_line_is_redir]) and is stated anyway, exactly as   *)
(* [ush_line_lexable]'s first conjunct is; what is NOT derivable, and so   *)
(* what the premise is really for, is the token count.                     *)
(* ===================================================================== *)
Definition ush_line_lexable_redir : Prop :=
  forall (ws : list (list (bv 8))) (file : list (bv 8)) (f : nat -> bv 8)
         (k len : nat),
    UkShRedirLine.ushs_line_is ws file f k len ->
    ushs_redir len (fun j : nat => f (k + j)%nat)
      (length (wl_body ws) + 1)%nat
      (length (wl_body ws) + 3 + length file)%nat
    /\ exists args : list (nat * nat),
         ushs_toks len (fun j : nat => f (k + j)%nat)
           (length (wl_body ws) + 1)%nat 0 args
         /\ (0 < length args)%nat
         /\ (length args < 10)%nat.

(* ...and its first conjunct IS derivable, so a supplier owes only the
   token list.  [UkShLoop] states it here because this is the lowest file
   that sees both halves. *)
Lemma ush_line_lexable_redir_shape (ws : list (list (bv 8)))
    (file : list (bv 8)) (f : nat -> bv 8) (k len : nat) :
  UkShRedirLine.ushs_line_is ws file f k len ->
  ushs_redir len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat
    (length (wl_body ws) + 3 + length file)%nat.
Proof. exact (UkShRedirLine.ushs_line_is_redir ws file f k len). Qed.

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
  Proof using .
    iIntros "(Hws & Hsy & Hfp & Hbase) Hsz".
    rewrite /UkShMalloc.ushm_fresh. iFrame "Hfp Hbase Hsz Hws Hsy".
  Qed.

  (* the loop head, at the resources and the budget main's body forces on
     it -- i.e. what [UkSh.ush_loop_head] has to become *)
  (* [T] IS A PARAMETER (lane IO-LEAF, M5(3)): the process state carries
     the cursor AT A LINE BOUNDARY now ([UkSh.ush_posb]), and the arm a
     tainted turn is at names the application's [T].  This file proves
     nothing about the taint, so it takes it opaquely rather than binding
     it as a section variable. *)
  (* ...AND [Wc] TOO (lane IO-LEAF, M6a(3)): the era's write credential
     the command loop carries beside its cursor, opaque here for [T]'s
     reason -- and, at step 3, the banner-owed credential [Wb] and the
     lease's pieces [Pm] that the loop holds in its place. *)
  Definition ushl_head (T : iProp Σ) (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) (sz : Z) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ UkSh.ush_regs m ⌝ -∗
       (* ...and the row the console preamble established (lane SH-OPEN):
          fd 0 is the console device, or it is closed.  PURE, and carried
          unchanged by the whole of the command loop. *)
       ⌜ UkSh.ush_fd0p l ⌝ -∗
       UkSh.ush_pstate N γp T Wc Wb Pm l -∗
       ushl_dat γd -∗ usz γs sz -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x914) (16 + (UkSh.ush_Dbody + n)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* [UkSh.ush_rest]'s opaque [R], AT THIS SHELL.  The re-cut left [R] a
     parameter precisely so that this line -- which mentions the parser's
     tables and the allocator's cells -- does not have to live in
     iris/UkSh.v.  The break rides with them: [usz] is not bytes, so it is
     not part of [ushl_dat], but a turn carries it all the same. *)
  Definition ushl_R (sz : Z) : iProp Σ := (ushl_dat γd ∗ usz γs sz)%I.

  (* ...and then [UkSh.ush_loop_head] AT that [R] IS [ushl_head]: the same
     four binders, the same budget ([UkSh.ush_Dbody]), and the two
     halves of [ushl_R] uncurried. *)
  (* ...AND THE PROMPT'S PAYMENT RIDES INSIDE THE PROCESS STATE (lane
     IO-LEAF, M6a(3), step 3): the era's credential is in [UkSh.ush_posb]'s
     slot beside the cursor, so this shell-level head -- which is what
     every arm of main's body discharges -- names nothing beyond the
     state. *)
  Lemma ushl_head_of_R (T : iProp Σ) (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) (sz : Z) :
    UkSh.ush_loop_head N γp T Wc Wb Pm (ushl_R sz) l -∗
    ushl_head T Wc Wb Pm l sz.
  Proof using .
    iIntros "H" (h m f n) "%Hregs %Hfd0 Hstd Hdat Hsz Hbuf Hrun".
    iApply ("H" $! h m f n with "[%//] [%//] Hstd [$Hdat $Hsz] Hbuf Hrun").
  Qed.


  (* ===================================================================== *)
  (* THE LOOP HEAD AT THE CREDENTIAL UNDER A LATER (design app-pipe        *)
  (* SS4.3o, route (a), the SECOND of the two generic additions) -- the    *)
  (* STATEMENT lands here and the DERIVATION is refuted (lane              *)
  (* SH-PIPE-ROUND-7, finding (1)).                                        *)
  (*                                                                       *)
  (* [ushl_head_later] is [ushl_head] with the process state -- and so the *)
  (* era's write credential inside it -- under a [▷].  It is what a caller *)
  (* that redeems its child's exit payload with the plain                  *)
  (* [ChildTok.gen_pay] at 0x914 would need, and SS4.3o rules it a generic *)
  (* addition over [UkRunLeaf.wp_uk_cmv_later].                            *)
  (*                                                                       *)
  (* IT IS NOT DERIVABLE FROM [ushl_head], and the reason is the head's    *)
  (* own first instruction.  A [▷] is strippable only at a later-providing *)
  (* step; the step available at 0x914 is [0x914 c.mv a1,s3] itself        *)
  (* ([UkRunLeaf.wp_uk_cmv_later]), and taking it CONSUMES the head's      *)
  (* first instruction and leaves the walk at 0x916, where [ushl_head] --  *)
  (* stated at [urun ... (mword_of_int 0x914) ...] -- no longer applies.   *)
  (* The loop offers no entry point at 0x916; [UkSh.wp_ksh_getcmd] is      *)
  (* reachable only with [UkSh.ush_read_leaf], which needs the era's       *)
  (* [ukn_pay N = ucons_pay ...] equation that [UkSh.ush_rest_l_at] does   *)
  (* not pass to a body law; and a walk that cannot re-enter cannot close. *)
  (* So the later has to be paid BEFORE 0x914 -- inside [wait], at         *)
  (* [0xc70 c.jr ra] ([UkShPipeWait.wp_kshr_wait_pid_later]) -- and this   *)
  (* definition stays as the record of what route (a) asked for.           *)
  (*                                                                       *)
  (* What IS true, and is all that is: the latered head is STRICTLY        *)
  (* STRONGER ([ushl_head_of_later] below).                                *)
  (* ===================================================================== *)
  Definition ushl_head_later (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) (sz : Z) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ UkSh.ush_regs m ⌝ -∗
       ⌜ UkSh.ush_fd0p l ⌝ -∗
       ▷ UkSh.ush_pstate N γp T Wc Wb Pm l -∗
       ushl_dat γd -∗ usz γs sz -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x914) (16 + (UkSh.ush_Dbody + n)) -∗
       mWP (Loop : expr riscv_lang))%I.

  Lemma ushl_head_of_later (T : iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ) (Pm : list (bv 8) -> iProp Σ)
      (l : list fdstate) (sz : Z) :
    ushl_head_later T Wc Wb Pm l sz -∗ ushl_head T Wc Wb Pm l sz.
  Proof using .
    iIntros "H" (h m f n) "%Hregs %Hfd0 Hstd Hdat Hsz Hbuf Hrun".
    iApply ("H" $! h m f n with "[%//] [%//] [Hstd] Hdat Hsz Hbuf Hrun").
    iNext. iExact "Hstd".
  Qed.

End UkShLoop.

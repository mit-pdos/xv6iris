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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UserBits.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun.
Require Import FdSlots UserFd.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShMalloc.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UkShLoop.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

  (* the DATA a turn of the loop needs and does not create.  [8208] is
     [freep] (0x2010) and [8328] is [base] (0x2088) -- the two literals
     [UkShMalloc.ushm_fresh] unfolds to. *)
  Definition ushl_dat : iProp Σ :=
    (ustr γd DfracDiscarded ushp_whitespace 5 ushp_ws_f ∗
     ustr γd DfracDiscarded ushp_symbols 7 ushp_sym_f ∗
     uword γd 8208 (mword_of_int 0) ∗
     (∃ fb : nat -> bv 8, ubytes γd 8328 16 fb))%I.

  Lemma ushl_fresh_of_dat (sz : Z) :
    ushl_dat -∗ usz γs sz -∗
      UkShMalloc.ushm_fresh γd γs sz ∗
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
       UkSh.ush_std γfd l -∗
       ushl_dat -∗ usz γs sz -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun γt γd γs γfd h m (mword_of_int 0x938) (16 + (80 + n)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* [UkSh.ush_rest]'s opaque [R], AT THIS SHELL.  The re-cut left [R] a
     parameter precisely so that this line -- which mentions the parser's
     tables and the allocator's cells -- does not have to live in
     iris/UkSh.v.  The break rides with them: [usz] is not bytes, so it is
     not part of [ushl_dat], but a turn carries it all the same. *)
  Definition ushl_R (sz : Z) : iProp Σ := (ushl_dat ∗ usz γs sz)%I.

  (* ...and then [UkSh.ush_loop_head] AT that [R] IS [ushl_head]: the same
     four binders, the same budget ([UkSh.ush_Dbody] is 80), and the two
     halves of [ushl_R] uncurried. *)
  Lemma ushl_head_of_R (l : list fdstate) (sz : Z) :
    UkSh.ush_loop_head γt γd γs γfd (ushl_R sz) l -∗ ushl_head l sz.
  Proof.
    iIntros "H" (h m f n) "%Hregs Hstd Hdat Hsz Hbuf Hrun".
    iApply ("H" $! h m f n with "[%//] Hstd [$Hdat $Hsz] Hbuf Hrun").
  Qed.

End UkShLoop.

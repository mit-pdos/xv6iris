(* LinkUartwrite.v -- the one place uartwrite's contract is ASSUMED.

   The fourth file of its kind (LinkPanic / LinkKerneltrap / LinkConsoleintr /
   LinkUserinit are the others).  Every other link file in the tree
   instantiates a proof functor against its callees' PROOFS; uartwrite has no
   proof yet, so this link supplies the interface with an [Axiom] instead.

   WHY IT IS ASSUMED, AND WHAT IS ALREADY DONE.  xv6 `ae96fd0` rewrote the
   transmit path (claude-notes/projects/uart-driver.md): the loop is now
   acquiresleep / { sleep_prepare; poll THRE; push or sleep } / releasesleep,
   which is a wholesale restructure of a ~1500-line proof rather than a
   replay.  The CONTRACT is written, compiling and believed right --
   SpecUartwrite.v, including the stack budget, which had to move from 32 to
   34 (an 8-slot frame over acquiresleep's 26, exactly tight) -- and so is the
   definitional layer of the proof.  What is missing is only the body:
   [uw_tail], [uw_one], [uw_iter], [wp_uartwrite_sconf] and the
   [Module UartwriteProof].

   Both the definitional layer and the intended real instantiation of this
   file are parked in `iris/wip/` (see `iris/wip/README.md`), out of
   `_CoqProject` so nothing they claim is ever counted.  The `PROOF PLAN`
   comment there carries the instruction table, the register roles, the
   frame-slot map and the per-callee premise lists, all checked against
   `kernel.asm`; read it before starting.  Proving uartwrite replaces this
   file with that one, and nothing else.

   A SECOND, INDEPENDENT GAP SITS UNDER THIS ONE, and it has SHRUNK but not
   closed.  The [is_txlock] this contract takes as a premise is still not
   derivable, and is assumed separately in LinkTxLockInit.v -- so that proving
   uartwrite and closing D2 retire independently, and neither hides the other.
     WHAT CHANGED: D2 was "upstream never initializes `tx_lock`", and xv6
   `b7c25cf` fixed exactly that, with `initsleeplock(&tx_lock, "uart")` in
   uartinit.  The proof side now carries the lock's storage end to end --
   `main_locks_raw` hands `sl_raw a_tx_lock` down through consoleinit to
   uartinit, which hands `sl_fresh a_tx_lock "uart"` back (ProofMain binds it
   as `Hslfresh`).
     WHAT REMAINS IS A DESIGN QUESTION, not a missing step: [sl_fresh_new]
   also wants the RESOURCE the lock is to own, and for [is_txlock] that is
   [UartTxInv.tx_res γd = ∃ l, uart_tx_own γd l].  main holds that token --
   and then gives it to printk's `pr.lock`, because
   [SpecPrintkGen.pr_res γd] contains [uart_tx_own] too.  The token is
   exclusive, so `tx_lock` and `pr.lock` cannot both own the transmitter.
   Deciding which one does is the standing tension in
   claude-notes/projects/uart-driver.md; until it is settled this axiom
   stays.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecUartwrite] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import WpLock FdSlots IrefSlots.
Require Import DiskPtsto WpUart.
Require Import SpecUartwrite.

Module Uartwrite : UARTWRITE.
  Axiom wp_uartwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool)
      (pidv : mword 32) (dqp : dfrac),
      wp_uartwrite_sconf_body γu γv γs j γlp γl m av eb C n f dq b pidv dqp.
End Uartwrite.

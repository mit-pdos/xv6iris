(* SpecBootDevCaps.v -- THE THREE BOOT CREDENTIALS NOBODY MINTS YET.

   [IntrDefs.intr_res] carries the handler contract, and that contract is a
   [□]: whatever kerneltrap's cone needs from its caller has to be closed over
   at the moment main FOLDS the resource ([SpecKernelvec]'s
   [devintr_caps] premise).  Of [devintr_caps]' eight members main holds five
   by then -- [dev_inv], [procs_inv], [panic_wp_any], the disk [is_lock] and
   [disk_geom].  The other three appear NOWHERE in the boot chain:

     is_txlock γtx γu   the UART transmit lock (uartinit creates it; main's
                        console-init group does not keep it)
     timer_cap          [sstc_enabled ∗ stimecmp_inv] (TimerCap.v): the sstc
                        pin plus the stimecmp invariant, both established from
                        M-mode cells that the boot bridge does not hand over
     tick_keeper γtl γs SpecClockintr's hart-indexed ticks-lock disjunction

   WHY THE DEBT ONLY BECAME VISIBLE NOW.  While kerneltrap was an [Axiom]
   nobody had to produce any of them: the handler contract said nothing about
   what the handler needs, so main folded [intr_res] out of a stvec cell and a
   ghost quarter alone.  With the real kerneltrap linked, the obligation is
   real -- and it is a BOOT obligation, not an interrupt-path one.

   WHERE IT SHOULD BE DISCHARGED: the whole-system adequacy composition
   (claude-notes/projects/main-boot.md's remaining item), beside the time-0
   device invariants it already has to mint.  Two of the three are ordinary
   time-0 allocations; [is_txlock] is uartinit's and wants that group to
   thread its lock out.  Nothing here is expected to stay.

   PERSISTENT, all three, which is what lets this be one flat entailment with
   no fupd and no ghost-name threading: the two names it introduces are
   existential.

   THIS FILE IS THE INTERFACE ONLY; [LinkBootDevCaps.v] supplies it with an
   [Axiom], and [ProofMain] / [ProofMainSecondary] take it as a functor
   parameter like any other callee contract -- so the day it is discharged for
   real, nothing above changes. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock FdSlots IrefSlots ProcGeom DiskPtsto WpUart.
Require Import SmodeCore TimerCap UartTxInv.
Require Import SchedCtx.
Require Import SpecClockintr.
Local Open Scope Z_scope.

Definition boot_dev_caps_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γu : uart_names) (γs : list gname) : iProp Σ :=
  (∃ γtx γtl : gname,
     is_txlock γtx γu ∗ timer_cap ∗ tick_keeper γtl γs)%I.

Module Type BOOT_DEV_CAPS.
  Parameter boot_dev_caps :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ}
      `{GEN : GenId} `{CID : CpuId} (γu : uart_names) (γs : list gname),
      ⊢ boot_dev_caps_body γu γs.
End BOOT_DEV_CAPS.

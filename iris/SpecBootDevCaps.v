(* SpecBootDevCaps.v -- THE THREE BOOT CREDENTIALS NOBODY MINTS YET.

   [IntrDefs.intr_res] carries the handler contract, and that contract is a
   [□]: whatever kerneltrap's cone needs from its caller has to be closed over
   at the moment main FOLDS the resource ([SpecKernelvec]'s
   [devintr_caps] premise).  Of [devintr_caps]' seven members main holds six
   by then -- [dev_inv], [procs_inv], [panic_wp_any], the disk [is_lock],
   [disk_geom] and [tick_keeper].  ONE appears nowhere in the boot chain:

     timer_cap          [sstc_enabled ∗ stimecmp_inv] (TimerCap.v).  This one
                        IS mechanical, and the pieces are all there:
                        [SpecEntry.wp_entry_boot]'s post already hands back
                        [mcounteren ↦ᵣ mcounterenf] and [stimecmp ↦ᵣ stimecmpf],
                        and [TimerCap.timer_cap_intro] turns them into the
                        credential.  What is missing is ONE pure conjunct in
                        that post -- [_get_Counteren_TM mcounterenf = '1'],
                        which timerinit provably wrote and whose proof
                        therefore already knows it (the same move the [mief =
                        MIE_S] conjunct beside it was added by) -- plus a
                        [timer_cap] allocation in the boot chain, which is the
                        right place because the credential is PERSISTENT and
                        every hart allocates its own from its own two cells

   IT USED TO BE THREE.  [is_txlock γtx γu] is DISCHARGED THE OTHER WAY: it was
   never mintable (its lock's name field is never written -- kernel-defects.md
   D2) and it is no longer WANTED, because ae96fd0's uartintr takes no lock at
   all.  It left [devintr_caps] with the rewrite of the UART transmit path, and
   with it went the [tx_busy] cell [SpecMain]'s bundle used to carry.

   [tick_keeper γtl γs] is DISCHARGED: the boot hart owes
   the real arm and pays it by bringing tickslock up itself (trapinit
   initialises the lock's words, [SpecMain]'s bundle now carries the [ticks]
   counter they protect, and [ProofMain]'s trap group runs [newlock]); a
   secondary hart owes only [tick_hart = false], which its [cid_word <> 0]
   premise gives outright.  Each remaining conjunct can go the same way,
   independently -- the statement is a flat [∗].

   WHY THE DEBT ONLY BECAME VISIBLE NOW.  While kerneltrap was an [Axiom]
   nobody had to produce any of them: the handler contract said nothing about
   what the handler needs, so main folded [intr_res] out of a stvec cell and a
   ghost quarter alone.  With the real kerneltrap linked, the obligation is
   real -- and it is a BOOT obligation, not an interrupt-path one.

   WHERE IT SHOULD BE DISCHARGED: the whole-system adequacy composition
   (claude-notes/projects/main-boot.md's remaining item), beside the time-0
   device invariants it already has to mint.  Nothing here is expected to stay.

   PERSISTENT, which is what lets this be one flat entailment with no fupd and
   no ghost-name threading.

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
Require Import WpLock FdSlots IrefSlots DiskPtsto WpUart.
Require Import SmodeCore TimerCap UartTxInv.
Require Import IrefSlots.
Local Open Scope Z_scope.

Definition boot_dev_caps_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γu : uart_names) : iProp Σ :=
  (timer_cap)%I.

Module Type BOOT_DEV_CAPS.
  Parameter boot_dev_caps :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ}
      `{GEN : GenId} `{CID : CpuId} (γu : uart_names),
      ⊢ boot_dev_caps_body γu.
End BOOT_DEV_CAPS.

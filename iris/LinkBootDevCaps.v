(* LinkBootDevCaps.v -- the three unminted boot credentials, ASSUMED.

   See SpecBootDevCaps.v for what they are, why nothing mints them yet, and
   where they belong (the whole-system adequacy composition).  This is the ONE
   assumption the interrupt path still rests on, and it is a BOOT obligation:
   the handler contract itself is axiom-free
   ([Print Assumptions Kernelvec.kernelvec_handler_spec] is the 5 platform
   axioms + funext + consoleintr).

   Written out with an explicit [Axiom] rather than a [Declare Module]: both are
   visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock FdSlots IrefSlots ProcGeom DiskPtsto WpUart.
Require Import SmodeCore TimerCap UartTxInv.
Require Import SchedCtx SpecClockintr.
Require Import SpecBootDevCaps.
Local Open Scope Z_scope.

Module BootDevCaps : BOOT_DEV_CAPS.
  Axiom boot_dev_caps :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ}
      `{GEN : GenId} `{CID : CpuId} (γu : uart_names) (γs : list gname),
      ⊢ boot_dev_caps_body γu γs.
End BootDevCaps.

(* ===================================================================== *)
(* SpecUser.v -- THE PUBLIC INTERFACE of arbitrary user-mode execution,    *)
(* stated independently of its proof.                                      *)
(*                                                                         *)
(* This is the one thing a CALLER of the user-mode development needs: the  *)
(* machine may run WHATEVER user code the mapped pages hold, forever, and  *)
(* the only exit is a trap into the kernel handler at stvec.  Everything   *)
(* else in the User*.v tower (the step engine, the five-way outcome        *)
(* classification, the decode/execute totalities, the 19 memory arms) is   *)
(* how that is proved, not what it says -- and lives behind the seal of    *)
(* [Module Type USER] (proved in ProofUser.v).                             *)
(*                                                                         *)
(* The contract, in the order the wands take it:                           *)
(*                                                                         *)
(*   [hw_config]     the platform constants (PMP/PMA/CLINT/... geometry).  *)
(*   [minstret_inv]  the ambient minstret invariant every step tower needs.*)
(*   [wire_inv]      the SHARED interrupt-wire invariant (WireInv.v): the  *)
(*                   external-interrupt wires are written concurrently by  *)
(*                   the device loop, so a user arm may only BORROW them   *)
(*                   across a step, never own them.  Interrupts are        *)
(*                   unmaskable at User, so this is not optional.          *)
(*   [user_inv C pt] the loop invariant: a valid User machine -- privilege *)
(*                   User, ARBITRARY pc / registers / trap CSRs, over the  *)
(*                   user page-table bundle [pt] (every mapped page owned  *)
(*                   with EXISTENTIAL contents) and the loop-constant boot *)
(*                   config [C].  Produced at boot / after userret by      *)
(*                   [UserKernelBridge.userret_to_user_inv].               *)
(*   [stvec_handler_wp C pt]                                             *)
(*                   the kernel re-entry contract: from [user_trap_frame]  *)
(*                   (Supervisor, pc at stvec's direct base, trap CSRs     *)
(*                   written, the same page table and config) the kernel   *)
(*                   handler runs safely.  Still ASSUMED by every caller;  *)
(*                   uservec's own proof (E-uservec) is what will discharge*)
(*                   it.  Taken UNDER A LATER: the trap frame reaches the  *)
(*                   handler only through the step obligation, whose       *)
(*                   continuations are already under a `▷`, and a caller   *)
(*                   closing the trap loop has its Löb hypothesis for the  *)
(*                   next round only under one.                            *)
(*                                                                         *)
(* There are NO totality hypotheses: the base and compressed execute       *)
(* totalities are discharged inside the proof, so this WP is closed.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv WireInv.
Require Import UserPtTree UserExec.
Local Open Scope Z_scope.
Import Defs.

Definition wp_user_exec_closed_body `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
    (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) :=
  hw_config -∗ minstret_inv -∗ wire_inv -∗
  user_inv C pt Rut -∗ ▷ stvec_handler_wp C pt Rut -∗
  WP (Loop : expr riscv_lang).

Module Type USER.
  Parameter wp_user_exec_closed :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ),
      wp_user_exec_closed_body C pt Rut.
End USER.

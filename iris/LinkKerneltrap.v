(* LinkKerneltrap.v -- kerneltrap's interface, instantiated.

   [Kerneltrap] is a THEOREM: [KerneltrapProof] applied to its three callees'
   proofs, so [Kerneltrap.wp_kerneltrap_sconf] assumes nothing.

   THE LEGACY ROUND-TRIP CONTRACT IS GONE.  [KerneltrapRet] used to live here,
   supplied with an [Axiom], because ProofKernelvec.v was a functor over
   [KERNELTRAP_RETURNS] -- the handler contract did not hand the handler the
   trap CSRs, the per-cpu bookkeeping, a deep enough stack carve or a
   hart-generic Loeb, so kernelvec could not consume the real thing.  It can
   now (claude-notes/projects/kerneltrap.md step 10), and with it the last
   assumption in the interrupt cone is retired. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import ProofKerneltrap.
Require Import LinkDevintr LinkMyproc LinkYield.

(* THE REAL THING: a theorem, over its callees' proofs. *)
Module Kerneltrap := KerneltrapProof Devintr Myproc Yield.

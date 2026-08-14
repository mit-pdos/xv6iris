(* LinkMainSecondary.v -- seals main's secondary-hart proof against its
   callees' links.  printk-general is still an ASSUMED contract (an Axiom in
   LinkPrintk), exactly as for the boot arm. *)
Require Import LinkCpuid LinkPrintk LinkKvminithart LinkTrapinithart.
Require Import LinkPlicinithart LinkScheduler LinkKernelvec.
Require Import ProofMainSecondary.

Module MainSecondary :=
  MainSecondaryProof Cpuid PrintkGen Kvminithart Trapinithart Plicinithart
                     Scheduler Kernelvec.

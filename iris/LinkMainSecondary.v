(* LinkMainSecondary.v -- seals main's secondary-hart proof against its
   callees' links.  printk-general is still an ASSUMED contract (an Axiom in
   LinkPrintkGen), exactly as for the boot arm. *)
Require Import LinkCpuid LinkPrintkGen LinkKvminithart LinkTrapinithart.
Require Import LinkPlicinithart LinkScheduler LinkKernelvec.
Require Import LinkBootDevCaps.
Require Import ProofMainSecondary.

Module MainSecondary :=
  MainSecondaryProof Cpuid PrintkGen Kvminithart Trapinithart Plicinithart
                     Scheduler Kernelvec BootDevCaps.

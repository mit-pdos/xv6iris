(* LinkMain.v -- the one place main's proof meets its callees' proofs.

   Nineteen functor arguments: the eighteen functions main calls, plus
   KERNELVEC (whose handler contract is what turns trapinithart's [stvec ↦ᵣ
   kernelvec] into the [intr_res] the scheduler consumes).  Three of
   the callee links are still ASSUMED contracts (an [Axiom] inside their own
   sealed module -- printk's general path, userinit, virtio_disk_init), which is
   exactly the axiom footprint [tools/proof_coverage.py] reports for main.

   The twentieth argument is not a function: [BOOT_DEV_CAPS] is the three
   persistent credentials kerneltrap's cone needs and nothing in the boot chain
   mints yet (SpecBootDevCaps.v), assumed in LinkBootDevCaps.v. *)
Require Import LinkCpuid LinkConsoleinit LinkPrintkinit LinkPrintkGen.
Require Import LinkKinit LinkKvminit LinkKvminithart LinkProcinit.
Require Import LinkTrapinit LinkTrapinithart LinkPlicinit LinkPlicinithart.
Require Import LinkBinit LinkIinit LinkFileinit LinkVirtioDiskInit.
Require Import LinkUserinit LinkScheduler LinkKernelvec.
Require Import LinkBootDevCaps.
Require Import ProofMain.

Module Main :=
  MainProof Cpuid Consoleinit Printkinit PrintkGen Kinit Kvminit Kvminithart
            Procinit Trapinit Trapinithart Plicinit Plicinithart Binit Iinit
            Fileinit VirtioDiskInit Userinit Scheduler Kernelvec
            BootDevCaps.

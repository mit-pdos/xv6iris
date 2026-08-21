(* LinkForkretPark.v -- the one place [forkret_park] is ASSUMED, in the form
   [ProofKfork.v] uses.  See SpecForkretPark.v's header for why: it is a
   real, pre-existing gap, not a shortcut invented for kfork.

   WHAT IS STILL MISSING IS NO LONGER THE ARGUMENT ABOUT [forkret].  That is
   [ProofForkretPark.v] -- the same park, PROVED, at one further precondition
   ([SpecForkretParkPaid.forkret_park_pkg]: the child's free kernel stack and
   the closer that builds the trap loop's kernel-side bundle for it).  This
   Axiom survives because kfork cannot pay that precondition, which is a
   question about a fresh process's half of the kernel environment.  Written
   with an explicit [Axiom] rather than a [Declare Module] for the same
   reason [LinkIput.v] is: [Print Assumptions] sees either, but only the
   [Axiom] keyword is visible to [tools/proof_coverage.py]'s textual scan. *)
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import FileInvDefs.
Require Import SpecForkretPark.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Module ForkretPark : FORKRET_PARK.
  Axiom forkret_park :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname)
      (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate),
      forkret_park_body γs γf pa ks rest pid V.
End ForkretPark.

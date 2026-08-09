(* LinkForkretPark.v -- the one place [forkret_park] is ASSUMED.  See
   SpecForkretPark.v's header for why: it is a real, pre-existing gap
   (turning a fresh process's raw saved context into a member of the
   scheduler's swtch chain needs a Löb argument about [forkret] that nothing
   in this tree has written), not a shortcut invented for kfork.  Written
   with an explicit [Axiom] rather than a [Declare Module] for the same
   reason [LinkIput.v] is: [Print Assumptions] sees either, but only the
   [Axiom] keyword is visible to [tools/proof_coverage.py]'s textual scan. *)
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import WpLock.
Require Import FdSlots FileInv ProcInv.
Require Import SpecForkretPark.

Module ForkretPark : FORKRET_PARK.
  Axiom forkret_park :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname)
      (γf : gname) (pa ks : mword 64) (rest : list (mword 64))
      (pid : mword 32) (V : pprivate),
      forkret_park_body γs γf pa ks rest pid V.
End ForkretPark.

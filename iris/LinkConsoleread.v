(* LinkConsoleread.v -- the one place consoleread's contract is ASSUMED.

   The third file of its kind (LinkKerneltrap.v and LinkConsoleintr.v are the
   others).  Every other link file in the tree instantiates a proof functor
   against its callees' PROOFS; consoleread has none, so this link supplies
   the interface with an [Axiom] instead -- the single assumption the fileread
   cone rests on ([tools/proof_coverage.py] reports it as such).  Isolating it
   here means [ProofFileread.v] itself is axiom-free: it is a functor over
   [CONSOLEREAD], and proving consoleread later replaces this file, nothing
   else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.

   What the assumption does and does not say: see SpecConsoleread.v -- in
   particular, it is silent about the console's ring buffer, which is what
   the (also assumed) consoleintr fills. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import FdSlots WpLock.
Require Import KallocInv.
Require Import FileInv ProcInv.
Require Import SpecConsoleread.

Module Consoleread : CONSOLEREAD.
  Axiom wp_consoleread_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool),
      wp_consoleread_sconf_body γa γf γs j γlp m av eb C pid V n b.
End Consoleread.

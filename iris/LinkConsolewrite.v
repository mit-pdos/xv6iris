(* LinkConsolewrite.v -- the one place consolewrite's contract is ASSUMED.

   The fourth file of its kind (LinkKerneltrap.v, LinkConsoleintr.v and
   LinkConsoleread.v are the others), and the write side's exact twin of the
   third.  Every other link file in the tree instantiates a proof functor
   against its callees' PROOFS; consolewrite has none, so this link supplies
   the interface with an [Axiom] instead -- the single assumption the
   filewrite cone rests on ([tools/proof_coverage.py] reports it as such).
   Isolating it here means [ProofFilewrite.v] itself is axiom-free: it is a
   functor over [CONSOLEWRITE], and proving consolewrite later replaces this
   file, nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.

   What the assumption does and does not say: see SpecConsolewrite.v -- in
   particular, it is silent about the uart's transmit ring, which is a
   strictly larger elision than the console ring buffer LinkConsoleread
   already elides. *)
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
Require Import SpecConsolewrite.

Module Consolewrite : CONSOLEWRITE.
  Axiom wp_consolewrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ, !kallocG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (n : Z) (b : bool),
      wp_consolewrite_sconf_body γa γf γs j γlp m av eb C pid V n b.
End Consolewrite.

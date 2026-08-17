(* LinkCreateFreshTy.v -- the one place [create_fresh_ty] is ASSUMED.

   READ [SpecCreateFreshTy.v]'s header before this file.  In one line: at
   create's [ilock(ip)], on the inode its own [ialloc] just claimed, the
   record the fill returns is the record the claim wrote.  fs-icache.md
   §20.17.6 refutes deriving it twice and independently -- licence (d) has
   no source ([ireg_claim_au] pays out [True]), and [ireg_withdraw]'s wall
   is untouched by the 9da28f5 guards -- so it is TRUE of the fixed binary
   and UNDISCHARGED, which is [SpecForkretPark]'s situation exactly.

   THE STATEMENT IS A SPAN AND NOT A FACT, AND THAT IS LOAD-BEARING.  A
   one-line gate concluding [di_type dn = ty] over free [ty] and [dn] is
   INCONSISTENT -- two instantiations at different types derive [False],
   and an axiom that proves [False] defeats every [Print Assumptions] in
   the tree.  The provenance has to come from the machine word in s4, so
   the assumed statement contains the [jal ialloc] that reads it.  Four
   instructions; create proves the other 158.

   IT HIDES NEITHER CALLEE: [wp_ialloc_gen] and [wp_ilock_sconf] are
   HYPOTHESES of the parameter, supplied by [ProofCreate] from its own
   functor arguments, so a wrong [ProofIalloc] or [ProofIlock] is not
   covered.  And [fresh_shape dn] is not assumed -- [InodeRegion.
   ireg_withdraw] proves it and D₀ increment 1 made [SpecIlock] expose it.

   Written with an explicit [Axiom] rather than a [Declare Module] for the
   reason [LinkForkretPark.v] and [LinkIput.v] give: [Print Assumptions]
   sees either, but only the [Axiom] keyword is visible to
   [tools/proof_coverage.py]'s textual scan -- which is what puts create's
   '!' marker in the coverage report, where it belongs. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock.
Require Import FdSlots.
Require Import IcacheRef.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import InodeRegion.
Require Import IrefSlots IcacheRef IcacheEscrow.
Require Import SpecCreateFreshTy.
Require Import ProcAvail.

Module CreateFreshTy : CREATE_FRESH_TY.
  Axiom create_fresh_ty :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             ICFG : icfg, !icacheG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (kd : nat) (dqp : dfrac)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (Ma : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      create_fresh_ty_body kt γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty kd dqp
                           u Sb pidv dq dqs dqn Ma K eb b lks.
End CreateFreshTy.

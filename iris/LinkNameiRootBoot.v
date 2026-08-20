(* LinkNameiRootBoot.v -- the one place the boot cone ASSUMES anything.

   [SpecNameiRootBoot.v]'s header is the inventory: this [Axiom] says
   [namei("/")] behaves, given everything the boot client can actually
   produce, and it assumes over the PROVEN corner
   ([LinkNameiRoot.NameiRoot], which discharges [SpecNamei.NAMEI_ROOT])
   exactly four persistent rows -- the itable lock, the [ref]-word
   invariant, the fifty escrows and the inode region.  They are [SpecIget]'s
   premises, forwarded unchanged by namex's root corner and namei's, and
   they do not exist at boot yet because [IcacheBoot.icache_boot] wants the
   stocked inode pool (fs-icache.md C7 owed (ii)/(c)).

   THIS REPLACED [LinkUserinit]'s AXIOM, which assumed userinit's WHOLE
   BODY -- allocproc, the [initproc] store, namei, the RUNNABLE park and the
   release.  All of that is now proven ([ProofUserinit.v]); what is left
   assumed is one call, at premises that are four persistent conjuncts short
   of a contract the tree already proves.

   DISCHARGING IT IS A FUNCTOR APPLICATION, not a proof: when main holds the
   four rows, this file becomes [Module NameiRootBoot := <adapter>
   LinkNameiRoot.NameiRoot] and nothing about [ProofUserinit.v] changes.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecNameiRootBoot] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import IrefSlots IcacheRef.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import SpecNameiRootBoot.

Module NameiRootBoot : NAMEI_ROOT_BOOT.
  Axiom wp_namei_root_boot :
    forall `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (dqp : dfrac)
      (m : regfile) (n K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string),
      wp_namei_root_boot_body dqp m n K eb p b lks.
End NameiRootBoot.

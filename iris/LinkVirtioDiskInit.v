(* LinkVirtioDiskInit.v -- the one place virtio_disk_init's contract is ASSUMED.

   virtio_disk_init WAS proven, over the raw [virtio_frag] half
   (ProofVirtioDiskInit.v, a functor over [INITLOCK], [KALLOC] and [MEMSET],
   which this link instantiated).  [SpecVirtioDiskInit] is now stated over
   [WpUart.disk_inv] plus the config tracker -- the disk thread must refute
   [DevStepDiskWild] at every step, so no CPU precondition may hold the
   fragment raw -- and the proof is being re-worked over the invariant-opening
   ACCESSOR-form virtio MMIO leaves, with the DMA lease paid in at the final
   STATUS write.  Until then the interface is supplied by an [Axiom], the way
   [LinkKerneltrap.v] does for kerneltrap, which keeps [ProofMain.v] a functor
   over [VIRTIODISKINIT] and axiom-free.  The deleted proof script is in git
   history -- see claude-notes/projects/main-boot.md, G1.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith String.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecVirtioDiskInit] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import WpLock KallocInv DiskPtsto VirtioModel.
Require Import SpecVirtioDiskInit.

Module VirtioDiskInit : VIRTIODISKINIT.
  Axiom wp_virtio_disk_init_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !diskGhostG Σ}
      `{CID : CpuId}
      (γ : gname) (γv : disk_names) (γa : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (K : nat)
      (eb : bool) (pp : mword 64) (C : iProp Σ) (on : option nat)
      (c0 : virtio_cfg) (vlock : bv 32) (vname vcpu : bv 64)
      (pd0 pav0 pu0 : mword 64) (free0 : nat -> bv 8),
      wp_virtio_disk_init_sconf_body γ γv γa Φ m K eb pp C on c0 vlock vname vcpu
                                     pd0 pav0 pu0 free0.
End VirtioDiskInit.

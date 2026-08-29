(* BioFs.v -- the bio handle AT THE FS INSTANTIATION: shared accessors.

   [BioInv] is deliberately FS-agnostic (its payloads [Ψc]/[Ψd] are opaque
   parameters), and [FsBlocks] knows nothing about buffers -- so a lemma
   about [bio_held bn (fs_view γfs γd dev cov) ...] has no home in either.
   It used to have FOUR: [ProofIupdate.iu_held_L], [ProofIlock.il_held_L],
   [ProofBfree.bf_held_L] and [ProofBalloc.ba_held_L], verbatim copies,
   because each proof file is sealed in its own module and importing a
   proof file from a proof file is exactly what the spec-module discipline
   forbids.  This leaf is the one copy.

   [bio_held_fs_L] pulls the block's MACHINERY half of the logged view out
   of the handle's payload and gives it back -- the shape every
   invariant-parked reader wants ([InodeRegion.ireg_read],
   [BitmapInv.bitmap_read]/[bitmap_read_own]): the half in hand pins the
   parked bytes by [ghost_map_elem_agree], and everything returns.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks.
Require Import Riscv.rv64d_types.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.

Section BioFs.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  Lemma bio_held_fs_L (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (kb : nat) (pidv dv bno : mword 32)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn (fs_view γfs γd dev cov) kb pidv dv bno bs bsl bsd d -∗
      (uint bno ↪[fs_cache γfs]{#(1/2)} bsl) ∗
      ((uint bno ↪[fs_cache γfs]{#(1/2)} bsl) -∗
       bio_held bn (fs_view γfs γd dev cov) kb pidv dv bno bs bsl bsd d).
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "(%A & %B & %C & H1 & H3 & H4 & H5 & H6 & Hpay)".
    destruct d.
    - rewrite /fs_mdirty. iDestruct "Hpay" as "[[HL HD] Hq]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H3 H4 H5 H6". iFrame "HL HD Hq".
    - rewrite /fs_mclean. iDestruct "Hpay" as "[[HL HD] %He]".
      iFrame "HL". iIntros "HL".
      iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
      iFrame "H1 H3 H4 H5 H6". iFrame "HL HD". done.
  Qed.

End BioFs.

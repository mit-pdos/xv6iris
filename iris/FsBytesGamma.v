(* FsBytesGamma.v -- THE ONE BRIDGE between the block layer's concrete byte
   map and the abstract view record every stage-2 file-system predicate is
   stated over.

   [FsStateDefs.fs_view_names] is a record whose only disk-facing field is
   [fsΦ], an ABSTRACT byte-address-keyed points-to (fs-state.md section 1).
   The file system is instantiated twice over it; this file supplies the
   LOGGED instance's [fsΦ], namely the FULL element of the era's byte view
   [FsBlocks.fs_bytes] --

     fsΦ (fs_gamma_L γfs) a v  :=  a ↪[fs_bytes γfs] v

   -- together with the two properties of it that consumers need and cannot
   prove of an abstract predicate ([phi_excl], [GTimeless]), and the two
   equations that identify the abstract runs with the concrete ones.

   THE EQUATIONS HOLD BY CONVERSION, NOT BY NAME.  [FsStateDefs.byte_range]
   multiplies by [FsImg.BSIZE_z], [FsBlocks.byte_range] by [FsBlocks.BSZ];
   both delta-reduce to 1024, so the two runs are convertible and the
   lemmas below are [reflexivity].  A [rewrite] between the two spellings
   will NOT fire (fs-state.md section 7, last bullet), which is exactly why
   these are stated once, here, and never re-derived at a use site.

   THE LINK AND TOP GNAMES COME OUT OF [fs_names] (durable-disk 2b-A / B3).
   [fs_gamma_L] reads [FsBlocks.fs_link] and [FsBlocks.fs_top], the two
   fields [FsBoot.fs_boot_ghosts] allocates for the era; there is no
   placeholder left.  Nothing stated over the byte view ALONE reads them --
   [FsStateBitmap.free_bitmap_at], which is the whole of the bitmap's
   in-memory owner, does not, and [free_bitmap_at_gname] is that fact -- so
   the bitmap's predicate is unchanged by their arrival. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import Xv6Cameras.
Require Import FsBlocks.
Require Export FsStateDefs.

Local Open Scope Z_scope.

Section Bridge.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  Definition fs_gamma_L (γfs : fs_names) : fs_view_names Σ :=
    MkFsView (fun (a : Z) (v : bv 8) => (a ↪[fs_bytes γfs] v)%I)
             (fs_link γfs) (fs_top γfs).

  (* two owners of one byte is [False] -- the concrete instance of
     [FsStateDefs.phi_excl], and the only exclusivity law the design ever
     invokes (fs-state.md section 0). *)
  Lemma fs_gamma_L_excl (γfs : fs_names) : phi_excl (fs_gamma_L γfs).
  Proof.
    intros a v w. rewrite /fs_gamma_L /phi_excl /=.
    iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  Global Instance fs_gamma_L_timeless (γfs : fs_names) :
    GTimeless (fs_gamma_L γfs).
  Proof. intros a v. rewrite /fs_gamma_L /=. apply _. Qed.

  (* ---- the two equations ------------------------------------------- *)

  Lemma gamma_byte_range (γfs : fs_names) (b off : Z) (bs : list (bv 8)) :
    FsStateDefs.byte_range (fs_gamma_L γfs) b off bs
    ⊣⊢ FsBlocks.byte_range (fs_bytes γfs) b off bs.
  Proof.
    rewrite /FsStateDefs.byte_range /FsBlocks.byte_range /fs_gamma_L /=.
    reflexivity.
  Qed.

  Lemma gamma_blk_owned (γfs : fs_names) (b : Z) (bs : list (bv 8)) :
    blk_owned (fs_gamma_L γfs) b bs ⊣⊢ fsblock (fs_bytes γfs) b bs.
  Proof.
    rewrite /blk_owned /fsblock gamma_byte_range. reflexivity.
  Qed.

End Bridge.

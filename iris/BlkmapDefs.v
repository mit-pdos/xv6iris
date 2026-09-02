(* BlkmapDefs.v -- the pure block-map record, split out of InodeInv.v so the
   camera bundle (Xv6Cameras §15) can name the icache box's shape type
   [ic_x] (IcLoaded g dn bm) without importing the inode theory.  InodeInv
   re-exports it; nothing else changes. *)
From stdpp Require Import base bitvector.definitions.

Record blkmap := MkBlkmap {
  bm_dir : list (bv 32);   (* the NDIRECT direct entries; 0 = unallocated *)
  bm_ind : bv 32;          (* the indirect block itself;  0 = none        *)
  bm_ent : list (bv 32);   (* the NINDIRECT entries of that block         *)
}.

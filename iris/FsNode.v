(* FsNode.v -- THE ERA'S INODE NODE, AS A TYPE AND NOTHING ELSE.

   [fs_node] is fs-state.md section 2's inode: the on-disk record, the
   indirect block's entry array, and the contents of every slot the inode
   owns.  Its THEORY -- the readings [fn_type] / [fn_data] /
   [dir_entries] ..., the local clauses, the ownership predicates -- is
   [FsStateInode.v]'s and stays there; this file holds the record alone.

   WHY IT IS DOWN HERE.  Since durable-disk 2b-inode-3 the era's top map is
   a ghost the ICACHE's payload carries ([IcacheEscrow.ic_loaded] holds
   [FsState.top_frag]), so its capacity class [fsTopG] reaches
   [ProcInv.proc_priv] through [FirstTok.first_boot_persist] and from there
   essentially the whole kernel.  A class in that position has to be an
   [Xv6G.xv6G] MEMBER -- the alternative is an explicit binder in ~400 files
   -- and a member class lives in [Xv6Cameras.v], which may only name TYPES.
   [Xv6Cameras.v] already requires [DinodeEnc] for [dinode]; this file adds
   exactly the one record on top of it, so the bundle's cone grows by a
   single leaf and nothing of the [FsState*] stack moves below it.

   A camera is a type-level claim, so it belongs at the bottom
   (durable-notes, "ONE BUNDLE PER GHOST CLASS"); this file is that rule
   applied to the one type the top map's camera is over. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import DinodeEnc.

Local Open Scope Z_scope.

Record fs_node := MkNode {
  fn_rec : dinode;                    (* the 64-byte on-disk record        *)
  fn_ent : list (bv 32);              (* the indirect block's entry array  *)
  fn_blk : gmap nat (list (bv 8));    (* slot |-> block contents           *)
}.

Global Instance fs_node_inhabited : Inhabited fs_node :=
  populate (MkNode inhabitant [] ∅).

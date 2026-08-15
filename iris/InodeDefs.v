(* InodeDefs.v -- pure inode vocabulary usable without the inode invariant. *)
From Stdlib Require Import List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Values.
Require Import BioDefs.  (* [BSIZE] *)

(* The flat byte view of block-indexed file contents. *)
Definition file_byte (data : nat -> list (bv 8)) (k : nat) : bv 8 :=
  data (k `div` BSIZE)%nat !!! (k `mod` BSIZE)%nat.

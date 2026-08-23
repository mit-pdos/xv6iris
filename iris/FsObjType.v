(* ====================================================================== *)
(* FsObjType.v -- [fsobj], the durable-disk OBJECT NAME, and nothing else.  *)
(*                                                                         *)
(* WHY THIS FILE EXISTS (durable-disk flip-C1).  The log's ledger entry     *)
(* ([Xv6Cameras.op_entry]) carries the set of objects an open transaction   *)
(* has claimed, so [gset fsobj] is a CAMERA-side type: it has to be in      *)
(* scope where the [ghost_mapG] class that stores the ledger is declared.   *)
(* [Xv6Cameras.v] deliberately sits on three shallow imports (its own       *)
(* header explains what an eighty-two-file cone there cost), and the        *)
(* object THEORY -- [FsObj.v] -- sits on [FsWf], i.e. on the whole pure     *)
(* file-system band.  Requiring [FsObj] from [Xv6Cameras] would drag that   *)
(* band under all 767 files that bind the ghost bundle, so the ordering is  *)
(* inverted the only way that costs nothing: the four-constructor           *)
(* INDUCTIVE and its [Countable] instance move down here, where the file's  *)
(* whole cone is [ZArith] plus stdpp's [countable].                         *)
(*                                                                         *)
(* This is the same shape [Xv6Cameras] already uses for [DinodeEnc.dinode]  *)
(* and [VirtioQueue.vslot]: the TYPE lives in a shallow file, the theory    *)
(* stated over it lives in the subsystem's own.  [FsObj.v] Require-Exports  *)
(* this file, so every consumer of the object layer still sees [fsobj] and  *)
(* its constructors by importing [FsObj] alone -- nothing downstream        *)
(* changed its import line.                                                 *)
(*                                                                         *)
(* THE ADDRESSING DECISIONS (why [ORec] is by BLOCK, why [OBlk] is a mask,  *)
(* and how the four constructors tile a home block) are documented at       *)
(* [FsObj.v]'s header, where the agreement relation that reads them lives.  *)
(* ====================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import base countable.

Local Open Scope Z_scope.

(* The four sharing granularities of the resource layer, as one type:
   dir/data records ([dv] slots and file payloads), bitmap bits (the free
   pool), dinode slots ([ireg]), and whole blocks. *)
Inductive fsobj :=
| ORec (b : Z) (k : nat)   (* bytes [16k, 16k+16) of block [b]           *)
| OBit (b : Z)             (* the allocation bit OF block number [b]     *)
| OSlot (i : Z)            (* dinode record of inum [i]                  *)
| OBlk (b : Z).            (* all of block [b] (a MASK, see FsObj.v)     *)

Global Instance fsobj_eq_dec : EqDecision fsobj.
Proof. solve_decision. Defined.

Definition fsobj_enc (o : fsobj) : Z * nat + Z + Z + Z :=
  match o with
  | ORec b k => inl (inl (inl (b, k)))
  | OBit b => inl (inl (inr b))
  | OSlot i => inl (inr i)
  | OBlk b => inr b
  end.

Definition fsobj_dec (c : Z * nat + Z + Z + Z) : fsobj :=
  match c with
  | inl (inl (inl (b, k))) => ORec b k
  | inl (inl (inr b)) => OBit b
  | inl (inr i) => OSlot i
  | inr b => OBlk b
  end.

Lemma fsobj_dec_enc (o : fsobj) : fsobj_dec (fsobj_enc o) = o.
Proof. by destruct o. Qed.

Global Instance fsobj_countable : Countable fsobj :=
  inj_countable' fsobj_enc fsobj_dec fsobj_dec_enc.

(* SpecSysWriteAU.v -- THE WRITE DELTA'S PURE VOCABULARY: the chunk
   constant, the per-chunk side conditions, the chained reading and the
   instant-count bound.  A LEAF: pure Coq, no [iProp], no [Module Type],
   no contract.

   WHY THE WRITE'S CONSTANTS LIVE IN A LEAF OF THEIR OWN.  Both the
   INVARIANT layer ([FsAbsWriteFire.v], the fire point) and the CONTRACT
   ([SpecFilewrite.v]) need [FW_MAX] and [wchunks], and a spec file may not
   own a definition the invariant layer needs
   (design/code-organization.md), so they sit here, below both.  [FW_MAX]'s
   derivation from the log's budget stays in [SpecFilewrite.fw_max_value],
   where [MAXOPBLOCKS] is in scope.

   sys_write itself has ONE contract, [SpecSysWrite.SYSWRITE], whose arms
   are keyed on the descriptor's state; the abstract commits it is stated
   over are [FsAbsWriteFire]'s, at the γtop AUTHORITY (an [FsAbs.astate]-
   shaped commit is not dischargeable in either phase -- that file's header
   is the argument).

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-4
   (the sys_write paragraph of section 4). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
(* the proofmode, for ssreflect's [rewrite /x] -- the pure proofs below are
   written in it, and it is not transitive *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import BioDefs.        (* [BSIZE]                                   *)
Require Import InodeInv.       (* [MAXFILE]                                 *)
Require Import FsBlocks.       (* [blk_splice]: the landed byte splice      *)
Require Import FsAbs.          (* the abstract state (lane A, landed)       *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE CHUNK SIZE                                                    *)
(* ===================================================================== *)

(* THE CHUNK SIZE, as the two [lui]/[addi] pairs at filewrite+0x42..+0x4e
   materialise it: ((MAXOPBLOCKS-1-1-2)/2)*BSIZE with MAXOPBLOCKS = 10 and
   BSIZE = 1024.  The equation with the log's budget is
   [SpecFilewrite.fw_max_value]; this file only needs the value. *)
Definition FW_MAX : Z := 3072.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS ALGEBRA (PURE)                                  *)
(* ===================================================================== *)

Require Export FsAbsDelta.   (* the splice algebra, [delta_write] + its row algebra (hoisted 2026-09-04) *)

(* THE SIDE CONDITIONS a fired chunk's caller may assume at its instant,
   each realized by a writei guard (header, prover item 5): the row is a
   file, the chunk wrote something, the start is inside the current bytes
   (writei refuses past-size starts, so the splice never leaves a hole),
   and the end is inside the file-size cap. *)
Definition wri_pre (av : aview) (i : Z) (off : nat)
    (bs bs0 : list (bv 8)) (nl : nat) : Prop :=
  (* on the COUNT ([FsAbsDefs.arow_at], E2-V2): a write through the fd of
     an unlinked file finds no row, and moves none *)
  arow_at av i (MkAnode (AFile bs0) nl)
  /\ (0 < length bs)%nat
  /\ (off <= length bs0)%nat
  /\ (off + length bs <= MAXFILE * BSIZE)%nat.

(* ---------------------------------------------------------------------
   1b.  THE INSTANT-COUNT BOUND

   Every chunk that CONTINUES the loop wrote exactly
   [min (n - i) FW_MAX] bytes, so at most [⌈n / FW_MAX⌉] instants fire
   (the last possibly short).  [wchunks] is that ceiling; it sizes the
   commit bundle.  [wchunks_covers] is the non-vacuity fact -- the bundle
   is big enough for the count -- and [wchunks_nonpos] the degenerate
   arms' (nothing to hand in when the count is not positive).
   --------------------------------------------------------------------- *)

Definition wchunks (n : Z) : nat := Z.to_nat ((n + FW_MAX - 1) / FW_MAX).

Lemma wchunks_covers (n : Z) :
  0 <= n -> n <= FW_MAX * Z.of_nat (wchunks n).
Proof.
  intros Hn. rewrite /wchunks Z2Nat.id.
  - assert (Hdm := Z.div_mod (n + FW_MAX - 1) FW_MAX).
    assert (Hmb := Z.mod_pos_bound (n + FW_MAX - 1) FW_MAX).
    rewrite /FW_MAX in Hdm Hmb *.
    specialize (Hdm ltac:(lia)). specialize (Hmb ltac:(lia)). lia.
  - apply Z.div_pos; rewrite /FW_MAX; lia.
Qed.

Lemma wchunks_nonpos (n : Z) : n <= 0 -> wchunks n = 0%nat.
Proof.
  intros Hn. rewrite /wchunks.
  assert (Hlt : (n + FW_MAX - 1) / FW_MAX < 1).
  { apply Z.div_lt_upper_bound; rewrite /FW_MAX; lia. }
  apply Z2Nat.nonpos. lia.
Qed.

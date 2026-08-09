(* InodeLock.v -- THE ICACHE SEAM: what an inode's sleeplock parks, and the
   shadow that names it.  Design: claude-notes/design/fs-inode.md, "ilock /
   iunlock -- the LOAD, and the icache seam".

   Designing the full inode cache -- who owns an unlocked entry, how iget
   hands out references, how ip->ref is counted -- is its own effort, and
   ilock is stated OVER this seam rather than behind it, exactly as bmap is
   stated over an assumed balloc and iupdate over a caller-supplied inode
   block.  What is fixed here is only the shape of the resource the
   sleeplock protects; the layer that CREATES such a lock is deferred.

   ---- THE PARKED RESOURCE HAS TWO SHAPES, AND ip->valid SAYS WHICH ------

   [inode_parked] is what [is_sleeplock] protects.  It is

     valid = 1 : the inode's resources, parked -- the five metadata cells at
                 [dn] and the thirteen addrs cells at [bm_cells bm];
     valid = 0 : the RAW cells, at no particular value -- iget minted the
                 entry but nobody has read the dinode yet.

   Either way the block-level resources are there: the indirect block's
   [ind_res] and the file's [inode_blocks].  Those do NOT depend on the
   in-memory cells having been loaded -- the file's blocks exist on disk
   whether or not the icache has looked at them -- which is what makes the
   two shapes differ only in the CELLS.

   ---- WHY THE SHADOW EXISTS (this is the load-bearing decision) ---------

   The lock's resource is existentially quantified over [dn] and [bm]: they
   change (writei, iupdate), so they cannot be parameters of a predicate
   fixed at lock-creation time.  But on the valid = 0 arm ilock reads the
   dinode OFF THE DISK and must produce [inode_map γfs ip bm] -- whose
   [ind_res γfs bm] can only come from the lock.  So the map the disk names
   and the map the lock parked have to be THE SAME [bm], and nothing in an
   existential says so.

   That is claude-notes/durable-notes.md's rule verbatim -- "an invariant
   that takes an exclusive fragment across a sleep must RECORD the
   fragment's value".  [inode_key γi v dn bm] is that record: a HALF of a
   [ghost_var], the other half sitting inside [inode_parked].  The icache
   holds the caller-side half between locks; ilock reads the two against
   each other ([inode_key_agree]) and so learns the lock's [dn]/[bm] are
   the ones its own premises are about.  It also carries [v], which is what
   lets a caller state the on-disk agreement premise CONDITIONALLY -- "if
   this inode has never been loaded, the block I am handing you holds its
   dinode" -- rather than as an unconditional claim that would be false for
   an inode with unflushed changes.

   Locked, the caller holds BOTH halves ([inode_keys]); that is what lets it
   retag the pair after a write ([inode_keys_update]) before iunlock parks
   it again.  Unlocked, it holds one and the lock holds the other. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* The shadow's ghost.  One class, one instance; nothing below the inode
   layer knows about it, so it is introduced here rather than in the
   global [riscvGS] bundle. *)
Class inodeG (Σ : gFunctors) :=
  InodeG { inode_key_inG :: ghost_varG Σ (bool * dinode * blkmap) }.

(* WHAT A WELL-FORMED IN-MEMORY INODE IS.  Exactly the pure facts readi,
   writei and iupdate consume, plus the type test ilock's second panic
   needs.  A caller gets them OUT of ilock; nobody has to supply them. *)
Definition inode_ok (cov : gset Z) (logstart : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) : Prop :=
  blkmap_wf cov logstart bm
  /\ bm_covers bm (bv_unsigned (di_size dn))
  /\ di_addrs dn = bm_cells bm
  /\ bv_unsigned (di_type dn) <> 0
  /\ blk_holes_zero bm data.

(* ip->valid, as the word the [sw]/[lw] at +0x96 / +0x1a see *)
Definition valid_word (v : bool) : mword 32 :=
  if v then mword_of_int 1 else mword_of_int 0.

Lemma valid_word_true : valid_word true = (mword_of_int 1 : mword 32).
Proof. reflexivity. Qed.

(* the branch at +0x1c reads the cell sign-extended and tests it against
   zero: [c.beqz] is TAKEN exactly on the unloaded inode. *)
Lemma valid_word_eqz (v : bool) :
  eq_vec (sign_extend' 64 (valid_word v) : mword 64) (zero_reg : mword 64)
  = negb v.
Proof. destruct v; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(*  THE TWO GUARD TESTS BOTH ilock's AND iunlock's DEAD PANICS TURN ON      *)
(*                                                                          *)
(*  [if (ip == 0 || ip->ref < 1) panic(...)] compiles to a [c.beqz a0] and  *)
(*  a [bge x0,a5] over the SIGN-EXTENDED [lw] of ip->ref.  A real inode     *)
(*  with a live reference falls through both, and these are the two         *)
(*  readings that say so.  (FileInv.fref_word_spos is the same fact for     *)
(*  struct file's refcount, and kills filedup's and fileclose's panics.)    *)
(* ---------------------------------------------------------------------- *)

Lemma inode_ptr_nonzero (a : mword 64) :
  uint a <> 0 -> eq_vec a (zero_reg : mword 64) = false.
Proof.
  intro Ha. apply eq_vec_false_iff. intro Hc. apply Ha. rewrite Hc.
  reflexivity.
Qed.

Lemma inode_ref_spos (w : mword 32) :
  0 < bv_unsigned w < 2 ^ 31 ->
  zopz0zKzJ_s (zero_reg : mword 64) (sign_extend' 64 w : mword 64) = false.
Proof.
  intros [H0 H1].
  assert (Hw : w = (mword_of_int (bv_unsigned w) : mword 32)).
  { apply bv_eq. rewrite moi32_unsigned. symmetry. apply bvw32_small.
    change (2 ^ 32)%Z with 4294967296%Z.
    change (2 ^ 31)%Z with 2147483648%Z in H1. lia. }
  rewrite Hw. unfold zopz0zKzJ_s. rewrite Z.geb_leb. apply Z.leb_gt.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite sint64_moi32; lia.
Qed.

Section InodeLockRes.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !inodeG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The shadow                                                         *)
  (* ------------------------------------------------------------------ *)

  (* ONE half.  The icache holds this between locks; the other half is
     inside [inode_parked]. *)
  Definition inode_key (gi : gname) (v : bool) (dn : dinode) (bm : blkmap)
    : iProp Σ := ghost_var gi (1/2) (v, dn, bm).

  (* BOTH halves: what a thread holding the lock has, and what lets it
     retag the pair after a write. *)
  Definition inode_keys (gi : gname) (dn : dinode) (bm : blkmap) : iProp Σ :=
    (inode_key gi true dn bm ∗ inode_key gi true dn bm)%I.

  Lemma inode_key_agree (gi : gname) (v1 v2 : bool) (dn1 dn2 : dinode)
      (bm1 bm2 : blkmap) :
    inode_key gi v1 dn1 bm1 -∗ inode_key gi v2 dn2 bm2 -∗
      ⌜v1 = v2 /\ dn1 = dn2 /\ bm1 = bm2⌝.
  Proof.
    rewrite /inode_key. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq.
    injection Heq as -> -> ->. done.
  Qed.

  (* the two halves move together, and only together *)
  Lemma inode_key_retag (gi : gname) (v : bool) (dn : dinode) (bm : blkmap)
      (v' : bool) (dn' : dinode) (bm' : blkmap) :
    inode_key gi v dn bm -∗ inode_key gi v dn bm ==∗
      inode_key gi v' dn' bm' ∗ inode_key gi v' dn' bm'.
  Proof. rewrite /inode_key. iApply ghost_var_update_halves. Qed.

  Lemma inode_keys_update (gi : gname) (dn bm : _) (dn' : dinode) (bm' : blkmap) :
    inode_keys gi dn bm ==∗ inode_keys gi dn' bm'.
  Proof.
    rewrite /inode_keys. iIntros "[H1 H2]".
    iApply (inode_key_retag with "H1 H2").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The parked resource                                                *)
  (* ------------------------------------------------------------------ *)

  (* the cells at NO particular value: what iget leaves behind.  The length
     is what makes memmove's 52-byte destination well formed. *)
  Definition inode_raw (ip : mword 64) : iProp Σ :=
    ((∃ d : dinode, inode_meta ip d) ∗
     (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs ip l))%I.

  Definition inode_parked (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (ip : mword 64) : iProp Σ :=
    (∃ (v : bool) (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       inode_key gi v dn bm ∗
       i_valid ip ↦₄ valid_word v ∗
       ind_res gfs bm ∗
       inode_blocks gfs bm data ∗
       (if v then inode_meta ip dn ∗ inode_addrs ip (bm_cells bm)
             else inode_raw ip))%I.

  (* ------------------------------------------------------------------ *)
  (*  ...and what comes out of it while the lock is held                 *)
  (* ------------------------------------------------------------------ *)

  (* THE LOCKED INODE.  ilock produces this on both arms; iunlock consumes
     it (at whatever [dn']/[bm'] the holder ended with) and parks it back.
     [data] stays existential -- readi and writei take it as a parameter,
     so a caller instantiates rather than supplies it. *)
  Definition inode_locked (gfs : fs_names) (gi : gname)
      (cov : gset Z) (logstart : Z) (ip : mword 64)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ data : nat -> list (bv 8),
       ⌜inode_ok cov logstart dn bm data⌝ ∗
       inode_keys gi dn bm ∗
       i_valid ip ↦₄ (mword_of_int 1 : mword 32) ∗
       inode_meta ip dn ∗
       inode_map gfs ip bm ∗
       inode_blocks gfs bm data)%I.

End InodeLockRes.

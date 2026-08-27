(* InodeLock.v -- WHAT A WELL-FORMED IN-MEMORY INODE IS, and the two guard
   readings ilock's and iunlock's dead panics turn on.  Design:
   claude-notes/design/fs-icache.md §13.

   ---- WHAT USED TO BE HERE, AND WHERE IT WENT -------------------------

   This file used to hold the whole icache SEAM -- [inode_parked] (the
   resource an inode's sleeplock protected) and the [inode_key] ghost_var
   shadow that named its existentially-quantified [dn]/[bm], plus
   [inode_locked], the bundle ilock produced.  All three are gone, and the
   design note records why:

   * the CONTENT no longer lives in the sleeplock at all.  It lives in
     [IcacheEscrow.ic_escrow], a three-armed per-entry escrow, because
     iget's recycle rewrites a slot's cells holding [itable.lock] and no
     sleeplock, so a sleeplock-only home was never reachable by every
     writer (§10, §13.1c).  The sleeplock keeps [ic_tok] and nothing else.
   * the SHADOW retires with it (§13.1).  Its coupling job is done by the
     arm's own [InodeRegion.dinode_at] fragment, pinned to the entry by the
     escrow's permanent half of [i_inum] (§13.1b); and its second job --
     letting a caller state ilock's on-disk agreement premise
     conditionally -- disappeared with that premise (§11.3).  It could not
     have survived in any case: with N reference holders only two
     [ghost_var] halves exist, so "the caller supplies one" is
     unsatisfiable for the second holder.
   * [inode_locked] is now [IcacheEscrow.ic_loaded] plus the two identity
     halves and the valid cell -- i.e. exactly what [ic_swap_park] takes,
     which is what makes SpecIlock v2's postcondition literally
     SpecIunlock v2's precondition.

   What is left is pure, and shared by both sides of that seam.

   ---- WHAT A WELL-FORMED IN-MEMORY INODE IS ---------------------------

   [inode_ok] is the pure record ilock mints and every fs.c function above
   it consumes; [inode_raw] is the cell-shaped remains of an entry nobody
   has loaded yet (the escrow's unloaded arm); [valid_word] is the word in
   [ip->valid] and [valid_word_eqz] reads the cached/uncached branch off
   it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import BioDefs.   (* [BSIZE]: [inode_ok]'s size cap, §13.5 *)
Require Import DinodeEnc.
Require Import InodeInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* WHAT A WELL-FORMED IN-MEMORY INODE IS.  Exactly the pure facts readi,
   writei and iupdate consume, plus the type test ilock's second panic
   needs.  A caller gets them OUT of ilock; nobody has to supply them.

   THE SIZE CAP (design/fs-icache.md §13.5) is the fifth conjunct and it is
   NOT derivable from the fourth: [bm_covers] only says that every block
   index BELOW MAXFILE whose byte range starts inside the file is mapped,
   and says nothing at all about a size above [MAXFILE * BSIZE].  Yet
   [SpecReadi.v] (and writei behind it) takes exactly that bound as a
   genuine premise -- a file claiming a larger size would drive bmap past
   MAXFILE and into its out-of-range panic.  Before the icache that premise
   was suppliable by a caller, because the caller named the [dn] it was
   handing ilock; under SpecIlock v2 the record is an OUTPUT, existentially
   bound in the postcondition, so a caller cannot constrain it and the fact
   has to travel WITH the record.  Stated over [Z], matching SpecReadi's own
   phrasing, so no [nat] literal is ever forced (durable-notes' unary-literal
   rule). *)
Definition inode_ok (cov : gset Z) (logstart : Z)
    (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) : Prop :=
  blkmap_wf cov logstart bm
  /\ bm_covers bm (bv_unsigned (di_size dn))
  /\ di_addrs dn = bm_cells bm
  /\ bv_unsigned (di_type dn) <> 0
  /\ bv_unsigned (di_size dn) <= Z.of_nat MAXFILE * Z.of_nat BSIZE
  /\ blk_holes_zero bm data
  (* EVERY BLOCK IS A BLOCK'S WORTH OF BYTES (design §6(ii), landed by
     §13.12(b)).  itrunc's [bfree] needs it of every block it frees, and
     under SpecIlock v2 [data] is an OUTPUT -- existentially bound inside
     [IcacheEscrow.ic_loaded] -- so iput cannot supply it as a premise and
     it has to travel WITH the record, exactly as §13.5's size cap does.
     [blk_holes_zero] above pins the length only at HOLES; the blocks
     itrunc frees are precisely the ALLOCATED indices, which is why the
     hole clause could not serve.  Producers re-establish it with
     [InodeInv.inode_sized_zero] / [_insert] / [_of_alloc]. *)
  /\ inode_sized data.

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
  Context `{!riscvGS Σ}.
  (* M1 stage 2: [inode_meta]/[inode_addrs] are ↦₄ towers, hence
     context-indexed.  QUALIFIED because this file does not import
     [TsoCtx] -- an unqualified [CurCtx] here would silently generalize a
     fresh [CurCtx : Type] instead of binding the class. *)
  Context `{XI : TsoCtx.CurCtx}.

  (* the cells at NO particular value: what iget leaves behind, and what
     [IcacheEscrow.ic_unloaded] parks.  The length is what makes memmove's
     52-byte destination well formed. *)
  Definition inode_raw (ip : mword 64) : iProp Σ :=
    ((∃ d : dinode, inode_meta ip d) ∗
     (∃ l : list (bv 32), ⌜length l = 13%nat⌝ ∗ inode_addrs ip l))%I.

End InodeLockRes.

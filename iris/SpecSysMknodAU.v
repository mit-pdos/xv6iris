(* SpecSysMknodAU.v -- the mknod/create family's PURE VOCABULARY LEAF: the
   device-number reading of a syscall argument, the abstract child
   [SpecCreate.create_made] leaves behind, and nameiparent's hop-name
   family.  It re-exports [FsAbsDelta], so every consumer of the create
   delta and its row algebra sees the same names through this file.

   Definitions and small pure lemmas only -- no contract, no walk, no
   [Module Type].  sys_mknod's ONE contract is [SpecSysMknod]'s
   [SYSMKNOD]; the commits the bundle carries are [FsAbsCreateFire]'s
   authority-shaped family, re-exported by [FsAbsMknodFire].

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   ("ONE CONTRACT PER SYSCALL") and section 7's mknod row.  The abstract
   vocabulary is FsAbs.v: [anode]/[abs_of], [aview], [nview],
   [astate Γ av], [apath_at].

   ==== THE DELTA, AND THE FRESHNESS SHAPE ==============================

   [delta_create d nm i c av] (FsAbsDelta, re-exported) is the fused
   delta, type-parameterized in the child's [absnode] [c] so mkdir ([ADir]
   with dots, parent bump) and open(O_CREATE) ([AFile []]) reuse it
   verbatim; [acre_bump] is the mkdir-only parent-nlink increment, fused
   as the design asks.

   The design sketch writes the success arm as [exists i not in dom av].
   That is NOT statable over the landed [astate]: the gtop authority
   carries a row for EVERY inum of the region (free records read as bare
   nodes), so [dom av] is the whole region and no inum is ever outside it.
   The honest per-instant condition -- and the one the machine realizes --
   is [cre_pre]'s third conjunct: at the fire instant the row at [i]
   ALREADY reads as the freshly-minted child ([MkAnode c 1], the orphan
   create built before dirlink runs).  Under that observation the fused
   delta COLLAPSES to the one-row parent insert ([delta_create_dev] --
   [insert_id] on the child's row), which is why ONE ghost move at ONE
   instant realizes it: the fire point is dirlink's successful entry
   write, the only retag the delta needs.

   What the success arm therefore does NOT claim is "i was free at the
   start of the call".  Its freshness content is: the child's row reads
   [ADev ma mi] at nlink 1 at the instant, and the parent's entry map did
   not contain [nm].  A client that needs "i is none of MY nodes" gets it
   from agreement: its own pinned values are visible in the SAME [av], so
   any pinned node whose value differs from the child's is not [i].

   ==== THE HOP-NAME FAMILY ============================================

   [mknod_parent_elems pl = removelast (path_elems pl)] covers the PARENT
   PREFIX only: create resolves with nameiparent, which fires dirlookup on
   every element but the last; the LAST element is the created NAME, tied
   in the post arms by [last (path_elems pl) = Some nm] (SpecNamex's bname
   ruling makes the tie provable).  It is the family the era nameiparent
   walk ranges over ([FsAbsNpar.np_elems] is the same function), and
   unlink, open and create all state their walks over it.

   BINDERS: none -- every definition here is pure. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheEscrow.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecCreate.      (* [create_slots], [T_DEVICE], [create_made] *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname] *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   ([sb_ninodes] : fs_sb -> Z) would shadow
                                   the superblock CELL ADDRESSES a syscall
                                   frame threads *)
Require Import FsAbs.           (* the abstract state *)
Require Import FsStateDefs.    (* [fs_gamma_L]: the live Γ *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DELTA AND ITS SIDE CONDITIONS (PURE)                          *)
(* ===================================================================== *)

(* the device-number reading of a syscall argument word: argint keeps the
   low int, create's lh/sh pair keeps the low HALFWORD, and the record
   field reads back unsigned -- so the abstract child's number is the low
   sixteen bits of the trapframe word, read unsigned *)
Definition dev_arg (v : mword 64) : Z := (bv_unsigned v) mod (2 ^ 16).

Lemma dev_arg_range (v : mword 64) : 0 <= dev_arg v < 2 ^ 16.
Proof. apply Z.mod_pos_bound. lia. Qed.

Require Export FsAbsDelta.   (* [acre_bump], [delta_create] + its row algebra *)

(* [cre_pre] (THE SIDE CONDITIONS, one proposition), [cre_pre_ne] and the
   collapse [delta_create_dev] live in FsAbsDelta.v section 1, because
   [SpecCreate]'s bundle names the parent-leg commit and this file requires
   [SpecCreate].  Exported from there through the [Require Export FsAbsDelta]
   above, so every consumer sees the same names. *)

(* the reading bridge's trivial half -- pushing one raw-map insert through
   [abs_view] -- is [FsAbsDefs.abs_view_insert] (the view is an [omap], so
   the insert needs the node's row) *)

(* the abstract child create's non-directory success arm leaves behind:
   [SpecCreate.create_made] read through [abs_of] *)
Lemma abs_of_create_dev (n : fs_node) (major minor : mword 16) :
  fn_rec n = create_made T_DEVICE major minor ->
  abs_of n
  = Some (MkAnode (ADev (bv_unsigned major) (bv_unsigned minor)) 1%nat).
Proof.
  intros Hr.
  rewrite /abs_of /abs_row /abs_node /fn_is_dir /fn_type /fn_major /fn_minor
          /fn_nlink Hr.
  reflexivity.
Qed.

(* nameiparent's hop names: every element but the last (the last is the
   created NAME, tied in the post arms) *)
Definition mknod_parent_elems (pl : list (bv 8)) : list fname :=
  removelast (path_elems pl).

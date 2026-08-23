(* FsStateDefs.v -- the view record [Γ], the byte points-to, and the two
   block-level shapes every other file-system predicate is built from.

   Design of record: claude-notes/design/fs-state.md sections 0-2.  This is
   stage 2a of claude-notes/projects/durable-disk.md.

   THE ONE THING THAT MENTIONS A DISK is the field [fsΦ] of [fs_view_names]:
   a byte-address-keyed points-to, ABSTRACT here.  The file system is
   instantiated twice over the same definitions (fs-state.md section 1) --
   at the committed view [Γ_D], where [fsΦ] is the full element of the
   fixed-layer byte map, and at the logged view [Γ_L], where it is the full
   element of the era's logged view.  Nothing below knows which.

   Consequently this file imports NOTHING from [FsBlocks]/[LogInv]/any
   [Proof*]/[Spec*] file: it is pure Iris over the tree's ENCODING
   vocabulary (FsImg/DinodeEnc/BitmapEnc/FsTree/BlockWords) only.

   Two properties of [fsΦ] are needed by consumers and cannot be proved of
   an abstract predicate, so they are stated here and TAKEN AS PARAMETERS
   where they are used (the standing rule: a parameter, not a new
   config-class dependency):

   - [phi_excl Γ]: two owners of one byte is [False].  This is what makes
     [free_bitmap]'s "the bit reads allocated" argument run (fs-state.md
     section 2) -- the [fsblock_excl] of the concrete instance, lifted.
   - [GTimeless Γ]: every byte points-to is timeless.  Both concrete
     instances are ghost-map elements, so both satisfy it, and every
     predicate below is then timeless -- which is what the [>]-strips of
     the in-memory accessors need (fs-ghost-state.md section 1).  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
Require Import BioDefs.
Require Import FsImg.

(* the proofmode import re-opens nat_scope on top of the scope stack, so the
   file's scope has to be (re-)issued after it -- durable-notes.md *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The view record                                                *)
(* ------------------------------------------------------------------ *)

Section GammaDefs.
  Context {Σ : gFunctors}.

  (* [fsΦ] is spelled [Φ] in the design; the field is renamed here because a
     top-level projection named [Φ] would shadow the proofmode's ubiquitous
     [Φ] binder at every use site. *)
  Record fs_view_names := MkFsView {
    fsΦ   : Z -> bv 8 -> iProp Σ;   (* byte ownership, BY BYTE ADDRESS *)
    γlink : gname;                  (* the link-counting family (FsStateLink) *)
    γtop  : gname;                  (* the top-level abstract map (FsState)   *)
  }.

  (* the exclusivity law of the concrete instances, as a hypothesis *)
  Definition phi_excl (Γ : fs_view_names) : Prop :=
    forall (a : Z) (v w : bv 8), (fsΦ Γ a v ∗ fsΦ Γ a w) ⊢ False.

  Class GTimeless (Γ : fs_view_names) :=
    gtimeless : forall (a : Z) (v : bv 8), Timeless (fsΦ Γ a v).

  (* ---------------------------------------------------------------- *)
  (*  2.  The points-to run                                            *)
  (* ---------------------------------------------------------------- *)

  (* [bs] resides at byte offset [off] of block [b]. *)
  Definition byte_range (Γ : fs_view_names) (b off : Z) (bs : list (bv 8))
    : iProp Σ :=
    ([∗ list] k ↦ v ∈ bs, fsΦ Γ (b * BSIZE_z + off + Z.of_nat k) v)%I.

  (* a whole block, at its full width *)
  Definition blk_owned (Γ : fs_view_names) (b : Z) (bs : list (bv 8))
    : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range Γ b 0 bs)%I.

  Global Instance byte_range_timeless `{!GTimeless Γ} b off bs :
    Timeless (byte_range Γ b off bs).
  Proof.
    rewrite /byte_range. apply big_sepL_timeless.
    intros. apply gtimeless.
  Qed.

  Global Instance blk_owned_timeless `{!GTimeless Γ} b bs :
    Timeless (blk_owned Γ b bs).
  Proof. rewrite /blk_owned. apply _. Qed.

  Lemma blk_owned_length Γ b bs : blk_owned Γ b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma byte_range_nil Γ b off : byte_range Γ b off [] ⊣⊢ emp.
  Proof. rewrite /byte_range //. Qed.

  Lemma byte_range_app Γ b off bs1 bs2 :
    byte_range Γ b off (bs1 ++ bs2)
    ⊣⊢ byte_range Γ b off bs1
        ∗ byte_range Γ b (off + Z.of_nat (length bs1)) bs2.
  Proof.
    rewrite /byte_range big_sepL_app.
    apply bi.sep_proper; [done |].
    apply big_sepL_proper. intros k y _.
    assert (Hz : b * BSIZE_z + off + Z.of_nat (length bs1 + k)
                 = b * BSIZE_z + (off + Z.of_nat (length bs1)) + Z.of_nat k)
      by lia.
    rewrite Hz //.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  Exclusivity: two owners of one byte is [False]               *)
  (*                                                                   *)
  (*  This is the ONE exclusivity law the design ever invokes -- used  *)
  (*  exactly as [l ↦ _ ∗ l ↦ _ ⊢ False] is, to learn that two owned   *)
  (*  things are different objects, never as an invariant.             *)
  (* ---------------------------------------------------------------- *)

  Lemma byte_range_excl Γ (Hex : phi_excl Γ) b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range Γ b off bs -∗ byte_range Γ b off bs' -∗ False.
  Proof.
    intros Hl Hl'.
    iIntros "H H'".
    destruct (lookup_lt_is_Some_2 bs 0%nat Hl) as [v Hv].
    destruct (lookup_lt_is_Some_2 bs' 0%nat Hl') as [v' Hv'].
    rewrite /byte_range.
    iDestruct (big_sepL_lookup _ _ 0%nat v Hv with "H") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat v' Hv' with "H'") as "H2".
    iApply (Hex (b * BSIZE_z + off + Z.of_nat 0%nat) v v').
    iFrame.
  Qed.

  Lemma BSIZE_pos_nat : (0 < BSIZE)%nat.
  Proof. rewrite /BSIZE. lia. Qed.

  Lemma blk_owned_excl Γ (Hex : phi_excl Γ) b bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b bs' -∗ False.
  Proof.
    iIntros "[%Hl H] [%Hl' H']".
    iApply (byte_range_excl Γ Hex b 0 bs bs' with "H H'");
      [rewrite Hl | rewrite Hl']; apply BSIZE_pos_nat.
  Qed.

  (* "distinctness of an inode's own blocks is the [∗]" (fs-state.md
     section 2): the disjointness clause [blkmap_wf]'s injectivity used to
     state is a CONSEQUENCE here, not a maintained fact. *)
  Lemma blk_owned_ne Γ (Hex : phi_excl Γ) b b' bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    iIntros "H H'". destruct (decide (b = b')) as [-> | Hne]; [| done].
    iDestruct (blk_owned_excl Γ Hex with "H H'") as "[]".
  Qed.

End GammaDefs.

Global Arguments fs_view_names : clear implicits.
Global Existing Instance gtimeless.

(* Any [Definition] whose body is a big-op over a block-sized list must be
   sealed the day it is written, or [iFrame] resolves its [Frame] instances
   up to delta, unfolds a 1024-element [big_sepL] and does not come back
   (measured at over ten minutes on the concrete twin, [FsBlocks.fsblock]).
   [rewrite /byte_range] and the declared [Timeless] instances still work. *)
Global Typeclasses Opaque byte_range blk_owned.

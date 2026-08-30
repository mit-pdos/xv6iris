(* FsAbsStart.v -- THE DEFERRED START: the ONE premise shape that lets an
   era walk begin somewhere other than the root.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item ("the RELATIVE START").  A leaf and not an append, for
   [FsAbsNpar]'s reason (the mirror forbids touching a tracked file); fuse
   the three [FsAbs*] era leaves when [FsAbsEra.v] is next edited.

   ==== WHAT THE GAP ACTUALLY WAS =======================================

   The era contracts ([SpecNamexEra], [SpecNparEra] and the wrappers over
   them) carried TWO trace premises -- [P 0 ROOTINO] and the hop family --
   beside the scope premise [pfun 0 = SLASH].  A RELATIVE walk starts at
   [idup(p->cwd)] instead, and the recorded blocker (SpecNameiTr's Q-c,
   restated in [SpecNparEra]'s header) was that no landed reading exposes
   the cwd's inum: [IcacheRef.inode_held] hides it existentially, so
   [P 0 <the cwd's inum>] is not a formula the caller can write.

   IT DOES NOT HAVE TO BE.  The caller never needs to NAME the start inum
   -- the WALK knows it, and knows it at exactly the instant it matters:
   idup's postcondition hands back a package whose existential witness IS
   the slot's inum, so the proof reads it there and instantiates the
   caller's trace at that value.  What the contract has to carry is
   therefore not an exposed cwd but a trace that is PARAMETRIC in the
   start: a one-shot, universally quantified over the start inum, with the
   only tie a caller can be expected to know -- an ABSOLUTE path starts at
   the root.

   That is precisely the shape lane W's [FsAbsEraMknod.mknod_walk_pre_era]
   was already written in (that file's ∀ pl r with the [pl !! 0 = Some
   SLASH -> r = ROOTINO] side condition), which is why the consumer side
   needed no invention: [ep_start] at lane W's own [pl] IS that predicate
   ([FsAbsNparMknod.np_start_of_mknod], one [iMod] and a [vm_compute]).

   ==== THE ABSOLUTE ARMS DO NOT WEAKEN =================================

   [ex_start_of_pair] / [ep_start_of_pair] are the receipts: a caller
   holding the landed pair, on a path that begins with SLASH, builds the
   deferred form and loses nothing (the tie forces [r = ROOTINO], so the
   pair it holds is already at the right index).  So every consumer of the
   old contracts composes through the new ones, and the strengthening is
   one-directional.

   ==== THE TIE IS ON THE PATH LIST, NOT THE BUFFER =====================

   [pl !! 0 = Some SLASH] rather than [pfun 0 = SLASH]: the walk has both
   ([pl = bview plen pfun]) but only the list form is statable at the
   altitudes above namex, and it is lane W's spelling.  The two head
   lemmas below are the bridge, and they are the reason the walk's
   RELATIVE arm can discharge the tie at all -- it holds [pfun 0 <> SLASH]
   and needs the [pl] form refuted. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import ByteBuf.         (* [bb_cstr]: the C-string buffer invariant *)
Require Import DirentEnc.       (* [bview]                                  *)
Require Import PathElems.       (* [path_elems], [SLASH]                    *)
Require Import InodeInv.        (* [ROOTINO] : mword 32, namex's own        *)
Require Import FsBlocks.        (* [fs_names]                               *)
Require Import FsBytesGamma.    (* [fs_gamma_L]                             *)
Require Import FsStateEra.
Require Import IcacheRef.
Require Import IcacheEscrow.
Require Import Xv6G.
Require Import FsAbsEra.        (* [ex_hops_from]: the namei-side family    *)
Require Import FsAbsNpar.       (* [ep_hops_from]: the parent-prefix family *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE HEAD OF THE PATH BUFFER, BOTH WAYS                            *)
(*                                                                        *)
(*  Top level, outside the ghost section, so they carry no binder -- and  *)
(*  because the walk's proofmode context is where [lia] starves           *)
(*  (ProofNamex's [nx_wi_*] rule).                                        *)
(* ===================================================================== *)

Lemma bview_head_slash (plen : nat) (pfun : nat -> bv 8) :
  bview plen pfun !! 0%nat = Some SLASH -> pfun 0%nat = SLASH.
Proof.
  destruct plen as [| p'].
  - intros H. discriminate H.
  - rewrite (bview_lookup (S p') pfun 0%nat ltac:(lia)).
    intros H. by injection H.
Qed.

(* The other direction needs the buffer to be NONEMPTY, and [bb_cstr]
   gives that for free at a path beginning with SLASH: the terminator sits
   at index [plen], so [plen = 0] would make the head a NUL. *)
Lemma bview_head_slash_intro (plen : nat) (pfun : nat -> bv 8) :
  bb_cstr pfun plen -> pfun 0%nat = SLASH ->
  bview plen pfun !! 0%nat = Some SLASH.
Proof.
  intros [_ Hnul] Hsl.
  destruct plen as [| p'].
  - exfalso. rewrite Hsl in Hnul.
    assert (HSN : SLASH <> (mword_of_int 0 : mword 8))
      by (vm_compute; discriminate).
    exact (HSN Hnul).
  - rewrite (bview_lookup (S p') pfun 0%nat ltac:(lia)). by rewrite Hsl.
Qed.

Section FsAbsStart.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE DEFERRED TRACE, AT BOTH FAMILIES                            *)
  (* =================================================================== *)

  (* THE NAMEI SIDE: the full family over [path_elems pl].  One shot, at
     the start inum the walk supplies -- ROOTINO on the absolute arm,
     idup's own package's inum on the relative one. *)
  Definition ex_start (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∀ r : Z,
       ⌜pl !! 0%nat = Some SLASH -> r = bv_unsigned ROOTINO⌝ ={⊤}=∗
       P 0%nat r ∗ ex_hops_from γfs P Pmiss pl 0%nat)%I.

  (* THE NAMEIPARENT SIDE: the same one shot over the PARENT PREFIX
     ([FsAbsNpar.np_elems], which is lane W's [mknod_parent_elems]). *)
  Definition ep_start (γfs : fs_names) (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∀ r : Z,
       ⌜pl !! 0%nat = Some SLASH -> r = bv_unsigned ROOTINO⌝ ={⊤}=∗
       P 0%nat r ∗ ep_hops_from γfs P Pmiss pl 0%nat)%I.

  (* =================================================================== *)
  (*  2.  THE RECEIPTS: THE ABSOLUTE PAIR IS A START                      *)
  (* =================================================================== *)

  Lemma ex_start_of_pair (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    pl !! 0%nat = Some SLASH ->
    P 0%nat (bv_unsigned ROOTINO) -∗
    ex_hops_from γfs P Pmiss pl 0%nat -∗
    ex_start γfs P Pmiss pl.
  Proof.
    iIntros (Hsl) "HP Hh". rewrite /ex_start.
    iIntros (r Hr). rewrite (Hr Hsl). iModIntro. iFrame.
  Qed.

  Lemma ep_start_of_pair (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    pl !! 0%nat = Some SLASH ->
    P 0%nat (bv_unsigned ROOTINO) -∗
    ep_hops_from γfs P Pmiss pl 0%nat -∗
    ep_start γfs P Pmiss pl.
  Proof.
    iIntros (Hsl) "HP Hh". rewrite /ep_start.
    iIntros (r Hr). rewrite (Hr Hsl). iModIntro. iFrame.
  Qed.

End FsAbsStart.

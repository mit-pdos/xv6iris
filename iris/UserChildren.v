(* ===================================================================== *)
(* UserChildren.v -- THE PROCESS'S LIVE CHILDREN, AS A RESOURCE.          *)
(*                                                                        *)
(* The key a user process is resumed at carries the GENERATIONS of its    *)
(* live children ([UexecSlot.uvis_ch], the reading of the kernel's        *)
(* per-slot children cell under <wait_lock>), and [UkRun.urun] binds the  *)
(* set existentially exactly as it binds the image, the break, the        *)
(* descriptor view and the working directory.  A program that never       *)
(* forks therefore never names it.  A program that DOES -- one whose      *)
(* wait(2) has to know that the child it is waiting for is still its      *)
(* child, or that it has no others -- needs a carrier for the claim that  *)
(* its children are exactly [S], and that carrier is this file.           *)
(*                                                                        *)
(* THE SHAPE IS [UserCwd]'s, at a set instead of an inum.  A descriptor   *)
(* table is a ghost map because its slots move independently; a children  *)
(* set moves as a whole (fork adds one generation, wait removes one, exit *)
(* hands the lot to init), so the ghost is one variable split in half:    *)
(*                                                                        *)
(*   uch_auth γs S   the ENGINE's half, inside [UkRun.urun], pinned to    *)
(*                   the very [cs] the trap key is at -- that pinning is  *)
(*                   the whole content of the resource, and it is why the *)
(*                   half has to live in [urun] and not beside it.        *)
(*   uch γs S        the PROGRAM's half, a separable resource a proof     *)
(*                   carries into a subroutine, frames across unrelated   *)
(*                   calls, and hands to the syscall that moves it.       *)
(*                                                                        *)
(* WHY HALVES AND NOT A PERSISTENT PIN.  fork and wait move the set, so   *)
(* the value must be updatable; an update needs the whole variable, so    *)
(* each side holds enough that neither can move it alone.  Every other    *)
(* syscall keeps it ([UsysMemOk.usys_ch_ok] is the identity at every      *)
(* number), so the program's half rides through a call untouched and no   *)
(* leaf but fork's, wait's and exit's mentions it.                        *)
(*                                                                        *)
(* THE GENERATION ITSELF ([UexecSlot.uvis_gen]) HAS NO MIRROR HERE.  A    *)
(* process does not need a resource saying what its own name is: the      *)
(* parties that read it are the exit deposit (which names it as the key's *)
(* own projection) and the escrow's payment law, both of which have the   *)
(* key in hand.                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var.
Local Open Scope Z_scope.

Section UserChildren.
  (* [Xv6Cameras.uchG]'s capacity -- the one member of [ghost_varG Σ (gset
     gname)] on the whole-system bundle, so there is no second instance
     path and no need for the [OffGv] pinning idiom *)
  Context `{!ghost_varG Σ (gset gname)}.

  (* the ENGINE's half: [UkRun.urun] carries it at the key's [uvis_ch] *)
  Definition uch_auth (γs : gname) (S : gset gname) : iProp Σ :=
    ghost_var γs (1/2) S.

  (* the PROGRAM's half *)
  Definition uch (γs : gname) (S : gset gname) : iProp Σ :=
    ghost_var γs (1/2) S.

  Global Instance uch_auth_timeless γs S : Timeless (uch_auth γs S).
  Proof. apply _. Qed.
  Global Instance uch_timeless γs S : Timeless (uch γs S).
  Proof. apply _. Qed.

  (* the fragment READS the engine's half: this is the lemma the whole
     resource exists for, and it is why the authority sits INSIDE [urun]
     rather than beside it -- [cs] is bound by [urun]'s own existential, so
     a program learns it only by agreement. *)
  Lemma uch_agree (γs : gname) (S S' : gset gname) :
    uch_auth γs S -∗ uch γs S' -∗ ⌜ S = S' ⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  (* ...and BOTH halves move it, which is what fork, wait and exit spend. *)
  Lemma uch_update (γs : gname) (S S' S'' : gset gname) :
    uch_auth γs S -∗ uch γs S' ==∗ uch_auth γs S'' ∗ uch γs S''.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->.
    iMod (ghost_var_update_2 S'' with "H1 H2") as "[$ $]"; [ | done ].
    rewrite Qp.half_half. reflexivity.
  Qed.

  (* the mint, at the set the key carries: an entry constructor keeps the
     authority in the [urun] it is building and hands the fragment to the
     program. *)
  Lemma uch_alloc (S : gset gname) :
    ⊢ |==> ∃ γs : gname, uch_auth γs S ∗ uch γs S.
  Proof.
    iMod (ghost_var_alloc S) as (γs) "Hc".
    iEval (rewrite -Qp.half_half) in "Hc".
    iDestruct (ghost_var_split with "Hc") as "[HA HF]".
    iModIntro. iExists γs. iFrame "HA HF".
  Qed.

  (* A FRAGMENT AT A SET THE CARRIER IS NOT READING -- [UserCwd.ucwd_any]'s
     shape.  A program that holds its children only so that it can hand
     them to a call it does not care about the result of carries THIS,
     which has no index and therefore costs its lemma statements one
     resource and no binder.  It is also what the kernel-side program
     constructors weaken the fragment to for a pstate. *)
  Definition uch_any (γs : gname) : iProp Σ :=
    (∃ S : gset gname, uch γs S)%I.

  Global Instance uch_any_timeless γs : Timeless (uch_any γs).
  Proof. apply _. Qed.

  Lemma uch_any_of (γs : gname) (S : gset gname) : uch γs S -∗ uch_any γs.
  Proof. iIntros "H". iExists S. iExact "H". Qed.

End UserChildren.

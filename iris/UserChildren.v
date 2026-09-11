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
Require Import SailStdpp.Base SailStdpp.Values.
Require Import ChildTok.   (* [exit_tok] / [gen_uniq] -- what a reap answers
                              with beside the set it moved *)
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

(* ===================================================================== *)
(* WHAT A REAP DOES TO THE READING, as the one PURE row every party from  *)
(* kwait to the trap loop relays: AT MOST ONE generation leaves it -- the *)
(* one that was reaped, which [WaitInv.children_inv_reap] takes out of    *)
(* both columns of the wait-lock invariant -- and every failing arm       *)
(* leaves it alone, because the C returns before [pp->parent = 0].  WHICH *)
(* generation left, and the escrow that redeems it, are [wait_ans] below; *)
(* this is that answer's pure shadow, for the relays that only need to    *)
(* know the reading moved.  Outside the section: it names no ghost and no *)
(* class.                                                                 *)
(* ===================================================================== *)
Definition ch_reaped (cs cs' : gset gname) : Prop :=
  cs' = cs \/ exists γ' : gname, cs' = cs ∖ {[γ']}.

Lemma ch_reaped_refl (cs : gset gname) : ch_reaped cs cs.
Proof. left. reflexivity. Qed.

Lemma ch_reaped_del (cs : gset gname) (γ' : gname) : ch_reaped cs (cs ∖ {[γ']}).
Proof. right. exists γ'. reflexivity. Qed.

(* ===================================================================== *)
(* WHAT A WAIT ANSWERS, IN THE TWO ARMS wait() HAS -- the ONE predicate   *)
(* every party from kwait to the program relays.                         *)
(*                                                                       *)
(* IT FAILED and returned -1: the caller has no children at all, or it    *)
(* was killed, or copyout could not place the status.  Nothing was        *)
(* reaped (the C returns before [pp->parent = 0]), so the caller's        *)
(* children reading does not move.  THE -1 ARM CLAIMS NOTHING ABOUT THE   *)
(* SET, and that is forced by the code and not a weakening: two of those  *)
(* three exits happen with children present.                             *)
(*                                                                       *)
(* IT REAPED, and then it returns THAT child's pid and three things ride  *)
(* with it:                                                              *)
(*   the reaped generation leaves the caller's reading                    *)
(*     ([WaitInv.children_inv_reap] takes it out of both columns of the   *)
(*     wait-lock invariant, so the move is [cs ∖ {γ'}] whether the zombie *)
(*     was the caller's own child or an orphan reparented to it);         *)
(*   the ESCROW ([ChildTok.exit_tok]) the zombie's exit parked, at the    *)
(*     status its [p->xstate] cell holds -- which is the very word the    *)
(*     copyout put in the caller's buffer;                                *)
(*   and PID UNIQUENESS over the caller's reading                         *)
(*     ([ChildTok.gen_uniq]): no other child of this caller carries the   *)
(*     returned pid, which is what makes the returned NUMBER name the     *)
(*     generation the escrow is at.  A parent holding                     *)
(*     [ChildTok.child_tok] for a child it forked spends the two together *)
(*     ([ChildTok.gen_uniq_tok] then [ChildTok.gen_pay]).                 *)
(*                                                                       *)
(* THE ARMS ARE DISJOINT AT THE RETURN VALUE: a reaped pid is in          *)
(* [1, PIDMAX], so a caller that reads a nonnegative result knows it is   *)
(* on the second arm without holding anything. *)
(* ===================================================================== *)
Section WaitAns.
  Context `{!ctokG Σ}.

  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝
     ∨ ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']}⌝ ∗ exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.

  (* the pure row, which is all the twenty-odd relays between kwait and the
     program ever look at *)
  Lemma wait_ans_reaped (rv : mword 32) (xs : Z) (cs cs' : gset gname) :
    wait_ans rv xs cs cs' -∗ ⌜ch_reaped cs cs'⌝.
  Proof.
    iIntros "[[_ %He] | (%γ' & %He & _)]"; iPureIntro.
    - left. exact He.
    - right. exists γ'. exact He.
  Qed.

  (* the failing arm, for the three exits that reap nothing *)
  Lemma wait_ans_neg (xs : Z) (cs : gset gname) :
    ⊢ wait_ans (mword_of_int (-1) : mword 32) xs cs cs.
  Proof. iLeft. iPureIntro. split; reflexivity. Qed.

End WaitAns.

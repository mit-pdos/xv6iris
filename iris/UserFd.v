(* ===================================================================== *)
(* UserFd.v -- THE PROGRAM'S OWN VIEW OF ITS DESCRIPTOR TABLE.             *)
(*                                                                        *)
(* [FdSlots] already has a two-sided ghost table for descriptors, and this *)
(* is NOT a second copy of it.  The distinction is who holds what:         *)
(*                                                                        *)
(*   FdSlots.fd_st_auth / fd_st  is the KERNEL/PROCESS split.  The kernel  *)
(*     keeps the authority inside [ProcInv.ofile_slot]; the fragments go   *)
(*     out to the process for the duration of user execution and come back *)
(*     at the trap ([UexecRet.uvb_F]'s [Rfd fdv]).  Its ghost name is      *)
(*     [pv_fdg], chosen by allocproc, and a user-level proof cannot see    *)
(*     it: [uslot] ∀-binds the resource that realizes the view.           *)
(*                                                                        *)
(*   ufd_auth / ufd (this file) is the PROGRAM-INTERNAL split.  The        *)
(*     authority lives inside [UkRun.urun], beside the heap and the stack; *)
(*     a handle [ufd γf 1 (FdOpen …)] is a SEPARABLE resource a program    *)
(*     proof can carry into a subroutine, frame across unrelated calls,    *)
(*     and hand back -- which is the whole point, and is exactly what the  *)
(*     kernel-side fragments cannot do, since the program never names      *)
(*     their ghost name and hands the whole bundle back at every trap.     *)
(*                                                                        *)
(* CLOSED SLOTS ARE ABSENT, not mapped to [FdClosed].  That is the one     *)
(* design decision here and it is what makes [open] work: minting a handle *)
(* for the descriptor the kernel just returned is [ghost_map_insert],      *)
(* which needs the key FREE.  Were closed slots mapped, [open] would have  *)
(* to UPDATE the slot and would need its handle first -- and there is      *)
(* nobody to hold the handle of a closed descriptor.  So:                  *)
(*                                                                        *)
(*     ufd γf fd st   =   "fd is open, at st, and this is my handle"       *)
(*                                                                        *)
(* and a closed descriptor is the ABSENCE of a handle, which is also the   *)
(* reading a program wants ("I hold fd 0 and fd 1; I say nothing about the *)
(* other fourteen").                                                       *)
(*                                                                        *)
(* WHAT THE OPEN/DUP RULES NEED FROM THE KERNEL, and why the table had to  *)
(* be sharpened for them: [ufd_open] and [ufd_dup] take                    *)
(* [fdv !! fd = Some FdClosed] -- the slot the kernel chose was FREE.      *)
(* Without it a syscall would be licensed to retype a descriptor the       *)
(* program is already holding a handle for, and the handle would be a lie. *)
(* xv6's fdalloc really does scan for a free slot, so the fact is true and *)
(* was already proved inside sys_open/sys_dup; it simply was not in the    *)
(* row.  See [UsysMemOk.usys_fd_ok]'s open and dup arms.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import FdSlots.
Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------- *)
(* §1  THE MAP A DESCRIPTOR LIST DENOTES.                                *)
(* ------------------------------------------------------------------- *)
(* [map_seq 0] is the list read as a map on its indices; the filter drops
   the closed slots.  Both halves are stdpp's, so every fact below is one
   rewrite of [lookup_map_seq_0] and one of [map_lookup_filter]. *)
Definition ufd_map (fdv : list fdstate) : gmap nat fdstate :=
  filter (fun kv => kv.2 <> FdClosed) (map_seq 0 fdv).

(* the reading, in the only direction anything needs it *)
Lemma ufd_map_lookup (fdv : list fdstate) (fd : nat) (st : fdstate) :
  ufd_map fdv !! fd = Some st <-> fdv !! fd = Some st /\ st <> FdClosed.
Proof.
  unfold ufd_map. rewrite map_lookup_filter_Some lookup_map_seq_0. reflexivity.
Qed.

Lemma ufd_map_lookup_None (fdv : list fdstate) (fd : nat) :
  fdv !! fd = Some FdClosed -> ufd_map fdv !! fd = None.
Proof.
  intros Hc. destruct (ufd_map fdv !! fd) as [st |] eqn:He; [| reflexivity].
  exfalso. apply ufd_map_lookup in He as [Hl Hne].
  rewrite Hc in Hl. injection Hl as <-. exact (Hne eq_refl).
Qed.

(* [map_seq] commutes with a list insert INSIDE the list.  stdpp has no
   such lemma, and it is one [map_eq]. *)
Lemma map_seq_insert (fdv : list fdstate) (fd : nat) (st : fdstate) :
  (fd < length fdv)%nat ->
  map_seq 0 (<[fd := st]> fdv) = <[fd := st]> (map_seq 0 fdv : gmap nat fdstate).
Proof.
  intros Hlt. apply map_eq. intros i.
  rewrite lookup_map_seq_0.
  destruct (decide (i = fd)) as [-> | Hne].
  - rewrite lookup_insert list_lookup_insert; [reflexivity | exact Hlt].
  - (* both side conditions are the disequality, and each library states it
       in whichever order it prefers -- [congruence] is indifferent. *)
    rewrite lookup_insert_ne; [| congruence].
    rewrite lookup_map_seq_0 list_lookup_insert_ne; [reflexivity | congruence].
Qed.

(* ...and the two ways the filter reacts to it: a slot that becomes OPEN is
   an insert, a slot that becomes CLOSED is a delete. *)
Lemma ufd_map_insert_open (fdv : list fdstate) (fd : nat) (st : fdstate) :
  (fd < length fdv)%nat -> st <> FdClosed ->
  ufd_map (<[fd := st]> fdv) = <[fd := st]> (ufd_map fdv).
Proof.
  intros Hlt Hne. unfold ufd_map. rewrite (map_seq_insert fdv fd st Hlt).
  apply map_filter_insert_True. exact Hne.
Qed.

Lemma ufd_map_insert_closed (fdv : list fdstate) (fd : nat) :
  (fd < length fdv)%nat ->
  ufd_map (<[fd := FdClosed]> fdv) = delete fd (ufd_map fdv).
Proof.
  intros Hlt. unfold ufd_map. rewrite (map_seq_insert fdv fd FdClosed Hlt).
  (* stdpp's [_False] arm gives [filter P (delete i m)]; the delete then
     comes out through the filter. *)
  rewrite map_filter_insert_False; [| intro Hc; exact (Hc eq_refl)].
  apply map_filter_delete.
Qed.

(* the table a fresh process starts at holds no handles at all *)
Lemma ufd_map_fdt0 : ufd_map fdt0 = ∅.
Proof.
  apply map_eq. intros i. rewrite lookup_empty.
  destruct (ufd_map fdt0 !! i) as [st |] eqn:He; [| reflexivity].
  exfalso. apply ufd_map_lookup in He as [Hl Hne].
  unfold fdt0 in Hl. apply lookup_replicate in Hl as [-> _].
  exact (Hne eq_refl).
Qed.

(* ------------------------------------------------------------------- *)
(* §2  THE RESOURCE.                                                     *)
(* ------------------------------------------------------------------- *)
Class ufdG (Σ : gFunctors) := UfdG { ufd_ghost_mapG :: ghost_mapG Σ nat fdstate }.
Definition ufdΣ : gFunctors := #[ ghost_mapΣ nat fdstate ].
Global Instance subG_ufdG {Σ} : subG ufdΣ Σ -> ufdG Σ.
Proof. solve_inG. Qed.

Section UserFd.
  Context `{!ufdG Σ}.

  (* the AUTHORITY, which [UkRun.urun] carries beside the heap: it pins the
     map to the descriptor view the kernel handed the process. *)
  (* THE LENGTH RIDES WITH THE AUTHORITY.  A descriptor table is [NOFILE]
     slots and every row preserves that ([UsysMemOk.usys_fd_ok_length]) --
     but the U-tier has no other way to know it, since the bundle that
     carries it ([FdSlots.fd_frags], inside the kernel's abstract [Rfd]) is
     invisible there.  Carrying it here is what lets a leaf turn "the handle
     is for [fd]" into "[fd] is a number a C [int] holds", which every
     argument-register premise needs. *)
  Definition ufd_auth (γf : gname) (fdv : list fdstate) : iProp Σ :=
    (ghost_map_auth γf 1 (ufd_map fdv) ∗ ⌜length fdv = NOFILE⌝)%I.

  Lemma ufd_auth_len (γf : gname) (fdv : list fdstate) :
    ufd_auth γf fdv -∗ ⌜length fdv = NOFILE⌝.
  Proof. iIntros "[_ $]". Qed.

  (* ...and the HANDLE, which the program carries.  The [FdClosed] side
     condition is redundant against the authority (a closed slot is absent
     from the map) but is worth having in the handle itself, so that a
     lemma can read "this descriptor is open" off one hypothesis. *)
  Definition ufd (γf : gname) (fd : nat) (st : fdstate) : iProp Σ :=
    (fd ↪[γf] st ∗ ⌜st <> FdClosed⌝)%I.

  Global Instance ufd_timeless γf fd st : Timeless (ufd γf fd st).
  Proof. apply _. Qed.

  (* a handle READS the view: this is the lemma that makes a handle worth
     carrying, and it is why the authority has to sit inside [urun] rather
     than beside it. *)
  Lemma ufd_agree (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st -∗ ⌜fdv !! fd = Some st⌝.
  Proof.
    iIntros "[Ha _] [Hf _]".
    iDestruct (ghost_map_lookup with "Ha Hf") as %He.
    iPureIntro. exact (proj1 (proj1 (ufd_map_lookup fdv fd st) He)).
  Qed.

  (* two handles for the same descriptor cannot both exist -- the map is at
     the full fraction, so a handle is exclusive. *)
  Lemma ufd_excl (γf : gname) (fd : nat) (st st' : fdstate) :
    ufd γf fd st -∗ ufd γf fd st' -∗ False.
  Proof.
    iIntros "[H1 _] [H2 _]".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
    destruct (Hne eq_refl).
  Qed.

  (* ---- OPEN: a free slot becomes a handle. ---- *)
  (* The premise is the kernel's own choice made visible: fdalloc scanned
     for a CLOSED descriptor and this is the one it found.  Without it this
     rule would be unsound-looking in exactly the interesting way -- it
     would mint a second handle for a descriptor the program already
     holds. *)
  Lemma ufd_open (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    fdv !! fd = Some FdClosed ->
    st <> FdClosed ->
    ufd_auth γf fdv ==∗ ufd_auth γf (<[fd := st]> fdv) ∗ ufd γf fd st.
  Proof.
    intros Hc Hne. iIntros "Ha".
    iDestruct "Ha" as "[Ha %Hlen]".
    rewrite /ufd_auth (ufd_map_insert_open fdv fd st
                         (lookup_lt_Some _ _ _ Hc) Hne).
    iMod (ghost_map_insert fd st (ufd_map_lookup_None fdv fd Hc) with "Ha")
      as "[Ha Hf]".
    iModIntro. iSplitL "Ha".
    { iFrame "Ha". iPureIntro. by rewrite length_insert. }
    iFrame "Hf". iPureIntro. exact Hne.
  Qed.

  (* ---- DUP: the source handle comes back, and the target is a copy. ---- *)
  (* The source handle is a PRECONDITION rather than a convenience: dup's
     row says the new descriptor holds a copy of the ARGUMENT's state, so
     without knowing what that state is there is nothing to hand back.  The
     handle is what says it, via [ufd_agree]. *)
  Lemma ufd_dup (γf : gname) (fdv : list fdstate) (fd0 fd1 : nat)
      (st : fdstate) :
    fdv !! fd1 = Some FdClosed ->
    ufd_auth γf fdv -∗ ufd γf fd0 st ==∗
    ufd_auth γf (<[fd1 := st]> fdv) ∗ ufd γf fd0 st ∗ ufd γf fd1 st.
  Proof.
    intros Hc. iIntros "Ha Hf".
    iDestruct "Hf" as "[Hf %Hne]".
    iMod (ufd_open γf fdv fd1 st Hc Hne with "Ha") as "[$ $]".
    iModIntro. iFrame "Hf". iPureIntro. exact Hne.
  Qed.

  (* ---- DUP, WITHOUT THE SOURCE HANDLE. ----
     A caller that is not tracking the source descriptor still has to move
     the authority, because the TABLE moved whether or not the caller was
     watching.  It can: the new slot was free, so either the source was
     closed too -- and then the copy changes nothing the map records -- or
     it was open, and the insert is [ufd_open]'s, whose handle this caller
     simply drops.  What it CANNOT do is learn anything, which is the whole
     difference between this and [ufd_dup].

     This is what lets a program that does not yet track its descriptors
     call dup at all.  It is not a weaker rule so much as a rule with
     nothing in its conclusion. *)
  Lemma ufd_dup_untracked (γf : gname) (fdv : list fdstate) (fd0 fd1 : nat) :
    fdv !! fd1 = Some FdClosed ->
    ufd_auth γf fdv ==∗ ufd_auth γf (<[fd1 := fdv !!! fd0]> fdv).
  Proof.
    intros Hc. iIntros "Ha".
    destruct (decide (fdv !!! fd0 = FdClosed)) as [He | Hne].
    - (* the source was closed too: the map does not record either slot, so
         writing one over the other leaves it alone *)
      iDestruct "Ha" as "[Ha %Hlen]".
      rewrite He /ufd_auth (ufd_map_insert_closed fdv fd1
                              (lookup_lt_Some _ _ _ Hc)).
      rewrite (delete_notin _ _ (ufd_map_lookup_None fdv fd1 Hc)).
      iModIntro. iFrame "Ha". iPureIntro. by rewrite length_insert.
    - iMod (ufd_open γf fdv fd1 (fdv !!! fd0) Hc Hne with "Ha") as "[$ _]".
      by iModIntro.
  Qed.

  (* ---- CLOSE: the handle is spent. ---- *)
  Lemma ufd_close (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st ==∗ ufd_auth γf (<[fd := FdClosed]> fdv).
  Proof.
    iIntros "Ha Hf".
    iDestruct (ufd_agree with "Ha Hf") as %Hl.
    iDestruct "Hf" as "[Hf _]".
    iDestruct "Ha" as "[Ha %Hlen]".
    rewrite /ufd_auth (ufd_map_insert_closed fdv fd (lookup_lt_Some _ _ _ Hl)).
    iMod (ghost_map_delete with "Ha Hf") as "Ha". iModIntro.
    iFrame "Ha". iPureIntro. by rewrite length_insert.
  Qed.

  (* ---- the QUIET rows: the view did not move, so neither does the map. ---- *)
  Lemma ufd_auth_quiet (γf : gname) (fdv fdv' : list fdstate) :
    fdv' = fdv -> ufd_auth γf fdv -∗ ufd_auth γf fdv'.
  Proof. intros ->. iIntros "$". Qed.

  (* ---- allocation, AT ANY VIEW. ----
     Minted where a process's [UkRun.urun] is created, beside the heap's own
     three ghost names, and at the view the resumed KEY carries -- which for
     a process the kernel has just started is [fdt0], but for one it is
     resuming is whatever the table then reads. *)
  Lemma ufd_alloc (fdv : list fdstate) :
    length fdv = NOFILE -> ⊢ |==> ∃ γf : gname, ufd_auth γf fdv.
  Proof.
    intros Hlen. iMod (ghost_map_alloc (ufd_map fdv)) as (γf) "[Ha _]".
    iModIntro. iExists γf. iFrame "Ha". iPureIntro. exact Hlen.
  Qed.

  (* the fresh-process instance, where every slot is closed and the program
     therefore starts holding no handles at all *)
  Lemma ufd_alloc_fdt0 : ⊢ |==> ∃ γf : gname, ufd_auth γf fdt0.
  Proof. iApply (ufd_alloc fdt0 fdt0_length). Qed.

  (* A HANDLE NAMES A DESCRIPTOR A C [int] CAN HOLD.  This is the fact an
     argument-register premise is proved from. *)
  Lemma ufd_bound (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st -∗ ⌜(fd < NOFILE)%nat⌝.
  Proof.
    iIntros "Ha Hh". iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ufd_agree with "Ha Hh") as %Hl.
    iPureIntro. rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hl).
  Qed.

End UserFd.

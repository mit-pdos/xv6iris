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
(*   ufd_auth / ufd / ustd (this file) is the PROGRAM-INTERNAL split.  The *)
(*     authority lives inside [UkRun.urun], beside the heap and the stack; *)
(*     the fragments are SEPARABLE resources a program proof can carry     *)
(*     into a subroutine, frame across unrelated calls, and hand back --   *)
(*     which is the whole point, and is exactly what the kernel-side       *)
(*     fragments cannot do, since the program never names their ghost name *)
(*     and hands the whole bundle back at every trap.                      *)
(*                                                                        *)
(* THE LOW [NSTD] SLOTS ARE TRACKED TOTALLY; THE REST ONLY WHEN OPEN.      *)
(* That is the one design decision in this file and everything follows     *)
(* from it.  Above [NSTD] a closed slot is ABSENT from [ufd_map], so       *)
(* [open] MINTS a handle ([ghost_map_insert], which needs the key free)    *)
(* and [close] SPENDS one ([ghost_map_delete], and an authority cannot     *)
(* shrink without the element): “a program that closed a descriptor must   *)
(* stop claiming it is open” is not a policy there, it is the only thing   *)
(* the ghost state can express.  Below [NSTD] the key is ALWAYS present,   *)
(* so the fragment is a total claim on the slot -- [ufd γ k st] when it is *)
(* open, [ufd_shut γ k] when it is closed -- and close/open UPDATE it      *)
(* rather than deleting and re-inserting.                                  *)
(*                                                                        *)
(* WHY THE ASYMMETRY IS THE POINT.  [fdalloc] returns the LOWEST closed    *)
(* descriptor ([UsysMemOk.usys_fd_ok]'s open/dup/pipe rows say so), so a   *)
(* program can predict the number it gets back exactly when it knows the   *)
(* states of a PREFIX of the table.  Knowing a slot is OPEN is what a      *)
(* handle already said; knowing a slot is CLOSED is the fact that had no   *)
(* carrier at all, because absence is not ownable and [UkRun.urun] binds   *)
(* the table existentially.  [ufd_shut] is that carrier, and it is minted  *)
(* by exactly the operation that makes it true: [close].  Hence sh's       *)
(*   close(1); dup(p[1])   ==>   the copy lands on 1                       *)
(* is arithmetic on the three-element list a program carries in [ustd].    *)
(*                                                                        *)
(* WHAT THE ALLOCATING RULES NEED FROM THE KERNEL: [fd_least_closed], the  *)
(* fdalloc scan itself.  A rule that said only “the slot it returned was   *)
(* free” would license a syscall to retype a descriptor the program is     *)
(* already holding a handle for, and would leave the number unpredictable. *)
(* See [UsysMemOk.usys_fd_ok]'s three allocating arms.                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import FdSlots.
Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------- *)
(* §0  HOW WIDE THE TOTALLY-TRACKED WINDOW IS.                           *)
(* ------------------------------------------------------------------- *)
(* [NSTD] is how many descriptors at the bottom of the table are tracked
   TOTALLY -- open or closed -- rather than only when open.  It is NOT a
   kernel constant: nothing in xv6 mentions it, no kernel proof may read
   it, and that is why it lives here rather than beside [NOFILE].  It is
   the width of the window a USER program has to know the exact state of
   in order to predict where the next [fdalloc] lands.

   THREE, because that is where the code's dependence stops.  init opens
   the console as fd 0 and dups it to 1 and 2; sh's REDIR is [close(0 or
   1); open(...)] and each half of its PIPE is [close(0 or 1); dup(pipe
   end)].  No xv6 program closes a descriptor of 3 or above and then
   depends on the NUMBER the next allocation returns.  If one ever does,
   raise this constant: nothing but the width of a program's ledger
   ([ustd]) changes. *)
Definition NSTD : nat := 3%nat.

Lemma NSTD_le_NOFILE : (NSTD <= NOFILE)%nat.
Proof. unfold NSTD, NOFILE. lia. Qed.

(* a fresh process's standard streams are three closed slots, which is what
   makes init's first [open] land on descriptor 0. *)
Lemma fdt0_take : take NSTD fdt0 = replicate NSTD FdClosed.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------- *)
(* §1  THE MAP A DESCRIPTOR LIST DENOTES.                                *)
(* ------------------------------------------------------------------- *)
(* [map_seq 0] is the list read as a map on its indices; the filter keeps
   every slot below [NSTD] and, above it, only the open ones.  Both halves
   are stdpp's, so every fact below is one rewrite of [lookup_map_seq_0]
   and one of [map_lookup_filter]. *)
Definition ufd_map (fdv : list fdstate) : gmap nat fdstate :=
  filter (fun kv => (kv.1 < NSTD)%nat \/ kv.2 <> FdClosed) (map_seq 0 fdv).

(* ...and the part of it ABOVE the standard streams, which is what a set of
   ordinary handles can cover.  [ufd_map] is this plus the prefix, and
   [ufd_map_split] is the join. *)
Definition ufd_map_hi (fdv : list fdstate) : gmap nat fdstate :=
  filter (fun kv => kv.2 <> FdClosed) (map_seq NSTD (drop NSTD fdv)).

(* the reading, in the only direction anything needs it *)
Lemma ufd_map_lookup (fdv : list fdstate) (fd : nat) (st : fdstate) :
  ufd_map fdv !! fd = Some st <->
  fdv !! fd = Some st /\ ((fd < NSTD)%nat \/ st <> FdClosed).
Proof.
  unfold ufd_map. rewrite map_lookup_filter_Some lookup_map_seq_0. reflexivity.
Qed.

Lemma ufd_map_lookup_1 (fdv : list fdstate) (fd : nat) (st : fdstate) :
  ufd_map fdv !! fd = Some st -> fdv !! fd = Some st.
Proof. intros H. exact (proj1 (proj1 (ufd_map_lookup fdv fd st) H)). Qed.

(* a std slot is present WHATEVER its state -- the whole difference *)
Lemma ufd_map_std (fdv : list fdstate) (fd : nat) (st : fdstate) :
  (fd < NSTD)%nat -> fdv !! fd = Some st -> ufd_map fdv !! fd = Some st.
Proof. intros Hlt Hl. apply ufd_map_lookup. split; [exact Hl | by left]. Qed.

(* ...and a closed slot ABOVE the prefix is absent, which is what makes
   minting a handle for it an insert. *)
Lemma ufd_map_lookup_None (fdv : list fdstate) (fd : nat) :
  (NSTD <= fd)%nat -> fdv !! fd = Some FdClosed -> ufd_map fdv !! fd = None.
Proof.
  intros Hge Hc. destruct (ufd_map fdv !! fd) as [st |] eqn:He; [| reflexivity].
  exfalso. apply ufd_map_lookup in He as [Hl [Hlt | Hne]]; [lia |].
  rewrite Hc in Hl. injection Hl as <-. exact (Hne eq_refl).
Qed.

(* [map_seq] commutes with a list insert INSIDE the list; stdpp states it
   the other way round. *)
Lemma map_seq_insert0 (fdv : list fdstate) (fd : nat) (st : fdstate) :
  (fd < length fdv)%nat ->
  map_seq 0 (<[fd := st]> fdv) = <[fd := st]> (map_seq 0 fdv : gmap nat fdstate).
Proof. intros Hlt. symmetry. by apply insert_map_seq_0. Qed.

(* THE TWO WAYS THE FILTER REACTS TO AN INSERT, and there are only two: the
   slot stays in the map (it is a std slot, or it became open), or it leaves
   it (a tail slot that became closed). *)
Lemma ufd_map_insert (fdv : list fdstate) (fd : nat) (st : fdstate) :
  (fd < length fdv)%nat -> ((fd < NSTD)%nat \/ st <> FdClosed) ->
  ufd_map (<[fd := st]> fdv) = <[fd := st]> (ufd_map fdv).
Proof.
  intros Hlt HP. unfold ufd_map. rewrite (map_seq_insert0 fdv fd st Hlt).
  apply map_filter_insert_True. exact HP.
Qed.

Lemma ufd_map_insert_closed (fdv : list fdstate) (fd : nat) :
  (fd < length fdv)%nat -> (NSTD <= fd)%nat ->
  ufd_map (<[fd := FdClosed]> fdv) = delete fd (ufd_map fdv).
Proof.
  intros Hlt Hge. unfold ufd_map. rewrite (map_seq_insert0 fdv fd FdClosed Hlt).
  rewrite map_filter_insert_False;
    [| cbn; intros [Hc | Hc]; [lia | exact (Hc eq_refl)]].
  apply map_filter_delete.
Qed.

(* THE SPLIT: the prefix, whole, and the open slots above it. *)
Lemma ufd_map_split_disj (fdv : list fdstate) :
  map_seq 0 (take NSTD fdv) ##ₘ ufd_map_hi fdv.
Proof.
  apply (map_disjoint_weaken_r _ _ (map_seq NSTD (drop NSTD fdv))).
  - apply map_seq_disjoint. rewrite length_take. lia.
  - apply map_filter_subseteq.
Qed.

Lemma ufd_map_split (fdv : list fdstate) :
  (NSTD <= length fdv)%nat ->
  ufd_map fdv = map_seq 0 (take NSTD fdv) ∪ ufd_map_hi fdv.
Proof.
  intros Hn.
  assert (Hlen : length (take NSTD fdv) = NSTD) by (rewrite length_take; lia).
  unfold ufd_map, ufd_map_hi.
  rewrite <- (take_drop NSTD fdv) at 1.
  rewrite map_seq_app Hlen Nat.add_0_l.
  rewrite map_filter_union; [| apply map_seq_disjoint; rewrite Hlen; lia].
  f_equal.
  - apply map_filter_id. intros i x Hi. cbn.
    rewrite lookup_map_seq_0 in Hi. apply lookup_lt_Some in Hi.
    left. lia.
  - apply map_filter_ext. intros i x Hi. cbn.
    apply lookup_map_seq_Some in Hi as [Hle _].
    split; [ intros [Hlt | H]; [lia | exact H] | intros H; by right ].
Qed.

Lemma ufd_map_hi_open (fdv : list fdstate) (fd : nat) (st : fdstate) :
  ufd_map_hi fdv !! fd = Some st -> st <> FdClosed /\ (NSTD <= fd)%nat.
Proof.
  unfold ufd_map_hi. rewrite map_lookup_filter_Some. intros [Hm Hne].
  split; [exact Hne |].
  exact (proj1 (proj1 (lookup_map_seq_Some _ _ _ _) Hm)).
Qed.

(* the premise the fork mint takes, out of the two facts a caller has *)
Lemma ufd_map_hi_sub (fdv : list fdstate) (D : gmap nat fdstate) :
  D ⊆ ufd_map fdv ->
  (forall k : nat, is_Some (D !! k) -> (NSTD <= k)%nat) ->
  D ⊆ ufd_map_hi fdv.
Proof.
  intros Hsub Hlo.
  pose proof (proj1 (map_subseteq_spec D (ufd_map fdv)) Hsub) as Hs.
  apply (proj2 (map_subseteq_spec D (ufd_map_hi fdv))). intros i x Hi.
  assert (Hge : (NSTD <= i)%nat) by (apply Hlo; by exists x).
  apply Hs in Hi. apply ufd_map_lookup in Hi as [Hl [Hlt | Hne]]; [lia |].
  unfold ufd_map_hi. apply map_lookup_filter_Some. split; [| exact Hne].
  apply lookup_map_seq_Some. split; [exact Hge |].
  rewrite lookup_drop.
  replace (NSTD + (i - NSTD))%nat with i by lia. exact Hl.
Qed.

(* ------------------------------------------------------------------- *)
(* §2  THE RESOURCE.                                                     *)
(* ------------------------------------------------------------------- *)
(* THE CELLS OF THE ONE GHOST MAP.  Key [Some k] is descriptor [k]'s slot
   (the fragments below); key [None] is the WHOLE TABLE (design/seccomp.md
   S3 ruling G2): half of it rides in [ufd_auth], the other half in the
   LEDGER ([ustd] / [ustd_at]), so a program that holds its ledger at a
   named view KNOWS its whole table up to closes above the standard
   streams ([tab_le]) -- the fact [urun] otherwise hides.  One map, one
   gname: the record and every signature over [ufd_auth] are unchanged. *)
Inductive ufdcell : Type :=
| UCSlot (st : fdstate)
| UCTab (v : list fdstate).

(* THE TABLE VIEW'S RELATION TO THE TABLE.  The view [v] is the table as
   of the last move the ledger saw; a close ABOVE the standard streams
   spends only a tail handle (no ledger), so it may have closed a slot the
   view still shows open.  Nothing else moves the table without the
   ledger. *)
Definition tab_le (fdv v : list fdstate) : Prop :=
  (length fdv = length v)%nat /\
  (forall (k : nat) (st : fdstate), fdv !! k = Some st ->
     v !! k = Some st \/ (st = FdClosed /\ (NSTD <= k)%nat)).

Lemma tab_le_refl (fdv : list fdstate) : tab_le fdv fdv.
Proof. split; [reflexivity | intros k st H; by left]. Qed.

Lemma tab_le_close_hi (fdv v : list fdstate) (fd : nat) :
  (NSTD <= fd)%nat -> tab_le fdv v -> tab_le (<[fd := FdClosed]> fdv) v.
Proof.
  intros Hge [Hl H]. split; [by rewrite length_insert |].
  intros k st Hk. destruct (decide (k = fd)) as [-> | Hne].
  - apply list_lookup_insert_Some in Hk as [(_ & <- & _) | [Hne _]];
      [ by right | exfalso; exact (Hne eq_refl) ].
  - rewrite list_lookup_insert_ne in Hk; [| lia]. exact (H k st Hk).
Qed.

(* A VIEW WHOSE ROWS ARE CLOSED OR A DEVICE (seccomp S4): what sh's ledger
   carries of its whole table -- no inode and no pipe row, which is what the
   seccomp child needs of the table it execs with ([UexecSecc.secc_rows]).
   sh's parent only ever holds the console, and every step of its loop
   keeps the view; the console preamble's opens re-set it to a table that
   still satisfies it ([ush_view_ok_open]). *)
Definition ush_view_ok (v : list fdstate) : Prop :=
  Forall (fun st => st = FdClosed \/ exists (r w : bool) (mj : Z),
                      st = FdOpen r w (FdDevice mj)) v.

(* a table under an ok view is ok: a slot the view shows may have closed *)
Lemma ush_view_ok_tab (sts v : list fdstate) :
  ush_view_ok v -> tab_le sts v -> ush_view_ok sts.
Proof.
  intros Hv [_ Hle]. apply Forall_lookup. intros k st Hk.
  destruct (Hle k st Hk) as [Hv' | [-> _]]; [| by left].
  exact (proj1 (Forall_lookup _ _) Hv k st Hv').
Qed.

(* ...an allocation of a device keeps it *)
Lemma ush_view_ok_open (fdv v : list fdstate) (fd : nat) (r w : bool) (mj : Z) :
  ush_view_ok v -> tab_le fdv v ->
  ush_view_ok (<[fd := FdOpen r w (FdDevice mj)]> fdv).
Proof.
  intros Hv Hle. pose proof (ush_view_ok_tab fdv v Hv Hle) as Hf.
  apply Forall_insert; [exact Hf | right; by exists r, w, mj].
Qed.

(* ...and so does a copy of a row the table already has (dup) *)
Lemma ush_view_ok_dup (fdv v : list fdstate) (fd i : nat) (st : fdstate) :
  ush_view_ok v -> tab_le fdv v -> fdv !! i = Some st ->
  ush_view_ok (<[fd := st]> fdv).
Proof.
  intros Hv Hle Hi. pose proof (ush_view_ok_tab fdv v Hv Hle) as Hf.
  apply Forall_insert; [exact Hf |].
  exact (proj1 (Forall_lookup _ _) Hf i st Hi).
Qed.

(* the standard streams are never closed behind the view's back *)
Lemma tab_le_take (fdv v : list fdstate) :
  tab_le fdv v -> take NSTD fdv = take NSTD v.
Proof.
  intros [Hl H]. apply list_eq. intros i.
  destruct (decide (i < NSTD)%nat) as [Hlt | Hge].
  - rewrite !lookup_take; [| exact Hlt | exact Hlt].
    destruct (fdv !! i) as [st |] eqn:Hi.
    + destruct (H i st Hi) as [-> | [_ Hc]]; [reflexivity | lia].
    + symmetry. apply lookup_ge_None. apply lookup_ge_None in Hi. lia.
  - rewrite !lookup_take_ge; [reflexivity | lia | lia].
Qed.

(* the slot map and the table cell, as the one map the ghost holds *)
Definition ufd_gm (S : gmap nat fdstate) (v : list fdstate)
    : gmap (option nat) ufdcell :=
  <[None := UCTab v]> (kmap Some (UCSlot <$> S)).

Lemma ufd_gm_some (S : gmap nat fdstate) (v : list fdstate) (k : nat) :
  ufd_gm S v !! Some k = UCSlot <$> S !! k.
Proof.
  unfold ufd_gm. rewrite lookup_insert_ne; [| discriminate].
  rewrite (lookup_kmap Some). by rewrite lookup_fmap.
Qed.

Lemma ufd_gm_none (S : gmap nat fdstate) (v : list fdstate) :
  ufd_gm S v !! None = Some (UCTab v).
Proof. unfold ufd_gm. by rewrite lookup_insert. Qed.

Lemma ufd_gm_insert (S : gmap nat fdstate) (v : list fdstate) (k : nat)
    (st : fdstate) :
  <[Some k := UCSlot st]> (ufd_gm S v) = ufd_gm (<[k := st]> S) v.
Proof.
  unfold ufd_gm. rewrite insert_commute; [| discriminate].
  f_equal. rewrite fmap_insert. by rewrite (kmap_insert Some).
Qed.

Lemma ufd_gm_delete (S : gmap nat fdstate) (v : list fdstate) (k : nat) :
  delete (Some k) (ufd_gm S v) = ufd_gm (delete k S) v.
Proof.
  unfold ufd_gm. rewrite delete_insert_ne; [| discriminate].
  f_equal. rewrite fmap_delete. by rewrite (kmap_delete Some).
Qed.

Lemma ufd_gm_retab (S : gmap nat fdstate) (v w : list fdstate) :
  <[None := UCTab w]> (ufd_gm S v) = ufd_gm S w.
Proof. unfold ufd_gm. by rewrite insert_insert. Qed.

Class ufdG (Σ : gFunctors) := UfdG { ufd_ghost_mapG :: ghost_mapG Σ (option nat) ufdcell }.
Definition ufdΣ : gFunctors := #[ ghost_mapΣ (option nat) ufdcell ].
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
  (* ...AND THE TABLE VIEW'S HALF, at a view the table is [tab_le] of: the
     other half is in the program's ledger. *)
  Definition ufd_auth (γf : gname) (fdv : list fdstate) : iProp Σ :=
    (∃ v : list fdstate,
       ghost_map_auth γf 1 (ufd_gm (ufd_map fdv) v) ∗ ⌜length fdv = NOFILE⌝ ∗
       ⌜tab_le fdv v⌝ ∗ @None nat ↪[γf]{#1/2} UCTab v)%I.

  Lemma ufd_auth_len (γf : gname) (fdv : list fdstate) :
    ufd_auth γf fdv -∗ ⌜length fdv = NOFILE⌝.
  Proof using . iIntros "(%v & _ & $ & _)". Qed.

  (* THE PROGRAM'S HALF OF THE TABLE VIEW *)
  Definition utab (γf : gname) (v : list fdstate) : iProp Σ :=
    (@None nat ↪[γf]{#1/2} UCTab v)%I.

  Global Instance utab_timeless γf v : Timeless (utab γf v).
  Proof using . apply _. Qed.

  Lemma utab_agree (γf : gname) (fdv v : list fdstate) :
    ufd_auth γf fdv -∗ utab γf v -∗ ⌜tab_le fdv v⌝.
  Proof using .
    iIntros "(%w & Ha & _ & %Hle & _) Ht".
    iDestruct (ghost_map_lookup with "Ha Ht") as %He.
    rewrite ufd_gm_none in He. injection He as ->. by iPureIntro.
  Qed.

  (* THE ONE WAY THE VIEW MOVES: both halves in hand, re-set to the table *)
  Local Lemma ufd_retab (γf : gname) (S : gmap nat fdstate) (v v' w : list fdstate) :
    ghost_map_auth γf 1 (ufd_gm S v) -∗ @None nat ↪[γf]{#1/2} UCTab v -∗
    @None nat ↪[γf]{#1/2} UCTab v' ==∗
    ghost_map_auth γf 1 (ufd_gm S w) ∗ @None nat ↪[γf]{#1/2} UCTab w ∗
    @None nat ↪[γf]{#1/2} UCTab w.
  Proof using .
    iIntros "Ha H1 H2".
    iCombine "H1 H2" as "H" gives %[_ Heq]. injection Heq as <-.
    rewrite dfrac_op_own Qp.half_half.
    iMod (ghost_map_update (UCTab w) with "Ha H") as "[Ha [H1 H2]]".
    rewrite ufd_gm_retab. by iFrame.
  Qed.

  (* THE FRAGMENT is [fd ↪[γf] st], the raw claim on one slot at one state,
     and the two predicates below are it, READ.

     ...the OPEN HANDLE, which is what a program carries for a descriptor it
     opened.  IT IS A TAIL HANDLE: [NSTD <= fd] rides inside it, because a
     standard stream's fragment lives in the ledger and nowhere else, and
     because it is what lets [close] spend a handle WITHOUT the ledger -- a
     tail slot leaves the map entirely, so nothing has to be written back,
     which is what keeps close out of the way of every program that opens a
     file and closes it without caring about its standard streams.  Every
     producer has the bound in hand ([ufd_map_hi]'s keys are above [NSTD] by
     construction, and an allocation that hands back a handle at all
     allocated from above), so carrying it costs nothing. *)
  Definition ufd (γf : gname) (fd : nat) (st : fdstate) : iProp Σ :=
    (Some fd ↪[γf] UCSlot st ∗ ⌜st <> FdClosed /\ (NSTD <= fd)%nat⌝)%I.

  (* ...and the NEGATIVE half, which only a std slot has: "descriptor [fd] is
     closed, and this is my claim on that fact".  [close] mints it and the
     next [open]/[dup] spends it -- which is the only way the two can be
     tied together, since the syscall in between picks the descriptor. *)
  Definition ufd_shut (γf : gname) (fd : nat) : iProp Σ :=
    (Some fd ↪[γf] UCSlot FdClosed)%I.

  Global Instance ufd_timeless γf fd st : Timeless (ufd γf fd st).
  Proof using . apply _. Qed.
  Global Instance ufd_shut_timeless γf fd : Timeless (ufd_shut γf fd).
  Proof using . apply _. Qed.

  (* THE LEDGER: the whole of the standard streams, as a list of states.
     This is what a program that means to redirect carries, and it is the
     resource the three allocating leaves read to say WHICH descriptor came
     back.  It is one resource rather than [NSTD] because every allocating
     row consumes all of it: the scan reads slot 0, then 1, then 2, and a
     program holding only some of them could not compute the answer. *)
  Definition ustd_raw (γf : gname) (l : list fdstate) : iProp Σ :=
    (⌜length l = NSTD⌝ ∗
     [∗ map] k ↦ st ∈ (map_seq 0 l : gmap nat fdstate), Some k ↪[γf] UCSlot st)%I.

  (* ...AND THE LEDGER CARRIES THE PROGRAM'S HALF OF THE TABLE VIEW
     (design/seccomp.md, S3 ruling G2): every move of the table but a tail
     close takes the ledger already, so the view moves with it and no
     statement over [ustd] changes.  [ustd] forgets the view; [ustd_at]
     names it, and is what a program that must know its whole table
     carries (the seccomp child, through [UkFork.wp_uk_ecall_fork_at]). *)
  Definition ustd (γf : gname) (l : list fdstate) : iProp Σ :=
    (ustd_raw γf l ∗ ∃ v : list fdstate, utab γf v)%I.

  Definition ustd_at (γf : gname) (l : list fdstate) (v : list fdstate) : iProp Σ :=
    (ustd_raw γf l ∗ utab γf v)%I.

  Lemma ustd_at_ustd (γf : gname) (l v : list fdstate) :
    ustd_at γf l v -∗ ustd γf l.
  Proof using . iIntros "[$ H]". by iExists v. Qed.

  Lemma ustd_ustd_at (γf : gname) (l : list fdstate) :
    ustd γf l -∗ ∃ v, ustd_at γf l v.
  Proof using . iIntros "[H [%v Ht]]". iExists v. iFrame. Qed.

  Global Instance ustd_timeless γf l : Timeless (ustd γf l).
  Proof using . apply _. Qed.
  Global Instance ustd_at_timeless γf l v : Timeless (ustd_at γf l v).
  Proof using . apply _. Qed.
  (* THE LEDGER AT AN OK VIEW, or the application's taint [T] (seccomp S4):
     what sh and /init carry ([UkSh.ush_std] is this at sh's record). *)
  Definition ustd_ok (T : iProp Σ) (γf : gname) (l : list fdstate) : iProp Σ :=
    (∃ v : list fdstate, (⌜ush_view_ok v⌝ ∨ T) ∗ ustd_at γf l v)%I.

  Global Instance ustd_ok_timeless T γf l `{!Timeless T} : Timeless (ustd_ok T γf l).
  Proof using . rewrite /ustd_ok. apply _. Qed.

  Lemma ustd_ok_ustd (T : iProp Σ) (γf : gname) (l : list fdstate) :
    ustd_ok T γf l -∗ ustd γf l.
  Proof using . iIntros "[%v [_ H]]". iApply (ustd_at_ustd with "H"). Qed.

  Lemma ustd_ok_taint (T : iProp Σ) (γf : gname) (l : list fdstate) :
    T -∗ ustd γf l -∗ ustd_ok T γf l.
  Proof using .
    iIntros "HT H". iDestruct (ustd_ustd_at with "H") as (v) "H".
    iExists v. iFrame "H". by iRight.
  Qed.


  Lemma ustd_len (γf : gname) (l : list fdstate) :
    ustd γf l -∗ ⌜length l = NSTD⌝.
  Proof using . iIntros "[[$ _] _]". Qed.

  (* the ledger at a named view reads the WHOLE table *)
  Lemma ustd_at_tab (γf : gname) (fdv l v : list fdstate) :
    ufd_auth γf fdv -∗ ustd_at γf l v -∗ ⌜tab_le fdv v⌝.
  Proof using . iIntros "Ha [_ Ht]". iApply (utab_agree with "Ha Ht"). Qed.

  (* a handle READS the view: this is the lemma that makes a fragment worth
     carrying, and it is why the authority has to sit inside [urun] rather
     than beside it. *)
  Lemma ufd_slot_agree (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ Some fd ↪[γf] UCSlot st -∗ ⌜fdv !! fd = Some st⌝.
  Proof using .
    iIntros "(%v & Ha & _) Hf".
    iDestruct (ghost_map_lookup with "Ha Hf") as %He.
    rewrite ufd_gm_some in He.
    destruct (ufd_map fdv !! fd) as [st' |] eqn:Hm; [| discriminate].
    injection He as ->.
    iPureIntro. exact (ufd_map_lookup_1 fdv fd st Hm).
  Qed.

  Lemma ufd_agree (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st -∗ ⌜fdv !! fd = Some st⌝.
  Proof using . iIntros "Ha [Hf _]". iApply (ufd_slot_agree with "Ha Hf"). Qed.

  (* the two facts the handle carries: the descriptor is OPEN, and it is
     never a standard stream *)
  Lemma ufd_ne (γf : gname) (fd : nat) (st : fdstate) :
    ufd γf fd st -∗ ⌜st <> FdClosed⌝.
  Proof using . iIntros "[_ %H]". iPureIntro. exact (proj1 H). Qed.

  Lemma ufd_ge (γf : gname) (fd : nat) (st : fdstate) :
    ufd γf fd st -∗ ⌜(NSTD <= fd)%nat⌝.
  Proof using . iIntros "[_ %H]". iPureIntro. exact (proj2 H). Qed.

  Lemma ufd_shut_agree (γf : gname) (fdv : list fdstate) (fd : nat) :
    ufd_auth γf fdv -∗ ufd_shut γf fd -∗ ⌜fdv !! fd = Some FdClosed⌝.
  Proof using . iIntros "Ha Hf". iApply (ufd_slot_agree with "Ha Hf"). Qed.

  (* two fragments for the same descriptor cannot both exist -- the map is
     at the full fraction, so a fragment is exclusive.  Read at [ufd] and
     [ufd_shut] it says a program cannot hold "fd is open" and "fd is
     closed" at once, which is what makes the ledger's reading sound. *)
  Lemma ufd_slot_excl (γf : gname) (fd : nat) (st st' : fdstate) :
    Some fd ↪[γf] UCSlot st -∗ Some fd ↪[γf] UCSlot st' -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
    destruct (Hne eq_refl).
  Qed.

  Lemma ufd_excl (γf : gname) (fd : nat) (st st' : fdstate) :
    ufd γf fd st -∗ ufd γf fd st' -∗ False.
  Proof using . iIntros "[H1 _] [H2 _]". iApply (ufd_slot_excl with "H1 H2"). Qed.

  (* ------------------------------------------------------------------ *)
  (* §2½  READING AND WRITING ONE SLOT OF THE LEDGER.                     *)
  (* ------------------------------------------------------------------ *)
  Lemma ustd_acc (γf : gname) (l : list fdstate) (k : nat) (st : fdstate) :
    l !! k = Some st ->
    ustd γf l -∗
    Some k ↪[γf] UCSlot st ∗
    (∀ st' : fdstate, Some k ↪[γf] UCSlot st' -∗ ustd γf (<[k := st']> l)).
  Proof using .
    iIntros (Hk) "[[%Hlen Hm] Ht]". iFrame "Ht".
    assert (Hm : (map_seq 0 l : gmap nat fdstate) !! k = Some st)
      by (by rewrite lookup_map_seq_0).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hm with "Hm") as "[$ Hback]".
    iIntros (st') "Hs". iDestruct ("Hback" with "Hs") as "Hm".
    rewrite (insert_map_seq_0 l k st' (lookup_lt_Some _ _ _ Hk)).
    iFrame "Hm". iPureIntro. by rewrite length_insert.
  Qed.

  (* ...at a named view: a slot move leaves the view where it was *)
  Lemma ustd_at_acc (γf : gname) (l v : list fdstate) (k : nat) (st : fdstate) :
    l !! k = Some st ->
    ustd_at γf l v -∗
    Some k ↪[γf] UCSlot st ∗
    (∀ st' : fdstate, Some k ↪[γf] UCSlot st' -∗ ustd_at γf (<[k := st']> l) v).
  Proof using .
    iIntros (Hk) "[[%Hlen Hm] Ht]". iFrame "Ht".
    assert (Hm : (map_seq 0 l : gmap nat fdstate) !! k = Some st)
      by (by rewrite lookup_map_seq_0).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hm with "Hm") as "[$ Hback]".
    iIntros (st') "Hs". iDestruct ("Hback" with "Hs") as "Hm".
    rewrite (insert_map_seq_0 l k st' (lookup_lt_Some _ _ _ Hk)).
    iFrame "Hm". iPureIntro. by rewrite length_insert.
  Qed.

  (* THE LEDGER READS THE VIEW, whole: this is what turns "my three states"
     into "the table's first three slots", and it is the fact every
     lowest-descriptor argument starts from. *)
  Lemma ustd_agree (γf : gname) (fdv l : list fdstate) :
    ufd_auth γf fdv -∗ ustd γf l -∗ ⌜take NSTD fdv = l⌝.
  Proof using .
    iIntros "(%v & Ha & %Hlen & _) [[%Hl Hm] _]".
    iAssert (⌜forall (i : nat) (st : fdstate),
               (map_seq 0 l : gmap nat fdstate) !! i = Some st ->
               ufd_map fdv !! i = Some st⌝)%I as %Hsub'.
    { iIntros (i st Hi).
      iDestruct (big_sepM_lookup with "Hm") as "Hf"; [exact Hi |].
      iDestruct (ghost_map_lookup with "Ha Hf") as %He.
      rewrite ufd_gm_some in He.
      destruct (ufd_map fdv !! i) as [st' |]; [| discriminate].
      injection He as ->. by iPureIntro. }
    assert (Hsub : (map_seq 0 l : gmap nat fdstate) ⊆ ufd_map fdv)
      by (apply map_subseteq_spec; exact Hsub').
    iPureIntro.
    apply list_eq. intros i.
    destruct (decide (i < NSTD)%nat) as [Hlt | Hge].
    - rewrite lookup_take; [| exact Hlt].
      destruct (l !! i) as [st |] eqn:Hi.
      + assert (Hm : (map_seq 0 l : gmap nat fdstate) !! i = Some st)
          by (by rewrite lookup_map_seq_0).
        exact (ufd_map_lookup_1 _ _ _
                 (proj1 (map_subseteq_spec _ _) Hsub i st Hm)).
      + exfalso. apply lookup_ge_None in Hi. lia.
    - rewrite lookup_take_ge; [| lia].
      symmetry. apply lookup_ge_None. lia.
  Qed.

  Lemma ustd_at_agree (γf : gname) (fdv l v : list fdstate) :
    ufd_auth γf fdv -∗ ustd_at γf l v -∗ ⌜take NSTD fdv = l⌝.
  Proof using .
    iIntros "Ha [Hl Ht]". iApply (ustd_agree with "Ha [Hl Ht]").
    iFrame "Hl". by iExists v.
  Qed.

  (* the std fragments live IN the ledger, so nobody else can hold one *)
  Lemma ustd_ufd_excl (γf : gname) (l : list fdstate) (k : nat) (st : fdstate) :
    (k < NSTD)%nat -> ustd γf l -∗ ufd γf k st -∗ False.
  Proof using .
    iIntros (Hk) "Hl [Hs _]".
    iDestruct (ustd_len with "Hl") as %Hlen.
    destruct (l !! k) as [st' |] eqn:Hi;
      [| exfalso; apply lookup_ge_None in Hi; lia].
    iDestruct (ustd_acc γf l k st' Hi with "Hl") as "[Hs' _]".
    iApply (ufd_slot_excl with "Hs' Hs").
  Qed.

  (* A FRAGMENT NAMES A DESCRIPTOR A C [int] CAN HOLD.  This is the fact an
     argument-register premise is proved from. *)
  Lemma ufd_slot_bound (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ Some fd ↪[γf] UCSlot st -∗ ⌜(fd < NOFILE)%nat⌝.
  Proof using .
    iIntros "Ha Hh". iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ufd_slot_agree with "Ha Hh") as %Hl.
    iPureIntro. rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hl).
  Qed.

  Lemma ufd_bound (γf : gname) (fdv : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st -∗ ⌜(fd < NOFILE)%nat⌝.
  Proof using . iIntros "Ha [Hh _]". iApply (ufd_slot_bound with "Ha Hh"). Qed.

  (* ------------------------------------------------------------------- *)
  (* §3  A PROGRAM'S CLAIM ON ONE DESCRIPTOR, WHEREVER IT LIVES.           *)
  (* ------------------------------------------------------------------- *)
  (* close and dup name a descriptor the program already has; that claim is
     a LEDGER ENTRY for a standard stream and a HANDLE for anything else.
     Writing the disjunction once is what lets one rule serve both -- and
     both arms are used on the first day: init's [dup(0)] takes the left,
     sh's [dup(p[1])] takes the right. *)
  Definition ufd_own (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate)
    : iProp Σ :=
    (⌜(fd < NSTD)%nat /\ l !! fd = Some st⌝ ∨ ufd γf fd st)%I.

  Lemma ufd_own_std (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate) :
    (fd < NSTD)%nat -> l !! fd = Some st -> ⊢ ufd_own γf l fd st.
  Proof using . intros H1 H2. iLeft. iPureIntro. by split. Qed.

  Lemma ufd_own_hi (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate) :
    ufd γf fd st -∗ ufd_own γf l fd st.
  Proof using . iIntros "H". by iRight. Qed.

  (* a claim survives an update to a DIFFERENT slot of the ledger *)
  Lemma ufd_own_insert_ne (γf : gname) (l : list fdstate) (fd k : nat)
      (st v : fdstate) :
    k <> fd -> ufd_own γf l fd st -∗ ufd_own γf (<[k := v]> l) fd st.
  Proof using .
    iIntros (Hne) "[[%Hlt %Hl] | H]"; [| by iRight].
    iLeft. iPureIntro. split; [exact Hlt |].
    rewrite list_lookup_insert_ne; [exact Hl | exact Hne].
  Qed.

  (* what a claim says about the table -- and, on the handle arm, that the
     descriptor is NOT a standard stream, since those fragments are in the
     ledger the caller also handed in. *)
  Lemma ufd_own_agree (γf : gname) (fdv l : list fdstate) (fd : nat) (st : fdstate) :
    ufd_auth γf fdv -∗ ustd γf l -∗ ufd_own γf l fd st -∗
    ⌜fdv !! fd = Some st /\ (fd < NOFILE)%nat⌝.
  Proof using .
    iIntros "Ha Hl Ho".
    iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ustd_agree with "Ha Hl") as %Hst.
    iDestruct "Ho" as "[[%Hlt %Hl] | Hh]".
    - iPureIntro.
      assert (Hi : take NSTD fdv !! fd = Some st) by (by rewrite Hst).
      rewrite lookup_take in Hi; [| exact Hlt].
      split; [exact Hi |]. rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hi).
    - iDestruct (ufd_agree with "Ha Hh") as %Hi.
      iDestruct (ufd_bound with "Ha Hh") as %Hb.
      iPureIntro. by split.
  Qed.

  Lemma ufd_own_hi_ge (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate) :
    ustd γf l -∗ ufd γf fd st -∗ ⌜(NSTD <= fd)%nat⌝.
  Proof using . iIntros "_ Hh". iApply (ufd_ge with "Hh"). Qed.

  (* ------------------------------------------------------------------- *)
  (* §3½  WHAT AN ALLOCATION HANDS BACK.                                   *)
  (* ------------------------------------------------------------------- *)
  (* fdalloc scans from 0, so a program that knows its standard streams
     exactly knows where the next descriptor lands: at the first CLOSED one
     if there is one, and otherwise somewhere above them.  [ustd_after] is
     the ledger that leaves, and [ualloc] is the whole result -- the ledger,
     plus either the number (when it landed in the ledger, where the state
     is now recorded and [ustd_open_acc] reads it back as a handle) or a
     fresh handle (when it landed above).

     BOTH ARMS ARE COMPUTED FROM [l], not chosen by the kernel.  That is the
     difference between this and a row that says only "the slot was free":
     at a concrete ledger exactly one arm survives, and a program proof
     never sees the other. *)
  Definition ustd_after (l : list fdstate) (st : fdstate) : list fdstate :=
    match fd_lowest_closed l with
    | Some k => <[k := st]> l
    | None => l
    end.

  (* the ARM alone, without the ledger: which descriptor came back, and the
     handle if it came back from above the standard streams.  Split out
     because pipe allocates TWICE and there is only ever ONE ledger -- its
     post is two arms and one ledger, at the table the second scan ran on. *)
  Definition ualloc_at (γf : gname) (l : list fdstate) (fd : nat)
      (st : fdstate) : iProp Σ :=
    (match fd_lowest_closed l with
     | Some k => ⌜fd = k⌝
     | None => ⌜(NSTD <= fd)%nat⌝ ∗ ufd γf fd st
     end)%I.

  Definition ualloc (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate)
    : iProp Σ :=
    (ustd γf (ustd_after l st) ∗ ualloc_at γf l fd st)%I.

  (* the two readings, one per arm.  A program has [fd_lowest_closed l] by
     computation, so it applies whichever one its own ledger decides. *)
  Lemma ualloc_std (γf : gname) (l : list fdstate) (fd k : nat) (st : fdstate) :
    fd_lowest_closed l = Some k ->
    ualloc γf l fd st -∗ ⌜fd = k⌝ ∗ ustd γf (<[k := st]> l).
  Proof using .
    intros Hk. rewrite /ualloc /ualloc_at /ustd_after Hk.
    iIntros "[Hl %H]". iSplitR; [ by iPureIntro | iExact "Hl" ].
  Qed.

  Lemma ualloc_hi (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate) :
    fd_lowest_closed l = None ->
    ualloc γf l fd st -∗ ⌜(NSTD <= fd)%nat⌝ ∗ ustd γf l ∗ ufd γf fd st.
  Proof using .
    intros Hk. rewrite /ualloc /ualloc_at /ustd_after Hk.
    iIntros "[Hl [%H Hh]]". iSplitR; [ by iPureIntro | iFrame "Hl Hh" ].
  Qed.

  (* the ledger, whichever arm it came out of -- what a leaf that is only
     passing the allocation through needs *)
  Lemma ualloc_ledger (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate) :
    ualloc γf l fd st -∗ ustd γf (ustd_after l st).
  Proof using . iIntros "[$ _]". Qed.

  (* ...AT A NAMED VIEW (seccomp S4): the ledger after the allocation at
     the view [w] the allocation left it at *)
  Definition ualloc_v (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate)
      (w : list fdstate) : iProp Σ :=
    (ustd_at γf (ustd_after l st) w ∗ ualloc_at γf l fd st)%I.

  Lemma ualloc_v_std (γf : gname) (l : list fdstate) (fd k : nat) (st : fdstate)
      (w : list fdstate) :
    fd_lowest_closed l = Some k ->
    ualloc_v γf l fd st w -∗ ⌜fd = k⌝ ∗ ustd_at γf (<[k := st]> l) w.
  Proof using .
    intros Hk. rewrite /ualloc_v /ualloc_at /ustd_after Hk.
    iIntros "[Hl %H]". iSplitR; [ by iPureIntro | iExact "Hl" ].
  Qed.

  Lemma ualloc_v_hi (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate)
      (w : list fdstate) :
    fd_lowest_closed l = None ->
    ualloc_v γf l fd st w -∗ ⌜(NSTD <= fd)%nat⌝ ∗ ustd_at γf l w ∗ ufd γf fd st.
  Proof using .
    intros Hk. rewrite /ualloc_v /ualloc_at /ustd_after Hk.
    iIntros "[Hl [%H Hh]]". iSplitR; [ by iPureIntro | iFrame "Hl Hh" ].
  Qed.

  Lemma ualloc_v_ualloc (γf : gname) (l : list fdstate) (fd : nat) (st : fdstate)
      (w : list fdstate) :
    ualloc_v γf l fd st w -∗ ualloc γf l fd st.
  Proof using .
    rewrite /ualloc_v /ualloc. iIntros "[Hl $]". iApply (ustd_at_ustd with "Hl").
  Qed.

  (* a claim on an OPEN descriptor is never a claim on the slot an
     allocation lands in, which is what lets dup hand its source back at the
     ledger the allocation left. *)
  Lemma ufd_own_ne_shut (γf : gname) (l : list fdstate) (fd k : nat)
      (st : fdstate) :
    st <> FdClosed -> l !! k = Some FdClosed ->
    ustd γf l -∗ ufd_own γf l fd st -∗ ⌜k <> fd⌝.
  Proof using .
    iIntros (Hne Hk) "Hl Ho".
    iDestruct (ustd_len with "Hl") as %Hlen.
    iDestruct "Ho" as "[[%Hlt %Hl] | Hh]".
    - iPureIntro. intros Heq. subst k.
      rewrite Hl in Hk. injection Hk as Hst. exact (Hne Hst).
    - iDestruct (ufd_own_hi_ge with "Hl Hh") as %Hge.
      iPureIntro. pose proof (lookup_lt_Some _ _ _ Hk). lia.
  Qed.

  (* ...and the same fact in the form the allocating leaves apply it *)
  Lemma ufd_own_ne_lowest (γf : gname) (l : list fdstate) (fd0 : nat)
      (st : fdstate) :
    st <> FdClosed ->
    ustd γf l -∗ ufd_own γf l fd0 st -∗
    ⌜forall k : nat, fd_lowest_closed l = Some k -> k <> fd0⌝.
  Proof using .
    iIntros (Hne) "Hl Ho".
    destruct (fd_lowest_closed l) as [k0 |] eqn:Hk0;
      [| iPureIntro; intros k Hk; discriminate ].
    iDestruct (ufd_own_ne_shut γf l fd0 k0 st Hne
                 (fd_lowest_closed_is_closed l k0 Hk0) with "Hl Ho") as %Hne0.
    iPureIntro. intros k Hk. injection Hk as Heq. subst k0. exact Hne0.
  Qed.

  Lemma ufd_own_after (γf : gname) (l : list fdstate) (fd0 : nat)
      (st st' : fdstate) :
    (forall k : nat, fd_lowest_closed l = Some k -> k <> fd0) ->
    ufd_own γf l fd0 st -∗ ufd_own γf (ustd_after l st') fd0 st.
  Proof using .
    intros Hne. rewrite /ustd_after.
    destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| iIntros "$"].
    iApply (ufd_own_insert_ne γf l fd0 k st st' (Hne k eq_refl)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4  THE THREE STEPS A SYSCALL TAKES.                                  *)
  (* ------------------------------------------------------------------- *)

  (* ---- ALLOCATE: open, dup, and each half of pipe. ----
     ONE lemma for all four, because they are one operation: fdalloc scans
     from 0 and the row hands back [fd_least_closed].  The CONCLUSION is a
     case analysis on the LEDGER, not on the kernel's answer -- which is the
     point.  If the program knows a standard stream is closed, the
     descriptor is DETERMINED and the ledger's slot is updated in place; if
     it knows all three are open, the descriptor is somewhere above them and
     a fresh handle is minted for it.  Nothing else can happen. *)
  Lemma ufd_alloc_least (γf : gname) (fdv l : list fdstate) (fd : nat)
      (st : fdstate) :
    fd_least_closed fdv fd -> st <> FdClosed ->
    ufd_auth γf fdv -∗ ustd γf l ==∗
    ufd_auth γf (<[fd := st]> fdv) ∗ ualloc γf l fd st.
  Proof using .
    intros Hle Hne. iIntros "Ha Hl".
    iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ustd_len with "Hl") as %Hll.
    iDestruct (ustd_agree with "Ha Hl") as %Hst.
    pose proof (fd_least_closed_free _ _ Hle) as Hfree.
    pose proof (lookup_lt_Some _ _ _ Hfree) as Hlt.
    (* THE VIEW MOVES WITH THE LEDGER: re-set to the new table *)
    iDestruct "Ha" as (v) "(Ha & _ & _ & Hta)".
    iDestruct "Hl" as "[Hl [%v' Htl]]".
    iMod (ufd_retab γf _ v v' (<[fd := st]> fdv) with "Ha Hta Htl")
      as "(Ha & Hta & Htl)".
    iAssert (ustd γf l) with "[Hl Htl]" as "Hl";
      [ iFrame "Hl"; by iExists _ | ].
    rewrite /ualloc /ualloc_at /ustd_after.
    destruct (fd_lowest_closed l) as [k |] eqn:Hk.
    - (* THE DESCRIPTOR IS THE LEDGER'S OWN ANSWER. *)
      assert (Hfd : fd = k)
        by (apply (fd_least_closed_prefix fdv NSTD fd k Hle); by rewrite Hst).
      subst fd.
      assert (Hkl : l !! k = Some FdClosed)
        by (exact (fd_lowest_closed_is_closed l k Hk)).
      assert (Hklt : (k < NSTD)%nat)
        by (rewrite <- Hll; exact (fd_lowest_closed_bound l k Hk)).
      iDestruct (ustd_acc γf l k FdClosed Hkl with "Hl") as "[Hs Hback]".
      iMod (ghost_map_update (UCSlot st) with "Ha Hs") as "[Ha Hs]".
      iEval (rewrite ufd_gm_insert -(ufd_map_insert fdv k st Hlt ltac:(by left))) in "Ha".
      iModIntro. iSplitL "Ha Hta".
      + iExists _. iFrame "Ha Hta". iPureIntro.
        split; [ by rewrite length_insert | apply tab_le_refl ].
      + iSplitL; [ iApply ("Hback" with "Hs") | by iPureIntro ].
    - (* IT IS ABOVE THE STANDARD STREAMS, so the ledger does not move and a
         fresh handle is minted. *)
      assert (Hge : (NSTD <= fd)%nat)
        by (apply (fd_least_closed_prefix_none fdv NSTD fd Hle); by rewrite Hst).
      assert (Hnone : ufd_gm (ufd_map fdv) (<[fd := st]> fdv) !! Some fd = None)
        by (rewrite ufd_gm_some (ufd_map_lookup_None fdv fd Hge Hfree); reflexivity).
      iMod (ghost_map_insert (Some fd) (UCSlot st) Hnone with "Ha") as "[Ha Hs]".
      iEval (rewrite ufd_gm_insert -(ufd_map_insert fdv fd st Hlt ltac:(by right))) in "Ha".
      iModIntro. iSplitL "Ha Hta".
      + iExists _. iFrame "Ha Hta". iPureIntro.
        split; [ by rewrite length_insert | apply tab_le_refl ].
      + iFrame "Hl". iSplitR; [ by iPureIntro |].
        iFrame "Hs". iPureIntro. exact (conj Hne Hge).
  Qed.

  (* ...AT A NAMED VIEW (seccomp S4): the allocation reads the caller's
     view against the table ([tab_le]) and re-sets it to the new table,
     and says so -- what a program that must know its whole table (sh,
     for the seccomp child) carries across its own opens. *)
  Lemma ufd_alloc_least_at (γf : gname) (fdv l v : list fdstate) (fd : nat)
      (st : fdstate) :
    fd_least_closed fdv fd -> st <> FdClosed ->
    ufd_auth γf fdv -∗ ustd_at γf l v ==∗
    ⌜tab_le fdv v⌝ ∗ ufd_auth γf (<[fd := st]> fdv)
    ∗ ustd_at γf (ustd_after l st) (<[fd := st]> fdv) ∗ ualloc_at γf l fd st.
  Proof using .
    intros Hle Hne. iIntros "Ha Hl".
    iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ustd_at_agree with "Ha Hl") as %Hst.
    iDestruct (ustd_at_tab with "Ha Hl") as %Htab.
    assert (Hll : length l = NSTD)
      by (rewrite -Hst length_take Hlen; pose proof NSTD_le_NOFILE; lia).
    pose proof (fd_least_closed_free _ _ Hle) as Hfree.
    pose proof (lookup_lt_Some _ _ _ Hfree) as Hlt.
    (* THE VIEW MOVES WITH THE LEDGER: re-set to the new table *)
    iDestruct "Ha" as (v0) "(Ha & _ & _ & Hta)".
    iDestruct "Hl" as "[Hl Htl]".
    iMod (ufd_retab γf _ v0 v (<[fd := st]> fdv) with "Ha Hta Htl")
      as "(Ha & Hta & Htl)".
    iAssert (ustd_at γf l (<[fd := st]> fdv)) with "[Hl Htl]" as "Hl";
      [ iFrame "Hl Htl" | ].
    rewrite /ualloc_at /ustd_after.
    destruct (fd_lowest_closed l) as [k |] eqn:Hk.
    - (* THE DESCRIPTOR IS THE LEDGER'S OWN ANSWER. *)
      assert (Hfd : fd = k)
        by (apply (fd_least_closed_prefix fdv NSTD fd k Hle); by rewrite Hst).
      subst fd.
      assert (Hkl : l !! k = Some FdClosed)
        by (exact (fd_lowest_closed_is_closed l k Hk)).
      assert (Hklt : (k < NSTD)%nat)
        by (rewrite <- Hll; exact (fd_lowest_closed_bound l k Hk)).
      iDestruct (ustd_at_acc γf l _ k FdClosed Hkl with "Hl") as "[Hs Hback]".
      iMod (ghost_map_update (UCSlot st) with "Ha Hs") as "[Ha Hs]".
      iEval (rewrite ufd_gm_insert -(ufd_map_insert fdv k st Hlt ltac:(by left))) in "Ha".
      iModIntro. iSplitR; [ by iPureIntro |]. iSplitL "Ha Hta".
      + iExists _. iFrame "Ha Hta". iPureIntro.
        split; [ by rewrite length_insert | apply tab_le_refl ].
      + iSplitL; [ iApply ("Hback" with "Hs") | by iPureIntro ].
    - (* IT IS ABOVE THE STANDARD STREAMS, so the ledger does not move and a
         fresh handle is minted. *)
      assert (Hge : (NSTD <= fd)%nat)
        by (apply (fd_least_closed_prefix_none fdv NSTD fd Hle); by rewrite Hst).
      assert (Hnone : ufd_gm (ufd_map fdv) (<[fd := st]> fdv) !! Some fd = None)
        by (rewrite ufd_gm_some (ufd_map_lookup_None fdv fd Hge Hfree); reflexivity).
      iMod (ghost_map_insert (Some fd) (UCSlot st) Hnone with "Ha") as "[Ha Hs]".
      iEval (rewrite ufd_gm_insert -(ufd_map_insert fdv fd st Hlt ltac:(by right))) in "Ha".
      iModIntro. iSplitR; [ by iPureIntro |]. iSplitL "Ha Hta".
      + iExists _. iFrame "Ha Hta". iPureIntro.
        split; [ by rewrite length_insert | apply tab_le_refl ].
      + iFrame "Hl". iSplitR; [ by iPureIntro |].
        iFrame "Hs". iPureIntro. exact (conj Hne Hge).
  Qed.

  (* ---- CLOSE, IN ITS TWO FOOTPRINTS. ----
     A TAIL descriptor's handle is simply SPENT: the slot leaves the map, so
     there is nothing to write back and the ledger is not needed at all --
     which is what keeps close out of the way of every program that opens a
     file and closes it without caring about its standard streams.  A
     STANDARD STREAM's fragment cannot leave (its key is in the map by
     construction), so it comes back SHUT, inside the ledger -- and that is
     the resource the next allocation spends.  Nothing else can happen. *)
  Lemma ufd_close_hi (γf : gname) (fdv : list fdstate) (fd : nat)
      (st : fdstate) :
    ufd_auth γf fdv -∗ ufd γf fd st ==∗ ufd_auth γf (<[fd := FdClosed]> fdv).
  Proof using .
    iIntros "Ha Hh".
    iDestruct (ufd_agree with "Ha Hh") as %Hl.
    iDestruct (ufd_ge with "Hh") as %Hge.
    iDestruct "Hh" as "[Hh _]". iDestruct "Ha" as (v) "(Ha & %Hlen & %Hle & Hta)".
    (* NO LEDGER: the view stays, and [tab_le] absorbs the close *)
    iMod (ghost_map_delete with "Ha Hh") as "Ha".
    iEval (rewrite ufd_gm_delete -(ufd_map_insert_closed fdv fd
                              (lookup_lt_Some _ _ _ Hl) Hge)) in "Ha".
    iModIntro. iExists v. iFrame "Ha Hta". iPureIntro.
    split; [ by rewrite length_insert | exact (tab_le_close_hi fdv v fd Hge Hle) ].
  Qed.

  Lemma ufd_close_std (γf : gname) (fdv l : list fdstate) (fd : nat)
      (st : fdstate) :
    (fd < NSTD)%nat -> l !! fd = Some st ->
    ufd_auth γf fdv -∗ ustd γf l ==∗
    ufd_auth γf (<[fd := FdClosed]> fdv) ∗ ustd γf (<[fd := FdClosed]> l).
  Proof using .
    intros Hs Hkl. iIntros "Ha Hl".
    iDestruct (ufd_auth_len with "Ha") as %Hlen.
    iDestruct (ustd_len with "Hl") as %Hll.
    iDestruct (ustd_agree with "Ha Hl") as %Hst.
    assert (Hi : fdv !! fd = Some st).
    { rewrite <- (lookup_take fdv NSTD fd Hs). by rewrite Hst. }
    assert (Hlt : (fd < length fdv)%nat) by exact (lookup_lt_Some _ _ _ Hi).
    iDestruct "Ha" as (v) "(Ha & _ & _ & Hta)".
    iDestruct "Hl" as "[Hl [%v' Htl]]".
    iMod (ufd_retab γf _ v v' (<[fd := FdClosed]> fdv) with "Ha Hta Htl")
      as "(Ha & Hta & Htl)".
    iAssert (ustd γf l) with "[Hl Htl]" as "Hl";
      [ iFrame "Hl"; by iExists _ | ].
    iDestruct (ustd_acc γf l fd st Hkl with "Hl") as "[Hsl Hback]".
    iMod (ghost_map_update (UCSlot FdClosed) with "Ha Hsl") as "[Ha Hsl]".
    iEval (rewrite ufd_gm_insert -(ufd_map_insert fdv fd FdClosed Hlt ltac:(by left))) in "Ha".
    iModIntro. iSplitL "Ha Hta".
    - iExists _. iFrame "Ha Hta". iPureIntro.
      split; [ by rewrite length_insert | apply tab_le_refl ].
    - iApply ("Hback" with "Hsl").
  Qed.

  (* ---- THE DEGENERATE ALLOCATION. ----
     dup's row copies the ARGUMENT's state, and nothing in it says the
     argument was open -- a dup of a closed descriptor writes [FdClosed]
     into the free slot, which is the table it already had.  (xv6 returns -1
     for it; the row does not say so, and does not need to.) *)
  Lemma ufd_alloc_least_closed (γf : gname) (fdv : list fdstate) (fd : nat) :
    fd_least_closed fdv fd ->
    ufd_auth γf fdv -∗ ufd_auth γf (<[fd := FdClosed]> fdv).
  Proof using .
    intros Hle. rewrite (list_insert_id _ _ _ (fd_least_closed_free _ _ Hle)).
    iIntros "$".
  Qed.

  (* A LEDGER AT A STATE THE CARRIER IS NOT TRACKING.  A program that calls
     an allocating syscall must hold its ledger whether or not it reads it
     -- the table cannot move without the fragment of the slot it moves --
     so a proof that does not care carries THIS, which has no index and
     therefore costs its lemma statements one resource and no binder. *)
  Definition ustd_any (γf : gname) : iProp Σ :=
    (∃ l : list fdstate, ustd γf l)%I.

  (* ---- THE AUTHORITY TOGETHER WITH A LEDGER NOBODY IS READING. ----
     A channel that does not track descriptors still cannot MOVE the table
     without the ledger: an allocation that lands on a standard stream
     updates that slot's fragment.  So the two travel together there -- one
     resource, so that a run predicate carrying it, and every lemma that
     opens and closes one, is unchanged by the ledger's arrival. *)
  Definition ufd_state (γf : gname) (fdv : list fdstate) : iProp Σ :=
    (ufd_auth γf fdv ∗ ustd_any γf)%I.

  Lemma ufd_state_len (γf : gname) (fdv : list fdstate) :
    ufd_state γf fdv -∗ ⌜length fdv = NOFILE⌝.
  Proof using . iIntros "[Ha _]". iApply (ufd_auth_len with "Ha"). Qed.

  (* ---- THE QUIET ROWS: the view did not move, so neither does anything. ---- *)
  Lemma ufd_auth_quiet (γf : gname) (fdv fdv' : list fdstate) :
    fdv' = fdv -> ufd_auth γf fdv -∗ ufd_auth γf fdv'.
  Proof using . intros ->. iIntros "$". Qed.

  (* ---- AN ALLOCATION NOBODY IS WATCHING. ----
     A caller on a channel whose rows include open and dup, but which is not
     tracking descriptors, still has to move the authority -- the TABLE
     moved whether or not the caller was watching.  It can, and the ledger
     is what pays for it: the allocation either lands in the ledger, and the
     ledger's own fragment is updated, or above it, and the minted handle is
     dropped.  What the caller CANNOT do is learn anything, which is the
     whole difference between this and [ufd_alloc_least]. *)
  Lemma ufd_alloc_least_any (γf : gname) (fdv l : list fdstate) (fd : nat)
      (st : fdstate) :
    fd_least_closed fdv fd -> st <> FdClosed ->
    ufd_auth γf fdv -∗ ustd γf l ==∗
    ufd_auth γf (<[fd := st]> fdv) ∗ ∃ l' : list fdstate, ustd γf l'.
  Proof using .
    intros Hle Hne. iIntros "Ha Hl".
    iMod (ufd_alloc_least γf fdv l fd st Hle Hne with "Ha Hl") as "[$ Hr]".
    iDestruct (ualloc_ledger with "Hr") as "Hl".
    iModIntro. by iExists _.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5  ALLOCATION -- where a process's table is founded.                 *)
  (* ------------------------------------------------------------------- *)
  (* Minted where a process's [UkRun.urun] is created, at the view the
     resumed KEY carries -- which for a process the kernel has just started
     is [fdt0], and for a forked child is its parent's table.

     THE LEDGER ALWAYS COMES OUT, and it has to: the low [NSTD] keys are in
     the map by construction, so their fragments exist, and an exclusive
     fragment for a key already in the map can never be minted later.  A
     program that does not care about its standard streams simply drops the
     ledger -- but then it can call no allocating syscall, which is the
     honest reading of "it is not tracking its descriptors".

     [D] IS WHAT A FORKED CHILD INHERITS: the sub-map of open descriptors
     above the standard streams that its parent chose to hand it.  Every key
     of [ufd_map_hi] is open by construction of the filter, so the big-op is
     a family of real handles and not of [ufd_slot] alone. *)
  (* the two disjoint families a fresh authority's fragments split into *)
  Lemma ufd_frags_split (γf : gname) (fdv : list fdstate) :
    (NSTD <= length fdv)%nat ->
    ([∗ map] k ↦ v ∈ ufd_map fdv, Some k ↪[γf] UCSlot v) -∗
    ([∗ map] k ↦ v ∈ (map_seq 0 (take NSTD fdv) : gmap nat fdstate), Some k ↪[γf] UCSlot v) ∗
    ([∗ map] k ↦ v ∈ ufd_map_hi fdv, Some k ↪[γf] UCSlot v).
  Proof using .
    intros Hn.
    rewrite (ufd_map_split fdv Hn)
            (big_sepM_union _ _ _ (ufd_map_split_disj fdv)).
    iIntros "$".
  Qed.

  (* the big-op over the slot half of the map, re-indexed *)
  Local Lemma big_sepM_kmap_some (m : gmap nat ufdcell)
      (Φ : option nat -> ufdcell -> iProp Σ) :
    ([∗ map] k ↦ x ∈ kmap Some m, Φ k x) ⊣⊢ ([∗ map] k ↦ x ∈ m, Φ (Some k) x).
  Proof using .
    induction m as [| i x m Hi IH] using map_ind.
    - by rewrite kmap_empty !big_sepM_empty.
    - rewrite (kmap_insert Some) big_sepM_insert;
        [| by rewrite (lookup_kmap Some)].
      rewrite big_sepM_insert; [| exact Hi]. by rewrite IH.
  Qed.

  (* THE MINT AT A NAMED VIEW: any view the table is [tab_le] of -- the
     table itself at an entry, the PARENT's view at a fork (the child's
     table is the parent's, so the parent's view bounds it too). *)
  Lemma ufd_alloc_std_at (fdv v : list fdstate) (D : gmap nat fdstate) :
    length fdv = NOFILE -> D ⊆ ufd_map_hi fdv -> tab_le fdv v ->
    ⊢ |==> ∃ γf : gname,
        ufd_auth γf fdv ∗ ustd_at γf (take NSTD fdv) v ∗
        ([∗ map] fd ↦ st ∈ D, ufd γf fd st).
  Proof using .
    intros Hlen Hsub Hle.
    assert (Hn : (NSTD <= length fdv)%nat)
      by (rewrite Hlen; exact NSTD_le_NOFILE).
    iMod (ghost_map_alloc (ufd_gm (ufd_map fdv) v)) as (γf) "[Ha Hfr]".
    assert (Hnk : kmap Some (UCSlot <$> ufd_map fdv) !! (@None nat) = None)
      by (apply (lookup_kmap_None Some); intros i Hi; inversion Hi).
    iEval (rewrite /ufd_gm (big_sepM_insert _ _ _ _ Hnk)) in "Hfr".
    iDestruct "Hfr" as "[[Ht1 Ht2] Hfr]".
    iEval (rewrite big_sepM_kmap_some big_sepM_fmap) in "Hfr".
    iModIntro. iExists γf. iSplitL "Ha Ht1".
    { iExists v. iFrame "Ha Ht1". iPureIntro. exact (conj Hlen Hle). }
    iDestruct (ufd_frags_split γf fdv Hn with "Hfr") as "[Hlo Hhi]".
    iSplitL "Hlo Ht2".
    { iFrame "Ht2 Hlo". iPureIntro. rewrite length_take. lia. }
    iDestruct (big_sepM_subseteq _ _ _ Hsub with "Hhi") as "Hd".
    iApply (big_sepM_mono with "Hd").
    intros fd st Hst. cbn beta.
    iIntros "Hf". iFrame "Hf". iPureIntro.
    exact (ufd_map_hi_open fdv fd st (lookup_weaken _ _ _ _ Hst Hsub)).
  Qed.

  Lemma ufd_alloc_std (fdv : list fdstate) (D : gmap nat fdstate) :
    length fdv = NOFILE -> D ⊆ ufd_map_hi fdv ->
    ⊢ |==> ∃ γf : gname,
        ufd_auth γf fdv ∗ ustd γf (take NSTD fdv) ∗
        ([∗ map] fd ↦ st ∈ D, ufd γf fd st).
  Proof using .
    intros Hlen Hsub.
    iMod (ufd_alloc_std_at fdv fdv D Hlen Hsub (tab_le_refl fdv))
      as (γf) "(Ha & Hl & Hd)".
    iModIntro. iExists γf. iFrame "Ha Hd". iApply (ustd_at_ustd with "Hl").
  Qed.

  (* the fresh-process instance, where every slot is closed: the ledger is
     three shut standard streams, which is exactly what makes init's first
     [open] land on descriptor 0. *)
  Lemma ufd_alloc_fdt0 :
    ⊢ |==> ∃ γf : gname, ufd_auth γf fdt0 ∗ ustd γf (take NSTD fdt0).
  Proof using .
    iMod (ufd_alloc_std fdt0 ∅ fdt0_length (map_empty_subseteq _))
      as (γf) "(Ha & Hl & _)".
    iModIntro. iExists γf. by iFrame.
  Qed.

  (* WHAT A SET OF HANDLES SAYS ABOUT THE TABLE: the states they name are
     the table's, at the slots they name.  Stated as a map inclusion so it
     composes with [big_sepM_subseteq] -- which is how a forked child gets
     handles for exactly what its parent held, without either side ever
     naming the whole table. *)
  Lemma ufd_sub (γf : gname) (fdv : list fdstate) (D : gmap nat fdstate) :
    ufd_auth γf fdv -∗
    ([∗ map] fd ↦ st ∈ D, ufd γf fd st) -∗
    ⌜D ⊆ ufd_map fdv⌝.
  Proof using .
    iIntros "Ha HD".
    iAssert (⌜forall (i : nat) (st : fdstate), D !! i = Some st ->
               ufd_map fdv !! i = Some st⌝)%I as %Hs.
    { iIntros (i st Hi).
      iDestruct (big_sepM_lookup with "HD") as "[Hf _]"; [exact Hi |].
      iDestruct "Ha" as (v) "(Ha & _)".
      iDestruct (ghost_map_lookup with "Ha Hf") as %He.
      rewrite ufd_gm_some in He.
      destruct (ufd_map fdv !! i) as [st' |]; [| discriminate].
      injection He as ->. by iPureIntro. }
    iPureIntro. by apply map_subseteq_spec.
  Qed.

  (* pulling ONE inherited handle out of a family, at a slot the caller can
     point to in the table.  The rest comes back, so a child that inherited
     three descriptors spends this three times. *)
  (* ...and the inclusion a forking parent proves of its own handles.  The
     [NSTD <= k] half is definitional now that the handle carries it. *)
  Lemma ufd_sub_hi (γf : gname) (fdv : list fdstate) (D : gmap nat fdstate) :
    ufd_auth γf fdv -∗
    ([∗ map] fd ↦ st ∈ D, ufd γf fd st) -∗
    ⌜D ⊆ ufd_map_hi fdv⌝.
  Proof using .
    iIntros "Ha HD".
    iAssert (⌜map_Forall (fun k (_ : fdstate) => (NSTD <= k)%nat) D⌝)%I as %Hlo.
    { rewrite <- big_sepM_pure. iApply (big_sepM_mono with "HD").
      intros k v _. cbn beta. iIntros "Hh".
      iDestruct (ufd_ge with "Hh") as %H. by iPureIntro. }
    iDestruct (ufd_sub with "Ha HD") as %Hsub.
    iPureIntro. apply ufd_map_hi_sub; [exact Hsub |].
    intros k [v Hv]. exact (Hlo k v Hv).
  Qed.

  Lemma ufd_open_at (γf : gname) (D : gmap nat fdstate)
      (fd : nat) (st : fdstate) :
    D !! fd = Some st ->
    ([∗ map] k ↦ v ∈ D, ufd γf k v) -∗
    ufd γf fd st ∗ ([∗ map] k ↦ v ∈ delete fd D, ufd γf k v).
  Proof using .
    intros Hl. iIntros "Hfr".
    iDestruct (big_sepM_delete _ _ fd st Hl with "Hfr") as "[$ $]".
  Qed.

End UserFd.

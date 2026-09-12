(* ===================================================================== *)
(* UInitFd.v -- INIT'S CONSOLE LEDGER ROWS, at an ABSTRACT descriptor.    *)
(*                                                                        *)
(* /init's console prologue is                                            *)
(*                                                                        *)
(*     if (open("console", O_RDWR) < 0) { mknod("console", CONSOLE, 0);    *)
(*                                        open("console", O_RDWR); }       *)
(*     dup(0); dup(0);                                                     *)
(*                                                                        *)
(* and everything it does to the PROGRAM'S OWN descriptor ledger           *)
(* ([UserFd.ustd]) is a function of ONE descriptor state -- whatever the   *)
(* second open installed at slot 0.  The rows are therefore stated here    *)
(* over an abstract [st], and the two tiers that need them instantiate it: *)
(*                                                                        *)
(*   the PROGRAM tier ([UkInit], [UkInitMain]) at a section variable, so   *)
(*     that init's walk never names an application (the rule                *)
(*     [UConsLine.v:202] states for the read leaf's taint: the program     *)
(*     tier names no application);                                         *)
(*   the APPLICATION tier ([UInitCons]) at                                  *)
(*     [FdOpen true true (FdDevice ConsoleInv.CONSOLE)], which is what     *)
(*     open's PINNED receipt says came back.                                *)
(*                                                                        *)
(* WHY A FILE OF ITS OWN.  The two tiers do not see each other -- [UkInit] *)
(* is below the file-system tower and [UInitCons] is above it -- so a row  *)
(* both must name lives below both.  Its whole cone is [FdSlots] and       *)
(* [UserFd].                                                               *)
(*                                                                        *)
(* THE LEDGER IS [take NSTD fdt0], THREE SLOTS, and not [FdSlots.fdt0]:    *)
(* [UserFd.ustd] carries [length l = NSTD] inside it and [fdt0] is         *)
(* [NOFILE] slots, so a [fdt0]-shaped ledger is unsatisfiable.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import FdSlots.   (* [fdstate] / [fdt0] / [fd_lowest_closed] *)
Require Import UserFd.    (* [ustd] / [ualloc] / [ufd_own] / [NSTD] *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE FOUR LEDGERS THE PROLOGUE PASSES THROUGH                      *)
(* ===================================================================== *)

(* what /init enters with: three CLOSED standard streams *)
Definition ufd_l0 : list fdstate := take NSTD fdt0.

(* ...after the open landed on 0, after the first dup landed on 1, and
   after the second landed on 2.  Each number is decided by the LEDGER
   ([UserFd.ualloc]'s lowest-free discipline) and not by the kernel. *)
Definition ufd_l1 (st : fdstate) : list fdstate := <[0%nat := st]> ufd_l0.
Definition ufd_l2 (st : fdstate) : list fdstate := <[1%nat := st]> (ufd_l1 st).
Definition ufd_l3 (st : fdstate) : list fdstate := <[2%nat := st]> (ufd_l2 st).

Lemma ufd_l0_len : length ufd_l0 = NSTD.
Proof. reflexivity. Qed.

Lemma ufd_l0_row0 : ufd_l0 !! 0%nat = Some FdClosed.
Proof. reflexivity. Qed.

Lemma ufd_l1_row0 (st : fdstate) : ufd_l1 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l2_row0 (st : fdstate) : ufd_l2 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l3_row0 (st : fdstate) : ufd_l3 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE THREE SCANS                                                   *)
(*                                                                        *)
(*  This is what turns [UserFd.ualloc]'s two arms into ONE at each of      *)
(*  init's three allocating calls.  The second and third need [st] to be   *)
(*  OPEN -- a dup of a CLOSED descriptor writes [FdClosed] back into the   *)
(*  slot it found and the scan does not advance, which is precisely the    *)
(*  CLOSED arm of init's head.                                             *)
(* ===================================================================== *)
Lemma ufd_scan0 : fd_lowest_closed ufd_l0 = Some 0%nat.
Proof. reflexivity. Qed.

Lemma ufd_scan1 (st : fdstate) :
  st <> FdClosed -> fd_lowest_closed (ufd_l1 st) = Some 1%nat.
Proof.
  intro Hne. destruct st as [| rd wr t]; [ exfalso; exact (Hne eq_refl) |].
  reflexivity.
Qed.

Lemma ufd_scan2 (st : fdstate) :
  st <> FdClosed -> fd_lowest_closed (ufd_l2 st) = Some 2%nat.
Proof.
  intro Hne. destruct st as [| rd wr t]; [ exfalso; exact (Hne eq_refl) |].
  reflexivity.
Qed.

Section UInitFd.
  Context `{!ufdG Σ}.

  (* ...and the three readings of [UserFd.ualloc] they license, which is
     the whole of "WHICH descriptor came back" at each of init's calls. *)
  Lemma ufd_alloc0 (γfd : gname) (st : fdstate) (fd : nat) :
    ualloc γfd ufd_l0 fd st -∗ ⌜fd = 0%nat⌝ ∗ ustd γfd (ufd_l1 st).
  Proof. iApply (ualloc_std γfd ufd_l0 fd 0%nat st ufd_scan0). Qed.

  Lemma ufd_alloc1 (γfd : gname) (st : fdstate) (fd : nat) :
    st <> FdClosed ->
    ualloc γfd (ufd_l1 st) fd st -∗ ⌜fd = 1%nat⌝ ∗ ustd γfd (ufd_l2 st).
  Proof.
    intro Hne.
    iApply (ualloc_std γfd (ufd_l1 st) fd 1%nat st (ufd_scan1 st Hne)).
  Qed.

  Lemma ufd_alloc2 (γfd : gname) (st : fdstate) (fd : nat) :
    st <> FdClosed ->
    ualloc γfd (ufd_l2 st) fd st -∗ ⌜fd = 2%nat⌝ ∗ ustd γfd (ufd_l3 st).
  Proof.
    intro Hne.
    iApply (ualloc_std γfd (ufd_l2 st) fd 2%nat st (ufd_scan2 st Hne)).
  Qed.

  (* ===================================================================== *)
  (*  3.  THE SOURCE CLAIM THE TWO DUPS HAND IN                             *)
  (*                                                                        *)
  (*  [UkRunSys.wp_uk_ecall_dup] takes a claim on the descriptor being       *)
  (*  duplicated, and init's is its own LEDGER's row 0 -- a standard stream, *)
  (*  not a handle, which is [UserFd.ufd_own]'s LEFT arm.                    *)
  (* ===================================================================== *)
  Lemma ufd_dup_src (γfd : gname) (l : list fdstate) (fd : nat)
      (st : fdstate) :
    (fd < NSTD)%nat -> l !! fd = Some st -> ⊢ ufd_own γfd l fd st.
  Proof.
    intros Hlt Hl. iApply (ufd_own_std γfd l fd st); [ exact Hlt | exact Hl ].
  Qed.

  (* ===================================================================== *)
  (*  4.  INIT'S HEAD: THREE ARMS                                           *)
  (*                                                                        *)
  (*  What init's fork hands its child (sh) is one of                        *)
  (*                                                                        *)
  (*    CONSOLE  the second open reached the device node and the two dups    *)
  (*             copied it: rows 0, 1 and 2 all carry [st];                  *)
  (*    CLOSED   the mknod failed, or the second open failed at [filealloc]  *)
  (*             / [fdalloc] (about which /init proves nothing -- app-echo   *)
  (*             "OPEN-PIN FINDINGS", FACT 3).  fd 0 is still closed, both   *)
  (*             dups fail on a closed descriptor and the ledger never       *)
  (*             moved;                                                      *)
  (*    TAINT    the application is off its discipline and says nothing.     *)
  (*             The ledger is at a state nobody named.                      *)
  (*                                                                        *)
  (*  [T] IS A PARAMETER: the taint is an application's notion and the       *)
  (*  program tier names no application ([UConsLine.v:202]).                 *)
  (* ===================================================================== *)
  (* THE ROW SH-LINE READS ([UConsLine.ush_std_cons]): the ledger, with slot
     0 carrying the console descriptor.  The ledger's OTHER slots are not in
     it, and that is deliberate -- see [ufd_head]. *)
  Definition ufd_std_at (γfd : gname) (st : fdstate) (l : list fdstate)
      : iProp Σ :=
    (ustd γfd l ∗ ⌜l !! 0%nat = Some st⌝)%I.

  (* INIT'S HEAD: THREE ARMS, and ONE predicate from the second open to the
     fork -- it is CLOSED UNDER THE TWO DUPS, so there is no `after the
     first dup' shape and no stage index.

       CONSOLE  the second open reached the device node: slot 0 carries it,
                at a ledger this predicate does not name.  The two dups
                keep that true whichever way they go -- a dup lands on the
                LOWEST CLOSED slot, which is never slot 0 while slot 0 is
                open ([ufd_after_row0]), and a dup that FAILS moves nothing.
                THAT IS WHY THE LIST IS EXISTENTIAL: [UsysMemOk]'s dup row
                has a failure arm no caller can rule out (the table could be
                full), so "fds 0, 1 and 2 all carry the console" is NOT a
                theorem of /init's code -- "fd 0 does" is, and it is what
                sh reads its line from;
       CLOSED   the mknod failed, or the second open failed at [filealloc] /
                [fdalloc] -- about which /init proves nothing (app-echo.md,
                "OPEN-PIN FINDINGS", FACT 3).  fd 0 is still closed, both
                dups fail on a closed descriptor and the ledger never moved;
       TAINT    the application is off its discipline and says nothing.

     [T] IS A PARAMETER: the taint is an application's notion and the
     program tier names no application ([UConsLine.v:202]). *)
  Definition ufd_head (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ((∃ l : list fdstate, ufd_std_at γfd st l)
     ∨ ustd γfd ufd_l0
     ∨ (ustd_any γfd ∗ T))%I.

  (* A DUP NEVER LANDS ON SLOT 0 WHILE SLOT 0 IS OPEN, which is the whole of
     why the console arm survives the two dups: the scan takes the lowest
     CLOSED slot ([FdSlots.fd_lowest_closed_is_closed]). *)
  Lemma ufd_after_row0 (l : list fdstate) (st : fdstate) :
    st <> FdClosed -> l !! 0%nat = Some st ->
    ustd_after l st !! 0%nat = Some st.
  Proof.
    intros Hne Hrow. rewrite /ustd_after.
    destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| exact Hrow ].
    destruct k as [| k'].
    - exfalso. pose proof (fd_lowest_closed_is_closed l 0%nat Hk) as Hc.
      rewrite Hrow in Hc. injection Hc as Hc. exact (Hne Hc).
    - by rewrite list_lookup_insert_ne.
  Qed.

  Lemma ufd_head_at (T : iProp Σ) (st : fdstate) (γfd : gname)
      (l : list fdstate) :
    l !! 0%nat = Some st -> ustd γfd l -∗ ufd_head T st γfd.
  Proof.
    intro Hrow. iIntros "H". rewrite /ufd_head. iLeft. iExists l.
    rewrite /ufd_std_at. iFrame "H". by iPureIntro.
  Qed.

  (* the two ledgers the console arm is ENTERED at: right after the second
     open (slot 0 alone) and after both dups (all three) *)
  Lemma ufd_head_l1 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd γfd (ufd_l1 st) -∗ ufd_head T st γfd.
  Proof. iApply (ufd_head_at T st γfd (ufd_l1 st) (ufd_l1_row0 st)). Qed.

  Lemma ufd_head_l3 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd γfd (ufd_l3 st) -∗ ufd_head T st γfd.
  Proof. iApply (ufd_head_at T st γfd (ufd_l3 st) (ufd_l3_row0 st)). Qed.

  Lemma ufd_head_closed (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd γfd ufd_l0 -∗ ufd_head T st γfd.
  Proof. iIntros "H". rewrite /ufd_head. iRight. by iLeft. Qed.

  Lemma ufd_head_taint (T : iProp Σ) (st : fdstate) (γfd : gname)
      (l : list fdstate) :
    T -∗ ustd γfd l -∗ ufd_head T st γfd.
  Proof.
    iIntros "Ht H". rewrite /ufd_head. iRight. iRight.
    iSplitL "H"; [ by iExists l | iExact "Ht" ].
  Qed.

  (* ...and the ledger every arm carries, which is what the untracked
     leaves and the exec supply read out of it. *)
  Lemma ufd_head_ledger (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ufd_head T st γfd -∗ ustd_any γfd.
  Proof.
    rewrite /ufd_head /ufd_std_at /ustd_any.
    iIntros "[H | [H | [H _]]]";
      [ iDestruct "H" as (l) "[H _]"; by iExists l
      | by iExists _ | iExact "H" ].
  Qed.

  (* ...AND THE LEDGER THE HEAD IS AT, WITH THE ARM'S WAY BACK.  fork hands
     the child a ledger at the PARENT's own list under the child's ghost
     name (design/user-fd.md SS5), so what the fork needs is the list and a
     [□] reconstructor usable at EITHER name -- which is why the taint arm's
     credential has to be persistent, as every application's is
     ([AppEcho.echo_taint_persistent]). *)
  Lemma ufd_head_open (T : iProp Σ) `{!Persistent T} (st : fdstate)
      (γfd : gname) :
    ufd_head T st γfd -∗
    ∃ l : list fdstate,
      ustd γfd l ∗ □ (∀ γ : gname, ustd γ l -∗ ufd_head T st γ).
  Proof.
    rewrite /ufd_head /ufd_std_at.
    iIntros "[H | [H | [Hl #Ht]]]".
    - iDestruct "H" as (l) "[H %Hrow]". iExists l. iFrame "H". iModIntro.
      iIntros (γ) "H". iApply (ufd_head_at T st γ l Hrow with "H").
    - iExists ufd_l0. iFrame "H". iModIntro. iIntros (γ) "H".
      iApply (ufd_head_closed with "H").
    - iDestruct "Hl" as (l) "Hl". iExists l. iFrame "Hl". iModIntro.
      iIntros (γ) "H". iApply (ufd_head_taint with "Ht H").
  Qed.
End UInitFd.

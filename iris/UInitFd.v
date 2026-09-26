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

Lemma ufd_l0_row2 : ufd_l0 !! 2%nat = Some FdClosed.
Proof. reflexivity. Qed.

Lemma ufd_l1_row0 (st : fdstate) : ufd_l1 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l2_row0 (st : fdstate) : ufd_l2 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l3_row0 (st : fdstate) : ufd_l3 st !! 0%nat = Some st.
Proof. reflexivity. Qed.

(* ...AND ROWS 1 AND 2, which is what lane IO-LEAF M1(f) bought: the two
   dups land at 1 and 2 by the ledger's own scan, so the exit ledger says
   all three standard streams carry the descriptor the open installed.
   [ufd_l3_row1] is what /init's banner reads ([UInitBanner]). *)
Lemma ufd_l3_row1 (st : fdstate) : ufd_l3 st !! 1%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l3_row2 (st : fdstate) : ufd_l3 st !! 2%nat = Some st.
Proof. reflexivity. Qed.

Lemma ufd_l1_len (st : fdstate) : length (ufd_l1 st) = NSTD.
Proof. reflexivity. Qed.

Lemma ufd_l2_len (st : fdstate) : length (ufd_l2 st) = NSTD.
Proof. reflexivity. Qed.

Lemma ufd_l3_len (st : fdstate) : length (ufd_l3 st) = NSTD.
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

(* ...and the FOURTH scan, which is what says the prologue is DONE: after
   the two dups every standard slot is open, so a third [dup] would find
   nothing.  /init does not make one; the fact is here because the head's
   console arm is now stated at this ledger. *)
Lemma ufd_scan3 (st : fdstate) :
  st <> FdClosed -> fd_lowest_closed (ufd_l3 st) = None.
Proof.
  intro Hne. destruct st as [| rd wr t]; [ exfalso; exact (Hne eq_refl) |].
  reflexivity.
Qed.

(* THE TWO DUP STEPS, as LEDGER equations: [UserFd.ustd_after] at the scan
   each dup runs, which is what turns the tracked leaf's answer into the
   next named ledger. *)
Lemma ufd_after_l1 (st : fdstate) :
  st <> FdClosed -> ustd_after (ufd_l1 st) st = ufd_l2 st.
Proof. intro Hne. rewrite /ustd_after (ufd_scan1 st Hne). reflexivity. Qed.

Lemma ufd_after_l2 (st : fdstate) :
  st <> FdClosed -> ustd_after (ufd_l2 st) st = ufd_l3 st.
Proof. intro Hne. rewrite /ustd_after (ufd_scan2 st Hne). reflexivity. Qed.

Section UInitFd.
  Context `{!ufdG Σ}.

  (* ...and the three readings of [UserFd.ualloc] they license, which is
     the whole of "WHICH descriptor came back" at each of init's calls. *)
  Lemma ufd_alloc0 (γfd : gname) (st : fdstate) (fd : nat) :
    ualloc γfd ufd_l0 fd st -∗ ⌜fd = 0%nat⌝ ∗ ustd γfd (ufd_l1 st).
  Proof using . iApply (ualloc_std γfd ufd_l0 fd 0%nat st ufd_scan0). Qed.

  Lemma ufd_alloc1 (γfd : gname) (st : fdstate) (fd : nat) :
    st <> FdClosed ->
    ualloc γfd (ufd_l1 st) fd st -∗ ⌜fd = 1%nat⌝ ∗ ustd γfd (ufd_l2 st).
  Proof using .
    intro Hne.
    iApply (ualloc_std γfd (ufd_l1 st) fd 1%nat st (ufd_scan1 st Hne)).
  Qed.

  Lemma ufd_alloc2 (γfd : gname) (st : fdstate) (fd : nat) :
    st <> FdClosed ->
    ualloc γfd (ufd_l2 st) fd st -∗ ⌜fd = 2%nat⌝ ∗ ustd γfd (ufd_l3 st).
  Proof using .
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
  Proof using .
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
  (* INIT'S HEAD, AT A NAMED LEDGER: THREE ARMS, and ONE predicate from the
     second open to the fork.  The two dups MOVE it -- from [ufd_l1] to
     [ufd_l2] to [ufd_l3] -- and the two names below are the two ledgers
     /init's code actually stops at.

       CONSOLE  the second open reached the device node, and the ledger is
                the NAMED one: [ufd_l1 st] before the dups, [ufd_l3 st]
                after them.

                WHY THE LIST IS NAMED AND NOT EXISTENTIAL (lane IO-LEAF,
                M1(f)).  It used to be existential with only slot 0 pinned,
                because a failing [dup] was not refutable.  Lane DUP-ROW
                made it one: [UsysMemOk.usys_fd_ok]'s dup failure arm now
                carries its REASON, and at a ledger whose slot 0 is open
                and whose slots 1 and 2 are closed both disjuncts are
                refuted -- so neither of /init's dups can fail, and
                [UkInit.wp_kinit_dup_cons] hands back [UserFd.ualloc] at
                the named ledger, landing at 1 and then 2 by [ufd_scan1] /
                [ufd_scan2].  "fds 0, 1 and 2 all carry the console" IS now
                a theorem of /init's code;
       CLOSED   the mknod failed, or the second open failed at [filealloc] /
                [fdalloc] -- about which /init proves nothing (app-echo.md,
                "OPEN-PIN FINDINGS", FACT 3).  fd 0 is still closed, both
                dups fail on a closed descriptor and the ledger never moved;
       TAINT    the application is off its discipline and says nothing.

     [T] IS A PARAMETER: the taint is an application's notion and the
     program tier names no application ([UConsLine.v:202]). *)
  Definition ufd_headL (T : iProp Σ) (γfd : gname) (l : list fdstate)
      : iProp Σ :=
    (* ...the two clean arms AT AN OK TABLE VIEW (seccomp S4): /init's
       opens and dups install the console, so the view the fork hands sh
       has no inode or pipe row *)
    (ustd_ok T γfd l ∨ ustd_ok T γfd ufd_l0 ∨ (ustd_any γfd ∗ T))%I.

  (* the head BEFORE the two dups -- what the second open hands over
     ([UkInit.uki_open2]) and what [UkInitMain.wp_kinit_main_from_1e]
     walks the dups from *)
  Definition ufd_head1 (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ufd_headL T γfd (ufd_l1 st).

  (* ...and the head AFTER them, which is what the fork carries to sh and
     what /init's own banner is paid at *)
  Definition ufd_head (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ufd_headL T γfd (ufd_l3 st).

  (* A DUP NEVER LANDS ON SLOT 0 WHILE SLOT 0 IS OPEN: the scan takes the
     lowest CLOSED slot ([FdSlots.fd_lowest_closed_is_closed]). *)
  Lemma ufd_after_row0 (l : list fdstate) (st : fdstate) :
    st <> FdClosed -> l !! 0%nat = Some st ->
    ustd_after l st !! 0%nat = Some st.
  Proof using .
    intros Hne Hrow. rewrite /ustd_after.
    destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| exact Hrow ].
    destruct k as [| k'].
    - exfalso. pose proof (fd_lowest_closed_is_closed l 0%nat Hk) as Hc.
      rewrite Hrow in Hc. injection Hc as Hc. exact (Hne Hc).
    - by rewrite list_lookup_insert_ne.
  Qed.

  (* the three arms of the generic head, and the ledger it is at *)
  Lemma ufd_headL_at (T : iProp Σ) (γfd : gname) (l : list fdstate) :
    ustd_ok T γfd l -∗ ufd_headL T γfd l.
  Proof using . iIntros "H". rewrite /ufd_headL. by iLeft. Qed.

  Lemma ufd_headL_closed (T : iProp Σ) (γfd : gname) (l : list fdstate) :
    ustd_ok T γfd ufd_l0 -∗ ufd_headL T γfd l.
  Proof using . iIntros "H". rewrite /ufd_headL. iRight. by iLeft. Qed.

  Lemma ufd_headL_taint (T : iProp Σ) (γfd : gname) (l l' : list fdstate) :
    T -∗ ustd γfd l' -∗ ufd_headL T γfd l.
  Proof using .
    iIntros "Ht H". rewrite /ufd_headL. iRight. iRight.
    iSplitL "H"; [ by iExists l' | iExact "Ht" ].
  Qed.

  Lemma ufd_headL_ledger (T : iProp Σ) (γfd : gname) (l : list fdstate) :
    ufd_headL T γfd l -∗ ustd_any γfd.
  Proof using .
    rewrite /ufd_headL /ustd_any.
    iIntros "[H | [H | [H _]]]";
      [ iExists l; iApply (ustd_ok_ustd with "H")
      | iExists _; iApply (ustd_ok_ustd with "H") | iExact "H" ].
  Qed.

  (* the two ledgers the console arm is ENTERED at: right after the second
     open (slot 0 alone) and after both dups (all three) *)
  Lemma ufd_head1_l1 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd_ok T γfd (ufd_l1 st) -∗ ufd_head1 T st γfd.
  Proof using . rewrite /ufd_head1. iApply (ufd_headL_at T γfd (ufd_l1 st)). Qed.

  Lemma ufd_head1_closed (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd_ok T γfd ufd_l0 -∗ ufd_head1 T st γfd.
  Proof using . rewrite /ufd_head1. iApply (ufd_headL_closed T γfd (ufd_l1 st)). Qed.

  Lemma ufd_head1_taint (T : iProp Σ) (st : fdstate) (γfd : gname)
      (l : list fdstate) :
    T -∗ ustd γfd l -∗ ufd_head1 T st γfd.
  Proof using . rewrite /ufd_head1. iApply (ufd_headL_taint T γfd (ufd_l1 st) l). Qed.

  Lemma ufd_head_l3 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd_ok T γfd (ufd_l3 st) -∗ ufd_head T st γfd.
  Proof using . rewrite /ufd_head. iApply (ufd_headL_at T γfd (ufd_l3 st)). Qed.

  (* the two FOLDINGS the walk needs: [ufd_head1] IS the generic head at
     [ufd_l1] and [ufd_head] IS it at [ufd_l3], but the proofmode wants the
     step said out loud ([UkInitMain.wp_kinit_main_from_1e]). *)
  Lemma ufd_head1_to_l1 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ufd_head1 T st γfd -∗ ufd_headL T γfd (ufd_l1 st).
  Proof using . rewrite /ufd_head1. by iIntros "$". Qed.

  Lemma ufd_head_of_l3 (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ufd_headL T γfd (ufd_l3 st) -∗ ufd_head T st γfd.
  Proof using . rewrite /ufd_head. by iIntros "$". Qed.

  Lemma ufd_head_closed (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ustd_ok T γfd ufd_l0 -∗ ufd_head T st γfd.
  Proof using . rewrite /ufd_head. iApply (ufd_headL_closed T γfd (ufd_l3 st)). Qed.

  Lemma ufd_head_taint (T : iProp Σ) (st : fdstate) (γfd : gname)
      (l : list fdstate) :
    T -∗ ustd γfd l -∗ ufd_head T st γfd.
  Proof using . rewrite /ufd_head. iApply (ufd_headL_taint T γfd (ufd_l3 st) l). Qed.

  (* ...and the ledger every arm carries, which is what the untracked
     leaves and the exec supply read out of it. *)
  Lemma ufd_head_ledger (T : iProp Σ) (st : fdstate) (γfd : gname) :
    ufd_head T st γfd -∗ ustd_any γfd.
  Proof using . rewrite /ufd_head. iApply (ufd_headL_ledger T γfd (ufd_l3 st)). Qed.

  (* ...AND THE ROW THE HEAD CARRIES, READ AGAINST THE PROCESS'S OWN
     AUTHORITY.  A consumer that holds the descriptor AUTHORITY (the exec
     supply does: [UkRun.udepw_at] lends it so a pinned bundle can read
     the table) turns the head into a fact about slot 0 of that authority's
     own list, which is what the exec'd program's entry is told
     ([UkSh.ush_fd0]'s three arms are these three).  The authority goes
     back untouched; the LEDGER is spent, which is right -- the process
     that execs is replaced. *)
  Lemma ufd_head_row (T : iProp Σ) (st : fdstate) (γfd : gname)
      (fdv : list fdstate) :
    ufd_auth γfd fdv -∗ ufd_head T st γfd -∗
    ufd_auth γfd fdv ∗
    (⌜take NSTD fdv !! 0%nat = Some st⌝
     ∨ ⌜take NSTD fdv !! 0%nat = Some FdClosed⌝ ∨ T).
  Proof using .
    rewrite /ufd_head /ufd_headL.
    iIntros "Ha [H | [H | [_ HT]]]".
    - iDestruct (ustd_ok_ustd with "H") as "H".
      iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iLeft. iPureIntro. exact (ufd_l3_row0 st).
    - iDestruct (ustd_ok_ustd with "H") as "H".
      iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iRight. iLeft. iPureIntro. exact ufd_l0_row0.
    - iFrame "Ha". iRight. iRight. iExact "HT".
  Qed.

  (* ...AND ROWS 1 AND 2 BESIDE IT (lane IO-LEAF, M1(f)): on the console arm
     the two dups landed there, so the whole of /init's standard triple is
     the descriptor the open installed.  Stated separately so that
     [ufd_head_row]'s three-arm shape -- which is what [UkSh.ush_fd0] is --
     does not change. *)
  Lemma ufd_head_row12 (T : iProp Σ) (st : fdstate) (γfd : gname)
      (fdv : list fdstate) :
    ufd_auth γfd fdv -∗ ufd_head T st γfd -∗
    ufd_auth γfd fdv ∗
    ((⌜take NSTD fdv !! 1%nat = Some st⌝
      ∗ ⌜take NSTD fdv !! 2%nat = Some st⌝)
     ∨ ⌜take NSTD fdv !! 0%nat = Some FdClosed⌝ ∨ T).
  Proof using .
    rewrite /ufd_head /ufd_headL.
    iIntros "Ha [H | [H | [_ HT]]]".
    - iDestruct (ustd_ok_ustd with "H") as "H".
      iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iLeft. iSplit; iPureIntro;
        [ exact (ufd_l3_row1 st) | exact (ufd_l3_row2 st) ].
    - iDestruct (ustd_ok_ustd with "H") as "H".
      iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iRight. iLeft. iPureIntro. exact ufd_l0_row0.
    - iFrame "Ha". iRight. iRight. iExact "HT".
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
      ustd_ok T γfd l ∗ □ (∀ γ : gname, ustd_ok T γ l -∗ ufd_head T st γ).
  Proof using .
    rewrite /ufd_head /ufd_headL.
    iIntros "[H | [H | [Hl #Ht]]]".
    - iExists (ufd_l3 st). iFrame "H". iModIntro.
      iIntros (γ) "H". iApply (ufd_head_l3 T st γ with "H").
    - iExists ufd_l0. iFrame "H". iModIntro. iIntros (γ) "H".
      iApply (ufd_head_closed with "H").
    - iDestruct "Hl" as (l) "Hl". iExists l.
      iSplitL "Hl"; [ iApply (ustd_ok_taint with "Ht Hl") |]. iModIntro.
      iIntros (γ) "H". iApply (ufd_head_taint with "Ht [H]").
      iApply (ustd_ok_ustd with "H").
  Qed.

  (* THE ROW BEHIND THE HEAD, AS A PURE FACT (lane IO-LEAF, step 3).  Which
     of the three arms a ledger is at is decidable from the list itself,
     and the walk between /init's banner and its fork needs to say WHICH
     arm without holding the head as a disjunction: the credential the
     banner leaves is prompt-shaped on the console arm and banner-owed on
     the closed one, and the two must be lent to the shell at the SAME
     ledger the shell will inherit.  Persistent, so a ledger opened this
     way carries its arm to wherever it is closed again. *)
  Definition ufd_row (T : iProp Σ) (st : fdstate) (l : list fdstate)
      : iProp Σ :=
    (⌜l = ufd_l3 st⌝ ∨ ⌜l = ufd_l0⌝ ∨ T)%I.

  Global Instance ufd_row_persistent T `{!Persistent T} st l :
    Persistent (ufd_row T st l).
  Proof using . rewrite /ufd_row. apply _. Qed.

  Lemma ufd_head_open_row (T : iProp Σ) `{!Persistent T} (st : fdstate)
      (γfd : gname) :
    ufd_head T st γfd -∗
    ∃ l : list fdstate,
      ustd_ok T γfd l ∗ ufd_row T st l
      ∗ □ (∀ γ : gname, ustd_ok T γ l -∗ ufd_head T st γ).
  Proof using .
    rewrite /ufd_head /ufd_headL /ufd_row.
    iIntros "[H | [H | [Hl #Ht]]]".
    - iExists (ufd_l3 st). iFrame "H". iSplitR; [ iLeft; done | ].
      iModIntro. iIntros (γ) "H". iApply (ufd_head_l3 T st γ with "H").
    - iExists ufd_l0. iFrame "H". iSplitR; [ iRight; iLeft; done | ].
      iModIntro. iIntros (γ) "H". iApply (ufd_head_closed with "H").
    - iDestruct "Hl" as (l) "Hl". iExists l.
      iSplitL "Hl"; [ iApply (ustd_ok_taint with "Ht Hl") |].
      iSplitR; [ iRight; iRight; iExact "Ht" | ].
      iModIntro. iIntros (γ) "H". iApply (ufd_head_taint with "Ht [H]").
      iApply (ustd_ok_ustd with "H").
  Qed.

  (* ...and back: a ledger at its row is the head *)
  Lemma ufd_head_of_row (T : iProp Σ) `{!Persistent T} (st : fdstate)
      (γfd : gname) (l : list fdstate) :
    ufd_row T st l -∗ ustd_ok T γfd l -∗ ufd_head T st γfd.
  Proof using .
    rewrite /ufd_row. iIntros "[-> | [-> | #Ht]] H".
    - iApply (ufd_head_l3 T st γfd with "H").
    - iApply (ufd_head_closed with "H").
    - iApply (ufd_head_taint with "Ht [H]"). iApply (ustd_ok_ustd with "H").
  Qed.
End UInitFd.

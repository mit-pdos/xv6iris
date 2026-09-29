(* ====================================================================== *)
(*  LogHelp.v -- THE HELPING SLOT: sync waiters' hooks, fired by the next  *)
(*  commit's tail  (claude-notes/design/sync.md section 4.2, “The helping    *)
(*  slot”; section 4.3 item 4)                                            *)
(*                                                                        *)
(*  A [sys_sync] that finds a commit in flight (or operations open) cannot *)
(*  fire its caller's hook itself: the batch is not quiescent.  It         *)
(*  DEPOSITS the hook here, in [LogInv.log_res] (both arms), and sleeps;   *)
(*  the committer's tail ([ProofEndOp.eo_tail]), before it clears         *)
(*  [committing] and bumps [ncommit], EXTRACTS every pending hook, runs    *)
(*  the ghost commit on all of them ([LogGhostCommit.log_ghost_commit]),  *)
(*  and FLIPS each entry to Done with its [Q] left in the entry's escrow.  *)
(*  The waiter wakes with [ncommit] moved past the word it read at its    *)
(*  deposit, so its entry is Done, and COLLECTS [▷ Q].                    *)
(*                                                                        *)
(*  THE SLOT.  A [ghost_map] at [ln_help γ]: keys the waiters' ids, values *)
(*  [(γw, n0)] -- the waiter's escrow gname and the [ncommit] word it     *)
(*  read.  Per entry, the ESCROW invariant at [helpN .@ w] over a         *)
(*  [mono_nat] at [γw], three arms:                                       *)
(*                                                                        *)
(*    esc Q γw := (Q ∗ ◯ 1)  ∨  ●{½} 0  ∨  ● 1                             *)
(*                                                                        *)
(*  and the entry's state in the slot, at [log_res]'s own cells:          *)
(*                                                                        *)
(*    Pending:  hook Q ∗ ●{½} 0 ∗ ⌜n0 = nc⌝ ∗ ⌜cmt = true ∨ out ≠ 0⌝       *)
(*    Done:     ● 1                                                       *)
(*                                                                        *)
(*  The waiter keeps the full fragment [w ↪ (γw, n0)] and the escrow's    *)
(*  handle.  Every token arm is timeless, so the only later anywhere is   *)
(*  the one on [Q] at the collect, which the waiter's next instruction    *)
(*  strips.  No [saved_prop]: the escrow pins [Q] to [w].                  *)
(*                                                                        *)
(*  THE TWO PURE CLAUSES are what the two readers need.  The waiter's     *)
(*  collect reads [n0 = nc] to refute Pending once [ncommit] moved; a     *)
(*  fast-path [sys_sync] ([cmt = false], [out = 0]) knows every entry is  *)
(*  Done, so it flips nothing.  Both are re-established at EVERY writer   *)
(*  of the three cells ([log_help_cells] for the writers that keep [nc],  *)
(*  the extract's any-cells return for the tail that moves it).           *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list namespaces.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
Require Import SailStdpp.Values.
Require Import RiscvLang.   (* [GenId]/[gen_id]: the era the hooks are at *)
Require Import RiscvPtsto.  (* [riscv_sync_hook] *)
Require Import Xv6Cameras.  (* [logG]'s [loghelp_inG] *)
Require Import LogDefs.     (* [log_names]'s [ln_help] *)

Section LogHelp.
  Context `{!riscvGS Σ, !logG Σ}.
  Context `{GEN : GenId}.

  Definition helpN : namespace := nroot .@ "loghelp".

  (* THE ESCROW: [Q] with the "flipped" witness, or the waiter's half at
     zero (before the flip), or the terminal full authority at one (after
     the collect). *)
  Definition esc (Q : iProp Σ) (γw : gname) : iProp Σ :=
    ((Q ∗ mono_nat_lb_own γw 1%nat) ∨
     mono_nat_auth_own_frac γw (1/2) 0%nat ∨
     mono_nat_auth_own_frac γw 1 1%nat)%I.

  (* ONE ENTRY of the slot, at the cells [nc], [out], [cmt]. *)
  Definition log_help_entry (nc : mword 32) (out : nat) (cmt : bool)
      (w : nat) (e : gname * mword 32) : iProp Σ :=
    (∃ Q : iProp Σ, inv (helpN .@ w) (esc Q e.1) ∗
       ((riscv_sync_hook gen_id Q ∗ mono_nat_auth_own_frac e.1 (1/2) 0%nat ∗
         ⌜e.2 = nc⌝ ∗ ⌜cmt = true \/ out ≠ 0%nat⌝) ∨
        mono_nat_auth_own_frac e.1 1 1%nat))%I.

  (* THE SLOT, as [LogInv.log_res] holds it at its own three cells. *)
  Definition log_help (γ : log_names) (nc : mword 32) (out : nat) (cmt : bool)
      : iProp Σ :=
    (∃ m : gmap nat (gname * mword 32),
       ghost_map_auth_frac (ln_help γ) 1 m ∗
       [∗ map] w ↦ e ∈ m, log_help_entry nc out cmt w e)%I.

  (* ---------------------------------------------------------------- *)
  (*  The escrow's two moves                                          *)
  (* ---------------------------------------------------------------- *)

  (* THE FLIP (the committer): the entry's half at zero and the [Q] the
     ghost commit produced go in; the escrow is left holding [Q ∗ ◯ 1] and
     the full authority at one comes out for the Done arm. *)
  Lemma esc_flip (w : nat) (Q : iProp Σ) (γw : gname) :
    inv (helpN .@ w) (esc Q γw) -∗ mono_nat_auth_own_frac γw (1/2) 0%nat -∗ Q ={⊤}=∗
    mono_nat_auth_own_frac γw 1 1%nat.
  Proof using .
    iIntros "#Hinv Hh HQ".
    iInv "Hinv" as "Hb" "Hclose". rewrite /esc.
    iDestruct "Hb" as "[[_ >#Hlb] | [>Hh2 | >Hf]]".
    - iDestruct (mono_nat_auth_lb_own_valid with "Hh Hlb") as %[_ Hle]. lia.
    - iAssert (mono_nat_auth_own_frac γw 1 0%nat) with "[Hh Hh2]" as "Hfull".
      { iEval (rewrite -Qp.half_half). iSplitL "Hh"; [iExact "Hh" | iExact "Hh2"]. }
      iMod (mono_nat_own_update 1%nat with "Hfull") as "[Hfull #Hlb]"; [lia|].
      iMod ("Hclose" with "[HQ]") as "_".
      { iNext. iLeft. iFrame "HQ Hlb". }
      iModIntro. iExact "Hfull".
    - iDestruct (mono_nat_auth_own_agree with "Hh Hf") as %[Hq _].
      exfalso. by apply (Qp.not_add_le_r (1/2) 1).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  The four lemmas                                                 *)
  (* ---------------------------------------------------------------- *)

  (* THE DEPOSIT (the waiter, lock held, at the guard's [cmt ∨ out ≠ 0]):
     a fresh id, a fresh escrow at the caller's [Q], and a Pending entry at
     the current [ncommit] word. *)
  Lemma log_help_deposit (γ : log_names) (nc : mword 32) (out : nat) (cmt : bool)
      (Q : iProp Σ) :
    cmt = true \/ out ≠ 0%nat ->
    log_help γ nc out cmt -∗ riscv_sync_hook gen_id Q ={⊤}=∗
    ∃ (w : nat) (γw : gname),
      log_help γ nc out cmt ∗ w ↪[ln_help γ] (γw, nc) ∗ inv (helpN .@ w) (esc Q γw).
  Proof using .
    intros Hg. iIntros "H Hhook". rewrite /log_help.
    iDestruct "H" as (m) "[Ha Hm]".
    set (w := fresh (dom m)).
    assert (Hw : m !! w = None).
    { apply not_elem_of_dom. apply is_fresh. }
    iMod (mono_nat_own_alloc 0%nat) as (γw) "[Hfull _]".
    iEval (rewrite -{1}Qp.half_half) in "Hfull".
    iDestruct "Hfull" as "[H1 H2]".
    iMod (inv_alloc (helpN .@ w) ⊤ (esc Q γw) with "[H1]") as "#Hinv".
    { iNext. rewrite /esc. iRight. iLeft. iExact "H1". }
    iMod (ghost_map_insert w (γw, nc) Hw with "Ha") as "[Ha Hw]".
    iModIntro. iExists w, γw. iFrame "Hw Hinv".
    iExists (<[w := (γw, nc)]> m). iFrame "Ha".
    rewrite big_sepM_insert //. iFrame "Hm".
    rewrite /log_help_entry /=. iExists Q. iFrame "Hinv". iLeft.
    iFrame "Hhook H2". iPureIntro. split; [reflexivity | exact Hg].
  Qed.

  (* the extract, entry by entry *)
  Lemma log_help_entries_extract (m : gmap nat (gname * mword 32))
      (nc : mword 32) (out : nat) (cmt : bool) :
    ([∗ map] w ↦ e ∈ m, log_help_entry nc out cmt w e) -∗
    ∃ Qs : list (iProp Σ),
      ([∗ list] Q ∈ Qs, riscv_sync_hook gen_id Q) ∗
      (∀ (nc' : mword 32) (out' : nat) (cmt' : bool),
         ([∗ list] Q ∈ Qs, Q) ={⊤}=∗
         [∗ map] w ↦ e ∈ m, log_help_entry nc' out' cmt' w e).
  Proof using .
    induction m as [|w e m Hw IH] using map_ind.
    - iIntros "_". iExists []. iSplitR; [done|].
      iIntros (nc' out' cmt') "_". iModIntro. by rewrite big_sepM_empty.
    - rewrite big_sepM_insert //. iIntros "[He Hm]".
      iDestruct (IH with "Hm") as (Qs) "[Hhs Hk]".
      rewrite {1}/log_help_entry.
      iDestruct "He" as (Q) "[#Hinv [(Hh & Hhalf & _ & _) | Hdone]]".
      + (* PENDING: its hook comes out, its [Q] flips it *)
        iExists (Q :: Qs). rewrite big_sepL_cons. iFrame "Hh Hhs".
        iIntros (nc' out' cmt') "[HQ HQs]".
        iMod (esc_flip w Q e.1 with "Hinv Hhalf HQ") as "Hdone".
        iMod ("Hk" with "HQs") as "Hm".
        iModIntro. rewrite big_sepM_insert //. iFrame "Hm".
        rewrite /log_help_entry. iExists Q. iFrame "Hinv". iRight. iExact "Hdone".
      + (* DONE: stays Done, at any cells *)
        iExists Qs. iFrame "Hhs".
        iIntros (nc' out' cmt') "HQs".
        iMod ("Hk" with "HQs") as "Hm".
        iModIntro. rewrite big_sepM_insert //. iFrame "Hm".
        rewrite /log_help_entry. iExists Q. iFrame "Hinv". iRight. iExact "Hdone".
  Qed.

  (* THE EXTRACT (the committer's tail, lock held, [committing] still set):
     every Pending hook comes out, and the return wand -- fed each hook's
     [Q] -- flips every entry to Done, so the slot re-closes at ANY cells. *)
  Lemma log_help_extract (γ : log_names) (nc : mword 32) (out : nat) (cmt : bool) :
    log_help γ nc out cmt -∗
    ∃ Qs : list (iProp Σ),
      ([∗ list] Q ∈ Qs, riscv_sync_hook gen_id Q) ∗
      (∀ (nc' : mword 32) (out' : nat) (cmt' : bool),
         ([∗ list] Q ∈ Qs, Q) ={⊤}=∗ log_help γ nc' out' cmt').
  Proof using .
    iIntros "H". rewrite /log_help. iDestruct "H" as (m) "[Ha Hm]".
    iDestruct (log_help_entries_extract with "Hm") as (Qs) "[Hhs Hk]".
    iExists Qs. iFrame "Hhs". iIntros (nc' out' cmt') "HQs".
    iMod ("Hk" with "HQs") as "Hm". iModIntro. iExists m. iFrame.
  Qed.

  (* THE COLLECT (the waiter, lock re-held, [ncommit] moved past its word):
     the entry is Done, so it is deleted, and the full authority opens the
     escrow at its [Q] arm; the escrow closes in its terminal arm. *)
  Lemma log_help_collect (γ : log_names) (nc : mword 32) (out : nat) (cmt : bool)
      (w : nat) (γw : gname) (n0 : mword 32) (Q : iProp Σ) :
    w ↪[ln_help γ] (γw, n0) -∗ inv (helpN .@ w) (esc Q γw) -∗ ⌜n0 ≠ nc⌝ -∗
    log_help γ nc out cmt ={⊤}=∗ log_help γ nc out cmt ∗ ▷ Q.
  Proof using .
    iIntros "Hw #Hinv %Hne H". rewrite /log_help.
    iDestruct "H" as (m) "[Ha Hm]".
    iDestruct (ghost_map_lookup with "Ha Hw") as %Hlk.
    rewrite big_sepM_delete //. iDestruct "Hm" as "[He Hm]".
    rewrite /log_help_entry /=.
    iDestruct "He" as (Q') "[_ [(_ & _ & %Heq & _) | Hdone]]".
    { exfalso. exact (Hne Heq). }
    iMod (ghost_map_delete with "Ha Hw") as "Ha".
    iInv "Hinv" as "Hb" "Hclose". rewrite /esc.
    iDestruct "Hb" as "[[HQ _] | [>Hh | >Hf]]".
    - iMod ("Hclose" with "[Hdone]") as "_".
      { iNext. iRight. iRight. iExact "Hdone". }
      iModIntro. iFrame "HQ". iExists (delete w m). iFrame.
    - iDestruct (mono_nat_auth_own_agree with "Hh Hdone") as %[Hq _].
      exfalso. by apply (Qp.not_add_le_r (1/2) 1).
    - iDestruct (mono_nat_auth_own_exclusive with "Hf Hdone") as %[].
  Qed.

  (* THE CELL WRITERS THAT KEEP [nc] ([begin_op]'s [out+1], [end_op]'s
     non-final [out-1 ≠ 0] and its final [cmt := true]): the Pending
     entries' guard clause is carried by the given implication, the Done
     entries are cell-free. *)
  Lemma log_help_cells (γ : log_names) (nc : mword 32) (out out' : nat)
      (cmt cmt' : bool) :
    (cmt = true \/ out ≠ 0%nat -> cmt' = true \/ out' ≠ 0%nat) ->
    log_help γ nc out cmt -∗ log_help γ nc out' cmt'.
  Proof using .
    intros Himp. rewrite /log_help. iIntros "H".
    iDestruct "H" as (m) "[Ha Hm]". iExists m. iFrame "Ha".
    iApply (big_sepM_mono with "Hm"). intros w e _.
    rewrite /log_help_entry. iIntros "He".
    iDestruct "He" as (Q) "[Hinv [(Hh & Hhalf & %Heq & %Hg) | Hdone]]".
    - iExists Q. iFrame "Hinv". iLeft. iFrame "Hh Hhalf".
      iPureIntro. split; [exact Heq | exact (Himp Hg)].
    - iExists Q. iFrame "Hinv". iRight. iExact "Hdone".
  Qed.

  (* THE GENESIS: the empty map [LogDefs.log_free_tok] hands over. *)
  Lemma log_help_empty (γ : log_names) (nc : mword 32) (out : nat) (cmt : bool) :
    ghost_map_auth_frac (ln_help γ) 1 (∅ : gmap nat (gname * mword 32)) -∗
    log_help γ nc out cmt.
  Proof using .
    iIntros "Ha". rewrite /log_help. iExists ∅. iFrame "Ha".
    by rewrite big_sepM_empty.
  Qed.

End LogHelp.

(* ====================================================================== *)
(*  FsFlushedCore.v -- THE DURABILITY RECEIPT [flushed b D], AT AN         *)
(*  ALTITUDE THE WAL CAN SEE                                              *)
(*  (fs-syscall-specs lane Y; the owner-ruled banking of                   *)
(*   [LogInv.log_flushed_bank])                                            *)
(*                                                                        *)
(*  WHY THIS FILE EXISTS AND [FsFlushed.v] DID NOT SUFFICE.  Lane Y built  *)
(*  the receipt as a LEAF over [FsDurSyscall], which is the right place    *)
(*  for the per-node composition [dur_at] -- and the wrong place for the   *)
(*  receipt itself the moment the owner ruled that the committer must BANK *)
(*  it in [LogInv.log_res].  [FsDurSyscall]'s cone contains                *)
(*  [SystemAdequacy] and therefore the whole proof tree, [LogInv]          *)
(*  included; a conjunct of [log_res] cannot be stated at a vocabulary     *)
(*  that sits above [log_res].  So sections 1 and 2 of [FsFlushed.v] MOVED *)
(*  HERE, BYTE FOR BYTE in their statements and proofs, and this file is a *)
(*  leaf over [FsCrash] + [FsDurSnap] -- both of which [LogInv] can        *)
(*  already reach ([FsCrash]'s cone is 48 files and does not contain       *)
(*  [LogInv]; [FsDurSnap] is in [LogInv]'s cone already, through           *)
(*  [LogSnapLaw]).  [FsFlushed.v] re-exports this file, so nothing that    *)
(*  imported it sees any difference, and section 3's [dur_at] stays where  *)
(*  it was.                                                               *)
(*                                                                        *)
(*  WHAT THE RECEIPT IS (lane Y's finding, unchanged).  Design section 5   *)
(*  principle 2 asks for a PERSISTENT, MONOTONE, STATE-SHAPED receipt --   *)
(*  batches <= b are on disk -- whose VALUE is a COPY of the frozen        *)
(*  snapshot certificate ("sync-style receipts are copies").  It adds NO   *)
(*  ghost state, NO invariant and NO parameter to anything:               *)
(*                                                                        *)
(*    - the VALUE is [FsCrash.fs_receipt]'s committed map [D] -- the       *)
(*      mono-list lower bound the commit already mints;                   *)
(*    - the BOUND is that lower bound's own LENGTH.  [fs_receipt] is       *)
(*      [∃ l, fs_hist_lb (l ++ [D])] with [l] existential; naming          *)
(*      [length l] is the whole of the "commit counter", and it costs      *)
(*      nothing because the mono-list ALREADY carries it.                  *)
(*                                                                        *)
(*  WHY THE INDEX HAD TO COME FROM THE HISTORY AND NOT FROM A COUNTER.     *)
(*  There is no numeric durable-epoch pointer anywhere in the tree: the    *)
(*  epoch is [FsDurSnap.P_dur], whose gname family is existentially        *)
(*  closed and which is INDEXED BY THE COMMITTED MAP ALONE: an epoch is    *)
(*  named only by the map it stands at.  A commit DROPS the old epoch and  *)
(*  allocates a fresh one ([FsDurSnap.dsnap_step_xfer]), so no resource of *)
(*  the epoch survives to be compared.  What does survive is the mono-list *)
(*  [FsCrash.fcn_hist], and it is exactly a counter with its values        *)
(*  attached: index [b] IS the b-th commit, and [flushed_at_agree] below   *)
(*  is why two receipts at the same [b] name the same disk.                *)
(*                                                                        *)
(*  AND THE PRODUCER GAP IS CLOSED HERE (section 2b).  [P_fs_flushed_now]  *)
(*  hands out a receipt whenever the crash predicate is OPEN, which is a   *)
(*  disk write's own fupd and nothing else -- so a function that writes no *)
(*  block (sys_sync) can never reach it.  [FsCrash.fs_bank] is the COPY a  *)
(*  WAL write leaves behind for such a reader ([FsCrash.fs_rec_permit_bank] *)
(*  is where it is taken), and [flushed_of_bank] below is where its index  *)
(*  is named.  From there it is [LogInv.log_flushed_bank]'s business.      *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import mono_list.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat.

(* The import block is the SHORTEST one that states sections 1 and 2 --
   deliberately NOT [FsDurSyscall]'s, which is what put the receipt above
   the WAL in the first place.  [FsCrash] brings the record, the history and
   the bank; [FsDurSnap] brings [snap_ok]/[snap_holds] and the epoch's own
   reading [P_dur_tie_keep].  Nothing here reaches the pure well-formedness
   layer, so [LogInv]'s header rule ("nothing in the crash/log layer imports
   the pure wf layer") still holds after this file joins its cone. *)
Require Import RiscvPtsto.      (* [riscvEraGS], [log_mirror], the seam names *)
Require Import DiskImg.         (* [diskImgG]                              *)
Require Import Xv6Cameras.      (* [fsCrashG], [lockG], [fsLinkG], [fsTopG] *)
Require Import FsDurSnap.       (* [snap_ok], [snap_holds], [P_dur_tie_keep] *)
Require Import FsCrash.         (* [P_fs], [fs_receipt], [fs_hist_lb], [fs_bank] *)
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE RECEIPT, AT THE CRASH RECORD'S OWN GNAMES                      *)
(* ====================================================================== *)

Section flushed_hist.
  (* The binder list is [FsCrash]'s [Section fs_crash], VERBATIM -- the same
     rule [FsDurSyscall]'s [Section commit] follows, and for the same reason
     (durable-notes.md: a lemma about a definition of that section stated
     with a SHORTER list sends typeclass search after an unknown [Σ]). *)
  Context `{!fsCrashG Σ, !lockG Σ}.
  Context `{!ghost_mapG Σ nat riscvEraGS, !mono_natG Σ,
            !ghost_varG Σ log_mirror, !diskImgG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.

  (* THE RECEIPT.  "[D] is the [b]-th committed state" -- [b] counting from
     zero, so [b] is also the number of commits that PRECEDE it, which is
     what makes the reading "every batch <= b is on disk" literal: the lower
     bound holds the whole prefix, not just its last element. *)
  Definition flushed_at (γs : fs_crash_names) (b : nat)
      (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ l : list (gmap Z (list (bv 8))),
       ⌜length l = b⌝ ∗ fs_hist_lb (fcn_hist γs) (l ++ [D]))%I.

  Global Instance flushed_at_persistent γs b D :
    Persistent (flushed_at γs b D).
  Proof. rewrite /flushed_at. apply _. Qed.

  (* the two directions against the landed receipt: the index is exactly
     what [fs_receipt] existentially closes *)
  Lemma flushed_at_receipt γs b D :
    flushed_at γs b D -∗ fs_receipt γs D.
  Proof.
    rewrite /flushed_at /fs_receipt. iIntros "H".
    iDestruct "H" as (l _) "Hlb". iExists l. iExact "Hlb".
  Qed.

  Lemma flushed_at_of_receipt γs D :
    fs_receipt γs D -∗ ∃ b : nat, flushed_at γs b D.
  Proof.
    rewrite /flushed_at /fs_receipt. iIntros "H".
    iDestruct "H" as (l) "Hlb". iExists (length l), l.
    iSplitR; [by iPureIntro | iExact "Hlb"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  the mono-list's two facts, as [fs_hist] lemmas                      *)
  (* ------------------------------------------------------------------ *)

  (* A LOWER BOUND WEAKENS TO EVERY PREFIX.  This is what makes the receipt
     MONOTONE in the design's sense: holding "committed through b" is
     holding "committed through b'" for every earlier b'. *)
  Lemma fs_hist_lb_prefix (γ : gname) (l l' : list (gmap Z (list (bv 8)))) :
    l' `prefix_of` l -> fs_hist_lb γ l -∗ fs_hist_lb γ l'.
  Proof.
    intros Hpre. rewrite /fs_hist_lb. iApply own_mono.
    by apply mono_list_lb_mono.
  Qed.

  (* TWO LOWER BOUNDS ARE COMPARABLE, with no authority in hand.  This is
     the algebraic fact the whole ordering of receipts rests on. *)
  Lemma fs_hist_lb_compare (γ : gname) (l l' : list (gmap Z (list (bv 8)))) :
    fs_hist_lb γ l -∗ fs_hist_lb γ l' -∗
      ⌜l `prefix_of` l' \/ l' `prefix_of` l⌝.
  Proof.
    rewrite /fs_hist_lb. iIntros "H H'".
    iDestruct (own_valid_2 with "H H'") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  the receipt's three client-visible laws                             *)
  (* ------------------------------------------------------------------ *)

  (* (i) AGREEMENT: the bound determines the disk.  Without this, [dur_at]
     would be a certificate about nothing -- two receipts at the same [b]
     could name different maps and a consumer could not compose the
     per-node readings of two carriers at one bound (design section 5's
     "two bounded carriers + one flushed, same b"). *)
  Lemma flushed_at_agree γs b D D' :
    flushed_at γs b D -∗ flushed_at γs b D' -∗ ⌜D = D'⌝.
  Proof.
    iIntros "H H'".
    iDestruct "H" as (l Hl) "Hlb". iDestruct "H'" as (l' Hl') "Hlb'".
    iDestruct (fs_hist_lb_compare with "Hlb Hlb'") as %Hc.
    iPureIntro.
    assert (Hlen : length (l ++ [D]) = length (l' ++ [D'])).
    { rewrite !length_app Hl Hl'. reflexivity. }
    assert (Heq : l ++ [D] = l' ++ [D']).
    { destruct Hc as [Hp | Hp]; [| symmetry];
        apply prefix_length_eq; [exact Hp | lia | exact Hp | lia]. }
    destruct (app_inj_1 l l' [D] [D'] ltac:(lia) Heq) as [_ Htl].
    by injection Htl.
  Qed.

  (* (ii) MONOTONICITY: a receipt at [b] contains one at every earlier
     bound.  The earlier map is the history's own entry there, so this is
     not a weakening to a vacuous claim. *)
  Lemma flushed_at_earlier γs (b b' : nat) D :
    (b' <= b)%nat ->
    flushed_at γs b D -∗ ∃ D' : gmap Z (list (bv 8)), flushed_at γs b' D'.
  Proof.
    intros Hle. iIntros "H". iDestruct "H" as (l Hl) "Hlb".
    assert (Hlt : (b' < length (l ++ [D]))%nat)
      by (rewrite length_app Hl; simpl; lia).
    destruct (lookup_lt_is_Some_2 (l ++ [D]) b' Hlt) as [D' HD'].
    iExists D', (take b' (l ++ [D])).
    iSplitR; [iPureIntro; rewrite length_take; lia |].
    iApply (fs_hist_lb_prefix _ (l ++ [D]) with "Hlb").
    rewrite -(take_S_r (l ++ [D]) b' D' HD'). apply prefix_take.
  Qed.

  (* (iii) HONESTY: what a receipt names really was committed, AT ITS OWN
     INDEX.  [FsCrash.P_fs_receipt_committed] gives membership; this gives
     the position, which is what turns the index into a batch NUMBER. *)
  Lemma P_fs_flushed_lookup γs cov ls dk b D :
    P_fs γs cov ls dk -∗ flushed_at γs b D -∗
      ⌜exists r : fs_rec,
         fs_rec_wf r (fs_blocks dk) cov ls /\ fr_hist r !! b = Some D⌝.
  Proof.
    rewrite /P_fs /P_fs_at /flushed_at.
    iIntros "Hp Hf". iDestruct "Hp" as (gt r) "(Hauth & %Hwf & _)".
    iDestruct "Hf" as (l Hl) "Hlb".
    iDestruct (fs_hist_valid with "Hauth Hlb") as %Hpre.
    iPureIntro. exists r. split; [exact Hwf |].
    apply (prefix_lookup_Some (l ++ [D]) (fr_hist r) b D); [| exact Hpre].
    rewrite lookup_app_r; [| lia]. rewrite Hl Nat.sub_diag. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PRODUCER: the crash predicate hands out its own receipt         *)
  (* ------------------------------------------------------------------ *)

  (* WHENEVER [P_fs] IS OPEN, the current commit's receipt is free: the
     history's authority is right there, its last element IS the committed
     map ([fs_rec_wf]'s middle clause), and the durable snapshot standing at
     that map says the map is a file system ([FsDurSnap.P_dur_tie_keep], the
     same step [FsCrash.fs_commit_receipt] takes).  PURE and NON-DESTRUCTIVE:
     everything handed out is persistent and [P_fs] comes back unchanged.

     THIS IS BOTH PATHS' PRODUCER in design section 5 principle 2's case
     split -- the commit's fupd on the slow path, and (through the clause
     this file was split out to make statable) the invariant's own copy on
     the fast path, where no commit occurs at all. *)
  Lemma P_fs_flushed_now γs cov ls dk :
    P_fs γs cov ls dk -∗
      ∃ (b : nat) (D : gmap Z (list (bv 8))),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗ ⌜snap_holds D⌝ ∗
        flushed_at γs b D ∗ P_fs γs cov ls dk.
  Proof.
    rewrite /P_fs /P_fs_at. iIntros "Hp".
    iDestruct "Hp" as (gt r) "(Hauth & %Hwf & Harm & Hdur)".
    iDestruct (P_dur_at_tie_keep gt (fr_D r)
                 (fs_recovery_blocks_full dk (fr_D r) cov ls (proj1 Hwf))
                 with "Hdur") as (S Hok) "Hdur".
    iDestruct (fs_hist_snapshot with "Hauth") as "[Hauth #Hlb]".
    destruct Hwf as (Hrec & Hlast & Hhdr).
    destruct (proj1 (last_Some (fr_hist r) (fr_D r)) Hlast) as [l Hl].
    iExists (length l), (fr_D r).
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; by exists S |].
    iSplitR.
    { iExists l. iSplitR; [by iPureIntro |]. rewrite -Hl. iExact "Hlb". }
    iExists gt, r. iFrame "Hauth Harm Hdur". iPureIntro.
    split_and!; [exact Hrec | exact Hlast | exact Hhdr].
  Qed.

  (* ...and the same reading with the state's name dropped, for a consumer
     that wants only the certificate ([FsDurSyscall]'s convention). *)
  Lemma P_fs_flushed_holds γs cov ls dk b D :
    P_fs γs cov ls dk -∗ flushed_at γs b D -∗
      ⌜exists r : fs_rec,
         fs_rec_wf r (fs_blocks dk) cov ls /\ fr_hist r !! b = Some D⌝ ∗
      P_fs γs cov ls dk.
  Proof.
    iIntros "Hp #Hf".
    iDestruct (P_fs_flushed_lookup with "Hp Hf") as %H.
    iSplitR; [by iPureIntro | iExact "Hp"].
  Qed.
End flushed_hist.

(* ====================================================================== *)
(*  2.  THE CLIENT-FACING RECEIPT                                          *)
(* ====================================================================== *)

Section flushed_seam.
  (* The binder list is [FsCrash]'s [Section fs_crash_seam], VERBATIM: this
     section states things about [fs_receipt_any], which lives there because
     the seam equations name the FIXED layer's gnames. *)
  Context `{!riscvGS Σ, !fsCrashG Σ, !lockG Σ}.
  Context `{XI : CurCtx}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.

  (* [FsCrash.fs_receipt_any] with the batch NUMBER exposed.  [γs] is
     existential for that definition's own reason -- adequacy allocates the
     history gname under the update, so no client-visible constant can name
     it -- and the three seam equations are what a WAL fupd checks.

     WHAT THE EXISTENTIAL COSTS, said plainly: two receipts of THIS form are
     comparable only once a common [γs] is in hand, which is the case at
     every site that has the crash predicate open (the commit) and at every
     site that reads a banked copy (all copies in the bank come from the one
     record).  [flushed_at_agree] is the fact; this wrapper does not weaken
     it, it only defers naming the record. *)
  Definition flushed (b : nat) (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ γs : fs_crash_names,
       ⌜fcn_swap γs = riscv_swap_name /\ fcn_reg γs = riscv_registry_name /\
        fcn_start γs = riscv_start_name⌝ ∗ flushed_at γs b D)%I.

  Global Instance flushed_persistent b D : Persistent (flushed b D).
  Proof. rewrite /flushed. apply _. Qed.

  Lemma flushed_receipt_any b D : flushed b D -∗ fs_receipt_any D.
  Proof.
    rewrite /flushed /fs_receipt_any. iIntros "H".
    iDestruct "H" as (γs Hseam) "Hf". iExists γs.
    iSplitR; [by iPureIntro |]. by iApply flushed_at_receipt.
  Qed.

  (* THE BANKABLE FORM.  This is the whole of what the committer has to do
     with the receipt it drops today: [∃ b] closes the index, so the commit
     needs to know NOTHING about a counter to bank a receipt -- the counter
     is inside the mono-list already. *)
  Lemma flushed_of_receipt_any D :
    fs_receipt_any D -∗ ∃ b : nat, flushed b D.
  Proof.
    rewrite /fs_receipt_any. iIntros "H".
    iDestruct "H" as (γs Hseam) "Hr".
    iDestruct (flushed_at_of_receipt with "Hr") as (b) "Hf".
    iExists b, γs. iSplitR; [by iPureIntro |]. iExact "Hf".
  Qed.

  Lemma flushed_earlier (b b' : nat) D :
    (b' <= b)%nat ->
    flushed b D -∗ ∃ D' : gmap Z (list (bv 8)), flushed b' D'.
  Proof.
    intros Hle. iIntros "H". iDestruct "H" as (γs Hseam) "Hf".
    iDestruct (flushed_at_earlier _ b b' D Hle with "Hf") as (D') "Hf'".
    iExists D', γs. iSplitR; [by iPureIntro |]. iExact "Hf'".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  THE BANK, WITH ITS INDEX NAMED                                 *)
  (* ------------------------------------------------------------------ *)

  (* WHAT A WAL WRITE HANDS THE LOG INVARIANT.  [FsCrash.fs_bank] is the raw
     copy the permit takes ([fs_rec_permit_bank]) -- a durable map and the
     word that says it is a file system, with the map existential because the
     permit's caller does not know it.  This names the batch index, which is
     free ([flushed_of_receipt_any]) and is what makes the copy ORDERABLE
     against every other one a client holds ([flushed_earlier]).

     From here the clause is [LogInv.log_flushed_bank] and nothing in this
     file knows about the log. *)
  Lemma flushed_of_bank :
    fs_bank -∗ ∃ (b : nat) (D : gmap Z (list (bv 8))),
                 flushed b D ∗ ⌜snap_holds D⌝.
  Proof.
    rewrite /fs_bank. iIntros "H". iDestruct "H" as (D) "[Hr %Hh]".
    iDestruct (flushed_of_receipt_any with "Hr") as (b) "Hf".
    iExists b, D. iSplitL; [iExact "Hf" | by iPureIntro].
  Qed.
End flushed_seam.

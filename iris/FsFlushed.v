(* ====================================================================== *)
(*  FsFlushed.v -- THE DURABILITY RECEIPT [flushed b D] AND ITS PER-NODE   *)
(*  COMPOSITION [dur_at]                                                   *)
(*  (fs-syscall-specs lane Y; claude-notes/design/fs-syscall-specs.md      *)
(*   section 5 principles 2 and 3, claude-notes/design/durable-fs-plan.md  *)
(*   section 3's "Commit" and its receipt)                                 *)
(*                                                                        *)
(*  WHAT THIS FILE IS.  Design section 5 principle 2 asks for a            *)
(*  PERSISTENT, MONOTONE, STATE-SHAPED receipt -- batches <= b are on      *)
(*  disk -- whose VALUE is a COPY of the frozen snapshot certificate      *)
(*  ("sync-style receipts are copies").  This file builds it out of what   *)
(*  is already landed and adds NO ghost state, NO invariant and NO         *)
(*  parameter to anything:                                                 *)
(*                                                                        *)
(*    - the VALUE is [FsCrash.fs_receipt]'s committed map [D] -- the       *)
(*      mono-list lower bound the commit already mints                     *)
(*      ([FsCrash.fs_commit_L_seq_permit]'s residual, which ProofEndOp     *)
(*      holds and drops today);                                            *)
(*    - the BOUND is that lower bound's own LENGTH.  [fs_receipt] is       *)
(*      [∃ l, fs_hist_lb (l ++ [D])] with [l] existential; naming          *)
(*      [length l] is the whole of the "commit counter" the archived       *)
(*      worklist (completed/fs-log-stage4.md item 2) asks for, and it      *)
(*      costs nothing because the mono-list ALREADY carries it.            *)
(*                                                                        *)
(*  WHY THE INDEX HAD TO COME FROM THE HISTORY AND NOT FROM A COUNTER.     *)
(*  There is no numeric durable-epoch pointer anywhere in the tree: the    *)
(*  epoch is [FsDurSnap.P_dur], whose gname family is existentially        *)
(*  closed and which is INDEXED BY THE COMMITTED MAP ALONE: an epoch is   *)
(*  named only by the map it stands at.  A commit DROPS the old epoch and *)
(*  allocates a fresh one ([FsDurSnap.dsnap_step_xfer]), so no resource of *)
(*  the epoch survives to be compared.  What does survive is the mono-list *)
(*  [FsCrash.fcn_hist], and it is exactly a counter with its values        *)
(*  attached: index [b] IS the b-th commit, and [flushed_at_agree] below *)
(*  is why two receipts at the same [b] name the same disk.  This is the   *)
(*  reading FsCrash's own comment anticipated -- the lower bound records   *)
(*  the whole prefix, so a receipt also pins everything committed before   *)
(*  it, which is what makes two receipts comparable, phase D's sys_sync.   *)
(*                                                                        *)
(*  WHAT IS STILL MISSING, PRECISELY (and it is not in this file).  The    *)
(*  receipt has no PRODUCER a client can reach: [P_fs_flushed_now] below   *)
(*  hands one out whenever the crash predicate is OPEN, which is the       *)
(*  commit's own fupd and nothing else -- sys_sync writes no disk block    *)
(*  and so never opens it.  For a client to obtain a receipt the committer *)
(*  must BANK the one it currently drops, in the log invariant, beside the *)
(*  batch counter it bumps in the same breath.  That is a conjunct of      *)
(*  [LogInv.log_res] and hence an owner decision (it re-elaborates         *)
(*  LogInv.v and with it the whole proof tree); see SpecSysSyncFlush.v's   *)
(*  header for the shape of the clause and lane Y's report for the         *)
(*  measured cost.  Everything on THIS side of that clause is proven here. *)
(*                                                                        *)
(*  SECTION 3 is the composition the campaign worklist promised:           *)
(*  [dur_at b D i n] = the receipt at bound [b] together with              *)
(*  [FsDurSyscall.dur_node D i n], and nothing in FsDurSyscall moved.      *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import mono_list.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat.

(* The import block is [FsDurSyscall]'s, VERBATIM and in its order (its own
   header explains why: the file-system stack's names must win over the block
   layer's twins that arrive through the crash predicate), with FsDurSyscall
   itself appended -- section 3 is stated at its vocabulary. *)
Require Import RiscvPtsto.      (* [riscvEraGS], [log_mirror]              *)
Require Import DiskImg.         (* [diskImgG]                              *)
Require Import Xv6Cameras.      (* [fsCrashG], [lockG], [fsLinkG], [fsTopG] *)
Require Import SystemAdequacy.  (* [fs_boot_pure]                          *)
Require Import FsCrash.         (* [P_fs], [fs_receipt], [fs_hist_lb]      *)

Require Import BioDefs.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsDurSnap.       (* [P_dur], [snap_ok], [P_dur_tie_keep]    *)
Require Import FsDurSyscall.    (* [snap_holds], [dur_node], [dur_sb], ... *)

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
     below would be a certificate about nothing -- two receipts at the same
     [b] could name different maps and a consumer could not compose the
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
    rewrite /P_fs /flushed_at.
    iIntros "Hp Hf". iDestruct "Hp" as (r) "(Hauth & %Hwf & _)".
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
     split -- the commit's fupd on the slow path, and (once the clause named
     in this file's header banks it) the invariant's own copy on the fast
     path, where no commit occurs at all. *)
  Lemma P_fs_flushed_now γs cov ls dk :
    P_fs γs cov ls dk -∗
      ∃ (b : nat) (D : gmap Z (list (bv 8))),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗ ⌜snap_holds D⌝ ∗
        flushed_at γs b D ∗ P_fs γs cov ls dk.
  Proof.
    rewrite /P_fs. iIntros "Hp".
    iDestruct "Hp" as (r) "(Hauth & %Hwf & Harm & Hdur)".
    iDestruct (P_dur_tie_keep (fr_D r)
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
    iExists r. iFrame "Hauth Harm Hdur". iPureIntro.
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
End flushed_seam.

(* ====================================================================== *)
(*  3.  PER-NODE PERSISTENCE: [dur_at], the composition                    *)
(*                                                                        *)
(*  design section 5 principle 3, and the campaign worklist's promised     *)
(*  shape verbatim: dur_at b i a = flushed b * [dur_node D_b i n], with    *)
(*  nothing here moving.  Nothing in [FsDurSyscall] moved.               *)
(* ====================================================================== *)

Section dur_at.
  Context `{!riscvGS Σ, !fsCrashG Σ, !lockG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.

  (* THE CERTIFICATE.  The bound [b] and the map [D] travel together because
     [flushed_at_agree] makes [D] a function of [b]: a consumer that holds
     two of these at one bound is holding two rows of ONE disk. *)
  Definition dur_at (b : nat) (D : gmap Z (list (bv 8)))
      (i : Z) (n : fs_node) : iProp Σ :=
    (flushed b D ∗ ⌜snap_holds D⌝ ∗ ⌜dur_node D i n⌝)%I.

  Global Instance dur_at_persistent b D i n : Persistent (dur_at b D i n).
  Proof. rewrite /dur_at. apply _. Qed.

  (* THE READING (principle 3's [use] half, at the certificate's own
     altitude): whatever file system the disk at bound [b] describes, it has
     [i] at [n].  The step from here to "recovery preserves i at a" is the
     adequacy-altitude one the design keeps out of the logic. *)
  Lemma dur_at_node b D i n :
    dur_at b D i n -∗
      ⌜forall S : fs_state_rec, snap_ok S D -> fss_inodes S !! i = Some n⌝.
  Proof. rewrite /dur_at. iIntros "(_ & _ & $)". Qed.

  Lemma dur_at_flushed b D i n : dur_at b D i n -∗ flushed b D.
  Proof. rewrite /dur_at. iIntros "($ & _ & _)". Qed.

  (* THE MINT (principle 3's [mint] half).  A syscall proof knows the 64
     bytes its transaction left in the inum's slot -- which, the batch having
     committed, are the recovered disk's own bytes -- and gets the
     certificate.  This is [FsDurSyscall.dur_node_of_rec] with the receipt
     carried along; the receipt is what turns a fact about a map into a fact
     about a BOUND. *)
  Lemma dur_at_of_rec (b : nat) (D : gmap Z (list (bv 8))) (sb : fs_sb)
      (i : Z) (bs : list (bv 8)) (d : dinode) :
    snap_holds D ->
    dur_sb D sb ->
    0 <= i < 16 * (sb_ninodes sb / 16 + 1) ->
    dinode_wf d ->
    D !! rec_bno sb i = Some bs ->
    rec_in_blk bs (rec_off i) d ->
    flushed b D -∗ ∃ n : fs_node, ⌜fn_rec n = d⌝ ∗ dur_at b D i n.
  Proof.
    intros Hh Hsb Hran Hwf Hbs Hrec. iIntros "#Hfl".
    destruct (dur_node_of_rec D sb i bs d Hh Hsb Hran Hwf Hbs Hrec)
      as (n & Hdn & Hd).
    iExists n. iSplitR; [by iPureIntro |].
    rewrite /dur_at. iFrame "Hfl". iPureIntro. split; [exact Hh | exact Hdn].
  Qed.

  (* ...and off a snapshot state one already holds (the commit's own side) *)
  Lemma dur_at_of_snap (b : nat) (S : fs_state_rec)
      (D : gmap Z (list (bv 8))) (i : Z) (n : fs_node) :
    snap_ok S D ->
    0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
    fss_inodes S !! i = Some n ->
    flushed b D -∗ dur_at b D i n.
  Proof.
    intros HS Hran Hi. iIntros "#Hfl". rewrite /dur_at. iFrame "Hfl".
    iPureIntro. split.
    - by exists S.
    - exact (dur_node_of_snap S D i n HS Hran Hi).
  Qed.

  (* AGREEMENT, twice.  At one bound the map is fixed
     ([flushed_at_agree]), and at one map an inum's node is fixed
     ([FsDurSyscall.dur_node_agree]) -- so a consumer's certificates cannot
     disagree with each other. *)
  Lemma dur_at_agree b D i n n' :
    dur_at b D i n -∗ dur_at b D i n' -∗ ⌜n = n'⌝.
  Proof.
    rewrite /dur_at. iIntros "(_ & %Hh & %H1) (_ & _ & %H2)".
    iPureIntro. exact (dur_node_agree D i n n' Hh H1 H2).
  Qed.

  (* ...AND THE MAP, at a named record.  Stated at [flushed_at] rather than
     at [flushed] on purpose: the client-facing wrapper closes [γs], and two
     receipts whose records are not known to be the same one cannot be
     compared -- the mono-list is per-gname.  Every real consumer HAS the
     record (the commit has it open; a banked copy comes from the one
     record), so this is a naming obligation, not a gap. *)
  Lemma dur_at_map_agree (γs : fs_crash_names) b D D' i i' n n' :
    (fcn_swap γs = riscv_swap_name /\ fcn_reg γs = riscv_registry_name /\
     fcn_start γs = riscv_start_name) ->
    flushed_at γs b D -∗ flushed_at γs b D' -∗
    dur_at b D i n -∗ dur_at b D' i' n' -∗ ⌜D = D'⌝.
  Proof.
    intros _. iIntros "Hf Hf' _ _".
    iDestruct (flushed_at_agree with "Hf Hf'") as %Heq.
    iPureIntro. exact Heq.
  Qed.

  (* THE CROSS-NODE CONJUNCTION, which is the reason the bound is a number
     and not just a map: two certificates at ONE bound are two rows of one
     durable file system, with no ordering argument and no second state.
     (design section 5: two bounded carriers + one flushed, same b -- batch
     order gives the conjunction.) *)
  Lemma dur_at_pair b D i n j p :
    dur_at b D i n -∗ dur_at b D j p -∗
      ⌜forall S : fs_state_rec, snap_ok S D ->
         fss_inodes S !! i = Some n /\ fss_inodes S !! j = Some p⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (dur_at_node with "H1") as %G1.
    iDestruct (dur_at_node with "H2") as %G2.
    iPureIntro. intros S HS. split; [exact (G1 S HS) | exact (G2 S HS)].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ACCEPTANCE TEST, end to end                                     *)
  (*                                                                     *)
  (*  From the crash predicate ALONE -- the resource the commit's fupd    *)
  (*  runs against -- plus the bytes a transaction left at an inum's      *)
  (*  slot: a bounded, persistent, per-node durability certificate.  No   *)
  (*  ghost was added, no arity moved, and every step is a landed lemma.  *)
  (* ------------------------------------------------------------------ *)
  Theorem dur_at_of_crash (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) :
    fcn_swap γs = riscv_swap_name ->
    fcn_reg γs = riscv_registry_name ->
    fcn_start γs = riscv_start_name ->
    P_fs γs cov ls dk -∗
      ∃ (b : nat) (D : gmap Z (list (bv 8))),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗
        flushed b D ∗ ⌜snap_holds D⌝ ∗
        (* every inum whose record the caller can read off the recovered
           disk gets its certificate at this bound *)
        □ (∀ (sb : fs_sb) (i : Z) (bs : list (bv 8)) (d : dinode),
             ⌜dur_sb D sb⌝ -∗
             ⌜0 <= i < 16 * (sb_ninodes sb / 16 + 1)⌝ -∗
             ⌜dinode_wf d⌝ -∗
             ⌜D !! rec_bno sb i = Some bs⌝ -∗
             ⌜rec_in_blk bs (rec_off i) d⌝ -∗
             ∃ n : fs_node, ⌜fn_rec n = d⌝ ∗ dur_at b D i n) ∗
        P_fs γs cov ls dk.
  Proof.
    intros Hsw Hrg Hst. iIntros "Hp".
    iDestruct (P_fs_flushed_now with "Hp") as (b D) "(%Hrec & %Hh & #Hf & Hp)".
    iAssert (flushed b D) as "#Hfl".
    { iExists γs. iSplitR; [iPureIntro; split_and!; done |]. iExact "Hf". }
    iExists b, D.
    iSplitR; [by iPureIntro |].
    iSplitR; [iExact "Hfl" |].
    iSplitR; [by iPureIntro |].
    iSplitR "Hp"; [| iExact "Hp"].
    iModIntro. iIntros (sb i bs d) "%Hsb %Hran %Hwf %Hbs %Hrb".
    iDestruct (dur_at_of_rec b D sb i bs d Hh Hsb Hran Hwf Hbs Hrb with "Hfl")
      as (n Hd) "Hda".
    iExists n. iSplitR; [by iPureIntro | iExact "Hda"].
  Qed.

  (* NON-VACUITY (durable-fs-plan.md section 7's discipline).  The theorem's
     byte premises are [snap_ok]'s own clauses, so at any reachable state
     they are met and the certificate it returns is the snapshot's own row --
     the same witness [FsDurSyscall.mknod_durable_inhabited] exhibits, now
     carrying a bound. *)
  Lemma dur_at_inhabited (b : nat) (S : fs_state_rec)
      (D : gmap Z (list (bv 8))) (i : Z) :
    snap_ok S D ->
    0 <= i < 16 * (sb_ninodes (fss_sb S) / 16 + 1) ->
    flushed b D -∗ ∃ n : fs_node, dur_at b D i n ∗ ⌜fss_inodes S !! i = Some n⌝.
  Proof.
    intros HS Hran. iIntros "#Hfl".
    destruct (sk_regdom (sk_bytes HS) i Hran) as [n Hn].
    iExists n. iSplitR "".
    - iApply (dur_at_of_snap b S D i n HS Hran Hn with "Hfl").
    - by iPureIntro.
  Qed.
End dur_at.

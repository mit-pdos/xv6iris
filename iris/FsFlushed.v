(* ====================================================================== *)
(*  FsFlushed.v -- THE PER-NODE DURABILITY CERTIFICATE [dur_at], OVER THE  *)
(*  RECEIPT [flushed b D]                                                  *)
(*  (fs-syscall-specs lane Y; claude-notes/design/fs-syscall-specs.md      *)
(*   section 5 principles 2 and 3, claude-notes/design/durable-fs-plan.md  *)
(*   section 3's "Commit" and its receipt)                                 *)
(*                                                                        *)
(*  THE RECEIPT ITSELF MOVED DOWN, to [FsFlushedCore.v], and this file     *)
(*  re-exports it -- so every importer of [FsFlushed] still sees           *)
(*  [flushed_at], [flushed] and their laws exactly where it saw them.      *)
(*  The move is the owner-ruled banking's one structural cost and its      *)
(*  reason is in that file's header: a conjunct of [LogInv.log_res] cannot *)
(*  be stated at a vocabulary that sits ABOVE [log_res], and this file's   *)
(*  own cone (through [FsDurSyscall] -> [SystemAdequacy]) is the whole     *)
(*  proof tree.  Nothing in section 3 below moved, and nothing in          *)
(*  [FsDurSyscall] moved.                                                  *)
(*                                                                        *)
(*  WHAT IS HERE.  The composition the campaign worklist promised:         *)
(*  [dur_at b D i n] = the receipt at bound [b] together with              *)
(*  [FsDurSyscall.dur_node D i n] -- mint, read, agreement, the cross-node *)
(*  conjunction at one bound, the end-to-end acceptance test off [P_fs]    *)
(*  alone, and a non-vacuity witness.                                      *)
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
Require Import Xv6Cameras.      (* [fsCrashG], [lockG], [fsLinkG], [fsTopG] *)
Require Import FsCrash.         (* [P_fs], [fs_receipt], [fs_hist_lb]      *)

Require Import DinodeEnc.
Require Import FsImg.
Require Import FsDurSnap.       (* [P_dur], [snap_ok], [P_dur_tie_keep]    *)
Require Import FsDurSyscall.    (* [snap_holds], [dur_node], [dur_sb], ... *)
Require Import TsoCtx.
(* THE RECEIPT, re-exported so that this file's own interface is unchanged
   by the split.  [Require Export], not Import: importers of [FsFlushed]
   name [flushed]/[flushed_at] and must keep seeing them here. *)
Require Export FsFlushedCore.   (* [flushed_at], [flushed], [flushed_of_bank] *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  3.  PER-NODE PERSISTENCE: [dur_at], the composition                    *)
(*                                                                        *)
(*  design section 5 principle 3, and the campaign worklist's promised     *)
(*  shape verbatim: dur_at b i a = flushed b * [dur_node D_b i n], with    *)
(*  nothing here moving.  Nothing in [FsDurSyscall] moved.               *)
(* ====================================================================== *)

Section dur_at.
  Context `{!riscvGS Σ, !fsCrashG Σ, !lockG Σ}.
  Context `{XI : CurCtx}.
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

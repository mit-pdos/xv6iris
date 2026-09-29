(* ====================================================================== *)
(*  LogQuiet.v -- THE QUIESCENT LOG, AS A READER HOLDING THE LOCK SEES IT  *)
(*  (claude-notes/design/sync.md section 4, obligation K1)                 *)
(*                                                                        *)
(*  [sys_sync]'s fast path ([!committing && outstanding == 0] at the       *)
(*  acquire of [log.lock]) fires a caller's update at that instant with    *)
(*  "the running state is the durable one".  The WAL's half of that fact   *)
(*  is a statement about BYTES, and it is what this file provides:         *)
(*                                                                        *)
(*    quiescent  ==>  the batch is empty ([LogInv.log_res]'s               *)
(*                    [⌜out = 0 -> n = 0⌝])                                *)
(*               ==>  row (b) covers the whole home set                    *)
(*               ==>  the logged view on the home set IS the crash         *)
(*                    record's committed map ([log_quiet_committed]).      *)
(*                                                                        *)
(*  WHY NOT A CONJUNCT OVER THE ABSTRACT MAP.  The running abstract state  *)
(*  (the [fs_top] authority, split between [InodeRegion.ftop_inv] and      *)
(*  [AppInv.app_inv]) is moved by [AppInv.app_top_update] alone, and no    *)
(*  mover holds anything of the log's: a log-invariant conjunct about the  *)
(*  map could not be re-established by any of them.  The abstract          *)
(*  equality is instead READ where the log is quiescent, by the file       *)
(*  system's own law: the empty transaction authority [log_quiet] lends    *)
(*  is exactly what [LogSnapLaw.snap_law] takes, and the pair it hands     *)
(*  down stands at [fs_restrict (dv_of_D L) home] -- the committed map, by *)
(*  [log_quiet_committed] -- with its guest at the RUNNING map, by the     *)
(*  collection's construction ([FsCollectAll.fs_collect_dur]).  So a fast  *)
(*  path swaps the crash record's pair at an UNCHANGED committed map       *)
(*  ([P_fs_rec_quiet_acc]) and fires the caller's update on the new one,   *)
(*  exactly as the committer does after a real commit.                     *)
(*                                                                        *)
(*  NOTHING HERE MOVES: both accessors hand back what they lend.  A leaf,  *)
(*  so the lock invariant's cone does not see it.                          *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import RiscvLang.   (* [GenId]/[gen_id]: the era the record's arm is in *)
Require Import RiscvPtsto.
Require Import FsBlocks.    (* [fs_cache] *)
Require Import FsDurSnap.   (* [P_dur_at] *)
Require Import FsCrash.     (* [P_fs_rec_at], [fs_arm_acc], [fs_recovery_clean] *)
Require Import LogInv.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  1.  THE PURE CORE: a quiescent batch's logged view is the committed map *)
(* ---------------------------------------------------------------------- *)

(* The era's picture [M] reads a CLEAN header, and outside an EMPTY batch
   the logged view agrees with it (row (b) at [LB = ∅]); the custody arm
   says the picture is the physical disk; recovery of a disk with a clean
   header is its home blocks.  So the committed map is the logged view on
   the home set. *)
Lemma log_quiet_committed (M : log_mirror) (L : gmap Z (list (bv 8)))
    (cov : gset Z) (ls : Z) (dk : Z -> bv 8) (D : gmap Z (list (bv 8))) :
  lm_hdr M ls = (0%nat, []) ->
  log_mirror_tie_body M L cov ls ∅ ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  fs_recovery (fs_blocks dk) D cov ls ->
  D = fs_restrict (dv_of_D L) (fs_home_set cov ls).
Proof.
  intros Hhdr Htie Hok Hrec.
  assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, [])).
  { rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)). exact Hhdr. }
  assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
    by (rewrite -hdr_dec_n Hdk0 //).
  rewrite (proj1 (fs_recovery_clean _ _ _ _ Hn0) Hrec).
  apply fs_restrict_ext. intros b Hb.
  rewrite /dv_of_D (Htie b Hb (not_elem_of_empty b)) /=.
  symmetry. exact (Hok b (fs_home_in_ext cov ls b Hb)).
Qed.

(* THE BYTE VIEW'S CACHE PICTURE AGAINST THE LOGGED VIEW, pure half: the
   law's conclusion is stated at the byte invariant's own cache picture [C],
   a committer's at the checked-out [L], and on the home set -- which is
   [dom C] -- the two are the same map.  Here rather than in [ProofEndOp]
   (whose commit is its first reader) because the ghost commit
   ([LogGhostCommit]) reads the byte view the same way (sync K3-3). *)
Lemma eo_restrict_of_sub (C L : gmap Z (list (bv 8))) (home : gset Z) :
  dom C = home -> C ⊆ L ->
  fs_restrict (dv_of_D C) home = fs_restrict (dv_of_D L) home.
Proof.
  intros Hdom Hsub. apply fs_restrict_ext. intros b Hb.
  assert (Hin : is_Some (C !! b))
    by (apply elem_of_dom; rewrite Hdom; exact Hb).
  destruct Hin as [bs Hbs].
  rewrite /dv_of_D Hbs (lookup_weaken _ _ _ _ Hbs Hsub) //.
Qed.

Section LogQuiet.
  Context `{XI : CurCtx}.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !bioG Σ, !bioslotG Σ, !fsLogG Σ, !logG Σ,
            !fsLinkG Σ, !fsTopG Σ, !fsCrashG Σ}.
  Context `{GEN : GenId}.

  (* the checked-out CACHE authority against the halves the byte view's
     invariant parks: every home block's cached value is the one the
     committer holds.  [ghost_map_lookup_big] is stated at fraction 1 only in
     iris 4.4.0, so this is [FsBlocks.byte_range_q_lookup]'s three-line
     idiom at a half.  (The commit's [ProofEndOp.eo_snap_law_of_auth] and the
     ghost commit both read it.) *)
  Lemma eo_cache_body_sub (γfs : fs_names) (L C : gmap Z (list (bv 8))) :
    ghost_map_auth_frac (fs_cache γfs) 1 L -∗
    ([∗ map] b ↦ bs ∈ C, b ↪[fs_cache γfs]{#(1/2)} bs) -∗ ⌜C ⊆ L⌝.
  Proof using .
    iIntros "Ha HC". rewrite map_subseteq_spec. iIntros (k v Hk).
    iDestruct (ghost_map_lookup with "Ha [HC]") as %->; [| done].
    rewrite big_sepM_lookup; done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2.  WHAT THE QUIESCENT LOCK RESOURCE LENDS                       *)
  (* ---------------------------------------------------------------- *)

  (* the EMPTY transaction authority (what the file system's law takes),
     the cache authority at the logged view [L] (what the law is stated
     at), and the era's mirror half with the two rows that make [L] the
     committed map: a clean header, and row (b) over the whole home set *)
  Definition log_quiet (γ : log_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (L : gmap Z (list (bv 8))) (M : log_mirror) : iProp Σ :=
    (ghost_map_auth_frac (ln_tx γ) 1 (∅ : gmap nat unit) ∗
     ghost_map_auth_frac (fs_cache γfs) 1 L ∗
     log_mirror_half M ∗
     ⌜lm_hdr M logstart = (0%nat, [])⌝ ∗
     ⌜log_mirror_tie_body M L cov logstart ∅⌝)%I.

  (* THE READER'S ACCESSOR.  The three cells the guard reads come out as
     [ProofSysSync.ss_cells] hands them, beside the helping slot at those
     cells ([LogHelp.log_help]: the slow path deposits into it), and the way
     back is an ADDITIVE pair: either the cells and the slot alone (any
     arm), or -- when the cells read [outstanding = 0] and
     [committing = 0] -- the quiescent loan and the era's sync token as
     well (the ghost commit's two inputs), returned unchanged beside the
     cells and the slot. *)
  Lemma log_res_quiet_acc (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) :
    log_res γ bn γfs cov logstart -∗
    ∃ (out : nat) (cmt : bool) (nc : mword 32),
      ⌜(out <= 3)%nat⌝ ∗
      l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
      l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
      l_ncommit ↦₄ nc ∗
      log_help γ nc out cmt ∗
      ((l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) -∗
        l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) -∗
        l_ncommit ↦₄ nc -∗
        log_help γ nc out cmt -∗
        log_res γ bn γfs cov logstart)
       ∧
       (⌜out = 0%nat⌝ -∗ ⌜cmt = false⌝ -∗
        ∃ (L : gmap Z (list (bv 8))) (M : log_mirror),
          log_quiet γ γfs cov logstart L M ∗ riscv_sync_tok gen_id ∗
          (log_quiet γ γfs cov logstart L M -∗
           riscv_sync_tok gen_id -∗
           l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) -∗
           l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) -∗
           l_ncommit ↦₄ nc -∗
           log_help γ nc out cmt -∗
           log_res γ bn γfs cov logstart))).
  Proof using .
    rewrite /log_res.
    iIntros "H". iDestruct "H" as (out cmt nc om E X T)
      "(Hout & Hcmt & Hnc & Hauth & %Hsz & %Hbnd & %Hout3 & %Hcmt0 & Hepa &
        %Hepos & Hxa & %Hlive & %Hcap & Htxa & %Hszt & Hhelp & Hrest)".
    iExists out, cmt, nc.
    iSplitR; [iPureIntro; exact Hout3|].
    iFrame "Hout Hcmt Hnc Hhelp".
    iSplit.
    - (* the cells and the slot alone *)
      iIntros "Hout Hcmt Hnc Hhelp".
      iExists out, cmt, nc, om, E, X, T.
      iFrame "Hout Hcmt Hnc Hauth Hepa Hxa Htxa Hhelp Hrest".
      iPureIntro. done.
    - (* the quiescent loan and the token *)
      iIntros (Hout0 Hcmtf). subst cmt.
      (* nothing outstanding: the ledger, hence the transaction map, is empty *)
      assert (HT : T = ∅) by (apply map_size_empty_iff; rewrite Hszt Hsz; exact Hout0).
      subst T.
      iDestruct "Hrest" as (n LB) "(%Hsum & %Hsub & %Hreg & %Hquiet & Htok & Hbatch)".
      pose proof (Hquiet Hout0) as Hn0.
      rewrite /log_state.
      iDestruct "Hbatch" as (W L D M)
        "(%Hlen & %HLB & %Hnodup & %Hwok & Hncell & HW & Hjunk & HLauth & HDauth &
          Hcov & Hhdr & Hlogr & Hpool & Hmirh & %Hmhdr & %Hmtie)".
      (* the batch is EMPTY, so row (b) is over the whole home set *)
      assert (HLB0 : LB = ∅).
      { destruct Hlen as [HlenW _]. rewrite Hn0 in HlenW.
        symmetry in HlenW. apply nil_length_inv in HlenW. subst W. exact HLB. }
      iExists L, M. iFrame "Htxa HLauth Hmirh Htok".
      iSplitR; [iPureIntro; split; [exact Hmhdr | rewrite -HLB0; exact Hmtie]|].
      iIntros "(Htxa & HLauth & Hmirh & _ & _) Htok Hout Hcmt Hnc Hhelp".
      iExists out, false, nc, om, E, X, (∅ : gmap nat unit).
      iFrame "Hout Hcmt Hnc Hauth Hepa Hxa Htxa Hhelp".
      repeat (iSplitR; [iPureIntro; first [done | intros; discriminate]|]).
      iExists n, LB.
      iSplitR; [iPureIntro; exact Hsum|].
      iSplitR; [iPureIntro; exact Hsub|].
      iSplitR; [iPureIntro; exact Hreg|].
      iSplitR; [iPureIntro; exact Hquiet|].
      iSplitL "Htok"; [iExact "Htok"|].
      iExists W, L, D, M. iFrame. iPureIntro. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  THE CRASH RECORD, READ AT THE QUIESCENT PICTURE               *)
  (* ---------------------------------------------------------------- *)

  (* THE RECORD'S SNAPSHOT SLOT, AT THE MAP THE QUIESCENT LOG NAMES.  With
     the loan's mirror half and rows, the era's swap receipt and the
     started-generations authority (the squeeze of [FsCrash.fs_arm_acc]:
     the arm's picture is THIS era's), the committed map of the crash
     record is the logged view on the home set -- so the snapshot it holds
     stands there, and a snapshot at any other name but the SAME map closes
     the record again.  The record's history, arm and disk image are not
     touched: this is the ghost-only step a fast-path [sys_sync] swaps the
     durable pair at, the committed map not moving.

     THE STARTED-GENERATIONS AUTHORITY IS A PREMISE, as it is of every WAL
     permit ([RiscvPtsto.disk_write_permit]); only the DMA completion lends
     it today ([RiscvExec.wp_disk_step]). *)
  Lemma P_fs_rec_quiet_acc (gt : gname) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) (n : nat) (M : log_mirror)
      (L : gmap Z (list (bv 8))) :
    n = (gen_id + 1)%nat ->
    lm_hdr M ls = (0%nat, []) ->
    log_mirror_tie_body M L cov ls ∅ ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    start_auth n -∗
    log_mirror_half M -∗
    P_fs_rec_at gt cov ls dk ==∗
      start_auth n ∗ log_mirror_half M ∗
      P_dur_at gt (fs_restrict (dv_of_D L) (fs_home_set cov ls)) ∗
      (∀ gt' : gname,
         P_dur_at gt' (fs_restrict (dv_of_D L) (fs_home_set cov ls)) -∗
         P_fs_rec_at gt' cov ls dk).
  Proof using .
    intros Hn Hhdr Htie. iIntros "#Hreg #Hswlb Hsa Hmir HP".
    rewrite /P_fs_rec_at /P_fs_rec_named_at.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs_at. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm & Hdur)".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own_frac (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    rewrite /log_mirror_half.
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M Hn
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    (* the arm goes straight back: same image, same picture *)
    iMod ("Hclose" $! dk M with "[%]") as "[Harm Hmir]"; [exact Hok|].
    destruct Hwf as (Hrec & Hlast & Hhwf).
    pose proof (log_quiet_committed M L cov ls dk (fr_D r) Hhdr Htie Hok Hrec)
      as HD.
    iModIntro. iFrame "Hmir".
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite -HD. iFrame "Hdur".
    iIntros (gt') "Hdur".
    iExists γs. iSplitR; [iPureIntro; done|].
    rewrite /P_fs_at. iExists r. iFrame "Hhist Harm Hdur".
    iPureIntro. split_and!; done.
  Qed.

End LogQuiet.

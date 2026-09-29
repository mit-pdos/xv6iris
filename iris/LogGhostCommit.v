(* ====================================================================== *)
(*  LogGhostCommit.v -- THE GHOST COMMIT: a commit with no disk write      *)
(*  (claude-notes/design/sync.md section 4.3 item 3)                       *)
(*                                                                        *)
(*  A [sync] must strengthen the DURABLE copy of the application's claim  *)
(*  even when the log has nothing to write (the fast path finds it        *)
(*  quiescent; the committer's tail has just re-formed an empty batch).   *)
(*  With the batch quiescent the logged view IS the committed map         *)
(*  ([LogQuiet.log_quiet_committed]), so the file system's law can build  *)
(*  the next durable pair at the SAME committed map and the crash record  *)
(*  can take it in place of the old one -- nothing moves on disk.         *)
(*                                                                        *)
(*  THE STEPS, all ghost, all inside ONE custody fupd at the current      *)
(*  instruction ([HartCustody.wp_crash_fupd], the crash invariant's       *)
(*  second opener):                                                       *)
(*    1. the crash slot, through the seam at the HOOKED law's guest,      *)
(*       into the record and the old guest (the record is timeless);      *)
(*    2. the record's snapshot slot at the quiescent picture              *)
(*       ([LogQuiet.P_fs_rec_quiet_acc]), which needs the started        *)
(*       counter's authority -- custody's own;                            *)
(*    3. the byte view opened exactly as the commit opens it             *)
(*       ([ProofEndOp.eo_snap_law_of_auth]): the seal empties its         *)
(*       exception set, and the cache picture it holds is the logged     *)
(*       view on the home set;                                           *)
(*    4. the hooked law ([LogSnapLaw.snap_law_ghost], parked in           *)
(*       [LogInv.log_ctx]) at [⊤ ∖ ↑crashN ∖ ↑fsbN]: the old guest, the    *)
(*       token and the waiters' hooks in; the new pair, the token and     *)
(*       each hook's [Q] out;                                             *)
(*    5. everything closed in reverse, at the SAME committed map.         *)
(*                                                                        *)
(*  A LEAF: nothing in the WAL's cone imports it, and it imports nothing  *)
(*  of the commit's walk ([ProofEndOp]).                                  *)
(* ====================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets coPset namespaces bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import RiscvExec.      (* [mWP], [thread_gen] *)
Require Import HartCustody.    (* [wp_crash_fupd]: the crash invariant's second opener *)
Require Import RiscvPtsto.     (* [crash_inv], [gen_cert], [riscv_sync_tok]/[riscv_sync_hook] *)
Require Import FsBlocks.       (* [fsbN], [exc_sealed_empty], [bytes_tie_exc_empty] *)
Require Import FsCrash.        (* [fs_crash_seam_at], [P_fs_comp], [P_fs_any_at] *)
Require Import LogSnapLaw.     (* [snap_law_ghost_run], [crashN_fsbN_disj] *)
Require Import LogInv.
Require Import LogQuiet.       (* [log_quiet], [P_fs_rec_quiet_acc], [eo_cache_body_sub] *)
Require Import CtxIdDefs.

Local Open Scope Z_scope.

Section LogGhostCommit.
  Context `{XI : CurCtx}.
  Context `{!riscvGS Σ, !lockG Σ, !diskGhostG Σ, !bioG Σ, !bioslotG Σ, !fsLogG Σ, !logG Σ,
            !fsLinkG Σ, !fsTopG Σ, !fsCrashG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---------------------------------------------------------------- *)
  (*  1.  THE TAIL'S QUIESCENT LOAN                                     *)
  (* ---------------------------------------------------------------- *)

  (* [LogQuiet.log_res_quiet_acc] restated over the CHECKED-OUT batch: the
     committer's tail holds [log_state] at [n = 0] (re-formed empty after a
     real commit, or found empty on the empty-log path) together with the
     transaction authority, and lends the same [log_quiet] the fast path
     lends -- returned unchanged. *)
  Lemma log_state_quiet_acc (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (ls : Z) :
    log_state bn γfs cov ls 0 ∅ ∅ -∗
    ghost_map_auth_frac (ln_tx γ) 1 (∅ : gmap nat unit) -∗
    ∃ (L : gmap Z (list (bv 8))) (M : log_mirror),
      log_quiet γ γfs cov ls L M ∗
      (log_quiet γ γfs cov ls L M -∗
       ghost_map_auth_frac (ln_tx γ) 1 (∅ : gmap nat unit) ∗
       log_state bn γfs cov ls 0 ∅ ∅).
  Proof using .
    iIntros "Hbatch Htx". rewrite /log_state.
    iDestruct "Hbatch" as (W L D M)
      "(%Hlen & %HLB & %Hnodup & %Hwok & Hncell & HW & Hjunk & HLauth & HDauth &
        Hcov & Hhdr & Hlogr & Hpool & Hmirh & %Hmhdr & %Hmtie)".
    iExists L, M. rewrite /log_quiet. iFrame "Htx HLauth Hmirh".
    iSplitR; [iPureIntro; split; [exact Hmhdr | exact Hmtie]|].
    iIntros "(Htx & HLauth & Hmirh & _ & _)". iFrame "Htx".
    (* the rows by name: a bare [iFrame] here spent 5 s *)
    iExists W, L, D, M.
    iFrame "Hncell HW Hjunk HLauth HDauth Hcov Hhdr Hlogr Hpool Hmirh". iPureIntro. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2.  THE GHOST COMMIT                                              *)
  (* ---------------------------------------------------------------- *)

  (* the byte view's namespace is inside the custody fupd's mask *)
  Lemma fsbN_sub_crash : (↑fsbN : coPset) ⊆ ⊤ ∖ ↑crashN.
  Proof using .
    apply subseteq_difference_r; [| exact fsbN_top].
    symmetry. exact crashN_fsbN_disj.
  Qed.

  (* A [mWP e -∗ mWP e] rule: at ANY expression of this generation, with the
     batch quiescent (the loan in hand) and the era's token, fire the
     waiters' hooks at a fresh durable pair at the unchanged committed map.
     The loan and the token come back unchanged, beside each hook's [Q]. *)
  Lemma log_ghost_commit (e : mexpr) (Qs : list (iProp Σ))
      (γ : log_names) (bn : bio_names) (γfs : fs_names) (cov : gset Z) (ls : Z)
      (dev : mword 32) (L : gmap Z (list (bv 8))) (M : log_mirror) :
    thread_gen e = Some gen_id ->
    log_ctx γ bn γfs cov ls dev -∗
    log_quiet γ γfs cov ls L M -∗
    riscv_sync_tok gen_id -∗
    ([∗ list] Q ∈ Qs, riscv_sync_hook gen_id Q) -∗
    (log_quiet γ γfs cov ls L M -∗ riscv_sync_tok gen_id -∗
       ([∗ list] Q ∈ Qs, Q) -∗ mWP e) -∗
    mWP e.
  Proof using .
    intros Hg. iIntros "#Hctx Hq HT HQs Hk".
    iPoseProof (log_ctx_gen_cert with "Hctx") as "#Hcert".
    iPoseProof (log_ctx_crash_inv with "Hctx") as "#Hcinv".
    iPoseProof (log_ctx_swap with "Hctx") as "#Hswlb".
    iPoseProof (log_ctx_seal with "Hctx") as "#Hbseal".
    iPoseProof (log_ctx_bytes with "Hctx") as "#Hbrow".
    iDestruct "Hbrow" as (Xv) "#Hbinv".
    iPoseProof (log_ctx_snap_law_ghost with "Hctx") as "#Hlg".
    iDestruct (snap_law_ghost_run with "Hlg") as (G) "[#Hseam #Hlaw]".
    iDestruct (log_ctx_gen_cert with "Hctx") as "#(_ & _ & Hreg)".
    iApply (wp_crash_fupd e
              (log_quiet γ γfs cov ls L M ∗ riscv_sync_tok gen_id ∗
               ([∗ list] Q ∈ Qs, Q))%I Hg
              with "Hcert Hcinv [Hq HT HQs] [Hk]");
      last first.
    { iIntros "(Hq & HT & HQs)". iApply ("Hk" with "Hq HT HQs"). }
    iIntros (n Hn) "Hsa Hc".
    (* ---- 1. the crash slot, through the seam, into the record and the
       old guest ---- *)
    iDestruct "Hseam" as "[Hto Hfrom]".
    iAssert (▷ P_fs_comp G cov ls)%I with "[Hc]" as "Hc".
    { iNext. iApply ("Hto" with "Hc"). }
    rewrite {1}/P_fs_comp.
    iMod (bi.later_exist_except_0 with "Hc") as (gt_o) "Hc".
    iDestruct "Hc" as "[Hany HG]".
    iMod "Hany".
    rewrite /P_fs_any_at /P_fs_named_at.
    iDestruct "Hany" as (dk) "(Himg & %Hext & Hrec)".
    (* ---- 2. the record's snapshot slot at the quiescent picture ---- *)
    rewrite /log_quiet.
    iDestruct "Hq" as "(Htx & HcL & Hmir & %Hhdr & %Htie)".
    iMod (P_fs_rec_quiet_acc gt_o cov ls dk n M L Hn Hhdr Htie
            with "Hreg Hswlb Hsa Hmir Hrec")
      as "(Hsa & Hmir & _ & Hrclose)".
    (* ---- 3. the byte view, as the commit opens it ---- *)
    rewrite /fs_bytes_inv.
    iMod (inv_acc (⊤ ∖ ↑crashN) fsbN with "Hbinv") as "[Hbody Hclose]";
      [exact fsbN_sub_crash |].
    iDestruct "Hbody" as (Lb C X)
      ">(Hba & HC & Hxa & %Hdom & %Hlens & %Htiex & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_sealed_empty with "Hxa Hbseal") as %->.
    assert (Hbt : bytes_tie Lb C) by (apply bytes_tie_exc_empty; exact Htiex).
    iDestruct (eo_cache_body_sub γfs L C with "HcL HC") as %Hsub.
    (* ---- 4. the hooked law ---- *)
    (* ...LENT the custody fupd's started auth, which it lends the merge
       (sync SY3-A1) and hands back *)
    iMod ("Hlaw" $! Lb C Qs gt_o n with "[%] [%] [%] [%] Hba Htx HG HT [//] Hsa HQs")
      as "(Hpair & HT & Hsa & HQs & Hba & Htx)";
      [exact Hdom | exact Hlens | exact Hbt | exact Hdm |].
    iMod ("Hclose" with "[Hba HC Hxa]") as "_".
    { iApply bi.later_intro. iExists Lb, C, ∅. by iFrame. }
    (* ---- 5. the new pair at the SAME committed map closes the record,
       and the seam the crash slot ---- *)
    iDestruct "Hpair" as (gt) "[Hdur HG]".
    rewrite (eo_restrict_of_sub C L (fs_home_set cov ls) Hdom Hsub).
    iDestruct ("Hrclose" $! gt with "Hdur") as "Hrec".
    iModIntro. iFrame "Hsa".
    iSplitL "Himg Hrec HG".
    { iNext. iApply "Hfrom". rewrite /P_fs_comp. iExists gt. iFrame "HG".
      rewrite /P_fs_any_at /P_fs_named_at. iExists dk. iFrame "Himg Hrec".
      iPureIntro. exact Hext. }
    iFrame "HT HQs". rewrite /log_quiet. iFrame "Htx HcL Hmir".
    iPureIntro. split; [exact Hhdr | exact Htie].
  Qed.

  (* ...at the one expression a kernel proof's goal ever has: a hart's
     [Loop] (the fast-path [sys_sync] and the committer's tail both apply
     it there, and the generation premise is closed here once). *)
  Lemma log_ghost_commit_loop (c : CPU) (Qs : list (iProp Σ))
      (γ : log_names) (bn : bio_names) (γfs : fs_names) (cov : gset Z) (ls : Z)
      (dev : mword 32) (L : gmap Z (list (bv 8))) (M : log_mirror) :
    log_ctx γ bn γfs cov ls dev -∗
    log_quiet γ γfs cov ls L M -∗
    riscv_sync_tok gen_id -∗
    ([∗ list] Q ∈ Qs, riscv_sync_hook gen_id Q) -∗
    (log_quiet γ γfs cov ls L M -∗ riscv_sync_tok gen_id -∗
       ([∗ list] Q ∈ Qs, Q) -∗ mWP (LoopE gen_id c)) -∗
    mWP (LoopE gen_id c).
  Proof using .
    apply (log_ghost_commit (LoopE gen_id c) Qs γ bn γfs cov ls dev L M).
    reflexivity.
  Qed.

End LogGhostCommit.

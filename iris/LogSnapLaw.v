(* ====================================================================== *)
(*  LogSnapLaw.v -- THE FILE SYSTEM'S LAW, AS THE WAL PARKS IT            *)
(*  (durable-disk lane C-8; claude-notes/design/durable-fs-plan.md         *)
(*   section 3, "Commit")                                                 *)
(*                                                                        *)
(*  The commit RECONSTRUCTS the file-system predicate at the one moment    *)
(*  the era's invariants are all clean (plan section 4), and the WAL       *)
(*  stays file-system-agnostic: what it holds is a PERSISTENT,             *)
(*  PURE-FACT-PRODUCING law, parked in [LogInv.log_ctx] beside block 1's   *)
(*  park.  Given the byte authority at the logged view [L] and "no         *)
(*  transaction is open", it yields [∃ S, snap_ok S L] and hands BOTH      *)
(*  authorities back.  It moves NO durable resource, which is why the      *)
(*  refutation of plan section 8 (deposited client fupds) does not bite.   *)
(*                                                                        *)
(*  IT IS ARITY-FREE, exactly as [SbPark.sb_parked] is: the mask it needs  *)
(*  to run in is CLOSED OVER (the era's file-system namespaces, which      *)
(*  [LogInv] cannot name and the ~75 files that thread [log_ctx] have no   *)
(*  business seeing), with the one fact a caller does need beside it --    *)
(*  that the mask is disjoint from the byte view's own [fsbN], so a        *)
(*  committer holding [fsbN] open can still run it.                       *)
(*                                                                        *)
(*  THE AUTHORITY IS TAKEN AND RETURNED, not borrowed through an           *)
(*  accessor: what the law PRODUCES is the next durable epoch itself       *)
(*  ([FsDurSnap.P_dur] over fresh names), and the two authorities it is    *)
(*  handed come straight back.  It still moves no durable resource: the    *)
(*  epoch is ALLOCATED, not carved out of anything the WAL owns.           *)
(*                                                                        *)
(*  IT USED TO CONCLUDE A PURE [exists S, snap_ok S L] (durable-disk lane   *)
(*  H2 moved it).  A pure conclusion crosses [end_op]'s lock release as a  *)
(*  Coq hypothesis for free; a resource has to be carried in the walk's    *)
(*  hand -- [ProofEndOp.eo_commit]/[eo_loop] carry it, and the copy loop   *)
(*  writes only log SLOTS, so the map it stands at never moves             *)
(*  ([ProofEndOp.eo_home_restrict_upd]).  What the move buys is that the   *)
(*  WAL's commit permit no longer ALLOCATES the file system's snapshot     *)
(*  from a value it cannot check: the file system builds its own epoch,    *)
(*  at the one ghost step where its invariants are open, and the WAL only  *)
(*  swaps the registry over ([FsDurSnap.dsnap_step_xfer]).                 *)
(*                                                                        *)
(*  WHY THE PREMISES ARE THE ROWS OF [FsBlocks.fs_bytes_body] AND NOT      *)
(*  [FsCollect.col_auth].  This file sits BELOW [LogInv], which sits below *)
(*  the inode region and hence below [FsCollect]; the rows are             *)
(*  [FsBlocks]', and spelling them here is what keeps [log_ctx]'s cone     *)
(*  clear of the file system's.  [FsCollect.col_auth] IS this list.        *)
(* ====================================================================== *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list sets coPset namespaces bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.

Require Import RiscvPtsto.     (* [riscvGS] -- IMPORTED: a capacity class
                                  used as a Context binder is inert
                                  otherwise (durable-notes)             *)
Require Import Xv6Cameras.     (* [logG] *)
Require Import BioDefs.        (* [BSIZE] *)
Require Import LogDefs.        (* [log_names], [ln_tx], [fs_restrict],
                                  [fs_home_set]                        *)
Require Import FsBlocks.       (* [fs_names], [fs_bytes], [logN]/[fsbN],
                                  [bytes_tie], [bytes_dom]             *)
Require Import FsDurSnap.      (* [P_dur_at]/[dur_pair]: the durable epoch registry *)
Require Import FsCrash.        (* [fs_crash_seam_at]: the seam at the law's
                                  guest, carried beside the law (round C) *)

Local Open Scope Z_scope.

Section SnapLaw.
  (* [fsLinkG]/[fsTopG] are the snapshot's two capacity classes; [diskImgG]
     -- the byte map's -- comes out of [riscvGS] ([RiscvPtsto.riscvF_diskGS]).
     Both are members of [Xv6G.xv6G], so every consumer that binds the
     bundle resolves them, and this file (like [LogInv]) sits BELOW the
     bundle and therefore names the members. *)
  (* ...plus the seam's two ([fsCrashG], [lockG]), because the arity-free
     law below carries the crash seam at its own guest (round C); both are
     [Xv6G.xv6G] members too. *)
  Context `{!riscvGS Σ, !fsLogG Σ, !logG Σ, !fsLinkG Σ, !fsTopG Σ,
            !fsCrashG Σ, !lockG Σ}.

  (* THE CONCLUSION, AS ONE NAME.  [LogInv] must be able to STATE the law
     and to hand its output on, and it deliberately imports no pure
     well-formedness layer (see its header); wrapping the epoch here is
     what keeps [FsDurSnap]'s vocabulary out of [log_ctx]'s text
     ([dv_of_D] itself is [LogDefs] vocabulary, which [LogInv] has).  [FsCollect.col_view C home] IS [fs_restrict (dv_of_D C) home],
     so this is the registry at exactly the map the commit jumps to.

     ...AND THE GUEST BESIDE IT (app-instances.md round C).  The law
     produces the PAIR [FsDurSnap.dur_pair]: the file system's snapshot and
     an OPAQUE guest [G] at the snapshot's map name, under a later.  The WAL
     never learns what [G] is -- the one law the tree builds is at
     [AppDur.app_guest] ([FsCollectAll.fs_snap_law_build]) -- and no file
     below [fileG] binds the application's record. *)
  Definition snap_law_out (G : gname -> iProp Σ)
      (C : gmap Z (list (bv 8))) (home : gset Z) : iProp Σ :=
    dur_pair G (fs_restrict (dv_of_D C) home).

  (* THE LAW, at a NAMED mask and a NAMED guest.  Every premise below is a
     row of [FsBlocks.fs_bytes_body] -- what a committer holds when it has
     [fsbN] open -- plus the empty transaction authority. *)
  Definition snap_law_at (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (N : coPset) (G : gname -> iProp Σ)
    : iProp Σ :=
    (□ (∀ (E : coPset) (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))),
          ⌜N ⊆ E⌝ -∗
          ⌜dom C = fs_home_set cov logstart⌝ -∗
          ⌜forall (b : Z) (bs : list (bv 8)),
             C !! b = Some bs -> length bs = BSIZE⌝ -∗
          ⌜bytes_tie Lb C⌝ -∗
          ⌜bytes_dom Lb (fs_home_set cov logstart)⌝ -∗
          ghost_map_auth (fs_bytes γfs) 1 Lb -∗
          ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) ={E}=∗
            snap_law_out G C (fs_home_set cov logstart)
            ∗ ghost_map_auth (fs_bytes γfs) 1 Lb
            ∗ ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit)))%I.

  (* ...and the arity-free form [LogInv.log_ctx] carries: the mask and the
     guest are closed over, with the one fact a holder still needs about
     the mask -- and, beside the law, THE CRASH SEAM AT THE SAME GUEST
     (round C), so that the committer reads seam and epoch off ONE handle
     and hands both to the commit permit at one [G]
     ([FsCrash.fs_commit_L_seq_permit]). *)
  Definition snap_law (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) : iProp Σ :=
    (∃ (N : coPset) (G : gname -> iProp Σ),
       ⌜(↑fsbN : coPset) ## N⌝ ∗
       fs_crash_seam_at G cov logstart ∗
       snap_law_at γ γfs cov logstart N G)%I.

  Global Instance snap_law_at_persistent γ γfs cov logstart N G :
    Persistent (snap_law_at γ γfs cov logstart N G).
  Proof. rewrite /snap_law_at. apply _. Qed.

  Global Instance snap_law_persistent γ γfs cov logstart :
    Persistent (snap_law γ γfs cov logstart).
  Proof. rewrite /snap_law. apply _. Qed.

  Lemma snap_law_intro (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (N : coPset) (G : gname -> iProp Σ) :
    (↑fsbN : coPset) ## N ->
    fs_crash_seam_at G cov logstart -∗
    snap_law_at γ γfs cov logstart N G -∗ snap_law γ γfs cov logstart.
  Proof.
    intros Hdj. iIntros "#Hseam #H". rewrite /snap_law. iExists N, G.
    iSplitR; [iPureIntro; exact Hdj |]. iFrame "Hseam". iExact "H".
  Qed.

  (* THE READING A COMMITTER TAKES.  It holds [fsbN] open -- that is where
     the byte authority came from -- so the mask it can offer the law is
     everything BUT [fsbN], and the closed-over disjointness is exactly
     what makes that enough.  Stated at [⊤ ∖ ↑fsbN] and not at a general
     [E ∖ ↑fsbN]: the closure names no upper bound on its own mask other
     than [⊤], so a caller at a smaller mask must take [snap_law_at]
     itself (which the definition hands out unchanged) and discharge
     [N ⊆ E] however its own opening lets it. *)
  Lemma snap_law_run (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) :
    dom C = fs_home_set cov logstart ->
    (forall (b : Z) (bs : list (bv 8)), C !! b = Some bs -> length bs = BSIZE) ->
    bytes_tie Lb C ->
    bytes_dom Lb (fs_home_set cov logstart) ->
    snap_law γ γfs cov logstart -∗
    ghost_map_auth (fs_bytes γfs) 1 Lb -∗
    ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) ={⊤ ∖ ↑fsbN}=∗
      (* the epoch AND the seam, at the law's own guest (round C) *)
      (∃ G : gname -> iProp Σ,
         fs_crash_seam_at G cov logstart ∗
         snap_law_out G C (fs_home_set cov logstart))
      ∗ ghost_map_auth (fs_bytes γfs) 1 Lb
      ∗ ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit).
  Proof.
    intros Hdom Hlens Htie Hdm. iIntros "#Hlaw Hb Ht".
    iDestruct "Hlaw" as (N G Hdj) "[#Hseam #Hbody]".
    iMod ("Hbody" $! (⊤ ∖ ↑fsbN) Lb C with "[%] [%] [%] [%] [%] Hb Ht")
      as "(Hout & Hb & Ht)";
      [| exact Hdom | exact Hlens | exact Htie | exact Hdm |].
    2: { iModIntro. iFrame "Hb Ht". iExists G. iFrame "Hseam". iExact "Hout". }
    (* the law's mask misses [fsbN] -- the one namespace a committer, which
       is holding the byte view open, cannot offer it *)
    intros x Hx. apply elem_of_difference. split.
    - apply elem_of_top'.
    - intros Hxl. exact (Hdj x Hxl Hx).
  Qed.

End SnapLaw.

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
(*  accessor: the law's whole content is a PURE fact, and                  *)
(*  [FsCollectAll.pure_keep] is why producing it costs nothing.            *)
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
Require Import FsWf.           (* [dv_of_D] *)
Require Import FsBlocks.       (* [fs_names], [fs_bytes], [logN]/[fsbN],
                                  [bytes_tie], [bytes_dom]             *)
Require Import FsDurSnap.      (* [snap_ok], [fs_state_rec] *)

Local Open Scope Z_scope.

(* THE CONCLUSION, AS ONE NAME.  [LogInv] must be able to STATE the law and
   to read its output, and it deliberately imports no pure well-formedness
   layer (see its header); wrapping the existential here is what keeps
   [FsWf] and [FsDurSnap] out of [log_ctx]'s import list while leaving the
   proposition exactly what [FsCollect.col_snap_ok_ex] concludes --
   [FsCollect.col_view C home] IS [fs_restrict (dv_of_D C) home]. *)
Definition snap_law_ok (C : gmap Z (list (bv 8))) (home : gset Z) : Prop :=
  exists S : fs_state_rec, snap_ok S (fs_restrict (dv_of_D C) home).

Section SnapLaw.
  Context `{!riscvGS Σ, !fsLogG Σ, !logG Σ}.

  (* THE LAW, at a NAMED mask.  Every premise below is a row of
     [FsBlocks.fs_bytes_body] -- what a committer holds when it has [fsbN]
     open -- plus the empty transaction authority. *)
  Definition snap_law_at (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (N : coPset) : iProp Σ :=
    (□ (∀ (E : coPset) (Lb : gmap Z (bv 8)) (C : gmap Z (list (bv 8))),
          ⌜N ⊆ E⌝ -∗
          ⌜dom C = fs_home_set cov logstart⌝ -∗
          ⌜forall (b : Z) (bs : list (bv 8)),
             C !! b = Some bs -> length bs = BSIZE⌝ -∗
          ⌜bytes_tie Lb C⌝ -∗
          ⌜bytes_dom Lb (fs_home_set cov logstart)⌝ -∗
          ghost_map_auth (fs_bytes γfs) 1 Lb -∗
          ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit) ={E}=∗
            ⌜snap_law_ok C (fs_home_set cov logstart)⌝
            ∗ ghost_map_auth (fs_bytes γfs) 1 Lb
            ∗ ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit)))%I.

  (* ...and the arity-free form [LogInv.log_ctx] carries: the mask is
     closed over, with the one fact a holder still needs about it. *)
  Definition snap_law (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) : iProp Σ :=
    (∃ N : coPset,
       ⌜(↑fsbN : coPset) ## N⌝ ∗ snap_law_at γ γfs cov logstart N)%I.

  Global Instance snap_law_at_persistent γ γfs cov logstart N :
    Persistent (snap_law_at γ γfs cov logstart N).
  Proof. rewrite /snap_law_at. apply _. Qed.

  Global Instance snap_law_persistent γ γfs cov logstart :
    Persistent (snap_law γ γfs cov logstart).
  Proof. rewrite /snap_law. apply _. Qed.

  Lemma snap_law_intro (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (N : coPset) :
    (↑fsbN : coPset) ## N ->
    snap_law_at γ γfs cov logstart N -∗ snap_law γ γfs cov logstart.
  Proof.
    intros Hdj. iIntros "#H". rewrite /snap_law. iExists N.
    iSplitR; [iPureIntro; exact Hdj |]. iExact "H".
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
      ⌜snap_law_ok C (fs_home_set cov logstart)⌝
      ∗ ghost_map_auth (fs_bytes γfs) 1 Lb
      ∗ ghost_map_auth (ln_tx γ) 1 (∅ : gmap nat unit).
  Proof.
    intros Hdom Hlens Htie Hdm. iIntros "#Hlaw Hb Ht".
    iDestruct "Hlaw" as (N Hdj) "#Hbody".
    iApply ("Hbody" $! (⊤ ∖ ↑fsbN) Lb C with "[%] [%] [%] [%] [%] Hb Ht");
      [| exact Hdom | exact Hlens | exact Htie | exact Hdm].
    (* the law's mask misses [fsbN] -- the one namespace a committer, which
       is holding the byte view open, cannot offer it *)
    intros x Hx. apply elem_of_difference. split.
    - apply elem_of_top'.
    - intros Hxl. exact (Hdj x Hxl Hx).
  Qed.

End SnapLaw.

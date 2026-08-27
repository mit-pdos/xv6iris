(* ====================================================================== *)
(*  IregClean.v -- THE COMMIT'S READING OF THE LOCKED REGISTRY            *)
(*  (durable-disk lane A item 5; plan sections 3, 4, 4b)                  *)
(*                                                                        *)
(*  ONE lemma, in two forms.  It is the step the group commit takes at    *)
(*  [outstanding = 0]:                                                    *)
(*                                                                        *)
(*      no transaction is open                                            *)
(*   => no inum's well-formedness row is SUSPENDED                        *)
(*   => the file system's abstract map is [FsDurSnap.snap_local].         *)
(*                                                                        *)
(*  The first step is [InodeRegion.ireg_clean_acc] (the registry parks an *)
(*  arming transaction's own [ln_tx] element, so an empty [ln_tx]         *)
(*  authority refutes every registry entry); the second is the registry's *)
(*  pure row [InodeRegion.ftop_clean], read at the empty registry.        *)
(*                                                                        *)
(*  WHY IT IS ITS OWN FILE.  [snap_local] lives in [FsDurSnap] and the    *)
(*  registry in [InodeRegion], and neither file is on the other's cone;   *)
(*  putting the reading in either one would drag the other's cone into a  *)
(*  5100-line file for one entailment.  ProofEndOp is on NEITHER cone, so *)
(*  lane C can require this file from the commit path with no cycle --    *)
(*  and the plan's parked law (section 3) can be discharged from it       *)
(*  without ProofEndOp naming the file system at all.                     *)
(* ====================================================================== *)

Require Import stdpp.base stdpp.gmap stdpp.sets.
From iris.base_logic.lib Require Import invariants ghost_map.
From iris.proofmode Require Import proofmode.

Require Import RiscvPtsto.    (* [riscvGS] / [diskGhostG] -- IMPORTED, not merely
                                 required: a capacity class used as a Context
                                 binder is inert otherwise (durable-notes)  *)
Require Import Xv6Cameras.    (* [logG], [op_entry]                        *)
Require Import LogDefs.       (* [log_names], [ln_tx]                      *)
Require Import LogInv.        (* [log_tx_empty_of_ops]                     *)
Require Import FsState.       (* [fs_state_rec], [fss_inodes], [fsTopG]    *)
Require Import FsNode.  (* [fs_node], [inode_local]                  *)
Require Import FsBlocks.      (* [fs_names], [fs_top]                      *)
Require Import FsDurSnap.     (* [snap_local]                              *)
Require Import InodeRegion.   (* [ftopN], [ftop_inv], [ireg_clean_acc]     *)
Require Import IcacheRef.     (* [icfg], [icfg_log]                        *)

Local Open Scope Z_scope.

Section IregClean.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ, !fsTopG Σ, !fsLinkG Σ}.
  Context `{ICFG : icfg}.

  (* ---- (a) THE ACCESSOR, at the empty transaction authority ---------- *)

  (* The map's authority comes OUT and goes back unchanged: the reading
     moves no resource, which is what lets the commit take it at the same
     ghost step as its own byte work (plan section 3, "it moves NO durable
     resource").  The [ln_tx] authority is BORROWED, not consumed -- the
     committer holds it inside [LogInv.log_res] and needs it back. *)
  Lemma ireg_snap_local_acc (E : coPset) (γfs : fs_names) :
    ↑ftopN ⊆ E ->
    (ftop_inv γfs : iProp Σ) -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ={E, E ∖ ↑ftopN}=∗
      ∃ I : gmap Z fs_node,
        ghost_map_auth (fs_top γfs) 1 I ∗
        ⌜forall S : fs_state_rec, fss_inodes S = I -> snap_local S⌝ ∗
        ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ∗
        (ghost_map_auth (fs_top γfs) 1 I ={E ∖ ↑ftopN, E}=∗ True).
  Proof.
    iIntros (HE) "#Hi Htxa".
    iMod (ireg_clean_acc E γfs HE with "Hi Htxa")
      as (I) "(Hta & %Hloc & Htxa & Hclose)".
    iModIntro. iExists I. iFrame "Hta Htxa Hclose".
    iPureIntro. intros S HS i n Hin.
    rewrite HS in Hin. exact (Hloc i n Hin).
  Qed.

  (* ---- (b) ...AS THE COMMIT MEETS IT: off the LEDGER ------------------ *)

  (* [LogInv.log_res] carries the transaction authority beside the ledger's
     with [size T = size om] ([log_tx_empty_of_ops] is that tie read at
     zero), and a commit is exactly the step at which the ledger is empty.
     So this is the form with no ghost-state premise the WAL does not
     already hold. *)
  Lemma ireg_snap_local_of_ops (E : coPset) (γfs : fs_names)
      (om : gmap nat op_entry) (T : gmap nat unit) :
    ↑ftopN ⊆ E ->
    size T = size om ->
    om = ∅ ->
    (ftop_inv γfs : iProp Σ) -∗
    ghost_map_auth (ln_tx icfg_log) 1 T ={E, E ∖ ↑ftopN}=∗
      ∃ I : gmap Z fs_node,
        ghost_map_auth (fs_top γfs) 1 I ∗
        ⌜forall S : fs_state_rec, fss_inodes S = I -> snap_local S⌝ ∗
        ghost_map_auth (ln_tx icfg_log) 1 T ∗
        (ghost_map_auth (fs_top γfs) 1 I ={E ∖ ↑ftopN, E}=∗ True).
  Proof.
    iIntros (HE Hsz Hom) "#Hi Htxa".
    rewrite (log_tx_empty_of_ops om T Hsz Hom).
    iMod (ireg_snap_local_acc E γfs HE with "Hi Htxa") as (I) "H".
    iModIntro. iExists I. iExact "H".
  Qed.

End IregClean.

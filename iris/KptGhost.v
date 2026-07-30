(* KptGhost.v -- the ONE-SHOT AGREEMENT on the shared kernel page table.

   The kernel page table is SHARED between harts (claude-notes/projects/
   kpt-share.md): the tree itself lives in one Iris invariant, so no hart
   owns it, and a hart may not state any fact about the CURRENT tree.  What
   a hart keeps across steps is a persistent SNAPSHOT.

   The snapshot needs no order.  The only mutation a running machine
   performs on an installed table is the Svadu/ADUE A/D write-back, and that
   leaves the A/D-CANONICAL table [PtTree.ptree_canon] literally UNCHANGED
   ([PtTree.ptree_canon_set_leaf]); cached-entry coherence depends on the
   table only through that canonical form ([PtTree.tlb_ok_pt_canon]).  So
   the harts simply AGREE on it, and a write-back costs no ghost update.

   The RA is the standard one-shot [csum (excl unit) (agree …)] over
   [leibnizO ptree], with its [inG] and gname in [riscvGS] (RiscvPtsto.v):
     - [kpt_unset]  = [Cinl (Excl ())], minted at adequacy, before any page
                      table exists.  Spent once.
     - [kpt_shoot]  turns it into
       [kpt_lb t]   = [Cinr (to_agree (ptree_canon t))], PERSISTENT.
     - [kpt_lb_agree] reads the canonical-form equality back out;
       [kpt_lb_canon] moves a snapshot along a canonical-form equality --
       which is all the write-back re-close needs.                        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap namespaces.
From iris.algebra Require Import csum excl agree.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
Require Import RiscvPtsto.
Require Import PtTree.

Section KptGhost.
  Context `{!riscvGS Σ}.

  (* the unset one-shot token: no kernel page table yet *)
  Definition kpt_unset : iProp Σ :=
    own kpt_name (Cinl (Excl ()) : kptR).

  (* THE SNAPSHOT, stated at a canonical table.  Persistent, freely
     duplicable, carried in every hart's translation residue. *)
  Definition kpt_lb (t : ptree) : iProp Σ :=
    own kpt_name (Cinr (to_agree (ptree_canon t : leibnizO ptree)) : kptR).

  Global Instance kpt_unset_timeless : Timeless kpt_unset.
  Proof. apply _. Qed.
  Global Instance kpt_lb_timeless t : Timeless (kpt_lb t).
  Proof. apply _. Qed.
  Global Instance kpt_lb_persistent t : Persistent (kpt_lb t).
  Proof. rewrite /kpt_lb. apply own_core_persistent, Cinr_core_id, _. Qed.

  (* THE ONE SHOT: fix the canonical table, once *)
  Lemma kpt_shoot (t : ptree) : kpt_unset ==∗ kpt_lb t.
  Proof.
    iIntros "H". iApply (own_update with "H").
    apply cmra_update_exclusive. done.
  Qed.

  (* THE AGREEMENT: two snapshots have the same canonical table *)
  Lemma kpt_lb_agree (t t' : ptree) :
    kpt_lb t -∗ kpt_lb t' -∗ ⌜ ptree_canon t = ptree_canon t' ⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Cinr_op Cinr_valid in Hv.
    iPureIntro. exact (to_agree_op_inv_L _ _ Hv).
  Qed.

  (* moving a snapshot along a canonical-form equality: this IS the
     write-back re-close (the A/D write-back does not move [ptree_canon],
     so there is no ghost update at all) *)
  Lemma kpt_lb_canon (t t' : ptree) :
    ptree_canon t = ptree_canon t' -> kpt_lb t -∗ kpt_lb t'.
  Proof. intros He. rewrite /kpt_lb He. iIntros "H". iExact "H". Qed.
End KptGhost.

(* THE NAMESPACE of the shared kernel page table's invariant (the body is
   [KptShare.kpt_body]).  Defined at top level and free of any context,
   because [SRegime.s_regime]'s absorb field carries the mask premise
   [↑kptN ⊆ E] and must therefore name it. *)
Definition kptN : namespace := nroot .@ "kpt".

(* allocation of the ghost NAME at adequacy, at the unset value *)
Lemma kpt_ghost_alloc `{!inG Σ kptR} :
  ⊢ |==> ∃ γ : gname, own γ (Cinl (Excl ()) : kptR).
Proof. iApply own_alloc. done. Qed.

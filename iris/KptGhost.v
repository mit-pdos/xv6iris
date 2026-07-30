(* KptGhost.v -- the A/D-MONOTONE SNAPSHOT GHOST over page-table trees.

   The kernel page table is SHARED between harts (claude-notes/projects/
   kpt-share.md): the tree itself lives in one Iris invariant, so no hart
   owns it, and a hart may not state any fact about the CURRENT tree.  What
   a hart DOES keep across steps is a SNAPSHOT: "at some earlier moment the
   shared tree was [t0]" -- together with the guarantee that the live tree
   can only have moved UP the A/D-write-back order [PtTree.ptree_ad_le]
   since.  That is exactly enough, because every fact a hart's cached TLB
   entries rest on is stable along that order
   ([PtTree.tlb_ok_pt_ad_mono]).

   The encoding is the standard monotone one: [auth] over Iris's monotone
   resource algebra [iris.algebra.mra], instantiated at the preorder
   [ptree_ad_le0] -- [ptree_ad_le] extended to [option ptree] with [None]
   as a BOTTOM element.  The bottom is what lets the ghost be allocated at
   adequacy (before the kernel table exists) and be initialised later, at
   the tree kvminit actually built: a monotone auth can only grow, so it
   cannot be "reset" the way [kmap_auth] is.
     - [kpt_ad_auth t] = [● to_mra (Some t)], the authoritative live tree;
       it rides inside the shared invariant (KptShare.v) next to the tree
       ownership itself, so it is always in step with it.
     - [kpt_lb t0]     = [◯ to_mra (Some t0)], PERSISTENT (every [mra]
       element is [CoreId]) -- a snapshot a hart keeps forever, freely
       duplicable, carried in the hart's per-hart translation residue.
     - [kpt_ad_none]   = [● to_mra None], the uninitialised auth handed to
       the boot client; [kpt_ad_init] turns it into the first
       [kpt_ad_auth].
   [kpt_lb_valid] reads the order back out; [kpt_ad_update] advances the
   auth along the order and mints the new snapshot in one step (which is
   what an absorb does: write A/D back, bump, re-snapshot).

   A standalone class (like [fdslotG]/[kallocG]) rather than a [riscvGS]
   field: nothing below KptShare.v needs it, and the functor is wired at
   adequacy beside the other pre-ghost classes.                          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap relations namespaces.
From iris.algebra Require Import auth mra.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
Require Import PtTree.

(* [ptree_ad_le] with a bottom element: the ghost's carrier.  [None] means
   "no kernel table yet" and is below everything. *)
Definition ptree_ad_le0 (o o' : option ptree) : Prop :=
  match o with
  | None => True
  | Some t => match o' with
              | None => False
              | Some t' => ptree_ad_le t t'
              end
  end.

Global Instance ptree_ad_le0_preorder : PreOrder ptree_ad_le0.
Proof.
  split.
  - intros [t |]; [apply ptree_ad_le_refl | exact I].
  - intros [t1 |] [t2 |] [t3 |] H12 H23; try exact I; try contradiction.
    exact (ptree_ad_le_trans t1 t2 t3 H12 H23).
Qed.

(* the monotone RA over (optional) trees, ordered by A/D write-back *)
Definition kptUR : ucmra := authUR (mraUR ptree_ad_le0).

Class kptGpreS (Σ : gFunctors) := { kpt_pre_inG :: inG Σ kptUR }.
Class kptG (Σ : gFunctors) := KptG {
  kpt_inG :: inG Σ kptUR;
  kpt_name : gname;
}.
Global Instance kptG_preS `{!kptG Σ} : kptGpreS Σ :=
  {| kpt_pre_inG := kpt_inG |}.
Definition kptΣ : gFunctors := #[GFunctor kptUR].
Global Instance subG_kptΣ {Σ} : subG kptΣ Σ -> kptGpreS Σ.
Proof. solve_inG. Qed.

Section KptGhost.
  Context `{!kptG Σ}.

  (* the live tree, authoritative -- rides inside the shared invariant *)
  Definition kpt_ad_auth (t : ptree) : iProp Σ :=
    own kpt_name (● (to_mra (Some t) : mraUR ptree_ad_le0)).

  (* a persistent SNAPSHOT: the shared tree was [t0] at some earlier point,
     hence the live tree is [ptree_ad_le]-above [t0] *)
  Definition kpt_lb (t0 : ptree) : iProp Σ :=
    own kpt_name (◯ (to_mra (Some t0) : mraUR ptree_ad_le0)).

  (* the UNINITIALISED auth: what adequacy mints, before any page table
     exists.  Spent once, in main's kvm assembly. *)
  Definition kpt_ad_none : iProp Σ :=
    own kpt_name (● (to_mra None : mraUR ptree_ad_le0)).

  Global Instance kpt_ad_auth_timeless t : Timeless (kpt_ad_auth t).
  Proof. apply _. Qed.
  Global Instance kpt_ad_none_timeless : Timeless kpt_ad_none.
  Proof. apply _. Qed.
  Global Instance kpt_lb_timeless t : Timeless (kpt_lb t).
  Proof. apply _. Qed.
  Global Instance kpt_lb_persistent t : Persistent (kpt_lb t).
  Proof. rewrite /kpt_lb. apply own_core_persistent, auth_frag_core_id, _. Qed.

  (* THE agreement: a snapshot is below the live tree *)
  Lemma kpt_lb_valid (t t0 : ptree) :
    kpt_ad_auth t -∗ kpt_lb t0 -∗ ⌜ ptree_ad_le t0 t ⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    iPureIntro.
    exact (proj1 (to_mra_included (Some t0) (Some t)) Hincl).
  Qed.

  (* take a snapshot of the live tree *)
  Lemma kpt_lb_get (t : ptree) :
    kpt_ad_auth t ==∗ kpt_ad_auth t ∗ kpt_lb t.
  Proof.
    iIntros "Ha". rewrite -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    apply (mra_local_update_get_frag (Some t) (Some t)).
    apply ptree_ad_le_refl.
  Qed.

  (* advance the live tree along the order, and snapshot the result *)
  Lemma kpt_ad_update (t t' : ptree) :
    ptree_ad_le t t' ->
    kpt_ad_auth t ==∗ kpt_ad_auth t' ∗ kpt_lb t'.
  Proof.
    intros Hle. iIntros "Ha". rewrite -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    exact (mra_local_update_grow (Some t) ε (Some t') Hle).
  Qed.

  (* INITIALISE at the tree kvminit built *)
  Lemma kpt_ad_init (t : ptree) :
    kpt_ad_none ==∗ kpt_ad_auth t ∗ kpt_lb t.
  Proof.
    iIntros "Ha". rewrite -own_op.
    iApply (own_update with "Ha").
    apply auth_update_alloc.
    exact (mra_local_update_grow None ε (Some t) I).
  Qed.
End KptGhost.

(* THE NAMESPACE of the shared kernel page table's invariant (the body is
   [KptShare.kpt_body]).  Defined HERE, at top level and free of any ghost
   context, because [SRegime.s_regime]'s absorb field carries the mask
   premise [↑kptN ⊆ E] and must therefore name it -- without dragging
   [kptG Σ] into the context of every file that mentions a regime. *)
Definition kptN : namespace := nroot .@ "kpt".

(* allocation of the ghost NAME at adequacy, at the uninitialised value *)
Lemma kpt_ghost_alloc `{!kptGpreS Σ} :
  ⊢ |==> ∃ γ : gname, own γ (● (to_mra None : mraUR ptree_ad_le0)).
Proof.
  iApply own_alloc. apply auth_auth_valid. done.
Qed.

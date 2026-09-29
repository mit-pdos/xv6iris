(* AppTree.v -- THE TREE APPLICATION: a process's subtree of the live
   namespace, owned as a CLAIM IN THE APPLICATION INVARIANT.

   Design of record: claude-notes/design/user-tree.md (TL-0), lane TL-2,
   on TL-1's pure layer [TreeView.v].  [AppEcho.v] is the mould: its
   claim [echo_taint ∨ (⌜echo_fs_pure av⌝ ∗ cons_state)] is the WHOLE-FS
   special case of this one, and every shape below -- the taint arm, the
   claim law that hands the claim back, the per-delta step wands, the
   transport, the supply -- is echo's at a per-owner ownership map.

   THE CLAIM (design section 2).  [tree_pred c r av] is TAINTED or: the
   application holds the AUTHORITY of an ownership map [own : gmap gname
   (Z * ttree)] -- generation [g] owns the subtree [t] at the root [root]
   -- the map is WELL FORMED at the view ([TreeView.own_wf]: the view is
   tree-shaped, every root is a directory, the roots are pairwise
   non-nested) and it is EXACT: every entry's recorded tree IS the view's
   subtree at its root ([tree_exact]).  A process holds the map ELEMENT
   [tree_own r g root t = g ↪[r] (root, t)], and reads its own subtree off
   the claim by [ghost_map_lookup] -- the stable form
   design/fs-syscall-specs.md section 2 wanted, as a claim rather than as
   a fraction (design/user-exec.md's EX-2 is the refutation of the
   fraction).

   TWO DEVIATIONS FROM THE DESIGN PAGE'S SKETCH, both simplifications:
   (1) the authority is WHOLE ([ghost_map_auth_frac r 1]) and not a half.  The
       half in the sketch was copied off [AppInv.app_body]'s tie to the
       kernel's map, where the OTHER half is the kernel's; here nobody
       else holds one, and an owner's move is a [ghost_map_update], which
       needs the whole.  (2) the claim's third conjunct is the PURE
       [tree_exact] rather than a [[∗ map]] of pure facts -- the same
       proposition, one [iDestruct] cheaper.

   ============ THE THREE FINDINGS, and what they cost ============

   FINDING 1 (THE SEAM) -- CLOSED BY LANE TL-3W, design/user-tree.md
   section 7.2, AND CLOSED WITH NO SEAM.  (Lane SEAM-I has since made
   [AppInv.app_step] a BASIC UPDATE -- design section 9.1 -- but the
   argument below is unaffected and TL-3W's two-phase move stands: what
   the seam buys is the TAINT's mint, [TreeMove.tree_app_step_bump], not
   an owner's paid move.)  What TL-2 found stands as stated at the
   update-free reading: [AppInv.app_step] was an UPDATE-FREE wand applied
   under the invariant's later, and moving an owner's recorded subtree is
   a GHOST MAP UPDATE, so an owner's move cannot be paid BY THE STEP
   ALONE --
     - a plain wand can TRANSFER resources but cannot run a frame-
       preserving update;
     - wrapping the claim in [|==>] makes the wand able to update, but
       then the CLAIM LAW is unprovable: a pure fact cannot be read out
       from under a basic update;
     - a WINDOW made of two CLAIM-UPDATES re-establishes nothing: at the
       resync the owner must prove [subtree av root = Some t_new] at the
       invariant's CURRENT view, which only the party that SEES the move
       knows.
   WHAT TL-2 DID NOT USE is that every write-kind fire is ALREADY
   TWO-PHASE and its SECOND phase is handed [I'] with
   [abs_view I' = δ (abs_view I)]: that is the window, and it is a window
   that sees the move.  So the move splits, with no [AppInv] change at
   all (the seam of section 7.1 stays designed and deferred):
     PHASE 1  [tree_step_move_gen] and its legs -- an update-free wand,
              which [app_step] takes verbatim (and still does): the DEED and a
              fresh TOKEN are PARKED in the entry's SLOT, which leaves
              the exact arm and says nothing until phase 2;
     PHASE 2  [tree_resync] -- the ticket identifies the entry, the exact
              arm is REFUTED by TL-1's INSIDE lemma at the post view, the
              deed comes back, the entry moves, the slot closes exact.
   TL-2's [tree_move_write] / [tree_move_trunc] / [tree_move_create] /
   [tree_move_unl_ent] / [tree_move_gen] are RETIRED into that shape;
   their content is section 1i's pure layer, which both phases read.
   [TreeMove.v] joins the two phases at the write fire and [UkTreeWrite.v]
   carries the receipt to the U tier.

   THE SHAPE OF THE CLAIM MOVED WITH IT (section 2a below): TL-2's global
   [tree_exact] became a PER-ENTRY SLOT, because an entry whose owner is
   mid-move has no exactness at all; and the deed is SPLIT ACROSS TWO
   GHOST MAPS, because phase 2 must identify its entry while holding
   nothing of it and the parked deed must be the WHOLE element (only
   [DfracOwn 1] in the claim refutes the in-flight arm for a FROZEN
   reader).  See [tree_names] for the full argument.

   FINDING 2 (exec's (W)).  [PinnedObs.pin_resolves_at] -- what
   [ExecRun.exec_walk_of_pin] and [pobs_walk] take -- pins the walk's
   terminal row as an [anode], LINK COUNT INCLUDED.  The tree claim pins
   a node's CONTENT and not its count (TL-1's ruling: [absnode], nlink
   dropped), so [subtree_resolves_pin_file] yields the row only up to an
   EXISTENTIAL count and the pin is unsuppliable AS STATED.  Nothing in
   the walk needs the count ([pobs_hop] reads only the [arun] conjunct);
   it is the terminal IDENTIFICATION ([pobs_node], [ExecBundle.
   ex_node_id]) that asks for the row on the nose.  So [exec_walk_of_own]
   is NOT landed; what is landed is everything on this side of the seam:
   the claim law in both shapes, and [tree_resolves_abs], the pin's
   content at an existential count, ready for an absnode-level
   [pin_resolves_abs] / [ex_node_id] variant (additive, one definition
   each in [PinnedObs.v] and [ExecRun.v]).

   FINDING 3 (grant).  A parent CANNOT keep a hole-punched subtree: the
   claim is EXACT ("my subtree IS [t]") and [own_wf] wants the roots
   pairwise NON-NESTED, so design section 3's "[t_P] at [root_P] becomes
   [t_P ∖ t_C] plus a new entry" is not expressible over TL-1's
   [subtree].  What IS expressible, and what [tree_grant] below is, is
   the HAND-DOWN: the parent's entry is retired and the child's entry at
   a sub-root of it is born.  A hole-punched partition needs a new PURE
   reading in TL-1 ([subtree_except av root R]) and a disjointness
   theorem at it.

   FINDING 4 (THE ERA'S FIRST DEED HAS NO CHANNEL).  Nobody can mint a
   deed at "/" out of a running claim: the insert needs the new root to
   be NON-NESTED with every existing root, which at "/" means the
   ownership map is EMPTY -- and the claim cannot see that its own map
   is empty (a reader holds no deed, and there is no "the partition is
   empty" credential).  Nor can [Happ_init] hand one over: its
   conclusion has no room beside the claim, and App.v's own note says
   its instance never reaches a boot -- every era founds from the
   TRANSPORT's clone.  So the first deed must ride [App.app_boot], which
   the transport CAN build, because the view is available OUTSIDE the
   later (echo's [cons_inum av] trick decides the arm there): allocate
   the fresh map at [{[ g := (ROOTINO, t) ]}] when [subtree av ROOTINO =
   Some t].  WHAT BLOCKS IT is the OTHER arm: [app_boot] is av-FREE, and
   "this view has no root directory" has no av-free spelling, so the
   disjunction collapses to [emp].  THE FIX, priced: the claim grows one
   conjunct, [⌜adir_at av ROOTINO⌝] (or [is_Some (subtree av ROOTINO)]),
   which every landed leg preserves -- a fresh inum is not the root, a
   write/truncate is at a FILE row, and create's and unlink's entry legs
   leave a directory a directory -- and then the transport's None arm is
   refuted from the claim it was handed.  [tree_init_at] below is the
   mint at a FRESH instance, which is the era-0 shape but not the era's.
   Until that conjunct lands, [app_boot] here is [emp] and the tree
   application's owners are the ones a future [tree_grant] hands down
   from the first.

   WHAT ELSE IS OWED, and to whom:
     - [own_wf_ent] (create's PARENT leg alone) and the
       last-link [own_wf] for [delta_unl_tgt] at a row that is nobody's
       root: TL-1 landed [own_wf_write] / [own_wf_create] (FUSED) /
       [own_wf_arm] / [own_wf_unl_ent] / [own_wf_unl_tgt], so the moves
       below are write, truncate, the fused create, and unlink's entry
       leg -- [own_wf_trunc] is proved HERE, in section 1f', because it
       is [own_wf_write]'s twin line for line and TL-3 wants the move;
       it belongs in TreeView.v and moves there when a TL-1 lane runs.
       The PER-LEG create (its parent leg alone) is a harder one: it
       needs an [aview_tree_wf_ent], whose unique-parenthood conjunct
       wants "nothing else names the armed inum".  LANE TL-3W FOUND
       WHERE THAT BITES: [FsAbsDelta.cre_pre] puts the child's row IN
       the pre-view, so the leg a fire actually offers an owner is the
       parent leg alone and the FUSED move below does not reach it.  See
       [TreeMove.v] section 4 for the full accounting (and for the two
       further walls on the create-family BUNDLE: the child's unarm leg,
       and the missing pinned parent-prefix walk).
     - the unlink TARGET leg at the last link needs "the row is nobody's
       root" -- design section 3's "an owner never unlinks a root" --
       which is a fact about the HIDDEN ownership map that no mover
       holds.  It is payable only as a strengthening of the claim (every
       root is named, or is [ROOTINO]); recorded, not taken.
     - the ledger [app_R] below is a PLACEHOLDER that carries the taint
       counter and never bumps it, so the taint is not mintable and the
       SUPPLY (hence the generic slot) is unobtainable at this record.
       TL-4 gives it echo's shape: the step that reads the discipline is
       where an unpaid move is recorded.

   WHAT IS DELIBERATELY NOT HERE: a theorem.  [Happ_init] at the image's
   view is gated on a pure fact about the mkfs image ([aview_tree_wf]),
   and [Hinit_boot] is the first process's exec bundle -- TL-4's, both.
   The application is a DEFINITION with its obligations as free-standing
   lemmas (durable-notes.md's GAP-premise rule), exactly as [AppEcho]
   leaves its two. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl dfrac.
From iris.base_logic.lib Require Import own ghost_map mono_nat invariants.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [trace_shape], [obs_boots], [ObsPowerOn] *)
Require Import PathElems.        (* [path_elems] *)
Require Import FsTree.           (* [fname], [fs_proper] *)
Require Import FsAbsDefs.        (* [aview], [anode], [absnode], [abs_view] *)
Require Import FsBlocks.         (* [blk_splice]: the write leg's splice *)
Require Import FsAbsDelta.       (* the landed delta legs *)
Require Import FsImg.            (* [ROOTINO]: the era's root inum, as a [Z] *)
Require Import TreeView.         (* TL-1: [subtree], [own_wf], the deltas *)
Require Import AppInv.           (* [app_sup_raw], [app_xfer_raw] *)
Require ConsLog.               (* [cons_step] / [cons_ev]: the merged console claim's event type *)
Require Import SystemAdequacy.   (* [app_xfer_boot_raw]: [App.Happ_boot] *)
Require Import RiscvPtsto.       (* [app_iface_triv]: the interface a
                                    tree application sets *)
Require Import App.              (* [xv6_app], [MkApp] *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE GHOST CLASS                                                   *)
(* ===================================================================== *)

(* ONE class, bundling the cameras the claim is made of: the ownership
   map (used TWICE, at two names -- see [tree_names] below), the MOVE
   TOKEN's exclusive unit (design/user-tree.md section 7.2's [tok]) and
   the ERA-LICENCE REGISTRY.

   THE REGISTRY REPLACED A [mono_nat] COUNTER (lane TL-5): the taint used
   to be "a counter that has left 0", which is a permanent persistent
   fact but is ONE resource, and the hand-down needs one linear licence
   PER ERA -- section 2's own paragraph.  So the class carries a second
   [ghost_mapG] and no [mono_natG]; the list is what the closed theorem's
   [UTreeAdequacy.treeAppΣ] names, so an unused row here is a row in that
   statement's trusted base.

   TWO [ghost_mapG] INSTANCES IS A HAZARD, and it bit once: a bare [∅]
   under [ghost_map_auth_frac] no longer determines its key and value types,
   so a landed statement that wrote one ([tree_body_empty]) resolved to
   the WRONG map and its own proof stopped applying.  Annotate the map
   literal wherever one appears. *)
Class treeG (Σ : gFunctors) := TreeG {
  tr_own_map  : ghost_mapG Σ gname (Z * ttree);
  tr_tok      : inG Σ (exclR unitO);
  (* THE ERA-LICENCE REGISTRY (lane TL-5, the hand-down): the rows
     [App.al_pow] files, one per era.  A LIVE row is that era's unspent
     licence ([tree_turn]), a PERSISTED one is a spent one -- and the
     taint is "some era's licence was spent". *)
  tr_era      : ghost_mapG Σ nat unit;
}.
Global Existing Instance tr_own_map.
Global Existing Instance tr_tok.
Global Existing Instance tr_era.

Definition treeΣ : gFunctors :=
  #[ ghost_mapΣ gname (Z * ttree); GFunctor (exclR unitO);
     ghost_mapΣ nat unit ].

Global Instance subG_treeΣ {Σ} : subG treeΣ Σ -> treeG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  1.  THE PURE SIDE: exactness, and what the deltas do to it            *)
(*                                                                       *)
(*  ZERO Iris in this section: it is TL-1's layer, read at the ownership  *)
(*  map the claim carries.  Every step wand below is one of these lemmas  *)
(*  plus [tree_step_gen] (the free steps) or [tree_step_move_gen] (an     *)
(*  owner's own move, section 1i).  [tree_exact] survives as the SHAPE    *)
(*  TL-2's engine hypothesis is stated at, and section 1h says how the    *)
(*  slotted claim still answers it; the claim itself no longer carries it.*)
(* ===================================================================== *)

(* THE CLAIM'S THIRD CONJUNCT: every entry's recorded tree IS the view's
   subtree at its root. *)
Definition tree_exact (av : aview) (own : gmap gname (Z * ttree)) : Prop :=
  forall (g : gname) (root : Z) (t : ttree),
    own !! g = Some (root, t) -> subtree av root = Some t.

(* ---- 1a'.  THE CLAIM'S FOURTH CONJUNCT: "/" IS A DIRECTORY ---------- *)
(*                                                                       *)
(*  design/user-tree.md section 6, TL-2's FINDING 4, and TL-3's landing   *)
(*  of its price.  The era's FIRST deed has to be minted by the TRANSPORT *)
(*  ([App.app_boot]), which sees the view OUTSIDE the later and can       *)
(*  therefore decide [subtree av ROOTINO]; what it cannot do is answer the *)
(*  OTHER arm, because [app_boot] is av-FREE and “this view has no root   *)
(*  directory” has no av-free spelling.  So the claim carries             *)
(*  [⌜adir_at av ROOTINO⌝] and the transport REFUTES that arm from the    *)
(*  claim it was handed ([tree_xfer_boot_at] below).                      *)
(*                                                                       *)
(*  AND IT IS FREE AT EVERY LEG, because it is the roots conjunct of      *)
(*  [own_wf] at the partition that owns "/" and nothing else: each        *)
(*  preservation below is TL-1's own [own_wf_*] lemma at [root_own].      *)
(*  (Which is also the honest reading of the conjunct: the claim says the *)
(*  era has a root, exactly as an owner's entry says its own root is a    *)
(*  directory.) *)

Definition root_own : gmap gname (Z * ttree) :=
  {[ 1%positive := (FsImg.ROOTINO, MkTTree ∅ 0) ]}.

Lemma own_wf_root (av : aview) :
  aview_tree_wf av -> adir_at av FsImg.ROOTINO -> own_wf av root_own.
Proof.
  intros Hwf Hd. rewrite /root_own. split_and!; [exact Hwf | ..].
  - intros g r t Hg. destruct (decide (g = 1%positive)) as [-> | Hne].
    + rewrite lookup_singleton_eq in Hg. injection Hg as <- <-. exact Hd.
    + rewrite lookup_singleton_ne in Hg; [discriminate | congruence].
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
    destruct (decide (g1 = 1%positive)) as [-> | H1e].
    + destruct (decide (g2 = 1%positive)) as [-> | H2e]; [exact (Hne eq_refl) |].
      rewrite lookup_singleton_ne in H2; [discriminate | congruence].
    + rewrite lookup_singleton_ne in H1; [discriminate | congruence].
Qed.

Lemma root_of_own_wf (av : aview) :
  own_wf av root_own -> adir_at av FsImg.ROOTINO.
Proof.
  intros (_ & Hroots & _).
  apply (Hroots 1%positive FsImg.ROOTINO (MkTTree ∅ 0)).
  rewrite /root_own lookup_singleton_eq //.
Qed.

(* the root's reading, which is what the transport actually wants *)
Lemma subtree_root_of_claim (av : aview) :
  adir_at av FsImg.ROOTINO ->
  subtree av FsImg.ROOTINO
  = Some (MkTTree (subtree_nodes av FsImg.ROOTINO) FsImg.ROOTINO).
Proof. exact (subtree_of_dir av FsImg.ROOTINO). Qed.

(* ---- 1a.  the two congruences: a move the PROJECTION does not see ---- *)

Lemma own_wf_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av -> own_wf av own -> own_wf av' own.
Proof.
  intros Hv ((Hu & Hcl) & Hroots & Hnn). split_and!.
  - split.
    + rewrite /aview_uniq_parent Hv. exact Hu.
    + rewrite aview_closed_nstep Hv. by rewrite -aview_closed_nstep.
  - intros g r t Hg. apply adir_at_tview. rewrite Hv.
    apply adir_at_tview. exact (Hroots g r t Hg).
  - intros g g' r t r' t' Hne Hg Hg'. rewrite Hv.
    exact (Hnn g g' r t r' t' Hne Hg Hg').
Qed.

Lemma tree_exact_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av -> tree_exact av own -> tree_exact av' own.
Proof.
  intros Hv Hex g root t Hg. rewrite (subtree_cong av' av root Hv).
  exact (Hex g root t Hg).
Qed.

(* ---- 1b.  DISJOINTNESS, as the movers read it ----------------------- *)

(* THE ONE FACT EVERY OWNER'S MOVE TURNS ON: a node of MY tree is outside
   every other owner's reach.  [TreeView.subtree_disjoint] with the claim's
   own exactness supplying the two subtrees. *)
(* ...and the form the SLOTTED claim reads it at (lane TL-3W): the mover's
   OWN exactness is all the fact needs -- no other owner's, which is what
   makes it usable when other entries are mid-move (their slots carry no
   exactness at all). *)
Lemma tree_disjoint_out_at (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' d : Z) (t t' : ttree) :
  own_wf av own -> subtree av root = Some t ->
  own !! g = Some (root, t) -> own !! g' = Some (root', t') -> g <> g' ->
  d ∈ dom (tv_nodes t) -> ~ nreach (tview av) root' d.
Proof.
  intros Hwf Ht Hg Hg' Hne Hd Hr.
  pose proof (subtree_nodes_eq av root t Ht) as Hnodes.
  assert (Hdom : d ∈ dom av).
  { rewrite Hnodes in Hd. by apply elem_of_dom_subtree_nodes in Hd as [Hd _]. }
  assert (Hin : d ∈ dom (subtree_nodes av root)) by (rewrite -Hnodes; exact Hd).
  assert (Hin' : d ∈ dom (subtree_nodes av root'))
    by (apply elem_of_dom_subtree_nodes; split; assumption).
  pose proof (subtree_disjoint av own g g' root root' t t' Hwf Hne Hg Hg') as Hdis.
  rewrite elem_of_disjoint in Hdis. exact (Hdis d Hin Hin').
Qed.

Lemma tree_disjoint_out (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' d : Z) (t t' : ttree) :
  own_wf av own -> tree_exact av own ->
  own !! g = Some (root, t) -> own !! g' = Some (root', t') -> g <> g' ->
  d ∈ dom (tv_nodes t) -> ~ nreach (tview av) root' d.
Proof.
  intros Hwf Hex Hg Hg' Hne Hd.
  exact (tree_disjoint_out_at av own g g' root root' d t t'
           Hwf (Hex g root t Hg) Hg Hg' Hne Hd).
Qed.

(* ...and the same at the OWNER'S OWN root: a node it does not have is
   one it does not reach. *)
Lemma tree_not_in_own (av : aview) (root d : Z) (t : ttree) :
  subtree av root = Some t -> d ∈ dom av -> d ∉ dom (tv_nodes t) ->
  ~ nreach (tview av) root d.
Proof.
  intros Ht Hdom Hd Hr. apply Hd.
  rewrite (subtree_nodes_eq av root t Ht).
  apply elem_of_dom_subtree_nodes. split; assumption.
Qed.

(* ---- 1c.  [own_wf] does not read the TREES ------------------------- *)

(* an entry's recorded tree may be replaced at will: every conjunct of
   [own_wf] reads the ROOTS and the view, and nothing else.  (It is what
   makes an owner's move ONE [ghost_map_update] and no [own_wf] work.) *)
Lemma own_wf_retree (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root : Z) (t t' : ttree) :
  own !! g = Some (root, t) -> own_wf av own ->
  own_wf av (<[g := (root, t')]> own).
Proof.
  intros Hg (Hwf & Hroots & Hnn).
  assert (Hlk : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             <[g := (root, t')]> own !! g0 = Some (r0, t0) ->
             exists t1, own !! g0 = Some (r0, t1)).
  { intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
    - rewrite lookup_insert_eq in H0. injection H0 as <- <-. by exists t.
    - rewrite lookup_insert_ne in H0; [| congruence]. by exists t0. }
  split_and!; [exact Hwf | ..].
  - intros g0 r0 t0 H0. destruct (Hlk g0 r0 t0 H0) as (t1 & H1).
    exact (Hroots g0 r0 t1 H1).
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
    destruct (Hlk g1 r1 t1 H1) as (u1 & K1).
    destruct (Hlk g2 r2 t2 H2) as (u2 & K2).
    exact (Hnn g1 g2 r1 u1 r2 u2 Hne K1 K2).
Qed.

(* ---- 1d.  the INVISIBLE legs: nothing in the tree moves ------------- *)

Lemma tree_root_cong (av av' : aview) :
  tview av' = tview av ->
  adir_at av FsImg.ROOTINO -> adir_at av' FsImg.ROOTINO.
Proof.
  intros Hv Hd. apply adir_at_tview. rewrite Hv. by apply adir_at_tview.
Qed.

Lemma tree_pres_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf av' own /\ tree_exact av' own /\ adir_at av' FsImg.ROOTINO.
Proof.
  intros Hv Hwf Hex Hr.
  split_and!; [exact (own_wf_cong av av' own Hv Hwf)
              | exact (tree_exact_cong av av' own Hv Hex)
              | exact (tree_root_cong av av' Hv Hr)].
Qed.

(* ---- 1e.  create's ARM leg: a fresh inum is nobody's ---------------- *)

Lemma tree_pres_arm (av : aview) (own : gmap gname (Z * ttree))
    (i : Z) (c : absnode) :
  av !! i = None -> tabs_leaf (tabs_of c) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_arm i c av) own /\ tree_exact (delta_arm i c av) own
  /\ adir_at (delta_arm i c av) FsImg.ROOTINO.
Proof.
  intros Hi Hleaf Hwf Hex Hr.
  pose proof Hwf as (Hcl & Hroots & _).
  split; [exact (own_wf_arm av own i c Hi Hleaf Hwf) |].
  split; [| apply root_of_own_wf;
             exact (own_wf_arm av root_own i c Hi Hleaf
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g root t Hg.
  assert (Hne : i <> root).
  { intros Heq. rewrite Heq in Hi.
    pose proof (adir_at_dom av root (Hroots g root t Hg)) as Hd.
    apply elem_of_dom in Hd as [a Ha]. congruence. }
  rewrite (subtree_delta_arm_fresh av root i c (proj2 Hcl) Hi Hne).
  exact (Hex g root t Hg).
Qed.

(* UNLINK'S TARGET LEG AT THE LAST LINK, FREE (lane TL-3P).  The row
   LEAVES the view, and that is invisible to every owner for the same
   reason create's arm is: nothing names it ([aview_no_edge_to], which
   unlink's OWN entry leg proves -- [TreeView.aview_no_edge_to_unl_ent]),
   so no owner reaches it.  TL-2's "the row is nobody's root" is paid at a
   NON-DIRECTORY target out of [own_wf]'s roots conjunct
   ([TreeView.own_wf_unl_tgt_nodir]); a directory's last link keeps that
   wall. *)
Lemma tree_pres_unl_tgt_last (av : aview) (own : gmap gname (Z * ttree))
    (tg : Z) (a : anode) :
  av !! tg = Some a -> an_nlink a = 1%nat ->
  aview_no_edge_to av tg -> ~ adir_at av tg ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_unl_tgt tg av) own /\ tree_exact (delta_unl_tgt tg av) own
  /\ adir_at (delta_unl_tgt tg av) FsImg.ROOTINO.
Proof.
  intros Ha Hnl Hno Hnd Hwf Hex Hr.
  pose proof Hwf as (_ & Hroots & _).
  split; [exact (own_wf_unl_tgt_nodir av own tg a Ha Hnl Hno Hnd Hwf) |].
  split; [| apply root_of_own_wf;
             exact (own_wf_unl_tgt_nodir av root_own tg a Ha Hnl Hno Hnd
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g root t Hg.
  assert (Hne : tg <> root).
  { intros Heq. apply Hnd. rewrite Heq. exact (Hroots g root t Hg). }
  rewrite (subtree_delta_unl_tgt_out av root tg
             (nreach_no_edge av root tg Hno Hne)).
  exact (Hex g root t Hg).
Qed.

(* CREATE'S UNARM LEG (design section 7.4's WALL 2, closed by lane TL-3R).
   [delta_unarm i] is [delta_unl_tgt i] at the armed row's own count of
   one, so TL-1's row-removal lemma covers it -- and the two premises it
   asks for are exactly the ARM's credential read through the rooted
   view: nothing names the armed row, and it is not [ROOTINO].  "The row
   is nobody's root", which [tree_pres_unl_tgt_last] pays from the
   target's KIND, is paid here from [own_rooted] instead -- so this leg
   is free at MKDIR's directory child too. *)
(* at the armed row's own count of one the two row-removal deltas are the
   same function *)
Lemma delta_unarm_unl_tgt (av : aview) (i : Z) (a : anode) :
  av !! i = Some a -> an_nlink a = 1%nat ->
  delta_unarm i av = delta_unl_tgt i av.
Proof.
  intros Ha Hnl. rewrite (delta_unl_tgt_unfold av i a Ha).
  case_decide as Hz; [reflexivity | lia].
Qed.

Lemma tree_pres_unarm (av : aview) (own : gmap gname (Z * ttree))
    (i : Z) (a : anode) :
  av !! i = Some a -> an_nlink a = 1%nat ->
  aview_no_edge_to av i -> i <> FsImg.ROOTINO ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_rooted av own ->
  own_wf (delta_unarm i av) own /\ tree_exact (delta_unarm i av) own
  /\ adir_at (delta_unarm i av) FsImg.ROOTINO.
Proof.
  intros Ha Hnl Hno Hri Hwf Hex Hr Hor.
  pose proof (delta_unarm_unl_tgt av i a Ha Hnl) as Heq.
  pose proof (nreach_no_edge av FsImg.ROOTINO i Hno Hri) as Hunr.
  assert (Hnotroot : forall (g : gname) (r0 : Z) (t0 : ttree),
            own !! g = Some (r0, t0) -> r0 <> i).
  { intros g r0 t0 H0 ->. exact (Hunr (Hor g i t0 H0)). }
  rewrite Heq. split.
  { exact (own_wf_unl_tgt av own i a Ha Hnl Hno Hnotroot Hwf). }
  split.
  - intros g root t Hg.
    rewrite (subtree_delta_unl_tgt_out av root i
               (nreach_no_edge av root i Hno
                  (fun Hc => Hnotroot g root t Hg (eq_sym Hc)))).
    exact (Hex g root t Hg).
  - apply root_of_own_wf.
    apply (own_wf_unl_tgt av root_own i a Ha Hnl Hno);
      [| exact (own_wf_root av (proj1 Hwf) Hr)].
    intros g r0 t0 H0 ->. destruct (decide (g = 1%positive)) as [-> | Hne].
    + rewrite /root_own lookup_singleton_eq in H0. injection H0 as Hc _.
      exact (Hri (eq_sym Hc)).
    + rewrite /root_own lookup_singleton_ne in H0; [discriminate | congruence].
Qed.

(* ---- 1f.  the OWNER'S OWN legs, AT THE WHOLE-MAP EXACTNESS ---------- *)
(*                                                                       *)
(*  TL-2's shape, kept because it is the honest statement of what a leg   *)
(*  does to a partition that is exact everywhere, and because [own_wf_*]  *)
(*  is read out of it below.  What the SLOTTED claim uses is section 1i,  *)
(*  whose per-entry form asks only the MOVER'S own exactness.             *)

Lemma tree_pres_write (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> i ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_write i off new av) (<[g := (root, top_write i off new t)]> own)
  /\ tree_exact (delta_write i off new av)
       (<[g := (root, top_write i off new t)]> own)
  /\ adir_at (delta_write i off new av) FsImg.ROOTINO.
Proof.
  intros Hi Hg Hd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_write av own i off new bs0 nl Hi Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_write av root_own i off new bs0 nl Hi
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert_eq in H0. injection H0 as <- <-.
    exact (subtree_delta_write av root i t off new bs0 nl Ht Hi Hd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_write_out av root0 i off new
               (tree_disjoint_out av own g g0 root root0 i t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hd)).
    exact (Hex g0 root0 t0 H0).
Qed.

Lemma tree_pres_create (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (i : Z) (c : absnode)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = None -> tabs_leaf (tabs_of c) ->
  own !! g = Some (root, t) -> d ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_create d nm i c av)
    (<[g := (root, top_ins d nm i (tabs_of c) t)]> own)
  /\ tree_exact (delta_create d nm i c av)
       (<[g := (root, top_ins d nm i (tabs_of c) t)]> own)
  /\ adir_at (delta_create d nm i c av) FsImg.ROOTINO.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hg Hdd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  pose proof Hwf as (Hcl & Hroots & _).
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_create av own d nm i c e nl Hnm Hd Hi Hleaf Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_create av root_own d nm i c e nl Hnm Hd Hi Hleaf
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert_eq in H0. injection H0 as <- <-.
    exact (subtree_delta_create av root d nm i c t e nl Ht Hnm Hd Hnone Hi
             Hleaf Hdd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    assert (Hfresh : ~ nreach (tview av) root0 i).
    { assert (Hne0 : i <> root0).
      { intros Heq. rewrite Heq in Hi.
        pose proof (adir_at_dom av root0 (Hroots g0 root0 t0 H0)) as Hdm.
        apply elem_of_dom in Hdm as [a Ha]. congruence. }
      exact (nreach_fresh av root0 i (proj2 Hcl) Hi Hne0). }
    rewrite (subtree_delta_create_out av root0 d nm i c
               (tree_disjoint_out av own g g0 root root0 d t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdd)
               Hfresh).
    exact (Hex g0 root0 t0 H0).
Qed.

Lemma tree_pres_unl_ent (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (dec : nat)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir e) nl) ->
  own !! g = Some (root, t) -> d ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_unl_ent d nm dec av) (<[g := (root, top_unlink d nm t)]> own)
  /\ tree_exact (delta_unl_ent d nm dec av)
       (<[g := (root, top_unlink d nm t)]> own)
  /\ adir_at (delta_unl_ent d nm dec av) FsImg.ROOTINO.
Proof.
  intros Hd Hg Hdd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_unl_ent av own d nm dec e nl Hd Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_unl_ent av root_own d nm dec e nl Hd
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert_eq in H0. injection H0 as <- <-.
    exact (subtree_delta_unl_ent av root d nm dec t e nl Ht Hd Hdd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_unl_ent_out av root0 d nm dec
               (tree_disjoint_out av own g g0 root root0 d t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdd)).
    exact (Hex g0 root0 t0 H0).
Qed.

(* ---- 1f'.  TRUNCATE ------------------------------------------------
   [own_wf_trunc] MOVED to [TreeView.v]'s section 7c (lane TL-3's
   housekeeping), where it belongs and where TL-2's own note said it would
   go: it is [own_wf_write]'s twin line for line and reads no Iris.  Only
   the move below is left here. *)

Lemma tree_pres_trunc (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> i ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_trunc i av) (<[g := (root, top_trunc i t)]> own)
  /\ tree_exact (delta_trunc i av) (<[g := (root, top_trunc i t)]> own)
  /\ adir_at (delta_trunc i av) FsImg.ROOTINO.
Proof.
  intros Hi Hg Hd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_trunc av own i bs0 nl Hi Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_trunc av root_own i bs0 nl Hi
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert_eq in H0. injection H0 as <- <-.
    exact (subtree_delta_trunc av root i t bs0 nl Ht Hi Hd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_trunc_out av root0 i
               (tree_disjoint_out av own g g0 root root0 i t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hd)).
    exact (Hex g0 root0 t0 H0).
Qed.

(* ---- 1g.  THE HAND-DOWN (finding 3) --------------------------------- *)

(* the child's root is a directory of the view: it is a DIRECTORY ROW OF
   THE PARENT'S TREE, and the parent's tree is the view's own closure. *)
Lemma tree_sub_dir (av : aview) (root root' : Z) (t : ttree)
    (e : gmap fname Z) :
  subtree av root = Some t -> tv_nodes t !! root' = Some (ADir e) ->
  adir_at av root'.
Proof.
  intros Ht Hr'.
  assert (Hreach : nreach (tview av) root root').
  { apply (subtree_dom_reach av root t root' Ht). apply elem_of_dom. by exists (ADir e). }
  apply adir_at_tview. exists e.
  rewrite (subtree_nodes_eq av root t Ht) /subtree_nodes
    (nclose_lookup_in (tview av) root root' Hreach) in Hr'. exact Hr'.
Qed.

Lemma tree_pres_grant (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' : Z) (t t' : ttree) (e : gmap fname Z) :
  own !! g = Some (root, t) -> own !! g' = None ->
  tv_nodes t !! root' = Some (ADir e) ->
  subtree av root' = Some t' ->
  own_wf av own -> tree_exact av own ->
  own_wf av (<[g' := (root', t')]> (delete g own))
  /\ tree_exact av (<[g' := (root', t')]> (delete g own)).
Proof.
  intros Hg Hg' Hr' Ht' Hwf Hex.
  pose proof (Hex g root t Hg) as Ht.
  pose proof Hwf as (Hwf0 & Hroots & Hnn).
  assert (Hdom' : root' ∈ dom (tv_nodes t))
    by (apply elem_of_dom; by exists (ADir e)).
  assert (Hreach : nreach (tview av) root root')
    by exact (subtree_dom_reach av root t root' Ht Hdom').
  (* the two halves of NON-NESTING at the child's root, and both are
     TL-1's theorem: the child sits inside the parent, so a stranger that
     reached it would share a node with the parent, and a stranger the
     CHILD reached would be one the PARENT reached. *)
  assert (Hout : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) r0 root').
  { intros g0 r0 t0 Hne H0.
    exact (tree_disjoint_out av own g g0 root r0 root' t t0
             Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdom'). }
  assert (Hout2 : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) root' r0).
  { intros g0 r0 t0 Hne H0 Hc.
    exact (Hnn g g0 root t r0 t0 (fun Hc0 => Hne (eq_sym Hc0)) Hg H0
             (nreach_trans (tview av) root root' r0 Hreach Hc)). }
  assert (Hlk : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g' -> <[g' := (root', t')]> (delete g own) !! g0 = Some (r0, t0) ->
             g0 <> g /\ own !! g0 = Some (r0, t0)).
  { intros g0 r0 t0 Hne H0. rewrite lookup_insert_ne in H0; [| congruence].
    destruct (decide (g0 = g)) as [-> | Hg0].
    - rewrite lookup_delete_eq in H0. discriminate.
    - rewrite lookup_delete_ne in H0; [| congruence].
      split; assumption. }
  split.
  - split_and!; [exact Hwf0 | ..].
    + intros g0 r0 t0 H0. destruct (decide (g0 = g')) as [-> | Hne].
      * rewrite lookup_insert_eq in H0. injection H0 as <- <-.
        exact (tree_sub_dir av root root' t e Ht Hr').
      * destruct (Hlk g0 r0 t0 Hne H0) as (_ & H1).
        exact (Hroots g0 r0 t0 H1).
    + intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
      destruct (decide (g1 = g')) as [-> | Hne1].
      * rewrite lookup_insert_eq in H1. injection H1 as <- <-.
        destruct (Hlk g2 r2 t2 (fun Hc => Hne (eq_sym Hc)) H2) as (Hd2 & K2).
        exact (Hout2 g2 r2 t2 Hd2 K2).
      * destruct (Hlk g1 r1 t1 Hne1 H1) as (Hd1 & K1).
        destruct (decide (g2 = g')) as [-> | Hne2].
        { rewrite lookup_insert_eq in H2. injection H2 as <- <-.
          exact (Hout g1 r1 t1 Hd1 K1). }
        destruct (Hlk g2 r2 t2 Hne2 H2) as (Hd2 & K2).
        exact (Hnn g1 g2 r1 t1 r2 t2 Hne K1 K2).
  - intros g0 r0 t0 H0. destruct (decide (g0 = g')) as [-> | Hne].
    + rewrite lookup_insert_eq in H0. injection H0 as <- <-. exact Ht'.
    + destruct (Hlk g0 r0 t0 Hne H0) as (_ & H1). exact (Hex g0 r0 t0 H1).
Qed.

(* ...and the HAND-DOWN's [own_wf] alone, off the parent's OWN exactness
   (lane TL-3W: the slotted claim has no global [tree_exact] to offer). *)
Lemma own_wf_grant (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' : Z) (t t' : ttree) (e : gmap fname Z) :
  own !! g = Some (root, t) -> subtree av root = Some t ->
  tv_nodes t !! root' = Some (ADir e) ->
  own_wf av own ->
  own_wf av (<[g' := (root', t')]> (delete g own)).
Proof.
  intros Hg Ht Hr' Hwf.
  pose proof Hwf as (Hwf0 & Hroots & Hnn).
  assert (Hdom' : root' ∈ dom (tv_nodes t))
    by (apply elem_of_dom; by exists (ADir e)).
  assert (Hreach : nreach (tview av) root root')
    by exact (subtree_dom_reach av root t root' Ht Hdom').
  assert (Hout : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) r0 root').
  { intros g0 r0 t0 Hne H0.
    exact (tree_disjoint_out_at av own g g0 root r0 root' t t0
             Hwf Ht Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdom'). }
  assert (Hout2 : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) root' r0).
  { intros g0 r0 t0 Hne H0 Hc.
    exact (Hnn g g0 root t r0 t0 (fun Hc0 => Hne (eq_sym Hc0)) Hg H0
             (nreach_trans (tview av) root root' r0 Hreach Hc)). }
  assert (Hlk : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g' -> <[g' := (root', t')]> (delete g own) !! g0 = Some (r0, t0) ->
             g0 <> g /\ own !! g0 = Some (r0, t0)).
  { intros g0 r0 t0 Hne H0. rewrite lookup_insert_ne in H0; [| congruence].
    destruct (decide (g0 = g)) as [-> | Hg0].
    - rewrite lookup_delete_eq in H0. discriminate.
    - rewrite lookup_delete_ne in H0; [| congruence]. split; assumption. }
  split_and!; [exact Hwf0 | ..].
  - intros g0 r0 t0 H0. destruct (decide (g0 = g')) as [-> | Hne].
    + rewrite lookup_insert_eq in H0. injection H0 as <- <-.
      exact (tree_sub_dir av root root' t e Ht Hr').
    + destruct (Hlk g0 r0 t0 Hne H0) as (_ & H1).
      exact (Hroots g0 r0 t0 H1).
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
    destruct (decide (g1 = g')) as [-> | Hne1].
    + rewrite lookup_insert_eq in H1. injection H1 as <- <-.
      destruct (Hlk g2 r2 t2 (fun Hc => Hne (eq_sym Hc)) H2) as (Hd2 & K2).
      exact (Hout2 g2 r2 t2 Hd2 K2).
    + destruct (Hlk g1 r1 t1 Hne1 H1) as (Hd1 & K1).
      destruct (decide (g2 = g')) as [-> | Hne2].
      { rewrite lookup_insert_eq in H2. injection H2 as <- <-.
        exact (Hout g1 r1 t1 Hd1 K1). }
      destruct (Hlk g2 r2 t2 Hne2 H2) as (Hd2 & K2).
      exact (Hnn g1 g2 r1 t1 r2 t2 Hne K1 K2).
Qed.

(* ---- 1h.  THE SLOTTED CLAIM'S PURE LAYER (lane TL-3W) ---------------- *)
(*                                                                        *)
(*  design/user-tree.md section 7.2.  The claim no longer carries the      *)
(*  GLOBAL [tree_exact]: an entry whose owner is mid-move carries no       *)
(*  exactness at all (its SLOT is in the in-flight arm), so every pure     *)
(*  fact below is stated PER ENTRY.                                       *)
(*                                                                        *)
(*  [own_sync] is what keeps TL-2's engine [tree_step_gen] provable at its *)
(*  EXACT statement over the slotted claim: the hypothesis is a [∀ own]    *)
(*  gated on [tree_exact av own], which the slotted body cannot supply --  *)
(*  so it is applied at the map whose every recorded tree is REPLACED by   *)
(*  the view's own subtree at that entry's root.  That map is exact by     *)
(*  construction, it has the same roots (so [own_wf] transfers both ways,  *)
(*  which reads roots and never trees), and its exactness at the POST view *)
(*  says precisely "no owner's root moved" -- which is what each surviving *)
(*  exact slot needs.                                                      *)

Definition own_sync (av : aview) (own : gmap gname (Z * ttree))
    : gmap gname (Z * ttree) :=
  (fun p : Z * ttree => (p.1, MkTTree (subtree_nodes av p.1) p.1)) <$> own.

Lemma own_sync_lookup (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root : Z) (t : ttree) :
  own !! g = Some (root, t) ->
  own_sync av own !! g = Some (root, MkTTree (subtree_nodes av root) root).
Proof. intros H. rewrite /own_sync lookup_fmap H //. Qed.

Lemma own_sync_lookup_inv (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root : Z) (t : ttree) :
  own_sync av own !! g = Some (root, t) ->
  exists t0 : ttree, own !! g = Some (root, t0).
Proof.
  rewrite /own_sync lookup_fmap. intros H.
  destruct (own !! g) as [p |] eqn:E; [| discriminate].
  destruct p as [r0 t0]. cbn in H. injection H as <- _. by exists t0.
Qed.

(* the shape every [subtree] answer has: at a directory the reading is the
   closure, so an entry that IS exact records exactly that tree *)
Lemma subtree_sync_eq (av : aview) (root : Z) (t : ttree) :
  subtree av root = Some t -> t = MkTTree (subtree_nodes av root) root.
Proof.
  intros Ht. pose proof (subtree_Some_inv av root t Ht) as (Hd & _).
  rewrite (subtree_of_dir av root Hd) in Ht. by injection Ht as <-.
Qed.

Lemma own_wf_sync (av : aview) (own : gmap gname (Z * ttree)) :
  own_wf av own -> own_wf av (own_sync av own).
Proof.
  intros (Hwf & Hroots & Hnn). split_and!; [exact Hwf | ..].
  - intros g r t Hg. destruct (own_sync_lookup_inv av own g r t Hg) as (t0 & H0).
    exact (Hroots g r t0 H0).
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
    destruct (own_sync_lookup_inv av own g1 r1 t1 H1) as (u1 & K1).
    destruct (own_sync_lookup_inv av own g2 r2 t2 H2) as (u2 & K2).
    exact (Hnn g1 g2 r1 u1 r2 u2 Hne K1 K2).
Qed.

Lemma own_wf_of_sync (av av' : aview) (own : gmap gname (Z * ttree)) :
  own_wf av' (own_sync av own) -> own_wf av' own.
Proof.
  intros (Hwf & Hroots & Hnn). split_and!; [exact Hwf | ..].
  - intros g r t Hg.
    exact (Hroots g r (MkTTree (subtree_nodes av r) r)
             (own_sync_lookup av own g r t Hg)).
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
    exact (Hnn g1 g2 r1 _ r2 _ Hne
             (own_sync_lookup av own g1 r1 t1 H1)
             (own_sync_lookup av own g2 r2 t2 H2)).
Qed.

(* ...AND THE ROOTED CONJUNCT ACROSS THE SAME MOVE (lane TL-3R): [own_sync]
   replaces the recorded TREES and never the roots, and [own_rooted] reads
   the roots alone -- so it transfers both ways exactly as [own_wf] does. *)
Lemma own_rooted_sync (av : aview) (own : gmap gname (Z * ttree)) :
  own_rooted av own -> own_rooted av (own_sync av own).
Proof.
  intros Hro g root t Hg.
  destruct (own_sync_lookup_inv av own g root t Hg) as (t0 & H0).
  exact (Hro g root t0 H0).
Qed.

Lemma own_rooted_of_sync (av av' : aview) (own : gmap gname (Z * ttree)) :
  own_rooted av' (own_sync av own) -> own_rooted av' own.
Proof.
  intros Hro g root t Hg.
  exact (Hro g root (MkTTree (subtree_nodes av root) root)
           (own_sync_lookup av own g root t Hg)).
Qed.

Lemma tree_exact_sync (av : aview) (own : gmap gname (Z * ttree)) :
  own_wf av own -> tree_exact av (own_sync av own).
Proof.
  intros (_ & Hroots & _) g r t Hg.
  destruct (own_sync_lookup_inv av own g r t Hg) as (t0 & H0).
  rewrite (own_sync_lookup av own g r t0 H0) in Hg. injection Hg as <-.
  exact (subtree_of_dir av r (Hroots g r t0 H0)).
Qed.

(* THE BRIDGE: TL-2's [∀ own] step hypothesis, read per entry. *)
Lemma tree_step_pure (av av' : aview) (own : gmap gname (Z * ttree)) :
  (forall own0 : gmap gname (Z * ttree),
     own_wf av own0 -> tree_exact av own0 -> adir_at av FsImg.ROOTINO ->
     aview_rooted av -> own_rooted av own0 ->
     own_wf av' own0 /\ tree_exact av' own0 /\ adir_at av' FsImg.ROOTINO) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  aview_rooted av -> own_rooted av own ->
  own_wf av' own /\ adir_at av' FsImg.ROOTINO
  /\ (forall (g : gname) (root : Z) (t : ttree),
        own !! g = Some (root, t) -> subtree av root = Some t ->
        subtree av' root = Some t).
Proof.
  intros Hstep Hwf Hr Hro Hor.
  destruct (Hstep (own_sync av own) (own_wf_sync av own Hwf)
              (tree_exact_sync av own Hwf) Hr Hro
              (own_rooted_sync av own Hor)) as (Hwf' & Hex' & Hr').
  split_and!; [exact (own_wf_of_sync av av' own Hwf') | exact Hr' |].
  intros g root t Hg Ht.
  rewrite (subtree_sync_eq av root t Ht).
  exact (Hex' g root _ (own_sync_lookup av own g root t Hg)).
Qed.

(* ---- 1i.  THE OWNER'S MOVE, PER ENTRY (design section 7.2) ----------- *)
(*                                                                        *)
(*  What [tree_step_move] owes at each landed leg: the map is WELL FORMED  *)
(*  at the post view, the era still has its root, and EVERY OTHER entry's  *)
(*  reading is literally unchanged (an EQUATION, so a surviving exact slot *)
(*  transfers by rewriting).  The mover's own entry owes nothing here --   *)
(*  its slot goes IN FLIGHT.                                              *)

Definition tree_move_out (av av' : aview) (own : gmap gname (Z * ttree))
    (g : gname) : Prop :=
  own_wf av' own /\ adir_at av' FsImg.ROOTINO
  /\ (forall (g' : gname) (root' : Z) (t' : ttree),
        g' <> g -> own !! g' = Some (root', t') ->
        subtree av' root' = subtree av root').

Lemma tree_move_write_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> subtree av root = Some t ->
  i ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  tree_move_out av (delta_write i off new av) own g.
Proof.
  intros Hi Hg Ht Hd Hwf Hr. split_and!.
  - exact (own_wf_write av own i off new bs0 nl Hi Hwf).
  - apply root_of_own_wf.
    exact (own_wf_write av root_own i off new bs0 nl Hi
             (own_wf_root av (proj1 Hwf) Hr)).
  - intros g' root' t' Hne H'.
    exact (subtree_delta_write_out av root' i off new
             (tree_disjoint_out_at av own g g' root root' i t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hd)).
Qed.

Lemma tree_move_trunc_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> subtree av root = Some t ->
  i ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  tree_move_out av (delta_trunc i av) own g.
Proof.
  intros Hi Hg Ht Hd Hwf Hr. split_and!.
  - exact (own_wf_trunc av own i bs0 nl Hi Hwf).
  - apply root_of_own_wf.
    exact (own_wf_trunc av root_own i bs0 nl Hi
             (own_wf_root av (proj1 Hwf) Hr)).
  - intros g' root' t' Hne H'.
    exact (subtree_delta_trunc_out av root' i
             (tree_disjoint_out_at av own g g' root root' i t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hd)).
Qed.

Lemma tree_move_create_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (i : Z) (c : absnode)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = None -> tabs_leaf (tabs_of c) ->
  own !! g = Some (root, t) -> subtree av root = Some t ->
  d ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  tree_move_out av (delta_create d nm i c av) own g.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hg Ht Hdd Hwf Hr.
  pose proof Hwf as (Hcl & Hroots & _). split_and!.
  - exact (own_wf_create av own d nm i c e nl Hnm Hd Hi Hleaf Hwf).
  - apply root_of_own_wf.
    exact (own_wf_create av root_own d nm i c e nl Hnm Hd Hi Hleaf
             (own_wf_root av (proj1 Hwf) Hr)).
  - intros g' root' t' Hne H'.
    assert (Hfresh : ~ nreach (tview av) root' i).
    { assert (Hne0 : i <> root').
      { intros Heq. rewrite Heq in Hi.
        pose proof (adir_at_dom av root' (Hroots g' root' t' H')) as Hdm.
        apply elem_of_dom in Hdm as [a Ha]. congruence. }
      exact (nreach_fresh av root' i (proj2 Hcl) Hi Hne0). }
    exact (subtree_delta_create_out av root' d nm i c
             (tree_disjoint_out_at av own g g' root root' d t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hdd)
             Hfresh).
Qed.

(* CREATE'S PARENT LEG ALONE (lane TL-3P), which is the delta the landed
   fire actually commits: at [FsAbsDelta.cre_pre]'s instant the child is
   ALREADY ARMED, so [delta_create] has collapsed to [delta_ent]
   ([delta_create_armed]).  Two premises the FUSED lemma got for free are
   stated, and both are the ARM leg's own facts:
     - [aview_no_edge_to av i] -- nothing names the armed row.  It is
       what [TreeView.own_wf_ent] needs, and it is discharged at the arm
       by [TreeView.aview_no_edge_to_arm];
     - [~ adir_at av i] -- the armed child is not a directory, which is
       how "the armed inum is nobody's root" is paid without a credential
       ([TreeView.own_wf_ent_leaf]).  It covers open(O_CREATE)'s empty
       FILE and mknod's DEVICE; mkdir's child is a directory and needs
       the arm-to-ent credential instead. *)
Lemma tree_move_ent_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (i : Z) (a : anode)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) ->
  av !! i = Some a -> tabs_leaf (tnode_of a) ->
  ~ adir_at av i -> aview_no_edge_to av i ->
  own !! g = Some (root, t) -> subtree av root = Some t ->
  d ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  tree_move_out av (delta_ent d nm i av) own g.
Proof.
  intros Hnm Hd Hi Hleaf Hnd Hno Hg Ht Hdd Hwf Hr. split_and!.
  - exact (own_wf_ent_leaf av own d nm i a e nl Hnm Hd Hi Hleaf Hnd Hno Hwf).
  - exact (adir_at_delta_ent av d nm i e nl a FsImg.ROOTINO Hd Hi Hr).
  - intros g' root' t' Hne H'.
    exact (subtree_delta_ent_out av root' d nm i
             (tree_disjoint_out_at av own g g' root root' d t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hdd)).
Qed.

Lemma tree_move_unl_ent_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (dec : nat)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir e) nl) ->
  own !! g = Some (root, t) -> subtree av root = Some t ->
  d ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  tree_move_out av (delta_unl_ent d nm dec av) own g.
Proof.
  intros Hd Hg Ht Hdd Hwf Hr. split_and!.
  - exact (own_wf_unl_ent av own d nm dec e nl Hd Hwf).
  - apply root_of_own_wf.
    exact (own_wf_unl_ent av root_own d nm dec e nl Hd
             (own_wf_root av (proj1 Hwf) Hr)).
  - intros g' root' t' Hne H'.
    exact (subtree_delta_unl_ent_out av root' d nm dec
             (tree_disjoint_out_at av own g g' root root' d t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hdd)).
Qed.

(* ---- 1j.  WHEN A MOVE IS INVISIBLE: THE VIEW ITSELF DOES NOT MOVE ---- *)
(*                                                                        *)
(*  design section 7.2's “a move with [tree_op δ t = t] takes the FREE     *)
(*  step instead -- the owner decides by computation on its own tree”.     *)
(*  At write and truncate the decision is even cheaper than that: an       *)
(*  invisible splice leaves the ROW where it was, so the delta is the      *)
(*  IDENTITY on the view and the free step is [tree_step_gen] at a         *)
(*  congruence.  (It matters because the KERNEL picks the offset and the   *)
(*  bytes, so an owner supplying a write chain must answer both cases.)    *)

Lemma delta_write_id (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  blk_splice off new bs0 = bs0 ->
  delta_write i off new av = av.
Proof.
  intros Hi Hsp. rewrite /delta_write Hi /=. cbn [an_node an_nlink].
  rewrite Hsp. exact (insert_id av i (MkAnode (AFile bs0) nl) Hi).
Qed.

Lemma delta_trunc_id (av : aview) (i : Z) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  bs0 = [] ->
  delta_trunc i av = av.
Proof.
  intros Hi ->. rewrite /delta_trunc Hi /=. cbn [an_node an_nlink].
  exact (insert_id av i (MkAnode (AFile []) nl) Hi).
Qed.

(* ...and the reading that makes the decision a computation on the TREE:
   at a file row the owner's tree records, the splice is invisible in the
   tree exactly when it is invisible in the view. *)
Lemma top_write_id_inv (t : ttree) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs0) ->
  top_write i off new t = t -> blk_splice off new bs0 = bs0.
Proof.
  intros Hi Heq. rewrite /top_write Hi in Heq.
  pose proof (f_equal tv_nodes Heq) as Hn. cbn [tv_nodes] in Hn.
  pose proof (f_equal (fun m : gmap Z absnode => m !! i) Hn) as Hl.
  cbn beta in Hl. rewrite lookup_insert_eq Hi in Hl. by injection Hl as ->.
Qed.

Lemma top_trunc_id_inv (t : ttree) (i : Z) (bs0 : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs0) -> top_trunc i t = t -> bs0 = [].
Proof.
  intros Hi Heq. rewrite /top_trunc Hi in Heq.
  pose proof (f_equal tv_nodes Heq) as Hn. cbn [tv_nodes] in Hn.
  pose proof (f_equal (fun m : gmap Z absnode => m !! i) Hn) as Hl.
  cbn beta in Hl. rewrite lookup_insert_eq Hi in Hl. by injection Hl as ->.
Qed.

(* the owner's own tree records the view's bytes at a node of its subtree *)
Lemma tree_row_file (av : aview) (root i : Z) (t : ttree)
    (bs0 : list (bv 8)) (nl : nat) :
  subtree av root = Some t -> i ∈ dom (tv_nodes t) ->
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  tv_nodes t !! i = Some (AFile bs0).
Proof.
  intros Ht Hd Hi.
  rewrite (subtree_nodes_eq av root t Ht) /subtree_nodes
    (nclose_lookup_in (tview av) root i (subtree_dom_reach av root t i Ht Hd)).
  rewrite (tview_lookup_Some av i _ Hi) //.
Qed.

(* ...and the converse, which is what a WRITE's phase 1 reads: the owner's
   tree records a file at [i], so the VIEW has that file there, and the
   fire's own [arow_at] row is then pinned to it. *)
Lemma tree_file_row (av : aview) (root i : Z) (t : ttree) (bs : list (bv 8)) :
  subtree av root = Some t -> tv_nodes t !! i = Some (AFile bs) ->
  exists nl : nat, av !! i = Some (MkAnode (AFile bs) nl).
Proof.
  intros Ht Hi. rewrite (subtree_nodes_eq av root t Ht) in Hi.
  apply subtree_nodes_lookup_Some in Hi as ((a & Ha & Hn) & _).
  destruct a as [n0 nl]. cbn in Hn. exists nl.
  rewrite (tabs_of_file_inv n0 bs (eq_sym Hn)) in Ha. exact Ha.
Qed.

Lemma tree_file_dom (root i : Z) (t : ttree) (bs : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs) -> i ∈ dom (tv_nodes t).
Proof. intros H. apply elem_of_dom. by exists (AFile bs). Qed.

(* CREATE IS NEVER INVISIBLE: the child is a fresh inum, so the owner's
   tree gains a node it did not have. *)
Lemma dom_tedge_ins (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z) :
  dom (tedge_ins d nm i m) = dom m.
Proof.
  rewrite /tedge_ins. destruct (m !! d) as [n |] eqn:E; [| done].
  destruct n as [| e |]; [done | | done].
  assert (Hd : d ∈ dom m) by (apply elem_of_dom; by eexists).
  rewrite dom_insert_L. set_solver.
Qed.

Lemma top_ins_ne (av : aview) (root d i : Z) (nm : fname) (c : absnode)
    (t : ttree) :
  subtree av root = Some t -> av !! i = None ->
  top_ins d nm i c t <> t.
Proof.
  intros Ht Hi Heq.
  assert (Hnot : i ∉ dom (tv_nodes t)).
  { intros Hin. rewrite (subtree_nodes_eq av root t Ht) in Hin.
    apply elem_of_dom_subtree_nodes in Hin as [Hdm _].
    apply elem_of_dom in Hdm as [a Ha]. congruence. }
  apply Hnot. rewrite -Heq /top_ins /= dom_tedge_ins dom_insert_L. set_solver.
Qed.

(* the owner's own tree records the view's ENTRY MAP, up to the dots, at a
   directory of its subtree -- [tree_row_file]'s twin, and what unlink's
   phase 2 needs to know its tree really moves *)
Lemma tree_row_dir (av : aview) (root d : Z) (t : ttree)
    (e : gmap fname Z) (nl : nat) :
  subtree av root = Some t -> d ∈ dom (tv_nodes t) ->
  av !! d = Some (MkAnode (ADir e) nl) ->
  tv_nodes t !! d = Some (ADir (hide_dots e)).
Proof.
  intros Ht Hd Hi.
  rewrite (subtree_nodes_eq av root t Ht) /subtree_nodes
    (nclose_lookup_in (tview av) root d (subtree_dom_reach av root t d Ht Hd)).
  rewrite (tview_lookup_Some av d _ Hi) //.
Qed.

(* UNLINK'S ENTRY LEG IS NEVER INVISIBLE at a PROPER name the parent
   really carries: the tree loses that edge. *)
Lemma tv_nodes_top_unlink (t : ttree) (d : Z) (nm : fname) :
  tv_nodes (top_unlink d nm t)
  = nclose (tedge_del d nm (tv_nodes t)) (tv_root t).
Proof. reflexivity. Qed.

(* BOTH ARMS OF THE RE-CLOSURE SAY THE SAME THING.  [top_unlink] is the one
   tree op that re-closes (it is the one that can orphan), so the parent's
   row after it is either the map's -- the entry gone -- or ABSENT, if the
   deletion cut the parent off from the root.  Either way it is not the row
   the tree had. *)
Lemma top_unlink_ne (t : ttree) (d : Z) (nm : fname) (e' : gmap fname Z)
    (tg : Z) :
  tv_nodes t !! d = Some (ADir e') -> e' !! nm = Some tg ->
  top_unlink d nm t <> t.
Proof.
  intros Hd Hnm Heq.
  assert (Hl : tv_nodes (top_unlink d nm t) !! d = tv_nodes t !! d)
    by (by rewrite Heq).
  rewrite tv_nodes_top_unlink in Hl.
  destruct (decide (nreach (tedge_del d nm (tv_nodes t)) (tv_root t) d))
    as [Hr | Hr].
  - rewrite (nclose_lookup_in (tedge_del d nm (tv_nodes t)) (tv_root t) d Hr)
      in Hl.
    rewrite (tedge_del_lookup_at (tv_nodes t) d nm e' Hd) Hd in Hl.
    injection Hl as Hde.
    assert (Hx : delete nm e' !! nm = e' !! nm) by (by rewrite Hde).
    rewrite lookup_delete_eq Hnm in Hx. discriminate.
  - rewrite (nclose_lookup_out (tedge_del d nm (tv_nodes t)) (tv_root t) d Hr)
      in Hl.
    rewrite Hd in Hl. discriminate.
Qed.

(* ...AND THE PARENT LEG IS NEVER INVISIBLE EITHER, for the same reason
   one step weaker: the child is a row the owner does not REACH (nothing
   names it), so the owner's tree gains a node it did not have.  This is
   [top_ins_ne] with "absent from the view" weakened to "absent from the
   owner's closure", which is what the ARMED child satisfies. *)
Lemma top_ins_ne_unreached (av : aview) (root d i : Z) (nm : fname)
    (c : absnode) (t : ttree) :
  subtree av root = Some t -> ~ nreach (tview av) root i ->
  top_ins d nm i c t <> t.
Proof.
  intros Ht Hunr Heq.
  assert (Hnot : i ∉ dom (tv_nodes t)).
  { intros Hin. exact (Hunr (subtree_dom_reach av root t i Ht Hin)). }
  apply Hnot. rewrite -Heq /top_ins /= dom_tedge_ins dom_insert_L. set_solver.
Qed.

(* WHAT PHASE 2 READS AT THE PARENT LEG: the post view's subtree at the
   owner's root IS the fresh insert, and it is a DIFFERENT tree -- the two
   facts [tree_resync] takes.  Both come off the no-edge credential: a row
   nothing names is a row the owner does not reach
   ([TreeView.nreach_no_edge]). *)
Lemma tree_ent_post (av : aview) (root d : Z) (nm : fname) (i : Z)
    (a : anode) (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = Some a -> tabs_leaf (tnode_of a) ->
  ~ adir_at av i -> aview_no_edge_to av i ->
  subtree av root = Some t -> d ∈ dom (tv_nodes t) ->
  subtree (delta_ent d nm i av) root = Some (top_ins d nm i (tnode_of a) t)
  /\ top_ins d nm i (tnode_of a) t <> t.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hnd Hno Ht Hdd.
  assert (Hrootdir : adir_at av root).
  { destruct (subtree_root_dir av root t Ht) as (e0 & He0).
    apply adir_at_tview. by exists e0. }
  assert (Hne : i <> root) by (intros ->; exact (Hnd Hrootdir)).
  pose proof (nreach_no_edge av root i Hno Hne) as Hunr.
  split.
  - exact (subtree_delta_ent av root d nm i a t e nl Ht Hnm Hd Hnone Hi
             Hleaf Hunr Hdd).
  - exact (top_ins_ne_unreached av root d i nm (tnode_of a) t Ht Hunr).
Qed.

(* ---- 1k.  THE ROOTED ROUTE (lane TL-3R, design section 7.8) --------- *)
(*                                                                        *)
(*  The same parent leg, with the two credentials READ OFF THE CLAIM       *)
(*  instead of taken as premises.  The supplier hands in one PURE fact     *)
(*  about its OWN FIXED TREE -- [i ∉ dom (tv_nodes t)], the arm's receipt  *)
(*  -- and the claim's [aview_rooted] / [own_rooted] turn it into          *)
(*  [aview_no_edge_to av i] and "the armed inum is nobody's root".  So     *)
(*  this route covers MKDIR's directory child too, which                   *)
(*  [own_wf_ent_leaf] could not.                                          *)

Lemma tree_ent_post_unr (av : aview) (root d : Z) (nm : fname) (i : Z)
    (a : anode) (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = Some a -> tabs_leaf (tnode_of a) ->
  ~ nreach (tview av) root i ->
  subtree av root = Some t -> d ∈ dom (tv_nodes t) ->
  subtree (delta_ent d nm i av) root = Some (top_ins d nm i (tnode_of a) t)
  /\ top_ins d nm i (tnode_of a) t <> t.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hunr Ht Hdd. split.
  - exact (subtree_delta_ent av root d nm i a t e nl Ht Hnm Hd Hnone Hi
             Hleaf Hunr Hdd).
  - exact (top_ins_ne_unreached av root d i nm (tnode_of a) t Ht Hunr).
Qed.

(* the reading the OWNER OF "/" gets: the armed row is one its tree does
   not have, so it does not reach it *)
Lemma tree_unreached_of_arm (av : aview) (t : ttree) (i : Z) :
  subtree av FsImg.ROOTINO = Some t -> i ∈ dom av -> i ∉ dom (tv_nodes t) ->
  ~ nreach (tview av) FsImg.ROOTINO i.
Proof.
  intros Ht Hd Hni Hr. exact (Hni (subtree_reach_dom av FsImg.ROOTINO t i Ht Hd Hr)).
Qed.

Lemma tree_move_ent_rooted_pure (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (d : Z) (nm : fname) (i : Z) (a : anode)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = Some a -> tabs_leaf (tnode_of a) ->
  i ∉ dom (tv_nodes t) ->
  own !! g = Some (FsImg.ROOTINO, t) -> subtree av FsImg.ROOTINO = Some t ->
  d ∈ dom (tv_nodes t) ->
  own_wf av own -> adir_at av FsImg.ROOTINO ->
  aview_rooted av -> own_rooted av own ->
  tree_move_out av (delta_ent d nm i av) own g.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hni Hg Ht Hdd Hwf Hr Hro Hor.
  assert (Hidom : i ∈ dom av) by (apply elem_of_dom; by eexists).
  assert (Hno : aview_no_edge_to av i).
  { exact (aview_no_edge_to_rooted av t i Hro (proj2 (proj1 Hwf)) Ht Hni). }
  assert (Hnotroot : forall (g0 : gname) (r0 : Z) (t0 : ttree),
            own !! g0 = Some (r0, t0) -> r0 <> i).
  { intros g0 r0 t0 H0.
    exact (root_not_armed_rooted av t i r0 Ht Hni Hidom (Hor g0 r0 t0 H0)). }
  split_and!.
  - exact (own_wf_ent av own d nm i a e nl Hnm Hd Hi Hleaf Hno Hnotroot Hwf).
  - exact (adir_at_delta_ent av d nm i e nl a FsImg.ROOTINO Hd Hi Hr).
  - intros g' root' t' Hne H'.
    exact (subtree_delta_ent_out av root' d nm i
             (tree_disjoint_out_at av own g g' FsImg.ROOTINO root' d t t'
                Hwf Ht Hg H' (fun Hc => Hne (eq_sym Hc)) Hdd)).
Qed.

(* ===================================================================== *)
(*  2.  THE TAINT, THE FIXED PART, THE CLAIM                              *)
(* ===================================================================== *)

Section AppTree.
  Context {Σ : gFunctors} `{!treeG Σ}.

  (* THE FIXED PART: the ERA-LICENCE REGISTRY's name, born once, echo's
     [echo_fixed] exactly.

     IT WAS A BARE mono_nat COUNTER until lane TL-5, and the reason it is
     a registry now is the HAND-DOWN, which the design page priced wrong
     (design/user-tree.md section 9.1: "app_turn app_tree c k := tree_cl
     c", the counter itself).  THAT CANNOT BE PAID.  [App.al_pow] must
     yield [app_turn] at EVERY power-on out of [app_R] alone, and one
     exclusive counter can be handed down ONCE: after era 1's <init> holds
     it, era 2's power-on has nothing to hand, and a ledger arm weak
     enough to be re-established after the hand-down (the counter's lower
     bound, which the design page names) is PERSISTENT -- so the licence
     would be free and the mint with it, which is exactly what
     [tree_bump_free_is_vacuous] rules out.  So the licence is PER ERA and
     the ledger keeps the AUTHORITY that mints one: the registry's
     authority is [tree_cl] (born by [tree_birth], carried by [tree_R]),
     era k's licence is a LIVE entry of it ([tree_turn]) and the taint is
     a PERSISTED entry ([tree_taint]) -- "some era's licence was spent".
     Allocation is free, so every era gets a licence; spending one is not,
     because no entry exists without the authority. *)
  Definition tree_fixed : Type := gname.

  (* THE CLAIM'S INSTANCE NAMES, A PAIR (lane TL-3W, and the one deviation
     from design section 7.2's letter).  The deed is now SPLIT ACROSS TWO
     GHOST LOCATIONS and it has to be, for a reason the design page's phase
     2 states but does not price: phase 2 must "agree the entry is still
     [(root, t)]" while holding NOTHING of the entry -- the whole point of
     the in-flight arm is that the owner's element is PARKED there, and it
     has to be parked WHOLE, because only [DfracOwn 1] in the claim refutes
     the in-flight arm for a reader, and a FROZEN reader ([tree_pin],
     [DfracDiscarded]) is refutable at no smaller fraction.  So the owner
     keeps a MOVE TICKET at a second ghost map that carries the SAME map:
       [tn_own r] -- the deed proper, parked whole while a move is in flight;
       [tn_tk  r] -- the ticket, HALF held by the owner at all times and
                     half by the claim's slot, which is what identifies the
                     owner's entry at phase 2 (and what phase 2 spends,
                     with the slot's half, to update the entry).
     Everything downstream quantifies [tree_names] opaquely, so no landed
     statement moves. *)
  Definition tree_names : Type := gname * gname.

  Definition tn_own (r : tree_names) : gname := r.1.
  Definition tn_tk (r : tree_names) : gname := r.2.

  (* THE TAINT: some era's licence has been SPENT, and a spent licence can
     never come back -- a persisted registry entry is a permanent,
     persistent fact -- "some move of the file system was paid by
     nobody". *)
  Definition tree_taint (c : tree_fixed) : iProp Σ :=
    (∃ k : nat, k ↪[c]□ tt)%I.

  Global Instance tree_taint_persistent c : Persistent (tree_taint c).
  Proof using . rewrite /tree_taint. apply _. Qed.
  Global Instance tree_taint_timeless c : Timeless (tree_taint c).
  Proof using . rewrite /tree_taint. apply _. Qed.

  (* THE ERA'S LICENCE ([App.app_turn] at this record): an UNSPENT entry of
     the registry.  LINEAR -- it is a whole ghost-map element -- and one
     per era, because [al_pow] files a fresh row at every power-on. *)
  Definition tree_turn (c : tree_fixed) : iProp Σ :=
    (∃ k : nat, k ↪[c] tt)%I.

  Global Instance tree_turn_timeless c : Timeless (tree_turn c).
  Proof using . rewrite /tree_turn. apply _. Qed.

  (* THE BIRTH RESOURCE ([App.app_cl]): the registry's authority.  The
     LEDGER carries it for the whole run ([tree_R]), which is what lets
     [al_pow] mint a licence at EVERY era rather than only at the first. *)
  Definition tree_cl (c : tree_fixed) : iProp Σ :=
    (∃ M : gmap nat unit, ghost_map_auth_frac c 1 M)%I.

  Global Instance tree_cl_timeless c : Timeless (tree_cl c).
  Proof using . rewrite /tree_cl. apply _. Qed.

  Lemma tree_birth : ⊢ |==> ∃ c : tree_fixed, tree_cl c.
  Proof using .
    iMod (ghost_map_alloc_empty (K := nat) (V := unit)) as (γ) "Ha".
    iModIntro. iExists γ, ∅. iExact "Ha".
  Qed.

  (* THE ERA'S MINT, and it is the whole of the hand-down: the ledger files
     a FRESH row and keeps its authority, so the next era is served too. *)
  Lemma tree_licence_mint (c : tree_fixed) :
    tree_cl c ==∗ tree_cl c ∗ tree_turn c.
  Proof using .
    iIntros "Ha". iDestruct "Ha" as (M) "Ha".
    iMod (ghost_map_insert (fresh (dom M)) tt with "Ha") as "[Ha Hk]".
    { apply not_elem_of_dom. apply is_fresh. }
    iModIntro. iSplitL "Ha"; [ iExists _; iExact "Ha" | ].
    iExists (fresh (dom M)). iExact "Hk".
  Qed.

  (* ...AND WHAT A LICENCE IS WORTH BESIDE THE AUTHORITY: nothing is
     derivable from the ledger alone, so an era that never received one
     cannot taint the claim.  (The authority's own row for a LIVE licence
     is exclusive, which is what makes [tree_turn] linear.) *)
  Lemma tree_taint_needs_a_row (c : tree_fixed) (M : gmap nat unit) :
    ghost_map_auth_frac c 1 M -∗ tree_taint c -∗ ⌜M <> ∅⌝.
  Proof using .
    iIntros "Ha (%k & Hk)".
    iDestruct (ghost_map_lookup with "Ha Hk") as %Hlk.
    iPureIntro. intros ->. by rewrite lookup_empty in Hlk.
  Qed.

  (* the mint an unpaid mover runs, at the era's own licence *)
  Lemma tree_taint_mint (c : tree_fixed) : tree_turn c ==∗ tree_taint c.
  Proof using .
    iIntros "(%k & Hk)". rewrite /tree_taint.
    iMod (ghost_map_elem_persist with "Hk") as "#Hk".
    iModIntro. iExists k. iExact "Hk".
  Qed.

  (* ---- 2a.  THE CLAIM ------------------------------------------------ *)

  (* THE MOVE TOKEN (design section 7.2): an exclusive one-shot, FRESH per
     move, allocated by the owner in phase 1 and spent in phase 2.  It is
     what makes the in-flight arm a resource NO party can fabricate inside
     an update-free wand; nothing is lost when a move turns out invisible,
     because the owner simply drops it. *)
  Definition tok (γi : gname) : iProp Σ := own γi (Excl ()).

  Global Instance tok_timeless γi : Timeless (tok γi).
  Proof using . rewrite /tok. apply _. Qed.

  Lemma tok_alloc : ⊢ |==> ∃ γi : gname, tok γi.
  Proof using . rewrite /tok. iApply own_alloc. done. Qed.

  (* THE ENTRY'S SLOT (design section 7.2).  Half the ticket, always -- the
     owner holds the other half -- and then the entry is EXACT or IN FLIGHT:

       exact      the view's subtree at this root IS the recorded tree;
       in flight  the owner has parked its deed and a fresh token here, and
                  the entry's reading says nothing until phase 2 resyncs it.

     A READER REFUTES THE IN-FLIGHT ARM BY EXCLUSIVITY: the parked deed is
     [DfracOwn 1] at that key, so it is incompatible with ANY further
     fraction -- a linear deed and a frozen one alike.  That is why the
     whole deed is parked and why the ticket exists. *)
  Definition tree_slot (r : tree_names) (av : aview) (g : gname)
      (p : Z * ttree) : iProp Σ :=
    (g ↪[tn_tk r]{# (1/2)%Qp} p ∗
     (⌜subtree av p.1 = Some p.2⌝
      ∨ (g ↪[tn_own r] p ∗ ∃ γi : gname, tok γi)))%I.

  Global Instance tree_slot_timeless r av g p : Timeless (tree_slot r av g p).
  Proof using . rewrite /tree_slot. apply _. Qed.

  (* THE CLAIM'S BODY.  The two authorities at ONE map, the two pure
     conjuncts that read the ROOTS alone -- the map is well formed at the
     view, and (TL-3's landing of TL-2's finding 4) THE ERA HAS A ROOT --
     and the per-entry SLOTS, which is where TL-2's global [tree_exact]
     went: exactness is now a per-entry fact, because an entry whose owner
     is mid-move has none. *)
  Definition tree_body (r : tree_names) (av : aview) : iProp Σ :=
    (∃ own : gmap gname (Z * ttree),
       ghost_map_auth_frac (tn_own r) 1 own ∗ ghost_map_auth_frac (tn_tk r) 1 own
       ∗ ⌜own_wf av own⌝ ∗ ⌜adir_at av FsImg.ROOTINO⌝
       ∗ ⌜aview_rooted av⌝ ∗ ⌜own_rooted av own⌝
       ∗ ([∗ map] g ↦ p ∈ own, tree_slot r av g p))%I.

  Definition tree_pred (c : tree_fixed) (r : tree_names) (av : aview)
      : iProp Σ := (tree_taint c ∨ tree_body r av)%I.

  Global Instance tree_body_timeless r av : Timeless (tree_body r av).
  Proof using . rewrite /tree_body. apply _. Qed.
  Global Instance tree_pred_timeless c r av : Timeless (tree_pred c r av).
  Proof using . rewrite /tree_pred. apply _. Qed.

  (* the mint's shape: a map that is EXACT at every entry, so every slot is
     built in its exact arm out of the ticket halves the allocation gave *)
  Lemma tree_body_intro (r : tree_names) (av : aview)
      (own : gmap gname (Z * ttree)) :
    own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
    aview_rooted av -> own_rooted av own ->
    ghost_map_auth_frac (tn_own r) 1 own -∗ ghost_map_auth_frac (tn_tk r) 1 own -∗
    ([∗ map] g ↦ p ∈ own, g ↪[tn_tk r]{# (1/2)%Qp} p) -∗
    tree_body r av.
  Proof using .
    intros Hwf Hex Hr Hro Hor. iIntros "Ha Hk Hm". iExists own. iFrame "Ha Hk".
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iApply (big_sepM_mono with "Hm"). intros g [root t] Hg. cbn.
    iIntros "Htk". rewrite /tree_slot. iFrame "Htk". iLeft. iPureIntro.
    exact (Hex g root t Hg).
  Qed.

  (* ---- 2b.  THE DEED, THE TICKET, AND THE FROZEN DEED ---------------- *)

  (* "I own the subtree [t] at [root]" -- the map element, EXCLUSIVE, and
     the ticket half beside it (see [tree_names]). *)
  Definition tree_deed (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (g ↪[tn_own r] (root, t))%I.

  Definition tree_tkt (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (g ↪[tn_tk r]{# (1/2)%Qp} (root, t))%I.

  Definition tree_own (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (tree_deed r g root t ∗ tree_tkt r g root t)%I.

  Lemma tree_own_split (r : tree_names) (g : gname) (root : Z) (t : ttree) :
    tree_own r g root t ⊣⊢ tree_deed r g root t ∗ tree_tkt r g root t.
  Proof using . reflexivity. Qed.

  (* ...and it is TIMELESS, which is what lets a deed ride a walk's cursor
     out from under the invariant's later ([PinnedObs] section 11a). *)
  Global Instance tree_own_timeless r g root t : Timeless (tree_own r g root t).
  Proof using . rewrite /tree_own /tree_deed /tree_tkt. apply _. Qed.

  (* ...AND ITS FROZEN FORM: the element PERSISTED.  An owner that will
     never move its subtree again may trade the deed for a persistent one
     -- and what it buys is the [□]-shaped claim law below, which is what
     a walk (many hops, each reading the claim) needs and which no linear
     deed can pay.  The trade is one-way by construction: a persisted
     element cannot be updated, so a frozen owner's subtree is frozen for
     the whole application (any move inside it taints) -- and, now that a
     move PARKS the deed, a frozen owner cannot even enter the in-flight
     arm, because it holds no [DfracOwn] of its element at all. *)
  Definition tree_pin (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (g ↪[tn_own r]□ (root, t) ∗ g ↪[tn_tk r]□ (root, t))%I.

  Global Instance tree_pin_persistent r g root t : Persistent (tree_pin r g root t).
  Proof using . rewrite /tree_pin. apply _. Qed.
  Global Instance tree_pin_timeless r g root t : Timeless (tree_pin r g root t).
  Proof using . rewrite /tree_pin. apply _. Qed.

  Lemma tree_freeze (r : tree_names) (g : gname) (root : Z) (t : ttree) :
    tree_own r g root t ==∗ tree_pin r g root t.
  Proof using .
    rewrite /tree_own /tree_deed /tree_tkt /tree_pin. iIntros "[H1 H2]".
    iMod (ghost_map_elem_persist with "H1") as "$".
    iMod (ghost_map_elem_persist with "H2") as "$". done.
  Qed.

  (* the exclusion the in-flight arm rests on: a PARKED deed is the whole
     element, so it stands beside no further fraction -- linear or frozen *)
  Lemma tree_elem_excl (γ : gname) (g : gname) (dq : dfrac) (p q : Z * ttree) :
    g ↪[γ] p -∗ g ↪[γ]{dq} q -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    iPureIntro. exact (exclusive_l (DfracOwn 1) dq Hv).
  Qed.

  (* two deeds at one generation are two authorities at one key *)
  Lemma tree_own_excl (r : tree_names) (g : gname) (root root' : Z)
      (t t' : ttree) :
    tree_own r g root t -∗ tree_own r g root' t' -∗ False.
  Proof using .
    rewrite /tree_own /tree_deed. iIntros "[H1 _] [H2 _]".
    iDestruct (tree_elem_excl with "H1 H2") as %[].
  Qed.

  (* ---- 2b'.  THE THREE MOVES ON THE BODY ----------------------------- *)

  (* (i) THE PURE FACTS EVERY MINT AND EVERY TRANSPORT READS, without
     spending the body: the view is tree shaped and the era has a root. *)
  Lemma tree_body_facts (r : tree_names) (av : aview) :
    tree_body r av -∗
      tree_body r av ∗ ⌜aview_tree_wf av /\ adir_at av FsImg.ROOTINO
                        /\ aview_rooted av⌝.
  Proof using .
    iIntros "Hb".
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hr & %Hro & %Hor & Hm)".
    iSplitR "".
    - iExists own. iFrame "Ha Hk Hm". iSplit; [by iPureIntro |].
      iSplit; [by iPureIntro |]. iSplit; by iPureIntro.
    - iPureIntro. exact (conj (proj1 Hwf) (conj Hr Hro)).
  Qed.

  (* (ii) THE EMPTY PARTITION, which is what every fresh instance is born
     at (the transport's clone, era 0's mint). *)
  Lemma tree_body_empty (r : tree_names) (av : aview) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO -> aview_rooted av ->
    (* THE EMPTY MAPS ARE ANNOTATED, and they have to be since lane TL-5:
       [treeG] carries TWO [ghost_mapG] instances now (the ownership map
       and the era-licence registry), so a bare [∅] under [ghost_map_auth_frac]
       no longer determines its key and value types and resolution may
       pick the registry's. *)
    ghost_map_auth_frac (tn_own r) 1 (∅ : gmap gname (Z * ttree)) -∗
    ghost_map_auth_frac (tn_tk r) 1 (∅ : gmap gname (Z * ttree)) -∗
    tree_body r av.
  Proof using .
    intros Hwf Hr Hro. iIntros "Ha Hk".
    assert (Hwf0 : own_wf av (∅ : gmap gname (Z * ttree))).
    { split_and!; [exact Hwf | ..]; intros g *; rewrite lookup_empty;
        discriminate. }
    assert (Hex0 : tree_exact av (∅ : gmap gname (Z * ttree))).
    { intros g root t Hg. rewrite lookup_empty in Hg. discriminate. }
    assert (Hor0 : own_rooted av (∅ : gmap gname (Z * ttree))).
    { intros g root t Hg. rewrite lookup_empty in Hg. discriminate. }
    iApply (tree_body_intro r av ∅ Hwf0 Hex0 Hr Hro Hor0 with "Ha Hk []").
    by rewrite big_sepM_empty.
  Qed.

  (* (iii) THE READ, at ANY fraction of the deed's own element -- linear or
     frozen.  The IN-FLIGHT arm is refuted by exclusivity: it parks the
     WHOLE element, which stands beside no further fraction. *)
  Lemma tree_body_read (r : tree_names) (av : aview) (g : gname) (dq : dfrac)
      (root : Z) (t : ttree) :
    g ↪[tn_own r]{dq} (root, t) -∗ tree_body r av -∗
      ⌜subtree av root = Some t⌝ ∗ g ↪[tn_own r]{dq} (root, t) ∗ tree_body r av.
  Proof using .
    iIntros "Hg Hb".
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hr & %Hro & %Hor & Hm)".
    iDestruct (ghost_map_lookup with "Ha Hg") as %Hlk.
    iDestruct (big_sepM_lookup_acc _ own g (root, t) Hlk with "Hm")
      as "[Hs Hback]".
    iDestruct "Hs" as "[Htk [%Hex | [Hpark _]]]"; last first.
    { iDestruct (tree_elem_excl with "Hpark Hg") as %[]. }
    iSplitR; [by iPureIntro |]. iFrame "Hg".
    iExists own. iFrame "Ha Hk". iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iApply "Hback". rewrite /tree_slot.
    iFrame "Htk". iLeft. by iPureIntro.
  Qed.

  (* (iv) THE TICKET SPLITS, which is what makes the owner's half and the
     slot's half two readings of one element. *)
  Lemma tk_split (γ g : gname) (p : Z * ttree) :
    g ↪[γ] p ⊣⊢ g ↪[γ]{# (1/2)%Qp} p ∗ g ↪[γ]{# (1/2)%Qp} p.
  Proof using .
    rewrite -(ghost_map_elem_fractional g γ p (1/2)%Qp (1/2)%Qp) Qp.div_2 //.
  Qed.

  (* (v) THE MINT AT ONE ENTRY: a FRESH instance owning exactly [g].  The
     era-0 mints and the transport's first deed are both this. *)
  Lemma tree_mint_singleton (g : gname) (root : Z) (t : ttree) :
    ⊢ |==> ∃ r : tree_names,
        ghost_map_auth_frac (tn_own r) 1 ({[ g := (root, t) ]} : gmap gname (Z * ttree))
        ∗ ghost_map_auth_frac (tn_tk r) 1 ({[ g := (root, t) ]} : gmap gname (Z * ttree))
        ∗ g ↪[tn_tk r]{# (1/2)%Qp} (root, t)
        ∗ tree_deed r g root t ∗ tree_tkt r g root t.
  Proof using .
    iMod (ghost_map_alloc ({[ g := (root, t) ]} : gmap gname (Z * ttree)))
      as (γa) "[Ha Hea]".
    iMod (ghost_map_alloc ({[ g := (root, t) ]} : gmap gname (Z * ttree)))
      as (γb) "[Hb Heb]".
    rewrite !big_sepM_singleton.
    iEval (rewrite tk_split) in "Heb". iDestruct "Heb" as "[Hb1 Hb2]".
    iModIntro. iExists (γa, γb). rewrite /tn_own /tn_tk /tree_deed /tree_tkt /=.
    iFrame "Ha Hb Hb1 Hea Hb2".
  Qed.

  (* ---- 2c.  THE SUPPLY AND THE TRANSPORT ----------------------------- *)

  (* echo's [echo_sup_of_taint], verbatim at this claim: a tainted
     application claims nothing, so its claim holds of every view -- which
     is the credential the generic user-execution slot runs on. *)
  Lemma tree_sup_of_taint (c : tree_fixed) (r : tree_names) :
    tree_taint c -∗ app_sup_raw (tree_pred c) r.
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /tree_pred. iLeft. iExact "Ht".
  Qed.

  (* ---- 2c'.  THE MINT (SEAM-I's consumer; design section 9.1) -------- *)

  (* THE UNPAID MOVER'S OWN STEP.  With [AppInv.app_step] a BASIC UPDATE
     (seam I), a party that holds the era's counter may pay a view move it
     cannot justify by BUMPING the counter and leaving the claim in its
     taint arm -- design section 3's "the first unpaid move is recorded as
     the taint", as a resource.  It is neither dead (the counter sits at 0
     until somebody actually moves unpaid) nor vacuous (the taint costs the
     era's counter, which exists once).

     WHY THE COUNTER IS A PREMISE AND NOT A ROW OF [tree_body].  Section
     9.1 asked for this lemma FROM NOTHING, with the authority parked in
     the claim's live arm.  That shape is inconsistent, and
     [tree_bump_free_is_vacuous] below is the proof: era 0's claim is
     minted from nothing ([App.xv6_app_adequacy]'s [Happ_init] is
     [⊢ |==> ∃ r, app_pred A c r av], which for this claim is [tree_init]),
     so a bump that needs nothing beside the claim needs nothing at all,
     and [tree_taint c] -- hence [AppInv.app_sup] -- would be free.  (And
     even setting that aside, the TRANSPORT makes an exclusive row of the
     live arm unworkable rather than merely awkward: [app_xfer_boot_raw]
     hands out a SECOND live claim at the one fixed [c] on every crossing,
     so a globally unique row could be transported only by tainting the
     era at each one.)  So the LICENCE travels WITH THE MOVER, and the era
     hands it down: the registry's authority is born with the fixed part
     ([tree_cl] IS [App.app_cl] at this record), the ledger keeps it, and
     [al_pow] files one licence per era which the kernel carries to
     <init> ([App.app_turn]) -- through the era's own resources, never
     through the claim. *)
  Lemma tree_step_bump (c : tree_fixed) (r : tree_names) (av av' : aview) :
    tree_turn c -∗ ▷ tree_pred c r av ==∗ ▷ tree_pred c r av' ∗ tree_taint c.
  Proof using .
    iIntros "Hcl _". iMod (tree_taint_mint c with "Hcl") as "#Ht".
    iModIntro. iSplit; [| iExact "Ht"].
    iNext. rewrite /tree_pred. iLeft. iExact "Ht".
  Qed.

  (* ...and the supply it buys, which is what a generic slot's every
     [AppInv.app_step] is then paid from ([AppInv.app_step_acc]). *)
  Lemma tree_sup_of_bump (c : tree_fixed) (r : tree_names) :
    tree_turn c ==∗ app_sup_raw (tree_pred c) r.
  Proof using .
    iIntros "Hcl". iMod (tree_taint_mint c with "Hcl") as "#Ht".
    iModIntro. iApply (tree_sup_of_taint c r with "Ht").
  Qed.

  (* THE TRANSPORT ([App.Happ_xfer]): a copy of the claim at FRESH names.
     The copy is born OWNING NOTHING -- the empty partition -- which is
     well formed at any view the original's own [own_wf] says is
     tree-shaped.  Echo's [echo_xfer] shape: the fresh authority is
     allocated OUTSIDE the later (the allocation is an update) and the
     arms are read under ONE later. *)
  Lemma tree_xfer (c : tree_fixed) : ⊢ app_xfer_raw (tree_pred c).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree)) as (γa) "Ha".
    iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree)) as (γb) "Hb".
    iAssert (▷ (tree_pred c r av ∗ tree_pred c (γa, γb) av))%I
      with "[H Ha Hb]" as "HH"; last first.
    { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1".
      iExists (γa, γb). iExact "H2". }
    iNext. rewrite /tree_pred.
    iDestruct "H" as "[#Ht | Hb0]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct (tree_body_facts with "Hb0") as "[Hb0 %Hf]".
    destruct Hf as (Hwf & Hr & Hro).
    iSplitL "Hb0"; [by iRight |].
    iRight. iApply (tree_body_empty (γa, γb) av Hwf Hr Hro with "Ha Hb").
  Qed.

  (* ...AND THE ERA'S FIRST DEED, WHICH IS WHAT THE ROOT CONJUNCT BUYS
     (design section 6, finding 4).  The clone is born owning "/" -- the
     whole namespace at the era's root -- and the arm that blocked this
     before is REFUTED rather than answered with [emp]: the claim the
     transport was handed says the view HAS a root directory, so
     [subtree av ROOTINO] is a [Some] and the deed is minted at it.

     THE VIEW IS AVAILABLE OUTSIDE THE LATER (echo's [cons_inum av] trick),
     and the claim itself is TIMELESS, so the refutation runs inside the
     transport's own [==∗] with no later in the way. *)
  Lemma tree_xfer_boot_at (c : tree_fixed) :
    ⊢ app_clone_raw (tree_pred c)
        (fun r' : tree_names =>
           ∃ (g : gname) (t : ttree), tree_own r' g FsImg.ROOTINO t)%I.
  Proof using .
    rewrite /app_clone_raw. iIntros "!>" (r av) "H".
    (* THE VIEW IS AVAILABLE OUTSIDE THE LATER (echo's [cons_inum av]
       trick), so the clone's entry is allocated AT THE ERA'S OWN ROOT
       SUBTREE -- unconditionally, because the deed is only ever cashed
       through the claim law, whose taint arm covers a tainted era. *)
    set (t0 := MkTTree (subtree_nodes av FsImg.ROOTINO) FsImg.ROOTINO).
    iMod (tree_mint_singleton 1%positive FsImg.ROOTINO t0)
      as (r') "(Ha & Hk & Htk & Hown & Hel)".
    iAssert (▷ (tree_pred c r av ∗ tree_pred c r' av))%I
      with "[H Ha Hk Htk]" as "HH"; last first.
    { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
      iFrame "H2". iExists 1%positive, t0. rewrite /tree_own. iFrame "Hown Hel". }
    iNext. rewrite /tree_pred.
    iDestruct "H" as "[#Ht | Hb]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct (tree_body_facts with "Hb") as "[Hb %Hf]".
    destruct Hf as (Hwf & Hr & Hro).
    (* THE ARM THAT BLOCKED THIS is refuted here, from the claim's own
       root conjunct: the era HAS a root directory, so its subtree is a
       [Some] and the clone's single entry is exact at it. *)
    pose proof (subtree_root_of_claim av Hr) as Hsub.
    (* ...AND THE ERA'S FIRST DEED PAYS THE ROOTED CONJUNCT ON THE NOSE
       (lane TL-3R): its root IS [ROOTINO], which reaches itself. *)
    assert (Hex0 : tree_exact av
              ({[ 1%positive := (FsImg.ROOTINO, t0) ]}
                 : gmap gname (Z * ttree))).
    { intros g0 r0 t1 H0. destruct (decide (g0 = 1%positive)) as [-> | Hne].
      - rewrite lookup_singleton_eq in H0. injection H0 as <- <-. exact Hsub.
      - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    assert (Hor0 : own_rooted av
              ({[ 1%positive := (FsImg.ROOTINO, t0) ]}
                 : gmap gname (Z * ttree))).
    { intros g0 r0 t1 H0. destruct (decide (g0 = 1%positive)) as [-> | Hne].
      - rewrite lookup_singleton_eq in H0. injection H0 as <- <-.
        apply nreach_refl.
      - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    assert (Hwf0 : own_wf av
              ({[ 1%positive := (FsImg.ROOTINO, t0) ]}
                 : gmap gname (Z * ttree))).
    { split_and!.
      - exact Hwf.
      - intros g0 r0 t1 H0. destruct (decide (g0 = 1%positive)) as [-> | Hne].
        + rewrite lookup_singleton_eq in H0. injection H0 as <- <-. exact Hr.
        + rewrite lookup_singleton_ne in H0; [discriminate | congruence].
      - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
        destruct (decide (g1 = 1%positive)) as [-> | H1e].
        + destruct (decide (g2 = 1%positive)) as [-> | H2e];
            [ exact (Hne eq_refl) | ].
          rewrite lookup_singleton_ne in H2; [discriminate | congruence].
        + rewrite lookup_singleton_ne in H1; [discriminate | congruence]. }
    iSplitL "Hb"; [by iRight |].
    iRight.
    iApply (tree_body_intro r' av _ Hwf0 Hex0 Hr Hro Hor0 with "Ha Hk [Htk]").
    by rewrite big_sepM_singleton.
  Qed.

  (* ===================================================================== *)
  (*  3.  THE CLAIM LAWS                                                    *)
  (* ===================================================================== *)

  (* THE STABLE FORM (design section 2), LINEAR: the deed goes in and
     comes back, and what it buys is the reading of its own subtree at
     the view the claim was read at -- or the taint.  This is
     [AppEcho.echo_cons_abs_law]'s shape and [PinnedObs.pobs_walk_dead]'s
     premise; a fire that opens [AppInv.app_inv] once (every AU commit,
     every claim-update) takes it as it stands. *)
  Lemma tree_claim_law (c : tree_fixed) (r : tree_names) :
    ⊢ □ (∀ (v : aview) (g : gname) (root : Z) (t : ttree),
           tree_own r g root t -∗ tree_pred c r v -∗
           tree_pred c r v ∗ tree_own r g root t ∗
           (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    iIntros "!>" (v g root t) "Hg [#HT | Hb]".
    { iSplitR; [by iLeft |]. iFrame "Hg". iRight. iExact "HT". }
    iDestruct "Hg" as "[Hd Htk]".
    iDestruct (tree_body_read r v g (DfracOwn 1) root t with "Hd Hb")
      as "(%Hex & Hd & Hb)".
    iSplitL "Hb"; [by iRight |]. rewrite /tree_own. iFrame "Hd Htk".
    iLeft. by iPureIntro.
  Qed.

  (* ...AND THE [□] FORM, at a FROZEN deed: this is
     [PinnedObs.pobs_walk]'s and [ExecRun.exec_walk_of_pin]'s premise on
     the nose, at [Pin := fun v => subtree v root = Some t].  It cannot be
     had from a linear deed -- a walk reads the claim once per hop, under
     a [□] -- which is what [tree_freeze] is for. *)
  Lemma tree_pin_law (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t : ttree) :
    tree_pin r g root t -∗
    □ (∀ v : aview, tree_pred c r v -∗
         tree_pred c r v ∗ (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    iIntros "#Hg !>" (v) "[#HT | Hb]".
    { iSplitR; [by iLeft |]. iRight. iExact "HT". }
    iDestruct "Hg" as "[#Hd #Hk]".
    iDestruct (tree_body_read r v g DfracDiscarded root t with "Hd Hb")
      as "(%Hex & _ & Hb)".
    iSplitL "Hb"; [by iRight |]. iLeft. by iPureIntro.
  Qed.

  (* THE PIN'S CONTENT (finding 2), as the walk families want it and as
     far as the tree claim can pin it: at every view the claim admits,
     the path's run is the SAME run ([resolve_hops], computed from the
     tree alone), it ends at the SAME inum, and the row there is the
     tree's node -- up to the LINK COUNT, which the application tree does
     not carry.  [PinnedObs.pin_resolves_at] wants the row on the nose;
     an absnode-level variant of it takes this. *)
  Lemma tree_resolves_abs (root d i : Z) (t : ttree) (bs : list (bv 8))
      (pl : list (bv 8)) :
    fs_proper (path_elems pl) ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile bs) ->
    forall av : aview,
      subtree av root = Some t ->
      arun av d (path_elems pl) (resolve_hops t d pl)
      /\ resolve_hops t d pl !!! 0%nat = d
      /\ resolve_hops t d pl !!! length (path_elems pl) = i
      /\ (exists k : nat, av !! i = Some (MkAnode (AFile bs) k)).
  Proof using .
    intros Hp Hd Hres av Ht.
    exact (subtree_resolves_pin_file t d i bs pl Hp Hres av root Ht
             (subtree_dom_reach av root t d Ht Hd)).
  Qed.

  (* ===================================================================== *)
  (*  4.  THE STEP WANDS                                                    *)
  (* ===================================================================== *)

  (* THE ENGINE, and the only Iris in the free steps: a view move that
     preserves the THREE pure conjuncts at EVERY ownership map preserves
     the claim.  [AppInv.app_top_update_step] takes exactly this shape.
     (The third is the root's, TL-3's: section 1a' pays it at every leg out
     of the leg's own [own_wf] lemma.) *)
  Lemma tree_step_gen (c : tree_fixed) (r : tree_names) (av av' : aview) :
    (forall own : gmap gname (Z * ttree),
       own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
       aview_rooted av -> own_rooted av own ->
       own_wf av' own /\ tree_exact av' own /\ adir_at av' FsImg.ROOTINO) ->
    (* THE ROOTED CONJUNCTS (lane TL-3R, design section 7.8's RULING), as a
       SECOND obligation rather than as three more conjuncts of the first:
       every landed [tree_pres_*] then still answers the first hypothesis
       on the nose, and the new one is a [TreeView] section 9 lemma. *)
    (forall own : gmap gname (Z * ttree),
       own_wf av own -> adir_at av FsImg.ROOTINO ->
       aview_rooted av -> own_rooted av own ->
       aview_rooted av' /\ own_rooted av' own) ->
    tree_pred c r av -∗ tree_pred c r av'.
  Proof using .
    intros Hstep Hroot. iIntros "[#HT | Hb]"; [by iLeft |].
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hr & %Hro & %Hor & Hm)".
    (* the [∀ own] hypothesis is applied at the SYNCED map (section 1h):
       the slotted body has no global exactness to hand it. *)
    destruct (tree_step_pure av av' own Hstep Hwf Hr Hro Hor)
      as (Hwf' & Hr' & Hslot).
    destruct (Hroot own Hwf Hr Hro Hor) as (Hro' & Hor').
    iRight. iExists own. iFrame "Ha Hk". iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |].
    iApply (big_sepM_mono with "Hm"). intros g [root t] Hg. cbn.
    rewrite /tree_slot /=. iIntros "[Htk Harm]". iFrame "Htk".
    iDestruct "Harm" as "[%Hex | Hfl]"; [| by iRight].
    iLeft. iPureIntro. exact (Hslot g root t Hg Hex).
  Qed.

  (* THE CLAIM'S PURE CONJUNCTS, read without spending it -- the tree
     application's own [tree_body_facts] lifted through the taint arm.
     This is what an owner reads at the fire to turn the ARM's receipt
     into create's missing credential (section 1k). *)
  Lemma tree_pred_facts (c : tree_fixed) (r : tree_names) (av : aview) :
    tree_pred c r av -∗
      tree_pred c r av ∗
      (⌜aview_tree_wf av /\ adir_at av FsImg.ROOTINO /\ aview_rooted av⌝
       ∨ tree_taint c).
  Proof using .
    iIntros "[#HT | Hb]".
    { iSplitR; [by iLeft |]. iRight. iExact "HT". }
    iDestruct (tree_body_facts with "Hb") as "[Hb %Hf]".
    iSplitL "Hb"; [by iRight |]. iLeft. by iPureIntro.
  Qed.

  (* ---- 4a.  THE INVISIBLE LEGS: free, and at EVERY owner ------------- *)

  (* mkdir's two interior [dirlink]s.  The tree hides the dots, so these
     move nothing at all -- whoever pays them, whatever anyone owns. *)
  Lemma tree_step_dots (c : tree_fixed) (r : tree_names) (av : aview)
      (i d : Z) :
    tree_pred c r av -∗ tree_pred c r (delta_dots i d av).
  Proof using .
    iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_dots av i d Hro)
             | exact (own_rooted_dots av own i d Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_cong av (delta_dots i d av) own (tview_delta_dots av i d)
             Hwf Hex Hr).
  Qed.

  Lemma tree_step_dot (c : tree_fixed) (r : tree_names) (av : aview) (i : Z) :
    tree_pred c r av -∗ tree_pred c r (delta_dot i av).
  Proof using .
    iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_dot av i Hro)
             | exact (own_rooted_dot av own i Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_cong av (delta_dot i av) own (tview_delta_dot av i) Hwf Hex Hr).
  Qed.

  (* link's TARGET leg at a row the view has: a pure count bump *)
  Lemma tree_step_link_tgt (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (a : anode) :
    av !! i = Some a ->
    tree_pred c r av -∗ tree_pred c r (delta_link_tgt i a av).
  Proof using .
    intros Ha. iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_link_tgt av i a Ha Hro)
             | exact (own_rooted_link_tgt av own i a Ha Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_cong av (delta_link_tgt i a av) own
             (tview_delta_link_tgt av i a Ha) Hwf Hex Hr).
  Qed.

  (* unlink's TARGET leg above the last link: a count drop *)
  Lemma tree_step_unl_tgt_live (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (a : anode) :
    av !! i = Some a -> (2 <= an_nlink a)%nat ->
    tree_pred c r av -∗ tree_pred c r (delta_unl_tgt i av).
  Proof using .
    intros Ha Hnl. iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_unl_tgt_live av i a Ha Hnl Hro)
             | exact (own_rooted_unl_tgt_live av own i a Ha Hnl Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_cong av (delta_unl_tgt i av) own
             (tview_delta_unl_tgt_live av i a Ha Hnl) Hwf Hex Hr).
  Qed.

  (* ...AND AT THE LAST LINK, at a NON-DIRECTORY target (lane TL-3P): the
     row LEAVES, and it is STILL free at every owner -- nothing names it,
     so nobody reached it.  The two credentials are the entry leg's own
     ([TreeView.aview_no_edge_to_unl_ent]) and the target's kind.  This is
     half of TL-2's recorded wall, lifted: what is left owed is a
     DIRECTORY's last link, which is [rmdir]-shaped. *)
  Lemma tree_step_unl_tgt_last (c : tree_fixed) (r : tree_names) (av : aview)
      (tg : Z) (a : anode) :
    av !! tg = Some a -> an_nlink a = 1%nat ->
    aview_no_edge_to av tg -> ~ adir_at av tg ->
    tree_pred c r av -∗ tree_pred c r (delta_unl_tgt tg av).
  Proof using .
    intros Ha Hnl Hno Hnd. iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      assert (Hrt : tg <> FsImg.ROOTINO) by (intros ->; exact (Hnd Hr)).
      split; [exact (aview_rooted_unl_tgt av tg a Ha Hnl Hno Hrt Hro)
             | exact (own_rooted_unl_tgt av own tg a Ha Hnl Hno Hrt Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_unl_tgt_last av own tg a Ha Hnl Hno Hnd Hwf Hex Hr).
  Qed.

  (* ---- 4b.  CREATE'S ARM LEG: free, because a fresh inum is nobody's -- *)

  (* the first of create's two legs, and the reason they may be paid in
     either order: no entry dangles ([aview_closed], a conjunct of the
     claim's own [own_wf]), so nothing names the armed inum yet and no
     owner reaches it. *)
  Lemma tree_step_arm (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (n : absnode) :
    av !! i = None -> tabs_leaf (tabs_of n) ->
    tree_pred c r av -∗ tree_pred c r (delta_arm i n av).
  Proof using .
    intros Hi Hleaf. iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_arm av i n Hi Hleaf Hro)
             | exact (own_rooted_arm av own i n Hi Hleaf Hor)]. }
    intros own Hwf Hex Hr _ _.
    exact (tree_pres_arm av own i n Hi Hleaf Hwf Hex Hr).
  Qed.

  (* ...AND CREATE'S UNARM LEG, FREE (lane TL-3R; design section 7.4's
     WALL 2).  The row the failure arm removes is one nothing names and
     which is not the era's root, so no owner reaches it -- whatever its
     KIND, which is what makes this usable at mkdir's child. *)
  Lemma tree_step_unarm (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (a : anode) :
    av !! i = Some a -> an_nlink a = 1%nat ->
    aview_no_edge_to av i -> i <> FsImg.ROOTINO ->
    tree_pred c r av -∗ tree_pred c r (delta_unarm i av).
  Proof using .
    intros Ha Hnl Hno Hri. iApply tree_step_gen; last first.
    { intros own Hwf Hr Hro Hor.
      split; [exact (aview_rooted_unarm av i Hno Hri Hro)
             | exact (own_rooted_unarm av own i Hno Hri Hor)]. }
    intros own Hwf Hex Hr _ Hor.
    exact (tree_pres_unarm av own i a Ha Hnl Hno Hri Hwf Hex Hr Hor).
  Qed.

  (* ---- 4c.  AN OWNER'S OWN MOVE: THE TWO PHASES (section 7.2) -------- *)
  (*                                                                      *)
  (*  TL-2's FINDING 1, CLOSED -- and closed with NO [AppInv] seam (design *)
  (*  section 7.1 stays designed and deferred).  An owner's move is        *)
  (*                                                                      *)
  (*    PHASE 1  an UPDATE-FREE STEP ([tree_step_move_*] below), which is  *)
  (*             exactly what [AppInv.app_step] takes: the deed and a      *)
  (*             fresh token are PARKED in the entry's slot, which moves   *)
  (*             from EXACT to IN FLIGHT and then says nothing at all;     *)
  (*    PHASE 2  a RESYNC ([tree_resync]), run in the fire's own second    *)
  (*             phase, where the POST view and the delta's equation are   *)
  (*             in hand: the exact arm is REFUTED, the parked deed and    *)
  (*             the token come back, the entry is updated to the post     *)
  (*             tree, and the slot closes EXACT again.                    *)
  (*                                                                      *)
  (*  TL-2's [tree_move_gen] / [tree_move_write] / [tree_move_trunc] /     *)
  (*  [tree_move_create] / [tree_move_unl_ent] basic updates are RETIRED   *)
  (*  into this shape: their content is the pure layer of section 1i,      *)
  (*  which both phases read.                                             *)

  (* PHASE 1's ENGINE.  Nothing comes back: that is what makes it a plain
     wand.  The mover's own slot is refuted in the IN-FLIGHT arm first --
     two parked deeds at one key are two whole elements -- so an owner can
     have at most one move in flight, which is design section 7.2's
     "EXCLUSIVITY, restated". *)
  Lemma tree_step_move_gen (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t : ttree) (γi : gname) (av av' : aview) :
    (forall own : gmap gname (Z * ttree),
       own !! g = Some (root, t) -> subtree av root = Some t ->
       own_wf av own -> adir_at av FsImg.ROOTINO ->
       aview_rooted av -> own_rooted av own ->
       tree_move_out av av' own g) ->
    (* the rooted conjuncts, as at [tree_step_gen] (lane TL-3R) *)
    (forall own : gmap gname (Z * ttree),
       own !! g = Some (root, t) -> subtree av root = Some t ->
       own_wf av own -> adir_at av FsImg.ROOTINO ->
       aview_rooted av -> own_rooted av own ->
       aview_rooted av' /\ own_rooted av' own) ->
    tree_deed r g root t -∗ tok γi -∗ tree_pred c r av -∗ tree_pred c r av'.
  Proof using .
    intros Hstep Hroot. iIntros "Hd Htok [#HT | Hb]"; [by iLeft |].
    rewrite /tree_deed.
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hr & %Hro & %Hor & Hm)".
    iDestruct (ghost_map_lookup with "Ha Hd") as %Hlk.
    iDestruct (big_sepM_delete _ own g (root, t) Hlk with "Hm") as "[Hs Hm]".
    iDestruct "Hs" as "[Htk [%Hex | [Hpark _]]]"; last first.
    { iDestruct (tree_elem_excl with "Hpark Hd") as %[]. }
    destruct (Hstep own Hlk Hex Hwf Hr Hro Hor) as (Hwf' & Hr' & Hout).
    destruct (Hroot own Hlk Hex Hwf Hr Hro Hor) as (Hro' & Hor').
    iRight. iExists own. iFrame "Ha Hk". iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |].
    iApply (big_sepM_delete _ own g (root, t) Hlk). iSplitR "Hm".
    - rewrite /tree_slot /=. iFrame "Htk". iRight. iFrame "Hd".
      iExists γi. iExact "Htok".
    - iApply (big_sepM_mono with "Hm"). intros g' [root' t'] Hg'. cbn.
      apply lookup_delete_Some in Hg' as [Hne Hg'].
      rewrite /tree_slot /=. iIntros "[Htk' Harm]". iFrame "Htk'".
      iDestruct "Harm" as "[%Hex' | Hfl]"; [| by iRight].
      iLeft. iPureIntro.
      rewrite (Hout g' root' t' (fun Hc => Hne (eq_sym Hc)) Hg'). exact Hex'.
  Qed.

  (* WRITE: the owner's file's bytes are spliced.  Every other owner's
     subtree is untouched by DISJOINTNESS (section 1i). *)
  Lemma tree_step_move_write (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) (off : nat) (new bs0 : list (bv 8))
      (nl : nat) (av : aview) (γi : gname) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    i ∈ dom (tv_nodes t) ->
    tree_deed r g root t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_write i off new av).
  Proof using .
    intros Hi Hd. iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      split; [exact (aview_rooted_write av i off new bs0 nl Hi Hro)
             | exact (own_rooted_write av own i off new bs0 nl Hi Hor)]. }
    intros own Hg Ht Hwf Hr _ _.
    exact (tree_move_write_pure av own g root i t off new bs0 nl
             Hi Hg Ht Hd Hwf Hr).
  Qed.

  Lemma tree_step_move_trunc (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) (bs0 : list (bv 8)) (nl : nat) (av : aview)
      (γi : gname) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    i ∈ dom (tv_nodes t) ->
    tree_deed r g root t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_trunc i av).
  Proof using .
    intros Hi Hd. iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      split; [exact (aview_rooted_trunc av i bs0 nl Hi Hro)
             | exact (own_rooted_trunc av own i bs0 nl Hi Hor)]. }
    intros own Hg Ht Hwf Hr _ _.
    exact (tree_move_trunc_pure av own g root i t bs0 nl Hi Hg Ht Hd Hwf Hr).
  Qed.

  (* CREATE, FUSED (TL-1 landed [own_wf_create] at the fused delta): a
     fresh leaf hung under a directory of the owner's own tree. *)
  Lemma tree_step_move_create (c : tree_fixed) (r : tree_names) (g : gname)
      (root d : Z) (nm : fname) (i : Z) (n : absnode) (t : ttree)
      (e : gmap fname Z) (nl : nat) (av : aview) (γi : gname) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = None -> tabs_leaf (tabs_of n) ->
    d ∈ dom (tv_nodes t) ->
    tree_deed r g root t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_create d nm i n av).
  Proof using .
    intros Hnm Hd Hnone Hi Hleaf Hdd. iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      assert (Hrd : nreach (tview av) FsImg.ROOTINO d).
      { exact (nreach_trans (tview av) FsImg.ROOTINO root d (Hor g root t Hg)
                 (subtree_dom_reach av root t d Ht Hdd)). }
      split;
        [ exact (aview_rooted_create av d nm i n e nl Hnm Hd Hnone Hi Hleaf
                   Hrd Hro)
        | exact (own_rooted_create av own d nm i n e nl Hnm Hd Hnone Hi Hleaf
                   Hor) ]. }
    intros own Hg Ht Hwf Hr _ _.
    exact (tree_move_create_pure av own g root d nm i n t e nl
             Hnm Hd Hnone Hi Hleaf Hg Ht Hdd Hwf Hr).
  Qed.

  (* ...AND CREATE'S PARENT LEG ALONE (lane TL-3P), which is the delta the
     landed fire commits: the child is already armed, so an owner's create
     move is [delta_ent] and its [own_wf] preservation is TL-1's
     [own_wf_ent].  The fused form above stays, because the pure layer
     proves both. *)
  Lemma tree_step_move_ent (c : tree_fixed) (r : tree_names) (g : gname)
      (root d : Z) (nm : fname) (i : Z) (a : anode) (t : ttree)
      (e : gmap fname Z) (nl : nat) (av : aview) (γi : gname) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = Some a -> tabs_leaf (tnode_of a) ->
    ~ adir_at av i -> aview_no_edge_to av i ->
    d ∈ dom (tv_nodes t) ->
    tree_deed r g root t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_ent d nm i av).
  Proof using .
    intros Hnm Hd Hnone Hi Hleaf Hnd Hno Hdd.
    iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      assert (Hrd : nreach (tview av) FsImg.ROOTINO d).
      { exact (nreach_trans (tview av) FsImg.ROOTINO root d (Hor g root t Hg)
                 (subtree_dom_reach av root t d Ht Hdd)). }
      split; [exact (aview_rooted_ent av d nm i e nl a Hnm Hd Hnone Hi Hrd Hro)
             | exact (own_rooted_ent av own d nm i e nl a Hnm Hd Hnone Hi Hor)]. }
    intros own Hg Ht Hwf Hr _ _.
    exact (tree_move_ent_pure av own g root d nm i a t e nl
             Hnm Hd Hi Hleaf Hnd Hno Hg Ht Hdd Hwf Hr).
  Qed.

  (* ...AND THE SAME LEG BY THE ROOTED ROUTE (lane TL-3R), at an owner of
     "/": the two credentials are READ OFF THE CLAIM from the arm's PURE
     receipt, so this form takes neither [aview_no_edge_to] nor
     [~ adir_at av i] -- and therefore covers MKDIR's directory child. *)
  Lemma tree_step_move_ent_rooted (c : tree_fixed) (r : tree_names) (g : gname)
      (d : Z) (nm : fname) (i : Z) (a : anode) (t : ttree)
      (e : gmap fname Z) (nl : nat) (av : aview) (γi : gname) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = Some a -> tabs_leaf (tnode_of a) ->
    i ∉ dom (tv_nodes t) ->
    d ∈ dom (tv_nodes t) ->
    tree_deed r g FsImg.ROOTINO t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_ent d nm i av).
  Proof using .
    intros Hnm Hd Hnone Hi Hleaf Hni Hdd.
    iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      pose proof (subtree_dom_reach av FsImg.ROOTINO t d Ht Hdd) as Hrd.
      split; [exact (aview_rooted_ent av d nm i e nl a Hnm Hd Hnone Hi Hrd Hro)
             | exact (own_rooted_ent av own d nm i e nl a Hnm Hd Hnone Hi Hor)]. }
    intros own Hg Ht Hwf Hr Hro Hor.
    exact (tree_move_ent_rooted_pure av own g d nm i a t e nl
             Hnm Hd Hnone Hi Hleaf Hni Hg Ht Hdd Hwf Hr Hro Hor).
  Qed.

  (* UNLINK'S ENTRY LEG: the name goes and the tree RE-CLOSES (the one op
     that can orphan).  The TARGET leg at the last link is not offered --
     see the header. *)
  Lemma tree_step_move_unl_ent (c : tree_fixed) (r : tree_names) (g : gname)
      (root d : Z) (nm : fname) (dec : nat) (t : ttree)
      (e : gmap fname Z) (nl : nat) (tg : Z) (av : aview) (γi : gname) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) ->
    (* THE ENTRY LEG'S SHAPE (lane TL-3R, design section 7.8's second new
       premise): the name being cut points at a node with NO PROPER
       OUT-EDGE -- [SysUnlinkDefs.unl_pre]'s own [dots_only] clause, which
       every unlink fire has already established.  It is what makes the
       cut LOCAL: the only node the deleted edge can orphan is its own
       target, and the target is not a source. *)
    e !! nm = Some tg ->
    (forall s : fname, fs_pname s -> astep av tg s = None) ->
    d ∈ dom (tv_nodes t) ->
    tree_deed r g root t -∗ tok γi -∗
    tree_pred c r av -∗ tree_pred c r (delta_unl_ent d nm dec av).
  Proof using .
    intros Hnm Hd He Hlf Hdd. iApply tree_step_move_gen; last first.
    { intros own Hg Ht Hwf Hr Hro Hor.
      assert (Hleaf : forall s : fname, fs_pname s ->
                nstep (tview av) tg s = None).
      { intros s Hs. rewrite (nstep_tview av tg s Hs). exact (Hlf s Hs). }
      assert (Hstep : nstep (tview av) d nm = Some tg).
      { rewrite (nstep_tview av d nm Hnm) /astep /aents Hd /anode_ents /= He //. }
      pose proof (subtree_dom_reach av root t d Ht Hdd) as Hrd.
      pose proof (nreach_hop (tview av) root d nm tg Hrd Hnm Hstep) as Hrtg.
      (* THE TARGET IS NOBODY'S ROOT, and it is not a premise: a stranger's
         root is refuted by [own_wf]'s NON-NESTING (the mover reaches [tg]),
         and the MOVER'S OWN root is refuted by the target's own shape -- a
         node with no proper out-edge reaches nothing but itself, so [d]
         would have to BE [tg], which its own edge refutes. *)
      assert (Hnotroot : forall (g0 : gname) (r0 : Z) (t0 : ttree),
                own !! g0 = Some (r0, t0) -> r0 <> tg).
      { intros g0 r0 t0 H0 Heq. subst r0.
        destruct (decide (g0 = g)) as [-> | Hne].
        - rewrite Hg in H0. injection H0 as Hrt _. rewrite Hrt in Hrd.
          pose proof (nreach_leaf_eq (tview av) tg d Hleaf Hrd) as Hdtg.
          rewrite Hdtg (Hleaf nm Hnm) in Hstep. discriminate.
        - destruct Hwf as (_ & _ & Hnn).
          exact (Hnn g g0 root t tg t0 (fun Hc => Hne (eq_sym Hc)) Hg H0 Hrtg). }
      split;
        [ exact (aview_rooted_unl_ent av d nm dec e nl tg Hnm Hd He Hlf Hro)
        | exact (own_rooted_unl_ent av own d nm dec e nl tg Hnm Hd He Hlf
                   Hnotroot Hor) ]. }
    intros own Hg Ht Hwf Hr _ _.
    exact (tree_move_unl_ent_pure av own g root d nm dec t e nl
             Hd Hg Ht Hdd Hwf Hr).
  Qed.

  (* ---- 4d.  THE FREE ARM OF A WRITE (section 7.2's "[tree_op δ t = t]
     takes the FREE step instead").  The KERNEL picks the offset and the
     bytes, so an owner supplying a write chain has to answer both cases --
     and the invisible one is free at every owner, because the delta is the
     IDENTITY on the view (section 1j). *)
  Lemma tree_step_write_free (c : tree_fixed) (r : tree_names) (i : Z)
      (off : nat) (new bs0 : list (bv 8)) (nl : nat) (av : aview) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    blk_splice off new bs0 = bs0 ->
    tree_pred c r av -∗ tree_pred c r (delta_write i off new av).
  Proof using .
    intros Hi Hsp. rewrite (delta_write_id av i off new bs0 nl Hi Hsp).
    iIntros "$".
  Qed.

  Lemma tree_step_trunc_free (c : tree_fixed) (r : tree_names) (i : Z)
      (nl : nat) (av : aview) :
    av !! i = Some (MkAnode (AFile []) nl) ->
    tree_pred c r av -∗ tree_pred c r (delta_trunc i av).
  Proof using .
    intros Hi. rewrite (delta_trunc_id av i [] nl Hi eq_refl). iIntros "$".
  Qed.

  (* ---- 4e.  PHASE 2: THE RESYNC -------------------------------------- *)
  (*                                                                      *)
  (*  What the fire's SECOND phase runs, with the post view in hand.  The  *)
  (*  owner presents its MOVE TICKET -- the half it never parted with --   *)
  (*  which identifies its entry against the claim's own half; the EXACT   *)
  (*  arm is refuted by the delta's INSIDE lemma ([t' <> t] is exactly     *)
  (*  design section 7.2's [tree_op δ t ≠ t]); the parked deed and the     *)
  (*  token come back; the entry moves to the post tree and the slot       *)
  (*  closes EXACT.  What the owner gets is its DEED AT THE MOVED TREE --  *)
  (*  the receipt the U tier carries home.                                 *)
  Lemma tree_resync (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t t' : ttree) (av' : aview) :
    subtree av' root = Some t' -> t' <> t ->
    tree_tkt r g root t -∗ tree_pred c r av' ==∗
      tree_pred c r av' ∗ (tree_own r g root t' ∨ tree_taint c).
  Proof using .
    intros Ht' Hne. iIntros "Htk [#HT | Hb]".
    { iModIntro. iSplitR; [by iLeft |]. iRight. iExact "HT". }
    rewrite /tree_tkt.
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hr & %Hro & %Hor & Hm)".
    iDestruct (ghost_map_lookup with "Hk Htk") as %Hlk.
    iDestruct (big_sepM_delete _ own g (root, t) Hlk with "Hm") as "[Hs Hm]".
    iDestruct "Hs" as "[Htk2 [%Hex | [Hpark Htok]]]".
    { exfalso. rewrite Hex in Ht'. injection Ht' as Heq.
      exact (Hne (eq_sym Heq)). }
    iAssert (g ↪[tn_tk r]{DfracOwn 1} (root, t))%I with "[Htk Htk2]" as "Htkf".
    { rewrite tk_split. iFrame "Htk Htk2". }
    iMod (ghost_map_update (root, t') with "Ha Hpark") as "[Ha Hd]".
    iMod (ghost_map_update (root, t') with "Hk Htkf") as "[Hk Htkf]".
    iEval (rewrite tk_split) in "Htkf". iDestruct "Htkf" as "[Htk1 Htk2]".
    iModIntro. iSplitR "Hd Htk1"; last first.
    { iLeft. rewrite /tree_own /tree_deed /tree_tkt. iFrame "Hd Htk1". }
    iRight. iExists (<[g := (root, t')]> own). iFrame "Ha Hk".
    iSplit.
    { iPureIntro. exact (own_wf_retree av' own g root t t' Hlk Hwf). }
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit.
    { iPureIntro. exact (own_rooted_retree av' own g root t t' Hlk Hor). }
    iApply (big_sepM_delete _ (<[g := (root, t')]> own) g (root, t')
              (lookup_insert_eq own g (root, t'))).
    iSplitR "Hm".
    - rewrite /tree_slot /=. iFrame "Htk2". iLeft. by iPureIntro.
    - rewrite delete_insert_eq. iExact "Hm".
  Qed.

  (* ...and the REFUND (design section 7.2's "THE REFUND ARM"): a syscall
     that fails before firing hands the deed and the ticket straight back,
     which is exactly [tree_own_split] read right to left.  Nothing to
     prove -- it is stated so the fire sites can name it. *)
  Lemma tree_move_refund (r : tree_names) (g : gname) (root : Z) (t : ttree) :
    tree_deed r g root t -∗ tree_tkt r g root t -∗ tree_own r g root t.
  Proof using . iIntros "Hd Ht". rewrite /tree_own. iFrame "Hd Ht". Qed.

  (* ===================================================================== *)
  (*  5.  THE MINTS: era 0, the boot owner, and the hand-down               *)
  (* ===================================================================== *)

  (* ERA 0 ([App.Happ_init]), at the EMPTY partition: nobody owns
     anything, so all the claim says is that the view is tree-shaped.
     THE PREMISE IS THE GATE: at the theorem's own literal the view is the
     mkfs image's, and [aview_tree_wf] of it is a pure fact about the
     image that TL-4 must compute. *)
  Lemma tree_init (c : tree_fixed) (av : aview) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO -> aview_rooted av ->
    ⊢ |==> ∃ r : tree_names, tree_pred c r av.
  Proof using .
    intros Hwf Hr Hro.
    iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree)) as (γa) "Ha".
    iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree)) as (γb) "Hb".
    iModIntro. iExists (γa, γb). iRight.
    iApply (tree_body_empty (γa, γb) av Hwf Hr Hro with "Ha Hb").
  Qed.

  (* WHY THE MINT CANNOT BE FREE (the SEAM-I lane's finding; design
     section 9.1 asked for [tree_step_bump] with NO premise).  Era 0's
     claim is minted from nothing at any tree-shaped view -- that is
     [tree_init] just above, and it is forced by [App.xv6_app_adequacy]'s
     [Happ_init] binder, which is [⊢ |==> ∃ r, app_pred A c r av] with no
     antecedent.  So a bump provable from the claim alone is provable from
     nothing, [AppInv.app_sup] is free at this claim
     ([tree_sup_of_taint]), and every owner's deed reads back a disjunction
     whose right arm always holds: the application says nothing.  No
     arrangement of rows inside [tree_body] escapes this, because the
     hypothesis quantifies over the instance [r] and a fresh one is
     allocatable. *)
  Lemma tree_bump_free_is_vacuous (c : tree_fixed) (av : aview) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO -> aview_rooted av ->
    (forall (r : tree_names) (av1 av2 : aview),
       ⊢ ▷ tree_pred c r av1 ==∗ ▷ tree_pred c r av2 ∗ tree_taint c) ->
    ⊢ |==> tree_taint c.
  Proof using .
    intros Hwf Hr Hro Hbump.
    iMod (tree_init c av Hwf Hr Hro) as (r) "Hp".
    iMod (Hbump r av av with "[Hp]") as "[_ #Ht]"; [iNext; iExact "Hp" |].
    iModIntro. iExact "Ht".
  Qed.

  (* ...AND THE ERA'S FIRST OWNER BESIDE IT: the boot process owns the
     whole namespace at the root the image gives it.  (Design section 3's
     "the first process owns / at the mkfs image's tree"; the view is an
     argument, so this is equally the mint at any era.) *)
  Lemma tree_init_at (c : tree_fixed) (av : aview) (g : gname)
      (root : Z) (t : ttree) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO -> aview_rooted av ->
    nreach (tview av) FsImg.ROOTINO root ->
    subtree av root = Some t ->
    ⊢ |==> ∃ r : tree_names, tree_pred c r av ∗ tree_own r g root t.
  Proof using .
    intros Hwf Hroot Hro Hrr Ht.
    iMod (tree_mint_singleton g root t) as (r) "(Ha & Hk & Htk & Hd & Ht2)".
    assert (Hex0 : tree_exact av ({[ g := (root, t) ]} : gmap gname (Z * ttree))).
    { intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
      - rewrite lookup_singleton_eq in H0. injection H0 as <- <-. exact Ht.
      - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    assert (Hor0 : own_rooted av ({[ g := (root, t) ]} : gmap gname (Z * ttree))).
    { intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
      - rewrite lookup_singleton_eq in H0. injection H0 as <- <-. exact Hrr.
      - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    assert (Hwf0 : own_wf av ({[ g := (root, t) ]} : gmap gname (Z * ttree))).
    { split_and!.
      - exact Hwf.
      - intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
        + rewrite lookup_singleton_eq in H0. injection H0 as <- <-.
          by apply subtree_Some_inv in Ht as (Hd & _).
        + rewrite lookup_singleton_ne in H0; [discriminate | congruence].
      - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
        destruct (decide (g1 = g)) as [-> | H1e].
        + destruct (decide (g2 = g)) as [-> | H2e].
          * exact (Hne eq_refl).
          * rewrite lookup_singleton_ne in H2; [discriminate | congruence].
        + rewrite lookup_singleton_ne in H1; [discriminate | congruence]. }
    iModIntro. iExists r. rewrite /tree_own. iFrame "Hd Ht2". iRight.
    iApply (tree_body_intro r av _ Hwf0 Hex0 Hroot Hro Hor0 with "Ha Hk [Htk]").
    by rewrite big_sepM_singleton.
  Qed.

  (* THE HAND-DOWN (finding 3): an owner retires its entry and a fresh
     generation is born owning a SUB-ROOT of it.  A pure re-partition of
     the ownership map -- no view moves -- so it runs at whatever view the
     invariant is at ([AppInv.app_claim_update]'s shape), and the child's
     non-nesting with every stranger IS TL-1's disjointness theorem. *)
  Lemma tree_grant (c : tree_fixed) (r : tree_names) (g : gname)
      (root root' : Z) (t : ttree) (e : gmap fname Z) (av : aview) :
    tv_nodes t !! root' = Some (ADir e) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r av ∗
      ((∃ (g' : gname) (t' : ttree),
          tree_own r g' root' t' ∗ ⌜subtree av root' = Some t'⌝)
       ∨ tree_taint c).
  Proof using .
    intros Hr'. iIntros "Hg [#HT | Hb]".
    { iModIntro. iSplitR; [by iLeft |]. iRight. iExact "HT". }
    rewrite /tree_own /tree_deed /tree_tkt. iDestruct "Hg" as "[Hd Htk]".
    iDestruct "Hb" as (own) "(Ha & Hk & %Hwf & %Hroot & %Hro & %Hor & Hm)".
    iDestruct (ghost_map_lookup with "Ha Hd") as %Hlk.
    iDestruct (big_sepM_delete _ own g (root, t) Hlk with "Hm") as "[Hs Hm]".
    iDestruct "Hs" as "[Htk2 [%Ht | [Hpark _]]]"; last first.
    { iDestruct (tree_elem_excl with "Hpark Hd") as %[]. }
    iAssert (g ↪[tn_tk r]{DfracOwn 1} (root, t))%I with "[Htk Htk2]" as "Htkf".
    { rewrite tk_split. iFrame "Htk Htk2". }
    pose proof (tree_sub_dir av root root' t e Ht Hr') as Hdir.
    pose proof (subtree_of_dir av root' Hdir) as Ht'.
    set (g' := fresh (dom own)).
    assert (Hfresh : own !! g' = None).
    { apply not_elem_of_dom. rewrite /g'. apply is_fresh. }
    assert (Hfd : delete g own !! g' = None).
    { rewrite lookup_delete_ne; [exact Hfresh |].
      intros ->. by rewrite Hfresh in Hlk. }
    iMod (ghost_map_delete with "Ha Hd") as "Ha".
    iMod (ghost_map_delete with "Hk Htkf") as "Hk".
    iMod (ghost_map_insert g' (root', MkTTree (subtree_nodes av root') root')
            with "Ha") as "[Ha Hd']"; [exact Hfd |].
    iMod (ghost_map_insert g' (root', MkTTree (subtree_nodes av root') root')
            with "Hk") as "[Hk Hk']"; [exact Hfd |].
    iEval (rewrite tk_split) in "Hk'". iDestruct "Hk'" as "[Hk1 Hk2]".
    pose proof (own_wf_grant av own g g' root root' t
                  (MkTTree (subtree_nodes av root') root') e
                  Hlk Ht Hr' Hwf) as Hwf'.
    iModIntro. iSplitR "Hd' Hk1"; last first.
    { iLeft. iExists g', (MkTTree (subtree_nodes av root') root').
      iFrame "Hd' Hk1". iPureIntro. exact Ht'. }
    (* THE HAND-DOWN PAYS THE ROOTED CONJUNCT (lane TL-3R): the child's
       root is a node of its parent's OWN tree, so it is reachable from the
       parent's root and hence from [ROOTINO]. *)
    assert (Hor' : own_rooted av
              (<[g' := (root', MkTTree (subtree_nodes av root') root')]>
                 (delete g own))).
    { apply (own_rooted_grant av own g g' root root' t
               (MkTTree (subtree_nodes av root') root') Hlk Ht); [| exact Hor].
      apply elem_of_dom. by eexists. }
    iRight. iExists (<[g' := (root', MkTTree (subtree_nodes av root') root')]>
                       (delete g own)).
    iFrame "Ha Hk". iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
    iApply (big_sepM_insert _ (delete g own) g'
              (root', MkTTree (subtree_nodes av root') root') Hfd).
    iSplitR "Hm".
    - rewrite /tree_slot /=. iFrame "Hk2". iLeft. by iPureIntro.
    - iExact "Hm".
  Qed.

End AppTree.

(* ===================================================================== *)
(*  6.  THE RECORD                                                        *)
(* ===================================================================== *)

(* THE TREE APPLICATION as an [App.xv6_app]: the claim is [tree_pred], the
   fixed part is the taint counter, and EVERY CONSOLE FIELD IS THE GENERIC
   SLOT'S ([App.app_triv]'s) -- this application claims a file system and
   nothing about the two UARTs.  [app_kill := True]: a kill does not taint
   a tree application (design section 3 -- an owner dying leaves its entry
   orphaned, and nothing moves an orphaned subtree until a parent
   re-grants it).

   THE LEDGER IS THE ERA-LICENCE REGISTRY'S AUTHORITY (lane TL-5's
   hand-down): it carries the fixed part's birth for the whole run, which
   is what lets the power-on step file ONE LICENCE PER ERA and hand it to
   <init> through [App.app_turn].  It records nothing about the trace --
   the taint's mint is a ghost move inside a process's own step and NO
   trace event witnesses it (design section 8.2), so there is nothing for
   a trace ledger to see. *)
Section AppTreeRecord.
  Context {Σ : gFunctors} `{!treeG Σ}.

  (* the ledger: the registry's authority, at every history *)
  Definition tree_R (c : tree_fixed) (_ : list mobs) : iProp Σ := tree_cl c.

  Global Instance tree_R_timeless c h : Timeless (tree_R c h).
  Proof using . rewrite /tree_R. apply _. Qed.

  (* THE ERA'S FIRST DEED, as the boot resource (design section 6, finding
     4, landed by TL-3): the era's first process owns "/" at whatever the
     image's namespace is there -- or the application is already tainted,
     which is the arm a tainted era transports at.  It is av-FREE, which
     is what [App.app_boot] requires and what blocked this before the
     claim grew its root conjunct. *)
  Definition tree_boot (_ : tree_fixed) (_ : nat) (r : tree_names) : iProp Σ :=
    (∃ (g : gname) (t : ttree), tree_own r g FsImg.ROOTINO t)%I.

  Definition app_tree : App.xv6_app Σ :=
    MkApp tree_fixed tree_cl tree_names tree_pred
          tree_boot                          (* app_boot *)
          tree_R                             (* app_R *)
          (* THE CONSOLE INTERFACE (upstream redesign R2/R4): a tree
             application says nothing about a received byte, puts no price
             on a kill and claims nothing of the console *)
          (fun _ => app_iface_triv Σ)        (* app_ifc *)
          (* THE ERA'S TURN (lane TL-5): the licence its <init> may spend
             to taint the claim -- the one per-era linear channel from the
             application to the era's first process, and the ONLY route by
             which [AppInv.app_sup] is ever reachable at this record. *)
          (fun c _ => tree_turn c)           (* app_turn *)
          (* ...the same at the swap's and <init>'s stages, and the
             trivial sync values: no sync ledger (sync SY3-A1) *)
          (fun c _ => tree_turn c)           (* app_turn' *)
          (fun c _ => tree_turn c)           (* app_turn'' *)
          (fun c _ => tree_turn c)           (* app_iturn *)
          app_triv_cls app_triv_born app_triv_ok app_triv_okc app_triv_tk app_triv_hk
          (fun _ _ => True).                 (* app_phi *)

  (* ---- the obligations of [App.xv6_app_adequacy] that are lemmas ---- *)

  Lemma app_tree_birth (γd γsw γreg γst : gname) :
    ⊢ |==> ∃ c : app_fixed app_tree,
        ⌜app_born app_tree γd γsw γreg γst c⌝ ∗
        app_cls app_tree c ∗ app_cl app_tree c.
  Proof using .
    apply app_birth_of_valid_cls;
      [exact app_triv_cls_intro | intros; exact Logic.I |].
    cbn [app_tree app_fixed app_cl]. iApply tree_birth.
  Qed.

  Lemma app_tree_Rt (c : app_fixed app_tree) (h : list mobs) :
    Timeless (app_R app_tree c h).
  Proof using . cbn [app_tree app_R]. apply _. Qed.

  Lemma app_tree_tagp (c : app_fixed app_tree) (h : list mobs) :
    Persistent (app_tag app_tree c h).
  Proof using . cbn [app_tree app_tag]. apply _. Qed.

  Lemma app_tree_tagt (c : app_fixed app_tree) (h : list mobs) :
    Timeless (app_tag app_tree c h).
  Proof using . cbn [app_tree app_tag]. apply _. Qed.

  Lemma app_tree_killp (c : app_fixed app_tree) : Persistent (app_kill app_tree c).
  Proof using . cbn [app_tree app_kill]. apply _. Qed.

  Lemma app_tree_killt (c : app_fixed app_tree) : Timeless (app_kill app_tree c).
  Proof using . cbn [app_tree app_kill]. apply _. Qed.

  (* A KILL COSTS THIS APPLICATION NOTHING (design section 3) *)
  Lemma app_tree_kill (c : app_fixed app_tree) (r : app_names app_tree) :
    app_sup_raw (app_pred app_tree c) r ⊢ □ app_kill app_tree c.
  Proof using .
    rewrite /app_kill. cbn [app_tree app_ifc app_iface_triv ai_kill].
    iIntros "_ !>". done.
  Qed.

  (* ONE LICENCE over the console claim (redesign R2): the tree
     application's claim is [emp], so every console event on it is free;
     and its timelessness, vacuous at [emp]. *)
  Lemma app_tree_cons_sup (c : app_fixed app_tree) (r : app_names app_tree) :
    app_sup_raw (app_pred app_tree c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_tree c k h H ==∗
             app_cons app_tree c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons. cbn [app_tree app_ifc app_iface_triv ai_cons].
    rewrite /cons_res_triv. iIntros "_ !>" (k h H ev) "_". by iModIntro.
  Qed.

  Lemma app_tree_R0 (c : app_fixed app_tree) :
    app_cl app_tree c ⊢ |==> app_R app_tree c [].
  Proof using .
    cbn [app_tree app_cl app_R]. rewrite /tree_R. iIntros "H". by iModIntro.
  Qed.

  (* THE POWER STEP, AND THE HAND-DOWN (lane TL-5): the ledger rides, the
     era's console claim is [emp] -- and the era's TURN is a fresh licence
     filed in the registry the ledger holds.  This is the one step of the
     machine that runs once per era, so it is the only place a per-era
     linear thing can be minted, and the kernel carries it to <init>
     ([App.app_turn]'s own paragraph). *)
  Lemma app_tree_pow (c : app_fixed app_tree) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_tree c h ==∗
      app_R app_tree c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_tree c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            app_turn app_tree c (S (obs_boots h))).
  Proof using .
    intros _. rewrite /app_cons.
    cbn [app_tree app_R app_ifc app_iface_triv ai_cons app_turn].
    rewrite /tree_R. iIntros "H".
    destruct on.
    { iModIntro. iSplitL "H"; [iExact "H" |]. done. }
    iMod (tree_licence_mint c with "H") as "[H Ht]". iModIntro.
    iSplitL "H"; [iExact "H" |]. iSplitR; [done |]. iExact "Ht".
  Qed.

  (* ...at the identity on the turn, the slot keeping its copy (sync
     SY3-A1: [SystemAdequacy.app_xfer_boot_raw_of_clone]) *)
  Lemma app_tree_boot (HSt : mono_natG Σ) (c : app_fixed app_tree) (k : nat)
      (γst : gname) (gen : nat) :
    ⊢ app_xfer_boot_raw HSt (app_pred app_tree c) (app_okc app_tree c)
        (app_boot app_tree c k)
        (app_turn app_tree c k) (app_turn' app_tree c k) γst gen.
  Proof using .
    cbn [app_tree app_pred app_boot app_turn app_turn']. rewrite /tree_boot.
    apply app_xfer_boot_raw_of_clone.
    iApply tree_xfer_boot_at.
  Qed.

  (* ...and the plain transport the commit's merge is made of
     ([AppInv.app_merge_raw_of_xfer]) *)
  Lemma app_tree_xfer (c : app_fixed app_tree) :
    ⊢ app_xfer_raw (app_pred app_tree c).
  Proof using . cbn [app_tree app_pred]. exact (tree_xfer c). Qed.

End AppTreeRecord.

(* ===================================================================== *)
(*  7.  WHAT THE RECORD STILL OWES ([App.xv6_app_adequacy]'s binders)     *)
(*                                                                       *)
(*  Discharged above, as lemmas at the record's fields: [Hbirth], [HRt],  *)
(*  [al_kill], [al_sup], [HR0], [Hpow], [Happ_boot].               *)
(*                                                                       *)
(*  Trivial at this record's fields and left to the instance site (they   *)
(*  are [app_triv]'s one-liners at [emp] claims -- see                    *)
(*  [App.xv6_app_adequacy_triv_xv6Σ]'s [ltac:] block): [Htx], [Hrx],      *)
(*  [Hphi] (the conclusion is [True]).                                    *)
(*                                                                       *)
(*  LANDED ELSEWHERE:                                                     *)
(*    [Happ_init] -- era 0's claim at the IMAGE's view: [TreeImg.         *)
(*      tree_Happ_init] (lane TL-4), a computation over the mkfs image.   *)
(*    [Hinit_boot] -- the first process's exec bundle at "/init":         *)
(*      [UTreeAdequacy.tree_Hinit_boot] (lane TL-5), out of the ERA'S OWN *)
(*      LICENCE ([app_turn] above): the licence mints the taint           *)
(*      ([tree_sup_of_bump]), the taint IS [AppInv.app_sup] at this claim *)
(*      ([tree_sup_of_taint]), and the generic bundle follows             *)
(*      ([SystemAdequacy.init_boot_of_sup]).  design/user-tree.md         *)
(*      section 9.1's wall (a), closed the way section 8.4 wanted.        *)
(*    ...and the whole class instance and the closed corollary at the     *)
(*      literal image: [UTreeAdequacy.v].                                 *)
(*                                                                       *)
(*  WHAT THE SECOND APPLICATION DOES NOT YET HAVE, and design/user-tree.md *)
(*  section 9.2 is the worklist: a VERIFIED <init> at this claim, which   *)
(*  would move the mint from the boot bundle to <init>'s own exec of /sh. *)
(* ===================================================================== *)

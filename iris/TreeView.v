(* TreeView.v -- THE APPLICATION TREE: a pure reading of [aview] at a root.

   Design of record: claude-notes/design/user-tree.md (TL-0), lane TL-1.
   ZERO Iris: nothing here mentions an [iProp], a ghost name or a Sigma;
   the whole file is a theory of [gmap]s, and it sits below [AppInv] so
   that the tree application's claim ([tree_pred], lane TL-2) can be
   stated over it.

   THE TWO TREES (user-tree.md section 1).  This is NOT [FsRep.fs_rep]'s
   kernel-boundary tree: that one is a reading of the kernel's inode
   ghosts, whose job is kernel-internal.  This one is a reading of
   [FsAbsDefs.abs_view] -- THE LIVE NAMESPACE -- at a root [r]: the nodes
   reachable from [r] by directory entries, with the dots hidden.  It
   lives in an application predicate and never in a kernel invariant.

   WHY NOT [FsTree.fsnode] (the brief's first question).  [fsnode] has two
   arms, [NFile] and [NDir]; a DEVICE reads as [NFile []] ([FsTree]'s
   header: "the type halfword distinguishing T_FILE from T_DEVICE is the
   dinode's business, not the tree's").  That is right for the kernel
   tree and wrong here: a program that mknod's /console and then opens it
   must be able to tell its own device node from an empty file, and the
   console IS the second application's subject.  Extending [fsnode] with a
   device arm was the brief's recommendation; it is declined, because
   [fsnode] is the KERNEL tree's node type -- it is what [FsTree.node_of]
   is total onto, and [node_of] cannot see a device (the dinode's type
   halfword is not in the tree's data).  Adding the arm would force a
   decision inside the kernel-boundary reading and touch FsTree's cone
   (essentially the whole tree) for an application-tier need: exactly the
   conflation section 1 of the design forbids.

   WHAT IS USED INSTEAD IS NOT A NEW TYPE EITHER: the application tree's
   node is [FsAbsDefs.absnode] -- [anode] minus [nlink], which is the
   design's own "same shape modulo nlink and ADev".  [tnode_of] is the
   projection: the node's content, with the dots deleted from a
   directory's entry map.  So the tree's node type is the view's node
   type, and [ttree] is [FsTree.fstree]'s shape ([MkTree nodes root])
   over it.

   NLINK IS DROPPED, and that is a decision with a consequence TL-2 must
   know: the claim "my subtree is exactly [t]" pins every node's CONTENT
   and the whole shape of the namespace below the root, but NOT the link
   counts.  Four of the landed delta legs ([delta_dots], [delta_dot],
   [delta_link_tgt] at a row the view has, and [delta_unl_tgt] above the
   last link) move nothing but counts and dots, and are therefore
   INVISIBLE in the tree -- which is what makes the owner's step wands
   for mkdir's interior legs free.  The price is
   paid at [PinnedObs.pin_resolves_at], whose pinned row is an [anode]:
   section 6's [subtree_resolves_pin] supplies the [absnode] and an
   EXISTENTIAL count.  See the report / worklist note.

   Layout:
     1. names, the dot-hiding projection, [tview]
     2. the walk on a node map ([nstep]/[npath]/[nchain]) and its bridge
        to [FsAbsDefs]'s [astep]/[apath_at]/[arun]
     3. reachability: the saturating iteration, [nreach_set], [nclose],
        and [subtree]
     4. well-formedness, non-nesting, and SUBTREE DISJOINTNESS
     5. the delta lemmas: inside the subtree the tree moves by a tree op,
        outside it does not move at all
     6. path resolution in a tree, and its equivalence with [arun] on the
        view
     7. [own_wf] preservation under an owner's own-subtree deltas
     8. the parent prefix, and create's parent leg alone (lane TL-3P)
     9. THE ROOTED VIEW (lane TL-3R): [aview_rooted] / [own_rooted], the
        two pure conjuncts the claim carries, their preservation at every
        landed leg, and the two credentials they buy at create's parent
        leg -- design/user-tree.md section 7.8's RULING
*)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
(* the ssreflect tactic language only ([rewrite /def]); no [iProp], no
   camera and no ghost name appears anywhere below *)
From iris.proofmode Require Import proofmode.
(* the tree-wide [set_solver] override -- EXPORT so the dead-import sweep
   keeps it (FastSetSolver.v's rule, BitmapEnc.v's note) *)
Require Export FastSetSolver.
Require Import FsBlocks.       (* [blk_splice]: write's splice              *)
Require Import PathElems.      (* [path_elems]                              *)
Require Import FsTree.         (* [fname], [DOT], [DOTDOT], [fs_proper]     *)
Require Import FsAbsDefs.      (* [absnode], [anode], [aview], [arun]       *)
Require Import FsAbsDelta.     (* the landed delta legs                     *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  NAMES, THE PROJECTION, AND THE TREE                              *)
(* ===================================================================== *)

(* A PROPER name -- [FsTree.fs_proper]'s element predicate, named, because
   every statement here is about proper names and only about them.  The
   dots are the two links every xv6 directory carries; the application
   tree hides them (design section 1: "dots hidden"), so a name that IS a
   dot names no edge of this tree. *)
Definition fs_pname (s : fname) : Prop := s <> DOT /\ s <> DOTDOT.

Global Instance fs_pname_dec (s : fname) : Decision (fs_pname s).
Proof. rewrite /fs_pname. apply and_dec; apply not_dec; apply _. Defined.

Lemma fs_proper_cons (s : fname) (p : list fname) :
  fs_proper (s :: p) <-> fs_pname s /\ fs_proper p.
Proof. rewrite /fs_proper /fs_pname Forall_cons //. Qed.

Lemma fs_proper_app (p q : list fname) :
  fs_proper (p ++ q) <-> fs_proper p /\ fs_proper q.
Proof. rewrite /fs_proper Forall_app //. Qed.

Lemma fs_proper_nil : fs_proper [].
Proof. constructor. Qed.

Lemma fs_proper_singleton (s : fname) : fs_pname s -> fs_proper [s].
Proof. intros Hs. by apply Forall_singleton. Qed.

(* THE DOT-HIDING of one directory's entry map.  Total, idempotent, and
   the identity on every proper lookup: hiding is invisible to a walk
   that never names a dot. *)
Definition hide_dots (e : gmap fname Z) : gmap fname Z :=
  delete DOT (delete DOTDOT e).

Lemma hide_dots_lookup (e : gmap fname Z) (s : fname) :
  fs_pname s -> hide_dots e !! s = e !! s.
Proof.
  intros [H1 H2]. rewrite /hide_dots !lookup_delete_ne //.
Qed.

Lemma hide_dots_lookup_Some (e : gmap fname Z) (s : fname) (i : Z) :
  hide_dots e !! s = Some i -> fs_pname s /\ e !! s = Some i.
Proof.
  rewrite /hide_dots. intros Hs.
  destruct (decide (s = DOT)) as [-> | Hd].
  { rewrite lookup_delete_eq in Hs. discriminate. }
  rewrite lookup_delete_ne in Hs; [| congruence].
  destruct (decide (s = DOTDOT)) as [-> | Hdd].
  { rewrite lookup_delete_eq in Hs. discriminate. }
  rewrite lookup_delete_ne in Hs; [| congruence].
  split; [split; assumption | exact Hs].
Qed.

(* the two names are distinct, which is what makes the hiding a pair of
   independent deletes *)
Lemma dot_ne_dotdot : DOT <> DOTDOT.
Proof. rewrite /DOT /DOTDOT. intros Hc. discriminate. Qed.

(* the dots go in and the hiding takes them straight back out: mkdir's
   two interior [dirlink]s are invisible to this tree *)
Lemma hide_dots_insert_dots (e : gmap fname Z) (i d : Z) :
  hide_dots (<[DOT := i]> (<[DOTDOT := d]> e)) = hide_dots e.
Proof.
  rewrite /hide_dots (delete_insert_ne _ DOTDOT DOT);
    [| intros Hc; exact (dot_ne_dotdot (eq_sym Hc))].
  rewrite !delete_insert_eq //.
Qed.

Lemma hide_dots_insert_dot (e : gmap fname Z) (i : Z) :
  hide_dots (<[DOT := i]> e) = hide_dots e.
Proof.
  rewrite /hide_dots (delete_insert_ne _ DOTDOT DOT);
    [| intros Hc; exact (dot_ne_dotdot (eq_sym Hc))].
  rewrite delete_insert_eq //.
Qed.

(* ...and a PROPER insert or delete commutes with the hiding *)
Lemma hide_dots_insert (e : gmap fname Z) (s : fname) (i : Z) :
  fs_pname s -> hide_dots (<[s := i]> e) = <[s := i]> (hide_dots e).
Proof.
  intros [H1 H2]. rewrite /hide_dots.
  rewrite (delete_insert_ne _ DOTDOT s); [| congruence].
  rewrite (delete_insert_ne _ DOT s); [| congruence]. reflexivity.
Qed.

(* deletes commute unconditionally, dots or not *)
Lemma hide_dots_delete (e : gmap fname Z) (s : fname) :
  hide_dots (delete s e) = delete s (hide_dots e).
Proof.
  rewrite /hide_dots (delete_delete e DOTDOT s) (delete_delete _ DOT s) //.
Qed.

(* THE PROJECTION [absnode -> absnode]: the node's content with the dots
   hidden, and then [anode -> absnode], which additionally drops [nlink]
   (header). *)
Definition tabs_of (n : absnode) : absnode :=
  match n with
  | ADir e => ADir (hide_dots e)
  | n' => n'
  end.

Definition tnode_of (a : anode) : absnode := tabs_of (an_node a).

(* THE VIEW, PROJECTED: the whole namespace as a node map of the tree's
   own type.  [subtree] is a closure of this at a root, so every lemma
   about the tree is a lemma about [tview]. *)
Definition tview (av : aview) : gmap Z absnode := tnode_of <$> av.

Lemma tview_lookup (av : aview) (i : Z) : tview av !! i = tnode_of <$> av !! i.
Proof. rewrite /tview lookup_fmap //. Qed.

Lemma tview_lookup_Some (av : aview) (i : Z) (a : anode) :
  av !! i = Some a -> tview av !! i = Some (tnode_of a).
Proof. intros Ha. rewrite tview_lookup Ha //. Qed.

Lemma tview_lookup_None (av : aview) (i : Z) :
  av !! i = None -> tview av !! i = None.
Proof. intros Ha. rewrite tview_lookup Ha //. Qed.

Lemma tview_dom (av : aview) : dom (tview av) = dom av.
Proof. rewrite /tview dom_fmap_L //. Qed.

(* THE TREE.  [FsTree.fstree]'s shape over [absnode] (header: why not
   [fstree] itself). *)
Record ttree := MkTTree { tv_nodes : gmap Z absnode ; tv_root : Z }.

Global Instance ttree_eq_dec : EqDecision ttree.
Proof. solve_decision. Defined.

(* ===================================================================== *)
(*  2.  THE WALK ON A NODE MAP, AND THE BRIDGE TO [apath_at]             *)
(* ===================================================================== *)

(* One step out of node [d] by name [s].  A file, a device and an inum the
   map does not have all have NO out-edges -- [FsTree.tree_ent]'s rule and
   [FsAbsDefs.astep]'s, restated at this node type. *)
Definition nents (m : gmap Z absnode) (d : Z) : option (gmap fname Z) :=
  match m !! d with Some (ADir e) => Some e | _ => None end.

Definition nstep (m : gmap Z absnode) (d : Z) (s : fname) : option Z :=
  nents m d ≫= (fun e => e !! s).

Fixpoint npath (m : gmap Z absnode) (d : Z) (ps : list fname) : option Z :=
  match ps with
  | [] => Some d
  | s :: ps' => match nstep m d s with
                | Some c => npath m c ps'
                | None => None
                end
  end.

Lemma npath_nil (m : gmap Z absnode) (d : Z) : npath m d [] = Some d.
Proof. reflexivity. Qed.

Lemma npath_cons (m : gmap Z absnode) (d : Z) (s : fname) (ps : list fname) :
  npath m d (s :: ps)
  = match nstep m d s with Some c => npath m c ps | None => None end.
Proof. reflexivity. Qed.

Lemma npath_app (m : gmap Z absnode) (d : Z) (ps qs : list fname) :
  npath m d (ps ++ qs)
  = match npath m d ps with Some c => npath m c qs | None => None end.
Proof.
  revert d. induction ps as [| s ps IH]; intros d; [reflexivity |].
  cbn [app]. rewrite !npath_cons.
  destruct (nstep m d s) as [c |]; [apply IH | reflexivity].
Qed.

Lemma npath_snoc (m : gmap Z absnode) (d : Z) (ps : list fname) (s : fname) :
  npath m d (ps ++ [s])
  = match npath m d ps with Some c => nstep m c s | None => None end.
Proof.
  rewrite npath_app. destruct (npath m d ps) as [c |]; [| reflexivity].
  rewrite npath_cons. destruct (nstep m c s); reflexivity.
Qed.

(* the nodes the walk stands on, in order -- [FsTree.path_chain]'s twin,
   and exactly the [hops] list [PinnedObs.pin_resolves_at] is indexed by *)
Fixpoint nchain (m : gmap Z absnode) (d : Z) (ps : list fname) : list Z :=
  match ps with
  | [] => [d]
  | s :: ps' => d :: (match nstep m d s with
                      | Some c => nchain m c ps'
                      | None => []
                      end)
  end.

(* ---- THE BRIDGE: on PROPER names the projected view steps exactly as
   the view does.  Everything the tree layer proves about [npath] is
   therefore a fact about [FsAbsDefs.apath_at]. ------------------------ *)

Lemma nents_tview (av : aview) (d : Z) :
  nents (tview av) d = hide_dots <$> aents av d.
Proof.
  rewrite /nents /aents tview_lookup.
  destruct (av !! d) as [a |]; [| reflexivity].
  rewrite /= /anode_ents /tnode_of. destruct (an_node a); reflexivity.
Qed.

Lemma nstep_tview (av : aview) (d : Z) (s : fname) :
  fs_pname s -> nstep (tview av) d s = astep av d s.
Proof.
  intros Hs. rewrite /nstep /astep nents_tview.
  destruct (aents av d) as [e |]; [| reflexivity].
  cbn. rewrite hide_dots_lookup //.
Qed.

Lemma npath_tview (av : aview) (d : Z) (ps : list fname) :
  fs_proper ps -> npath (tview av) d ps = apath_at av d ps.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hp; [reflexivity |].
  apply fs_proper_cons in Hp as [Hs Hps].
  rewrite npath_cons apath_at_cons (nstep_tview _ _ _ Hs).
  destruct (astep av d s) as [c |]; [apply IH; exact Hps | reflexivity].
Qed.

Lemma nchain_tview (av : aview) (d : Z) (ps : list fname) :
  fs_proper ps -> arun av d ps (nchain (tview av) d ps) \/ apath_at av d ps = None.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hp.
  { left. cbn. constructor. }
  apply fs_proper_cons in Hp as [Hs Hps].
  cbn [nchain]. rewrite (nstep_tview _ _ _ Hs).
  destruct (astep av d s) as [c |] eqn:Hst.
  - destruct (IH c Hps) as [Hr | Hn].
    + left. econstructor; [exact Hst | exact Hr].
    + right. rewrite apath_at_cons Hst //.
  - right. rewrite apath_at_cons Hst //.
Qed.

(* the run a SUCCESSFUL walk realizes: the chain IS the [arun] witness *)
Lemma nchain_arun (av : aview) (d : Z) (ps : list fname) (i : Z) :
  fs_proper ps -> apath_at av d ps = Some i ->
  arun av d ps (nchain (tview av) d ps).
Proof.
  intros Hp Hw. destruct (nchain_tview av d ps Hp) as [Hr | Hn];
    [exact Hr | rewrite Hn in Hw; discriminate].
Qed.

(* ...AND THE TWO ENDS OF THE CHAIN, PURELY (lane TL-3).  [resolves_from]
   answers the walk at every view the claim admits, but
   [PinnedObs.pin_walks_at]'s first two conjuncts are about the hops list
   ALONE -- "the walk starts where the start rule says" and "it ends at the
   inum the resolution names" -- and a pin must state them without any view
   in hand (there may be no view at all at which the claim holds).  Both
   are facts about [nchain]. *)
Lemma nchain_head (m : gmap Z absnode) (d : Z) (ps : list fname) :
  nchain m d ps !!! 0%nat = d.
Proof. destruct ps; reflexivity. Qed.

Lemma nchain_last (m : gmap Z absnode) (d : Z) (ps : list fname) (i : Z) :
  npath m d ps = Some i -> nchain m d ps !!! length ps = i.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hw.
  - cbn in Hw |- *. by injection Hw as <-.
  - rewrite npath_cons in Hw.
    destruct (nstep m d s) as [c |] eqn:Hst; [| discriminate].
    cbn [nchain length]. rewrite Hst. cbn. exact (IH c Hw).
Qed.

(* ===================================================================== *)
(*  3.  REACHABILITY, THE CLOSURE, AND [subtree]                          *)
(* ===================================================================== *)

(* WHAT THE SUBTREE IS: the nodes [r] reaches by PROPER names.  Stated as
   a Prop over paths -- the honest definition -- and COMPUTED below by a
   saturating iteration, which is the only reason any of section 3a
   exists: a [gmap] needs a decidable membership test, and this is it.
   Nothing outside this section unfolds [nexpand]. *)
Definition nreach (m : gmap Z absnode) (r i : Z) : Prop :=
  exists p : list fname, fs_proper p /\ npath m r p = Some i.

Lemma nreach_refl (m : gmap Z absnode) (r : Z) : nreach m r r.
Proof. exists []. split; [apply fs_proper_nil | reflexivity]. Qed.

Lemma nreach_hop (m : gmap Z absnode) (r d : Z) (s : fname) (c : Z) :
  nreach m r d -> fs_pname s -> nstep m d s = Some c -> nreach m r c.
Proof.
  intros (p & Hp & Hw) Hs Hst. exists (p ++ [s]). split.
  - apply fs_proper_app. split; [exact Hp | by apply fs_proper_singleton].
  - rewrite npath_snoc Hw //.
Qed.

Lemma nreach_trans (m : gmap Z absnode) (r d i : Z) :
  nreach m r d -> nreach m d i -> nreach m r i.
Proof.
  intros (p & Hp & Hw) (q & Hq & Hv). exists (p ++ q).
  split; [by apply fs_proper_app | rewrite npath_app Hw //].
Qed.

(* a walk stands on nodes the map HAS: only a directory has out-edges *)
Lemma nstep_dom (m : gmap Z absnode) (d : Z) (s : fname) (c : Z) :
  nstep m d s = Some c -> d ∈ dom m.
Proof.
  rewrite /nstep /nents. destruct (m !! d) as [n |] eqn:Hd; [| discriminate].
  intros _. apply elem_of_dom. by exists n.
Qed.

(* ---- 3a.  THE SATURATING ITERATION (the decision procedure) --------- *)

(* the children of [d] the map HAS, by proper names *)
Definition nkids (m : gmap Z absnode) (d : Z) : gset Z :=
  (match nents m d with Some e => map_img (hide_dots e) | None => ∅ end) ∩ dom m.

Lemma elem_of_nkids (m : gmap Z absnode) (d i : Z) :
  i ∈ nkids m d <-> (exists s, fs_pname s /\ nstep m d s = Some i) /\ i ∈ dom m.
Proof.
  rewrite /nkids elem_of_intersection /nstep.
  destruct (nents m d) as [e |]; cbn.
  - rewrite elem_of_map_img. split.
    + intros [(s & Hs) Hd]. split; [| exact Hd].
      destruct (hide_dots_lookup_Some e s i Hs) as [Hp He]. by exists s.
    + intros [(s & Hp & He) Hd]. split; [| exact Hd].
      exists s. rewrite hide_dots_lookup //.
  - rewrite elem_of_empty. split.
    + intros [[] _].
    + intros [(s & _ & Hc) _]. discriminate.
Qed.

Definition nexpand (m : gmap Z absnode) (X : gset Z) : gset Z :=
  X ∪ ⋃ ((nkids m) <$> elements X).

Lemma elem_of_nexpand (m : gmap Z absnode) (X : gset Z) (i : Z) :
  i ∈ nexpand m X <-> i ∈ X \/ exists d, d ∈ X /\ i ∈ nkids m d.
Proof.
  rewrite /nexpand elem_of_union elem_of_union_list. split.
  - intros [Hi | (Y & HY & Hi)]; [by left | right].
    apply list_elem_of_fmap in HY as (d & -> & Hd).
    exists d. split; [by apply elem_of_elements | exact Hi].
  - intros [Hi | (d & Hd & Hi)]; [by left | right].
    exists (nkids m d). split; [| exact Hi].
    apply list_elem_of_fmap. exists d. split; [reflexivity |].
    by apply elem_of_elements.
Qed.

Lemma nexpand_incl (m : gmap Z absnode) (X : gset Z) : X ⊆ nexpand m X.
Proof. intros i Hi. apply elem_of_nexpand. by left. Qed.

Lemma nexpand_mono (m : gmap Z absnode) (X X' : gset Z) :
  X ⊆ X' -> nexpand m X ⊆ nexpand m X'.
Proof.
  intros Hs i Hi. apply elem_of_nexpand. apply elem_of_nexpand in Hi.
  destruct Hi as [Hi | (d & Hd & Hi)]; [left; by apply Hs |].
  right. exists d. split; [by apply Hs | exact Hi].
Qed.

Fixpoint nexpand_n (m : gmap Z absnode) (X : gset Z) (n : nat) : gset Z :=
  match n with
  | O => X
  | S n' => nexpand m (nexpand_n m X n')
  end.

Lemma nexpand_n_mono_set (m : gmap Z absnode) (X X' : gset Z) (n : nat) :
  X ⊆ X' -> nexpand_n m X n ⊆ nexpand_n m X' n.
Proof.
  intros Hs. induction n as [| n IH]; [exact Hs |].
  cbn. by apply nexpand_mono.
Qed.

Lemma nexpand_n_incl (m : gmap Z absnode) (X : gset Z) (n : nat) :
  X ⊆ nexpand_n m X n.
Proof.
  induction n as [| n IH]; [done |].
  cbn. etrans; [exact IH | apply nexpand_incl].
Qed.

Lemma nexpand_n_le (m : gmap Z absnode) (X : gset Z) (n n' : nat) :
  (n <= n')%nat -> nexpand_n m X n ⊆ nexpand_n m X n'.
Proof.
  intros Hle. induction Hle as [| n' Hle IH]; [done |].
  etrans; [exact IH | apply nexpand_incl].
Qed.

(* one more round on the OUTSIDE is one more round on the inside *)
Lemma nexpand_n_comm (m : gmap Z absnode) (X : gset Z) (n : nat) :
  nexpand_n m (nexpand m X) n = nexpand m (nexpand_n m X n).
Proof. induction n as [| n IH]; [reflexivity | cbn; by rewrite IH]. Qed.

(* SOUNDNESS: everything the iteration finds is reachable *)
Lemma nexpand_n_sound (m : gmap Z absnode) (r : Z) (n : nat) (i : Z) :
  i ∈ nexpand_n m {[r]} n -> nreach m r i /\ (i = r \/ i ∈ dom m).
Proof.
  revert i. induction n as [| n IH]; cbn; intros i Hi.
  { apply elem_of_singleton in Hi as ->. split; [apply nreach_refl | by left]. }
  apply elem_of_nexpand in Hi as [Hi | (d & Hd & Hi)]; [by apply IH |].
  destruct (IH d Hd) as (Hrd & _).
  apply elem_of_nkids in Hi as ((s & Hs & Hst) & Hdom).
  split; [| by right]. exact (nreach_hop m r d s i Hrd Hs Hst).
Qed.

(* COMPLETENESS: a walk of length [k] is found in [k] rounds *)
Lemma nexpand_n_complete (m : gmap Z absnode) (r : Z) (p : list fname) (i : Z) :
  fs_proper p -> npath m r p = Some i -> (i ∈ dom m \/ p = []) ->
  i ∈ nexpand_n m {[r]} (length p).
Proof.
  revert i. induction p as [| s p IH] using rev_ind; intros i Hp Hw Hdom.
  { cbn in Hw. injection Hw as <-. cbn. apply elem_of_singleton. reflexivity. }
  apply fs_proper_app in Hp as [Hq Hs].
  apply fs_proper_cons in Hs as [Hs _].
  rewrite npath_snoc in Hw.
  destruct (npath m r p) as [d |] eqn:Hd; [| discriminate].
  assert (Hddom : d ∈ dom m) by exact (nstep_dom m d s i Hw).
  assert (Hi : i ∈ dom m).
  { destruct Hdom as [Hdom | Hc]; [exact Hdom |].
    exfalso. destruct p; discriminate. }
  rewrite length_app /=. rewrite Nat.add_1_r. cbn.
  apply elem_of_nexpand. right. exists d.
  split; [by apply IH; [| | left] |].
  apply elem_of_nkids. split; [| exact Hi]. by exists s.
Qed.

(* the iteration lives inside a FINITE set, which is what makes it stop *)
Lemma nexpand_n_bound (m : gmap Z absnode) (r : Z) (n : nat) :
  nexpand_n m {[r]} n ⊆ {[r]} ∪ dom m.
Proof.
  intros i Hi. destruct (nexpand_n_sound m r n i Hi) as (_ & [-> | Hd]).
  - apply elem_of_union. left. by apply elem_of_singleton.
  - apply elem_of_union. by right.
Qed.

(* once a round adds nothing, no later round does either *)
Lemma nexpand_n_stable (m : gmap Z absnode) (X : gset Z) (n : nat) :
  nexpand_n m X n = nexpand_n m X (S n) ->
  forall k, (n <= k)%nat -> nexpand_n m X k = nexpand_n m X n.
Proof.
  intros Hst k Hle. induction Hle as [| k Hle IH]; [reflexivity |].
  cbn [nexpand_n]. rewrite IH. symmetry. exact Hst.
Qed.

(* ...and until it does, each round has added one: the counting argument
   that bounds the number of rounds by the size of the map *)
Lemma nexpand_n_grow (m : gmap Z absnode) (r : Z) (n : nat) :
  nexpand_n m {[r]} n = nexpand_n m {[r]} (S n)
  \/ (S n <= size (nexpand_n m {[r]} n))%nat.
Proof.
  induction n as [| n IH].
  { destruct (decide (nexpand_n m {[r]} 0 = nexpand_n m {[r]} 1)) as [He | He];
      [by left | right]. cbn. rewrite size_singleton. lia. }
  destruct IH as [He | Hsz].
  { left. cbn [nexpand_n]. cbn [nexpand_n] in He. by rewrite -He. }
  destruct (decide (nexpand_n m {[r]} (S n) = nexpand_n m {[r]} (S (S n))))
    as [He | He]; [by left | right].
  assert (Hsub : nexpand_n m {[r]} n ⊂ nexpand_n m {[r]} (S n)).
  { split; [apply nexpand_n_le; lia |].
    intros Hc. apply He. cbn [nexpand_n].
    f_equal. apply (anti_symm (⊆)); [apply nexpand_incl | exact Hc]. }
  pose proof (subset_size _ _ Hsub) as Hlt. lia.
Qed.

(* THE COMPUTED REACHABLE SET: [S (size m)] rounds saturate, because the
   whole iteration lives in [{[r]} ∪ dom m]. *)
Definition nreach_set (m : gmap Z absnode) (r : Z) : gset Z :=
  nexpand_n m {[r]} (S (size m)).

Lemma nreach_set_sat (m : gmap Z absnode) (r : Z) :
  nexpand_n m {[r]} (S (size m)) = nexpand_n m {[r]} (S (S (size m))).
Proof.
  destruct (nexpand_n_grow m r (S (size m))) as [He | Hsz]; [exact He |].
  exfalso.
  pose proof (subseteq_size _ _ (nexpand_n_bound m r (S (size m)))) as Hle.
  assert (Hun : (size ({[r]} ∪ dom m) <= 1 + size (dom m))%nat).
  { rewrite size_union_alt size_singleton.
    pose proof (subseteq_size (dom m ∖ {[r]}) (dom m)
                  ltac:(set_solver)) as H2. lia. }
  rewrite size_dom in Hun. lia.
Qed.

Lemma nexpand_n_at (m : gmap Z absnode) (r : Z) (k : nat) :
  (S (size m) <= k)%nat -> nexpand_n m {[r]} k = nreach_set m r.
Proof.
  intros Hle. rewrite /nreach_set.
  exact (nexpand_n_stable m {[r]} (S (size m)) (nreach_set_sat m r) k Hle).
Qed.

(* THE SPEC, and the only fact about [nreach_set] anything below uses *)
Lemma elem_of_nreach_set (m : gmap Z absnode) (r i : Z) :
  i ∈ nreach_set m r <-> nreach m r i /\ (i = r \/ i ∈ dom m).
Proof.
  split.
  - intros Hi. exact (nexpand_n_sound m r _ i Hi).
  - intros ((p & Hp & Hw) & Hd).
    assert (Hin : i ∈ nexpand_n m {[r]} (length p)).
    { apply nexpand_n_complete; [exact Hp | exact Hw |].
      destruct Hd as [-> | Hd]; [| by left].
      destruct p as [| s p]; [by right |].
      rewrite npath_cons in Hw.
      destruct (nstep m r s) as [c |] eqn:Hst; [| discriminate].
      (* the root is in [dom m] as soon as it has an out-edge *)
      left. by apply (nstep_dom m r s c). }
    rewrite -(nexpand_n_at m r (Nat.max (S (size m)) (length p))); [| lia].
    eapply elem_of_weaken; [exact Hin | apply nexpand_n_le; lia].
Qed.

(* ---- 3b.  THE CLOSURE, AND THE SUBTREE ITSELF ---------------------- *)

Definition nclose (m : gmap Z absnode) (r : Z) : gmap Z absnode :=
  filter (fun ix => ix.1 ∈ nreach_set m r) m.

Lemma nclose_lookup_Some (m : gmap Z absnode) (r i : Z) (n : absnode) :
  nclose m r !! i = Some n <-> m !! i = Some n /\ nreach m r i.
Proof.
  rewrite /nclose map_lookup_filter_Some /=. split.
  - intros [Hm Hi]. split; [exact Hm |].
    by apply elem_of_nreach_set in Hi as [? _].
  - intros [Hm Hr]. split; [exact Hm |]. apply elem_of_nreach_set.
    split; [exact Hr |]. right. apply elem_of_dom. by eexists.
Qed.

Lemma nclose_lookup_in (m : gmap Z absnode) (r i : Z) :
  nreach m r i -> nclose m r !! i = m !! i.
Proof.
  intros Hr. destruct (m !! i) as [n |] eqn:Hm.
  - apply nclose_lookup_Some. by split.
  - apply map_lookup_filter_None. by left.
Qed.

Lemma nclose_lookup_out (m : gmap Z absnode) (r i : Z) :
  ~ nreach m r i -> nclose m r !! i = None.
Proof.
  intros Hr. apply map_lookup_filter_None. right. intros n Hm Hi.
  apply Hr. by apply elem_of_nreach_set in Hi as [? _].
Qed.

Lemma nclose_subseteq (m : gmap Z absnode) (r : Z) : nclose m r ⊆ m.
Proof. apply map_filter_subseteq. Qed.

Lemma elem_of_dom_nclose (m : gmap Z absnode) (r i : Z) :
  i ∈ dom (nclose m r) <-> i ∈ dom m /\ nreach m r i.
Proof.
  rewrite !elem_of_dom. split.
  - intros [n Hn]. apply nclose_lookup_Some in Hn as [Hm Hr].
    split; [by eexists | exact Hr].
  - intros [[n Hn] Hr]. exists n. apply nclose_lookup_Some. by split.
Qed.

(* the root is always in its own closure, provided the map has it *)
Lemma nclose_root (m : gmap Z absnode) (r : Z) :
  nclose m r !! r = m !! r.
Proof. apply nclose_lookup_in, nreach_refl. Qed.

(* ---- THE AGREEMENT LAW: the closure sees only what it reaches ------- *)

Lemma nstep_agree (m m' : gmap Z absnode) (d : Z) (s : fname) :
  m !! d = m' !! d -> nstep m d s = nstep m' d s.
Proof. intros Hd. rewrite /nstep /nents Hd //. Qed.

Lemma npath_agree (m m' : gmap Z absnode) (r : Z) :
  (forall j, nreach m r j -> m !! j = m' !! j) ->
  forall (p : list fname) (d i : Z),
    fs_proper p -> nreach m r d ->
    (npath m d p = Some i <-> npath m' d p = Some i).
Proof.
  intros Hag p. induction p as [| s p IH]; intros d i Hp Hd; [done |].
  apply fs_proper_cons in Hp as [Hs Hp].
  rewrite !npath_cons -(nstep_agree m m' d s (Hag d Hd)).
  destruct (nstep m d s) as [c |] eqn:Hst; [| done].
  apply IH; [exact Hp | exact (nreach_hop m r d s c Hd Hs Hst)].
Qed.

(* TWO MAPS THAT AGREE ON WHAT THE ROOT REACHES HAVE THE SAME SUBTREE.
   This is the whole content of the OUTSIDE half of section 5: a delta at
   a node the owner does not reach changes nothing the owner can see. *)
Lemma nreach_agree (m m' : gmap Z absnode) (r : Z) :
  (forall j, nreach m r j -> m !! j = m' !! j) ->
  forall i, nreach m r i <-> nreach m' r i.
Proof.
  intros Hag i. split.
  - intros (p & Hp & Hw). exists p. split; [exact Hp |].
    by apply (npath_agree m m' r Hag p r i Hp (nreach_refl m r)).
  - intros (p & Hp & Hw). exists p. split; [exact Hp |].
    by apply (npath_agree m m' r Hag p r i Hp (nreach_refl m r)).
Qed.

Lemma nclose_agree (m m' : gmap Z absnode) (r : Z) :
  (forall j, nreach m r j -> m !! j = m' !! j) -> nclose m r = nclose m' r.
Proof.
  intros Hag. apply map_eq. intros i.
  destruct (nclose m r !! i) as [n |] eqn:H1.
  - apply nclose_lookup_Some in H1 as [Hm Hr]. symmetry.
    apply nclose_lookup_Some. rewrite -(Hag i Hr).
    split; [exact Hm | by apply (nreach_agree m m' r Hag)].
  - symmetry. destruct (nclose m' r !! i) as [n |] eqn:H2; [| reflexivity].
    exfalso. apply nclose_lookup_Some in H2 as [Hm' Hr'].
    assert (Hr : nreach m r i) by (by apply (nreach_agree m m' r Hag)).
    rewrite (nclose_lookup_in m r i Hr) (Hag i Hr) Hm' in H1. discriminate.
Qed.

(* ---- THE SUBTREE ---------------------------------------------------- *)

(* the root must be a DIRECTORY of the view: an owner's root is a place
   names can hang from, not a file *)
Definition adir_at (av : aview) (r : Z) : Prop :=
  exists (a : anode) (e : gmap fname Z), av !! r = Some a /\ an_node a = ADir e.

Global Instance adir_at_dec (av : aview) (r : Z) : Decision (adir_at av r).
Proof.
  destruct (av !! r) as [a |] eqn:Ha; [| right; intros (b & e & Hb & _); congruence].
  destruct (an_node a) as [bs | e | ma mi] eqn:Hn.
  - right. intros (b & e & Hb & He). rewrite Ha in Hb. injection Hb as <-.
    rewrite Hn in He. discriminate.
  - left. by exists a, e.
  - right. intros (b & e & Hb & He). rewrite Ha in Hb. injection Hb as <-.
    rewrite Hn in He. discriminate.
Defined.

Lemma adir_at_tview (av : aview) (r : Z) :
  adir_at av r <-> exists e, tview av !! r = Some (ADir e).
Proof.
  split.
  - intros (a & e & Ha & He). exists (hide_dots e).
    rewrite (tview_lookup_Some _ _ _ Ha) /tnode_of He //.
  - intros (e & He). rewrite tview_lookup in He.
    destruct (av !! r) as [a |] eqn:Ha; [| discriminate].
    cbn in He. injection He as He. exists a.
    rewrite /tnode_of in He. destruct (an_node a) as [bs | e0 | ma mi] eqn:Hn;
      [discriminate | | discriminate].
    by exists e0.
Qed.

(* THE NODE MAP of the subtree at [r]: the projected view, cut down to
   what [r] reaches by proper names. *)
Definition subtree_nodes (av : aview) (r : Z) : gmap Z absnode :=
  nclose (tview av) r.

(* THE SUBTREE: [None] at a root that is not a directory of the view. *)
Definition subtree (av : aview) (r : Z) : option ttree :=
  match tview av !! r with
  | Some (ADir _) => Some (MkTTree (subtree_nodes av r) r)
  | _ => None
  end.

Lemma subtree_of_dir (av : aview) (r : Z) :
  adir_at av r -> subtree av r = Some (MkTTree (subtree_nodes av r) r).
Proof.
  intros Hd. apply adir_at_tview in Hd as (e & He). rewrite /subtree He //.
Qed.

Lemma subtree_None (av : aview) (r : Z) :
  ~ adir_at av r -> subtree av r = None.
Proof.
  intros Hd. rewrite /subtree.
  destruct (tview av !! r) as [n |] eqn:He; [| reflexivity].
  destruct n as [bs | e | ma mi]; [reflexivity | | reflexivity].
  exfalso. apply Hd, adir_at_tview. by exists e.
Qed.

Lemma subtree_Some_inv (av : aview) (r : Z) (t : ttree) :
  subtree av r = Some t ->
  adir_at av r /\ t = MkTTree (subtree_nodes av r) r.
Proof.
  rewrite /subtree. destruct (tview av !! r) as [n |] eqn:He; [| discriminate].
  destruct n as [bs | e | ma mi]; [discriminate | | discriminate].
  intros Ht. injection Ht as <-. split; [| reflexivity].
  apply adir_at_tview. by exists e.
Qed.

Lemma subtree_root (av : aview) (r : Z) (t : ttree) :
  subtree av r = Some t -> tv_root t = r.
Proof. intros Ht. by apply subtree_Some_inv in Ht as (_ & ->). Qed.

Lemma subtree_nodes_eq (av : aview) (r : Z) (t : ttree) :
  subtree av r = Some t -> tv_nodes t = subtree_nodes av r.
Proof. intros Ht. by apply subtree_Some_inv in Ht as (_ & ->). Qed.

(* THE CONGRUENCE that makes the whole of section 5 work: the subtree is
   a function of the PROJECTED view, so a delta that moves no node's
   content and no proper entry moves no subtree at all. *)
Lemma subtree_cong (av av' : aview) (r : Z) :
  tview av = tview av' -> subtree av r = subtree av' r.
Proof. intros Hv. rewrite /subtree /subtree_nodes Hv //. Qed.

(* the tree's nodes, read back against the view *)
Lemma subtree_nodes_lookup_Some (av : aview) (r i : Z) (n : absnode) :
  subtree_nodes av r !! i = Some n <->
  (exists a, av !! i = Some a /\ n = tnode_of a) /\ nreach (tview av) r i.
Proof.
  rewrite /subtree_nodes nclose_lookup_Some tview_lookup. split.
  - intros [Hm Hr]. split; [| exact Hr].
    destruct (av !! i) as [a |]; [| discriminate].
    cbn in Hm. injection Hm as <-. by exists a.
  - intros ((a & Ha & ->) & Hr). rewrite Ha. by split.
Qed.

Lemma subtree_nodes_lookup_of (av : aview) (r i : Z) (a : anode) :
  av !! i = Some a -> nreach (tview av) r i ->
  subtree_nodes av r !! i = Some (tnode_of a).
Proof.
  intros Ha Hr. apply subtree_nodes_lookup_Some. split; [by exists a | exact Hr].
Qed.

Lemma elem_of_dom_subtree_nodes (av : aview) (r i : Z) :
  i ∈ dom (subtree_nodes av r) <-> i ∈ dom av /\ nreach (tview av) r i.
Proof. rewrite /subtree_nodes elem_of_dom_nclose tview_dom //. Qed.

(* the walk in the view, and the walk in the projection, are one walk *)
Lemma nreach_tview (av : aview) (r i : Z) :
  nreach (tview av) r i <-> exists p, fs_proper p /\ apath_at av r p = Some i.
Proof.
  rewrite /nreach. split; intros (p & Hp & Hw); exists p; split; try exact Hp.
  - by rewrite -npath_tview.
  - by rewrite npath_tview.
Qed.

(* ===================================================================== *)
(*  4.  WELL-FORMEDNESS, NON-NESTING, AND SUBTREE DISJOINTNESS           *)
(* ===================================================================== *)

(* WHICH ACYCLICITY FACT.  [FsTree.fs_dirs_acyclic] is the landed one, and
   it is stated at the KERNEL tree ([fstree]); there is no [aview] twin --
   fs-syscall-specs.md section 6 item 2 promises one ("acyclicity /
   root-reachability are pure predicates of the held fragment") and
   nothing has minted it.  It is minted here for the record...  *)
Definition aview_dirs_acyclic (av : aview) : Prop :=
  forall (i : Z) (p : list fname),
    p <> [] -> fs_proper p -> apath_at av i p <> Some i.

(* ...and tied to the landed one by [FsAbsDefs.apath_at_tree], so the two
   are the same predicate read at the two trees (the root [r] the reading
   carries is irrelevant: [path_at] never looks at it). *)
Lemma aview_dirs_acyclic_tree (av : aview) (r : Z) :
  fs_dirs_acyclic (abs_tree av r) <-> aview_dirs_acyclic av.
Proof.
  rewrite /fs_dirs_acyclic /aview_dirs_acyclic.
  split; intros H i p Hne Hp; specialize (H i p Hne Hp);
    by rewrite ?apath_at_tree -?apath_at_tree in H |- *.
Qed.

(* BUT ACYCLICITY IS NOT WHAT DISJOINTNESS NEEDS, and saying so is half of
   this section's content.  Two subtrees can be node-disjoint in a cyclic
   graph and can OVERLAP in an acyclic one (a diamond: one file hard-linked
   under two unrelated directories is acyclic and shared).  What rules the
   diamond out is UNIQUE PARENTHOOD -- "no hard links" -- and nothing else;
   acyclicity is never used below. *)

Definition nis_dir (m : gmap Z absnode) (i : Z) : Prop :=
  exists e, m !! i = Some (ADir e).

Lemma nstep_dir (m : gmap Z absnode) (d : Z) (s : fname) (c : Z) :
  nstep m d s = Some c -> nis_dir m d.
Proof.
  rewrite /nstep /nents. destruct (m !! d) as [n |] eqn:Hd; [| discriminate].
  destruct n as [bs | e | ma mi]; [discriminate | | discriminate].
  intros _. by exists e.
Qed.

(* EVERY NODE HAS AT MOST ONE PROPER IN-EDGE: the namespace is a forest.
   In xv6 this is true of DIRECTORIES by construction (link refuses a
   directory, and there is no rename), and it is what the tree
   application DECLARES of its files as well -- see [ndirs_tree] below for
   the weaker fact that holds unconditionally, and the header note on
   sys_link. *)
Definition nuniq_parent (m : gmap Z absnode) : Prop :=
  forall (d1 : Z) (s1 : fname) (d2 : Z) (s2 : fname) (j : Z),
    fs_pname s1 -> fs_pname s2 ->
    nstep m d1 s1 = Some j -> nstep m d2 s2 = Some j -> d1 = d2 /\ s1 = s2.

(* the same, restricted to directory targets: xv6's OWN invariant *)
Definition ndirs_tree (m : gmap Z absnode) : Prop :=
  forall (d1 : Z) (s1 : fname) (d2 : Z) (s2 : fname) (j : Z),
    nis_dir m j -> fs_pname s1 -> fs_pname s2 ->
    nstep m d1 s1 = Some j -> nstep m d2 s2 = Some j -> d1 = d2 /\ s1 = s2.

Lemma nuniq_parent_dirs_tree (m : gmap Z absnode) :
  nuniq_parent m -> ndirs_tree m.
Proof. intros Hu d1 s1 d2 s2 j _ Hs1 Hs2 H1 H2. exact (Hu _ _ _ _ _ Hs1 Hs2 H1 H2). Qed.

Lemma list_snoc_inv {A : Type} (p : list A) :
  p = [] \/ exists (q : list A) (s : A), p = q ++ [s].
Proof. induction p using rev_ind; [by left | right; by exists p, x]. Qed.

(* THE CORE: a node two roots both reach forces one root to reach the
   other.  [P] is the class of nodes whose parent is unique -- every node
   ([nuniq_parent]) or every directory ([ndirs_tree]) -- and the second
   premise is what lets the induction strip a hop: the SOURCE of an edge
   is in the class too. *)
Lemma nreach_common_gen (m : gmap Z absnode) (P : Z -> Prop) (r r' i : Z) :
  (forall d1 s1 d2 s2 j, P j -> fs_pname s1 -> fs_pname s2 ->
     nstep m d1 s1 = Some j -> nstep m d2 s2 = Some j -> d1 = d2 /\ s1 = s2) ->
  (forall d s c, nstep m d s = Some c -> P d) ->
  P i -> nreach m r i -> nreach m r' i ->
  nreach m r r' \/ nreach m r' r.
Proof.
  intros Huniq Hsrc Hi (p & Hp & Hw) (p' & Hp' & Hw').
  remember (length p) as n eqn:Hn.
  revert r r' i p p' Hi Hp Hp' Hw Hw' Hn.
  induction n as [n IH] using lt_wf_ind; intros r r' i p p' Hi Hp Hp' Hw Hw' Hn.
  destruct (list_snoc_inv p) as [-> | (q & s & ->)].
  { cbn in Hw. injection Hw as <-. right. by exists p'. }
  destruct (list_snoc_inv p') as [-> | (q' & s' & ->)].
  { cbn in Hw'. injection Hw' as <-. left. by exists (q ++ [s]). }
  apply fs_proper_app in Hp as [Hq Hs].
  apply fs_proper_cons in Hs as [Hs _].
  apply fs_proper_app in Hp' as [Hq' Hs'].
  apply fs_proper_cons in Hs' as [Hs' _].
  rewrite npath_snoc in Hw. destruct (npath m r q) as [d |] eqn:Hd; [| discriminate].
  rewrite npath_snoc in Hw'. destruct (npath m r' q') as [d' |] eqn:Hd'; [| discriminate].
  destruct (Huniq d s d' s' i Hi Hs Hs' Hw Hw') as [<- _].
  eapply (IH (length q)); [| exact (Hsrc d s i Hw) | exact Hq | exact Hq'
                          | exact Hd | exact Hd' | reflexivity].
  rewrite Hn length_app /=. lia.
Qed.

(* the two instances *)
Lemma nreach_common (m : gmap Z absnode) (r r' i : Z) :
  nuniq_parent m -> nreach m r i -> nreach m r' i ->
  nreach m r r' \/ nreach m r' r.
Proof.
  intros Hu. apply (nreach_common_gen m (fun _ => True) r r' i);
    [| done | done].
  intros d1 s1 d2 s2 j _ Hs1 Hs2 H1 H2. exact (Hu _ _ _ _ _ Hs1 Hs2 H1 H2).
Qed.

(* WITHOUT the no-hard-links declaration, this is all that survives -- and
   it is exactly the honest statement: a node two unrelated owners both
   reach is a FILE with two links, never a directory. *)
Lemma nreach_common_dir (m : gmap Z absnode) (r r' i : Z) :
  ndirs_tree m -> nis_dir m i -> nreach m r i -> nreach m r' i ->
  nreach m r r' \/ nreach m r' r.
Proof.
  intros Hd Hi. apply (nreach_common_gen m (nis_dir m) r r' i);
    [| intros d s c Hst; exact (nstep_dir m d s c Hst) | exact Hi].
  intros d1 s1 d2 s2 j Hj Hs1 Hs2 H1 H2. exact (Hd _ _ _ _ _ Hj Hs1 Hs2 H1 H2).
Qed.

(* ---- 4b.  THE OWNERSHIP MAP ---------------------------------------- *)

(* ENTRIES ARE NEVER DANGLING: a name in a directory names a node the view
   has.  True of xv6 at every quiescent instant (create arms the child
   BEFORE linking it; unlink removes the name BEFORE the row) and it is
   what makes a fresh inum unreachable -- create's arm is invisible to
   every subtree because nothing points at the new inum yet. *)
Definition aview_closed (av : aview) : Prop :=
  forall (d : Z) (s : fname) (j : Z),
    fs_pname s -> astep av d s = Some j -> is_Some (av !! j).

Definition aview_uniq_parent (av : aview) : Prop := nuniq_parent (tview av).

(* ...spelled in the view's own vocabulary *)
Lemma aview_uniq_parent_astep (av : aview) :
  aview_uniq_parent av <->
  (forall d1 s1 d2 s2 j, fs_pname s1 -> fs_pname s2 ->
     astep av d1 s1 = Some j -> astep av d2 s2 = Some j -> d1 = d2 /\ s1 = s2).
Proof.
  rewrite /aview_uniq_parent /nuniq_parent.
  split; intros Hh d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
  - apply (Hh d1 s1 d2 s2 j Hs1 Hs2);
      [rewrite (nstep_tview av d1 s1 Hs1) | rewrite (nstep_tview av d2 s2 Hs2)];
      assumption.
  - apply (Hh d1 s1 d2 s2 j Hs1 Hs2);
      [rewrite -(nstep_tview av d1 s1 Hs1) | rewrite -(nstep_tview av d2 s2 Hs2)];
      assumption.
Qed.

Lemma aview_closed_nreach (av : aview) (r i : Z) :
  aview_closed av -> nreach (tview av) r i -> i = r \/ i ∈ dom av.
Proof.
  intros Hc (p & Hp & Hw). destruct (list_snoc_inv p) as [-> | (q & s & ->)].
  { cbn in Hw. injection Hw as <-. by left. }
  right. apply fs_proper_app in Hp as [_ Hs].
  apply fs_proper_cons in Hs as [Hs _].
  rewrite npath_snoc in Hw. destruct (npath (tview av) r q) as [d |]; [| discriminate].
  rewrite (nstep_tview av d s Hs) in Hw.
  apply elem_of_dom. exact (Hc d s i Hs Hw).
Qed.

(* THE TREE-SHAPE the application declares of the view and every step
   preserves (section 7).  Both conjuncts are facts about the LIVE
   namespace, not about any ghost. *)
Definition aview_tree_wf (av : aview) : Prop :=
  aview_uniq_parent av /\ aview_closed av.

Section Own.
  (* the ownership map of user-tree.md section 2: a generation [g] owns
     the subtree [t] at [root].  The key type is a parameter -- TL-2's is
     the generation id -- because nothing here reads it. *)
  Context {K : Type} `{Countable K}.

  Definition own_wf (av : aview) (own : gmap K (Z * ttree)) : Prop :=
    aview_tree_wf av
    (* every root is a directory of the view *)
    /\ (forall g r t, own !! g = Some (r, t) -> adir_at av r)
    (* ...and no root reaches another: the roots are pairwise NON-NESTED *)
    /\ (forall g g' r t r' t', g <> g' ->
          own !! g = Some (r, t) -> own !! g' = Some (r', t') ->
          ~ nreach (tview av) r r').

  (* THE THEOREM: two owners' subtrees share no node. *)
  Lemma subtree_disjoint (av : aview) (own : gmap K (Z * ttree))
      (g g' : K) (r r' : Z) (t t' : ttree) :
    own_wf av own -> g <> g' ->
    own !! g = Some (r, t) -> own !! g' = Some (r', t') ->
    dom (subtree_nodes av r) ## dom (subtree_nodes av r').
  Proof using .
    intros ((Hu & _) & _ & Hnn) Hne Hg Hg' i Hi Hi'.
    apply elem_of_dom_subtree_nodes in Hi as (_ & Hr).
    apply elem_of_dom_subtree_nodes in Hi' as (_ & Hr').
    destruct (nreach_common (tview av) r r' i Hu Hr Hr') as [Hc | Hc].
    - exact (Hnn g g' r t r' t' Hne Hg Hg' Hc).
    - exact (Hnn g' g r' t' r t (fun Hx => Hne (eq_sym Hx)) Hg' Hg Hc).
  Qed.

  (* ...and the same at the trees the claim actually names *)
  Lemma subtree_disjoint_trees (av : aview) (own : gmap K (Z * ttree))
      (g g' : K) (r r' : Z) (t t' : ttree) :
    own_wf av own -> g <> g' ->
    own !! g = Some (r, t) -> own !! g' = Some (r', t') ->
    subtree av r = Some t -> subtree av r' = Some t' ->
    dom (tv_nodes t) ## dom (tv_nodes t').
  Proof using .
    intros Hwf Hne Hg Hg' Ht Ht'.
    rewrite (subtree_nodes_eq av r t Ht) (subtree_nodes_eq av r' t' Ht').
    exact (subtree_disjoint av own g g' r r' t t' Hwf Hne Hg Hg').
  Qed.
End Own.

(* ===================================================================== *)
(*  5.  THE DELTA LEMMAS                                                  *)
(* ===================================================================== *)

(* ---- 5a.  THE TOOLKIT ---------------------------------------------- *)

(* the children of [d] the map may or may not have -- [nkids] without the
   presence filter.  It exists for ONE reason: to decide [nreach] at an
   inum the map lacks (a DANGLING entry names a node no subtree holds, but
   the walk still answers with its inum). *)
Definition nkids_all (m : gmap Z absnode) (d : Z) : gset Z :=
  match nents m d with Some e => map_img (hide_dots e) | None => ∅ end.

Lemma nkids_eq (m : gmap Z absnode) (d : Z) : nkids m d = nkids_all m d ∩ dom m.
Proof. reflexivity. Qed.

Lemma elem_of_nkids_all (m : gmap Z absnode) (d i : Z) :
  i ∈ nkids_all m d <-> exists s, fs_pname s /\ nstep m d s = Some i.
Proof.
  rewrite /nkids_all /nstep. destruct (nents m d) as [e |]; cbn.
  - rewrite elem_of_map_img. split.
    + intros (s & Hs). destruct (hide_dots_lookup_Some e s i Hs) as [Hp He].
      by exists s.
    + intros (s & Hp & He). exists s. rewrite hide_dots_lookup //.
  - rewrite elem_of_empty. split; [done | intros (s & _ & Hc); discriminate].
Qed.

Definition nreach_set_ext (m : gmap Z absnode) (r : Z) : gset Z :=
  nreach_set m r ∪ ⋃ ((nkids_all m) <$> elements (nreach_set m r)).

Lemma elem_of_nreach_set_ext (m : gmap Z absnode) (r i : Z) :
  i ∈ nreach_set_ext m r <-> nreach m r i.
Proof.
  rewrite /nreach_set_ext elem_of_union elem_of_union_list. split.
  - intros [Hi | (X & HX & Hi)].
    + by apply elem_of_nreach_set in Hi as [? _].
    + apply list_elem_of_fmap in HX as (d & -> & Hd).
      apply elem_of_elements, elem_of_nreach_set in Hd as [Hrd _].
      apply elem_of_nkids_all in Hi as (s & Hs & Hst).
      exact (nreach_hop m r d s i Hrd Hs Hst).
  - intros Hr. destruct (decide (i ∈ nreach_set m r)) as [Hi | Hi]; [by left |].
    right. destruct Hr as (p & Hp & Hw).
    destruct (list_snoc_inv p) as [-> | (q & s & ->)].
    { exfalso. cbn in Hw. injection Hw as <-. apply Hi, elem_of_nreach_set.
      split; [apply nreach_refl | by left]. }
    apply fs_proper_app in Hp as [Hq Hs].
    apply fs_proper_cons in Hs as [Hs _].
    rewrite npath_snoc in Hw.
    destruct (npath m r q) as [d |] eqn:Hd; [| discriminate].
    exists (nkids_all m d). split.
    + apply list_elem_of_fmap. exists d. split; [reflexivity |].
      apply elem_of_elements, elem_of_nreach_set. split.
      * by exists q.
      * right. exact (nstep_dom m d s i Hw).
    + apply elem_of_nkids_all. by exists s.
Qed.

Global Instance nreach_dec (m : gmap Z absnode) (r i : Z) : Decision (nreach m r i).
Proof.
  refine (cast_if (decide (i ∈ nreach_set_ext m r)));
    by rewrite -elem_of_nreach_set_ext.
Defined.

(* THE CLOSURE INDUCTION: a property of the root that survives every
   proper edge holds at every node the root reaches.  Every "the delta
   adds no reach" argument below is this lemma. *)
Lemma nreach_closed_ind (m : gmap Z absnode) (r : Z) (Q : Z -> Prop) :
  Q r ->
  (forall d s c, Q d -> fs_pname s -> nstep m d s = Some c -> Q c) ->
  forall i, nreach m r i -> Q i.
Proof.
  intros Hr Hstep i (p & Hp & Hw). revert r Hr Hp Hw.
  induction p as [| s p IH]; intros d Hd Hp Hw.
  { cbn in Hw. by injection Hw as <-. }
  apply fs_proper_cons in Hp as [Hs Hp].
  rewrite npath_cons in Hw. destruct (nstep m d s) as [c |] eqn:Hst; [| discriminate].
  exact (IH c (Hstep d s c Hd Hs Hst) Hp Hw).
Qed.

(* ...and its mirror: a map with FEWER edges reaches fewer nodes *)
Lemma nreach_mono_edges (m1 m2 : gmap Z absnode) (r : Z) :
  (forall j s c, fs_pname s -> nstep m1 j s = Some c -> nstep m2 j s = Some c) ->
  forall i, nreach m1 r i -> nreach m2 r i.
Proof.
  intros Hsub i. apply (nreach_closed_ind m1 r (nreach m2 r) (nreach_refl m2 r)).
  intros d s c Hd Hs Hst. exact (nreach_hop m2 r d s c Hd Hs (Hsub d s c Hs Hst)).
Qed.

(* THE LOCALITY LAW: an edit that only reads and writes nodes inside the
   closure may be applied to the CLOSURE instead of to the whole map.
   This is what lets a tree op be an op on the OWNER'S TREE rather than on
   the view -- the point of the whole layer. *)
Lemma nclose_op_local (op : gmap Z absnode -> gmap Z absnode)
    (m : gmap Z absnode) (r : Z) (Q : Z -> Prop) :
  (forall j, nreach (op m) r j -> nreach m r j \/ Q j) ->
  (forall j, nreach m r j \/ Q j -> op m !! j = op (nclose m r) !! j) ->
  nclose (op m) r = nclose (op (nclose m r)) r.
Proof. intros H1 H2. apply nclose_agree. intros j Hj. exact (H2 j (H1 j Hj)). Qed.

(* ---- 5b.  THE EDGE EDITS ON A NODE MAP ----------------------------- *)

Definition tedge_ins (d : Z) (nm : fname) (i : Z)
    (m : gmap Z absnode) : gmap Z absnode :=
  match m !! d with
  | Some (ADir e) => <[d := ADir (<[nm := i]> e)]> m
  | _ => m
  end.

Definition tedge_del (d : Z) (nm : fname) (m : gmap Z absnode) : gmap Z absnode :=
  match m !! d with
  | Some (ADir e) => <[d := ADir (delete nm e)]> m
  | _ => m
  end.

Lemma tedge_ins_lookup_ne (m : gmap Z absnode) (d : Z) (nm : fname) (i j : Z) :
  j <> d -> tedge_ins d nm i m !! j = m !! j.
Proof.
  intros Hj. rewrite /tedge_ins. destruct (m !! d) as [n |]; [| done].
  destruct n; [done | | done]. rewrite lookup_insert_ne //.
Qed.

Lemma tedge_ins_lookup_at (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) :
  m !! d = Some (ADir e) ->
  tedge_ins d nm i m !! d = Some (ADir (<[nm := i]> e)).
Proof. intros Hd. rewrite /tedge_ins Hd lookup_insert_eq //. Qed.

Lemma tedge_del_lookup_ne (m : gmap Z absnode) (d : Z) (nm : fname) (j : Z) :
  j <> d -> tedge_del d nm m !! j = m !! j.
Proof.
  intros Hj. rewrite /tedge_del. destruct (m !! d) as [n |]; [| done].
  destruct n; [done | | done]. rewrite lookup_insert_ne //.
Qed.

Lemma tedge_del_lookup_at (m : gmap Z absnode) (d : Z) (nm : fname)
    (e : gmap fname Z) :
  m !! d = Some (ADir e) ->
  tedge_del d nm m !! d = Some (ADir (delete nm e)).
Proof. intros Hd. rewrite /tedge_del Hd lookup_insert_eq //. Qed.

(* the edits are CONGRUENCES: they read only the edited node's row *)
Lemma tedge_del_cong (m1 m2 : gmap Z absnode) (d : Z) (nm : fname) (j : Z) :
  m1 !! d = m2 !! d -> m1 !! j = m2 !! j ->
  tedge_del d nm m1 !! j = tedge_del d nm m2 !! j.
Proof.
  intros Hd Hj. rewrite /tedge_del -Hd.
  destruct (m1 !! d) as [n |]; [| exact Hj].
  destruct n as [bs | e | ma mi]; [exact Hj | | exact Hj].
  destruct (decide (j = d)) as [-> | Hne];
    [rewrite !lookup_insert_eq // | rewrite !lookup_insert_ne //].
Qed.

Lemma tedge_ins_cong (m1 m2 : gmap Z absnode) (d : Z) (nm : fname) (i j : Z) :
  m1 !! d = m2 !! d -> m1 !! j = m2 !! j ->
  tedge_ins d nm i m1 !! j = tedge_ins d nm i m2 !! j.
Proof.
  intros Hd Hj. rewrite /tedge_ins -Hd.
  destruct (m1 !! d) as [n |]; [| exact Hj].
  destruct n as [bs | e | ma mi]; [exact Hj | | exact Hj].
  destruct (decide (j = d)) as [-> | Hne];
    [rewrite !lookup_insert_eq // | rewrite !lookup_insert_ne //].
Qed.

Lemma nstep_of_lookup (m m' : gmap Z absnode) (j : Z) (s : fname) :
  m !! j = m' !! j -> nstep m j s = nstep m' j s.
Proof. exact (nstep_agree m m' j s). Qed.

Lemma nstep_tedge_ins_at (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (s : fname) :
  m !! d = Some (ADir e) ->
  nstep (tedge_ins d nm i m) d s
  = (if decide (s = nm) then Some i else nstep m d s).
Proof.
  intros Hd. rewrite /nstep /nents (tedge_ins_lookup_at m d nm i e Hd) Hd /=.
  case_decide as Hs; [subst s; rewrite lookup_insert_eq // | rewrite lookup_insert_ne //].
Qed.

Lemma nstep_tedge_del_at (m : gmap Z absnode) (d : Z) (nm : fname)
    (e : gmap fname Z) (s : fname) :
  m !! d = Some (ADir e) ->
  nstep (tedge_del d nm m) d s
  = (if decide (s = nm) then None else nstep m d s).
Proof.
  intros Hd. rewrite /nstep /nents (tedge_del_lookup_at m d nm e Hd) Hd /=.
  case_decide as Hs; [subst s; rewrite lookup_delete_eq // | rewrite lookup_delete_ne //].
Qed.

(* the deleting edit never adds an edge: [nreach] can only shrink *)
Lemma nstep_tedge_del_sub (m : gmap Z absnode) (d : Z) (nm : fname)
    (j : Z) (s : fname) (c : Z) :
  nstep (tedge_del d nm m) j s = Some c -> nstep m j s = Some c.
Proof.
  intros H. destruct (decide (j = d)) as [-> | Hj]; last first.
  { rewrite -(nstep_of_lookup (tedge_del d nm m) m j s
                (tedge_del_lookup_ne m d nm j Hj)). exact H. }
  destruct (m !! d) as [n |] eqn:Hd; [| rewrite /tedge_del Hd /= in H; exact H].
  destruct n as [bs | e | ma mi];
    [rewrite /tedge_del Hd /= in H; exact H | | rewrite /tedge_del Hd /= in H; exact H].
  rewrite (nstep_tedge_del_at m d nm e s Hd) in H.
  case_decide as Hs; [discriminate | exact H].
Qed.

(* ---- 5c.  THE PROJECTED VIEW UNDER EACH LANDED LEG ------------------ *)

Lemma tview_insert (av : aview) (i : Z) (a : anode) :
  tview (<[i := a]> av) = <[i := tnode_of a]> (tview av).
Proof. rewrite /tview fmap_insert //. Qed.

Lemma tview_delete (av : aview) (i : Z) :
  tview (delete i av) = delete i (tview av).
Proof. rewrite /tview fmap_delete //. Qed.

(* the row-wise transfer: a leg that leaves a row alone leaves the
   projected row alone *)
Lemma tview_lookup_ne_of (av av' : aview) (j : Z) :
  av' !! j = av !! j -> tview av' !! j = tview av !! j.
Proof. intros Hj. rewrite !tview_lookup Hj //. Qed.

(* THE DOTS ARE INVISIBLE (both of mkdir's interior legs) *)
Lemma tview_delta_dots (av : aview) (i d : Z) :
  tview (delta_dots i d av) = tview av.
Proof.
  rewrite /delta_dots. destruct (av !! i) as [a |] eqn:Ha; [| reflexivity].
  destruct (an_node a) as [bs | e | ma mi] eqn:Hn; [reflexivity | | reflexivity].
  rewrite tview_insert. apply insert_id.
  rewrite (tview_lookup_Some _ _ _ Ha) /tnode_of /tabs_of /= Hn.
  by rewrite hide_dots_insert_dots.
Qed.

Lemma tview_delta_dot (av : aview) (i : Z) :
  tview (delta_dot i av) = tview av.
Proof.
  rewrite /delta_dot. destruct (av !! i) as [a |] eqn:Ha; [| reflexivity].
  destruct (an_node a) as [bs | e | ma mi] eqn:Hn; [reflexivity | | reflexivity].
  rewrite tview_insert. apply insert_id.
  rewrite (tview_lookup_Some _ _ _ Ha) /tnode_of /tabs_of /= Hn.
  by rewrite hide_dots_insert_dot.
Qed.

(* A COUNT BUMP AT A ROW THE VIEW HAS IS INVISIBLE (link's target leg).
   At a row the view does NOT have, the leg RESURRECTS an unlinked-but-open
   node -- see the header's note; that arm is excluded by the premise. *)
Lemma tview_delta_link_tgt (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> tview (delta_link_tgt t a av) = tview av.
Proof.
  intros Ha. rewrite /delta_link_tgt tview_insert. apply insert_id.
  rewrite (tview_lookup_Some _ _ _ Ha) /tnode_of //.
Qed.

(* ...and so is a count DROP that does not reach zero (unlink's target leg
   at a file with another link) *)
Lemma tview_delta_unl_tgt_live (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> (2 <= an_nlink a)%nat ->
  tview (delta_unl_tgt t av) = tview av.
Proof.
  intros Ha Hnl. rewrite (delta_unl_tgt_unfold av t a Ha).
  case_decide as Hz; [lia |]. rewrite tview_insert. apply insert_id.
  rewrite (tview_lookup_Some _ _ _ Ha) /tnode_of //.
Qed.

Lemma tview_delta_unl_tgt_last (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> an_nlink a = 1%nat ->
  tview (delta_unl_tgt t av) = delete t (tview av).
Proof.
  intros Ha Hnl. rewrite (delta_unl_tgt_unfold av t a Ha).
  case_decide as Hz; [by rewrite tview_delete | lia].
Qed.

Lemma tview_delta_arm (av : aview) (i : Z) (c : absnode) :
  tview (delta_arm i c av) = <[i := tabs_of c]> (tview av).
Proof. rewrite /delta_arm tview_insert //. Qed.

Lemma tview_delta_unarm (av : aview) (i : Z) :
  tview (delta_unarm i av) = delete i (tview av).
Proof. rewrite /delta_unarm tview_delete //. Qed.

Lemma tview_delta_write (av : aview) (i : Z) (off : nat) (new bs0 : list (bv 8))
    (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  tview (delta_write i off new av)
  = <[i := AFile (blk_splice off new bs0)]> (tview av).
Proof.
  intros Hi. rewrite (delta_write_file av i off new bs0 nl Hi) tview_insert //.
Qed.

Lemma tview_delta_trunc (av : aview) (i : Z) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  tview (delta_trunc i av) = <[i := AFile []]> (tview av).
Proof.
  intros Hi. rewrite (delta_trunc_file av i bs0 nl Hi) tview_insert //.
Qed.

(* THE PARENT LEGS ARE EDGE INSERTS, at a PROPER name (a leg at a dot is
   invisible, which is [tview_delta_dots] again) *)
Lemma tview_delta_ent (av : aview) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (nl : nat) (a : anode) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> av !! i = Some a ->
  tview (delta_ent d nm i av) = tedge_ins d nm i (tview av).
Proof.
  intros Hnm Hd Hi.
  rewrite (delta_ent_dir av d nm i e nl (an_node a) (an_nlink a) Hd);
    [| by destruct a].
  rewrite tview_insert /tnode_of /tabs_of /= hide_dots_insert; [| exact Hnm].
  rewrite /tedge_ins (tview_lookup_Some av d _ Hd) /tnode_of /tabs_of /= //.
Qed.

Lemma tview_delta_link_ent (av : aview) (d : Z) (nm : fname) (t : Z)
    (e : gmap fname Z) (nl : nat) :
  fs_pname nm -> av !! d = Some (MkAnode (ADir e) nl) ->
  tview (delta_link_ent d nm t av) = tedge_ins d nm t (tview av).
Proof.
  intros Hnm Hd. rewrite (delta_link_ent_dir av d nm t e nl Hd).
  rewrite tview_insert /tnode_of /tabs_of /= hide_dots_insert; [| exact Hnm].
  rewrite /tedge_ins (tview_lookup_Some av d _ Hd) /tnode_of /tabs_of /= //.
Qed.

Lemma tview_delta_unl_ent (av : aview) (d : Z) (nm : fname) (dec : nat)
    (e : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir e) nl) ->
  tview (delta_unl_ent d nm dec av) = tedge_del d nm (tview av).
Proof.
  intros Hd. rewrite /delta_unl_ent Hd /=.
  rewrite tview_insert /tnode_of /tabs_of /= hide_dots_delete.
  rewrite /tedge_del (tview_lookup_Some av d _ Hd) /tnode_of /tabs_of /= //.
Qed.

(* ---- 5d.  OUTSIDE: A DELTA THE OWNER DOES NOT REACH MOVES NOTHING --- *)

Lemma subtree_out (av av' : aview) (r : Z) :
  (forall j, nreach (tview av) r j -> tview av' !! j = tview av !! j) ->
  subtree av' r = subtree av r.
Proof.
  intros Hag.
  assert (Hr : tview av' !! r = tview av !! r)
    by exact (Hag r (nreach_refl (tview av) r)).
  rewrite /subtree /subtree_nodes Hr.
  destruct (tview av !! r) as [n |]; [| reflexivity].
  destruct n as [bs | e | ma mi]; [reflexivity | | reflexivity].
  rewrite (nclose_agree (tview av) (tview av') r
             (fun j Hj => eq_sym (Hag j Hj))) //.
Qed.

(* the shape every leg instantiates: the leg moves ONE row, and the owner
   does not reach it *)
Lemma subtree_out_row (av av' : aview) (r i : Z) :
  (forall j, j <> i -> av' !! j = av !! j) ->
  ~ nreach (tview av) r i ->
  subtree av' r = subtree av r.
Proof.
  intros Hne Hi. apply subtree_out. intros j Hj.
  apply tview_lookup_ne_of, Hne. intros ->. exact (Hi Hj).
Qed.

(* A FRESH INUM IS UNREACHABLE -- provided no entry dangles (create's arm
   is invisible to every subtree, which is why the fired legs commute with
   the claim in any order). *)
Lemma nreach_fresh (av : aview) (r i : Z) :
  aview_closed av -> av !! i = None -> i <> r -> ~ nreach (tview av) r i.
Proof.
  intros Hc Hi Hne Hr.
  destruct (aview_closed_nreach av r i Hc Hr) as [-> | Hd]; [done |].
  apply elem_of_dom in Hd as [a Ha]. congruence.
Qed.

(* ---- 5e.  THE CLOSURE UNDER ONE EDIT -------------------------------- *)

Definition nents_of (n : absnode) : option (gmap fname Z) :=
  match n with ADir e => Some e | _ => None end.

Lemma nents_unfold (m : gmap Z absnode) (d : Z) : nents m d = m !! d ≫= nents_of.
Proof. rewrite /nents /nents_of. destruct (m !! d) as [n |]; [by destruct n | done]. Qed.

(* two maps with the same out-edges have the same walks, whatever their
   nodes' CONTENT says *)
Lemma npath_nents_cong (m m' : gmap Z absnode) (d : Z) (ps : list fname) :
  (forall j, nents m j = nents m' j) -> npath m d ps = npath m' d ps.
Proof.
  intros He. revert d. induction ps as [| s ps IH]; intros d; [reflexivity |].
  rewrite !npath_cons /nstep He.
  destruct (nents m' d ≫= (fun e => e !! s)) as [c |]; [apply IH | reflexivity].
Qed.

Lemma nreach_nents_cong (m m' : gmap Z absnode) (r i : Z) :
  (forall j, nents m j = nents m' j) -> nreach m r i <-> nreach m' r i.
Proof.
  intros He. split; intros (p & Hp & Hw); exists p; split; try exact Hp.
  - by rewrite -(npath_nents_cong m m' r p He).
  - by rewrite (npath_nents_cong m m' r p He).
Qed.

(* (1) A CONTENT EDIT at a node the owner reaches: the tree's node moves,
   the shape of the tree does not.  write and trunc are this. *)
Lemma nclose_content_edit (m : gmap Z absnode) (r i : Z) (c c0 : absnode) :
  m !! i = Some c0 -> nents_of c = nents_of c0 -> nreach m r i ->
  nclose (<[i := c]> m) r = <[i := c]> (nclose m r).
Proof.
  intros Hi Hc Hr.
  assert (He : forall j, nents m j = nents (<[i := c]> m) j).
  { intros j. rewrite !nents_unfold.
    destruct (decide (j = i)) as [-> | Hj]; [| by rewrite lookup_insert_ne].
    rewrite lookup_insert_eq Hi /= Hc //. }
  apply map_eq. intros j. destruct (decide (nreach m r j)) as [Hj | Hj].
  - rewrite (nclose_lookup_in _ r j); last first.
    { by apply (nreach_nents_cong m (<[i := c]> m) r j He). }
    destruct (decide (j = i)) as [-> | Hne].
    + rewrite !lookup_insert_eq //.
    + rewrite !lookup_insert_ne // (nclose_lookup_in m r j Hj) //.
  - rewrite (nclose_lookup_out _ r j); last first.
    { intros Hc'. apply Hj. by apply (nreach_nents_cong m (<[i := c]> m) r j He). }
    destruct (decide (j = i)) as [-> | Hne]; [done |].
    rewrite lookup_insert_ne // (nclose_lookup_out m r j Hj) //.
Qed.

(* a node with no proper entries: create's fresh child (a file, a device,
   or a directory holding only its dots) *)
Definition tabs_leaf (c : absnode) : Prop :=
  forall e : gmap fname Z, c = ADir e -> hide_dots e = ∅.

Lemma nstep_leaf (m : gmap Z absnode) (i : Z) (c : absnode) (s : fname) :
  m !! i = Some c -> tabs_leaf c -> fs_pname s -> nstep m i s = None.
Proof.
  intros Hi Hl Hs. rewrite /nstep nents_unfold Hi /=.
  destruct c as [bs | e | ma mi]; [reflexivity | | reflexivity].
  cbn. rewrite -(hide_dots_lookup e s Hs) (Hl e eq_refl) lookup_empty //.
Qed.

(* (2) THE EDGE INSERT at a node the owner reaches, with the target
   ALREADY in the subtree: link's parent leg.  Nothing new becomes
   reachable, so the tree op does not re-close. *)
Lemma nclose_tedge_ins_in (m : gmap Z absnode) (r d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) :
  fs_pname nm -> m !! d = Some (ADir e) -> e !! nm = None ->
  nreach m r d -> nreach m r i ->
  nclose (tedge_ins d nm i m) r = tedge_ins d nm i (nclose m r).
Proof.
  intros Hnm Hd Hnone Hrd Hri.
  set (m' := tedge_ins d nm i m).
  assert (Hstep : forall j s c, nstep m' j s = Some c ->
                   nstep m j s = Some c \/ (j = d /\ c = i)).
  { intros j s c. destruct (decide (j = d)) as [-> | Hj]; last first.
    { rewrite (nstep_of_lookup m' m j s (tedge_ins_lookup_ne m d nm i j Hj)).
      by left. }
    rewrite /m' (nstep_tedge_ins_at m d nm i e s Hd). case_decide as Hs.
    - intros Hc. injection Hc as <-. right. by split.
    - by left. }
  assert (Hin : forall j, nreach m' r j -> nreach m r j).
  { apply (nreach_closed_ind m' r (nreach m r) (nreach_refl m r)).
    intros d0 s c Hd0 Hs Hst. destruct (Hstep d0 s c Hst) as [Hc | [-> ->]].
    - exact (nreach_hop m r d0 s c Hd0 Hs Hc).
    - exact Hri. }
  assert (Hout : forall j, nreach m r j -> nreach m' r j).
  { apply (nreach_mono_edges m m' r). intros j s c Hs Hst.
    destruct (decide (j = d)) as [-> | Hj]; last first.
    { by rewrite (nstep_of_lookup m' m j s (tedge_ins_lookup_ne m d nm i j Hj)). }
    rewrite /m' (nstep_tedge_ins_at m d nm i e s Hd). case_decide as Hs'.
    - exfalso. subst s. rewrite /nstep nents_unfold Hd /= Hnone in Hst. discriminate.
    - exact Hst. }
  apply map_eq. intros j. destruct (decide (j = d)) as [-> | Hj].
  - rewrite (nclose_lookup_in m' r d (Hout d Hrd)) /m'.
    rewrite (tedge_ins_lookup_at m d nm i e Hd).
    rewrite (tedge_ins_lookup_at (nclose m r) d nm i e);
      [reflexivity | rewrite (nclose_lookup_in m r d Hrd) //].
  - rewrite (tedge_ins_lookup_ne (nclose m r) d nm i j Hj).
    destruct (decide (nreach m r j)) as [Hrj | Hrj].
    + rewrite (nclose_lookup_in m' r j (Hout j Hrj)) /m'.
      rewrite (tedge_ins_lookup_ne m d nm i j Hj) (nclose_lookup_in m r j Hrj) //.
    + rewrite (nclose_lookup_out m' r j); [| intros Hc; exact (Hrj (Hin j Hc))].
      rewrite (nclose_lookup_out m r j Hrj) //.
Qed.

(* (3) THE FRESH INSERT: create's child arm and parent leg together -- a
   new leaf appears under a directory the owner reaches. *)
Lemma nclose_tedge_ins_fresh (m : gmap Z absnode) (r d : Z) (nm : fname)
    (i : Z) (c : absnode) (e : gmap fname Z) :
  fs_pname nm -> m !! d = Some (ADir e) -> e !! nm = None ->
  nreach m r d -> m !! i = None -> tabs_leaf c ->
  nclose (tedge_ins d nm i (<[i := c]> m)) r
  = tedge_ins d nm i (<[i := c]> (nclose m r)).
Proof.
  intros Hnm Hd Hnone Hrd Hfresh Hleaf.
  assert (Hne : d <> i) by (intros ->; rewrite Hd in Hfresh; discriminate).
  set (m0 := <[i := c]> m).
  set (m' := tedge_ins d nm i m0).
  assert (Hd0 : m0 !! d = Some (ADir e)) by (rewrite /m0 lookup_insert_ne //).
  assert (Hstep : forall j s c0, fs_pname s -> nstep m' j s = Some c0 ->
                   nstep m j s = Some c0 \/ (j = d /\ c0 = i)).
  { intros j s c0 Hs. destruct (decide (j = d)) as [-> | Hj]; last first.
    { rewrite (nstep_of_lookup m' m0 j s (tedge_ins_lookup_ne m0 d nm i j Hj)).
      destruct (decide (j = i)) as [-> | Hji].
      - rewrite (nstep_leaf m0 i c s ltac:(rewrite /m0 lookup_insert_eq //) Hleaf Hs).
        intros Hc; discriminate.
      - rewrite (nstep_of_lookup m0 m j s ltac:(rewrite /m0 lookup_insert_ne //)).
        by left. }
    rewrite /m' (nstep_tedge_ins_at m0 d nm i e s Hd0). case_decide as Hs'.
    - intros Hc0. injection Hc0 as <-. right. by split.
    - rewrite (nstep_of_lookup m0 m d s ltac:(rewrite /m0 lookup_insert_ne //)).
      by left. }
  assert (Hin : forall j, nreach m' r j -> nreach m r j \/ j = i).
  { apply (nreach_closed_ind m' r (fun j => nreach m r j \/ j = i)
             (or_introl (nreach_refl m r))).
    intros d0 s c0 Hd0' Hs Hst. destruct (Hstep d0 s c0 Hs Hst) as [Hc | [-> ->]].
    - destruct Hd0' as [Hd0' | ->].
      + left. exact (nreach_hop m r d0 s c0 Hd0' Hs Hc).
      + exfalso. rewrite /nstep nents_unfold Hfresh /= in Hc. discriminate.
    - by right. }
  assert (Hout : forall j, nreach m r j -> nreach m' r j).
  { apply (nreach_mono_edges m m' r). intros j s c0 Hs Hst.
    destruct (decide (j = d)) as [-> | Hj]; last first.
    { rewrite (nstep_of_lookup m' m0 j s (tedge_ins_lookup_ne m0 d nm i j Hj)).
      destruct (decide (j = i)) as [-> | Hji].
      { exfalso. rewrite /nstep nents_unfold Hfresh /= in Hst. discriminate. }
      rewrite (nstep_of_lookup m0 m j s ltac:(rewrite /m0 lookup_insert_ne //)).
      exact Hst. }
    rewrite /m' (nstep_tedge_ins_at m0 d nm i e s Hd0). case_decide as Hs'.
    - exfalso. subst s. rewrite /nstep nents_unfold Hd /= Hnone in Hst. discriminate.
    - rewrite (nstep_of_lookup m0 m d s ltac:(rewrite /m0 lookup_insert_ne //)).
      exact Hst. }
  assert (Hri : nreach m' r i).
  { apply (nreach_hop m' r d nm i (Hout d Hrd) Hnm).
    rewrite /m' (nstep_tedge_ins_at m0 d nm i e nm Hd0).
    by rewrite (decide_True (P := nm = nm)). }
  apply map_eq. intros j. destruct (decide (j = d)) as [-> | Hj].
  - rewrite (nclose_lookup_in m' r d (Hout d Hrd)) /m'.
    rewrite (tedge_ins_lookup_at m0 d nm i e Hd0).
    rewrite (tedge_ins_lookup_at (<[i := c]> (nclose m r)) d nm i e);
      [reflexivity |].
    rewrite lookup_insert_ne; [| congruence].
    rewrite (nclose_lookup_in m r d Hrd) //.
  - rewrite (tedge_ins_lookup_ne (<[i := c]> (nclose m r)) d nm i j Hj).
    destruct (decide (j = i)) as [-> | Hji].
    + rewrite lookup_insert_eq (nclose_lookup_in m' r i Hri) /m'.
      rewrite (tedge_ins_lookup_ne m0 d nm i i ltac:(congruence)).
      rewrite /m0 lookup_insert_eq //.
    + rewrite lookup_insert_ne //.
      destruct (decide (nreach m r j)) as [Hrj | Hrj].
      * rewrite (nclose_lookup_in m' r j (Hout j Hrj)) /m'.
        rewrite (tedge_ins_lookup_ne m0 d nm i j Hj) /m0 lookup_insert_ne //.
        rewrite (nclose_lookup_in m r j Hrj) //.
      * rewrite (nclose_lookup_out m' r j);
          [| intros Hc0; destruct (Hin j Hc0) as [Hc1 | Hc1]; [exact (Hrj Hc1) | done]].
        rewrite (nclose_lookup_out m r j Hrj) //.
Qed.

(* (4) THE EDGE DELETE: unlink's parent leg.  This is the ONE op that can
   orphan nodes, so it is the one whose tree op RE-CLOSES. *)
Lemma nclose_tedge_del_in (m : gmap Z absnode) (r d : Z) (nm : fname) :
  nreach m r d ->
  nclose (tedge_del d nm m) r = nclose (tedge_del d nm (nclose m r)) r.
Proof.
  intros Hrd. apply (nclose_op_local (tedge_del d nm) m r (fun _ => False)).
  - intros j Hj. left.
    exact (nreach_mono_edges (tedge_del d nm m) m r
             (fun j0 s c _ H => nstep_tedge_del_sub m d nm j0 s c H) j Hj).
  - intros j [Hj | []]. apply tedge_del_cong.
    + exact (eq_sym (nclose_lookup_in m r d Hrd)).
    + exact (eq_sym (nclose_lookup_in m r j Hj)).
Qed.

(* ---- 5f.  THE TREE OPS, AND THE DELTA LEMMAS ------------------------ *)

(* THE FSCQ-STYLE OPS on the owner's own tree.  Only [top_unlink] closes:
   it is the only op that can orphan a node. *)
Definition top_write (i : Z) (off : nat) (new : list (bv 8)) (t : ttree) : ttree :=
  MkTTree (match tv_nodes t !! i with
           | Some (AFile bs) => <[i := AFile (blk_splice off new bs)]> (tv_nodes t)
           | _ => tv_nodes t
           end) (tv_root t).

Definition top_trunc (i : Z) (t : ttree) : ttree :=
  MkTTree (match tv_nodes t !! i with
           | Some (AFile _) => <[i := AFile []]> (tv_nodes t)
           | _ => tv_nodes t
           end) (tv_root t).

Definition top_link (d : Z) (nm : fname) (i : Z) (t : ttree) : ttree :=
  MkTTree (tedge_ins d nm i (tv_nodes t)) (tv_root t).

Definition top_ins (d : Z) (nm : fname) (i : Z) (c : absnode) (t : ttree) : ttree :=
  MkTTree (tedge_ins d nm i (<[i := c]> (tv_nodes t))) (tv_root t).

Definition top_unlink (d : Z) (nm : fname) (t : ttree) : ttree :=
  MkTTree (nclose (tedge_del d nm (tv_nodes t)) (tv_root t)) (tv_root t).

(* the three shapes every statement below closes with *)
Lemma subtree_eq_of (av : aview) (r : Z) (e : gmap fname Z) (m : gmap Z absnode) :
  tview av !! r = Some (ADir e) -> nclose (tview av) r = m ->
  subtree av r = Some (MkTTree m r).
Proof. intros H1 H2. rewrite /subtree /subtree_nodes H1 H2 //. Qed.

Lemma tedge_ins_dir (m : gmap Z absnode) (d : Z) (nm : fname) (i j : Z)
    (e : gmap fname Z) :
  m !! j = Some (ADir e) ->
  exists e', tedge_ins d nm i m !! j = Some (ADir e').
Proof.
  intros Hj. destruct (decide (j = d)) as [-> | Hne].
  - rewrite (tedge_ins_lookup_at m d nm i e Hj). by eexists.
  - rewrite (tedge_ins_lookup_ne m d nm i j Hne) Hj. by eexists.
Qed.

Lemma tedge_del_dir (m : gmap Z absnode) (d : Z) (nm : fname) (j : Z)
    (e : gmap fname Z) :
  m !! j = Some (ADir e) ->
  exists e', tedge_del d nm m !! j = Some (ADir e').
Proof.
  intros Hj. destruct (decide (j = d)) as [-> | Hne].
  - rewrite (tedge_del_lookup_at m d nm e Hj). by eexists.
  - rewrite (tedge_del_lookup_ne m d nm j Hne) Hj. by eexists.
Qed.

(* the premise every INSIDE lemma takes, unpacked once *)
Lemma subtree_dom_reach (av : aview) (r : Z) (t : ttree) (i : Z) :
  subtree av r = Some t -> i ∈ dom (tv_nodes t) -> nreach (tview av) r i.
Proof.
  intros Ht Hi. rewrite (subtree_nodes_eq av r t Ht) in Hi.
  by apply elem_of_dom_subtree_nodes in Hi as [_ ?].
Qed.

Lemma subtree_root_dir (av : aview) (r : Z) (t : ttree) :
  subtree av r = Some t -> exists e, tview av !! r = Some (ADir e).
Proof.
  intros Ht. apply subtree_Some_inv in Ht as (Hd & _). by apply adir_at_tview.
Qed.

(* ---- INSIDE: write and trunc splice a file's bytes ------------------ *)

Lemma subtree_delta_write (av : aview) (r i : Z) (t : ttree) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  subtree av r = Some t ->
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  i ∈ dom (tv_nodes t) ->
  subtree (delta_write i off new av) r = Some (top_write i off new t).
Proof.
  intros Ht Hi Hdom.
  pose proof (subtree_dom_reach av r t i Ht Hdom) as Hri.
  destruct (subtree_root_dir av r t Ht) as (e & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  assert (Hne : r <> i) by (intros ->; rewrite Hr in Hti; discriminate).
  assert (Hnodes_i : tv_nodes t !! i = Some (AFile bs0)).
  { rewrite Hnodes /subtree_nodes (nclose_lookup_in (tview av) r i Hri) //. }
  rewrite /subtree /subtree_nodes (tview_delta_write av i off new bs0 nl Hi).
  rewrite lookup_insert_ne; [| intros Hc; exact (Hne (eq_sym Hc))]. rewrite Hr.
  rewrite /top_write Hnodes_i Hroot Hnodes /subtree_nodes.
  rewrite (nclose_content_edit (tview av) r i (AFile (blk_splice off new bs0))
             (AFile bs0) Hti eq_refl Hri) //.
Qed.

Lemma subtree_delta_trunc (av : aview) (r i : Z) (t : ttree)
    (bs0 : list (bv 8)) (nl : nat) :
  subtree av r = Some t ->
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  i ∈ dom (tv_nodes t) ->
  subtree (delta_trunc i av) r = Some (top_trunc i t).
Proof.
  intros Ht Hi Hdom.
  pose proof (subtree_dom_reach av r t i Ht Hdom) as Hri.
  destruct (subtree_root_dir av r t Ht) as (e & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  assert (Hne : r <> i) by (intros ->; rewrite Hr in Hti; discriminate).
  assert (Hnodes_i : tv_nodes t !! i = Some (AFile bs0)).
  { rewrite Hnodes /subtree_nodes (nclose_lookup_in (tview av) r i Hri) //. }
  rewrite /subtree /subtree_nodes (tview_delta_trunc av i bs0 nl Hi).
  rewrite lookup_insert_ne; [| intros Hc; exact (Hne (eq_sym Hc))]. rewrite Hr.
  rewrite /top_trunc Hnodes_i Hroot Hnodes /subtree_nodes.
  rewrite (nclose_content_edit (tview av) r i (AFile []) (AFile bs0)
             Hti eq_refl Hri) //.
Qed.

(* ---- INSIDE: link puts a second name on a node already owned -------- *)

Lemma subtree_delta_link_ent (av : aview) (r d : Z) (nm : fname) (i : Z)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  subtree av r = Some t -> fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  d ∈ dom (tv_nodes t) -> i ∈ dom (tv_nodes t) ->
  subtree (delta_link_ent d nm i av) r = Some (top_link d nm i t).
Proof.
  intros Ht Hnm Hd Hnone Hdd Hdi.
  pose proof (subtree_dom_reach av r t d Ht Hdd) as Hrd.
  pose proof (subtree_dom_reach av r t i Ht Hdi) as Hri.
  destruct (subtree_root_dir av r t Ht) as (e0 & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hhn : hide_dots e !! nm = None) by (rewrite hide_dots_lookup //).
  rewrite /subtree /subtree_nodes (tview_delta_link_ent av d nm i e nl Hnm Hd).
  destruct (tedge_ins_dir (tview av) d nm i r e0 Hr) as (e' & Hr').
  rewrite Hr' /top_link Hroot Hnodes /subtree_nodes.
  rewrite (nclose_tedge_ins_in (tview av) r d nm i (hide_dots e)
             Hnm Htd Hhn Hrd Hri) //.
Qed.

(* ---- INSIDE: create hangs a fresh leaf under an owned directory ----- *)

Lemma tview_delta_create (av : aview) (d : Z) (nm : fname) (i : Z) (c : absnode)
    (e : gmap fname Z) (nl : nat) :
  fs_pname nm -> av !! d = Some (MkAnode (ADir e) nl) -> av !! i = None ->
  tview (delta_create d nm i c av)
  = tedge_ins d nm i (<[i := tabs_of c]> (tview av)).
Proof.
  intros Hnm Hd Hi.
  assert (Hne : d <> i) by (intros ->; rewrite Hd in Hi; discriminate).
  rewrite (delta_create_split av d nm i c e nl Hd Hi).
  rewrite (tview_delta_ent (delta_arm i c av) d nm i e nl (MkAnode c 1%nat) Hnm).
  - rewrite (tview_delta_arm av i c) //.
  - rewrite (delta_arm_lookup_same av i c d Hne) //.
  - apply delta_arm_lookup_at.
Qed.

Lemma subtree_delta_create (av : aview) (r d : Z) (nm : fname) (i : Z)
    (c : absnode) (t : ttree) (e : gmap fname Z) (nl : nat) :
  subtree av r = Some t -> fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = None -> tabs_leaf (tabs_of c) ->
  d ∈ dom (tv_nodes t) ->
  subtree (delta_create d nm i c av) r = Some (top_ins d nm i (tabs_of c) t).
Proof.
  intros Ht Hnm Hd Hnone Hi Hleaf Hdd.
  pose proof (subtree_dom_reach av r t d Ht Hdd) as Hrd.
  destruct (subtree_root_dir av r t Ht) as (e0 & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hhn : hide_dots e !! nm = None) by (rewrite hide_dots_lookup //).
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  assert (Hri : r <> i) by (intros ->; rewrite Hr in Hti; discriminate).
  rewrite /subtree /subtree_nodes (tview_delta_create av d nm i c e nl Hnm Hd Hi).
  assert (Hr2 : <[i := tabs_of c]> (tview av) !! r = Some (ADir e0))
    by (rewrite lookup_insert_ne; [exact Hr | intros Hc; exact (Hri (eq_sym Hc))]).
  destruct (tedge_ins_dir (<[i := tabs_of c]> (tview av)) d nm i r e0 Hr2)
    as (e' & Hr').
  rewrite Hr' /top_ins Hroot Hnodes /subtree_nodes.
  rewrite (nclose_tedge_ins_fresh (tview av) r d nm i (tabs_of c) (hide_dots e)
             Hnm Htd Hhn Hrd Hti Hleaf) //.
Qed.

(* ...AND THE PARENT LEG ON ITS OWN, which is what the fires actually
   commit (round E2's legs): the child is already ARMED -- a row of the
   view -- but nothing named it yet, so the owner still does not reach
   it, and the leg is the same fresh insert. *)
Lemma subtree_delta_ent (av : aview) (r d : Z) (nm : fname) (i : Z)
    (a : anode) (t : ttree) (e : gmap fname Z) (nl : nat) :
  subtree av r = Some t -> fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = Some a -> tabs_leaf (tnode_of a) ->
  ~ nreach (tview av) r i ->
  d ∈ dom (tv_nodes t) ->
  subtree (delta_ent d nm i av) r = Some (top_ins d nm i (tnode_of a) t).
Proof.
  intros Ht Hnm Hd Hnone Hi Hleaf Hunr Hdd.
  pose proof (subtree_dom_reach av r t d Ht Hdd) as Hrd.
  destruct (subtree_root_dir av r t Ht) as (e0 & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hti : tview av !! i = Some (tnode_of a))
    by (rewrite (tview_lookup_Some av i a Hi) //).
  assert (Hhn : hide_dots e !! nm = None) by (rewrite hide_dots_lookup //).
  assert (Hdi : d <> i) by (intros ->; exact (Hunr Hrd)).
  (* the child is a row the owner does not reach, so DELETING it changes
     nothing the owner can see -- and then it is create's fresh insert *)
  set (m1 := delete i (tview av)).
  assert (Hag : forall j, nreach (tview av) r j -> tview av !! j = m1 !! j).
  { intros j Hj. rewrite /m1 lookup_delete_ne; [reflexivity |].
    intros ->. exact (Hunr Hj). }
  assert (Hcl : nclose (tview av) r = nclose m1 r)
    by exact (nclose_agree (tview av) m1 r Hag).
  assert (Hrd1 : nreach m1 r d)
    by (apply (nreach_agree (tview av) m1 r Hag); exact Hrd).
  assert (Hd1 : m1 !! d = Some (ADir (hide_dots e)))
    by (rewrite /m1 lookup_delete_ne; [exact Htd | congruence]).
  assert (Hi1 : m1 !! i = None) by (rewrite /m1 lookup_delete_eq //).
  assert (Hback : <[i := tnode_of a]> m1 = tview av)
    by (rewrite /m1 insert_delete_id //).
  rewrite /subtree /subtree_nodes (tview_delta_ent av d nm i e nl a Hnm Hd Hi).
  destruct (tedge_ins_dir (tview av) d nm i r e0 Hr) as (e' & Hr').
  rewrite Hr' /top_ins Hroot Hnodes /subtree_nodes.
  rewrite -{1}Hback
    (nclose_tedge_ins_fresh m1 r d nm i (tnode_of a) (hide_dots e)
       Hnm Hd1 Hhn Hrd1 Hi1 Hleaf) -Hcl //.
Qed.

(* ---- INSIDE: unlink cuts a name, and the tree RE-CLOSES ------------- *)

Lemma subtree_delta_unl_ent (av : aview) (r d : Z) (nm : fname) (dec : nat)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  subtree av r = Some t ->
  av !! d = Some (MkAnode (ADir e) nl) ->
  d ∈ dom (tv_nodes t) ->
  subtree (delta_unl_ent d nm dec av) r = Some (top_unlink d nm t).
Proof.
  intros Ht Hd Hdd.
  pose proof (subtree_dom_reach av r t d Ht Hdd) as Hrd.
  destruct (subtree_root_dir av r t Ht) as (e0 & Hr).
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (subtree_root av r t Ht) as Hroot.
  rewrite /subtree /subtree_nodes (tview_delta_unl_ent av d nm dec e nl Hd).
  destruct (tedge_del_dir (tview av) d nm r e0 Hr) as (e' & Hr').
  rewrite Hr' /top_unlink Hroot Hnodes /subtree_nodes.
  rewrite (nclose_tedge_del_in (tview av) r d nm Hrd) //.
Qed.

(* ---- THE INVISIBLE LEGS -------------------------------------------- *)

(* mkdir's two interior [dirlink]s: the tree hides the dots, so the legs
   move nothing at all -- at ANY root, owner or not. *)
Lemma subtree_delta_dots (av : aview) (r i d : Z) :
  subtree (delta_dots i d av) r = subtree av r.
Proof. apply subtree_cong, tview_delta_dots. Qed.

Lemma subtree_delta_dot (av : aview) (r i : Z) :
  subtree (delta_dot i av) r = subtree av r.
Proof. apply subtree_cong, tview_delta_dot. Qed.

(* link's target leg at a row the view HAS: a pure count bump *)
Lemma subtree_delta_link_tgt (av : aview) (r t : Z) (a : anode) :
  av !! t = Some a -> subtree (delta_link_tgt t a av) r = subtree av r.
Proof. intros Ha. apply subtree_cong. exact (tview_delta_link_tgt av t a Ha). Qed.

(* unlink's target leg when the link was NOT the last: a count drop *)
Lemma subtree_delta_unl_tgt_live (av : aview) (r t : Z) (a : anode) :
  av !! t = Some a -> (2 <= an_nlink a)%nat ->
  subtree (delta_unl_tgt t av) r = subtree av r.
Proof.
  intros Ha Hnl. apply subtree_cong. exact (tview_delta_unl_tgt_live av t a Ha Hnl).
Qed.

(* ---- OUTSIDE: one corollary per leg --------------------------------- *)

Lemma subtree_out_row2 (av av' : aview) (r i1 i2 : Z) :
  (forall j, j <> i1 -> j <> i2 -> av' !! j = av !! j) ->
  ~ nreach (tview av) r i1 -> ~ nreach (tview av) r i2 ->
  subtree av' r = subtree av r.
Proof.
  intros Hne H1 H2. apply subtree_out. intros j Hj.
  apply tview_lookup_ne_of, Hne; intros ->; [exact (H1 Hj) | exact (H2 Hj)].
Qed.

Lemma subtree_delta_write_out (av : aview) (r i : Z) (off : nat)
    (new : list (bv 8)) :
  ~ nreach (tview av) r i -> subtree (delta_write i off new av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_write_other av i off new j Hj).
Qed.

Lemma subtree_delta_trunc_out (av : aview) (r i : Z) :
  ~ nreach (tview av) r i -> subtree (delta_trunc i av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_trunc_other av i j Hj).
Qed.

Lemma subtree_delta_ent_out (av : aview) (r d : Z) (nm : fname) (i : Z) :
  ~ nreach (tview av) r d -> subtree (delta_ent d nm i av) r = subtree av r.
Proof.
  intros Hd. apply (subtree_out_row _ _ r d); [| exact Hd].
  intros j Hj. exact (delta_ent_lookup_same av d nm i j Hj).
Qed.

Lemma subtree_delta_link_ent_out (av : aview) (r d : Z) (nm : fname) (i : Z) :
  ~ nreach (tview av) r d -> subtree (delta_link_ent d nm i av) r = subtree av r.
Proof.
  intros Hd. apply (subtree_out_row _ _ r d); [| exact Hd].
  intros j Hj. exact (delta_link_ent_lookup_same av d nm i j Hj).
Qed.

Lemma subtree_delta_unl_ent_out (av : aview) (r d : Z) (nm : fname) (dec : nat) :
  ~ nreach (tview av) r d -> subtree (delta_unl_ent d nm dec av) r = subtree av r.
Proof.
  intros Hd. apply (subtree_out_row _ _ r d); [| exact Hd].
  intros j Hj. exact (delta_unl_ent_other av d nm dec j Hj).
Qed.

Lemma subtree_delta_unl_tgt_out (av : aview) (r i : Z) :
  ~ nreach (tview av) r i -> subtree (delta_unl_tgt i av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_unl_tgt_other av i j Hj).
Qed.

Lemma subtree_delta_link_tgt_out (av : aview) (r i : Z) (a : anode) :
  ~ nreach (tview av) r i -> subtree (delta_link_tgt i a av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_link_tgt_lookup_same av i a j Hj).
Qed.

Lemma subtree_delta_arm_out (av : aview) (r i : Z) (c : absnode) :
  ~ nreach (tview av) r i -> subtree (delta_arm i c av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_arm_lookup_same av i c j Hj).
Qed.

Lemma subtree_delta_unarm_out (av : aview) (r i : Z) :
  ~ nreach (tview av) r i -> subtree (delta_unarm i av) r = subtree av r.
Proof.
  intros Hi. apply (subtree_out_row _ _ r i); [| exact Hi].
  intros j Hj. exact (delta_unarm_lookup_same av i j Hj).
Qed.

(* CREATE'S ARM IS ALWAYS OUTSIDE (a fresh inum is unreachable when no
   entry dangles): the child appears to the owner at the PARENT leg, not
   before -- which is why the two legs may be paid in either order. *)
Lemma subtree_delta_arm_fresh (av : aview) (r i : Z) (c : absnode) :
  aview_closed av -> av !! i = None -> i <> r ->
  subtree (delta_arm i c av) r = subtree av r.
Proof.
  intros Hc Hi Hne. apply subtree_delta_arm_out.
  exact (nreach_fresh av r i Hc Hi Hne).
Qed.

(* the FUSED deltas, outside: two keys move *)
Lemma subtree_delta_create_out (av : aview) (r d : Z) (nm : fname) (i : Z)
    (c : absnode) :
  ~ nreach (tview av) r d -> ~ nreach (tview av) r i ->
  subtree (delta_create d nm i c av) r = subtree av r.
Proof.
  intros Hd Hi. apply (subtree_out_row2 _ _ r d i); [| exact Hd | exact Hi].
  intros j Hjd Hji. exact (delta_create_other av d nm i c j Hjd Hji).
Qed.

Lemma subtree_delta_unlink_out (av : aview) (r d : Z) (nm : fname) (tg : Z) :
  ~ nreach (tview av) r d -> ~ nreach (tview av) r tg ->
  subtree (delta_unlink d nm tg av) r = subtree av r.
Proof.
  intros Hd Ht. apply (subtree_out_row2 _ _ r d tg); [| exact Hd | exact Ht].
  intros j Hjd Hjt. exact (delta_unlink_other av d nm tg j Hjd Hjt).
Qed.

Lemma subtree_delta_link_out (av : aview) (r d : Z) (nm : fname) (tg : Z)
    (a : anode) :
  ~ nreach (tview av) r d -> ~ nreach (tview av) r tg ->
  subtree (delta_link d nm tg a av) r = subtree av r.
Proof.
  intros Hd Ht. apply (subtree_out_row2 _ _ r d tg); [| exact Hd | exact Ht].
  intros j Hjd Hjt. exact (delta_link_other av d nm tg a j Hjd Hjt).
Qed.

(* ===================================================================== *)
(*  6.  PATH RESOLUTION IN A TREE, AND [arun] ON THE VIEW                 *)
(* ===================================================================== *)

(* THE WALK IS LOCAL: inside the closure, walking the OWNER'S TREE and
   walking the whole view are the same walk.  (This is why a held subtree
   can answer exec's (W) and open's walk with no view in hand.) *)
Lemma npath_nclose (m : gmap Z absnode) (r : Z) (ps : list fname) (d : Z) :
  fs_proper ps -> nreach m r d -> npath (nclose m r) d ps = npath m d ps.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hp Hd; [reflexivity |].
  apply fs_proper_cons in Hp as [Hs Hp].
  rewrite !npath_cons (nstep_of_lookup _ m d s (nclose_lookup_in m r d Hd)).
  destruct (nstep m d s) as [c |] eqn:Hst; [| reflexivity].
  apply IH; [exact Hp | exact (nreach_hop m r d s c Hd Hs Hst)].
Qed.

Lemma nchain_nclose (m : gmap Z absnode) (r : Z) (ps : list fname) (d : Z) :
  fs_proper ps -> nreach m r d -> nchain (nclose m r) d ps = nchain m d ps.
Proof.
  revert d. induction ps as [| s ps IH]; intros d Hp Hd; [reflexivity |].
  apply fs_proper_cons in Hp as [Hs Hp].
  cbn [nchain]. rewrite (nstep_of_lookup _ m d s (nclose_lookup_in m r d Hd)).
  destruct (nstep m d s) as [c |] eqn:Hst; [| reflexivity].
  rewrite (IH c Hp (nreach_hop m r d s c Hd Hs Hst)) //.
Qed.

(* PATHS ARE PROPER HERE.  A path naming "." or ".." is not a path in the
   application tree: ".." at the root leaves the subtree, which is the
   one move the claim cannot answer.  [fs_proper (path_elems pl)] is a
   pure fact about the program's own string and is discharged by its code
   proof -- the design's "the premise the program needs is a pure fact
   about its path". *)
Definition resolves_from (t : ttree) (d : Z) (pl : list (bv 8))
    : option (Z * absnode) :=
  match npath (tv_nodes t) d (path_elems pl) with
  | Some i => match tv_nodes t !! i with
              | Some n => Some (i, n)
              | None => None
              end
  | None => None
  end.

Definition resolves_in (t : ttree) (pl : list (bv 8)) : option (Z * absnode) :=
  resolves_from t (tv_root t) pl.

(* the hops the walk stands on -- computed FROM THE TREE ALONE, which is
   what makes it the same list at every view the claim admits *)
Definition resolve_hops (t : ttree) (d : Z) (pl : list (bv 8)) : list Z :=
  nchain (tv_nodes t) d (path_elems pl).

Lemma resolves_from_dom (t : ttree) (d i : Z) (n : absnode) (pl : list (bv 8)) :
  resolves_from t d pl = Some (i, n) -> tv_nodes t !! i = Some n.
Proof.
  rewrite /resolves_from. destruct (npath (tv_nodes t) d _) as [j |]; [| discriminate].
  destruct (tv_nodes t !! j) as [n0 |] eqn:Hn; [| discriminate].
  intros Hc. injection Hc as <- <-. exact Hn.
Qed.

(* ---- THE EQUIVALENCE ------------------------------------------------ *)

(* (=>) what a held subtree ANSWERS: the run on the view, the inum, and
   the node -- the three pieces [PinnedObs.pin_resolves_at] asks for. *)
Lemma resolves_from_arun (av : aview) (r : Z) (t : ttree) (d i : Z)
    (n : absnode) (pl : list (bv 8)) :
  subtree av r = Some t -> fs_proper (path_elems pl) ->
  nreach (tview av) r d ->
  resolves_from t d pl = Some (i, n) ->
  arun av d (path_elems pl) (resolve_hops t d pl)
  /\ resolve_hops t d pl !!! 0%nat = d
  /\ resolve_hops t d pl !!! length (path_elems pl) = i
  /\ (exists a, av !! i = Some a /\ n = tnode_of a).
Proof.
  intros Ht Hp Hd Hres.
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  assert (Hwalk : npath (tv_nodes t) d (path_elems pl) = apath_at av d (path_elems pl)).
  { rewrite Hnodes /subtree_nodes (npath_nclose (tview av) r (path_elems pl) d Hp Hd).
    exact (npath_tview av d (path_elems pl) Hp). }
  assert (Hchain : resolve_hops t d pl = nchain (tview av) d (path_elems pl)).
  { rewrite /resolve_hops Hnodes /subtree_nodes.
    exact (nchain_nclose (tview av) r (path_elems pl) d Hp Hd). }
  rewrite /resolves_from Hwalk in Hres.
  destruct (apath_at av d (path_elems pl)) as [j |] eqn:Hw; [| discriminate].
  destruct (tv_nodes t !! j) as [n0 |] eqn:Hn; [| discriminate].
  injection Hres as <- <-.
  assert (Hrun : arun av d (path_elems pl) (resolve_hops t d pl)).
  { rewrite Hchain. exact (nchain_arun av d (path_elems pl) j Hp Hw). }
  split; [exact Hrun |].
  split; [exact (arun_head av d (path_elems pl) _ Hrun) |].
  split.
  - pose proof (arun_apath_tot av d (path_elems pl) _ Hrun) as Htot.
    rewrite Hw in Htot. by injection Htot as ->.
  - rewrite Hnodes in Hn. apply subtree_nodes_lookup_Some in Hn as ((a & Ha & ->) & _).
    by exists a.
Qed.

Lemma resolves_in_arun (av : aview) (r : Z) (t : ttree) (i : Z)
    (n : absnode) (pl : list (bv 8)) :
  subtree av r = Some t -> fs_proper (path_elems pl) ->
  resolves_in t pl = Some (i, n) ->
  arun av r (path_elems pl) (resolve_hops t r pl)
  /\ resolve_hops t r pl !!! 0%nat = r
  /\ resolve_hops t r pl !!! length (path_elems pl) = i
  /\ (exists a, av !! i = Some a /\ n = tnode_of a).
Proof.
  intros Ht Hp Hres. rewrite /resolves_in (subtree_root av r t Ht) in Hres.
  exact (resolves_from_arun av r t r i n pl Ht Hp (nreach_refl (tview av) r) Hres).
Qed.

(* (<=) the converse: a walk the VIEW answers, at a start the owner
   reaches, is answered by the owner's TREE -- nothing is lost by holding
   the subtree instead of the view. *)
Lemma resolves_from_of_arun (av : aview) (r : Z) (t : ttree) (d i : Z)
    (a : anode) (pl : list (bv 8)) (hops : list Z) :
  subtree av r = Some t -> fs_proper (path_elems pl) ->
  nreach (tview av) r d ->
  arun av d (path_elems pl) hops ->
  hops !!! length (path_elems pl) = i ->
  av !! i = Some a ->
  resolves_from t d pl = Some (i, tnode_of a).
Proof.
  intros Ht Hp Hd Hrun Hi Ha.
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  pose proof (arun_apath_tot av d (path_elems pl) hops Hrun) as Hw.
  rewrite Hi in Hw.
  assert (Hri : nreach (tview av) r i).
  { apply (nreach_trans (tview av) r d i Hd). apply nreach_tview. by exists (path_elems pl). }
  rewrite /resolves_from Hnodes /subtree_nodes.
  rewrite (npath_nclose (tview av) r (path_elems pl) d Hp Hd)
          (npath_tview av d (path_elems pl) Hp) Hw.
  rewrite (subtree_nodes_lookup_of av r i a Ha Hri) //.
Qed.

(* THE PIN SHAPE.  [PinnedObs.pin_resolves_at Pin cw pl hops ino aa] asks
   for a FIXED [hops] and a FIXED [anode] good at every view the claim
   admits.  [resolve_hops] is fixed (it is computed from the tree alone);
   the node is fixed only up to what the tree FORGETS -- the link count,
   and a directory's two dots.  So the general form quantifies over the
   view's row and says it PROJECTS to the tree's node... *)
Lemma subtree_resolves_pin (t : ttree) (d i : Z) (n : absnode)
    (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  resolves_from t d pl = Some (i, n) ->
  forall (av : aview) (r : Z),
    subtree av r = Some t -> nreach (tview av) r d ->
    arun av d (path_elems pl) (resolve_hops t d pl)
    /\ resolve_hops t d pl !!! 0%nat = d
    /\ resolve_hops t d pl !!! length (path_elems pl) = i
    /\ (exists (n' : absnode) (k : nat),
          av !! i = Some (MkAnode n' k) /\ tabs_of n' = n).
Proof.
  intros Hp Hres av r Ht Hd.
  destruct (resolves_from_arun av r t d i n pl Ht Hp Hd Hres)
    as (Hrun & H0 & Hlen & (a & Ha & Hn)).
  split; [exact Hrun |]. split; [exact H0 |]. split; [exact Hlen |].
  destruct a as [n0 k]. exists n0, k. split; [exact Ha |].
  by rewrite /tnode_of /= in Hn.
Qed.

(* ...AND AT A NON-DIRECTORY THE PROJECTION IS THE IDENTITY, so the row
   IS pinned up to its count: this is the form exec's (W) takes (a file),
   and the form open takes at a file or a device. *)
Lemma tabs_of_file_inv (n' : absnode) (bs : list (bv 8)) :
  tabs_of n' = AFile bs -> n' = AFile bs.
Proof. destruct n' as [bs0 | e | ma mi]; cbn; congruence. Qed.

Lemma tabs_of_dev_inv (n' : absnode) (ma mi : Z) :
  tabs_of n' = ADev ma mi -> n' = ADev ma mi.
Proof. destruct n' as [bs0 | e | ma0 mi0]; cbn; congruence. Qed.

Lemma subtree_resolves_pin_file (t : ttree) (d i : Z) (bs : list (bv 8))
    (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  resolves_from t d pl = Some (i, AFile bs) ->
  forall (av : aview) (r : Z),
    subtree av r = Some t -> nreach (tview av) r d ->
    arun av d (path_elems pl) (resolve_hops t d pl)
    /\ resolve_hops t d pl !!! 0%nat = d
    /\ resolve_hops t d pl !!! length (path_elems pl) = i
    /\ (exists k : nat, av !! i = Some (MkAnode (AFile bs) k)).
Proof.
  intros Hp Hres av r Ht Hd.
  destruct (subtree_resolves_pin t d i (AFile bs) pl Hp Hres av r Ht Hd)
    as (Hrun & H0 & Hlen & (n' & k & Ha & Hn)).
  split; [exact Hrun |]. split; [exact H0 |]. split; [exact Hlen |].
  exists k. rewrite (tabs_of_file_inv n' bs Hn) in Ha. exact Ha.
Qed.

(* ===================================================================== *)
(*  7.  [own_wf] IS PRESERVED BY AN OWNER'S OWN-SUBTREE DELTAS            *)
(* ===================================================================== *)

(* the closedness conjunct, in the projected map's vocabulary *)
Definition nclosed (m : gmap Z absnode) : Prop :=
  forall (d : Z) (s : fname) (j : Z),
    fs_pname s -> nstep m d s = Some j -> j ∈ dom m.

Lemma aview_closed_nstep (av : aview) : aview_closed av <-> nclosed (tview av).
Proof.
  rewrite /aview_closed /nclosed. split; intros Hh d s j Hs Hst.
  - rewrite (nstep_tview av d s Hs) in Hst. rewrite tview_dom.
    apply elem_of_dom. exact (Hh d s j Hs Hst).
  - rewrite -(nstep_tview av d s Hs) in Hst.
    apply elem_of_dom. rewrite -tview_dom. exact (Hh d s j Hs Hst).
Qed.

(* ---- 7a.  THE THREE EDITS, AT THE MAP LEVEL ------------------------- *)

Lemma dom_content_edit (m : gmap Z absnode) (i : Z) (c c0 : absnode) :
  m !! i = Some c0 -> dom (<[i := c]> m) = dom m.
Proof. intros Hi. rewrite dom_insert_L. apply elem_of_dom_2 in Hi. set_solver. Qed.

Lemma dom_tedge_del (m : gmap Z absnode) (d : Z) (nm : fname) :
  dom (tedge_del d nm m) = dom m.
Proof.
  rewrite /tedge_del. destruct (m !! d) as [n |] eqn:Hd; [| reflexivity].
  destruct n as [bs | e | ma mi]; [reflexivity | | reflexivity].
  rewrite dom_insert_L. apply elem_of_dom_2 in Hd. set_solver.
Qed.

Lemma nstep_content_edit (m : gmap Z absnode) (i : Z) (c c0 : absnode)
    (d : Z) (s : fname) :
  m !! i = Some c0 -> nents_of c = nents_of c0 ->
  nstep (<[i := c]> m) d s = nstep m d s.
Proof.
  intros Hi Hc. rewrite /nstep !nents_unfold.
  destruct (decide (d = i)) as [-> | Hd]; [| by rewrite lookup_insert_ne].
  rewrite lookup_insert_eq Hi /= Hc //.
Qed.

Lemma nuniq_parent_content_edit (m : gmap Z absnode) (i : Z) (c c0 : absnode) :
  m !! i = Some c0 -> nents_of c = nents_of c0 ->
  nuniq_parent m -> nuniq_parent (<[i := c]> m).
Proof.
  intros Hi Hc Hu d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
  rewrite (nstep_content_edit m i c c0 d1 s1 Hi Hc) in H1.
  rewrite (nstep_content_edit m i c c0 d2 s2 Hi Hc) in H2.
  exact (Hu _ _ _ _ _ Hs1 Hs2 H1 H2).
Qed.

Lemma nclosed_content_edit (m : gmap Z absnode) (i : Z) (c c0 : absnode) :
  m !! i = Some c0 -> nents_of c = nents_of c0 ->
  nclosed m -> nclosed (<[i := c]> m).
Proof.
  intros Hi Hc Hn d s j Hs Hst.
  rewrite (nstep_content_edit m i c c0 d s Hi Hc) in Hst.
  rewrite (dom_content_edit m i c c0 Hi). exact (Hn d s j Hs Hst).
Qed.

Lemma nuniq_parent_edge_del (m : gmap Z absnode) (d : Z) (nm : fname) :
  nuniq_parent m -> nuniq_parent (tedge_del d nm m).
Proof.
  intros Hu d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
  exact (Hu _ _ _ _ _ Hs1 Hs2
           (nstep_tedge_del_sub m d nm d1 s1 j H1)
           (nstep_tedge_del_sub m d nm d2 s2 j H2)).
Qed.

Lemma nclosed_edge_del (m : gmap Z absnode) (d : Z) (nm : fname) :
  nclosed m -> nclosed (tedge_del d nm m).
Proof.
  intros Hn d0 s j Hs Hst. rewrite dom_tedge_del.
  exact (Hn d0 s j Hs (nstep_tedge_del_sub m d nm d0 s j Hst)).
Qed.

(* the fresh insert, whose edges are the old ones plus exactly one *)
Lemma nstep_ins_fresh_inv (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) (x : Z) (s : fname) (j : Z) :
  m !! d = Some (ADir e) -> m !! i = None -> tabs_leaf c -> fs_pname s ->
  nstep (tedge_ins d nm i (<[i := c]> m)) x s = Some j ->
  (nstep m x s = Some j /\ x <> i) \/ (x = d /\ s = nm /\ j = i).
Proof.
  intros Hd Hfresh Hleaf Hs Hst.
  assert (Hne : i <> d) by (intros ->; rewrite Hd in Hfresh; discriminate).
  assert (Hins : forall x0, x0 <> i -> <[i := c]> m !! x0 = m !! x0).
  { intros x0 Hx0. rewrite lookup_insert_ne //. }
  assert (Hdi : d <> i) by (intros Hc; exact (Hne (eq_sym Hc))).
  assert (Hd0 : <[i := c]> m !! d = Some (ADir e)) by (rewrite (Hins d Hdi) //).
  destruct (decide (x = d)) as [-> | Hx].
  - rewrite (nstep_tedge_ins_at _ d nm i e s Hd0) in Hst.
    case_decide as Hs'.
    + right. injection Hst as <-. by repeat split.
    + left. rewrite (nstep_of_lookup (<[i := c]> m) m d s (Hins d Hdi)) in Hst.
      by split.
  - rewrite (nstep_of_lookup _ (<[i := c]> m) x s (tedge_ins_lookup_ne _ d nm i x Hx))
      in Hst.
    destruct (decide (x = i)) as [-> | Hxi].
    + assert (Hii : <[i := c]> m !! i = Some c) by (rewrite lookup_insert_eq //).
      rewrite (nstep_leaf (<[i := c]> m) i c s Hii Hleaf Hs) in Hst.
      discriminate.
    + left. rewrite (nstep_of_lookup (<[i := c]> m) m x s (Hins x Hxi)) in Hst.
      by split.
Qed.

Lemma nuniq_parent_ins_fresh (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) :
  m !! d = Some (ADir e) -> m !! i = None -> tabs_leaf c -> nclosed m ->
  nuniq_parent m -> nuniq_parent (tedge_ins d nm i (<[i := c]> m)).
Proof.
  intros Hd Hfresh Hleaf Hn Hu d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
  destruct (nstep_ins_fresh_inv m d nm i c e d1 s1 j Hd Hfresh Hleaf Hs1 H1)
    as [[Ha1 _] | (-> & -> & Hj1)].
  - destruct (nstep_ins_fresh_inv m d nm i c e d2 s2 j Hd Hfresh Hleaf Hs2 H2)
      as [[Ha2 _] | (-> & -> & Hj2)].
    + exact (Hu _ _ _ _ _ Hs1 Hs2 Ha1 Ha2).
    + exfalso. subst j. pose proof (Hn d1 s1 i Hs1 Ha1) as Hc.
      apply elem_of_dom in Hc as [n Hn0]. rewrite Hfresh in Hn0. discriminate.
  - destruct (nstep_ins_fresh_inv m d nm i c e d2 s2 j Hd Hfresh Hleaf Hs2 H2)
      as [[Ha2 _] | (-> & -> & Hj2)].
    + exfalso. subst j. pose proof (Hn d2 s2 i Hs2 Ha2) as Hc.
      apply elem_of_dom in Hc as [n Hn0]. rewrite Hfresh in Hn0. discriminate.
    + by split.
Qed.

Lemma nclosed_ins_fresh (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) :
  m !! d = Some (ADir e) -> m !! i = None -> tabs_leaf c ->
  nclosed m -> nclosed (tedge_ins d nm i (<[i := c]> m)).
Proof.
  intros Hd Hfresh Hleaf Hn x s j Hs Hst.
  assert (Hdom : dom (tedge_ins d nm i (<[i := c]> m)) = dom m ∪ {[i]}).
  { assert (Hd0 : <[i := c]> m !! d = Some (ADir e)) by
      (rewrite lookup_insert_ne //; intros ->; rewrite Hd in Hfresh; discriminate).
    rewrite /tedge_ins Hd0 !dom_insert_L. apply elem_of_dom_2 in Hd. set_solver. }
  rewrite Hdom.
  destruct (nstep_ins_fresh_inv m d nm i c e x s j Hd Hfresh Hleaf Hs Hst)
    as [[Ha _] | (_ & _ & ->)]; [| set_solver].
  pose proof (Hn x s j Hs Ha). set_solver.
Qed.

(* the reach inversion the non-nesting conjunct needs: after a fresh
   insert, the only node newly reachable is the fresh one *)
Lemma nreach_ins_fresh_inv (m : gmap Z absnode) (r d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) :
  m !! d = Some (ADir e) -> m !! i = None -> tabs_leaf c -> nclosed m ->
  forall j, nreach (tedge_ins d nm i (<[i := c]> m)) r j -> nreach m r j \/ j = i.
Proof.
  intros Hd Hfresh Hleaf Hn.
  apply (nreach_closed_ind _ r (fun j => nreach m r j \/ j = i)
           (or_introl (nreach_refl m r))).
  intros d0 s c0 Hd0 Hs Hst.
  destruct (nstep_ins_fresh_inv m d nm i c e d0 s c0 Hd Hfresh Hleaf Hs Hst)
    as [[Ha Hne] | (_ & _ & ->)]; [| by right].
  destruct Hd0 as [Hd0 | ->]; [| done].
  left. exact (nreach_hop m r d0 s c0 Hd0 Hs Ha).
Qed.

(* ---- 7b.  THE TREE-SHAPE CONJUNCT, AT EACH DELTA -------------------- *)

Lemma aview_tree_wf_write (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  aview_tree_wf av -> aview_tree_wf (delta_write i off new av).
Proof.
  intros Hi [Hu Hc].
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_write av i off new bs0 nl Hi).
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc |- *. split.
  - exact (nuniq_parent_content_edit (tview av) i (AFile (blk_splice off new bs0))
             (AFile bs0) Hti eq_refl Hu).
  - exact (nclosed_content_edit (tview av) i (AFile (blk_splice off new bs0))
             (AFile bs0) Hti eq_refl Hc).
Qed.

Lemma aview_tree_wf_trunc (av : aview) (i : Z) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  aview_tree_wf av -> aview_tree_wf (delta_trunc i av).
Proof.
  intros Hi [Hu Hc].
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_trunc av i bs0 nl Hi).
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc |- *. split.
  - exact (nuniq_parent_content_edit (tview av) i (AFile []) (AFile bs0)
             Hti eq_refl Hu).
  - exact (nclosed_content_edit (tview av) i (AFile []) (AFile bs0)
             Hti eq_refl Hc).
Qed.

Lemma aview_tree_wf_create (av : aview) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) (nl : nat) :
  fs_pname nm -> av !! d = Some (MkAnode (ADir e) nl) -> av !! i = None ->
  tabs_leaf (tabs_of c) ->
  aview_tree_wf av -> aview_tree_wf (delta_create d nm i c av).
Proof.
  intros Hnm Hd Hi Hleaf [Hu Hc].
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc.
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_create av d nm i c e nl Hnm Hd Hi).
  split.
  - exact (nuniq_parent_ins_fresh (tview av) d nm i _ _ Htd Hti Hleaf Hc Hu).
  - exact (nclosed_ins_fresh (tview av) d nm i _ _ Htd Hti Hleaf Hc).
Qed.

(* create's ARM on its own: a leaf row appears at an inum nothing names,
   so not one edge of the namespace moves *)
Lemma nstep_ins_leaf (m : gmap Z absnode) (i : Z) (c : absnode)
    (x : Z) (s : fname) :
  m !! i = None -> tabs_leaf c -> fs_pname s ->
  nstep (<[i := c]> m) x s = nstep m x s.
Proof.
  intros Hi Hleaf Hs.
  assert (Hii : <[i := c]> m !! i = Some c) by (rewrite lookup_insert_eq //).
  destruct (decide (x = i)) as [-> | Hx].
  - rewrite (nstep_leaf (<[i := c]> m) i c s Hii Hleaf Hs).
    rewrite /nstep nents_unfold Hi //.
  - assert (Hne : <[i := c]> m !! x = m !! x)
      by (rewrite lookup_insert_ne //).
    rewrite (nstep_of_lookup (<[i := c]> m) m x s Hne) //.
Qed.

Lemma aview_tree_wf_arm (av : aview) (i : Z) (c : absnode) :
  av !! i = None -> tabs_leaf (tabs_of c) ->
  aview_tree_wf av -> aview_tree_wf (delta_arm i c av).
Proof.
  intros Hi Hleaf [Hu Hc].
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc.
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_arm av i c).
  split.
  - intros d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
    rewrite (nstep_ins_leaf (tview av) i _ d1 s1 Hti Hleaf Hs1) in H1.
    rewrite (nstep_ins_leaf (tview av) i _ d2 s2 Hti Hleaf Hs2) in H2.
    exact (Hu _ _ _ _ _ Hs1 Hs2 H1 H2).
  - intros x s j Hs Hst.
    rewrite (nstep_ins_leaf (tview av) i _ x s Hti Hleaf Hs) in Hst.
    rewrite dom_insert_L. pose proof (Hc x s j Hs Hst). set_solver.
Qed.

Lemma aview_tree_wf_unl_ent (av : aview) (d : Z) (nm : fname) (dec : nat)
    (e : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir e) nl) ->
  aview_tree_wf av -> aview_tree_wf (delta_unl_ent d nm dec av).
Proof.
  intros Hd [Hu Hc].
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc.
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_unl_ent av d nm dec e nl Hd).
  split; [exact (nuniq_parent_edge_del (tview av) d nm Hu)
         | exact (nclosed_edge_del (tview av) d nm Hc)].
Qed.

(* THE ROW REMOVAL (unlink's target leg at the last link) is the one move
   that can BREAK well-formedness, and the premise says exactly how: the
   row may only leave when nothing names it any more.  In xv6 that is the
   tie between [nlink] and the number of entries -- a global fact the tree
   layer does not carry, so it is a premise here and an obligation on the
   owner's step (the entry leg fires FIRST, which is what makes it hold). *)
Definition aview_no_edge_to (av : aview) (i : Z) : Prop :=
  forall (d : Z) (s : fname), fs_pname s -> astep av d s <> Some i.

Lemma aview_tree_wf_unl_tgt (av : aview) (tg : Z) (a : anode) :
  av !! tg = Some a -> an_nlink a = 1%nat -> aview_no_edge_to av tg ->
  aview_tree_wf av -> aview_tree_wf (delta_unl_tgt tg av).
Proof.
  intros Ha Hnl Hno [Hu Hc].
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc.
  assert (Hsub : forall x s j, nstep (delete tg (tview av)) x s = Some j ->
                   nstep (tview av) x s = Some j).
  { intros x s j. destruct (decide (x = tg)) as [-> | Hx].
    - rewrite /nstep nents_unfold lookup_delete_eq /=. intros Hcc; discriminate.
    - rewrite (nstep_of_lookup _ (tview av) x s (lookup_delete_ne _ tg x
                 (fun Hcc => Hx (eq_sym Hcc)))). exact (fun H => H). }
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_unl_tgt_last av tg a Ha Hnl).
  split.
  - intros d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
    exact (Hu _ _ _ _ _ Hs1 Hs2 (Hsub _ _ _ H1) (Hsub _ _ _ H2)).
  - intros x s j Hs Hst. pose proof (Hsub x s j Hst) as Hst'.
    assert (Hjne : j <> tg).
    { intros ->. apply (Hno x s Hs). by rewrite -(nstep_tview av x s Hs). }
    rewrite dom_delete_L. apply elem_of_difference.
    split; [exact (Hc x s j Hs Hst') | set_solver].
Qed.

(* ---- 7c.  [own_wf] ITSELF ------------------------------------------- *)

Lemma adir_at_dom (av : aview) (r : Z) : adir_at av r -> r ∈ dom av.
Proof. intros (a & e & Ha & _). apply elem_of_dom. by exists a. Qed.

Section OwnPres.
  Context {K : Type} `{Countable K}.

  (* WRITE and TRUNC: no edge and no row moves, so every conjunct rides *)
  Lemma own_wf_write (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (off : nat) (new bs0 : list (bv 8)) (nl : nat) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    own_wf av own -> own_wf (delta_write i off new av) own.
  Proof using .
    intros Hi (Hwf & Hroots & Hnn).
    assert (Hti : tview av !! i = Some (AFile bs0))
      by (rewrite (tview_lookup_Some av i _ Hi) //).
    pose proof (tview_delta_write av i off new bs0 nl Hi) as Hview.
    split; [exact (aview_tree_wf_write av i off new bs0 nl Hi Hwf) |].
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (a & e & Ha & He).
      apply adir_at_tview. rewrite Hview.
      destruct (decide (r = i)) as [-> | Hne].
      { exfalso. assert (a = MkAnode (AFile bs0) nl) as -> by congruence.
        cbn in He. discriminate. }
      rewrite lookup_insert_ne; [| intros Hc; exact (Hne (eq_sym Hc))].
      apply adir_at_tview. by exists a, e.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      apply (nreach_nents_cong (<[i := AFile (blk_splice off new bs0)]> (tview av))
               (tview av) r r'); [| exact Hr].
      intros j. symmetry. rewrite !nents_unfold.
      destruct (decide (j = i)) as [-> | Hj]; [| by rewrite lookup_insert_ne].
      rewrite lookup_insert_eq Hti //.
  Qed.

  (* ...AND ITS TWIN AT [delta_trunc], line for line (lane TL-3's
     housekeeping: it was proved in [AppTree.v]'s section 1f' so that TL-2
     had the truncate move without waiting for a TL-1 lane, and its note
     said it belonged here).  The row's CONTENT is edited and nothing
     else: no edge moves, and the row being edited is a FILE, so no root
     is it. *)
  Lemma own_wf_trunc (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (bs0 : list (bv 8)) (nl : nat) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    own_wf av own -> own_wf (delta_trunc i av) own.
  Proof using .
    intros Hi (Hwf & Hroots & Hnn).
    assert (Hti : tview av !! i = Some (AFile bs0))
      by (rewrite (tview_lookup_Some av i _ Hi) //).
    pose proof (tview_delta_trunc av i bs0 nl Hi) as Hview.
    split; [exact (aview_tree_wf_trunc av i bs0 nl Hi Hwf) |].
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (a & e & Ha & He).
      apply adir_at_tview. rewrite Hview.
      destruct (decide (r = i)) as [-> | Hne].
      { exfalso. assert (a = MkAnode (AFile bs0) nl) as -> by congruence.
        cbn in He. discriminate. }
      rewrite lookup_insert_ne; [| congruence].
      apply adir_at_tview. by exists a, e.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      apply (nreach_nents_cong (<[i := AFile []]> (tview av)) (tview av) r r');
        [| exact Hr].
      intros j. symmetry. rewrite !nents_unfold.
      destruct (decide (j = i)) as [-> | Hj]; [| by rewrite lookup_insert_ne].
      rewrite lookup_insert_eq Hti //.
  Qed.

  (* CREATE: the fresh inum is a NEW LEAF under an existing root, and it
     is not a root itself (roots are rows of the view, and it was not).
     Nothing else in [own] can see it. *)
  Lemma own_wf_create (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (i : Z) (c : absnode) (e : gmap fname Z) (nl : nat) :
    fs_pname nm -> av !! d = Some (MkAnode (ADir e) nl) -> av !! i = None ->
    tabs_leaf (tabs_of c) ->
    own_wf av own -> own_wf (delta_create d nm i c av) own.
  Proof using .
    intros Hnm Hd Hi Hleaf (Hwf & Hroots & Hnn).
    destruct Hwf as [Hu Hcl].
    assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
      by (rewrite (tview_lookup_Some av d _ Hd) //).
    assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
    pose proof (tview_delta_create av d nm i c e nl Hnm Hd Hi) as Hview.
    split; [exact (aview_tree_wf_create av d nm i c e nl Hnm Hd Hi Hleaf
                     (conj Hu Hcl)) |].
    assert (Hnotroot : forall g r t, own !! g = Some (r, t) -> r <> i).
    { intros g r t Hg Heq. subst r.
      pose proof (adir_at_dom av i (Hroots g i t Hg)) as Hdom.
      apply elem_of_dom in Hdom as [a Ha]. congruence. }
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (a & e0 & Ha & He).
      apply adir_at_tview. rewrite Hview.
      assert (Hr0 : <[i := tabs_of c]> (tview av) !! r = Some (ADir (hide_dots e0))).
      { rewrite lookup_insert_ne;
          [| intros Hc0; exact (Hnotroot g r t Hg (eq_sym Hc0))].
        rewrite (tview_lookup_Some av r a Ha) /tnode_of He //. }
      destruct (tedge_ins_dir _ d nm i r (hide_dots e0) Hr0) as (e' & Hr').
      by exists e'.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      rewrite aview_closed_nstep in Hcl.
      destruct (nreach_ins_fresh_inv (tview av) r d nm i (tabs_of c) (hide_dots e)
                  Htd Hti Hleaf Hcl r' Hr) as [Hc0 | Hc0]; [exact Hc0 |].
      exfalso. exact (Hnotroot g' r' t' Hg' Hc0).
  Qed.

  (* CREATE'S ARM alone: the fires commit a leg at a time, and this is
     the first one.  Not an edge moves, so nothing but the new row's
     presence changes -- and the fresh inum is no root. *)
  Lemma own_wf_arm (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (c : absnode) :
    av !! i = None -> tabs_leaf (tabs_of c) ->
    own_wf av own -> own_wf (delta_arm i c av) own.
  Proof using .
    intros Hi Hleaf (Hwf & Hroots & Hnn).
    assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
    destruct Hwf as [Hu Hcl].
    assert (Hcln : nclosed (tview av)) by (by apply aview_closed_nstep).
    split; [exact (aview_tree_wf_arm av i c Hi Hleaf (conj Hu Hcl)) |].
    assert (Hnotroot : forall g r t, own !! g = Some (r, t) -> r <> i).
    { intros g r t Hg Heq. subst r.
      pose proof (adir_at_dom av i (Hroots g i t Hg)) as Hdom.
      apply elem_of_dom in Hdom as [b Hb]. congruence. }
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (b & e0 & Hb & He).
      apply adir_at_tview. rewrite (tview_delta_arm av i c).
      exists (hide_dots e0). rewrite lookup_insert_ne;
        [| intros Hc0; exact (Hnotroot g r t Hg (eq_sym Hc0))].
      rewrite (tview_lookup_Some av r b Hb) /tnode_of He //.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite (tview_delta_arm av i c) in Hr.
      apply (nreach_mono_edges (<[i := tabs_of c]> (tview av)) (tview av) r);
        [| exact Hr].
      intros x s c0 Hs. by rewrite (nstep_ins_leaf (tview av) i _ x s Hti Hleaf Hs).
  Qed.

  (* UNLINK'S ENTRY LEG: an edge leaves.  Reach only shrinks, so
     non-nesting rides; no row moves, so the roots stay directories. *)
  Lemma own_wf_unl_ent (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (dec : nat) (e : gmap fname Z) (nl : nat) :
    av !! d = Some (MkAnode (ADir e) nl) ->
    own_wf av own -> own_wf (delta_unl_ent d nm dec av) own.
  Proof using .
    intros Hd (Hwf & Hroots & Hnn).
    pose proof (tview_delta_unl_ent av d nm dec e nl Hd) as Hview.
    split; [exact (aview_tree_wf_unl_ent av d nm dec e nl Hd Hwf) |].
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (a & e0 & Ha & He).
      apply adir_at_tview. rewrite Hview.
      assert (Hr0 : tview av !! r = Some (ADir (hide_dots e0)))
        by (rewrite (tview_lookup_Some av r a Ha) /tnode_of He //).
      destruct (tedge_del_dir (tview av) d nm r (hide_dots e0) Hr0) as (e' & Hr').
      by exists e'.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      exact (nreach_mono_edges _ (tview av) r
               (fun x s c0 _ H0 => nstep_tedge_del_sub (tview av) d nm x s c0 H0)
               r' Hr).
  Qed.

  (* UNLINK'S TARGET LEG at the LAST link: the row leaves.  THE OWNER MAY
     NOT UNLINK A ROOT -- its own or anyone's -- which is the side
     condition the brief asked for, stated where it bites. *)
  Lemma own_wf_unl_tgt (av : aview) (own : gmap K (Z * ttree)) (tg : Z)
      (a : anode) :
    av !! tg = Some a -> an_nlink a = 1%nat -> aview_no_edge_to av tg ->
    (forall g r t, own !! g = Some (r, t) -> r <> tg) ->
    own_wf av own -> own_wf (delta_unl_tgt tg av) own.
  Proof using .
    intros Ha Hnl Hno Hnotroot (Hwf & Hroots & Hnn).
    pose proof (tview_delta_unl_tgt_last av tg a Ha Hnl) as Hview.
    split; [exact (aview_tree_wf_unl_tgt av tg a Ha Hnl Hno Hwf) |].
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (b & e0 & Hb & He).
      apply adir_at_tview. rewrite Hview lookup_delete_ne;
        [| intros Hc0; exact (Hnotroot g r t Hg (eq_sym Hc0))].
      exists (hide_dots e0).
      rewrite (tview_lookup_Some av r b Hb) /tnode_of He //.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      apply (nreach_mono_edges (delete tg (tview av)) (tview av) r); [| exact Hr].
      intros x s c0 Hs. destruct (decide (x = tg)) as [-> | Hx].
      + rewrite /nstep nents_unfold lookup_delete_eq /=. intros Hcc; discriminate.
      + rewrite (nstep_of_lookup _ (tview av) x s (lookup_delete_ne _ tg x
                   (fun Hcc => Hx (eq_sym Hcc)))). exact (fun H0 => H0).
  Qed.

  (* [own_wf_ent] -- create's PARENT leg ALONE -- IS LANDED, in section 8c
     (lane TL-3P).  The paragraph below is TL-3's pricing, kept because it
     is right about the PREMISE and wrong about the proof: the honest
     premise is indeed [aview_no_edge_to av i], but no induction of its
     own was needed ([nuniq_parent_ins_fresh]'s case analysis goes through
     with freshness replaced by the no-edge fact in the two mixed cases).
     What the leg does need beyond the fresh case is a SECOND credential
     the fresh case got free -- "the armed inum is nobody's root" -- see
     section 8's header.

     (TL-3's note, as it stood): NOT a one-liner (lane TL-3 priced it):
     [own_wf_ent], create's PARENT leg ALONE.  The other four legs above ride a landed
     [aview_tree_wf_*]; this one would need an [aview_tree_wf_ent], and its
     UNIQUE-PARENTHOOD conjunct is not available at the leg's own premises:
     [nuniq_parent_ins_fresh] wants the target inum ABSENT from the map,
     which is exactly what the ARM leg has just made false.  The honest
     premise is the armed-inum one -- [aview_no_edge_to av i], "nothing
     else names the row the arm installed" -- and no landed lemma proves
     [nuniq_parent (tedge_ins d nm i m)] from it: it needs its own
     induction on [nstep], the twin of [nuniq_parent_ins_fresh] at a
     present-but-unnamed row.  Until it lands the create MOVE is offered
     FUSED only ([AppTree.tree_move_create]), which is what the fires
     actually take when both legs are paid in one step. *)
End OwnPres.

(* ==== TL1-END ==== *)

(* ===================================================================== *)
(*  8.  THE PARENT PREFIX, AND CREATE'S PARENT LEG ALONE (lane TL-3P)     *)
(*                                                                        *)
(*  ADDITIVE: nothing above this line moves.  Two independent pieces,     *)
(*  both of which the create/unlink write family needs and neither of     *)
(*  which the read side did.                                             *)
(*                                                                        *)
(*  (a) RESOLUTION AT AN ARBITRARY ELEMENT LIST.  [resolves_from] is      *)
(*      stated at [path_elems pl] because every READ-side consumer walks  *)
(*      the whole path; nameiparent walks the PARENT PREFIX               *)
(*      ([FsAbsEra.np_elems pl] = [removelast (path_elems pl)]) and a pin *)
(*      for it needs the same three facts at that shorter list.  The      *)
(*      general form is the landed one with [path_elems pl] replaced by a *)
(*      parameter [ps], and [resolves_from] IS it at [path_elems pl]      *)
(*      ([tres_from_path], [reflexivity]) -- so this subsumes rather than *)
(*      competes, exactly as [PinnedObs] section 10 subsumes sections 5-6.*)
(*                                                                        *)
(*  (b) [own_wf_ent]: create's PARENT LEG ALONE, which the note at the    *)
(*      end of [OwnPres] recorded as PRICED AND NOT TAKEN.  It is taken   *)
(*      here.  THE PRICE WAS RIGHT ABOUT THE PREMISE AND WRONG ABOUT THE  *)
(*      PROOF: the honest premise is indeed [aview_no_edge_to av i]       *)
(*      (nothing else names the row the arm installed), but no            *)
(*      induction on [nstep] is needed -- [nuniq_parent_ins_fresh]'s own  *)
(*      case analysis goes through with the FRESHNESS of [i] replaced by  *)
(*      the no-edge fact in exactly the two mixed cases where freshness   *)
(*      was used (an old edge into [i] is refuted by the premise instead  *)
(*      of by [nclosed]).  What the leg DOES need beyond the fresh case   *)
(*      is a second premise the fresh case got for free: THE ARMED INUM   *)
(*      IS NOBODY'S ROOT.  With [i] absent that followed from the fact    *)
(*      that roots are rows of the view; at the leg's instant [i] IS a    *)
(*      row (an empty directory at count 1 is [adir_at]), so it is        *)
(*      stated, in                                                       *)
(*      [own_wf_unl_tgt]'s shape.  It is a credential from the ARM leg --  *)
(*      true because [own] does not move between the two legs and the     *)
(*      arm's own view had no row at [i].                                 *)
(* ===================================================================== *)

(* ---- 8a.  RESOLUTION AT AN ARBITRARY ELEMENT LIST ------------------- *)

Definition tres_from (t : ttree) (d : Z) (ps : list fname)
    : option (Z * absnode) :=
  match npath (tv_nodes t) d ps with
  | Some i => match tv_nodes t !! i with
              | Some n => Some (i, n)
              | None => None
              end
  | None => None
  end.

Definition tres_hops (t : ttree) (d : Z) (ps : list fname) : list Z :=
  nchain (tv_nodes t) d ps.

Lemma tres_from_path (t : ttree) (d : Z) (pl : list (bv 8)) :
  tres_from t d (path_elems pl) = resolves_from t d pl.
Proof. reflexivity. Qed.

Lemma tres_hops_path (t : ttree) (d : Z) (pl : list (bv 8)) :
  tres_hops t d (path_elems pl) = resolve_hops t d pl.
Proof. reflexivity. Qed.

(* the resolved node is a node of the tree -- which at the PARENT PREFIX
   is the fact an owner's move needs first: the directory the walk stops
   at is one the owner's own claim records. *)
Lemma tres_from_dom (t : ttree) (d i : Z) (n : absnode) (ps : list fname) :
  tres_from t d ps = Some (i, n) -> i ∈ dom (tv_nodes t).
Proof.
  rewrite /tres_from. destruct (npath (tv_nodes t) d ps) as [j |]; [| discriminate].
  destruct (tv_nodes t !! j) as [n0 |] eqn:Hn; [| discriminate].
  intros Hc. injection Hc as <- <-. apply elem_of_dom. by exists n0.
Qed.

(* a PREFIX of a proper path is proper -- what the parent-prefix walk
   needs of the program's own pure side condition *)
Lemma fs_proper_removelast (ps : list fname) :
  fs_proper ps -> fs_proper (removelast ps).
Proof.
  rewrite /fs_proper. induction ps as [| s ps IH]; [done |].
  intros Hf. apply Forall_cons in Hf as [Hs Hps].
  destruct ps as [| s' ps']; [constructor |].
  cbn [removelast]. apply Forall_cons. split; [exact Hs | exact (IH Hps)].
Qed.

(* [resolves_from_arun] at the parameter: same proof, line for line *)
Lemma tres_from_arun (av : aview) (r : Z) (t : ttree) (d i : Z)
    (n : absnode) (ps : list fname) :
  subtree av r = Some t -> fs_proper ps ->
  nreach (tview av) r d ->
  tres_from t d ps = Some (i, n) ->
  arun av d ps (tres_hops t d ps)
  /\ tres_hops t d ps !!! 0%nat = d
  /\ tres_hops t d ps !!! length ps = i
  /\ (exists a, av !! i = Some a /\ n = tnode_of a).
Proof.
  intros Ht Hp Hd Hres.
  pose proof (subtree_nodes_eq av r t Ht) as Hnodes.
  assert (Hwalk : npath (tv_nodes t) d ps = apath_at av d ps).
  { rewrite Hnodes /subtree_nodes (npath_nclose (tview av) r ps d Hp Hd).
    exact (npath_tview av d ps Hp). }
  assert (Hchain : tres_hops t d ps = nchain (tview av) d ps).
  { rewrite /tres_hops Hnodes /subtree_nodes.
    exact (nchain_nclose (tview av) r ps d Hp Hd). }
  rewrite /tres_from Hwalk in Hres.
  destruct (apath_at av d ps) as [j |] eqn:Hw; [| discriminate].
  destruct (tv_nodes t !! j) as [n0 |] eqn:Hn; [| discriminate].
  injection Hres as <- <-.
  assert (Hrun : arun av d ps (tres_hops t d ps)).
  { rewrite Hchain. exact (nchain_arun av d ps j Hp Hw). }
  split; [exact Hrun |].
  split; [exact (arun_head av d ps _ Hrun) |].
  split.
  - pose proof (arun_apath_tot av d ps _ Hrun) as Htot.
    rewrite Hw in Htot. by injection Htot as ->.
  - rewrite Hnodes in Hn. apply subtree_nodes_lookup_Some in Hn as ((a & Ha & ->) & _).
    by exists a.
Qed.

(* [subtree_resolves_pin] at the parameter *)
Lemma subtree_tres_pin (t : ttree) (d i : Z) (n : absnode) (ps : list fname) :
  fs_proper ps ->
  tres_from t d ps = Some (i, n) ->
  forall (av : aview) (r : Z),
    subtree av r = Some t -> nreach (tview av) r d ->
    arun av d ps (tres_hops t d ps)
    /\ tres_hops t d ps !!! 0%nat = d
    /\ tres_hops t d ps !!! length ps = i
    /\ (exists (n' : absnode) (k : nat),
          av !! i = Some (MkAnode n' k) /\ tabs_of n' = n).
Proof.
  intros Hp Hres av r Ht Hd.
  destruct (tres_from_arun av r t d i n ps Ht Hp Hd Hres)
    as (Hrun & H0 & Hlen & (a & Ha & Hn)).
  split; [exact Hrun |]. split; [exact H0 |]. split; [exact Hlen |].
  destruct a as [n0 k]. exists n0, k. split; [exact Ha |].
  by rewrite /tnode_of /= in Hn.
Qed.

(* ...AND AT A DIRECTORY, which is what the parent prefix ends at.  The
   projection is NOT the identity here -- the tree hides the dots -- so
   what comes back is the view's own entry map together with the fact
   that it agrees with the tree's on every PROPER name.  That is exactly
   what a create/unlink consumer reads ("is [nm] an entry of my
   parent?"), and no more is true. *)
Lemma tabs_of_dir_inv (n' : absnode) (ents : gmap fname Z) :
  tabs_of n' = ADir ents -> exists e, n' = ADir e /\ hide_dots e = ents.
Proof.
  destruct n' as [bs | e | ma mi]; cbn; try discriminate.
  intros H. injection H as <-. by exists e.
Qed.

Lemma subtree_tres_pin_dir (t : ttree) (d i : Z) (ents : gmap fname Z)
    (ps : list fname) :
  fs_proper ps ->
  tres_from t d ps = Some (i, ADir ents) ->
  forall (av : aview) (r : Z),
    subtree av r = Some t -> nreach (tview av) r d ->
    arun av d ps (tres_hops t d ps)
    /\ tres_hops t d ps !!! 0%nat = d
    /\ tres_hops t d ps !!! length ps = i
    /\ (exists (e : gmap fname Z) (k : nat),
          av !! i = Some (MkAnode (ADir e) k)
          /\ (forall s : fname, fs_pname s -> e !! s = ents !! s)).
Proof.
  intros Hp Hres av r Ht Hd.
  destruct (subtree_tres_pin t d i (ADir ents) ps Hp Hres av r Ht Hd)
    as (Hrun & H0 & Hlen & (n' & k & Ha & Hn)).
  destruct (tabs_of_dir_inv n' ents Hn) as (e & -> & He).
  split; [exact Hrun |]. split; [exact H0 |]. split; [exact Hlen |].
  exists e, k. split; [exact Ha |].
  intros s Hs. rewrite -He (hide_dots_lookup e s Hs) //.
Qed.

(* ---- 8b.  THE ARMED INUM IS NAMED BY NOTHING ------------------------ *)

(* THE ARM'S CREDENTIAL, PURELY.  A fresh inum is named by no entry (no
   entry dangles), and the arm itself installs a LEAF, so after the arm
   nothing names the armed row either.  This is the premise
   [aview_tree_wf_ent] below asks for, and the reason the entry-leg-first
   order is the one that works. *)
Lemma aview_no_edge_to_fresh (av : aview) (i : Z) :
  aview_closed av -> av !! i = None -> aview_no_edge_to av i.
Proof.
  intros Hcl Hi d s Hs Hst.
  destruct (Hcl d s i Hs Hst) as [a Ha]. congruence.
Qed.

(* ...and what it buys: a row nothing names is a row no root reaches.
   [nreach_fresh]'s twin at a row that IS there. *)
Lemma nreach_no_edge (av : aview) (r i : Z) :
  aview_no_edge_to av i -> i <> r -> ~ nreach (tview av) r i.
Proof.
  intros Hno Hne (p & Hp & Hw). destruct (list_snoc_inv p) as [-> | (q & s & ->)].
  { cbn in Hw. injection Hw as Hri. exact (Hne (eq_sym Hri)). }
  apply fs_proper_app in Hp as [_ Hs]. apply fs_proper_cons in Hs as [Hs _].
  rewrite npath_snoc in Hw.
  destruct (npath (tview av) r q) as [d |]; [| discriminate].
  rewrite (nstep_tview av d s Hs) in Hw. exact (Hno d s Hs Hw).
Qed.

Lemma aview_no_edge_to_arm (av : aview) (i : Z) (c : absnode) :
  aview_closed av -> av !! i = None -> tabs_leaf (tabs_of c) ->
  aview_no_edge_to (delta_arm i c av) i.
Proof.
  intros Hcl Hi Hleaf d s Hs.
  rewrite -(nstep_tview (delta_arm i c av) d s Hs) (tview_delta_arm av i c).
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  rewrite (nstep_ins_leaf (tview av) i (tabs_of c) d s Hti Hleaf Hs).
  rewrite (nstep_tview av d s Hs).
  exact (aview_no_edge_to_fresh av i Hcl Hi d s Hs).
Qed.

(* ---- 8b'.  ...AND THE ENTRY LEG'S OWN CREDENTIAL --------------------- *)

(* THE ENTRY-LEG-FIRST ORDER, MADE A THEOREM.  TL-1's note at
   [aview_no_edge_to] says the [nlink]-vs-edge-count tie "is what the
   entry-leg-first order gives"; here it is.  After unlink's ENTRY leg has
   cut [d.nm], NOTHING names the target -- not because of any count, but
   because UNIQUE PARENTHOOD says the edge just cut was the only one.  So
   unlink's target leg gets its own credential from its own first leg,
   exactly as create's parent leg gets one from the arm, and the tree
   layer never has to carry the count tie at all. *)
Lemma aview_no_edge_to_unl_ent (av : aview) (d : Z) (nm : fname) (dec : nat)
    (e : gmap fname Z) (nl : nat) (tg : Z) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = Some tg ->
  aview_uniq_parent av ->
  aview_no_edge_to (delta_unl_ent d nm dec av) tg.
Proof.
  intros Hnm Hd He Hu x s Hs Hst.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hdel : nstep (tview av) d nm = Some tg).
  { rewrite /nstep nents_unfold Htd /= (hide_dots_lookup e nm Hnm) He //. }
  assert (Hnone : nstep (tedge_del d nm (tview av)) d nm = None).
  { rewrite (nstep_tedge_del_at (tview av) d nm (hide_dots e) nm Htd).
    case_decide as Hc; [reflexivity | by destruct (Hc eq_refl)]. }
  rewrite -(nstep_tview (delta_unl_ent d nm dec av) x s Hs)
          (tview_delta_unl_ent av d nm dec e nl Hd) in Hst.
  pose proof (nstep_tedge_del_sub (tview av) d nm x s tg Hst) as Hold.
  destruct (Hu x s d nm tg Hs Hnm Hold Hdel) as [-> ->].
  rewrite Hnone in Hst. discriminate.
Qed.

(* ---- 8c.  THE PARENT LEG'S EDGE INSERT, AT A PRESENT TARGET --------- *)

(* [nstep_ins_fresh_inv]'s twin, and SIMPLER: at [x <> d] the insert does
   not touch the row at all, so nothing has to be said about the target's
   own row (the fresh case needed [nstep_leaf] at [i] because it had
   INSERTED that row). *)
Lemma nstep_ins_ent_inv (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (x : Z) (s : fname) (j : Z) :
  m !! d = Some (ADir e) ->
  nstep (tedge_ins d nm i m) x s = Some j ->
  (nstep m x s = Some j /\ ~ (x = d /\ s = nm)) \/ (x = d /\ s = nm /\ j = i).
Proof.
  intros Hd Hst. destruct (decide (x = d)) as [-> | Hx]; last first.
  { left. rewrite (nstep_of_lookup _ m x s (tedge_ins_lookup_ne m d nm i x Hx))
      in Hst. split; [exact Hst |]. intros [Hc _]. exact (Hx Hc). }
  rewrite (nstep_tedge_ins_at m d nm i e s Hd) in Hst.
  case_decide as Hs.
  - right. injection Hst as <-. by repeat split.
  - left. split; [exact Hst |]. intros [_ Hc]. exact (Hs Hc).
Qed.

Lemma nuniq_parent_ins_ent (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) :
  m !! d = Some (ADir e) ->
  (forall (x : Z) (s : fname), fs_pname s -> nstep m x s <> Some i) ->
  nuniq_parent m -> nuniq_parent (tedge_ins d nm i m).
Proof.
  intros Hd Hno Hu d1 s1 d2 s2 j Hs1 Hs2 H1 H2.
  destruct (nstep_ins_ent_inv m d nm i e d1 s1 j Hd H1)
    as [[Ha1 _] | (-> & -> & Hj1)].
  - destruct (nstep_ins_ent_inv m d nm i e d2 s2 j Hd H2)
      as [[Ha2 _] | (-> & -> & Hj2)].
    + exact (Hu _ _ _ _ _ Hs1 Hs2 Ha1 Ha2).
    + exfalso. subst j. exact (Hno d1 s1 Hs1 Ha1).
  - destruct (nstep_ins_ent_inv m d nm i e d2 s2 j Hd H2)
      as [[Ha2 _] | (-> & -> & Hj2)].
    + exfalso. subst j. exact (Hno d2 s2 Hs2 Ha2).
    + by split.
Qed.

Lemma dom_tedge_ins_eq (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z) :
  dom (tedge_ins d nm i m) = dom m.
Proof.
  rewrite /tedge_ins. destruct (m !! d) as [n |] eqn:E; [| done].
  destruct n as [| e |]; [done | | done].
  assert (Hd : d ∈ dom m) by (apply elem_of_dom; by eexists).
  rewrite dom_insert_L. set_solver.
Qed.

Lemma nclosed_ins_ent (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) :
  m !! d = Some (ADir e) -> i ∈ dom m -> nclosed m ->
  nclosed (tedge_ins d nm i m).
Proof.
  intros Hd Hi Hn x s j Hs Hst. rewrite dom_tedge_ins_eq.
  destruct (nstep_ins_ent_inv m d nm i e x s j Hd Hst)
    as [[Ha _] | (_ & _ & ->)]; [exact (Hn x s j Hs Ha) | exact Hi].
Qed.

(* the reach inversion: the target is a LEAF, so the only node newly
   reachable is the target itself *)
Lemma nreach_ins_ent_inv (m : gmap Z absnode) (r d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) :
  m !! d = Some (ADir e) -> m !! i = Some c -> tabs_leaf c ->
  forall j, nreach (tedge_ins d nm i m) r j -> nreach m r j \/ j = i.
Proof.
  intros Hd Hi Hleaf.
  apply (nreach_closed_ind _ r (fun j => nreach m r j \/ j = i)
           (or_introl (nreach_refl m r))).
  intros d0 s c0 Hd0 Hs Hst.
  destruct (nstep_ins_ent_inv m d nm i e d0 s c0 Hd Hst)
    as [[Ha _] | (_ & _ & ->)]; [| by right].
  destruct Hd0 as [Hd0 | ->].
  - left. exact (nreach_hop m r d0 s c0 Hd0 Hs Ha).
  - exfalso. rewrite (nstep_leaf m i c s Hi Hleaf Hs) in Ha. discriminate.
Qed.

Lemma aview_tree_wf_ent (av : aview) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (nl : nat) (a : anode) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> av !! i = Some a ->
  aview_no_edge_to av i ->
  aview_tree_wf av -> aview_tree_wf (delta_ent d nm i av).
Proof.
  intros Hnm Hd Hi Hno [Hu Hc].
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hti : tview av !! i = Some (tnode_of a))
    by (rewrite (tview_lookup_Some av i a Hi) //).
  assert (Hidom : i ∈ dom (tview av)) by (apply elem_of_dom; by eexists).
  assert (Hnon : forall (x : Z) (s : fname), fs_pname s ->
                   nstep (tview av) x s <> Some i).
  { intros x s Hs. rewrite (nstep_tview av x s Hs). exact (Hno x s Hs). }
  rewrite /aview_uniq_parent aview_closed_nstep in Hu, Hc.
  rewrite /aview_tree_wf /aview_uniq_parent aview_closed_nstep
          (tview_delta_ent av d nm i e nl a Hnm Hd Hi).
  split.
  - exact (nuniq_parent_ins_ent (tview av) d nm i _ Htd Hnon Hu).
  - exact (nclosed_ins_ent (tview av) d nm i _ Htd Hidom Hc).
Qed.

(* ...and the row at the era's root survives for free: the leg moves ONE
   row and leaves it a directory. *)
Lemma adir_at_delta_ent (av : aview) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (nl : nat) (a : anode) (r : Z) :
  av !! d = Some (MkAnode (ADir e) nl) -> av !! i = Some a ->
  adir_at av r -> adir_at (delta_ent d nm i av) r.
Proof.
  intros Hd Hi (b & e0 & Hb & He). destruct a as [c0 k0].
  destruct (decide (r = d)) as [-> | Hne].
  - exists (MkAnode (ADir (<[nm := i]> e)) (nl + acre_bump c0)%nat),
           (<[nm := i]> e).
    split; [exact (delta_ent_lookup_at av d nm i e nl c0 k0 Hd Hi)
           | reflexivity].
  - exists b, e0. split; [| exact He].
    rewrite (delta_ent_lookup_same av d nm i r Hne). exact Hb.
Qed.

Section OwnPresEnt.
  Context {K : Type} `{Countable K}.

  (* CREATE'S PARENT LEG ALONE.  The two premises the fused lemma got for
     free are stated: nothing names the armed row, and the armed inum is
     nobody's root.  Both are the ARM leg's own facts, carried forward --
     [own] does not move between the legs, and at the arm's view [i] was
     not a row at all. *)
  Lemma own_wf_ent (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (i : Z) (a : anode) (e : gmap fname Z) (nl : nat) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) ->
    av !! i = Some a -> tabs_leaf (tnode_of a) ->
    aview_no_edge_to av i ->
    (forall g r t, own !! g = Some (r, t) -> r <> i) ->
    own_wf av own -> own_wf (delta_ent d nm i av) own.
  Proof using .
    intros Hnm Hd Hi Hleaf Hno Hnotroot (Hwf & Hroots & Hnn).
    destruct Hwf as [Hu Hcl].
    assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
      by (rewrite (tview_lookup_Some av d _ Hd) //).
    assert (Hti : tview av !! i = Some (tnode_of a))
      by (rewrite (tview_lookup_Some av i a Hi) //).
    pose proof (tview_delta_ent av d nm i e nl a Hnm Hd Hi) as Hview.
    split; [exact (aview_tree_wf_ent av d nm i e nl a Hnm Hd Hi Hno
                     (conj Hu Hcl)) |].
    split.
    - intros g r t Hg. destruct (Hroots g r t Hg) as (b & e0 & Hb & He).
      apply adir_at_tview. rewrite Hview.
      assert (Hr0 : tview av !! r = Some (ADir (hide_dots e0)))
        by (rewrite (tview_lookup_Some av r b Hb) /tnode_of He //).
      destruct (tedge_ins_dir (tview av) d nm i r (hide_dots e0) Hr0)
        as (e' & Hr').
      by exists e'.
    - intros g g' r t r' t' Hne Hg Hg' Hr. apply (Hnn g g' r t r' t' Hne Hg Hg').
      rewrite Hview in Hr.
      destruct (nreach_ins_ent_inv (tview av) r d nm i (tnode_of a)
                  (hide_dots e) Htd Hti Hleaf r' Hr) as [Hc0 | Hc0];
        [exact Hc0 |].
      exfalso. exact (Hnotroot g' r' t' Hg' Hc0).
  Qed.

  (* ...AND THE CREDENTIAL, DISCHARGED, FOR EVERY CHILD BUT A DIRECTORY.
     An owner's root is [adir_at] by [own_wf]'s own roots conjunct, so a
     child that is NOT a directory in the view is nobody's root and the
     premise above is free.  That covers create's two non-directory
     children -- open(O_CREATE)'s empty FILE and mknod's DEVICE.  mkdir's
     child IS a directory (empty but for its dots, so still
     [tabs_leaf]), and for it the credential has to be threaded from the
     ARM leg, whose own view had no row at [i] at all -- the same kind of
     credential [FsAbsCreateFire]'s UNARM leg needs, and a kernel-tier
     lane either way. *)
  Lemma own_wf_ent_leaf (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (i : Z) (a : anode) (e : gmap fname Z) (nl : nat) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) ->
    av !! i = Some a -> tabs_leaf (tnode_of a) ->
    ~ adir_at av i ->
    aview_no_edge_to av i ->
    own_wf av own -> own_wf (delta_ent d nm i av) own.
  Proof using .
    intros Hnm Hd Hi Hleaf Hnd Hno Hwf.
    apply (own_wf_ent av own d nm i a e nl Hnm Hd Hi Hleaf Hno); [| exact Hwf].
    intros g r t Hg Heq. subst r. destruct Hwf as (_ & Hroots & _).
    exact (Hnd (Hroots g i t Hg)).
  Qed.

  (* UNLINK'S TARGET LEG AT THE LAST LINK, WITH TL-2's WALL HALF LIFTED.
     [own_wf_unl_tgt] asks for "the row is nobody's root", which TL-2
     recorded as a fact about the ownership map that no mover holds.  At a
     NON-DIRECTORY target it is not about the map at all: an owner's root
     is [adir_at] by [own_wf]'s own roots conjunct, so a file's or a
     device's row is nobody's root and the premise is free -- the same
     trick [own_wf_ent_leaf] plays.  A DIRECTORY's last link (which is
     [rmdir]-shaped) keeps TL-2's wall. *)
  Lemma own_wf_unl_tgt_nodir (av : aview) (own : gmap K (Z * ttree)) (tg : Z)
      (a : anode) :
    av !! tg = Some a -> an_nlink a = 1%nat -> aview_no_edge_to av tg ->
    ~ adir_at av tg ->
    own_wf av own -> own_wf (delta_unl_tgt tg av) own.
  Proof using .
    intros Ha Hnl Hno Hnd Hwf.
    apply (own_wf_unl_tgt av own tg a Ha Hnl Hno); [| exact Hwf].
    intros g r t Hg Heq. subst r. destruct Hwf as (_ & Hroots & _).
    exact (Hnd (Hroots g tg t Hg)).
  Qed.

End OwnPresEnt.

(* ===================================================================== *)
(*  9.  THE ROOTED VIEW (lane TL-3R; design/user-tree.md section 7.8)     *)
(*                                                                        *)
(*  ADDITIVE: nothing above this line moves.  The RULING of section 7.8   *)
(*  adopts TWO PURE conjuncts for the tree claim, and this section is     *)
(*  their theory: the definitions, and their preservation at every leg    *)
(*  the claim offers a step for.                                         *)
(*                                                                        *)
(*  WHY THE SOURCE FORM (section 7.7, and it is not a detail): the        *)
(*  obvious reading -- "every proper edge's TARGET is reachable" -- is    *)
(*  NOT preserved by unlink's entry leg (cut [d.nm -> tg] while a second, *)
(*  unreachable directory still names [tg], and that surviving edge's     *)
(*  target is now unreachable).  The SOURCE form has no such hole,        *)
(*  because an unreachable source is what it forbids outright, and it     *)
(*  still gives the consumer its conclusion in one [nreach_hop].          *)
(*                                                                        *)
(*  WHAT IT BUYS (the whole point): at an owner of "/" the claim's own    *)
(*  conjuncts turn the ARM's pure receipt -- [i] is no node of the        *)
(*  owner's OWN fixed tree -- into [aview_no_edge_to av i] at the PARENT  *)
(*  LEG's own view, which is [own_wf_ent]'s first credential and the one  *)
(*  premise TL-3C left the create family owing.  See section 9d.          *)
(* ===================================================================== *)

(* ---- 9a.  THE TWO CONJUNCTS ---------------------------------------- *)

(* THE LIVE NAMESPACE HAS NO ORPHAN DIRECTORY HOLDING A PROPER ENTRY.
   True of xv6 for two reasons the design already carries: a directory is
   unlinked only when it is EMPTY ([SysUnlinkDefs.unl_pre]'s [dots_only]
   clause), and create's fresh directory holds only its dots until its
   parent leg files it. *)
Definition aview_rooted (av : aview) : Prop :=
  forall (d : Z) (s : fname) (i : Z),
    fs_pname s -> astep av d s = Some i ->
    nreach (tview av) FsImg.ROOTINO d.

(* ...and the same one notch up: EVERY OWNER'S ROOT IS REACHABLE.  The
   era's first deed is minted at [ROOTINO] itself and [tree_grant] births
   a child at a sub-root of its parent's tree, so the ownership map never
   acquires an unreachable root. *)
Section OwnRooted.
  Context {K : Type} `{Countable K}.

  Definition own_rooted (av : aview) (own : gmap K (Z * ttree)) : Prop :=
    forall (g : K) (root : Z) (t : ttree),
      own !! g = Some (root, t) -> nreach (tview av) FsImg.ROOTINO root.
End OwnRooted.

(* ---- 9b.  THE WORKHORSE: A LEG WHOSE PROPER EDGES DO NOT MOVE ------- *)

(* [nreach] and [astep] both read the projected map through PROPER names
   only, so a leg that leaves [nstep] alone on proper names leaves both
   conjuncts alone.  SIX of the landed legs are this lemma: mkdir's two
   dot legs, link's target leg, unlink's target leg above the last link,
   write and truncate (a content edit at a FILE row moves no [nents]),
   and create's ARM (a leaf row appears at an inum nothing names). *)
Lemma nreach_step_cong (av av' : aview) (r j : Z) :
  (forall (x : Z) (s : fname), fs_pname s ->
     nstep (tview av') x s = nstep (tview av) x s) ->
  nreach (tview av) r j -> nreach (tview av') r j.
Proof.
  intros Hag. apply nreach_mono_edges.
  intros x s0 c Hs0 H0. rewrite (Hag x s0 Hs0) //.
Qed.

Lemma aview_rooted_step_cong (av av' : aview) :
  (forall (x : Z) (s : fname), fs_pname s ->
     nstep (tview av') x s = nstep (tview av) x s) ->
  aview_rooted av -> aview_rooted av'.
Proof.
  intros Hag Hro d s i Hs Hst.
  assert (Hold : astep av d s = Some i).
  { rewrite -(nstep_tview av d s Hs) -(Hag d s Hs) (nstep_tview av' d s Hs) //. }
  exact (nreach_step_cong av av' FsImg.ROOTINO d Hag (Hro d s i Hs Hold)).
Qed.

Lemma aview_rooted_cong (av av' : aview) :
  tview av' = tview av -> aview_rooted av -> aview_rooted av'.
Proof.
  intros Hv. apply aview_rooted_step_cong. intros x s _. rewrite Hv //.
Qed.

(* ---- 9c.  PRESERVATION, LEG BY LEG --------------------------------- *)

(* the four legs the tree does not see at all *)
Lemma aview_rooted_dots (av : aview) (i d : Z) :
  aview_rooted av -> aview_rooted (delta_dots i d av).
Proof. exact (aview_rooted_cong av _ (tview_delta_dots av i d)). Qed.

Lemma aview_rooted_dot (av : aview) (i : Z) :
  aview_rooted av -> aview_rooted (delta_dot i av).
Proof. exact (aview_rooted_cong av _ (tview_delta_dot av i)). Qed.

Lemma aview_rooted_link_tgt (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> aview_rooted av -> aview_rooted (delta_link_tgt t a av).
Proof. intros Ha. exact (aview_rooted_cong av _ (tview_delta_link_tgt av t a Ha)). Qed.

Lemma aview_rooted_unl_tgt_live (av : aview) (t : Z) (a : anode) :
  av !! t = Some a -> (2 <= an_nlink a)%nat ->
  aview_rooted av -> aview_rooted (delta_unl_tgt t av).
Proof.
  intros Ha Hnl.
  exact (aview_rooted_cong av _ (tview_delta_unl_tgt_live av t a Ha Hnl)).
Qed.

(* WRITE and TRUNCATE: a content edit at a FILE row, so [nents] does not
   move at any node *)
Lemma aview_rooted_write (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  aview_rooted av -> aview_rooted (delta_write i off new av).
Proof.
  intros Hi. apply aview_rooted_step_cong. intros x s Hs.
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  rewrite (tview_delta_write av i off new bs0 nl Hi).
  exact (nstep_content_edit (tview av) i (AFile (blk_splice off new bs0))
           (AFile bs0) x s Hti eq_refl).
Qed.

Lemma aview_rooted_trunc (av : aview) (i : Z) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  aview_rooted av -> aview_rooted (delta_trunc i av).
Proof.
  intros Hi. apply aview_rooted_step_cong. intros x s Hs.
  assert (Hti : tview av !! i = Some (AFile bs0))
    by (rewrite (tview_lookup_Some av i _ Hi) //).
  rewrite (tview_delta_trunc av i bs0 nl Hi).
  exact (nstep_content_edit (tview av) i (AFile []) (AFile bs0) x s Hti eq_refl).
Qed.

(* CREATE'S ARM: a LEAF row appears at an inum nothing names, so not one
   edge of the namespace moves.  [av !! i = None] is the premise the
   mover already holds (design section 7.8's "two new premises"). *)
Lemma aview_rooted_arm (av : aview) (i : Z) (c : absnode) :
  av !! i = None -> tabs_leaf (tabs_of c) ->
  aview_rooted av -> aview_rooted (delta_arm i c av).
Proof.
  intros Hi Hleaf. apply aview_rooted_step_cong. intros x s Hs.
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  rewrite (tview_delta_arm av i c).
  exact (nstep_ins_leaf (tview av) i (tabs_of c) x s Hti Hleaf Hs).
Qed.

(* ---- CREATE'S PARENT LEG: one edge appears, AT A REACHABLE SOURCE --- *)

(* the edge insert at a FREE name adds edges and removes none, so
   [nreach] can only GROW *)
Lemma nstep_tedge_ins_sub (m : gmap Z absnode) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (x : Z) (s : fname) (c : Z) :
  m !! d = Some (ADir e) -> e !! nm = None ->
  nstep m x s = Some c -> nstep (tedge_ins d nm i m) x s = Some c.
Proof.
  intros Hd Hnone Hst. destruct (decide (x = d)) as [-> | Hx]; last first.
  { rewrite (nstep_of_lookup _ m x s (tedge_ins_lookup_ne m d nm i x Hx)).
    exact Hst. }
  rewrite (nstep_tedge_ins_at m d nm i e s Hd). case_decide as Hs.
  - exfalso. subst s. rewrite /nstep nents_unfold Hd /= Hnone in Hst. discriminate.
  - exact Hst.
Qed.

Lemma nreach_tedge_ins_mono (m : gmap Z absnode) (r d : Z) (nm : fname)
    (i : Z) (e : gmap fname Z) :
  m !! d = Some (ADir e) -> e !! nm = None ->
  forall j, nreach m r j -> nreach (tedge_ins d nm i m) r j.
Proof.
  intros Hd Hnone. apply nreach_mono_edges.
  intros x s c Hs. exact (nstep_tedge_ins_sub m d nm i e x s c Hd Hnone).
Qed.

(* THE LEG THE WHOLE LANE IS FOR.  [d] reachable is what the owner has:
   [d] is a node of its own tree and its root is reachable
   ([own_rooted] + [subtree_dom_reach]). *)
Lemma aview_rooted_ent (av : aview) (d : Z) (nm : fname) (i : Z)
    (e : gmap fname Z) (nl : nat) (a : anode) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = Some a ->
  nreach (tview av) FsImg.ROOTINO d ->
  aview_rooted av -> aview_rooted (delta_ent d nm i av).
Proof.
  intros Hnm Hd Hnone Hi Hrd Hro.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hhn : hide_dots e !! nm = None)
    by (rewrite (hide_dots_lookup e nm Hnm) //).
  pose proof (tview_delta_ent av d nm i e nl a Hnm Hd Hi) as Hview.
  intros x s j Hs Hst. rewrite Hview.
  rewrite -(nstep_tview (delta_ent d nm i av) x s Hs) Hview in Hst.
  destruct (nstep_ins_ent_inv (tview av) d nm i (hide_dots e) x s j Htd Hst)
    as [[Hold _] | (-> & _ & _)].
  - apply (nreach_tedge_ins_mono (tview av) FsImg.ROOTINO d nm i (hide_dots e)
             Htd Hhn). rewrite (nstep_tview av x s Hs) in Hold.
    exact (Hro x s j Hs Hold).
  - exact (nreach_tedge_ins_mono (tview av) FsImg.ROOTINO d nm i (hide_dots e)
             Htd Hhn d Hrd).
Qed.

(* ...AND THE FUSED CREATE, which is the arm followed by the parent leg
   ([FsAbsDelta.delta_create_split]) *)
Lemma aview_rooted_create (av : aview) (d : Z) (nm : fname) (i : Z)
    (c : absnode) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = None -> tabs_leaf (tabs_of c) ->
  nreach (tview av) FsImg.ROOTINO d ->
  aview_rooted av -> aview_rooted (delta_create d nm i c av).
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hrd Hro.
  assert (Hne : d <> i) by (intros ->; rewrite Hd in Hi; discriminate).
  assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
  assert (Harm : forall (x : Z) (s : fname), fs_pname s ->
            nstep (tview (delta_arm i c av)) x s = nstep (tview av) x s).
  { intros x s Hs. rewrite (tview_delta_arm av i c).
    exact (nstep_ins_leaf (tview av) i (tabs_of c) x s Hti Hleaf Hs). }
  rewrite (delta_create_split av d nm i c e nl Hd Hi).
  apply (aview_rooted_ent (delta_arm i c av) d nm i e nl (MkAnode c 1%nat)
           Hnm).
  - rewrite (delta_arm_lookup_same av i c d Hne) //.
  - exact Hnone.
  - apply delta_arm_lookup_at.
  - exact (nreach_step_cong av (delta_arm i c av) FsImg.ROOTINO d Harm Hrd).
  - exact (aview_rooted_arm av i c Hi Hleaf Hro).
Qed.

(* ---- UNLINK'S ENTRY LEG: one edge leaves, at a TARGET WITH NO PROPER
   OUT-EDGE ([SysUnlinkDefs.unl_pre]'s own [dots_only] clause).  Then no
   path to any SOURCE used the cut edge, because a path through [tg]
   would have to LEAVE [tg]. ---------------------------------------- *)

Lemma nreach_tedge_del_keep (m : gmap Z absnode) (r d : Z) (nm : fname)
    (e : gmap fname Z) (tg : Z) :
  m !! d = Some (ADir e) -> e !! nm = Some tg ->
  (forall s : fname, fs_pname s -> nstep m tg s = None) ->
  forall j, nreach m r j -> nreach (tedge_del d nm m) r j \/ j = tg.
Proof.
  intros Hd He Hleaf.
  apply (nreach_closed_ind m r
           (fun j => nreach (tedge_del d nm m) r j \/ j = tg)
           (or_introl (nreach_refl (tedge_del d nm m) r))).
  intros d0 s c [Hd0 | ->] Hs Hst; last first.
  { exfalso. rewrite (Hleaf s Hs) in Hst. discriminate. }
  destruct (decide (d0 = d)) as [-> | Hx]; last first.
  { left. apply (nreach_hop (tedge_del d nm m) r d0 s c Hd0 Hs).
    rewrite (nstep_of_lookup _ m d0 s (tedge_del_lookup_ne m d nm d0 Hx)).
    exact Hst. }
  destruct (decide (s = nm)) as [-> | Hs2].
  { right. rewrite /nstep nents_unfold Hd /= He in Hst. by injection Hst as <-. }
  left. apply (nreach_hop (tedge_del d nm m) r d s c Hd0 Hs).
  rewrite (nstep_tedge_del_at m d nm e s Hd).
  case_decide as Hc; [by destruct (Hs2 Hc) | exact Hst].
Qed.

(* a node with no proper out-edge reaches nothing but itself -- the fact
   that makes a [dots_only] target's removal local *)
Lemma nreach_leaf_eq (m : gmap Z absnode) (x j : Z) :
  (forall s : fname, fs_pname s -> nstep m x s = None) -> nreach m x j -> j = x.
Proof.
  intros Hl (p & Hp & Hw). destruct p as [| s p].
  - cbn in Hw. by injection Hw as <-.
  - apply fs_proper_cons in Hp as [Hs _].
    rewrite npath_cons (Hl s Hs) in Hw. discriminate.
Qed.

Lemma aview_rooted_unl_ent (av : aview) (d : Z) (nm : fname) (dec : nat)
    (e : gmap fname Z) (nl : nat) (tg : Z) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = Some tg ->
  (forall s : fname, fs_pname s -> astep av tg s = None) ->
  aview_rooted av -> aview_rooted (delta_unl_ent d nm dec av).
Proof.
  intros Hnm Hd He Hlf Hro.
  assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
    by (rewrite (tview_lookup_Some av d _ Hd) //).
  assert (Hhe : hide_dots e !! nm = Some tg)
    by (rewrite (hide_dots_lookup e nm Hnm) //).
  assert (Hleaf : forall s : fname, fs_pname s -> nstep (tview av) tg s = None).
  { intros s Hs. rewrite (nstep_tview av tg s Hs). exact (Hlf s Hs). }
  pose proof (tview_delta_unl_ent av d nm dec e nl Hd) as Hview.
  intros x s j Hs Hst. rewrite Hview.
  rewrite -(nstep_tview (delta_unl_ent d nm dec av) x s Hs) Hview in Hst.
  pose proof (nstep_tedge_del_sub (tview av) d nm x s j Hst) as Hold.
  destruct (nreach_tedge_del_keep (tview av) FsImg.ROOTINO d nm (hide_dots e)
              tg Htd Hhe Hleaf x
              (Hro x s j Hs (eq_trans (eq_sym (nstep_tview av x s Hs)) Hold)))
    as [Hk | ->]; [exact Hk |].
  exfalso. rewrite (Hleaf s Hs) in Hold. discriminate.
Qed.

(* ---- UNLINK'S TARGET LEG AT THE LAST LINK (and the child's UNARM):
   the ROW leaves.  Nothing names it ([aview_no_edge_to], which the
   entry leg itself proves), so no path to any surviving source went
   through it. ------------------------------------------------------ *)

Lemma nreach_delete_keep (m : gmap Z absnode) (i r : Z) :
  (forall (x : Z) (s : fname), fs_pname s -> nstep m x s <> Some i) ->
  r <> i ->
  forall j, nreach m r j -> nreach (delete i m) r j /\ j <> i.
Proof.
  intros Hno Hr.
  apply (nreach_closed_ind m r
           (fun j => nreach (delete i m) r j /\ j <> i)
           (conj (nreach_refl (delete i m) r) Hr)).
  intros d s c [Hd Hdi] Hs Hst.
  assert (Hsub : nstep (delete i m) d s = Some c).
  { rewrite (nstep_of_lookup _ m d s
               (lookup_delete_ne _ i d (fun Hc => Hdi (eq_sym Hc)))).
    exact Hst. }
  split; [exact (nreach_hop (delete i m) r d s c Hd Hs Hsub) |].
  intros ->. exact (Hno d s Hs Hst).
Qed.

Lemma aview_rooted_unl_tgt (av : aview) (tg : Z) (a : anode) :
  av !! tg = Some a -> an_nlink a = 1%nat ->
  aview_no_edge_to av tg -> tg <> FsImg.ROOTINO ->
  aview_rooted av -> aview_rooted (delta_unl_tgt tg av).
Proof.
  intros Ha Hnl Hno Hrt Hro.
  assert (Hnon : forall (x : Z) (s : fname), fs_pname s ->
            nstep (tview av) x s <> Some tg).
  { intros x s Hs. rewrite (nstep_tview av x s Hs). exact (Hno x s Hs). }
  pose proof (tview_delta_unl_tgt_last av tg a Ha Hnl) as Hview.
  intros x s j Hs Hst. rewrite Hview.
  rewrite -(nstep_tview (delta_unl_tgt tg av) x s Hs) Hview in Hst.
  assert (Hold : nstep (tview av) x s = Some j).
  { destruct (decide (x = tg)) as [-> | Hx].
    - rewrite /nstep nents_unfold lookup_delete_eq /= in Hst. discriminate.
    - rewrite (nstep_of_lookup _ (tview av) x s
                 (lookup_delete_ne _ tg x (fun Hc => Hx (eq_sym Hc)))) in Hst.
      exact Hst. }
  destruct (nreach_delete_keep (tview av) tg FsImg.ROOTINO Hnon
              (fun Hc => Hrt (eq_sym Hc)) x
              (Hro x s j Hs (eq_trans (eq_sym (nstep_tview av x s Hs)) Hold)))
    as [Hk _].
  exact Hk.
Qed.

(* the same row removal at create's UNARM leg (design section 7.4's
   wall 2, closed by the same credential at the same instant) *)
Lemma aview_rooted_unarm (av : aview) (i : Z) :
  aview_no_edge_to av i -> i <> FsImg.ROOTINO ->
  aview_rooted av -> aview_rooted (delta_unarm i av).
Proof.
  intros Hno Hri Hro.
  assert (Hnon : forall (x : Z) (s : fname), fs_pname s ->
            nstep (tview av) x s <> Some i).
  { intros x s Hs. rewrite (nstep_tview av x s Hs). exact (Hno x s Hs). }
  pose proof (tview_delta_unarm av i) as Hview.
  intros x s j Hs Hst. rewrite Hview.
  rewrite -(nstep_tview (delta_unarm i av) x s Hs) Hview in Hst.
  assert (Hold : nstep (tview av) x s = Some j).
  { destruct (decide (x = i)) as [-> | Hx].
    - rewrite /nstep nents_unfold lookup_delete_eq /= in Hst. discriminate.
    - rewrite (nstep_of_lookup _ (tview av) x s
                 (lookup_delete_ne _ i x (fun Hc => Hx (eq_sym Hc)))) in Hst.
      exact Hst. }
  destruct (nreach_delete_keep (tview av) i FsImg.ROOTINO Hnon
              (fun Hc => Hri (eq_sym Hc)) x
              (Hro x s j Hs (eq_trans (eq_sym (nstep_tview av x s Hs)) Hold)))
    as [Hk _].
  exact Hk.
Qed.

(* ---- 9d.  THE SECOND CONJUNCT, LEG BY LEG -------------------------- *)

(* ---- 9f.  WHAT THE ROOTED VIEW BUYS AT CREATE'S PARENT LEG --------- *)
(*                                                                       *)
(*  THE DERIVATION (design section 7.8).  The ARM's receipt records the   *)
(*  PURE fact [i ∉ dom (tv_nodes t)] -- a proposition about the OWNER'S   *)
(*  OWN FIXED TREE, which is why WALL C does not apply to it (WALL C is   *)
(*  about the whole VIEW, and no monotone reading of "nothing names [i]"  *)
(*  survives an arbitrary delta).  At the parent leg's own view the       *)
(*  claim's two conjuncts turn it back into the two credentials           *)
(*  [own_wf_ent] asks for.                                               *)

(* the converse of [subtree_dom_reach]: a REACHABLE row of the view is a
   node of the subtree *)
Lemma subtree_reach_dom (av : aview) (r : Z) (t : ttree) (i : Z) :
  subtree av r = Some t -> i ∈ dom av -> nreach (tview av) r i ->
  i ∈ dom (tv_nodes t).
Proof.
  intros Ht Hd Hr. rewrite (subtree_nodes_eq av r t Ht).
  apply elem_of_dom_subtree_nodes. exact (conj Hd Hr).
Qed.

(* ...and the two readings of a subtree's domain the arm's supplier needs *)
Lemma subtree_dom_view (av : aview) (r : Z) (t : ttree) (i : Z) :
  subtree av r = Some t -> i ∈ dom (tv_nodes t) -> i ∈ dom av.
Proof.
  intros Ht Hi. rewrite (subtree_nodes_eq av r t Ht) in Hi.
  exact (proj1 (proj1 (elem_of_dom_subtree_nodes av r i) Hi)).
Qed.

Lemma subtree_root_dom (av : aview) (r : Z) (t : ttree) :
  subtree av r = Some t -> r ∈ dom (tv_nodes t).
Proof.
  intros Ht. apply (subtree_reach_dom av r t r Ht);
    [apply adir_at_dom; exact (proj1 (subtree_Some_inv av r t Ht))
    | apply nreach_refl].
Qed.

(* CREDENTIAL ONE: nothing names the armed row.  If something did, the
   rooted view would make its SOURCE reachable, hence the armed row
   itself, hence a node of the root owner's tree -- which the receipt
   refutes. *)
Lemma aview_no_edge_to_rooted (av : aview) (t : ttree) (i : Z) :
  aview_rooted av -> aview_closed av ->
  subtree av FsImg.ROOTINO = Some t -> i ∉ dom (tv_nodes t) ->
  aview_no_edge_to av i.
Proof.
  intros Hro Hcl Ht Hni d s Hs Hst. apply Hni.
  apply (subtree_reach_dom av FsImg.ROOTINO t i Ht).
  - destruct (Hcl d s i Hs Hst) as [a Ha]. apply elem_of_dom. by exists a.
  - apply (nreach_hop (tview av) FsImg.ROOTINO d s i (Hro d s i Hs Hst) Hs).
    rewrite (nstep_tview av d s Hs) //.
Qed.

(* CREDENTIAL TWO -- the one [own_wf_ent_leaf] could only pay at a
   NON-DIRECTORY child, and which mkdir's directory child owed: THE ARMED
   INUM IS NOBODY'S ROOT.  [own_rooted] makes every owner's root
   reachable, and a reachable row of the view is a node of the root
   owner's tree. *)
Lemma root_not_armed_rooted (av : aview) (t : ttree) (i root : Z) :
  subtree av FsImg.ROOTINO = Some t -> i ∉ dom (tv_nodes t) ->
  i ∈ dom av -> nreach (tview av) FsImg.ROOTINO root -> root <> i.
Proof.
  intros Ht Hni Hd Hr Heq. subst root. apply Hni.
  exact (subtree_reach_dom av FsImg.ROOTINO t i Ht Hd Hr).
Qed.

Section OwnRootedPres.
  Context {K : Type} `{Countable K}.

  Lemma own_rooted_step_cong (av av' : aview) (own : gmap K (Z * ttree)) :
    (forall (x : Z) (s : fname), fs_pname s ->
       nstep (tview av') x s = nstep (tview av) x s) ->
    own_rooted av own -> own_rooted av' own.
  Proof using .
    intros Hag Hro g root t Hg.
    exact (nreach_step_cong av av' FsImg.ROOTINO root Hag (Hro g root t Hg)).
  Qed.

  Lemma own_rooted_cong (av av' : aview) (own : gmap K (Z * ttree)) :
    tview av' = tview av -> own_rooted av own -> own_rooted av' own.
  Proof using .
    intros Hv. apply own_rooted_step_cong. intros x s _. rewrite Hv //.
  Qed.

  Lemma own_rooted_dots (av : aview) (own : gmap K (Z * ttree)) (i d : Z) :
    own_rooted av own -> own_rooted (delta_dots i d av) own.
  Proof using . exact (own_rooted_cong av _ own (tview_delta_dots av i d)). Qed.

  Lemma own_rooted_dot (av : aview) (own : gmap K (Z * ttree)) (i : Z) :
    own_rooted av own -> own_rooted (delta_dot i av) own.
  Proof using . exact (own_rooted_cong av _ own (tview_delta_dot av i)). Qed.

  Lemma own_rooted_link_tgt (av : aview) (own : gmap K (Z * ttree))
      (t : Z) (a : anode) :
    av !! t = Some a -> own_rooted av own -> own_rooted (delta_link_tgt t a av) own.
  Proof using .
    intros Ha. exact (own_rooted_cong av _ own (tview_delta_link_tgt av t a Ha)).
  Qed.

  Lemma own_rooted_unl_tgt_live (av : aview) (own : gmap K (Z * ttree))
      (t : Z) (a : anode) :
    av !! t = Some a -> (2 <= an_nlink a)%nat ->
    own_rooted av own -> own_rooted (delta_unl_tgt t av) own.
  Proof using .
    intros Ha Hnl.
    exact (own_rooted_cong av _ own (tview_delta_unl_tgt_live av t a Ha Hnl)).
  Qed.

  Lemma own_rooted_write (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (off : nat) (new bs0 : list (bv 8)) (nl : nat) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    own_rooted av own -> own_rooted (delta_write i off new av) own.
  Proof using .
    intros Hi. apply own_rooted_step_cong. intros x s Hs.
    assert (Hti : tview av !! i = Some (AFile bs0))
      by (rewrite (tview_lookup_Some av i _ Hi) //).
    rewrite (tview_delta_write av i off new bs0 nl Hi).
    exact (nstep_content_edit (tview av) i (AFile (blk_splice off new bs0))
             (AFile bs0) x s Hti eq_refl).
  Qed.

  Lemma own_rooted_trunc (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (bs0 : list (bv 8)) (nl : nat) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    own_rooted av own -> own_rooted (delta_trunc i av) own.
  Proof using .
    intros Hi. apply own_rooted_step_cong. intros x s Hs.
    assert (Hti : tview av !! i = Some (AFile bs0))
      by (rewrite (tview_lookup_Some av i _ Hi) //).
    rewrite (tview_delta_trunc av i bs0 nl Hi).
    exact (nstep_content_edit (tview av) i (AFile []) (AFile bs0) x s Hti eq_refl).
  Qed.

  Lemma own_rooted_arm (av : aview) (own : gmap K (Z * ttree)) (i : Z)
      (c : absnode) :
    av !! i = None -> tabs_leaf (tabs_of c) ->
    own_rooted av own -> own_rooted (delta_arm i c av) own.
  Proof using .
    intros Hi Hleaf. apply own_rooted_step_cong. intros x s Hs.
    assert (Hti : tview av !! i = None) by (rewrite tview_lookup Hi //).
    rewrite (tview_delta_arm av i c).
    exact (nstep_ins_leaf (tview av) i (tabs_of c) x s Hti Hleaf Hs).
  Qed.

  (* create's parent leg and the fused create: reach only GROWS *)
  Lemma own_rooted_ent (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (i : Z) (e : gmap fname Z) (nl : nat) (a : anode) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = Some a ->
    own_rooted av own -> own_rooted (delta_ent d nm i av) own.
  Proof using .
    intros Hnm Hd Hnone Hi Hro g root t Hg.
    assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
      by (rewrite (tview_lookup_Some av d _ Hd) //).
    assert (Hhn : hide_dots e !! nm = None)
      by (rewrite (hide_dots_lookup e nm Hnm) //).
    rewrite (tview_delta_ent av d nm i e nl a Hnm Hd Hi).
    exact (nreach_tedge_ins_mono (tview av) FsImg.ROOTINO d nm i (hide_dots e)
             Htd Hhn root (Hro g root t Hg)).
  Qed.

  Lemma own_rooted_create (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (i : Z) (c : absnode) (e : gmap fname Z) (nl : nat) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = None -> tabs_leaf (tabs_of c) ->
    own_rooted av own -> own_rooted (delta_create d nm i c av) own.
  Proof using .
    intros Hnm Hd Hnone Hi Hleaf Hro.
    assert (Hne : d <> i) by (intros ->; rewrite Hd in Hi; discriminate).
    rewrite (delta_create_split av d nm i c e nl Hd Hi).
    apply (own_rooted_ent (delta_arm i c av) own d nm i e nl
             (MkAnode c 1%nat) Hnm).
    - rewrite (delta_arm_lookup_same av i c d Hne) //.
    - exact Hnone.
    - apply delta_arm_lookup_at.
    - exact (own_rooted_arm av own i c Hi Hleaf Hro).
  Qed.

  (* unlink's ENTRY leg: the cut edge's target is [dots_only], so the only
     node the cut can orphan is the target itself -- and the target is
     nobody's root (at a FILE target [own_wf]'s roots conjunct pays it
     free; at a dots-only DIRECTORY the mover's own non-nesting does). *)
  Lemma own_rooted_unl_ent (av : aview) (own : gmap K (Z * ttree)) (d : Z)
      (nm : fname) (dec : nat) (e : gmap fname Z) (nl : nat) (tg : Z) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = Some tg ->
    (forall s : fname, fs_pname s -> astep av tg s = None) ->
    (forall (g : K) (root : Z) (t : ttree),
       own !! g = Some (root, t) -> root <> tg) ->
    own_rooted av own -> own_rooted (delta_unl_ent d nm dec av) own.
  Proof using .
    intros Hnm Hd He Hlf Hnotroot Hro g root t Hg.
    assert (Htd : tview av !! d = Some (ADir (hide_dots e)))
      by (rewrite (tview_lookup_Some av d _ Hd) //).
    assert (Hhe : hide_dots e !! nm = Some tg)
      by (rewrite (hide_dots_lookup e nm Hnm) //).
    assert (Hleaf : forall s : fname, fs_pname s -> nstep (tview av) tg s = None).
    { intros s Hs. rewrite (nstep_tview av tg s Hs). exact (Hlf s Hs). }
    rewrite (tview_delta_unl_ent av d nm dec e nl Hd).
    destruct (nreach_tedge_del_keep (tview av) FsImg.ROOTINO d nm (hide_dots e)
                tg Htd Hhe Hleaf root (Hro g root t Hg)) as [Hk | Hc];
      [exact Hk |].
    exfalso. exact (Hnotroot g root t Hg Hc).
  Qed.

  (* unlink's TARGET leg at the last link, and the UNARM: a row nothing
     names and that is not [ROOTINO] is UNREACHABLE, so it is nobody's
     root already -- this leg needs no "nobody's root" premise at all. *)
  Lemma own_rooted_unl_tgt (av : aview) (own : gmap K (Z * ttree))
      (tg : Z) (a : anode) :
    av !! tg = Some a -> an_nlink a = 1%nat ->
    aview_no_edge_to av tg -> tg <> FsImg.ROOTINO ->
    own_rooted av own -> own_rooted (delta_unl_tgt tg av) own.
  Proof using .
    intros Ha Hnl Hno Hrt Hro g root t Hg.
    assert (Hnon : forall (x : Z) (s : fname), fs_pname s ->
              nstep (tview av) x s <> Some tg).
    { intros x s Hs. rewrite (nstep_tview av x s Hs). exact (Hno x s Hs). }
    rewrite (tview_delta_unl_tgt_last av tg a Ha Hnl).
    destruct (nreach_delete_keep (tview av) tg FsImg.ROOTINO Hnon
                (fun Hc => Hrt (eq_sym Hc)) root (Hro g root t Hg)) as [Hk _].
    exact Hk.
  Qed.

  Lemma own_rooted_unarm (av : aview) (own : gmap K (Z * ttree)) (i : Z) :
    aview_no_edge_to av i -> i <> FsImg.ROOTINO ->
    own_rooted av own -> own_rooted (delta_unarm i av) own.
  Proof using .
    intros Hno Hri Hro g root t Hg.
    assert (Hnon : forall (x : Z) (s : fname), fs_pname s ->
              nstep (tview av) x s <> Some i).
    { intros x s Hs. rewrite (nstep_tview av x s Hs). exact (Hno x s Hs). }
    rewrite (tview_delta_unarm av i).
    destruct (nreach_delete_keep (tview av) i FsImg.ROOTINO Hnon
                (fun Hc => Hri (eq_sym Hc)) root (Hro g root t Hg)) as [Hk _].
    exact Hk.
  Qed.

  (* ---- 9e.  THE MAP MOVES: retree and the hand-down ---------------- *)

  Lemma own_rooted_retree (av : aview) (own : gmap K (Z * ttree))
      (g : K) (root : Z) (t t' : ttree) :
    own !! g = Some (root, t) ->
    own_rooted av own -> own_rooted av (<[g := (root, t')]> own).
  Proof using .
    intros Hg Hro g0 r0 t0 H0.
    destruct (decide (g0 = g)) as [-> | Hne].
    - rewrite lookup_insert_eq in H0. injection H0 as <- _. exact (Hro g root t Hg).
    - rewrite lookup_insert_ne in H0; [| congruence]. exact (Hro g0 r0 t0 H0).
  Qed.

  (* THE HAND-DOWN pays the conjunct: the child's root is a node of the
     parent's OWN tree, hence reachable from the parent's root, hence
     from [ROOTINO]. *)
  Lemma own_rooted_grant (av : aview) (own : gmap K (Z * ttree))
      (g g' : K) (root root' : Z) (t t' : ttree) :
    own !! g = Some (root, t) -> subtree av root = Some t ->
    root' ∈ dom (tv_nodes t) ->
    own_rooted av own ->
    own_rooted av (<[g' := (root', t')]> (delete g own)).
  Proof using .
    intros Hg Ht Hd Hro g0 r0 t0 H0.
    destruct (decide (g0 = g')) as [-> | Hne].
    - rewrite lookup_insert_eq in H0. injection H0 as <- _.
      exact (nreach_trans (tview av) FsImg.ROOTINO root root'
               (Hro g root t Hg) (subtree_dom_reach av root t root' Ht Hd)).
    - rewrite lookup_insert_ne in H0; [| congruence].
      apply lookup_delete_Some in H0 as [_ H0]. exact (Hro g0 r0 t0 H0).
  Qed.

End OwnRootedPres.

(* ===================================================================== *)
(* TreeObs.v -- WHAT A FROZEN DEED IS, READ AS A PIN.                     *)
(*                                                                       *)
(* design/user-tree.md (TL-0), lane TL-3, THE READ SIDE.  [AppTree.v]     *)
(* landed the claim, the deed [tree_own], the frozen deed [tree_pin] and  *)
(* its [□]-shaped law; [PinnedObs.v] landed the walk families every       *)
(* walk-shaped syscall's bundle is built out of.  This file is the ONE    *)
(* bridge between them, and everything TL-3 lands above it -- the exec    *)
(* supplier ([TreeExec.v]), open's and read's stable corollaries          *)
(* ([UkTreeRead.v]) -- is an instance of the two lemmas here:             *)
(*                                                                       *)
(*  (1) [tree_pin_claim_law]: the era's record equation turns             *)
(*      [AppTree.tree_pin_law] into the shape every pinned bundle takes,  *)
(*      [□ (∀ v, app_pred app_run v -∗ app_pred app_run v ∗ (⌜Pin v⌝ ∨    *)
(*      T))] at [Pin := fun v => subtree v root = Some t] and [T :=       *)
(*      tree_taint].  ([UInitCons.init_cons_laws]' shape, at the tree     *)
(*      application instead of at echo's console claim.)                  *)
(*                                                                       *)
(*  (2) [tree_pin_resolves]: the PURE content of the deed, as             *)
(*      [PinnedObs.pin_resolves_abs] -- the same hops at every admitted   *)
(*      view (they are computed from the TREE, not from a view), the same *)
(*      terminal inum, and the terminal row up to its LINK COUNT.  Up to  *)
(*      the count and no further: TL-1 dropped [nlink] from the tree      *)
(*      deliberately (design section 1), which is why the absnode pin     *)
(*      exists at all (PinnedObs section 10, TL-2's finding 2).           *)
(*                                                                       *)
(* AND THE ONE LIMIT, stated here because this is where it bites: a       *)
(* DIRECTORY row is pinned only up to its DOTS as well (the tree hides    *)
(* "." and ".."), so [tree_pin_resolves] is offered at a row the          *)
(* projection is the identity on -- a file or a device                    *)
(* ([TreeView.subtree_resolves_pin_file], [tabs_of_dev_inv]).  A          *)
(* corollary that wants a directory's ENTRY MAP off the claim (chdir's,   *)
(* fstat's on a directory) must read it out of the tree instead -- the    *)
(* tree HAS it, dots excepted -- and no landed leaf takes that shape yet  *)
(* (see UkTreeRead.v's section 5).                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map mono_nat invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedObs.v]'s header: a field instance is inert wherever its
   module is not imported). *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] field [file_app] *)
Require Import PathElems.       (* [path_elems] *)
Require Import FsTree.          (* [fname] *)
Require Import FsImg.           (* [ROOTINO] *)
Require Import AppCfg.          (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import FsAbsEra.        (* [um_start_of] *)
Require Import TreeView.        (* TL-1: [subtree], [resolves_from], the hops *)
Require Import AppTree.         (* TL-2: [tree_pred], [tree_pin], the laws *)
Require Import PinnedObs.       (* [pin_resolves_abs], section 10 *)
Require Import FsAbsDefs.       (* [aview] / [anode] (FsAbs's own rule: LAST) *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PIN, PURELY                                                   *)
(* ===================================================================== *)

(* THE DEED'S OWN PIN.  [Pin] is "my subtree is still [t]" -- the claim's
   reading -- and what it resolves is whatever the TREE resolves, which is
   the whole point of holding a subtree instead of a view: the hops are
   [TreeView.resolve_hops], computed from [t] alone.

   THE START RULE IS A PREMISE: [um_start_of cw pl] is [ROOTINO] at an
   absolute path and the caller's cwd at a relative one, and either way the
   program knows which and that it is a row of its own tree
   ([d ∈ dom (tv_nodes t)]).  That is design section 3's "the premise the
   program needs -- this path resolves inside my subtree -- is a pure fact
   about its path and its cwd, discharged by its code proof". *)
Lemma tree_pin_resolves_gen (root d i : Z) (t : ttree) (n : absnode)
    (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  um_start_of cw pl = d ->
  d ∈ dom (tv_nodes t) ->
  resolves_from t d pl = Some (i, n) ->
  (* the projection is the identity at this row: a FILE or a DEVICE *)
  (forall n' : absnode, tabs_of n' = n -> n' = n) ->
  pin_resolves_abs (fun v : aview => subtree v root = Some t) cw pl
    (resolve_hops t d pl) i n.
Proof.
  intros Hp Hstart Hd Hres Hid.
  assert (Hhead : resolve_hops t d pl !!! 0%nat = d)
    by (rewrite /resolve_hops; apply nchain_head).
  assert (Hlast : resolve_hops t d pl !!! length (path_elems pl) = i).
  { rewrite /resolve_hops. apply nchain_last.
    rewrite /resolves_from in Hres.
    destruct (npath (tv_nodes t) d (path_elems pl)) as [j |] eqn:Hw;
      [| discriminate].
    destruct (tv_nodes t !! j) as [n0 |] eqn:Hn0; [| discriminate].
    injection Hres as <- <-. reflexivity. }
  split.
  - split_and!; [ by rewrite Hhead | exact Hlast | ].
    intros v HPin.
    destruct (subtree_resolves_pin t d i n pl Hp Hres v root HPin
                (subtree_dom_reach v root t d HPin Hd))
      as (Hrun & _ & _ & _).
    by rewrite Hhead.
  - intros v HPin.
    destruct (subtree_resolves_pin t d i n pl Hp Hres v root HPin
                (subtree_dom_reach v root t d HPin Hd))
      as (_ & _ & Hfin & (n' & k & Ha & Hn')).
    exists k. by rewrite (Hid n' Hn') in Ha.
Qed.

(* ...AT A FILE, which is exec's (W) and open's file arm *)
Lemma tree_pin_resolves_file (root d i : Z) (t : ttree) (bs : list (bv 8))
    (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  um_start_of cw pl = d ->
  d ∈ dom (tv_nodes t) ->
  resolves_from t d pl = Some (i, AFile bs) ->
  pin_resolves_abs (fun v : aview => subtree v root = Some t) cw pl
    (resolve_hops t d pl) i (AFile bs).
Proof.
  intros Hp Hstart Hd Hres.
  exact (tree_pin_resolves_gen root d i t (AFile bs) cw pl Hp Hstart Hd Hres
           (fun n' Hn' => tabs_of_file_inv n' bs Hn')).
Qed.

(* ...AND AT A DEVICE, which is what a tree application's open("console")
   would take (the console is a node of the namespace like any other) *)
Lemma tree_pin_resolves_dev (root d i : Z) (t : ttree) (ma mi : Z)
    (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  um_start_of cw pl = d ->
  d ∈ dom (tv_nodes t) ->
  resolves_from t d pl = Some (i, ADev ma mi) ->
  pin_resolves_abs (fun v : aview => subtree v root = Some t) cw pl
    (resolve_hops t d pl) i (ADev ma mi).
Proof.
  intros Hp Hstart Hd Hres.
  exact (tree_pin_resolves_gen root d i t (ADev ma mi) cw pl Hp Hstart Hd Hres
           (fun n' Hn' => tabs_of_dev_inv n' ma mi Hn')).
Qed.

(* the ABSOLUTE and the RELATIVE start, spelled: an owner of "/" resolves
   absolute paths, and an owner whose cwd is inside its own tree resolves
   relative ones.  Both are [tree_pin_resolves_file] with the start rule
   discharged, and they are the two forms a program actually holds. *)
Lemma tree_pin_resolves_abs_path (i : Z) (t : ttree) (bs : list (bv 8))
    (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  pl !! 0%nat = Some SLASH ->
  FsImg.ROOTINO ∈ dom (tv_nodes t) ->
  resolves_from t FsImg.ROOTINO pl = Some (i, AFile bs) ->
  pin_resolves_abs (fun v : aview => subtree v FsImg.ROOTINO = Some t) cw pl
    (resolve_hops t FsImg.ROOTINO pl) i (AFile bs).
Proof.
  intros Hp Hsl Hd Hres.
  exact (tree_pin_resolves_file FsImg.ROOTINO FsImg.ROOTINO i t bs cw pl Hp
           (um_start_of_slash cw pl Hsl) Hd Hres).
Qed.

Lemma tree_pin_resolves_rel (root i : Z) (t : ttree) (bs : list (bv 8))
    (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  pl !! 0%nat <> Some SLASH ->
  cw ∈ dom (tv_nodes t) ->
  resolves_from t cw pl = Some (i, AFile bs) ->
  pin_resolves_abs (fun v : aview => subtree v root = Some t) cw pl
    (resolve_hops t cw pl) i (AFile bs).
Proof.
  intros Hp Hsl Hd Hres.
  exact (tree_pin_resolves_file root cw i t bs cw pl Hp
           (um_start_of_rel cw pl Hsl) Hd Hres).
Qed.

(* ===================================================================== *)
(*  2.  THE CLAIM LAW, AT THE ERA'S RECORD                                *)
(* ===================================================================== *)

Section TreeObs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!treeG Σ}.

  (* THE PREMISE IS THE ERA'S RECORD EQUATION, exactly as
     [UInitConsK.init_cons_never_abs_law]'s is, and THE REWRITE GOES FIRST,
     before anything typed at [app_names file_app] is introduced. *)
  Lemma tree_pin_claim_law (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_pin r g root t -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗
         (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    intros Heq. rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "#Hp". iApply (tree_pin_law c r g root t with "Hp").
  Qed.

  (* ...and the LINEAR one beside it, for a fire that opens the invariant
     ONCE ([AppTree.tree_claim_law]): an unfrozen owner takes this. *)
  Lemma tree_own_claim_law (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    ⊢ □ (∀ (v : aview) (g : gname) (root : Z) (t : ttree),
           tree_own r g root t -∗ app_pred app_run v -∗
           app_pred app_run v ∗ tree_own r g root t ∗
           (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    intros Heq. rewrite Heq. cbn [app_pred app_run app_names].
    iApply tree_claim_law.
  Qed.

End TreeObs.

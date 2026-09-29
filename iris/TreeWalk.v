(* ===================================================================== *)
(* TreeWalk.v -- THE PINNED PARENT-PREFIX WALK, OUT OF A FROZEN DEED.     *)
(*                                                                       *)
(* design/user-tree.md section 7.4's wall 3, lane TL-3P deliverable 2.    *)
(* [TreeExec.v] is the same construction at the FULL path ([namei]'s      *)
(* walk, [FsAbsEra.ex_start], which exec/open/read take); this file is    *)
(* its twin at the PARENT PREFIX ([nameiparent]'s walk,                   *)
(* [FsAbsEra.ep_start]) -- the piece every create-family bundle owes      *)
(* ([SysOpenDefs.open_au_create_at], [SpecSysMknod.mknod_au_at],          *)
(* [SpecSysUnlink.unlink_au_pre]) and the only supplier of which was, up  *)
(* to now, [FsAbsEra.ep_start_triv] (the caller who tracks nothing).      *)
(*                                                                       *)
(* WHAT IT IS MADE OF, and there is nothing else here:                    *)
(*   - [TreeObs.tree_pin_claim_law]: the deed, as the [□] claim law;      *)
(*   - [TreeView] section 8a: the deed's PURE content at an arbitrary     *)
(*     element list, instantiated at [FsAbsEra.np_elems pl];              *)
(*   - [PinnedObs] section 11: that pin, as [ep_start].                   *)
(*                                                                       *)
(* WHAT THE WALK FIXES, AND WHAT IT DOES NOT.  It fixes the PARENT: the   *)
(* cursor the bundle hands back at index [length (np_elems pl)] is the    *)
(* directory the owner's own tree resolves the prefix to, or the taint    *)
(* ([tree_pwalk_parent]).  It does NOT reach inside the create/unlink     *)
(* COMMITS, which quantify their own parent [d] and so owe a step at      *)
(* EVERY directory -- see [TreeMove.v] section 4, where that wall is      *)
(* stated in full.  This file is the half of wall 3 that is a tree-layer  *)
(* question; the other half is a contract-shape question one tier down.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map mono_nat invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
(* the ghost binder list's defining modules, each IMPORTED ([PinnedObs]'s
   header: a field instance is inert wherever its module is not imported) *)
Require Import Xv6Cameras.      (* [bioslotG] *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] field [file_app] *)
Require Import PathElems.       (* [path_elems] / [SLASH] *)
Require Import FsTree.          (* [fname] / [fs_proper] *)
Require Import FsBlocks.        (* [fs_names] *)
Require Import FsImg.           (* [ROOTINO] *)
Require Import AppCfg.          (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import AppInv.          (* [app_inv] *)
Require Import FsAbsEra.        (* [ep_start], [np_elems], [um_start_of] *)
Require Import TreeView.        (* TL-1 + section 8a: [tres_from] / [tres_hops] *)
Require Import AppTree.         (* TL-2/TL-3W: the claim, the deed, the laws *)
Require Import TreeObs.         (* the claim law at the era's record *)
Require Import PinnedObs.       (* section 11: [pin_presolves_at], [pobs_pwalk] *)
Require Import FsAbsDefs.       (* [aview] / [anode] (FsAbs's own rule: LAST) *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE DEED'S PARENT PREFIX, PURELY                                  *)
(* ===================================================================== *)

(* [TreeObs.tree_pin_resolves_gen]'s twin one element short.  The start
   rule is a premise exactly as it is there ([um_start_of cw pl] is
   [ROOTINO] at an absolute path and the caller's cwd at a relative one,
   and either way the program knows which and that it is a row of its own
   tree); what is new is only the LIST the resolution runs over.

   THE TERMINAL ROW IS A DIRECTORY, so -- unlike the read side's file and
   device pins -- the projection is NOT the identity and what comes back
   is the entry map UP TO THE DOTS.  That is the honest content and it is
   all a create/unlink consumer spends: it asks whether its own [nm] is an
   entry, and [nm] is proper. *)
Lemma tree_pin_presolves (root d0 dpar : Z) (t : ttree)
    (ents : gmap fname Z) (cw : Z) (pl : list (bv 8)) :
  fs_proper (path_elems pl) ->
  um_start_of cw pl = d0 ->
  d0 ∈ dom (tv_nodes t) ->
  tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
  pin_presolves_at (fun v : aview => subtree v root = Some t) cw pl
    (tres_hops t d0 (np_elems pl)) dpar ents.
Proof.
  intros Hp Hstart Hd Hres.
  assert (Hpp : fs_proper (np_elems pl))
    by exact (fs_proper_removelast (path_elems pl) Hp).
  assert (Hhead : tres_hops t d0 (np_elems pl) !!! 0%nat = d0)
    by (rewrite /tres_hops; apply nchain_head).
  assert (Hpath : npath (tv_nodes t) d0 (np_elems pl) = Some dpar).
  { rewrite /tres_from in Hres.
    destruct (npath (tv_nodes t) d0 (np_elems pl)) as [j |]; [| discriminate].
    destruct (tv_nodes t !! j) as [n0 |]; [| discriminate].
    injection Hres as Hj _. by rewrite Hj. }
  assert (Hlast : tres_hops t d0 (np_elems pl) !!! length (np_elems pl) = dpar)
    by (rewrite /tres_hops; exact (nchain_last _ _ _ _ Hpath)).
  split.
  - split_and!; [ by rewrite Hhead | exact Hlast | ].
    intros v HPin.
    destruct (subtree_tres_pin_dir t d0 dpar ents (np_elems pl) Hpp Hres
                v root HPin (subtree_dom_reach v root t d0 HPin Hd))
      as (Hrun & _ & _ & _).
    by rewrite Hhead.
  - intros v HPin.
    destruct (subtree_tres_pin_dir t d0 dpar ents (np_elems pl) Hpp Hres
                v root HPin (subtree_dom_reach v root t d0 HPin Hd))
      as (_ & _ & _ & (e & k & Ha & He)).
    exists e, k. split; [ exact Ha | ].
    intros s Hs1 Hs2. exact (He s (conj Hs1 Hs2)).
Qed.

(* ...and the fact the owner needs BESIDE the walk if it is ever to move
   at the parent: the directory the prefix stops at is a node of its own
   tree.  Pure, and read off the same resolution. *)
Lemma tree_pin_presolves_dom (d0 dpar : Z) (t : ttree)
    (ents : gmap fname Z) (pl : list (bv 8)) :
  tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
  dpar ∈ dom (tv_nodes t).
Proof. intros H. exact (tres_from_dom t d0 dpar (ADir ents) (np_elems pl) H). Qed.

Section TreeWalk.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!treeG Σ}.

  (* =================================================================== *)
  (*  2.  THE DEED ROUTE: [ep_start] OUT OF A FROZEN DEED                 *)
  (* =================================================================== *)

  (* [TreeExec.exec_walk_of_own]'s shape at the parent prefix.  Everything
     on the left is the program's own knowledge: its frozen deed, the
     era's record equation, and the PURE fact that the parent prefix of
     the path it is about to pass resolves INSIDE its tree to a
     directory. *)
  Lemma tree_pwalk_of_own (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root d0 dpar : Z) (t : ttree) (ents : gmap fname Z)
      (cw : Z) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d0 ->
    d0 ∈ dom (tv_nodes t) ->
    tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
    tree_pin r g root t -∗
    app_inv γfs -∗
    ep_start γfs cw (pobs_P (tree_taint c) (tres_hops t d0 (np_elems pl)))
      (pobs_Pmiss (tree_taint c)) pl.
  Proof using .
    intros Heq Hp Hstart Hd Hres. iIntros "#Hpin #Hinv".
    iDestruct (tree_pin_claim_law c r g root t Heq with "Hpin") as "#Hcl".
    iApply (pobs_pwalk γfs (fun v => subtree v root = Some t) (tree_taint c)
              (pobs_Pmiss (tree_taint c)) cw pl
              (tres_hops t d0 (np_elems pl)) dpar
              (pin_pwalks_at_of_presolves _ _ _ _ _ _
                 (tree_pin_presolves root d0 dpar t ents cw pl Hp Hstart Hd Hres))
              with "[] Hcl Hinv").
    iApply pobs_miss_taint_Pmiss.
  Qed.

  (* THE PARENT, IDENTIFIED: what the bundle's terminal cursor says.  This
     is the ingredient a [d]-indexed create/unlink commit would spend
     ([TreeMove.v] section 4); at the landed commits, whose [d] is
     quantified INSIDE, there is nowhere to spend it. *)
  Lemma tree_pwalk_parent (c : tree_fixed) (root d0 dpar : Z) (t : ttree)
      (ents : gmap fname Z) (cw : Z) (pl : list (bv 8)) (d' : Z) :
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d0 ->
    d0 ∈ dom (tv_nodes t) ->
    tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
    pobs_P (tree_taint c) (tres_hops t d0 (np_elems pl))
      (length (np_elems pl)) d' -∗
    ⌜d' = dpar⌝ ∨ tree_taint c.
  Proof using .
    intros Hp Hstart Hd Hres.
    iApply (pobs_pterm (fun v => subtree v root = Some t) (tree_taint c)
              cw pl (tres_hops t d0 (np_elems pl)) dpar d'
              (pin_pwalks_at_of_presolves _ _ _ _ _ _
                 (tree_pin_presolves root d0 dpar t ents cw pl Hp Hstart Hd Hres))).
  Qed.

  (* ...AND AT AN ABSOLUTE PATH UNDER "/", which is the shape a boot
     process's deed ([AppTree.tree_boot]) takes. *)
  Lemma tree_pwalk_of_own_root (γfs : fs_names) (c : tree_fixed)
      (r : tree_names) (g : gname) (dpar : Z) (t : ttree)
      (ents : gmap fname Z) (cw : Z) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) ->
    pl !! 0%nat = Some SLASH ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    tres_from t FsImg.ROOTINO (np_elems pl) = Some (dpar, ADir ents) ->
    tree_pin r g FsImg.ROOTINO t -∗
    app_inv γfs -∗
    ep_start γfs cw
      (pobs_P (tree_taint c) (tres_hops t FsImg.ROOTINO (np_elems pl)))
      (pobs_Pmiss (tree_taint c)) pl.
  Proof using .
    intros Heq Hp Hsl Hd Hres.
    exact (tree_pwalk_of_own γfs c r g FsImg.ROOTINO FsImg.ROOTINO dpar t ents
             cw pl Heq Hp (um_start_of_slash cw pl Hsl) Hd Hres).
  Qed.


  (* =================================================================== *)
  (*  3.  THE LIVE-DEED ROUTE, AT ANY PARENT PREFIX                       *)
  (*      (lane TL-3K; design/user-tree.md section 7.5's WALL B)           *)
  (*                                                                      *)
  (*  Section 2 needs a FROZEN deed, and a frozen deed can never be        *)
  (*  parked -- so the owner that walks can never MOVE, which is exactly   *)
  (*  what create and unlink need in the same syscall.  [PinnedObs] 11a    *)
  (*  lifts that: with the deed ON THE CURSOR, the LINEAR claim law        *)
  (*  ([TreeObs.tree_own_claim_law], the deed in and out) supplies the     *)
  (*  walk at ANY length, and the deed comes home inside the terminal      *)
  (*  cursor ([PinnedObs.pobs_pterm_lin]).                                 *)
  (*                                                                      *)
  (*  WHAT A CONSUMER MUST THEN DO, and it is the seam this lane records   *)
  (*  rather than closes: the terminal cursor now CARRIES the deed, and    *)
  (*  the cursor is what the cursor-threaded commits take as their premise *)
  (*  ([FsAbsCreateFire.acre_commit_at_gen]'s [Pd]).  Those commits READ   *)
  (*  the premise and hand it back IN PHASE 1, while an owner's move parks *)
  (*  the deed in phase 1 and only gets it back (MOVED) in phase 2 -- so a *)
  (*  deed-carrying cursor wants the commit to return [Pd d] at PHASE 2,   *)
  (*  at the moved deed.  That is a further kernel-tier restatement, and   *)
  (*  it is what a length-1 corollary needs on top of this file.           *)
  (* =================================================================== *)

  Lemma tree_pwalk_of_own_live (γfs : fs_names) (c : tree_fixed)
      (r : tree_names) (g : gname) (root d0 dpar : Z) (t : ttree)
      (ents : gmap fname Z) (cw : Z) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d0 ->
    d0 ∈ dom (tv_nodes t) ->
    tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
    app_inv γfs -∗
    tree_own r g root t -∗
    ep_start γfs cw
      (pobs_P_lin (tree_taint c) (tres_hops t d0 (np_elems pl))
         (tree_own r g root t))
      (pobs_Pmiss (tree_taint c)) pl.
  Proof using .
    intros Heq Hp Hstart Hd Hres. iIntros "#Hinv Hown".
    iDestruct (tree_own_claim_law c r Heq) as "#Hlaw".
    iApply (pobs_pwalk_lin γfs (fun v => subtree v root = Some t) (tree_taint c)
              (tree_own r g root t) (pobs_Pmiss (tree_taint c)) cw pl
              (tres_hops t d0 (np_elems pl)) dpar
              (pin_pwalks_at_of_presolves _ _ _ _ _ _
                 (tree_pin_presolves root d0 dpar t ents cw pl Hp Hstart Hd Hres))
              with "[] [] Hinv Hown").
    { iApply pobs_miss_taint_Pmiss. }
    iIntros "!>" (v) "Hown Hp".
    iDestruct ("Hlaw" $! v g root t with "Hown Hp") as "(A & B & C)".
    iFrame "A B C".
  Qed.

  (* ...and the terminal reading: the parent the owner's own tree resolves
     the prefix to, WITH THE LIVE DEED BACK. *)
  Lemma tree_pwalk_parent_live (c : tree_fixed) (r : tree_names) (g : gname)
      (root d0 dpar : Z) (t : ttree) (ents : gmap fname Z)
      (cw : Z) (pl : list (bv 8)) (d' : Z) :
    fs_proper (path_elems pl) ->
    um_start_of cw pl = d0 ->
    d0 ∈ dom (tv_nodes t) ->
    tres_from t d0 (np_elems pl) = Some (dpar, ADir ents) ->
    pobs_P_lin (tree_taint c) (tres_hops t d0 (np_elems pl))
      (tree_own r g root t) (length (np_elems pl)) d' -∗
    (⌜d' = dpar⌝ ∗ tree_own r g root t) ∨ tree_taint c.
  Proof using .
    intros Hp Hstart Hd Hres.
    iApply (pobs_pterm_lin (fun v => subtree v root = Some t) (tree_taint c)
              (tree_own r g root t) cw pl (tres_hops t d0 (np_elems pl))
              dpar d'
              (pin_pwalks_at_of_presolves _ _ _ _ _ _
                 (tree_pin_presolves root d0 dpar t ents cw pl Hp Hstart Hd Hres))).
  Qed.

End TreeWalk.

(* ===================================================================== *)
(* UInitTreeBoot.v -- THE CONSOLE DANCE AT THE TREE CLAIM, AND THE ONE    *)
(* PREMISE OF [UInitKernel.init_boot_con] THAT IS STILL OPEN (lane TL-7,  *)
(* deliverables D3/D4; design/user-tree.md section 9.5(5)).               *)
(*                                                                       *)
(* section 9.5(5) named TWO echo-indexed entries of /init's premise list. *)
(* This file closes the first and REDUCES the second to a single          *)
(* entailment, so that the ruling it needs can be taken on one line.      *)
(*                                                                       *)
(*  (1) THE CONSOLE DANCE, CLOSED.  [tree_init_cons_dance_all] is         *)
(*      [UInitKernel.init_cons_dance_all] at the tree claim, built from   *)
(*      [UInitTreeCons]'s two leaves on the MISS arm: the credential is   *)
(*      the era's own deed, it goes into the first open and the mknod and *)
(*      comes back, and nothing about it is echo's.                       *)
(*                                                                       *)
(*  (2) THE EXEC SUPPLY, WALLED, AND THE WALL IS ONE ENTAILMENT.          *)
(*      [UkInit.init_cons_sup] has exactly one producer in the tree,      *)
(*      [UInitSh.init_exec_sup_of_sh_slot], whose Coq-level premise is    *)
(*      [UInitSh.cons_cred_holds] -- nine laws over the console           *)
(*      credential record.  At the tree's record ([UInitTree.tree_cc])    *)
(*      the SEVENTH of them reads,                                        *)
(*      after the two trivial families are unfolded, exactly              *)
(*                                                                       *)
(*           the era's UNSPENT LICENCE becomes the taint, UPDATE-FREE     *)
(*                                                                       *)
(*      and [tree_cc_wb_conj8_is_turn_to_taint] below PROVES that         *)
(*      reduction, in both directions, so nothing is left to the reader's *)
(*      judgement.  The licence is a linear [ghost_map] element and the   *)
(*      taint is that element PERSISTED ([AppTree.tree_taint_mint] is one *)
(*      [ghost_map_elem_persist]), so no update-free entailment exists --  *)
(*      which is the same fact [AppTree.tree_bump_free_is_vacuous] rests  *)
(*      on, and the same shape section 9.4's ruling (b) already fixed     *)
(*      once for the KILL row ([UkInit.init_kill_law] is an UPDATE for    *)
(*      precisely this reason).                                           *)
(*                                                                       *)
(*      SO THE OWNER'S RULING IS THE SAME ONE, ONE PREMISE OVER: re-cut   *)
(*      [cons_cred_holds]'s seventh conjunct as an UPDATE                 *)
(*      ([==*] in place of [-*]), which echo discharges with one          *)
(*      [iModIntro] and the tree discharges by SPENDING the licence.      *)
(*      Until that ruling, [UTreeAdequacy.tree_Hinit_boot] stands in its  *)
(*      at-boot form and this file's dance is the half of                 *)
(*      [init_boot_con]'s list the tree claim can already pay.            *)
(*                                                                       *)
(*      TWO SMALLER ENTRIES ARE OWED BESIDE IT, and both are the same     *)
(*      record's: [cons_cred_holds]'s FIRST conjunct is                   *)
(*      sh's read leaf as a CLOSED entailment -- no taint in hand -- and  *)
(*      the HIT arm of the dance ([UkInit.uki_mknod_hit_leaf],            *)
(*      UkInit.v:499) wants a credential-free, box-shaped mknod, which    *)
(*      the tree's own mknod corollary cannot give (it needs the LIVE     *)
(*      deed).  [UInitTreeCons.v]'s header prices the second.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserConsole.       (* [cons_cred] and its six families *)
Require Import LineWords.         (* [wl_nl] *)
Require Import UexecExecInst.     (* [uprogSG_free] -- /init's instance *)
Require Import UInitKernel.       (* [init_cons_dance_all] and its two intros *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsTree.
Require Import FsAbsDefs.
Require Import TreeView.
Require Import AppTree.
Require Import UInitCons.         (* [init_cons_fd] *)
Require Import UInitTree.         (* [tree_cc] and the mint at the banner *)
Require Import UInitTreeCons.     (* the two leaves at the deed *)
Require Import FsConsPin.         (* [fname_console] *)
Require FsImg.

Local Open Scope Z_scope.

Section TreeInitBoot.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!treeG Σ}.

  (* =================================================================== *)
  (*  1.  THE CONSOLE DANCE, AT THE ERA'S OWN DEED                        *)
  (*                                                                     *)
  (*  [UInitKernel.init_cons_dance_all]'s MISS arm: the leaves are        *)
  (*  persistent in the record [N] (they are entailed by [AppInv.app_inv] *)
  (*  and the claim's two [box] laws), and the credential is the ONE      *)
  (*  linear thing -- the deed at the era's namespace, which the first    *)
  (*  open reads and hands back and the mknod MOVES.                      *)
  (* =================================================================== *)
  Lemma tree_init_cons_dance_all (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (e : gmap fname Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e) ->
    e !! fname_console = None ->
    app_inv fsc_fs -∗ tree_own r g FsImg.ROOTINO t -∗
    UInitKernel.init_cons_dance_all (PS := uprogSG_free) (tree_taint c)
      True%I init_cons_fd.
  Proof using .
    intros Heq Hd He. iIntros "#Hinv Hown".
    iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
              (tree_taint c) True%I (tree_own r g FsImg.ROOTINO t)
              init_cons_fd with "[] Hown").
    iIntros "!>" (N).
    iApply (tree_init_cons_leaves N c r g t e Heq Hd He with "Hinv").
  Qed.

  (* =================================================================== *)
  (*  2.  THE WALL, REDUCED                                               *)
  (*                                                                     *)
  (*  [UInitSh.cons_cred_holds]'s eighth conjunct, spelled at             *)
  (*  [UInitTree.tree_cc] and at the tree's taint.  Both directions, so   *)
  (*  the reduction is an equivalence and not a one-way weakening: what   *)
  (*  /init's exec supply asks of the tree claim IS the update-free mint  *)
  (*  the design forbids, and nothing else.                              *)
  (* =================================================================== *)
  Lemma tree_cc_wb_conj8_is_turn_to_taint (c : tree_fixed) :
    (forall (γp : gname) (I l : list (bv 8)), wl_nl ∉ l ->
       ⊢ cc_mid (tree_cc c) γp (I ++ l ++ [wl_nl]) -∗
         cc_wb (tree_cc c) I -∗
         cc_mid (tree_cc c) γp (I ++ l ++ [wl_nl]) ∗ tree_taint c)
    <-> (⊢ tree_turn c -∗ tree_taint c).
  Proof using .
    split.
    - intros H8.
      iIntros "Ht".
      iDestruct (H8 inhabitant [] [] ltac:(set_solver)) as "H".
      iDestruct ("H" with "[] [Ht]") as "[_ $]"; [ done | ].
      rewrite tree_cc_wb_eq. iLeft. iExact "Ht".
    - intros Hmint. intros γp I l _.
      iIntros "_ Hwb". iSplitR; [ done | ].
      rewrite tree_cc_wb_eq. iDestruct "Hwb" as "[Ht | #Ht]";
        [ iApply Hmint; iExact "Ht" | iExact "Ht" ].
  Qed.

End TreeInitBoot.

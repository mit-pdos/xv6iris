(* ===================================================================== *)
(* TreeMove.v -- THE OWNER'S MOVE AT THE FIRE (lane TL-3W).               *)
(*                                                                       *)
(* design/user-tree.md section 7.2, at the write-kind fires.  [AppTree.v] *)
(* landed the two halves of the move -- the update-free STEP              *)
(* ([tree_step_move_*]) and the RESYNC ([tree_resync]) -- as facts about  *)
(* the claim alone; this file joins them into the shape a two-phase       *)
(* commit takes, so that an OWNER can supply a write-kind AU out of its   *)
(* DEED and get the MOVED DEED back inside the commit's own receipt.      *)
(*                                                                       *)
(*   phase 1   opens [AppInv.app_inv], agrees the map the kernel lent,    *)
(*             reads its own subtree off the claim, DECIDES whether the   *)
(*             move is visible in its tree, and hands the fire an         *)
(*             [AppInv.app_step] -- the free one if not, the parking one  *)
(*             if so (the deed and a fresh token go in);                  *)
(*   phase 2   runs after the mover with [I'] and                         *)
(*             [abs_view I' = δ (abs_view I)] in hand, opens the claim    *)
(*             again, REFUTES the exact arm by TL-1's INSIDE lemma, and   *)
(*             resyncs the entry -- returning the deed AT THE MOVED TREE. *)
(*                                                                       *)
(* WHAT IS HERE: the WRITE chain ([tree_awrite_chain]), which is the one  *)
(* write-kind member whose U-tier leaf can carry the receipt home         *)
(* ([UkTreeWrite.v]).  WHAT IS NOT, AND EXACTLY WHY: section 4.           *)
(*                                                                       *)
(* SINCE TL-3C AND TL-3R the create/unlink family lives here too:         *)
(*   3b   the two moves AT A GIVEN PARENT ([tree_acre_phases],           *)
(*        [tree_uent_phases]);                                            *)
(*   3b'  create's parent leg BY THE ROOTED ROUTE                        *)
(*        ([tree_acre_phases_rooted]) -- the two credentials read off    *)
(*        the claim from the arm's PURE receipt, at EVERY child kind;    *)
(*   3c   unlink's ENTRY leg at the bundle's own shape;                   *)
(*   3d   THE CREATE MOVE CONSUMED: all four legs from ONE deed          *)
(*        ([tree_arm_commit] / [tree_unarm_commit] / [tree_dots_commit] / *)
(*        [tree_acre_commit], joined by [tree_cre_commits]);              *)
(*   3e   unlink's TARGET leg at a GIVEN target, and the two quantifier  *)
(*        seams that are all that blocks the unlink corollary;            *)
(*   3f   the three path-fixed BUNDLES at a parent prefix of length zero  *)
(*        ([tree_mknod_au] / [tree_mkdir_au] / [tree_open_create_au]).    *)
(* design/user-tree.md sections 7.7 and 7.9 are the as-landed blocks.     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.       (* [bioslotG] *)
Require Import Xv6G.             (* [xv6G] *)
Require Import FdSlots.          (* [fdslotG] *)
Require Import IrefSlots.        (* [irefslotG] *)
Require Import ProcAvail.        (* [pavG] *)
Require Import FileInvDefs.      (* [fileG], and its [appcfg] field [file_app] *)
Require Import PathElems.        (* [path_elems] *)
Require Import FsTree.           (* [fname] *)
Require Import FsBlocks.         (* [fs_names], [blk_splice] *)
Require Import FsBytesGamma.     (* [fs_gamma_L] *)
Require Import OffGv.            (* [off_gv] *)
Require Import AppCfg.           (* [app_pred] / [app_run] / [MkAppcfg] *)
Require Import AppInv.           (* [app_inv], [app_body], [app_step], [appE] *)
Require Import FsAbsDelta.       (* [cre_pre], [delta_ent], [delta_unl_ent] *)
Require Import FsAbsWriteFire.   (* [awrite_full_at] / [awrite_part_at] / chain *)
Require Import UserPtTree.       (* [uptd]: the partial arm's table *)
Require Import SysUnlinkDefs.    (* [uent_commit_at], [unl_pre] (lane TL-3C
                                    section 3c: the MOVE CONSUMED)         *)
Require Import PieceFam.         (* [pfam] / [pf_at]: a piece's receipt
                                    beside its refund                      *)
Require Import FsAbsCreateFire.  (* create's four commits, [cre_arm_fired] *)
Require Import FsAbsCreateNm.    (* the create commit at a NAME PREDICATE, and its bridges *)
Require Import SpecCreate.       (* [cre_commits], [cre_dots_leg]          *)
Require Import FsAbsEra.         (* [ep_start], [np_elems], [um_start_of]  *)
Require Import SysMknodDefs.     (* [npar_cur], [npar_elems]               *)
Require Import ArgPath.          (* [arg_path_of], [arg_path_of_uniq]      *)
Require Import SpecSysMknod.     (* [mknod_au_at]: the path-fixed bundle   *)
Require Import SpecSysMkdir.     (* [mkdir_au_at]: its twin, at T_DIR      *)
Require Import SysOpenDefs.      (* [open_au_create_at]: open(O_CREATE)    *)
Require Import TreeView.         (* TL-1 *)
Require Import AppTree.          (* TL-2 + TL-3W: the claim, the deed, the move *)
Require Import TreeObs.          (* the claim law at the era's record *)
Require Import FsAbsDefs.        (* [aview] / [anode] / [arow_at] *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  WHAT A RUN OF WRITES DOES TO AN OWNER'S TREE (pure)               *)
(*                                                                       *)
(*  The kernel picks the offset and the bytes of every chunk, so an owner *)
(*  cannot name the tree it will end with.  What it CAN name, and what    *)
(*  the chain's cursor carries, is the RELATION: the same subtree, the    *)
(*  same nodes, and only the file it is writing has moved.                *)
(* ===================================================================== *)

Definition twrote (i : Z) (t t' : ttree) : Prop :=
  tv_root t' = tv_root t
  /\ (forall j : Z, j <> i -> tv_nodes t' !! j = tv_nodes t !! j)
  /\ (exists bs bs' : list (bv 8),
        tv_nodes t !! i = Some (AFile bs) /\ tv_nodes t' !! i = Some (AFile bs')).

Lemma twrote_refl (i : Z) (t : ttree) (bs : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs) -> twrote i t t.
Proof. intros H. split_and!; [done | done |]. by exists bs, bs. Qed.

Lemma twrote_trans (i : Z) (t t' t'' : ttree) :
  twrote i t t' -> twrote i t' t'' -> twrote i t t''.
Proof.
  intros (H1 & H2 & (b1 & b1' & Hb1 & Hb1')) (K1 & K2 & (b2 & b2' & Hb2 & Hb2')).
  split_and!.
  - by rewrite K1 H1.
  - intros j Hj. by rewrite (K2 j Hj) (H2 j Hj).
  - exists b1, b2'. split; [exact Hb1 | exact Hb2'].
Qed.

Lemma twrote_file (i : Z) (t t' : ttree) :
  twrote i t t' -> exists bs' : list (bv 8), tv_nodes t' !! i = Some (AFile bs').
Proof. intros (_ & _ & (b & b' & _ & H')). by exists b'. Qed.

(* ...and the step of the relation the write leg makes *)
Lemma twrote_write (i : Z) (t : ttree) (off : nat) (new bs : list (bv 8)) :
  tv_nodes t !! i = Some (AFile bs) -> twrote i t (top_write i off new t).
Proof.
  intros H. split_and!.
  - by rewrite /top_write /=.
  - intros j Hj. rewrite /top_write /= H.
    apply lookup_insert_ne. congruence.
  - exists bs, (blk_splice off new bs). split; [exact H |].
    rewrite /top_write /= H lookup_insert_eq //.
Qed.

(* ---- 1a.  ...AND WHAT IT DOES NOT DO: MOVE A PATH ------------------- *)
(*                                                                       *)
(*  THE SEAM BETWEEN THE WRITE SIDE AND THE READ SIDE.  A write moves one *)
(*  FILE's content and nothing else, and a walk reads DIRECTORY ENTRIES   *)
(*  only, so every path that resolved before resolves to the same inum    *)
(*  after -- with the new bytes there.  One congruence                    *)
(*  ([TreeView.npath_nents_cong]) and no induction of its own, because a  *)
(*  file's [nents] is [None] in both trees.                              *)

Lemma twrote_dom (i : Z) (t t' : ttree) :
  twrote i t t' -> dom (tv_nodes t') = dom (tv_nodes t).
Proof.
  intros (_ & H2 & (b & b' & Hb & Hb')). apply set_eq. intros j.
  rewrite !elem_of_dom. destruct (decide (j = i)) as [-> | Hne].
  - rewrite Hb Hb'. split; intros _; by eexists.
  - rewrite (H2 j Hne). reflexivity.
Qed.

Lemma twrote_nents (i : Z) (t t' : ttree) :
  twrote i t t' -> forall j : Z, nents (tv_nodes t') j = nents (tv_nodes t) j.
Proof.
  intros (_ & H2 & (b & b' & Hb & Hb')) j. rewrite !nents_unfold.
  destruct (decide (j = i)) as [-> | Hne].
  - rewrite Hb Hb' //.
  - rewrite (H2 j Hne) //.
Qed.

Lemma resolves_from_twrote (i : Z) (t t' : ttree) (d : Z)
    (bs bs' : list (bv 8)) (pl : list (bv 8)) :
  twrote i t t' -> tv_nodes t' !! i = Some (AFile bs') ->
  resolves_from t d pl = Some (i, AFile bs) ->
  resolves_from t' d pl = Some (i, AFile bs').
Proof.
  intros Hw Hi' Hres. rewrite /resolves_from in Hres |- *.
  rewrite (npath_nents_cong (tv_nodes t') (tv_nodes t) d (path_elems pl)
             (twrote_nents i t t' Hw)).
  destruct (npath (tv_nodes t) d (path_elems pl)) as [j |]; [| discriminate].
  destruct (tv_nodes t !! j) as [n |] eqn:Hn0; [| discriminate].
  injection Hres as Hj Hn. subst j. rewrite Hi' //.
Qed.

(* ...and the form the composition actually takes: what the WRITE hands
   back is [∃ t', tree_own … t' ∗ ⌜twrote i t t'⌝], and this turns that
   [t'] into the read side's own premises at the SAME path. *)
Lemma twrote_read_back (i : Z) (t t' : ttree) (d : Z) (bs : list (bv 8))
    (pl : list (bv 8)) :
  twrote i t t' -> d ∈ dom (tv_nodes t) ->
  resolves_from t d pl = Some (i, AFile bs) ->
  exists bs' : list (bv 8),
    d ∈ dom (tv_nodes t') /\ resolves_from t' d pl = Some (i, AFile bs')
    /\ tv_nodes t' !! i = Some (AFile bs').
Proof.
  intros Hw Hd Hres. destruct (twrote_file i t t' Hw) as (bs' & Hi').
  exists bs'. split_and!.
  - by rewrite (twrote_dom i t t' Hw).
  - exact (resolves_from_twrote i t t' d bs bs' pl Hw Hi' Hres).
  - exact Hi'.
Qed.

Section TreeMove.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Context `{!treeG Σ}.

  (* =================================================================== *)
  (*  2.  THE TWO MOVES ON THE CLAIM, AT THE ERA'S RECORD                 *)
  (* =================================================================== *)

  (* THE STEP, WRAPPED: [AppInv.app_step]'s shape at the tree claim.  The
     record equation is rewritten FIRST, as [TreeObs]'s laws do. *)
  Lemma tree_app_step_of (c : tree_fixed) (r : tree_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (tree_pred c r (abs_view I) -∗ tree_pred c r av') -∗ app_step i I av'.
  Proof using .
    intros Heq. rewrite /app_step Heq. cbn [app_pred app_run app_names].
    iIntros "Hw" (n') "%Hav Hp". rewrite Hav. iModIntro. iNext.
    iApply ("Hw" with "Hp").
  Qed.

  (* ...and the one a TAINTED owner hands over: a tainted claim holds of
     every view, which is [AppInv.app_step_acc] without the supply. *)
  Lemma tree_app_step_taint (c : tree_fixed) (r : tree_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_taint c -∗ app_step i I av'.
  Proof using .
    intros Heq. iIntros "#HT".
    iApply (tree_app_step_of c r i I av' Heq). iIntros "_".
    rewrite /tree_pred. iLeft. iExact "HT".
  Qed.

  (* ...and THE UNPAID MOVER'S OWN STEP (SEAM-I's consumer,
     [AppTree.tree_step_bump] at the fire's shape).  This is the step that
     the seam bought: it is NOT an [AppInv.app_step] under the old,
     update-free reading, because paying it SPENDS the era's licence.
     A party holding the era's licence may therefore move the view without
     answering for it, at the price of recording the move as the taint --
     which is exactly what an exec into an unverified image spends
     ([ExecEntry.image_entry_taint] is a wand FROM the taint). *)
  Lemma tree_app_step_bump (c : tree_fixed) (r : tree_names) (i : Z)
      (I : gmap Z fs_node) (av' : aview) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tree_turn c -∗ app_step i I av'.
  Proof using .
    intros Heq. rewrite /app_step Heq. cbn [app_pred app_run app_names].
    iIntros "Hcl" (n') "%Hav Hp". rewrite Hav.
    iMod (tree_taint_mint c with "Hcl") as "#Ht". iModIntro. iNext.
    rewrite /tree_pred. iLeft. iExact "Ht".
  Qed.

  (* PHASE 1's READ: the owner agrees the map the kernel lent it against
     the application's own half and reads its subtree off the claim.
     [UkTreeRead.tree_read_piece]'s three lines, at a LINEAR deed. *)
  Lemma tree_claim_read (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root : Z) (t : ttree) (I : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗ tree_own r g root t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗ tree_own r g root t
      ∗ (⌜subtree (abs_view I) root = Some t⌝ ∨ tree_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv Hown Hka".
    iDestruct (tree_own_claim_law c r Heq) as "#Hlaw".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I)
                ∗ (tree_own r g root t
                   ∗ (⌜subtree (abs_view I) root = Some t⌝ ∨ tree_taint c))))%I
      with "[Hp Hown]" as "[Hp Hrest]".
    { iNext.
      iDestruct ("Hlaw" $! (abs_view I) g root t with "Hown Hp") as "(A & B & C)".
      iFrame "A B C". }
    iMod "Hrest" as "[Hown Hfact]".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka Hown Hfact".
  Qed.

  (* PHASE 2's RESYNC, at the era's record: the ticket buys the entry back
     at the tree the POST view actually has. *)
  Lemma tree_claim_resync (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root : Z) (t t' : ttree) (I' : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    subtree (abs_view I') root = Some t' -> t' <> t ->
    app_inv γfs -∗ tree_tkt r g root t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I'
      ∗ (tree_own r g root t' ∨ tree_taint c).
  Proof using .
    intros Heq Hsub Hne. iIntros "#Hinv Htk Hka".
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I0) "(>Hh & Hp & >%Hdom)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iEval (rewrite Heq; cbn [app_pred app_run app_names]) in "Hp".
    iDestruct "Hp" as ">Hp".
    iMod (tree_resync c r g root t t' (abs_view I') Hsub Hne with "Htk Hp")
      as "[Hp Hout]".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I'. iFrame "Hh".
      iSplitL "Hp".
      - rewrite Heq. cbn [app_pred app_run app_names]. iExact "Hp".
      - iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka Hout".
  Qed.

  (* =================================================================== *)
  (*  3.  THE WRITE CHAIN, PAID OUT OF A DEED                             *)
  (* =================================================================== *)

  (* THE CURSOR: the deed, at a tree that differs from the one the caller
     started with only at the file it is writing. *)
  Definition tree_wq (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) : iProp Σ :=
    ((∃ t' : ttree, tree_own r g root t' ∗ ⌜twrote i t t'⌝) ∨ tree_taint c)%I.

  (* ONE CHUNK, BOTH PHASES.  Common to the FULL and the PARTIAL arm: they
     differ only in the bytes they claim, never in the delta. *)
  Lemma tree_awrite_phases (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root i : Z) (t : ttree) (I : gmap Z fs_node)
      (off : nat) (bs bs0 : list (bv 8)) (nl : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    arow_at (abs_view I) i (MkAnode (AFile bs0) nl) ->
    app_inv γfs -∗ tree_wq c r g root i t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step i I (delta_write i off bs (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         tree_wq c r g root i t).
  Proof using .
    intros Heq Hrow. iIntros "#Hinv Hq Hka".
    rewrite /tree_wq.
    iDestruct "Hq" as "[Hd | #HT]"; last first.
    { (* THE TAINT: the step is free and the cursor comes back tainted *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    iDestruct "Hd" as (t') "[Hown %Hw]".
    iMod (tree_claim_read γfs c r g root t' I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { (* the claim is tainted: keep the deed, pay the step off the taint *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". iLeft.
      iExists t'. iFrame "Hown". by iPureIntro. }
    (* THE EXACT ARM: the owner's tree records the file the fire is at, so
       the fire's [arow_at] row is pinned to the tree's own bytes. *)
    destruct (twrote_file i t t' Hw) as (bst & Hti).
    destruct (tree_file_row (abs_view I) root i t' bst Hsub Hti) as (nl0 & Hav).
    pose proof (arow_at_pinned (abs_view I) i _ _ Hrow Hav) as Hab.
    injection Hab as Hbs Hnl. subst bs0. clear Hnl.
    assert (Hdom : i ∈ dom (tv_nodes t')) by exact (tree_file_dom root i t' bst Hti).
    destruct (decide (blk_splice off bs bst = bst)) as [Hinv0 | Hvis].
    - (* INVISIBLE: the delta is the identity on the view (AppTree 1j), so
         the free step pays it and the deed never moves. *)
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_of c r i I _ Heq).
        iApply (tree_step_write_free c r i off bs bst nl0 (abs_view I) Hav Hinv0). }
      iIntros (I') "%Hav' Hka'". iModIntro. iFrame "Hka'". iLeft.
      iExists t'. iFrame "Hown". by iPureIntro.
    - (* VISIBLE: park the deed and a fresh token, resync at phase 2 *)
      iMod tok_alloc as (γi) "Htok".
      rewrite tree_own_split. iDestruct "Hown" as "[Hdeed Htk]".
      assert (Hne : top_write i off bs t' <> t').
      { intros Hc. exact (Hvis (top_write_id_inv t' i off bs bst Hti Hc)). }
      assert (Hpost : subtree (delta_write i off bs (abs_view I)) root
                      = Some (top_write i off bs t'))
        by exact (subtree_delta_write (abs_view I) root i t' off bs bst nl0
                    Hsub Hav Hdom).
      iModIntro. iFrame "Hka". iSplitL "Hdeed Htok".
      { iApply (tree_app_step_of c r i I _ Heq).
        iApply (tree_step_move_write c r g root i t' off bs bst nl0
                  (abs_view I) γi Hav Hdom with "Hdeed Htok"). }
      iIntros (I') "%Hav' Hka'".
      iMod (tree_claim_resync γfs c r g root t' (top_write i off bs t') I'
              Heq ltac:(rewrite Hav'; exact Hpost) Hne with "Hinv Htk Hka'")
        as "[Hka' Hout]".
      iModIntro. iFrame "Hka'".
      iDestruct "Hout" as "[Hown | #HT]"; [| by iRight].
      iLeft. iExists (top_write i off bs t'). iFrame "Hown". iPureIntro.
      exact (twrote_trans i t t' _ Hw (twrote_write i t' off bs bst Hti)).
  Qed.

  (* THE CHAIN.  Every node offers the CURSOR and both arms; the kernel
     picks, and whichever arm fires builds the next node out of phase 2's
     own result.  This is [FsAbsWriteFire.awrite_chain_unit] with the
     application's SUPPLY replaced by the owner's DEED. *)
  (* THE TREE PAYS BOTH ARMS STILL (lane WRITE-RELAY).  The two relays the
     node gained -- the chunk's LENGTH on the full arm and the partial
     arm's REASON -- are facts the tree claim does not read: [tree_wq] is
     existential in everything the kernel picks, so each node is payable at
     any [(I, off, bs, bs0, nl)] whatever the relays say.  They are
     introduced and dropped.  ([FileWrite]'s node is where they are spent.) *)
  (* the chain AT ONE TABLE; [tree_awrite_chain] below owes every table and
     the tree reads none of them (lane WRITE-RELAY-2's [∀ P]) *)
  Lemma tree_awrite_chain_at (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root i : Z) (t : ttree) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd) (nn : Z) (cnt k : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗ tree_wq c r g root i t -∗
    awrite_chain_at (fs_gamma_L γfs) appE i γo M ua P nn
      (fun _ : nat => tree_wq c r g root i t) k cnt.
  Proof using .
    intros Heq. revert k. induction cnt as [| cnt IH]; intros k.
    { iIntros "#Hinv Hq". rewrite awrite_chain_at_0. iExact "Hq". }
    iIntros "#Hinv Hq". rewrite awrite_chain_at_S. iSplit; [iExact "Hq" |].
    iSplit.
    - rewrite /awrite_full_at.
      iIntros (I off bs bs0 nl) "%Hpre %Hby %Hlen Hka Hoff".
      destruct Hpre as (Hrow & _ & _ & _).
      iMod (tree_awrite_phases γfs c r g root i t I off bs bs0 nl Heq Hrow
              with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
      iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
      iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
      iModIntro. iFrame "Hka'".
      iSplitL "Hoff"; [iApply (off_ret_of_link with "Hoff") |].
      iApply (IH (S k) with "Hinv Hq'").
    - rewrite /awrite_part_at.
      iIntros (I off n bs bs0 nl)
        "%Hpre %Hn %Hgap %Hshort %Hwhy %Hsb1 %Hby Hka Hoff".
      destruct Hpre as (Hrow & _ & _ & _).
      iMod (tree_awrite_phases γfs c r g root i t I off bs bs0 nl Heq Hrow
              with "Hinv Hq Hka") as "(Hka & Hstep & Hph2)".
      iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
      iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hq']".
      iModIntro. iFrame "Hka'".
      iSplitL "Hoff"; [iApply (off_ret_of_link with "Hoff") |].
      iApply (IH (S k) with "Hinv Hq'").
  Qed.

  Lemma tree_awrite_chain (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root i : Z) (t : ttree) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (nn : Z) (cnt k : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗ tree_wq c r g root i t -∗
    awrite_chain (fs_gamma_L γfs) appE i γo M ua nn
      (fun _ : nat => tree_wq c r g root i t) k cnt.
  Proof using .
    intros Heq. rewrite /awrite_chain. iIntros "#Hinv Hq" (P).
    iApply (tree_awrite_chain_at γfs c r g root i t γo M ua P nn cnt k Heq
              with "Hinv Hq").
  Qed.

  (* =================================================================== *)
  (*  3b.  THE CREATE AND UNLINK MOVES, AT A PARENT THE OWNER NAMES        *)
  (*                                                                       *)
  (*  The tree-layer content of section 4's two walled syscalls, in full,   *)
  (*  and AT A GIVEN PARENT [d].  Each is [tree_awrite_phases]'s shape with *)
  (*  the write's inum-indexed row replaced by the parent's: phase 1 reads  *)
  (*  the claim, parks the deed and a fresh token, and hands out the very   *)
  (*  [AppInv.app_step] the fire's commit asks for; phase 2 takes the post  *)
  (*  view and returns the DEED AT THE MOVED TREE.                         *)
  (*                                                                       *)
  (*  WHY THEY ARE NOT [pf_at]-PACKAGED INTO THEIR COMMITS.  Both commits   *)
  (*  QUANTIFY [d] INSIDE ([FsAbsCreateFire.acre_commit_at_gen],            *)
  (*  [SysUnlinkDefs.uent_commit_at]), so a supplier owes the step at EVERY *)
  (*  directory -- including one inside a STRANGER'S subtree, where no step *)
  (*  exists at all.  These two lemmas are exactly the missing quantifier's *)
  (*  other side: hand the owner its own [d] and it pays.  Section 4 states *)
  (*  the wall and prices both fixes.                                       *)
  (* =================================================================== *)

  (* CREATE / MKNOD / OPEN(O_CREATE)'s PARENT LEG.  The delta the commit
     names is the FUSED [delta_create], which at [cre_pre]'s instant -- the
     child already armed -- IS the parent leg alone ([delta_create_armed]),
     and that is the leg TL-1's [own_wf_ent] covers. *)
  Lemma tree_acre_phases (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root d i : Z) (nm : fname) (ch : absnode) (t : ttree)
      (I : gmap Z fs_node) (e : gmap fname Z) (nl : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_pname nm ->
    cre_pre (abs_view I) d nm e nl i ch ->
    tabs_leaf (tabs_of ch) ->
    (* the child is not a DIRECTORY: open(O_CREATE)'s file and mknod's
       device, which is how "the armed inum is nobody's root" is paid
       without a credential from the arm ([TreeView.own_wf_ent_leaf]) *)
    (forall e0 : gmap fname Z, ch <> ADir e0) ->
    (* ...and the arm's other credential: nothing names the armed row
       ([TreeView.aview_no_edge_to_arm] discharges it at the arm) *)
    aview_no_edge_to (abs_view I) i ->
    d ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g root t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step d I (delta_create d nm i ch (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_create d nm i ch (abs_view I)⌝ -∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         (tree_own r g root (top_ins d nm i (tabs_of ch) t) ∨ tree_taint c)).
  Proof using .
    intros Heq Hnm Hpre Hleaf Hnd Hno Hdd. iIntros "#Hinv Hown Hka".
    pose proof (cre_pre_ne (abs_view I) d nm e nl i ch Hpre Hnd) as Hdi.
    pose proof (delta_create_armed (abs_view I) d nm e nl i ch Hpre Hdi) as Hcr.
    destruct Hpre as (Hd & Hnone & Hi).
    assert (Hent : delta_create d nm i ch (abs_view I)
                   = delta_ent d nm i (abs_view I)).
    { rewrite Hcr (delta_ent_dir (abs_view I) d nm i e nl ch 1%nat Hd Hi) //. }
    assert (Hnadir : ~ adir_at (abs_view I) i).
    { intros (a0 & e0 & Ha0 & He0). rewrite Hi in Ha0. injection Ha0 as <-.
      cbn in He0. exact (Hnd e0 He0). }
    iMod (tree_claim_read γfs c r g root t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r d I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    destruct (tree_ent_post (abs_view I) root d nm i (MkAnode ch 1%nat) t e nl
                Hnm Hd Hnone Hi Hleaf Hnadir Hno Hsub Hdd) as [Hpost Hne].
    iMod tok_alloc as (γi) "Htok".
    rewrite tree_own_split. iDestruct "Hown" as "[Hdeed Htk]".
    iModIntro. iFrame "Hka". iSplitL "Hdeed Htok".
    { iApply (tree_app_step_of c r d I _ Heq). rewrite Hent.
      iApply (tree_step_move_ent c r g root d nm i (MkAnode ch 1%nat) t e nl
                (abs_view I) γi Hnm Hd Hnone Hi Hleaf Hnadir Hno Hdd
                with "Hdeed Htok"). }
    iIntros (I') "%Hav Hka'".
    iMod (tree_claim_resync γfs c r g root t (top_ins d nm i (tabs_of ch) t) I'
            Heq ltac:(rewrite Hav Hent; exact Hpost) Hne with "Hinv Htk Hka'")
      as "[Hka' Hout]".
    iModIntro. iFrame "Hka' Hout".
  Qed.

  (* ---- 3b'.  ...AND THE SAME LEG BY THE ROOTED ROUTE (lane TL-3R;
     design/user-tree.md section 7.8's RULING), AT AN OWNER OF "/".
     This is the form the create BUNDLE can actually be supplied at, and
     it is the lane's point: the two credentials [own_wf_ent] asks for are
     no longer premises at all.  What the supplier hands in is ONE PURE
     FACT ABOUT ITS OWN FIXED TREE -- [i ∉ dom (tv_nodes t)], which is
     what the ARM's receipt records ([FsAbsCreateFire.cre_arm_fired]'s own
     [av !! i = None] at the arm's view, read at the owner's tree) -- and
     the claim's [aview_rooted] / [own_rooted] turn it into
     [aview_no_edge_to av i] and "the armed inum is nobody's root" AT THE
     PARENT LEG'S OWN VIEW.  WALL C, closed.

     AND IT TAKES NO [ch <> ADir] PREMISE: mkdir's DIRECTORY child is
     covered too, which is (C-iii-b) -- [own_wf_ent_leaf]'s free
     discharge only ever reached a non-directory child. *)
  Lemma tree_acre_phases_rooted (γfs : fs_names) (c : tree_fixed)
      (r : tree_names) (g : gname) (d i : Z) (nm : fname) (ch : absnode)
      (t : ttree) (I : gmap Z fs_node) (e : gmap fname Z) (nl : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_pname nm ->
    cre_pre (abs_view I) d nm e nl i ch ->
    tabs_leaf (tabs_of ch) ->
    (* THE ARM'S PURE RECEIPT *)
    i ∉ dom (tv_nodes t) ->
    d ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step d I (delta_create d nm i ch (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_create d nm i ch (abs_view I)⌝ -∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         (tree_own r g FsImg.ROOTINO (top_ins d nm i (tabs_of ch) t)
          ∨ tree_taint c)).
  Proof using .
    intros Heq Hnm Hpre Hleaf Hni Hdd. iIntros "#Hinv Hown Hka".
    assert (Hdi : d <> i) by (intros ->; exact (Hni Hdd)).
    pose proof (delta_create_armed (abs_view I) d nm e nl i ch Hpre Hdi) as Hcr.
    destruct Hpre as (Hd & Hnone & Hi).
    assert (Hent : delta_create d nm i ch (abs_view I)
                   = delta_ent d nm i (abs_view I)).
    { rewrite Hcr (delta_ent_dir (abs_view I) d nm i e nl ch 1%nat Hd Hi) //. }
    assert (Hidom : i ∈ dom (abs_view I)) by (apply elem_of_dom; by eexists).
    iMod (tree_claim_read γfs c r g FsImg.ROOTINO t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r d I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    pose proof (tree_unreached_of_arm (abs_view I) t i Hsub Hidom Hni) as Hunr.
    destruct (tree_ent_post_unr (abs_view I) FsImg.ROOTINO d nm i
                (MkAnode ch 1%nat) t e nl Hnm Hd Hnone Hi Hleaf Hunr Hsub Hdd)
      as [Hpost Hne].
    iMod tok_alloc as (γi) "Htok".
    rewrite tree_own_split. iDestruct "Hown" as "[Hdeed Htk]".
    iModIntro. iFrame "Hka". iSplitL "Hdeed Htok".
    { iApply (tree_app_step_of c r d I _ Heq). rewrite Hent.
      iApply (tree_step_move_ent_rooted c r g d nm i (MkAnode ch 1%nat) t e nl
                (abs_view I) γi Hnm Hd Hnone Hi Hleaf Hni Hdd
                with "Hdeed Htok"). }
    iIntros (I') "%Hav Hka'".
    iMod (tree_claim_resync γfs c r g FsImg.ROOTINO t
            (top_ins d nm i (tabs_of ch) t) I'
            Heq ltac:(rewrite Hav Hent; exact Hpost) Hne with "Hinv Htk Hka'")
      as "[Hka' Hout]".
    iModIntro. iFrame "Hka' Hout".
  Qed.

  (* UNLINK'S ENTRY LEG, at a parent the owner names.  The premises are
     [SysUnlinkDefs.unl_pre]'s first two conjuncts and the name's
     properness -- everything else that predicate carries is about the
     TARGET row, which the tree does not read at this leg. *)
  Lemma tree_uent_phases (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root d tg : Z) (nm : fname) (dec : nat) (t : ttree)
      (I : gmap Z fs_node) (e : gmap fname Z) (nl : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_pname nm ->
    abs_view I !! d = Some (MkAnode (ADir e) nl) ->
    e !! nm = Some tg ->
    (* THE ENTRY LEG'S SHAPE (lane TL-3R): the target has NO PROPER
       OUT-EDGE.  It is [unl_pre]'s own [dots_only] clause, read through
       [unl_pre_tgt_leaf] below, and it is what makes the cut LOCAL --
       see [AppTree.tree_step_move_unl_ent]. *)
    (forall s : fname, fs_pname s -> astep (abs_view I) tg s = None) ->
    d ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g root t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step d I (delta_unl_ent d nm dec (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_unl_ent d nm dec (abs_view I)⌝ -∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         (tree_own r g root (top_unlink d nm t) ∨ tree_taint c)).
  Proof using .
    intros Heq Hnm Hd Hnm0 Hlf Hdd. iIntros "#Hinv Hown Hka".
    iMod (tree_claim_read γfs c r g root t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r d I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    pose proof (tree_row_dir (abs_view I) root d t e nl Hsub Hdd Hd) as Hrow.
    assert (Hne : top_unlink d nm t <> t).
    { apply (top_unlink_ne t d nm (hide_dots e) tg Hrow).
      rewrite (hide_dots_lookup e nm Hnm) //. }
    pose proof (subtree_delta_unl_ent (abs_view I) root d nm dec t e nl
                  Hsub Hd Hdd) as Hpost.
    iMod tok_alloc as (γi) "Htok".
    rewrite tree_own_split. iDestruct "Hown" as "[Hdeed Htk]".
    iModIntro. iFrame "Hka". iSplitL "Hdeed Htok".
    { iApply (tree_app_step_of c r d I _ Heq).
      iApply (tree_step_move_unl_ent c r g root d nm dec t e nl tg
                (abs_view I) γi Hnm Hd Hnm0 Hlf Hdd with "Hdeed Htok"). }
    iIntros (I') "%Hav Hka'".
    iMod (tree_claim_resync γfs c r g root t (top_unlink d nm t) I'
            Heq ltac:(rewrite Hav; exact Hpost) Hne with "Hinv Htk Hka'")
      as "[Hka' Hout]".
    iModIntro. iFrame "Hka' Hout".
  Qed.

  (* =================================================================== *)
  (*  3c.  THE MOVE CONSUMED: unlink's ENTRY LEG, AS THE BUNDLE TAKES IT  *)
  (*      (lane TL-3C; design/user-tree.md section 7.7)                   *)
  (*                                                                     *)
  (*  This is section 3b's [tree_uent_phases] at the shape               *)
  (*  [SpecSysUnlink.unlink_au_at] actually asks for, and it exists       *)
  (*  because THREE things landed: WALL A's cursor (TL-3K), the          *)
  (*  path-fixed unlink bundle (TL-3C item (M)) and -- for free --       *)
  (*  [unl_pre]'s own [nm <> DOT /\ nm <> DOTDOT], which is [fs_pname nm] *)
  (*  and is the premise create needed a whole credential for (WALL D).   *)
  (*                                                                     *)
  (*  WHAT THE CURSOR DOES HERE, in one line: [uent_commit_at] quantifies *)
  (*  its parent [d] INSIDE, and an owner has NO STEP at a [d] inside a   *)
  (*  stranger's subtree (section 4's WALL A).  At [Pd d := d = dpar] the *)
  (*  premise DECIDES [d], so the supplier owes one step and not a        *)
  (*  family of them.  The cursor is PURE, so it is read and handed back  *)
  (*  for nothing -- which is exactly why a parent prefix of LENGTH ZERO  *)
  (*  needs no phase-2 cursor return (section 7.7's (R)).                 *)
  (*                                                                     *)
  (*  WHAT IS STILL MISSING FOR A COROLLARY, and it is not this leg:      *)
  (*  unlink's TARGET leg ([SysUnlinkDefs.utgt_commit_at]) quantifies its *)
  (*  own [t] with no cursor at all, and at the LAST LINK the row LEAVES  *)
  (*  -- so it wants [aview_no_edge_to av t] (WALL C) at a non-directory  *)
  (*  target and TL-2's rmdir-shaped wall at a directory one.             *)
  (* =================================================================== *)

  (* [unl_pre]'s [dots_only] clause, READ AS THE TREE LAYER NEEDS IT: the
     target of the name being cut has no PROPER out-edge.  At a file or a
     device there is no entry map at all; at a directory the map holds
     nothing but the dots, which the tree hides. *)
  Lemma unl_pre_tgt_leaf (av : aview) (d : Z) (nm : fname)
      (ents : gmap fname Z) (nl : nat) (tg : Z) (a : anode) :
    unl_pre av d nm ents nl tg a ->
    forall s : fname, fs_pname s -> astep av tg s = None.
  Proof using .
    intros (_ & _ & _ & _ & _ & Ht & _ & Hdots) s Hs.
    rewrite /astep /aents Ht /= /anode_ents.
    destruct (an_node a) as [bs | es | ma mi] eqn:Hn;
      [reflexivity | | reflexivity].
    cbn. destruct (es !! s) as [j |] eqn:He; [| reflexivity].
    exfalso. destruct (Hdots es eq_refl s (mk_is_Some _ _ He)) as [Hc | Hc];
      [exact (proj1 Hs Hc) | exact (proj2 Hs Hc)].
  Qed.

  (* the owner's family at this piece: the RECEIPT is the moved deed (or
     the taint) and the REFUND is the deed it put in -- the [∧] of [pf_at]
     is what lets ONE deed answer both, which is design section 7.2's
     refund arm. *)
  Definition tree_uent_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t : ttree) : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    {| pf_recv := (fun (_ : aview) (d : Z) (nm : fname) (_ : Z) =>
                     (tree_own r g root (top_unlink d nm t) ∨ tree_taint c)%I) ;
       pf_refund := tree_own r g root t |}.

  Lemma tree_uent_commit (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root dpar : Z) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    dpar ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g root t -∗
    uent_commit_at (fs_gamma_L γfs) appE (fun d : Z => ⌜d = dpar⌝%I)
      (tree_uent_fam c r g root t).(pf_recv).
  Proof using .
    intros Heq Hdd. iIntros "#Hinv Hown".
    rewrite /uent_commit_at.
    iIntros (I d tg nm ents nl a) "%Hpre %Hd Hka". subst d.
    pose proof (unl_pre_tgt_leaf (abs_view I) dpar nm ents nl tg a Hpre) as Hlf.
    destruct Hpre as (Hdrow & Hent & HnD & HnDD & _ & _ & _ & _).
    iMod (tree_uent_phases γfs c r g root dpar tg nm
            (unl_dec (an_node a)) t I ents nl Heq (conj HnD HnDD)
            Hdrow Hent Hlf Hdd with "Hinv Hown Hka") as "(Hka & Hstep & Hph2)".
    iModIntro. iFrame "Hka". iSplitR; [done |]. iFrame "Hstep".
    iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hout]".
    iModIntro. iFrame "Hka'". cbn [pf_recv]. iExact "Hout".
  Qed.

  (* ...and THE PIECE, as [SpecSysUnlink.unlink_au_at]'s first commit row
     takes it: the AU conjoined with its refund, both out of the ONE deed. *)
  Lemma tree_uent_piece (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (root dpar : Z) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    dpar ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g root t -∗
    pf_at (uent_commit_at (fs_gamma_L γfs) appE (fun d : Z => ⌜d = dpar⌝%I))
      (tree_uent_fam c r g root t).
  Proof using .
    intros Heq Hdd. iIntros "#Hinv Hown". iApply pf_at_intro. iSplit.
    - iApply (tree_uent_commit γfs c r g root dpar t Heq Hdd with "Hinv Hown").
    - cbn [pf_refund]. iExact "Hown".
  Qed.


  (* =================================================================== *)
  (*  3d.  THE CREATE MOVE CONSUMED: THE WHOLE FOUR-LEG BUNDLE, FROM ONE  *)
  (*      DEED (lane TL-3R; design/user-tree.md section 7.8)              *)
  (*                                                                     *)
  (*  HOW ONE DEED ANSWERS FOUR [*]-JOINED LEGS, which is the shape       *)
  (*  question this section had to settle.  It is [FsAbsCreateFire]'s own *)
  (*  answer, at a different resource: THE DEED GOES INTO THE ARM'S LEG   *)
  (*  and comes out in the ARM'S RECEIPT, and the two legs that can end   *)
  (*  the armed inode -- the parent leg and the unarm -- each TAKE that   *)
  (*  receipt ([cre_arm_fired]) and so are supplied from NOTHING but      *)
  (*  [app_inv].  The kernel holds one permit per armed inode and fires   *)
  (*  at most one of them, so the deed is never duplicated; and the       *)
  (*  arm's receipt carries, beside the deed, the PURE credential         *)
  (*  [i ∉ dom (tv_nodes t)] that the parent leg turns into               *)
  (*  [aview_no_edge_to] through the rooted view (section 3b').           *)
  (*                                                                     *)
  (*  The dots leg is FREE at every owner (the tree hides the dots), and  *)
  (*  every leg's refund is the deed itself or [True], so a syscall that  *)
  (*  fails before the arm hands the deed straight back.                  *)
  (* =================================================================== *)

  (* create's child kinds are all LEAVES of the application tree: an empty
     file, a device, and a directory holding nothing but its dots. *)
  Lemma tabs_leaf_cre_c0 (tyz ma mi : Z) : tabs_leaf (tabs_of (cre_c0 tyz ma mi)).
  Proof using .
    rewrite /cre_c0. case_decide as H1.
    - intros e0 He0. cbn in He0. injection He0 as <-.
      rewrite /hide_dots !delete_empty //.
    - case_decide as H2; intros e0 He0; cbn in He0; discriminate.
  Qed.

  Lemma tabs_leaf_cre_child (tyz ma mi d i : Z) :
    tabs_leaf (tabs_of (cre_child tyz ma mi d i)).
  Proof using .
    rewrite /cre_child. case_decide as H1; [| apply tabs_leaf_cre_c0].
    intros e0 He0. cbn in He0. injection He0 as <-.
    rewrite /dots_ents /hide_dots.
    rewrite (delete_insert_ne _ DOTDOT DOT);
      [| intros Hc; exact (dot_ne_dotdot (eq_sym Hc))].
    rewrite !delete_insert_eq !delete_empty //.
  Qed.

  (* THE CLAIM'S PURE CONJUNCTS, read at the fire without a deed: this is
     [AppTree.tree_pred_facts] under [app_inv], and it is what turns the
     arm's receipt into create's missing credential at the UNARM leg (the
     parent leg reads them inside its own step, section 1k). *)
  Lemma tree_claim_facts (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (I : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      (⌜aview_tree_wf (abs_view I) /\ adir_at (abs_view I) FsImg.ROOTINO
        /\ aview_rooted (abs_view I)⌝ ∨ tree_taint c).
  Proof using .
    intros Heq. iIntros "#Hinv Hka".
    iAssert (□ (∀ v : aview, app_pred app_run v -∗
                  app_pred app_run v ∗
                  (⌜aview_tree_wf v /\ adir_at v FsImg.ROOTINO
                    /\ aview_rooted v⌝ ∨ tree_taint c)))%I as "#Hlaw".
    { rewrite Heq. cbn [app_pred app_run app_names]. iIntros "!>" (v) "Hp".
      iApply (tree_pred_facts c r v with "Hp"). }
    iMod (inv_acc appE appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I') "(>Hh & Hp & >%Hdom)".
    iDestruct (ghost_map_auth_agree with "Hka Hh") as %<-.
    iAssert (▷ (app_pred app_run (abs_view I)
                ∗ (⌜aview_tree_wf (abs_view I)
                    /\ adir_at (abs_view I) FsImg.ROOTINO
                    /\ aview_rooted (abs_view I)⌝ ∨ tree_taint c)))%I
      with "[Hp]" as "[Hp Hrest]".
    { iNext. iDestruct ("Hlaw" $! (abs_view I) with "Hp") as "[A B]".
      iFrame "A B". }
    iMod "Hrest" as "Hfact".
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "Hka Hfact".
  Qed.

  (* ---- THE ARM'S FAMILY: the deed parked in the receipt, beside the
     PURE credential the parent leg needs ------------------------------ *)

  Definition tree_arm_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) : pfam Σ (aview -> Z -> iProp Σ) :=
    {| pf_recv := (fun (_ : aview) (i : Z) =>
                     ((⌜i ∉ dom (tv_nodes t)⌝
                       ∗ tree_own r g FsImg.ROOTINO t) ∨ tree_taint c)%I) ;
       pf_refund := tree_own r g FsImg.ROOTINO t |}.

  Lemma tree_arm_commit (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (ch : absnode) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tabs_leaf (tabs_of ch) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    aarm_commit_at (fs_gamma_L γfs) appE ch (tree_arm_fam c r g t).(pf_recv).
  Proof using .
    intros Heq Hleaf. iIntros "#Hinv Hown".
    rewrite /aarm_commit_at. iIntros (I i) "%Hnone %Hsome Hka".
    iMod (tree_claim_read γfs c r g FsImg.ROOTINO t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    (* THE CREDENTIAL, ESTABLISHED: the armed inum is no row of the view at
       this instant, and the owner's tree's nodes ARE rows of the view. *)
    assert (Hni : i ∉ dom (tv_nodes t)).
    { intros Hin.
      pose proof (subtree_dom_view (abs_view I) FsImg.ROOTINO t i Hsub Hin) as Hd.
      apply elem_of_dom in Hd as [a Ha]. rewrite Ha in Hnone. discriminate. }
    iModIntro. iFrame "Hka". iSplitR "Hown".
    { iApply (tree_app_step_of c r i I _ Heq).
      iApply (tree_step_arm c r (abs_view I) i ch Hnone Hleaf). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. iSplitR; [by iPureIntro | iExact "Hown"].
  Qed.

  (* ---- THE UNARM LEG, FREE (design section 7.4's WALL 2, closed): the
     arm's receipt hands back the deed AND the credential, and the rooted
     view turns the credential into "nothing names the row" at the
     UNARM's own view. ------------------------------------------------- *)

  Definition tree_unarm_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) : pfam Σ (aview -> Z -> iProp Σ) :=
    {| pf_recv := (fun (_ : aview) (_ : Z) =>
                     (tree_own r g FsImg.ROOTINO t ∨ tree_taint c)%I) ;
       pf_refund := True%I |}.

  Lemma tree_unarm_commit (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    app_inv γfs -∗
    aunarm_of_arm (fs_gamma_L γfs) appE (tree_arm_fam c r g t)
      (tree_unarm_fam c r g t).(pf_recv).
  Proof using .
    intros Heq. iIntros "#Hinv". rewrite /aunarm_of_arm.
    iIntros (i) "Harm". rewrite /cre_arm_fired.
    iDestruct "Harm" as (av0) "[_ Hrec]". cbn [pf_recv].
    rewrite /aunarm_commit_at. iIntros (I c0) "%Hi Hka".
    iDestruct "Hrec" as "[[%Hni Hown] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    iMod (tree_claim_read γfs c r g FsImg.ROOTINO t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    iMod (tree_claim_facts γfs c r I Heq with "Hinv Hka")
      as "(Hka & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r i I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    destruct Hf as (Hwf & Hrt & Hro).
    assert (Hne : i <> FsImg.ROOTINO).
    { intros ->.
      exact (Hni (subtree_root_dom (abs_view I) FsImg.ROOTINO t Hsub)). }
    pose proof (aview_no_edge_to_rooted (abs_view I) t i Hro (proj2 Hwf)
                  Hsub Hni) as Hno.
    iModIntro. iFrame "Hka". iSplitR "Hown".
    { iApply (tree_app_step_of c r i I _ Heq).
      iApply (tree_step_unarm c r (abs_view I) i (MkAnode c0 1%nat)
                Hi eq_refl Hno Hne). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
    iLeft. iExact "Hown".
  Qed.

  (* ---- THE DOTS LEG, FREE AT EVERY OWNER: the tree hides the dots ---- *)

  Lemma tree_dots_commit (γfs : fs_names) (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    ⊢ adots_commit_at (fs_gamma_L γfs) appE (fun _ _ _ _ => True%I).
  Proof using .
    intros Heq. rewrite /adots_commit_at.
    iIntros (I i d full) "%Hi Hka". iModIntro. iFrame "Hka". iSplitR.
    { iApply (tree_app_step_of c r i I _ Heq). rewrite /dots_delta.
      destruct full; [iApply tree_step_dots | iApply tree_step_dot]. }
    iIntros (I') "%Hav Hka'". iModIntro. by iFrame "Hka'".
  Qed.

  (* ---- THE PARENT LEG, AT THE BUNDLE'S SHAPE ------------------------- *)

  Definition tree_acre_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (cf : Z -> Z -> absnode)
      : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ) :=
    {| pf_recv := (fun (_ : aview) (d : Z) (nm : fname) (i : Z) =>
                     (tree_own r g FsImg.ROOTINO
                        (top_ins d nm i (tabs_of (cf d i)) t)
                      ∨ tree_taint c)%I) ;
       pf_refund := True%I |}.

  Lemma tree_acre_commit (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cf : Z -> Z -> absnode) (dpar : Z) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (forall d i : Z, tabs_leaf (tabs_of (cf d i))) ->
    dpar ∈ dom (tv_nodes t) ->
    app_inv γfs -∗
    acre_commit_at_gen (fs_gamma_L γfs) appE cf (fun d : Z => ⌜d = dpar⌝%I)
      (tree_arm_fam c r g t) (tree_acre_fam c r g t cf).(pf_recv).
  Proof using .
    intros Heq Hleaf Hdd. iIntros "#Hinv". rewrite /acre_commit_at_gen.
    iIntros (I d i nm ents nl) "%Hpre %Hnm Harm %Hd Hka". subst d.
    rewrite /cre_arm_fired. iDestruct "Harm" as (av0) "[_ Hrec]".
    cbn [pf_recv]. iDestruct "Hrec" as "[[%Hni Hown] | #HT]"; last first.
    { iModIntro. iFrame "Hka". iSplitR; [done |]. iSplitR.
      { iApply (tree_app_step_taint c r dpar I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". cbn [pf_recv].
      by iRight. }
    iMod (tree_acre_phases_rooted γfs c r g dpar i nm (cf dpar i) t I ents nl
            Heq Hnm Hpre (Hleaf dpar i) Hni Hdd with "Hinv Hown Hka")
      as "(Hka & Hstep & Hph2)".
    iModIntro. iFrame "Hka". iSplitR; [done |]. iFrame "Hstep".
    iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "[Hka' Hout]".
    iModIntro. iFrame "Hka'". cbn [pf_recv]. iExact "Hout".
  Qed.

  (* ---- ...AND THE WHOLE BUNDLE, FROM ONE DEED ----------------------- *)

  Lemma tree_cre_commits (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (tyz ma mi dpar : Z) (Nm : fname -> Prop)
      (Nd : absnode -> Prop) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    dpar ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    cre_commits (fs_gamma_L γfs) tyz ma mi Nm Nd (fun d : Z => ⌜d = dpar⌝%I)
      (tree_arm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I))
      (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (cre_child tyz ma mi)).
  Proof using .
    intros Heq Hdd. iIntros "#Hinv Hown". rewrite /cre_commits.
    iSplitL "Hown".
    { rewrite /pf_at. iSplit; [| cbn [pf_refund]; iExact "Hown"].
      iApply (tree_arm_commit γfs c r g t (cre_c0 tyz ma mi) Heq
                (tabs_leaf_cre_c0 tyz ma mi) with "Hinv Hown"). }
    iSplitR.
    { iApply cre_dots_leg_of. iApply pf_at_triv.
      iApply (tree_dots_commit γfs c r Heq). }
    iSplitR.
    { rewrite /pf_at. iSplit; [| cbn [pf_refund]; done].
      iApply (aunarm_of_arm_nd_of (fs_gamma_L γfs) appE Nd
                (tree_arm_fam c r g t) _).
      iApply (tree_unarm_commit γfs c r g t Heq with "Hinv"). }
    rewrite /pf_at. iSplit; [| cbn [pf_refund]; done].
    (* a provider that answers at EVERY name answers at the ones [Nm]
       admits ([FsAbsCreateNm.acre_commit_at_gen_nm_of]) *)
    iApply (acre_commit_at_gen_nm_of (fs_gamma_L γfs) appE
              (cre_child tyz ma mi) Nm _ _ _).
    iApply (tree_acre_commit γfs c r g t (cre_child tyz ma mi) dpar Heq
              (fun d i => tabs_leaf_cre_child tyz ma mi d i) Hdd with "Hinv").
  Qed.


  (* =================================================================== *)
  (*  3f.  THE MKNOD BUNDLE, AT A PARENT PREFIX OF LENGTH ZERO            *)
  (*      (lane TL-3R; design/user-tree.md section 7.7's (R))             *)
  (*                                                                     *)
  (*  The owner of "/" calling [mknod("/dev", ...)].  THE CURSOR IS PURE  *)
  (*  HERE, which is what makes the split-cursor seam (R) not a           *)
  (*  prerequisite: at [np_elems pl = []] the walk reads NO claim law     *)
  (*  ([ep_hops_from] is the empty big-op and [ep_start] is the start     *)
  (*  cursor alone), so the owner's [P] can be [⌜d = ROOTINO⌝], which is  *)
  (*  duplicable and returns itself in phase 1.                          *)
  (*                                                                     *)
  (*  AND THE DEED IS IN EXACTLY ONE LEG: the ARM's.  Section 3d says     *)
  (*  why -- the parent leg and the unarm each take the arm's receipt,    *)
  (*  and the walk and the [dirlookup] observation are free.             *)
  (* =================================================================== *)

  Lemma tabs_leaf_dev (ma mi : Z) : tabs_leaf (tabs_of (ADev ma mi)).
  Proof using . intros e0 He0. cbn in He0. discriminate. Qed.

  Lemma tree_mknod_au (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cw ma mi : Z) (M : gmap Z (bv 8))
      (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    arg_path_of M pv pl ->
    (* the parent prefix is EMPTY -- "/dev", not "/a/dev" *)
    np_elems pl = [] ->
    (* ...and the walk starts at the era's root *)
    um_start_of cw pl = FsImg.ROOTINO ->
    (* the parent leg's [d ∈ dom (tv_nodes t)] at this prefix, which is a
       fact about the owner's OWN tree: every tree the claim ever hands
       out has its root among its nodes ([TreeView.subtree_root_dom]) *)
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    mknod_au_at (fs_gamma_L γfs) γfs cw M pv ma mi
      (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I)
      (fun _ _ => True%I)
      (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (fun _ _ => ADev ma mi))
      (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    intros Heq Hpath Hnp Hstart Hdd. iIntros "#Hinv Hown".
    rewrite /mknod_au_at. iSplitR.
    { (* THE WALK: no hops at all, and the start cursor is pure *)
      iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR "Hown"; last first.
    { iSplitR.
      { (* the [dirlookup] observation is read-only and free *)
        iApply pf_at_triv. iApply dlookup_commit_at_unit. }
      (* THE CHILD'S TWO LEGS: the deed goes in HERE and comes back out in
         the arm's receipt *)
      rewrite /cre_child_unfired_nd. iSplitL "Hown".
      - rewrite /pf_at /tree_arm_fam /=. iSplit; [| iExact "Hown"].
        iApply (tree_arm_commit γfs c r g t (ADev ma mi) Heq
                  (tabs_leaf_dev ma mi) with "Hinv Hown").
      - rewrite /pf_at /tree_unarm_fam /=. iSplit; [| done].
        (* the unarm at the node sys_mknod PINS: a provider that answers at
           EVERY node answers at that one
           ([FsAbsCreateNm.aunarm_of_arm_nd_of]) *)
        iApply (aunarm_of_arm_nd_of (fs_gamma_L γfs) appE
                  (fun c' : absnode => c' = ADev ma mi)
                  (tree_arm_fam c r g t) _).
        iApply (tree_unarm_commit γfs c r g t Heq with "Hinv"). }
    (* THE PARENT LEG, at the guarded cursor: the move between the two
       readings is the ISO, and it costs nothing because the cursor is
       PURE at this prefix. *)
    rewrite /pf_at /tree_acre_fam /=. iSplit; [| done].
    rewrite /acre_commit_at_nm.
    iApply (acre_commit_at_gen_nm_of (fs_gamma_L γfs) appE
              (fun _ _ => ADev ma mi) (npar_nm M pv) _ _ _).
    iApply (acre_commit_at_gen_mono (fs_gamma_L γfs) appE
              (fun _ _ => ADev ma mi)
              (fun d : Z => ⌜d = FsImg.ROOTINO⌝%I)
              (npar_cur M pv (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I))
              (tree_arm_fam c r g t)
              (tree_acre_fam c r g t (fun _ _ => ADev ma mi)).(pf_recv)
              with "[] [] []").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (tree_acre_commit γfs c r g t (fun _ _ => ADev ma mi)
                FsImg.ROOTINO Heq (fun d i => tabs_leaf_dev ma mi) Hdd
                with "Hinv").
  Qed.



  (* ...AND open(O_CREATE)'s, which is mknod's with an empty FILE child,
     the (read-only) open observation and -- at [O_TRUNC] CLEAR -- no
     truncate leg at all. *)
  Lemma tabs_leaf_file : tabs_leaf (tabs_of (AFile [])).
  Proof using . intros e0 He0. cbn in He0. discriminate. Qed.

  Lemma tree_open_create_au (γfs : fs_names) (c : tree_fixed)
      (r : tree_names) (g : gname) (t : ttree) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    om_trunc vom = false ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    open_au_create_at (fs_gamma_L γfs) γfs cw M pv vom
      (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I)
      (fun _ _ => True%I)
      (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (fun _ _ => AFile []))
      (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)).
  Proof using .
    intros Heq Hpath Hnp Hstart Htr Hdd. iIntros "#Hinv Hown".
    rewrite /open_au_create_at. iSplitR.
    { iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR "Hown"; last first.
    { iSplitR.
      { iApply pf_at_triv. iApply dlookup_commit_at_unit. }
      iSplitR.
      { (* the open observation is READ-ONLY: it reads the row and returns
           it, and the tree claim asks nothing of it *)
        iApply pf_at_triv. rewrite /aopen_commit_at.
        iIntros (I i a) "%Hrow Hka". iModIntro. by iFrame "Hka". }
      iSplitR.
      { iApply (open_trunc_piece_none _ vom _ _ Htr). }
      rewrite /cre_child_unfired. iSplitL "Hown".
      - rewrite /pf_at /tree_arm_fam /=. iSplit; [| iExact "Hown"].
        iApply (tree_arm_commit γfs c r g t (AFile []) Heq tabs_leaf_file
                  with "Hinv Hown").
      - rewrite /pf_at /tree_unarm_fam /=. iSplit; [| done].
        iApply (tree_unarm_commit γfs c r g t Heq with "Hinv"). }
    rewrite /pf_at /tree_acre_fam /=. iSplit; [| done].
    rewrite /acre_commit_at_nm.
    (* the tree claim answers the create at EVERY name, so a fortiori at
       the one argument 0 spells ([FsAbsCreateNm.acre_commit_at_gen_nm_of]) *)
    iApply (acre_commit_at_gen_nm_of (fs_gamma_L γfs) appE
              (fun _ _ => AFile []) (npar_nm M pv)).
    iApply (acre_commit_at_gen_mono (fs_gamma_L γfs) appE
              (fun _ _ => AFile [])
              (fun d : Z => ⌜d = FsImg.ROOTINO⌝%I)
              (npar_cur M pv (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I))
              (tree_arm_fam c r g t)
              (tree_acre_fam c r g t (fun _ _ => AFile [])).(pf_recv)
              with "[] [] []").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (tree_acre_commit γfs c r g t (fun _ _ => AFile [])
                FsImg.ROOTINO Heq (fun d i => tabs_leaf_file) Hdd
                with "Hinv").
  Qed.

  (* [SpecSysMkdir.mkdir_au_at] carries a [GenId] binder of its own, so
     the mkdir bundle lives in a nested section: no landed statement of
     this file gains a binder. *)
  Section TreeMoveDir.
    Context `{GEN : GenId}.

  (* ...AND MKDIR'S, which is the same bundle with the DOTS leg and at a
     DIRECTORY child -- the case [own_wf_ent_leaf] could never reach, and
     which (C-iii-b) closes: the "armed inum is nobody's root" credential
     comes off [own_rooted] and not off the child's kind. *)
  Lemma tree_mkdir_au (γfs : fs_names) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cw : Z) (M : gmap Z (bv 8))
      (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    arg_path_of M pv pl ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    mkdir_au_at (fs_gamma_L γfs) γfs cw M pv
      (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I)
      (fun _ _ => True%I)
      (tree_arm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I))
      (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t
         (cre_child (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16))))
      (pfam_triv (fun _ _ _ _ => True%I)).
  Proof using .
    intros Heq Hpath Hnp Hstart Hdd. iIntros "#Hinv Hown".
    rewrite /mkdir_au_at. iSplitR.
    { iIntros (pl0) "%Hpath0".
      rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
      rewrite /ep_start. iIntros (r0) "%Hr0". iModIntro. iSplitR.
      - iPureIntro. rewrite Hr0 Hstart //.
      - iApply (ep_hops_done γfs _ _ pl 0%nat). rewrite Hnp /=. lia. }
    iSplitR.
    { iApply pf_at_triv. iApply dlookup_commit_at_unit. }
    iApply (cre_commits_mono (fs_gamma_L γfs) _ _ _ _ _
              (fun d : Z => ⌜d = FsImg.ROOTINO⌝%I)
              (npar_cur M pv (fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I))
              with "[] [] [Hown]").
    - iIntros "!>" (d) "H". rewrite /npar_cur.
      iApply ("H" $! pl). iPureIntro. exact Hpath.
    - iIntros "!>" (d) "%Hd". rewrite /npar_cur. iIntros (pl0) "_".
      by iPureIntro.
    - iApply (tree_cre_commits γfs c r g t _ _ _ FsImg.ROOTINO _ _ Heq Hdd
                with "Hinv Hown").
  Qed.

  End TreeMoveDir.

  (* =================================================================== *)
  (*  3e.  UNLINK'S TARGET LEG, AT A GIVEN TARGET (lane TL-3R)            *)
  (*                                                                     *)
  (*  THE CREDENTIAL IS NO LONGER THE BLOCKER, AND THE KIND IS NOT        *)
  (*  EITHER.  After the ENTRY leg has cut [d.nm], the target is no node  *)
  (*  of the owner's MOVED tree ([top_unlink]), and the rooted view turns *)
  (*  that into BOTH of [own_wf_unl_tgt]'s premises at the target leg's   *)
  (*  own view -- "nothing names it" and "it is nobody's root".  So       *)
  (*  TL-2's rmdir-shaped wall falls too: a DIRECTORY's last link is      *)
  (*  covered here, where [tree_step_unl_tgt_last] (which pays “nobody's  *)
  (*  root” from the target's KIND) reaches only a file or a device.      *)
  (*                                                                     *)
  (*  WHAT IS STILL OWED, and it is a QUANTIFIER and not a credential:    *)
  (*  [SysUnlinkDefs.utgt_commit_at] binds its target [t] INSIDE with no  *)
  (*  cursor, so a supplier owes a step at EVERY row of every view at     *)
  (*  count >= 1 -- including a row that IS named, where [delta_unl_tgt]  *)
  (*  leaves a DANGLING ENTRY and no step exists for anybody.  That is    *)
  (*  WALL A at instant 2, and its fix is TL-3K's, verbatim: a cursor     *)
  (*  [Pt : Z -> iProp] beside the commit's premise, plus a channel from  *)
  (*  the ENTRY leg's receipt to the target leg (the deed has to arrive   *)
  (*  MOVED), which is [cre_arm_fired]'s trick at the unlink family.      *)
  (*  This lemma is exactly what such a commit would consume.             *)
  (* =================================================================== *)

  Lemma tree_utgt_phases_rooted (γfs : fs_names) (c : tree_fixed)
      (r : tree_names) (g : gname) (tg : Z) (a : anode) (t : ttree)
      (I : gmap Z fs_node) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    abs_view I !! tg = Some a -> an_nlink a = 1%nat ->
    tg ∉ dom (tv_nodes t) ->
    app_inv γfs -∗ tree_own r g FsImg.ROOTINO t -∗
    ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
      ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I ∗
      app_step tg I (delta_unl_tgt tg (abs_view I)) ∗
      (∀ I' : gmap Z fs_node,
         ⌜abs_view I' = delta_unl_tgt tg (abs_view I)⌝ -∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
         ghost_map_auth_frac (γtop (fs_gamma_L γfs)) (1/2) I' ∗
         (tree_own r g FsImg.ROOTINO t ∨ tree_taint c)).
  Proof using .
    intros Heq Ha Hnl Hni. iIntros "#Hinv Hown Hka".
    iMod (tree_claim_read γfs c r g FsImg.ROOTINO t I Heq with "Hinv Hown Hka")
      as "(Hka & Hown & [%Hsub | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r tg I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    iMod (tree_claim_facts γfs c r I Heq with "Hinv Hka")
      as "(Hka & [%Hf | #HT])"; last first.
    { iModIntro. iFrame "Hka". iSplitR.
      { iApply (tree_app_step_taint c r tg I _ Heq). iExact "HT". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". by iRight. }
    destruct Hf as (Hwf & Hrt & Hro).
    assert (Hne : tg <> FsImg.ROOTINO).
    { intros ->.
      exact (Hni (subtree_root_dom (abs_view I) FsImg.ROOTINO t Hsub)). }
    pose proof (aview_no_edge_to_rooted (abs_view I) t tg Hro (proj2 Hwf)
                  Hsub Hni) as Hno.
    iModIntro. iFrame "Hka". iSplitR "Hown".
    { iApply (tree_app_step_of c r tg I _ Heq).
      (* the row LEAVES and the tree does not move: [delta_unl_tgt] at a
         count of one is [delta_unarm], which is free at a row nothing
         names and which is not the era's root *)
      rewrite -(delta_unarm_unl_tgt (abs_view I) tg a Ha Hnl).
      iApply (tree_step_unarm c r (abs_view I) tg a Ha Hnl Hno Hne). }
    iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'". iLeft. iExact "Hown".
  Qed.

End TreeMove.

(* ===================================================================== *)
(*  4.  THE CREATE/UNLINK FAMILY: WHAT IS PAID, AND THE WALLS THAT REMAIN *)
(*      (rewritten by TL-3P; AMENDED BY TL-3K, which took WALL A's fix    *)
(*      (i) and dissolved WALL B -- see the AS-OF-TL-3K block at the end  *)
(*      of this section, and design/user-tree.md section 7.6)             *)
(*                                                                       *)
(*  LARGELY SUPERSEDED BY TL-3R (sections 3b'/3d/3e/3f above, and         *)
(*  design/user-tree.md section 7.9).  WALL C IS CLOSED -- by the ROOTED  *)
(*  VIEW, at EVERY child kind -- and with it section 7.4's UNARM wall,    *)
(*  mkdir's second credential and TL-2's rmdir-shaped wall; all three     *)
(*  create-family bundles are SUPPLIED from one live deed at a parent     *)
(*  prefix of length zero ([tree_mknod_au] / [tree_mkdir_au] /            *)
(*  [tree_open_create_au]).  What is left for UNLINK is NOT a credential  *)
(*  but TWO QUANTIFIER seams at its TARGET leg -- section 3e states both. *)
(*  Kept below as the record of what TL-3P/TL-3K saw.                     *)
(*                                                                       *)
(*  WHAT TL-3P CLOSED, and it is everything on the TREE LAYER'S side:     *)
(*    - the PINNED PARENT-PREFIX WALK exists ([PinnedObs] section 11,     *)
(*      [TreeWalk.tree_pwalk_of_own]): a frozen deed supplies             *)
(*      [FsAbsEra.ep_start], which is what [SysOpenDefs.                  *)
(*      open_au_create_at], [SpecSysMknod.mknod_au_at] and                *)
(*      [SpecSysUnlink.unlink_au_pre] owe.  It cost nothing extra at its  *)
(*      last hop: [ep_hops_from] is [ax_hops_from] over the SHORTER list, *)
(*      so nameiparent's own read of the parent is not a hop at all --    *)
(*      it is the syscall's separate COMMIT.                              *)
(*    - [own_wf_ent] is LANDED ([TreeView] section 8c), so create's       *)
(*      PARENT LEG ALONE has its [own_wf] preservation and the move is no *)
(*      longer offered FUSED only ([AppTree.tree_step_move_ent]);         *)
(*    - the CREATE and UNLINK MOVES are landed in full, at a given parent *)
(*      ([tree_acre_phases], [tree_uent_phases] above): phase 1 parks the *)
(*      deed, phase 2 returns it at [top_ins] / [top_unlink];             *)
(*    - unlink's TARGET leg AT THE LAST LINK is landed too, and FREE      *)
(*      ([AppTree.tree_step_unl_tgt_last]) -- see WALL C's note.          *)
(*                                                                       *)
(*  WALL A -- THE COMMITS QUANTIFY THEIR OWN PARENT, AND THAT IS WHY THE  *)
(*  FAMILY IS STILL NOT PAYABLE.  [FsAbsCreateFire.acre_commit_at_gen]    *)
(*  and [SysUnlinkDefs.uent_commit_at] both bind [d] INSIDE, so a         *)
(*  supplier owes a step at EVERY directory of every view:                *)
(*    - at a [d] the MOVER'S OWN tree records: paid, above;               *)
(*    - at a [d] NO owner reaches: free (TL-1's OUTSIDE lemmas);          *)
(*    - at a [d] inside a STRANGER'S subtree: THERE IS NO STEP.  The      *)
(*      delta moves that owner's recorded tree, only the holder of THAT   *)
(*      deed can park it, and [tree_taint] is not mintable by an owner    *)
(*      (it is read off the application's ledger, [AppTree] section 6).   *)
(*  The three cases are decidable from the claim, and the mover cannot    *)
(*  tell the second from the third.                                       *)
(*                                                                       *)
(*  TL-3W's note said a pinned parent-prefix walk would FIX [d] before    *)
(*  the commit is handed in.  IT DOES NOT, and this is the lane's main    *)
(*  finding: the walk and the commit are SEPARATE CONJUNCTS of the bundle *)
(*  ([SpecSysUnlink.unlink_au_pre], [SpecSysMknod.mknod_au_pre]), and the *)
(*  walk's terminal cursor [P (length (npar_elems pl)) d] surfaces only   *)
(*  in the syscall's POST ([unlink_post_ok]) -- after every commit has    *)
(*  already had to be provable at every [d].  What the walk buys is real  *)
(*  but it is on the other side of the fire.                              *)
(*                                                                       *)
(*  TWO FIXES, PRICED.                                                    *)
(*   (i) THREAD THE CURSOR (kernel tier, mechanical).  Give the two       *)
(*       commits the walk's parent cursor as a premise -- [acre_commit_at *)
(*       _gen] and [uent_commit_at] each gain [P (length (npar_elems pl)) *)
(*       d -*] beside their [cre_pre]/[unl_pre].  The PROVER holds it at  *)
(*       the fire instant (it is what the ret-0 arm hands back), so the   *)
(*       kernel side is a restatement rather than a new proof; the owner  *)
(*       then reads [d = dpar \/ taint] off [TreeWalk.tree_pwalk_parent]  *)
(*       and pays with [tree_acre_phases] / [tree_uent_phases] verbatim.  *)
(*       Cone: SysOpenDefs, SpecCreate, SpecSysMknod, SpecSysUnlink,      *)
(*       SpecSysLink, FsAbs{Create,Unlink,Link}Fire, FsAbsInvFire's unit  *)
(*       dischargers, and the ProofSys{Unlink,Link}* fire sites.          *)
(*  (ii) CONSTRAIN THE CLAIM (tree tier).  Make "no stranger reaches [d]" *)
(*       a consequence of the claim.  It is TRUE of every reachable tree  *)
(*       application -- the era's first deed is ONE entry                 *)
(*       ([AppTree.tree_xfer_boot_at]) and [tree_grant] RETIRES the       *)
(*       parent as it births the child, so the ownership map never grows  *)
(*       -- but the claim cannot see it.  Price: one more conjunct in     *)
(*       [tree_body] and a third gname in [tree_names], i.e. an AppTree   *)
(*       regrow of TL-3W's size.  Every landed statement survives, for    *)
(*       TL-3W's own reason: [tree_names] is quantified opaquely.         *)
(*                                                                       *)
(*  WALL B -- THE WALK WANTS A FROZEN DEED AND THE MOVE WANTS A LIVE ONE. *)
(*  NEW, and independent of WALL A.  [PinnedObs]'s walk premise is a [BOX]*)
(*  claim law, because a walk reads the claim ONCE PER HOP; only          *)
(*  [AppTree.tree_pin_law] -- a FROZEN deed -- has that shape, and a      *)
(*  frozen deed can never be parked, so its owner can never move again.   *)
(*  create and unlink need the walk AND the move in ONE syscall, so one   *)
(*  owner cannot have both.  WRITE escaped this because its bundle has no *)
(*  walk at all ([awrite_full_at] is indexed by the descriptor's inum);   *)
(*  exec, open and read escape it because they never move.                *)
(*    THE ONE CASE WHERE IT DOES NOT BITE, and it is the case the second  *)
(*    application actually starts from: a parent prefix of LENGTH ZERO.   *)
(*    At a path naming an entry of the walk's own start directory         *)
(*    ("/foo" for an owner of "/"), [np_elems pl = []], [ep_hops_from] is *)
(*    the empty big-op and [ep_start] is the START CURSOR ALONE -- a pure *)
(*    fact, with no claim law read anywhere ([UInitCons.init_cons_au]'s   *)
(*    mknod("console") is the landed precedent).  So mkdir("/d") by the   *)
(*    owner of "/" is reachable the moment WALL A falls, while a longer   *)
(*    prefix needs a DUPLICABLE READ of a LIVE deed besides.  AND THE     *)
(*    LIMIT IS LENGTH 1, NOT 0 (priced, not taken): section 8's dead walk *)
(*    already shows a walk whose claim law is LINEAR -- it takes a        *)
(*    resource [K], spends it at hop 0 and hands it back -- so a parent   *)
(*    prefix with exactly ONE hop could be supplied by a LIVE deed.  Two  *)
(*    additive lemmas beside [pobs_phop] / [pobs_pwalk]; nothing consumes *)
(*    them until WALL A falls.  A prefix of length >= 2 genuinely needs   *)
(*    the frozen deed.                                                    *)
(*                                                                       *)
(*  WALL C -- THE CREDENTIALS THE LEGS OWE EACH OTHER, and they are all   *)
(*  ONE mechanism.  Each of create's and unlink's later legs needs a fact *)
(*  its own EARLIER leg has and the claim does not carry:                 *)
(*    - create's PARENT leg needs [aview_no_edge_to av i], nothing names  *)
(*      the armed row.  [TreeView.aview_no_edge_to_arm] PROVES it at      *)
(*      the arm's view; nothing carries it to the parent leg.             *)
(*    - create's parent leg also needs "the armed inum is nobody's root", *)
(*      which [TreeView.own_wf_ent_leaf] pays FREE at a non-directory     *)
(*      child (open(O_CREATE), mknod) and NOT at mkdir's directory child. *)
(*    - the child's UNARM leg ([FsAbsCreateFire.cre_child_unfired]) needs *)
(*      the same no-edge fact -- TL-3W's item (a), unchanged.             *)
(*    - unlink's TARGET leg at the LAST LINK needs [aview_no_edge_to av   *)
(*      tg], and its own ENTRY leg PROVES it                              *)
(*      ([TreeView.aview_no_edge_to_unl_ent]): unique parenthood says the *)
(*      edge the entry leg just cut was the only one, so the tree layer   *)
(*      never has to carry the [nlink]-vs-edge-count tie TL-1 recorded as *)
(*      missing.  With that credential and a NON-DIRECTORY target, the    *)
(*      leg is FREE at every owner ([AppTree.tree_step_unl_tgt_last]) --  *)
(*      TL-2's "the row is nobody's root" wall is HALF LIFTED: a file's   *)
(*      or a device's row is nobody's root because roots are directories. *)
(*      A DIRECTORY's last link ([rmdir]-shaped) keeps TL-2's wall.       *)
(*  So WALL C is ONE kernel-tier change: a credential carried on the      *)
(*  legs' receipts ([aarm_commit_at]'s and [uent_commit_at]'s [Phi]),     *)
(*  serving the unarm leg, mkdir's parent leg and the last-link target    *)
(*  leg at once.                                                          *)
(*                                                                       *)
(*  TRUNCATE -- unchanged: [AppTree.tree_step_move_trunc] is landed and   *)
(*  IS inum-indexed, so O_TRUNC is only WALL B's open-bundle walk.        *)
(*  THE U TIER -- unchanged: [UkTreeRead] section 5 records that unlink,  *)
(*  like chdir, still carries the [forall pl] walk form a pin cannot      *)
(*  answer, so even a payable unlink has no U-tier leaf yet.  mknod and   *)
(*  open(O_CREATE) do ([SpecSysMknod.mknod_au_at],                        *)
(*  [SysOpenDefs.open_au_create_at] are at the ONE path argument 0 names).*)
(*                                                                       *)
(*  ===== AS OF TL-3K (design/user-tree.md section 7.6) ================= *)
(*                                                                       *)
(*  WALL A: FIXED, by fix (i).  [FsAbsCreateFire.acre_commit_at_gen] and  *)
(*  [SysUnlinkDefs.uent_commit_at] now take the walk's terminal cursor    *)
(*  [Pd] and the premise [Pd d], READ and HANDED BACK in phase 1.  So     *)
(*  [tree_acre_phases]'s [d in dom (tv_nodes t)] is payable: the owner    *)
(*  reads [d = dpar \/ taint] off [TreeWalk.tree_pwalk_parent] (or        *)
(*  [tree_pwalk_parent_live]) and [TreeWalk.tree_pin_presolves_dom].      *)
(*  BUT ONLY WHERE THE BUNDLE HAS A PATH: mknod and open(O_CREATE) are    *)
(*  guarded by [ArgPath.arg_path_of] at argument 0 and carry a real       *)
(*  cursor; mkdir and unlink still take the [forall pl] one-shot and are  *)
(*  handed in at [Pd := fun _ => True].                                   *)
(*                                                                       *)
(*  WALL B: DISSOLVED, at EVERY length ([PinnedObs] section 11a).  The    *)
(*  resource rides the CURSOR ([pobs_P_lin]), so a hop takes it out of    *)
(*  its input cursor and puts it back into its output and the hop         *)
(*  RESOURCE is persistent-only; [TreeWalk.tree_pwalk_of_own_live]        *)
(*  supplies [ep_start] from a LIVE deed.  ONE SEAM LEFT: the terminal    *)
(*  cursor then CARRIES the deed, and the commit returns [Pd d] in PHASE  *)
(*  1 while a move parks the deed in phase 1 and gets it back only in     *)
(*  phase 2 -- so a deed-carrying cursor wants the commit to return the   *)
(*  cursor at PHASE 2.                                                    *)
(*                                                                       *)
(*  WALL C: STILL OPEN, and NOT a receipt-carried credential.  What       *)
(*  create's parent leg needs ([aview_no_edge_to av i]) is a fact about   *)
(*  ITS OWN view; the arm proves it at the ARM's view and the view moves  *)
(*  in between, and a receipt carries a resource, not a fact about a      *)
(*  later view.  The mechanisms that work are an ARMED LEDGER in          *)
(*  [InodeRegion.ftop_body] (the only entry-insert at [i] is the create   *)
(*  leg, and it SPENDS the arm's permit) or an application-side armed set *)
(*  in [AppTree.tree_body].  Either is a lane of its own.                 *)
(*                                                                       *)
(*  WALL D: NEW.  [tree_acre_phases] wants [fs_pname nm] and the commit   *)
(*  quantifies [nm] with nothing said about it.  True at every reachable  *)
(*  fire (create's own dirlookup takes the FOUND arm at "." / ".."),      *)
(*  invisible at the commit's altitude; fix = [fs_pname nm] beside        *)
(*  [cre_pre].                                                            *)
(*                                                                       *)
(*  ===== AS OF TL-3C (design/user-tree.md section 7.7) ================ *)
(*                                                                       *)
(*  WALL D: CLOSED.  [FsAbsCreateFire.acre_commit_at_gen] carries         *)
(*  [nm <> DOT /\ nm <> DOTDOT] (which IS [TreeView.fs_pname nm],         *)
(*  convertible -- spelled unfolded so the kernel tier does not require   *)
(*  the tree layer), and the two fire sites pay it FREE: create reaches   *)
(*  [dirlink] only over a name its own [dirlookup] MISSED over the        *)
(*  parent's whole record range, and a live directory's records 0 and 1   *)
(*  ARE the two dot names ([DirView.dir_dots_miss_not_dots], which both   *)
(*  ProofCreateAlloc and ProofCreateMkdir already apply).  So             *)
(*  [tree_acre_phases]'s [fs_pname nm] premise is now DELIVERED BY THE    *)
(*  COMMIT -- the owner intros it rather than proving it.                 *)
(*                                                                       *)
(*  WALL A, the other half: mkdir AND unlink CAN NOW CARRY A CURSOR, so   *)
(*  EVERY create/unlink-family bundle is path-fixed.                      *)
(*  [SpecSysMkdir.mkdir_au_at] and [SpecSysUnlink.unlink_au_at] are the   *)
(*  path-fixed bundles ([mknod_au_at]'s twins: the walk under             *)
(*  [ArgPath.arg_path_of] at argument 0, the legs at                      *)
(*  [SysMknodDefs.npar_cur]); [SpecCreate.cre_commits_mono] is the cursor *)
(*  ISO lifted over create's whole four-leg bundle and                    *)
(*  [SpecSysUnlink.unlink_uent_inst] is unlink's, off                     *)
(*  [SysUnlinkDefs.uent_commit_at_mono].                                  *)
(*                                                                       *)
(*  WALL C: THE (C-i) ROUTE IS REFUTED, AND A THIRD ROUTE IS CHEAP.       *)
(*  An ARMED LEDGER in [InodeRegion.ftop_body] is NOT maintainable: the   *)
(*  GENERIC retag [ireg_top_retag_gen] takes an arbitrary new row (its    *)
(*  only premise, [inode_local], says nothing about which inums the       *)
(*  entries name) and has thirteen caller files, and                      *)
(*  [FsAbsLinkFire.lf_ent_fire] inserts an entry at an ARBITRARY target   *)
(*  with nothing at that altitude to say the target is not armed.  What   *)
(*  makes it true of the RUN is the icache REFERENCE ([iget]'s ref keeps  *)
(*  [ialloc] off the row) -- and xv6's sys_link [iunlock]s before         *)
(*  [dirlink], so no fraction of the target's top element is even held at *)
(*  the fire.                                                             *)
(*  (C-iii), THE ROOTED VIEW, needs no ghost state at all: [tree_body]    *)
(*  grows the PURE conjunct “every proper edge's target is reachable from *)
(*  ROOTINO”, the ARM's receipt carries the PURE “[i] is not in dom       *)
(*  (tv_nodes t)” (a fact about the owner's own FIXED tree, so no         *)
(*  monotonicity is needed and WALL C does not apply to it), and at an    *)
(*  owner of "/" the two together give [aview_no_edge_to av i] AT THE     *)
(*  PARENT LEG'S OWN VIEW.  It closes the child's UNARM leg too.  mkdir's *)
(*  second credential ("the armed inum is nobody's root") wants one more  *)
(*  conjunct of the same kind, "every owner's root is reachable".         *)
(*                                                                       *)
(*  THE PHASE-2 CURSOR SEAM: both fixes section 7.6 offered are REFUTED   *)
(*  (phase 2 holds the MOVED deed, and [t' <> t] is exactly what          *)
(*  [tree_claim_resync] needs; and the parking step consumes the deed BY  *)
(*  CONSTRUCTION -- that is what makes the in-flight arm unfabricable).   *)
(*  The fix is a SPLIT CURSOR, [Pd] in and [Pd'] out.  It is not on the   *)
(*  critical path: at a parent prefix of LENGTH ZERO no claim law is read *)
(*  at all, so the owner's cursor is PURE and returns itself.             *)
(* ===================================================================== *)

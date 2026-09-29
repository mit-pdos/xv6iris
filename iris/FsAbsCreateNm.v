(* ===================================================================== *)
(*  FsAbsCreateNm.v -- THE CREATE COMMIT AT A NAME PREDICATE              *)
(*  (lane INIT-FILE, the §3.4 ruling's bottom layer).                     *)
(*                                                                       *)
(*  [FsAbsCreateFire.acre_commit_at_gen] quantifies the created NAME and  *)
(*  says only that it is neither dot name:                                *)
(*                                                                       *)
(*    forall I d i nm ents nl, pure(cre_pre ...) -* pure(nm <> DOT /\ nm <> DOTDOT) -* ... *)
(*                                                                       *)
(*  so a caller's claim is asked to absorb the create AT EVERY NAME.  The *)
(*  echo application absorbs it -- it tracks only `console`, and a create *)
(*  at another name does not touch that row -- but the FILE application   *)
(*  tracks `f` as well, and a create of a DEVICE called `f` in the root    *)
(*  is a view its claim has no arm for ([AppFile.f_ok] at an absent deed   *)
(*  is [f_absent], and the create makes it present).                      *)
(*                                                                       *)
(*  THE NAME PREDICATE is the commit at one more pure premise, and every  *)
(*  landed site is its instance at [fun _ => True]: the two bridges below  *)
(*  are that reading, in both directions.  A PROVIDER always has the      *)
(*  weaker obligation (it answers for fewer names), so the interesting    *)
(*  direction is [acre_commit_at -* acre_commit_at_nm Nm], which holds at *)
(*  EVERY [Nm] and is what keeps the landed dischargers one line.         *)
(*                                                                       *)
(*  A FILE OF ITS OWN, and additive: [FsAbsCreateFire.v] is at the bottom *)
(*  of the kernel tier and every one of its ~160 mention sites would      *)
(*  rebuild for a statement none of them uses.  What still has to move    *)
(*  for the file application to profit is recorded in the lane's          *)
(*  findings: the thread from here up to [SpecSysMknod.mknod_au_at] runs  *)
(*  through [SpecCreate]'s SHARED create bundle, which mkdir and          *)
(*  open(O_CREATE) also take.                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import FsTree.
Require Import FsStateDefs.
Require Import IrefSlots.
Require Import Xv6Cameras.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsAbsDelta.
Require Import AppInv.
Require Import PieceFam.
Require Import FsAbsDefs.
Require Import PathElems.
Require Import ArgPath.
Require Import FsAbsCreateFire.

Local Open Scope Z_scope.

Section CreateNm.
  (* [FsAbsCreateFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* [acre_commit_at_gen] with the NAME PREDICATE beside the dot-name
     credential, in the position the ruling names. *)
  Definition acre_commit_at_gen_nm Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop)
      (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜cre_pre (abs_view I) d nm ents nl i (cf d i)⌝ -∗
       ⌜nm <> DOT /\ nm <> DOTDOT⌝ -∗
       ⌜Nm nm⌝ -∗
       cre_arm_fired Farm i -∗
       Pd d -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗ Pd d ∗
         app_step d I (delta_create d nm i (cf d i) (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_create d nm i (cf d i) (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗ Φ (abs_view I) d nm i))%I.

  Definition acre_commit_at_nm Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop)
      (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    acre_commit_at_gen_nm Γ E (fun _ _ => c) Nm Pd Farm Φ.

  (* ---- THE TWO BRIDGES ---- *)

  (* A provider that answers at EVERY name answers a fortiori at the ones
     [Nm] admits.  This is the one line every landed discharger takes, and
     it is why none of them moves. *)
  Lemma acre_commit_at_gen_nm_of Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    acre_commit_at_gen Γ E cf Pd Farm Φ -∗
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ.
  Proof using .
    rewrite /acre_commit_at_gen /acre_commit_at_gen_nm. iIntros "H".
    iIntros (I d i nm ents nl) "%Hpre %Hnm _ Harm HPd Ha".
    iApply ("H" with "[//] [//] Harm HPd Ha").
  Qed.

  Lemma acre_commit_at_nm_of Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    acre_commit_at Γ E c Pd Farm Φ -∗
    acre_commit_at_nm Γ E c Nm Pd Farm Φ.
  Proof using .
    rewrite /acre_commit_at /acre_commit_at_nm.
    iApply (acre_commit_at_gen_nm_of Γ E (fun _ _ => c) Nm Pd Farm Φ).
  Qed.

  (* ...and back, at the predicate every landed site is at. *)
  Lemma acre_commit_at_gen_of_nm Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm nm) ->
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ -∗
    acre_commit_at_gen Γ E cf Pd Farm Φ.
  Proof using .
    intros HNm. rewrite /acre_commit_at_gen /acre_commit_at_gen_nm.
    iIntros "H". iIntros (I d i nm ents nl) "%Hpre %Hnm Harm HPd Ha".
    iApply ("H" with "[//] [//] [%] Harm HPd Ha"). exact (HNm nm).
  Qed.

  Lemma acre_commit_at_of_nm Γ (E : coPset) (c : absnode)
      (Nm : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm nm) ->
    acre_commit_at_nm Γ E c Nm Pd Farm Φ -∗
    acre_commit_at Γ E c Pd Farm Φ.
  Proof using .
    intros HNm. rewrite /acre_commit_at /acre_commit_at_nm.
    iApply (acre_commit_at_gen_of_nm Γ E (fun _ _ => c) Nm Pd Farm Φ HNm).
  Qed.


  (* ...and the CURSOR moves under it exactly as it does without it
     ([FsAbsCreateFire.acre_commit_at_gen_mono]): the name predicate is
     pure and rides through. *)
  Lemma acre_commit_at_gen_nm_cur_mono Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm : fname -> Prop) (Pd Pd' : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    □ (∀ d : Z, Pd' d -∗ Pd d) -∗ □ (∀ d : Z, Pd d -∗ Pd' d) -∗
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ -∗
    acre_commit_at_gen_nm Γ E cf Nm Pd' Farm Φ.
  Proof using .
    rewrite /acre_commit_at_gen_nm. iIntros "#Hin #Hout H".
    iIntros (I d i nm ents nl) "%Hpre %Hnm %HNm Harm HPd Ha".
    iDestruct ("Hin" $! d with "HPd") as "HPd".
    iMod ("H" $! I d i nm ents nl with "[//] [//] [//] Harm HPd Ha")
      as "(Ha & HPd & Hstep & Hph2)".
    iDestruct ("Hout" $! d with "HPd") as "HPd".
    iModIntro. by iFrame "Ha HPd Hstep Hph2".
  Qed.

  (* ...and the predicate NARROWS freely: a provider at a wider [Nm]
     provides at a narrower one. *)
  Lemma acre_commit_at_gen_nm_mono Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Nm Nm' : fname -> Prop) (Pd : Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    (forall nm : fname, Nm' nm -> Nm nm) ->
    acre_commit_at_gen_nm Γ E cf Nm Pd Farm Φ -∗
    acre_commit_at_gen_nm Γ E cf Nm' Pd Farm Φ.
  Proof using .
    intros Hle. rewrite /acre_commit_at_gen_nm. iIntros "H".
    iIntros (I d i nm ents nl) "%Hpre %Hnm %HNm' Harm HPd Ha".
    iApply ("H" with "[//] [//] [%] Harm HPd Ha"). exact (Hle nm HNm').
  Qed.

  (* THE SYSCALL-TIER READING, as [SysMknodDefs.npar_cur] is for the
     cursor: the created name at WHATEVER path argument 0 reads.  It is
     PURE, so the failure fold keeps its shape, and
     [ArgPath.arg_path_of_uniq] makes the guarded and the read forms
     interchangeable exactly as [SpecSysMknod.mknod_acre_inst] does for
     the cursor. *)
  Definition nlast_elem (pl : list (bv 8)) : option fname :=
    list_basics.list.last (path_elems pl).

  Definition npar_nm (M : gmap Z (bv 8)) (pv : mword 64) (nm : fname) : Prop :=
    forall pl : list (bv 8),
      arg_path_of M pv pl -> nlast_elem pl = Some nm.

  Lemma npar_nm_intro (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    arg_path_of M pv pl -> nlast_elem pl = Some nm -> npar_nm M pv nm.
  Proof using .
    intros Hpl Hlast. rewrite /npar_nm. intros pl' Hpl'.
    by rewrite (arg_path_of_uniq M pv pl' pl Hpl' Hpl).
  Qed.

  Lemma npar_nm_elim (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    arg_path_of M pv pl -> npar_nm M pv nm -> nlast_elem pl = Some nm.
  Proof using . intros Hpl Hnm. exact (Hnm pl Hpl). Qed.

  (* =================================================================== *)
  (*  THE UNARM AT A NODE PREDICATE                                       *)
  (*                                                                     *)
  (*  [FsAbsCreateFire.aunarm_commit_at] quantifies the unarmed row's     *)
  (*  NODE and says nothing about it -- deliberately, since the failure   *)
  (*  arms reach it with an empty file, a device, or a directory holding  *)
  (*  no, one or two dots.  A caller's claim is therefore asked to let    *)
  (*  ANY row at count 1 disappear.  The echo application can: the rows   *)
  (*  it tracks are the pinned binaries, the root and the console, all    *)
  (*  present at the arm's own view, and the arm's row is fresh there.    *)
  (*  The FILE application cannot: the deed's row may have been created   *)
  (*  AFTER the arm, so [av0 !! i = None] does not separate it, and       *)
  (*  [FileDeltas.f_ok_unarm_fresh] wants the deed's CURRENT value at     *)
  (*  [av0] -- a temporal fact no pure receipt about one view carries.    *)
  (*                                                                     *)
  (*  What DOES separate them is the two rows' NODES: the arm put a       *)
  (*  device there and the deed's row is a plain file.  So the unarm      *)
  (*  takes a node predicate, exactly as the create takes a name one, and *)
  (*  the arm-derived unarm instantiates it at the node                   *)
  (*  [cre_child_unfired] already names.                                  *)
  (* =================================================================== *)
  Definition aunarm_commit_at_nd Γ (E : coPset) (i : Z)
      (Nd : absnode -> Prop) (Φ : aview -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (c : absnode),
       ⌜abs_view I !! i = Some (MkAnode c 1%nat)⌝ -∗
       ⌜Nd c⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
         app_step i I (delta_unarm i (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_unarm i (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i))%I.

  Definition aunarm_of_arm_nd Γ (E : coPset) (Nd : absnode -> Prop)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> iProp Σ) : iProp Σ :=
    (∀ i : Z, cre_arm_fired Farm i -∗ aunarm_commit_at_nd Γ E i Nd Φ)%I.

  (* ---- the same three bridges as the name predicate's ---- *)
  Lemma aunarm_commit_at_nd_of Γ (E : coPset) (i : Z)
      (Nd : absnode -> Prop) (Φ : aview -> Z -> iProp Σ) :
    aunarm_commit_at Γ E i Φ -∗ aunarm_commit_at_nd Γ E i Nd Φ.
  Proof using .
    rewrite /aunarm_commit_at /aunarm_commit_at_nd. iIntros "H".
    iIntros (I c) "%Hrow _ Ha". iApply ("H" with "[//] Ha").
  Qed.

  Lemma aunarm_commit_at_of_nd Γ (E : coPset) (i : Z)
      (Nd : absnode -> Prop) (Φ : aview -> Z -> iProp Σ) :
    (forall c : absnode, Nd c) ->
    aunarm_commit_at_nd Γ E i Nd Φ -∗ aunarm_commit_at Γ E i Φ.
  Proof using .
    intros HNd. rewrite /aunarm_commit_at /aunarm_commit_at_nd. iIntros "H".
    iIntros (I c) "%Hrow Ha". iApply ("H" with "[//] [%] Ha"). exact (HNd c).
  Qed.

  Lemma aunarm_commit_at_nd_mono Γ (E : coPset) (i : Z)
      (Nd Nd' : absnode -> Prop) (Φ : aview -> Z -> iProp Σ) :
    (forall c : absnode, Nd' c -> Nd c) ->
    aunarm_commit_at_nd Γ E i Nd Φ -∗ aunarm_commit_at_nd Γ E i Nd' Φ.
  Proof using .
    intros Hle. rewrite /aunarm_commit_at_nd. iIntros "H".
    iIntros (I c) "%Hrow %HNd' Ha". iApply ("H" with "[//] [%] Ha").
    exact (Hle c HNd').
  Qed.

  Lemma aunarm_of_arm_nd_of Γ (E : coPset) (Nd : absnode -> Prop)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> iProp Σ) :
    aunarm_of_arm Γ E Farm Φ -∗ aunarm_of_arm_nd Γ E Nd Farm Φ.
  Proof using .
    rewrite /aunarm_of_arm /aunarm_of_arm_nd. iIntros "H" (i) "Harm".
    iApply (aunarm_commit_at_nd_of Γ E i Nd Φ). iApply ("H" with "Harm").
  Qed.

  Lemma aunarm_of_arm_of_nd Γ (E : coPset) (Nd : absnode -> Prop)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> iProp Σ) :
    (forall c : absnode, Nd c) ->
    aunarm_of_arm_nd Γ E Nd Farm Φ -∗ aunarm_of_arm Γ E Farm Φ.
  Proof using .
    intros HNd. rewrite /aunarm_of_arm /aunarm_of_arm_nd.
    iIntros "H" (i) "Harm".
    iApply (aunarm_commit_at_of_nd Γ E i Nd Φ HNd). iApply ("H" with "Harm").
  Qed.

  Lemma aunarm_of_arm_nd_mono Γ (E : coPset) (Nd Nd' : absnode -> Prop)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Φ : aview -> Z -> iProp Σ) :
    (forall c : absnode, Nd' c -> Nd c) ->
    aunarm_of_arm_nd Γ E Nd Farm Φ -∗ aunarm_of_arm_nd Γ E Nd' Farm Φ.
  Proof using .
    intros Hle. rewrite /aunarm_of_arm_nd. iIntros "H" (i) "Harm".
    iApply (aunarm_commit_at_nd_mono Γ E i Nd Nd' Φ Hle).
    iApply ("H" with "Harm").
  Qed.

  (* ---- THE CHILD'S TWO LEGS, with the unarm PINNED at the node the arm
          placed.  [FsAbsCreateFire.cre_child_unfired] names that node
          already; this is the same pair reading it. ---- *)
  Definition cre_child_unfired_nd Γ (c : absnode)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ)) : iProp Σ :=
    (pf_at (aarm_commit_at Γ appE c) Farm
     ∗ pf_at (aunarm_of_arm_nd Γ appE (fun c' : absnode => c' = c) Farm) Fun)%I.

  Lemma cre_child_unfired_nd_of Γ (c : absnode)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ)) :
    cre_child_unfired Γ c Farm Fun -∗ cre_child_unfired_nd Γ c Farm Fun.
  Proof using .
    rewrite /cre_child_unfired /cre_child_unfired_nd.
    iIntros "[$ Hun]".
    iApply (pf_at_mono (aunarm_of_arm Γ appE Farm)
              (aunarm_of_arm_nd Γ appE (fun c' : absnode => c' = c) Farm)
              Fun with "[] Hun").
    iApply (aunarm_of_arm_nd_of Γ appE (fun c' : absnode => c' = c) Farm).
  Qed.

End CreateNm.

(* ===================================================================== *)
(*  FsAbsWritePart.v -- THE PARTIAL ARM AT A MAPPED SOURCE, WITHOUT A     *)
(*  PURE PREMISE ABOUT EVERY VIEW                                         *)
(*                                                                       *)
(*  [FsAbsWriteFire.awrite_part_at_mapped_single] makes the partial arm   *)
(*  vacuous from "a chunk cannot straddle a block boundary", taken as a   *)
(*  PURE fact quantified over every abstract view and every offset        *)
(*  ([wri_pre (abs_view I) i off bs bs0 nl -> wi_blocks off n = 1]).  No   *)
(*  client can supply that: a view whose inode [i] is a long file          *)
(*  satisfies [wri_pre] at an offset one byte short of a block's end.     *)
(*  What a client DOES know it knows AT THE FIRE, where the node hands    *)
(*  it the view's half and the kernel's offset link -- its own half of    *)
(*  the offset agrees [off], and its deed bounds it.                      *)
(*                                                                       *)
(*  So the honest statement keeps the node and STRENGTHENS ITS            *)
(*  HYPOTHESES: at a mapped source nothing unnamed landed                 *)
(*  ([r = length bs]), and then a single-block write counted nothing      *)
(*  ([r = 0]) against [wri_pre]'s [0 < length bs] -- so the arm may       *)
(*  ASSUME the chunk straddles.  A client whose cursor pins the offset    *)
(*  refutes that at the fire; one whose cursor is tainted pays the arm.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import FsStateDefs.     (* [fs_gamma_L]                            *)
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import Xv6G.
Require Import SpecWritei.       (* [wi_dinode]                             *)
Require Import FsAbsDelta.   (* [abs_view_insert]                       *)
Require Import SysWriteDefs.   (* [FW_MAX], [wri_pre], [wchunks], [wr_fail_why] *)
Require Import UserPtTree.     (* [uptd] / [uva_rmapped]: the partial arm's reason *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule)                 *)
Require Import CtxIdDefs.

Require Import FsAbsWriteFire.
Local Open Scope Z_scope.

Section WritePart.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  Lemma awrite_part_at_mapped_straddle Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd) (n : Z) (k : nat)
      (REST : iProp Σ) :
    (forall j : nat, (j < Z.to_nat n)%nat ->
       uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))) ->
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       (* WHAT THE MAPPED SOURCE BUYS: the chunk STRADDLES a block boundary *)
       ⌜wi_blocks off (Z.to_nat (wchunk_at n k)) <> 1%nat⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I -∗ off_link γo (Z.of_nat off) ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
         app_step i I (delta_write i off bs (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗
            off_ret γo off (length bs) ∗
            REST)) -∗
    awrite_part_at Γ E i γo M ua P n k REST.
  Proof using .
    intros Hmap. iIntros "Hn". rewrite /awrite_part_at.
    iIntros (I off r bs bs0 nl) "%Hpre %Hr %Hgap %Hshort %Hwhy %Hsb1 %Hby Ha Hk".
    (* nothing unnamed landed *)
    assert (Hrl : r = length bs).
    { destruct (decide (r < length bs)%nat) as [Hlt | Hge]; [| lia].
      exfalso.
      exact (wr_fail_why_refute P ua (Z.to_nat n) (Z.to_nat n)
               ltac:(lia) Hmap (Hwhy Hlt)). }
    (* ...so a single-block write, which counted nothing, is refuted *)
    assert (Hns : wi_blocks off (Z.to_nat (wchunk_at n k)) <> 1%nat).
    { intro Hsb. pose proof (Hsb1 Hsb) as Hr0.
      destruct Hpre as (_ & Hpos & _ & _). lia. }
    rewrite Hrl.
    iApply ("Hn" $! I off bs bs0 nl with "[//] [//] Ha Hk").
  Qed.

  (* ...and at the ADVANCED node ([awrite_part_adv]: phase 2 hands the
     kernel's half back moved by the count, which at a mapped source IS the
     run) *)
  Lemma awrite_part_adv_mapped_straddle Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd) (n : Z) (k : nat)
      (REST : iProp Σ) :
    (forall j : nat, (j < Z.to_nat n)%nat ->
       uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))) ->
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜wi_blocks off (Z.to_nat (wchunk_at n k)) <> 1%nat⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I -∗ off_link γo (Z.of_nat off) ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
         app_step i I (delta_write i off bs (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗
            off_link γo (Z.of_nat (off + length bs)) ∗
            REST)) -∗
    awrite_part_adv Γ E i γo M ua P n k REST.
  Proof using .
    intros Hmap. iIntros "Hn". rewrite /awrite_part_adv.
    iIntros (I off r bs bs0 nl) "%Hpre %Hr %Hgap %Hshort %Hwhy %Hsb1 %Hby Ha Hk".
    assert (Hrl : r = length bs).
    { destruct (decide (r < length bs)%nat) as [Hlt | Hge]; [| lia].
      exfalso.
      exact (wr_fail_why_refute P ua (Z.to_nat n) (Z.to_nat n)
               ltac:(lia) Hmap (Hwhy Hlt)). }
    assert (Hns : wi_blocks off (Z.to_nat (wchunk_at n k)) <> 1%nat).
    { intro Hsb. pose proof (Hsb1 Hsb) as Hr0.
      destruct Hpre as (_ & Hpos & _ & _). lia. }
    rewrite Hrl.
    iApply ("Hn" $! I off bs bs0 nl with "[//] [//] Ha Hk").
  Qed.

  (* the landed lemma is the instance whose client knows the fact purely *)
  Lemma awrite_part_at_mapped_single' Γ (E : coPset) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd) (n : Z) (k : nat)
      (REST : iProp Σ) :
    (forall j : nat, (j < Z.to_nat n)%nat ->
       uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))) ->
    (forall (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       wri_pre (abs_view I) i off bs bs0 nl ->
       wi_blocks off (Z.to_nat (wchunk_at n k)) = 1%nat) ->
    ⊢ awrite_part_at Γ E i γo M ua P n k REST.
  Proof using .
    intros Hmap Hsb.
    iApply (awrite_part_at_mapped_straddle Γ E i γo M ua P n k REST Hmap).
    iIntros (I off bs bs0 nl) "%Hpre %Hns". exfalso.
    exact (Hns (Hsb I off bs bs0 nl Hpre)).
  Qed.

End WritePart.

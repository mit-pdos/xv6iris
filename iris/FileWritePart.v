(* ===================================================================== *)
(*  FileWritePart.v -- THE FILE APPLICATION'S PARTIAL-ARM NODE            *)
(*                                                                       *)
(*  [FileWrite.file_awrite_node_adv] is the FULL arm of one chunk of an    *)
(*  append, built from the cursor ([FileWrite.file_cur]: the deed at the   *)
(*  content, the program's half of the offset at its length -- or the     *)
(*  taint).  This is the PARTIAL arm from the SAME cursor, and it is what  *)
(*  retires K1's pure "single block" premise ([UEchoFile]'s [Hstr]), which *)
(*  quantified over every abstract view and was false as stated:          *)
(*                                                                       *)
(*    at a mapped source the arm may assume the chunk STRADDLES a block   *)
(*    boundary ([FsAbsWritePart.awrite_part_adv_mapped_straddle]);        *)
(*    a FIRED cursor agrees the fire's offset to the content's length     *)
(*    ([UserOff.uoff_agree_k]), a line's worth                            *)
(*    ([FileDeltas.f_bytes_typed_short]), so a chunk of at most a line    *)
(*    cannot straddle -- refuted;                                         *)
(*    a TAINTED cursor (or a disconnected link) pays the arm as the full  *)
(*    node does: the step is free under the taint and the half moves by   *)
(*    what landed.                                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.         (* [bioslotG] *)
Require Import Xv6G.               (* [xv6G] *)
Require Import FdSlots.            (* [fdslotG] *)
Require Import IrefSlots.          (* [irefslotG] *)
Require Import ProcAvail.          (* [pavG] *)
Require Import FileInvDefs.        (* [fileG], [file_app] *)
Require Import FsBlocks.           (* [fs_names], [fs_top], [blk_splice] *)
Require Import FsBytesGamma.       (* [fs_gamma_L] *)
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import SysWriteDefs.       (* [wri_pre], [FW_MAX] *)
Require Import OffGv.              (* [off_gv] *)
Require Import AppCfg.
Require Import AppInv.             (* [app_inv], [app_body], [app_step], [appE] *)
Require Import EchoDisc.           (* [line_ok] *)
Require Import EchoOut.            (* [echoOutG] *)
Require Import FileState.          (* [fst], [echo_chunks], [subseq], [sel_ok] *)
Require Import AppFile.
Require Import UserOff.            (* [uoff] -- THE PROGRAM'S HALF *)
Require Import FsAbsWriteFire.     (* [awrite_full_adv] -- the advanced node *)
Local Open Scope Z_scope.
Require Import FileWrite.
Require Import FileDeltas.         (* [f_bytes_typed_short] *)
Require Import FsAbsWritePart.     (* the arm under the straddle assumption *)
Require Import SpecWritei.         (* [wi_blocks] *)
Require Import BioDefs.            (* [BSIZE] *)
Require Import UserPtTree.         (* [uptd] / [uva_rmapped] *)

Section FileWritePart.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context `{XI : CurCtx}.

  (* a write that starts and ends inside one block touches one block *)
  Lemma fwp_single_block (off n : nat) :
    (0 < n)%nat -> (off `mod` BSIZE + n < BSIZE)%nat ->
    wi_blocks off n = 1%nat.
  Proof using .
    intros Hn Hfit. rewrite /wi_blocks. unfold BSIZE in *.
    replace (off `mod` 1024 + n + 1024 - 1)%nat
      with (1 * 1024 + (off `mod` 1024 + n - 1))%nat by lia.
    rewrite Nat.div_add_l; [ | lia ].
    rewrite (Nat.div_small (off `mod` 1024 + n - 1)%nat 1024 ltac:(lia)). lia.
  Qed.

  Lemma file_awrite_part_adv (γfs : fs_names) (c : file_fixed)
      (r : file_names) (N : list (bv 8)) (s : dst) (i : Z) (ws : wordline) (sel sel' : list nat)
      (γo : gname) (M : gmap Z (bv 8)) (ua : mword 64) (P : uptd)
      (nn : Z) (k : nat) :
    file_app = MkAppcfg file_names (file_pred c) r ->
    (forall j : nat, (j < Z.to_nat nn)%nat ->
       uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))) ->
    (* the chunk is at most a line *)
    (0 < Z.to_nat (wchunk_at nn k))%nat ->
    (Z.to_nat (wchunk_at nn k) <= EchoDisc.line_max)%nat ->
    □ (app_taint -∗ file_taint c) -∗
    file_cur c r N s i ws sel γo -∗
    awrite_part_adv (fs_gamma_L γfs) appE i γo M ua P nn k
      (file_cur c r N s i ws sel' γo).
  Proof using .
    intros Heq Hmap Hnpos Hnle. iIntros "#Hbr Hcur".
    iApply (awrite_part_adv_mapped_straddle (fs_gamma_L γfs) appE i γo M ua P
              nn k _ Hmap).
    iIntros (I off bs bs0 nl) "%Hpre %Hns Hka Hg".
    (* THE BOX'S ARM: the kernel's half, or the disconnect. *)
    iDestruct "Hg" as "[Hk | #HTa]"; last first.
    { iDestruct ("Hbr" with "HTa") as "#HTf".
      iDestruct (file_cur_half with "Hcur") as (p) "Hu".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitR; [ by iApply off_link_taint | ].
      iApply (file_cur_taint with "HTf Hu"). }
    iDestruct "Hcur" as "[[Hq Hu] | [#HTf Hu]]"; last first.
    { (* the cursor is already tainted: the arm is PAID *)
      iDestruct "Hu" as (p) "Hu".
      iDestruct (uoff_agree_k with "Hu Hk") as %Hz.
      assert (Hop : off = p) by lia. subst p.
      iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitL "Hk"; [ by iApply off_link_of | ].
      iApply (file_cur_taint with "HTf Hu"). }
    (* THE FIRED ARM: the half pins [off] to the content's length *)
    iDestruct (uoff_agree_k with "Hu Hk") as %Hz.
    assert (Hoff : off = length (subseq (echo_chunks ws) sel)) by lia.
    rewrite {1}/file_wq.
    iDestruct "Hq" as "[Hq | #HTf]"; last first.
    { iEval (rewrite -Hoff) in "Hu".
      iMod (uoff_advance γo off (length bs) with "Hu Hk") as "[Hk Hu]".
      iModIntro. iFrame "Hka". iSplitR.
      { iApply (file_app_step_taint c r i I _ Heq). iExact "HTf". }
      iIntros (I') "%Hav Hka'". iModIntro. iFrame "Hka'".
      iSplitL "Hk"; [ by iApply off_link_of | ].
      iApply (file_cur_taint with "HTf Hu"). }
    (* ...and the content is a line's worth, so the chunk does NOT straddle *)
    iDestruct "Hq" as (ls) "(_ & _ & %Hline & %Hsel & _ & %Hin)".
    iExFalso. iPureIntro. apply Hns.
    pose proof (f_bytes_typed_short ls N (subseq (echo_chunks ws) sel)
                  (ex_intro _ ws (ex_intro _ sel
                     (conj Hin (conj Hline (conj Hsel eq_refl)))))) as Hshort.
    apply fwp_single_block; [ exact Hnpos | ].
    rewrite Hoff. unfold EchoDisc.line_max, BSIZE in *.
    rewrite Nat.mod_small; lia.
  Qed.

End FileWritePart.

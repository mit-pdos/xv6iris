(* ====================================================================== *)
(* FsWfImg.v -- THE IMAGE DISCHARGE OF [fs_durable_wf_body], AT THE        *)
(* COMMITTED VIEW (worklist stage F1; consumed by stage E4).               *)
(*                                                                        *)
(* [FsWf.fsimg_durable_wf_view] proves the durable predicate's view form  *)
(* from [fsimg_wf] + [fs_links_eq] + the region sweep; THIS file states   *)
(* the [gmap]-level deliverable at the committed view a clean disk        *)
(* denotes, [fs_restrict P (fs_home_set cov logstart)] ([FsCrash]'s       *)
(* vocabulary -- which sits ABOVE [FsWf] in the import order, since       *)
(* [FsCrash] Require-Exports [FsWf]; that is the whole reason this lemma  *)
(* is not in [FsWf.v]).                                                   *)
(*                                                                        *)
(* The geometry step is the one fact worth a comment: the durable sweeps  *)
(* read block 1 and [inodestart, size) only ([FsWf] section 8), the home  *)
(* set removes exactly [log_region_set logstart] = [logstart,             *)
(* logstart + 1 + LOGBLOCKS) from [cov], and W1 pins [inodestart =        *)
(* logstart + nlog] with [nlog = 31 = 1 + LOGBLOCKS] -- so every block a  *)
(* sweep reads is a home block, and the committed view agrees with the    *)
(* disk there ([fs_restrict_lookup_Some]).                                *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import FsImg.
Require Import FsCrash.      (* [fs_restrict], [fs_home_set]; exports FsWf *)
Require Import FsImgBridge.  (* [log_region_bound] *)

Local Open Scope Z_scope.

Lemma fsimg_durable_wf (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (cov : gset Z) :
  fs_parse_sb P = Some sb ->
  fsimg_wf P sb = true ->
  fs_links_eq P sb = true ->
  fs_region_wf P sb nib = true ->
  Z.of_nat nib = sb_ninodes sb / 16 + 1 ->
  (forall b : Z, 1 <= b < sb_size sb -> b ∈ cov) ->
  fs_durable_wf_body (fs_restrict P (fs_home_set cov (sb_logstart sb))).
Proof.
  intros Hp Hwf Hle Hrw Hnib Hcov.
  pose proof (fsimg_wf_sb P sb Hwf) as Hok.
  pose proof (sbo_logstart sb Hok).
  pose proof (sbo_nlog sb Hok).
  pose proof (sbo_inodestart sb Hok).
  pose proof (sbo_bmapstart sb Hok).
  pose proof (sbo_size sb Hok).
  pose proof (sbo_ninodes sb Hok).
  pose proof (sbo_nblocks sb Hok).
  assert (Hq : 0 <= sb_ninodes sb / 16)
    by (apply Z.div_pos; unfold ROOTINO in *; lia).
  assert (HLB : Z.of_nat LOGBLOCKS = 30) by reflexivity.
  apply (fs_durable_wf_body_of_view P sb).
  - exact Hp.
  - intros b Hb. apply fs_restrict_lookup_Some. split; [| reflexivity].
    unfold fs_home_set. apply elem_of_difference. split.
    + apply Hcov. unfold fs_data_start, SB_BNO, ROOTINO in *.
      destruct Hb as [-> | Hb]; lia.
    + intros Hlog. apply log_region_bound in Hlog.
      unfold SB_BNO, fs_data_start in *.
      destruct Hb as [-> | Hb]; lia.
  - exact (fsimg_durable_wf_view P sb nib Hp Hwf Hle Hrw Hnib).
Qed.

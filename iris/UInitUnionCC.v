(* ===================================================================== *)
(*  UInitUnionCC.v -- THE UNION ERA'S CONSOLE CREDENTIAL, ITS TEN LAWS,   *)
(*  AND /init's FIRST CREDENTIAL (cut C9g; design:                        *)
(*  claude-notes/design/union.md section 4).                              *)
(*                                                                        *)
(*  [UInitFileCC.file_cc] / [file_cc_holds] at the union: the loop's      *)
(*  write credential is the WIDENED one ([UShURoundDefs.uWcu] at the      *)
(*  pipeline's shapes [UShURoundShapes.upterm_shape] / [updone_shape]),   *)
(*  the banner-owed one the file family's [uWbf] (the deed DONE beside    *)
(*  the record's banner credential), the record the union's at the era's  *)
(*  boot state ([UnionLinkInstAt.union_link_inst_at ug s0]), the          *)
(*  discipline the union model's ([lm_disc_input ulmG]), and the line     *)
(*  constructor the union's three file shapes and its admitted pipelines  *)
(*  ([UShURound.ush_line_union]).                                         *)
(*                                                                        *)
(*  The pieces at the claim ([AppFile.file_pred]) are the file            *)
(*  application's own and are applied, not twinned: the union's claim IS  *)
(*  the file's.                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UexecSG.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import ConsoleInv.
Require Import UexecExecInst.
Require Import UkRun.
Require Import UkInit.
Require Import UInitDiag.
Require Import UInitBanner.
Require Import UInitCons.
Require Import UInitSh.
Require Import UShLine.
Require Import LineWords.
Require Import EchoDisc.
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import UserFd.
Require Import UkSh.
Require Import UShConsK.
Require Import UShKernel.
Require Import LinkRec.
Require Import GenLinksLine.
Require Import LineModel.
Require Import LineModelLinks.
Require Import FileDisc.
Require Import FileState.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.
Require Import FileLinkGen.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesUline.
Require Import UkPipesIface.       (* [pipesNG] *)
Require Import UnionDisc.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import UnionLinkInstAt.
Require Import UnionReadInstAt.
Require Import UShURoundDefs.
Require Import UShURoundShapes.
Require Import UShURoundLaws.
Require Import UShURound.          (* [ush_line_union] *)
Require Import UInitFileLeaves.    (* the claim's laws at /init; [file_cons_in_of_Cns], [file_cons_cred_of_init] *)
Require Import AppFileCons.        (* [file_cons_cred] *)
Local Open Scope Z_scope.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  0.  THE UNION DISCIPLINE'S THREE LINE READINGS                        *)
(* ===================================================================== *)
Lemma union_disc_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  lm_disc_input U (I ++ [b])%list -> bv_unsigned b <> 13%Z.
Proof using.
  intros Hd.
  assert (Hin : b ∈ (I ++ [b])%list).
  { apply elem_of_app. right. by apply elem_of_list_singleton. }
  pose proof (lm_disc_input_byte_val U (ulm_byte_laws adm_u_g) (I ++ [b])%list b Hd Hin)
    as Hv.
  lia.
Qed.

Lemma union_disc_rest_short (I : list (bv 8)) :
  lm_disc_input U I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat.
Proof using. intros (_ & _ & H). exact H. Qed.

(* a newline closes an admissible body, which is one of the union's line
   shapes at the three projections [UkSh.ush_line_at] reads *)
Lemma union_disc_line (I : list (bv 8)) (f : nat -> bv 8) :
  lm_disc_input U (I ++ [wl_nl])%list ->
  (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
  f (length (rest_of I)) = wl_nl ->
  exists lu : uline,
    ush_line_union lu
    /\ uline_ws lu = wl_words (rest_of I)
    /\ length (line_bytes lu) = S (length (rest_of I))
    /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))).
Proof using.
  intros (Hb & _ & _) Hby Hfnl.
  rewrite bodies_of_snoc_nl in Hb. apply Forall_app in Hb as [_ Hlast].
  apply Forall_inv in Hlast.
  set (J := rest_of I) in *.
  assert (Hmain : exists lu : uline,
             ush_line_union lu /\ uline_ok lu /\ J = line_body lu
             /\ uline_ws lu = wl_words J).
  { destruct (decide (fbody_ok J)) as [Hf | Hnf].
    - exists (uline_of J). destruct (fbody_ok_line J Hf) as [Hok HJ].
      split; [| split; [exact Hok | split; [exact HJ | exact (uline_ws_words J Hf)]]].
      pose proof (uline_of_nopipe J) as Hnp. rewrite /ush_line_union.
      destruct (uline_of J) as [ws | ws | | p n] eqn:He; try exact Logic.I.
      exfalso. exact (Hnp p n eq_refl).
    - destruct Hlast as [Hf | Hp]; [contradiction |].
      revert Hp. rewrite /upipe_ok.
      destruct (pl_parse J) as [[ws | p n] |] eqn:Hq; intros Hp; try contradiction.
      destruct (pl_parse_some J _ Hq) as [Hok HJ].
      exists (FileDisc.LPipe p n).
      split; [split; [exact Hp | exact Hok] |].
      split; [exact (uline_ok_of_pl_all (LPipes p n) Hok) |].
      split; [rewrite HJ; symmetry; exact (line_body_of_pl_all (LPipes p n)) |].
      rewrite HJ. exact (uline_ws_of_pl_all (LPipes p n) Hok). }
  destruct Hmain as (lu & Hlu & Huok & HJ & Hws).
  assert (Hlb : line_bytes lu = (J ++ [wl_nl])%list) by (rewrite line_bytes_body -HJ; reflexivity).
  exists lu.
  split; [exact Hlu |].
  split; [exact Hws |].
  split; [rewrite Hlb length_app; cbn [length]; lia |].
  rewrite /UkSh.ush_line_at Hlb. split_and!.
  - exact Huok.
  - rewrite length_app. cbn [length]. lia.
  - intros j Hj. rewrite Nat.add_0_l.
    assert (Hnlat : (J ++ [wl_nl])%list !!! length J = wl_nl).
    { pose proof (wl_lta_app_r J [wl_nl] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. exact Hr. }
    destruct (Nat.eq_dec j (length J)) as [-> | Hne].
    + rewrite Hfnl Hnlat. reflexivity.
    + rewrite (Hby j ltac:(lia)).
      symmetry. exact (wl_lta_app_l J [wl_nl] j ltac:(lia)).
Qed.

Section UnionInitCC.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!fileAppG Σ, !fileOutG Σ, !pipeOutG Σ, !pipesNG Σ}.

  #[local] Instance uicc_T_pers0 (g : file_gn) : Persistent (file_taint (fgn_cl g)) | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance uicc_T_tl0 (g : file_gn) : Timeless (file_taint (fgn_cl g)) | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.

  (* =================================================================== *)
  (*  1.  THE CREDENTIAL                                                  *)
  (* =================================================================== *)

  (* THE HOLD /init's prologue carries beside the record's credential: the
     deed DONE at the input the prologue is at *)
  Definition union_H (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate) (n : nat) : iProp Σ :=
    (∃ I : list (bv 8), ⌜length I = n⌝
       ∗ ((∃ v : era_pins, era_pin (fgn_echo (ugn_file ug)) (S gen_id) v ∗ inp_lb v I)
          ∨ file_taint (fgn_cl (ugn_file ug)))
       ∗ ush_done_at ug r s0 I)%I.

  Lemma union_cc_rd_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (s0 : fstate) :
    forall i : nat,
      Timeless (UShLine.ush_rd_pin_at (lk_rres (union_link_inst_at ug s0))
                  (fgn_echo (ugn_file ug)) i).
  Proof using .
    intro i. rewrite /UShLine.ush_rd_pin_at.
    apply bi.exist_timeless; intro v.
    apply bi.exist_timeless; intro I.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply era_pin_timeless |].
    apply bi.sep_timeless; [apply _ |].
    apply bi.sep_timeless; [apply inp_lb_timeless |].
    apply (lk_rres_tl (union_link_inst_at ug s0)).
  Qed.

  Lemma union_cc_wb_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate) :
    forall I : list (bv 8), Timeless (uWbf ug r s0 I).
  Proof using . intro I. apply uWbf_timeless. Qed.

  Definition union_cc (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate) : cons_cred Σ :=
    MkConsCred
      (UShLine.ush_rd_pin_at (lk_rres (union_link_inst_at ug s0)) (fgn_echo (ugn_file ug)))
      (union_cc_rd_timeless HR GEN ug s0)
      (UShLine.ush_mid_at (lk_rres (union_link_inst_at ug s0)) (fgn_echo (ugn_file ug)))
      (uWcu ug r s0 (upterm_shape ug) (updone_shape ug))
      (uWbf ug r s0)
      (union_cc_wb_timeless HR GEN ug r s0)
      (fun n => (UInitDiag.kinit_pro_at (union_link_inst_at ug s0) n
                 ∗ union_H HR GEN ug r s0 n)%I).

  (* a prologue credential at the record is a boundary credential *)
  Local Lemma uicc_lcred_of_pban `{!riscvGS Σ} (L : LinkRec Σ) (k : nat) (v : era_pins)
      (I : list (bv 8)) :
    lk_pin L k v -∗ lk_pban L k v I -∗ lk_lcred L k I 0%nat.
  Proof using .
    iIntros "#Hpin Hc". rewrite /lk_lcred. iExists v. iFrame "Hpin".
    rewrite (lk_lpr_0 L).
    iApply (lk_line_of_pro L k v I). iApply (lk_pro_of_pban L k v I with "Hc").
  Qed.

  Lemma union_wp_line (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (s0 : fstate) (n : nat) :
    ⊢ UInitDiag.kinit_pro_at (union_link_inst_at ug s0) n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝ ∗ uWcl ug s0 I 0%nat.
  Proof using .
    iIntros "H". rewrite /UInitDiag.kinit_pro_at.
    iDestruct "H" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists I. iSplitR; [by iPureIntro |].
    rewrite /uWcl.
    iApply (uicc_lcred_of_pban (union_link_inst_at ug s0) (S gen_id) v I with "Hpin Hc").
  Qed.

  (* THE BANNER-OWED FAMILY WITH THE HOLD IS THE RECORD'S [cc_wbn] *)
  Lemma union_wbn_to (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate) (n : nat) :
    UserConsole.cc_wbn (union_cc HR GEN ug r s0) n -∗
    UInitBanner.kinit_ban_at (union_link_inst_at ug s0) n
    ∗ union_H HR GEN ug r s0 n.
  Proof using .
    rewrite /UserConsole.cc_wbn /union_cc /=. iIntros "H".
    iDestruct "H" as (I) "[%Hlen Hb]".
    iDestruct (uWbf_inp ug r s0 I with "Hb") as "[Hb #Hinp]".
    rewrite /uWbf /uWbl.
    iDestruct "Hb" as "[Hb Hd]". iDestruct "Hb" as (v) "[#Hpin Hb]".
    iSplitL "Hb".
    { rewrite /UInitBanner.kinit_ban_at. iExists v, I.
      iSplitR; [by iPureIntro |]. iFrame "Hpin Hb". }
    rewrite /union_H. iExists I. iSplitR; [by iPureIntro |]. iFrame "Hd".
    iDestruct "Hinp" as "[[Hinp _] | #HT]"; [iLeft; iExact "Hinp" | by iRight].
  Qed.

  Lemma union_wbn_of (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate) (n : nat) :
    UInitBanner.kinit_ban_at (union_link_inst_at ug s0) n -∗
    union_H HR GEN ug r s0 n -∗
    UserConsole.cc_wbn (union_cc HR GEN ug r s0) n.
  Proof using .
    rewrite /UInitBanner.kinit_ban_at /union_H /UserConsole.cc_wbn /union_cc /=.
    iIntros "Hb Hh".
    iDestruct "Hb" as (v I) "(%Hlen & #Hpin & Hb)".
    iDestruct "Hh" as (I') "(%Hlen' & #Hinp' & Hd)".
    iAssert (uWbl ug s0 I) with "[Hb]" as "Hb".
    { rewrite /uWbl. iExists v. iFrame "Hpin Hb". }
    iDestruct (uWbl_inp ug s0 I with "Hb") as "[Hb #Hinp]".
    iExists I. iSplitR; [by iPureIntro |]. rewrite /uWbf. iFrame "Hb".
    iDestruct "Hinp" as "[[Hinp _] | #HT]"; last first.
    { iApply (ush_deed_taint ug r with "HT"). }
    iDestruct "Hinp'" as "[Hinp' | #HT]"; last first.
    { iApply (ush_deed_taint ug r with "HT"). }
    iDestruct "Hinp" as (v1) "[#Hpin1 #Hi]".
    iDestruct "Hinp'" as (v') "[#Hpin' #Hi']".
    iDestruct (era_pin_agree (fgn_echo (ugn_file ug)) (S gen_id) v1 v' with "Hpin1 Hpin'")
      as %<-.
    iDestruct (inp_lb_agree v1 I I' ltac:(congruence) with "Hi Hi'") as %<-.
    iExact "Hd".
  Qed.

  (* =================================================================== *)
  (*  2.  THE TEN LAWS ([UInitSh.cons_cred_holds_at]) at the union era    *)
  (* =================================================================== *)
  Lemma union_cc_holds (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl (ugn_file ug))) r)
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = ucl ug)
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = utag ug) :
    (⊢ union_links ug) ->
    UInitSh.cons_cred_holds_at fsc_cons (file_taint (fgn_cl (ugn_file ug)))
      (lm_disc_input U) union_disc_snoc_ncr union_disc_rest_short
      ush_line_union union_disc_line
      (union_cc HR GEN ug r s0).
  Proof using .
    intros Hlkp.
    assert (Htsw : ⊢ file_taint (fgn_cl (ugn_file ug)) -∗ app_sup).
    { iIntros "#HT".
      iApply (UInitFileLeaves.file_sup_of_taint_at (ugn_file ug) r Heq with "HT"). }
    assert (Hstw : ⊢ app_sup -∗ file_taint (fgn_cl (ugn_file ug))).
    { iIntros "#Hs".
      iApply (UInitFileLeaves.file_taint_of_sup_at (ugn_file ug) r Heq with "Hs"). }
    pose proof (uWbf_inp ug r s0) as Hwbi.
    rewrite /UInitSh.cons_cred_holds_at /union_cc /=.
    split_and!.
    - (* (1) the read leaf at the index *)
      intros γp N l Hpeq.
      exact (union_read_leaf_holds_at ug Htag s0 (uWbf ug r s0) N γp l Hpeq Hstw Htsw Hlkp).
    - intros γp N i Hpeq.
      exact (UShLine.ush_lease_of_at (lk_rres (union_link_inst_at ug s0))
               (fgn_echo (ugn_file ug)) (file_taint (fgn_cl (ugn_file ug))) (uWbf ug r s0)
               N γp i Hpeq).
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_taint_at (lk_rres (union_link_inst_at ug s0))
               (fgn_echo (ugn_file ug)) (file_taint (fgn_cl (ugn_file ug))) (uWbf ug r s0)
               N γp I Hpeq).
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_wb_at (lk_rres (union_link_inst_at ug s0))
               (fgn_echo (ugn_file ug)) (file_taint (fgn_cl (ugn_file ug))) (uWbf ug r s0)
               N γp I Hpeq Hwbi).
    - (* (5) the read that completes a line, at the widened credential *)
      intros γp I l Hnl. exact (uWcu_read ug r s0 γp I l Hnl).
    - (* (6) the banner-owed credential is a boundary credential *)
      intros I. iIntros "H". iApply (uWcu_of ug r s0 (upterm_shape ug) (updone_shape ug) I 0%nat).
      iApply (uHwbwc_f ug r s0 I with "H").
    - (* (7) a block owed is one too *)
      intros I. exact (uHwbl_u ug r s0 (upterm_shape ug) (updone_shape ug) I).
    - (* (8) a line read at an unwritten prompt is the taint *)
      intros γp I l Hnl. iIntros "Hm [Hb _]".
      iApply (UShLine.ush_wb_read_holds_at (union_link_inst_at ug s0) (fgn_echo (ugn_file ug))
                γp (S gen_id) I l Hnl (union_ep_refl_at ug s0) with "Hm Hb").
    - (* (9) the cursor's boundary, at the widened credential *)
      intros γp N l i Hpeq.
      exact (UShLine.ush_posb_of_lend_at (lk_rres (union_link_inst_at ug s0))
               (fgn_echo (ugn_file ug)) (file_taint (fgn_cl (ugn_file ug))) N γp
               (uWcu ug r s0 (upterm_shape ug) (updone_shape ug)) (uWbf ug r s0) l i Hpeq
               (uWcu_inp ug r s0) Hwbi).
    - (* (10) THE STEP: the prologue credential carries the hold, and the
         two inputs -- the record's and the hold's -- are one input *)
      intros n. iIntros "[Hp Hh]".
      iDestruct (union_wp_line HR GEN ug s0 n with "Hp") as (I) "[%Hlen Hc]".
      rewrite /union_H. iDestruct "Hh" as (I') "(%Hlen' & #Hinp' & Hd)".
      iExists I. iSplitR; [by iPureIntro |].
      iDestruct (uWcl_inp ug s0 I 0%nat with "Hc") as "[Hc #Hinp]".
      assert (Hdone : forall J : list (bv 8),
                ⊢ uWcl ug s0 J 0%nat -∗ ush_done_at ug r s0 J -∗
                  uWcu ug r s0 (upterm_shape ug) (updone_shape ug) J 0%nat).
      { intro J. iIntros "Hc Hd".
        iApply (uWcu_of ug r s0 (upterm_shape ug) (updone_shape ug) J 0%nat).
        rewrite uWcf_0. iLeft. iFrame "Hc Hd". }
      iDestruct "Hinp" as "[Hinp | #HT]"; last first.
      { iApply (Hdone I with "Hc"). iApply (ush_deed_taint ug r with "HT"). }
      iDestruct "Hinp'" as "[Hinp' | #HT]"; last first.
      { iApply (Hdone I with "Hc"). iApply (ush_deed_taint ug r with "HT"). }
      iDestruct "Hinp" as (v) "[#Hpin #Hi]".
      iDestruct "Hinp'" as (v') "[#Hpin' #Hi']".
      iDestruct (era_pin_agree (fgn_echo (ugn_file ug)) (S gen_id) v v' with "Hpin Hpin'")
        as %<-.
      iDestruct (inp_lb_agree v I I' ltac:(congruence) with "Hi Hi'") as %<-.
      iApply (Hdone I with "Hc Hd").
  Qed.

  (* =================================================================== *)
  (*  3.  THE CONSOLE SUPPLY OUT OF sh's SLOT                              *)
  (* =================================================================== *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.
  #[local] Typeclasses Opaque UkSh.ush_rest_l_at.

  Lemma union_cons_sup_of_sh_slot (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (ug : union_gn) (r : file_names) (s0 : fstate)
      (Heq : @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl (ugn_file ug))) r)
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = ucl ug)
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = utag ug)
      (st : fdstate) (n0 : nat) :
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    (⊢ union_links ug) ->
    udep (PS := uprogSG_free) -∗
    □ (file_taint (fgn_cl (ugn_file ug)) -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free)
      (uWcu ug r s0 (upterm_shape ug) (updone_shape ug)) -∗
    □ (∀ jo : option Z,
         file_cons_cred (fgn_cl (ugn_file ug)) r jo -∗
         UInitSh.init_sh_slot (file_taint (fgn_cl (ugn_file ug)))
           (UInitSh.sh_pay_at ush_line_union (file_taint (fgn_cl (ugn_file ug)))
              (union_cc HR GEN ug r s0) UInitSh.sh_Rsh n0)) -∗
    UkInit.init_cons_sup fsc_cons (file_taint (fgn_cl (ugn_file ug)))
      (UInitCons.init_cons_cred (file_taint (fgn_cl (ugn_file ug))) (fn_cons r)) st
      (union_cc HR GEN ug r s0).
  Proof using .
    intros Hpsok_free Hn0 Hst Hlkp.
    iIntros "#Hdep #Hdp #Hplaw #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct (file_cons_cred_of_init (ugn_file ug) r with "Hcns") as (jo) "#Hcred".
      iDestruct ("Hcore" $! jo with "Hcred") as "#Hcore'".
      iApply (UInitSh.init_exec_sup_of_sh_slot_at (lm_disc_input U)
                union_disc_snoc_ncr union_disc_rest_short
                ush_line_union union_disc_line
                (file_taint (fgn_cl (ugn_file ug))) fsc_cons st (cons_never (fn_cons r))
                (union_cc HR GEN ug r s0) UInitSh.sh_Rsh n0
                Hpsok_free Hn0 Hst
                (union_cc_holds HR GEN ug r s0 Heq Hcons Htag Hlkp)
                with "Hdep Hdp Hplaw [] Hcore'").
      iApply (file_cons_in_of_Cns HR GEN (ugn_file ug) r Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (UInitCons.init_cons_cred_of_taint (file_taint (fgn_cl (ugn_file ug))) (fn_cons r)
                with "HT").
  Qed.
End UnionInitCC.

(* ===================================================================== *)
(*  4.  /init's FIRST CREDENTIAL, AT THE UNION RECORD                     *)
(* ===================================================================== *)
Section UnionInitHead.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).

  (* THE READER'S RESIDUE AT THE HEAD: the turn's bounds, the boot witness
     /init just filed, and the empty input's (vacuous) line witness *)
  Lemma union_rres_at_of_boot (s0 : fstate) :
    FileOut.fturn_core gf (S gen_id) -∗ f0pre_at gf s0 -∗
    FileOut.fturn_core gf (S gen_id)
    ∗ ∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v ∗ urresw ug v [].
  Proof using .
    iIntros "Ht #Hpre". rewrite /FileOut.fturn_core.
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iEval (rewrite /EchoOut.turn) in "Htn".
    iDestruct (mono_nat_lb_own_get with "Htn") as "#Hlb0".
    iSplitL "Htn Hdl".
    { iExists v, vf. iFrame "Hpin Hvf Htn Hdl Hcs Hps HE". }
    iExists v. iFrame "Hpin".
    rewrite /urresw /gwc_rres.
    iDestruct "Hpre" as "(_ & _ & #Hbw)".
    iSplitR.
    - iExists [], [], s0. rewrite lm_proc_before_nil. cbn [length].
      iFrame "Hlb0 Hps Hcs". iSplitR; [iPureIntro; apply lm_rd_stage_0 |].
      cbn [gWb gk0 union_params]. rewrite /uf0bwk.
      rewrite /FileLinksLine.f0bw. iDestruct "Hbw" as "[_ $]".
    - rewrite /FileLinksLine.flw. iLeft. iPureIntro. reflexivity.
  Qed.

  (* /init's FIRST CREDENTIAL: the round's banner-owed family at the deed's
     own content and the empty input *)
  Lemma union_Wbf_at_of_boot (s0 : fstate) (s : dst) :
    FileOut.fturn_core gf (S gen_id) -∗ f0pre_at gf s0 -∗
    fown r s -∗ UInitFileLeaves.boot_at gf s0 s -∗
    (∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v
       ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ uWbf ug r s0 [].
  Proof using .
    iIntros "Ht Hpre Hd Hb". rewrite /FileOut.fturn_core.
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iAssert (lk_turn (union_link_inst_at ug s0) (S gen_id)) with "[Htn Hdl Hpre]"
      as "Hturn".
    { cbn [lk_turn union_link_inst_at gen_link_inst]. rewrite /fturn_pre_at.
      iSplitR; [by iPureIntro |]. iFrame "Hpre". rewrite /FileOut.fturn_core.
      iExists v, vf. iFrame "Hpin Hvf Htn Hdl Hcs Hps HE". }
    iDestruct (lk_turn0 (union_link_inst_at ug s0) (S gen_id) with "Hturn")
      as "[Hrd Hwb]".
    iFrame "Hrd". rewrite /uWbf. iSplitL "Hwb"; [rewrite /uWbl; iExact "Hwb" |].
    iDestruct "Hb" as "[[-> #Hty] | [-> #HT]]".
    - iApply (ush_done_head ug r s v with "Hpin Hcs Hd Hty").
    - iApply (ush_deed_taint ug r with "HT").
  Qed.
End UnionInitHead.

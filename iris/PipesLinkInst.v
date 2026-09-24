(* ===================================================================== *)
(*  PipesLinkInst.v -- [LinkRec.LinkRec] AT THE PIPELINE APPLICATION'S    *)
(*  N-STAGE MODEL (cut C8).                                              *)
(*                                                                       *)
(*  The generic record ([GenLinksLine.gen_link_inst]) at                 *)
(*  [PipesDisc.pipes_lmE]: the taint, the era's pin, no state witness    *)
(*  ([unit]), no head arm; the links bundle [PipesLinks.pipes_links]      *)
(*  and its entailment of the generic interface; the read receipt, the   *)
(*  turn and the reader's residue at the generic shapes.                 *)
(*                                                                       *)
(*  THE PER-SHAPE LINE ARM [X] is an N-writer round's block COMPLETE and *)
(*  handed back by the family ([PipeOutN.pipesN_file]) but not yet       *)
(*  filed: the credential [pwc_blkN] at the block the family merged, a   *)
(*  block of the round's line.  Its prompt step ([pipes_X_dollar]) is    *)
(*  the filing link, after which the credential is the generic block     *)
(*  family's at the filed alternative [PLRun pre], and                   *)
(*  [GenLinksLine.gwc_blk_sp] takes it to the prompt's space.            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import AppEcho.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import PipesLinks.
Require Import EchoLinks.
Require Import EchoLinksPro.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
From stdpp Require Import list.
Local Open Scope list_scope.

Section pipes_link_inst.
  Context {Σ : gFunctors} `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).
  Local Notation fcE := (fun _ : bytes => @None bytes).

  (* =================================================================== *)
  (*  1.  THE PARAMETERS: no state, no witness, no head                   *)
  (* =================================================================== *)
  Definition pipes_W (k : nat) (s : lm_st pipes_lmE) : iProp Σ := emp%I.
  Definition pipes_H (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ := False%I.

  Lemma pipes_W_pers k s : Persistent (pipes_W k s).
  Proof using . rewrite /pipes_W. apply _. Qed.
  Lemma pipes_W_tl k s : Timeless (pipes_W k s).
  Proof using . rewrite /pipes_W. apply _. Qed.
  Lemma pipes_W_bw k s : pipes_W k s -∗ pipes_W k s.
  Proof using . by iIntros "$". Qed.
  Lemma pipes_W_bw0 k s : pipes_W k s -∗ pipes_W 0 s.
  Proof using . by iIntros "$". Qed.
  Lemma pipes_W_agree k (s s' : lm_st pipes_lmE) :
    pipes_W k s -∗ pipes_W k s' -∗ ⌜s = s'⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct s, s'. Qed.
  Lemma pipes_H_tl k v I : Timeless (pipes_H k v I).
  Proof using . rewrite /pipes_H. apply _. Qed.
  Lemma pipes_H_cur k v I :
    pipes_H k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.
  Lemma pipes_H_inp k v I : pipes_H k v I -∗ pipes_H k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using . iIntros "[]". Qed.

  Definition pipes_params : gen_params pipes_lmE :=
    MkGP pipes_lmE pipes_lm_echo_laws pipes_hooksE
      PT _ _
      (era_pin γ) _ _ (era_pin_agree γ)
      pipes_W pipes_W_pers pipes_W_tl
      pipes_W pipes_W_pers pipes_W_tl 0 pipes_W_bw pipes_W_bw0 pipes_W_agree
      pipes_H pipes_H_tl pipes_H_cur pipes_H_inp.

  (* =================================================================== *)
  (*  2.  THE LINKS ENTAIL THE GENERIC INTERFACE                          *)
  (* =================================================================== *)
  Lemma pipes_links_gl : pipes_links g -∗ glinks pipes_lmE pipes_params.
  Proof using .
    iIntros "#Hlk".
    iDestruct (pipes_links_eq with "Hlk") as %Hc.
    iDestruct (pipes_links_taint with "Hlk") as "#Ht".
    rewrite /glinks. iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - (* W *)
      rewrite /gl_w.
      iIntros "!>" (k v P b ps0 cs0 s0 I0 Φ) "%H1 %H2 %H3 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      destruct s0.
      iApply (pipes_write_link g Hc k v P b ps0 cs0 I0 Φ H1 H2 H3
                with "Hpin Htn Hps Hcs HE HΦ").
    - (* BLK *)
      rewrite /gl_blk.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ)
        "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      destruct s0.
      iApply (pipes_write_link_blk g Hc k v P a b ps0 cs0 I0 Φ H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Htn Hps Hcs HE HΦ").
    - (* PRO *)
      rewrite /gl_pro.
      iIntros "!>" (k v P a b ps0 cs0 s0 I0 Φ)
        "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin _ Htn #Hps #Hcs #HE HΦ".
      destruct s0.
      iApply (pipes_write_link_pro g Hc k v P a b ps0 cs0 I0 Φ H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Htn Hps Hcs HE HΦ").
    - (* HEAD: absent *)
      rewrite /gl_head. iIntros "!>" (k v I a b Φ) "_ _ _ [] _".
    - (* TAINT *)
      rewrite /gl_taint. iIntros "!>" (k b Φ) "#HT HΦ".
      iApply ("Ht" $! k b Φ with "HT HΦ").
  Qed.

  (* =================================================================== *)
  (*  3.  THE READ RECEIPT, THE TURN, THE RESIDUE                         *)
  (* =================================================================== *)
  Lemma preadE_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    preadE_ret g k v n ws -∗
    PT ∨ (∃ (ps0 cs0 : list nat) (s0 : lm_st pipes_lmE) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage pipes_lmE ps0 cs0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before pipes_lmE ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ pipes_W k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /preadE_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, tt, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0 Htlb". rewrite /pipes_W.
    iPureIntro. split; [rewrite length_fmap length_app Hdl; reflexivity |].
    first [exact Hrs | split; [exact Hrs | done]].
  Qed.

  Lemma pturn0E (k : nat) :
    pturn g k -∗
    (∃ v : era_pins, era_pin γ k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, era_pin γ k v ∗ gwc_ban pipes_lmE pipes_params k v [] 0%nat).
  Proof using .
    rewrite /pturn /eturn. iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin".
    rewrite /gwc_ban. iLeft. iExists [], [], tt, 0%nat.
    rewrite Nat.add_0_r. rewrite /gcur. cbn [gW pipes_params]. rewrite /pipes_W.
    iFrame "Htn Hps Hcs HE".
    iPureIntro. exact (lm_wr_ban_round0 pipes_lmE tt).
  Qed.

  Lemma pipes_rres_res (v : era_pins) (I : list (bv 8)) :
    gwc_rres pipes_lmE pipes_params v I -∗ gwc_rres pipes_lmE pipes_params v I.
  Proof using . by iIntros "$". Qed.

  (* =================================================================== *)
  (*  4.  THE N-WRITER ROUND'S LINE ARM, AND ITS PROMPT STEP              *)
  (* =================================================================== *)
  Definition pipes_X (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (∃ pre : list (bv 8),
       ⌜adm_echo (lineN fcE adm_echo I) = true
        /\ line_blocks fcE (lineN fcE adm_echo I) pre⌝
       ∗ pwc_blkN g fcE adm_echo v I k pre false)%I.

  Global Instance pipes_X_timeless k v I : Timeless (pipes_X k v I).
  Proof using .
    rewrite /pipes_X. apply bi.exist_timeless; intro pre.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_blkN_timeless].
  Qed.

  (* the filed alternative: admissible, state-free, not a panic, and its
     output is the block and the prompt *)
  Lemma pipes_run_apr (I pre : list (bv 8)) :
    adm_echo (lineN fcE adm_echo I) = true ->
    line_blocks fcE (lineN fcE adm_echo I) pre ->
    lm_apr pipes_lmE pipes_hooksE I (plalt_code (PLRun pre))
    /\ lm_ab pipes_lmE pipes_hooksE I (plalt_code (PLRun pre)) = pre ++ u_prompt.
  Proof using .
    intros Ha Hbl.
    assert (Hok : lm_ok pipes_lmE (lm_line_at pipes_lmE I)
                    (lm_dec pipes_lmE (plalt_code (PLRun pre)))).
    { cbn [pipes_lmE pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. right.
      split; [exact Ha | exact Hbl]. }
    assert (Hfree : lmh_free pipes_hooksE
                      (lm_dec pipes_lmE (plalt_code (PLRun pre))) = true).
    { cbn [pipes_hooksE pipes_hooks lmh_free pipes_lmE pipes_lm lm_dec].
      by rewrite plalt_of_code. }
    split.
    - split; [exact Hok | split; [exact Hfree |]].
      cbn [pipes_lmE pipes_lm lm_panic lm_dec]. by rewrite plalt_of_code.
    - rewrite /lm_ab decide_True; [| split; [exact Hok | exact Hfree]].
      cbn [pipes_lmE pipes_lm lm_cont lm_dec]. by rewrite plalt_of_code.
  Qed.

  Lemma pipes_X_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pipes_links g -∗ pipes_X k v I -∗
    (gwc_sp_t pipes_lmE pipes_params k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hx HΦ".
    iDestruct (pipes_links_eq with "Hlk") as %Hc.
    iDestruct "Hx" as (pre) "([%Ha %Hbl] & Hpw)".
    iApply (pipes_file_link g Hc k v I pre b Φ Ha Hbl Hb with "Hpw").
    iIntros "Hret". iApply "HΦ".
    destruct (pipes_run_apr I pre Ha Hbl) as [Hapr Hab].
    iApply (gwc_blk_sp pipes_lmE pipes_params k v I (plalt_code (PLRun pre)) Hapr).
    rewrite Hab length_app ll_prompt_len.
    rewrite (_ : (length pre + 2 - 1)%nat = S (length pre)); [| lia].
    rewrite /gwc_blk. iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
    iDestruct "Hx" as (ps cs P) "(%Hw & Htn & Hps & Hcs & HE)".
    iLeft. iExists ps, cs, tt, P. cbn [lm_blkcs].
    rewrite (_ : (P + S (length pre))%nat = S (P + length pre)); [| lia].
    iFrame "Htn Hps Hcs HE". iPureIntro. exact Hw.
  Qed.

  (* =================================================================== *)
  (*  5.  THE RECORD                                                      *)
  (* =================================================================== *)
  Definition pipes_link_inst_at : LinkRec Σ :=
    gen_link_inst pipes_lmE pipes_params pipes_X pipes_X_timeless
      (pipes_links g) (pipes_links_persistent g) pipes_links_gl
      pipes_X_dollar (preadE_ret g) preadE_ret_res (pturn g)
      pturn0E (gwc_rres pipes_lmE pipes_params)
      (gwc_rres_persistent pipes_lmE pipes_params)
      (gwc_rres_timeless pipes_lmE pipes_params)
      pipes_rres_res (plalt_code (PLRun [])).

  Lemma pipes_inst_T : lk_T pipes_link_inst_at = echo_taint γ.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_pin : lk_pin pipes_link_inst_at = era_pin γ.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_links : lk_links pipes_link_inst_at = pipes_links g.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_blk k v I a i :
    lk_blk pipes_link_inst_at k v I a i = gwc_blk pipes_lmE pipes_params k v I a i.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_lpr :
    lk_lpr pipes_link_inst_at = gwc_lpr pipes_lmE pipes_params pipes_X.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_rres : lk_rres pipes_link_inst_at = gwc_rres pipes_lmE pipes_params.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_turn : lk_turn pipes_link_inst_at = pturn g.
  Proof using . reflexivity. Qed.
  Lemma pipes_inst_lcred k I p :
    lk_lcred pipes_link_inst_at k I p
    = (∃ v : era_pins, era_pin γ k v ∗ gwc_lpr pipes_lmE pipes_params pipes_X k v I p)%I.
  Proof using . reflexivity. Qed.

  (* THE EXEC-FAILED CHILD'S BYTES AT AN ECHO LINE are echo's *)
  Lemma pipes_inst_exfb_echo I ws :
    lineN fcE adm_echo I = LEcho' ws ->
    lk_exfb pipes_link_inst_at I = EchoDisc.alt_execfail
    /\ (length (lk_exfb pipes_link_inst_at I) - 2)%nat = 17%nat.
  Proof using .
    intros Hl.
    cbn [lk_exfb pipes_link_inst_at gen_link_inst gK pipes_params pipes_hooksE
         lmh_exfb pipes_hooks].
    rewrite (_ : lm_line_at pipes_lmE I = LEcho' ws); [| exact Hl].
    cbn [pl_exfb]. split; [reflexivity |]. by vm_compute.
  Qed.
End pipes_link_inst.

(* ===================================================================== *)
(*  THE [UShRound]-FACING LEMMAS ([PipeLinkInst]'s, at this instance)     *)
(* ===================================================================== *)
Section pipes_sh_round_facing.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation PI := (pipes_link_inst_at g).

  Definition pipes_Wcl_at (I : list (bv 8)) (p : nat) : iProp Σ :=
    lk_lcred PI (S gen_id) I p.

  Definition pipes_Wbl_at (I : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       lk_pin PI (S gen_id) v ∗ lk_ban PI (S gen_id) v I 0%nat)%I.

  Global Instance pipes_Wcl_at_timeless I p : Timeless (pipes_Wcl_at I p).
  Proof using . rewrite /pipes_Wcl_at. apply lk_lcred_timeless. Qed.
  Global Instance pipes_Wbl_at_timeless I : Timeless (pipes_Wbl_at I).
  Proof using .
    rewrite /pipes_Wbl_at. apply bi.exist_timeless; intro.
    apply bi.sep_timeless; [apply lk_pin_tl | apply lk_ban_tl].
  Qed.

  Lemma pipes_Hwbl (I : list (bv 8)) : ⊢ pipes_Wcl_at I 3%nat -∗ pipes_Wcl_at I 0%nat.
  Proof using .
    rewrite /pipes_Wcl_at. iApply (lk_lcred_blk_line PI (S gen_id) I).
  Qed.

  Lemma pipes_Hwbwc (I : list (bv 8)) : ⊢ pipes_Wbl_at I -∗ pipes_Wcl_at I 0%nat.
  Proof using .
    rewrite /pipes_Wcl_at /pipes_Wbl_at.
    iApply (lk_lcred_of_ban PI (S gen_id) I).
  Qed.

  Lemma pipes_Hcltaint (I : list (bv 8)) (p : nat) (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ echo_taint γ -∗ pipes_Wcl_at I p.
  Proof using .
    rewrite /pipes_Wcl_at. iApply (lk_lcred_taint PI (S gen_id) I p v).
  Qed.

  Lemma pipes_Hwc (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin γ (S gen_id) v -∗
      inp_lb v (I ++ l ++ [wl_nl]) -∗
      pipes_Wcl_at I 2%nat -∗ pipes_Wcl_at (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros Hl. rewrite /pipes_Wcl_at.
    iApply (lk_lcred_read PI (S gen_id) I l v Hl).
  Qed.

  Lemma pipes_Hwbr (I l : list (bv 8)) (v : era_pins) :
    wl_nl ∉ l ->
    ⊢ era_pin γ (S gen_id) v -∗
      lk_rres PI v (I ++ l ++ [wl_nl]) -∗
      pipes_Wbl_at I -∗ echo_taint γ.
  Proof using .
    intros Hl. iIntros "#Hpin #Hres Hb". rewrite /pipes_Wbl_at.
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (lk_pin_agr PI (S gen_id) v v' with "Hpin Hpin'") as %<-.
    iApply (lk_ban_read_taint PI (S gen_id) v I l Hl with "Hb Hres").
  Qed.
End pipes_sh_round_facing.

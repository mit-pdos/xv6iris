(* ===================================================================== *)
(*  PipesStageInst.v -- [StageRec.StageRec] AND [ReadRec.ReadRec] AT THE  *)
(*  PIPELINE APPLICATION'S N-STAGE MODEL (cut C8).                       *)
(*                                                                       *)
(*  THE STAGE: the ECHO child of an echo line writes the line's content  *)
(*  and the prompt -- alternative [PLRun (wl_line (drop 1 ws))], whose   *)
(*  CODE is a function of the line ([StageRec.sk_code]) -- through the   *)
(*  generic block family at that code.  A pipeline line's writers go     *)
(*  through the N-writer family and never through this cursor.           *)
(*                                                                       *)
(*  THE READ RECORD: the discipline is the model's [lm_disc_input], the  *)
(*  read link [PipesLinks.pipes_read_link], and the window arm           *)
(*  [ReadRec.eri_arms]'s proof at the model's receipt.                   *)
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
Require Import PipesLinks.
Require Import PipesLinkInst.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import StageRec.
Require Import ReadRec.
Require Import ConsoleInv.
Require Import UserConsole.
Require Import RiscvPtsto.
Require Import WpUart.
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation fcE := (fun _ : bytes => @None bytes).

(* ===================================================================== *)
(*  S0  THE PURE GUARD AND THE CODE                                       *)
(* ===================================================================== *)

(* the round's line IS the echo line the input's last words spell *)
Definition pipes_lineok (I : list (bv 8)) : Prop :=
  lineN fcE adm_echo I = LEcho' (last_ws I).

(* the alternative echo's output files *)
Definition pipes_code (I : list (bv 8)) : nat :=
  plalt_code (PLRun (wl_line (drop 1 (last_ws I)))).

Lemma pipes_code_apr (I : list (bv 8)) :
  pipes_lineok I ->
  lm_apr pipes_lmE pipes_hooksE I (pipes_code I)
  /\ lm_ab pipes_lmE pipes_hooksE I (pipes_code I) = line_alts_of (last_ws I) !!! 0%nat.
Proof using.
  intros Hl.
  assert (Hok : lm_ok pipes_lmE tt (lm_line_at pipes_lmE I)
                  (lm_dec pipes_lmE (pipes_code I))).
  { rewrite /pipes_code. cbn [pipes_lmE pipes_lm lm_ok lm_dec].
    rewrite plalt_of_code. right.
    rewrite (_ : lm_line_at (pipes_lm fcE adm_echo) I = LEcho' (last_ws I));
      [| exact Hl].
    split; [reflexivity |].
    exists [wl_line (drop 1 (last_ws I))]. split; [constructor |].
    by apply merge_all_one. }
  assert (Hfree : lmh_free pipes_hooksE (lm_dec pipes_lmE (pipes_code I)) = true).
  { rewrite /pipes_code. cbn [pipes_hooksE pipes_hooks lmh_free pipes_lmE pipes_lm lm_dec].
    by rewrite plalt_of_code. }
  split.
  - split; [exact Hok | split; [exact Hfree |]].
    rewrite /pipes_code. cbn [pipes_lmE pipes_lm lm_panic lm_dec]. by rewrite plalt_of_code.
  - rewrite /lm_ab decide_True; [| split; [exact Hok | exact Hfree]].
    rewrite /pipes_code. cbn [pipes_lmE pipes_lm lm_cont lm_dec]. rewrite plalt_of_code.
    reflexivity.
Qed.

(* ===================================================================== *)
(*  S1  THE CURSOR AND THE STAGE                                          *)
(* ===================================================================== *)
Section pipes_stage_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Local Notation PI := (pipes_link_inst_at g).
  Local Notation PWB := (gwc_blk pipes_lmE (pipes_params g)).

  Record pipes_stg := MkPipesStg { pss_I : list (bv 8) }.

  Local Lemma psi_cur_tl (k : nat) (v : era_pins) (st : pipes_stg) (p : nat) :
    Timeless (PWB k v (pss_I st) (pipes_code (pss_I st)) p).
  Proof using . apply gwc_blk_timeless. Qed.

  Local Lemma psi_step (k : nat) (v : era_pins) (st : pipes_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    (pipes_lineok (pss_I st) /\ last_ws (pss_I st) = ws) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ lk_pin PI k v -∗ lk_links PI -∗ PWB k v (pss_I st) (pipes_code (pss_I st)) i -∗
      (PWB k v (pss_I st) (pipes_code (pss_I st)) (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros [Hln Hlast] Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (gblk_step pipes_lmE (pipes_params g) (pipes_links g)
              (pipes_links_persistent g) (pipes_links_gl g)
              k v (pss_I st) (pipes_code (pss_I st)) i b Φ with "Hpin Hlk Hc HΦ").
    cbn [gK pipes_params].
    rewrite (proj2 (pipes_code_apr (pss_I st) Hln)) Hlast. exact Hb.
  Qed.

  Definition pipes_cur_inst : CurRec PI :=
    MkCurRec PI pipes_stg
      (fun st ws => pipes_lineok (pss_I st) /\ last_ws (pss_I st) = ws)
      (fun ws => line_alts_of ws !!! 0%nat)
      pipes_lineok
      (fun k v st p => PWB k v (pss_I st) (pipes_code (pss_I st)) p)
      psi_cur_tl psi_step.

  Local Lemma psi_lend_stage (k : nat) (v : era_pins) (I : list (bv 8)) :
    pipes_lineok I ->
    ⊢ lk_lend PI k v I -∗
      (∃ st : pipes_stg,
         ⌜pipes_lineok (pss_I st) /\ last_ws (pss_I st) = last_ws I⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ PWB k v (pss_I st) (pipes_code (pss_I st)) 0%nat
         ∗ □ (PWB k v (pss_I st) (pipes_code (pss_I st))
                (length (wl_line (drop 1 (last_ws I)))) -∗
              lk_post PI k v I (pipes_code I)))
      ∨ lk_T PI.
  Proof using .
    intro Hlok.
    cbn [lk_lend pipes_link_inst_at gen_link_inst]. rewrite /gwc_lend.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs s0 P) "(%Hw & Htn & #Hps & #Hcs & #HE & Hf)".
    iLeft. iExists (MkPipesStg I). cbn [pss_I].
    iSplitR; [ iPureIntro; split; [ exact Hlok | reflexivity ] | ].
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn Hf".
    - rewrite /gwc_blk. iLeft. iExists ps, cs, s0, P.
      cbn [lm_blkcs]. rewrite Nat.add_0_r.
      iFrame "Htn Hps Hcs HE". by iPureIntro.
    - iIntros "!> Hc". rewrite /lk_post.
      cbn [lk_blk lk_ab pipes_link_inst_at gen_link_inst gK pipes_params].
      rewrite (proj2 (pipes_code_apr I Hlok)) line_alts_of_0 length_app ll_prompt_len.
      rewrite (_ : (length (wl_line (drop 1 (last_ws I))) + 2 - 2)%nat
                   = length (wl_line (drop 1 (last_ws I)))); [| lia].
      iExact "Hc".
  Qed.

  Local Lemma psi_apr0 (I : list (bv 8)) :
    pipes_lineok I -> lk_apr PI I (pipes_code I).
  Proof using .
    intro Hl. cbn [lk_apr pipes_link_inst_at gen_link_inst gK pipes_params].
    exact (proj1 (pipes_code_apr I Hl)).
  Qed.

  Definition pipes_stage_inst_at : StageRec PI :=
    MkStageRec PI pipes_cur_inst pipes_code psi_lend_stage psi_apr0.

  Lemma pipes_stage_inst_lineok (I : list (bv 8)) :
    ck_lineok (sk_cur pipes_stage_inst_at) I = pipes_lineok I.
  Proof using . reflexivity. Qed.
  Lemma pipes_stage_inst_code (I : list (bv 8)) :
    sk_code pipes_stage_inst_at I = pipes_code I.
  Proof using . reflexivity. Qed.
End pipes_stage_inst.

Global Arguments pipes_stg : clear implicits.

(* ===================================================================== *)
(*  S2  THE READ RECORD                                                   *)
(* ===================================================================== *)

(* the ring's translation is the identity on a disciplined input: every
   byte of it is printable or the newline *)
Lemma lm_disc_input_E_no_cr (I : list (bv 8)) (j : nat) :
  lm_disc_input pipes_lmE I -> (j < length I)%nat -> cons_xlate (I !!! j) = I !!! j.
Proof using.
  intros Hd Hj.
  assert (Hin : I !!! j ∈ I).
  { apply elem_of_list_lookup_2 with j. apply list_lookup_lookup_total_lt. exact Hj. }
  pose proof (lm_disc_input_byte_val pipes_lmE (pipes_lm_byte_laws fcE adm_echo)
                I (I !!! j) Hd Hin) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

Section pipes_read_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.

  Local Notation PI := (pipes_link_inst_at g).
  Local Notation RRES := (gwc_rres pipes_lmE (pipes_params g)).

  Local Lemma psr_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ pipes_links g -∗ era_pin γ k v -∗ dl_cnt v (1/2) n -∗
      (preadE_ret g k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk #Hpin Hdl HΦ".
    iDestruct (pipes_links_rd with "Hlk") as "#Hrdl".
    iApply ("Hrdl" $! k v n ws with "Hpin Hdl HΦ").
  Qed.

  Local Lemma psr_rd_taint (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ pipes_links g -∗ echo_taint γ -∗ (echo_taint γ -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk HT HΦ".
    iDestruct (pipes_links_rd_taint with "Hlk") as "#Hrdt".
    iApply ("Hrdt" $! k ws with "HT HΦ").
  Qed.

  Local Lemma psr_arms (cn : cons_names) (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ era_pin γ (S gen_id) v -∗ inp_lb v I -∗ RRES v I -∗
      preadE_ret g (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow cn False sl dd dc -∗
      ucons_stored_lb cn sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜lm_disc_input pipes_lmE (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ RRES v (I ++ J))
      ∨ echo_taint γ.
  Proof using .
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    iIntros "#Hpin #HE0 #Hres0 Hret _ _ _".
    rewrite /preadE_ret.
    iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]"; [ by iRight | ].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdscp & #HEin & %Hdinp & Hrest)".
    iEval (rewrite Hlws) in "Hdlr".
    iDestruct (inp_lb_cmp v I (snd <$> (dl ++ ws)) with "HE0 HEin") as %Hcmp.
    assert (Hlen' : length (snd <$> (dl ++ ws)) = (length I + dc)%nat).
    { rewrite length_fmap length_app Hdl Hlws. reflexivity. }
    assert (Hpre' : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hcmp as [Hc | Hc]; [ exact Hc | ].
      pose proof (prefix_length _ _ Hc) as Hle.
      assert (Hdc0 : dc = 0%nat) by lia.
      assert (Heq : (snd <$> (dl ++ ws)) = I).
      { apply (list_eq_same_length _ _ (length I)); [ lia | lia | ].
        intros i x y Hi Hx Hy.
        pose proof (prefix_lookup_Some _ _ i x Hx Hc) as Hxy.
        rewrite Hxy in Hy. by injection Hy as <-. }
      rewrite Heq. done. }
    destruct Hpre' as [J HJ].
    assert (HJlen : length J = dc)
      by (rewrite HJ length_app in Hlen'; lia).
    assert (HJdisc : lm_disc_input pipes_lmE (I ++ J)) by (rewrite <- HJ; exact Hdinp).
    iDestruct "Hrest" as "#Hrest".
    iAssert (RRES v (I ++ J)) as "#Hresn".
    { iDestruct "Hrest" as "[%Hws0 | Hbb]".
      - assert (Hdc0 : dc = 0%nat)
          by (rewrite <- Hlws, Hws0; reflexivity).
        assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iExact "Hres0".
      - iDestruct "Hbb" as (cs0 ps0) "(#Hcs & #Hps & _ & #Htlb & %Hrds)".
        rewrite /gwc_rres. iExists ps0, cs0, tt.
        rewrite <- HJ. iFrame "Htlb Hps Hcs". cbn [gWb pipes_params]. rewrite /pipes_W.
        iPureIntro. first [exact Hrds | split; [exact Hrds | done]]. }
    iAssert (inp_lb v (I ++ J)) as "#HEn";
      [ rewrite <- HJ; iExact "HEin" | ].
    iLeft. iFrame "Hdlr". iExists J.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ | iFrame "HEn Hresn" ].
    iPureIntro. intro Hdd0.
    exact (rr_byte_of_rows (lm_disc_input pipes_lmE) sl sl' ws dl hs pops I J dd dc g0
             lm_disc_input_E_no_cr
             Hdd0 Hddc Hwinf Hpre2 Hwsj Hpref Hdl HJ HJdisc ltac:(lia)).
  Qed.

  Definition pipes_read_inst : ReadRec PI :=
    MkReadRec PI (lm_disc_input pipes_lmE) psr_rd psr_rd_taint psr_arms.

  Lemma pipes_read_inst_disc : rk_disc PI pipes_read_inst = lm_disc_input pipes_lmE.
  Proof using . reflexivity. Qed.
End pipes_read_inst.

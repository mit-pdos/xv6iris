(* ===================================================================== *)
(*  UnionLinkInst.v -- [LinkRec.LinkRec] AT THE UNION MODEL (cut C9e';    *)
(*  design: claude-notes/design/union.md section 3, 'The link record').   *)
(*                                                                        *)
(*  [GenLinksLine.gen_link_inst ulmG union_params]:                       *)
(*  - the FILE's witness and head ([FileLinksLine.f0w] / the boot-ledger  *)
(*    entry [uf0bwk] / [FileLinksLine.fhead], as in [FileLinkGen]),       *)
(*    the file's turn [fturn_pre] and the file's residue with the typed   *)
(*    lines' witness beside it ([urresw]: the generic residue and         *)
(*    [FileLinksLine.flw]);                                               *)
(*  - the N-writer arm [X := union_X]: [PipesLinkInst.pipes_X] at the     *)
(*    union -- an N-writer round's block complete and handed back by the *)
(*    family, not yet filed, at the ROUND'S STATE [sR] -- whose prompt    *)
(*    step is the filing link;                                            *)
(*  - [union_links_gl]: the links entail the generic interface, proved as *)
(*    [PipesLinkInst.pipes_links_gl] is, through [PipesLinksV.peclV_glinks]. *)
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
Require Import GenOutPure.
Require Import GenOut.
Require Import AppEcho.
Require Import FileState.
Require Import FileDisc.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.     (* [f0w], [fhead], [f0pre], [flw], [fturn_pre] *)
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeOutN.
Require Import PipesLinksV.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionView.
Require Import UnionOut.
Require Import UnionLinks.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import FsCfg.             (* [fsc_cons] *)
Require Import Xv6G.              (* the ring's cameras, at the kernel's own instance *)
Require Import UserConsole.       (* [ucons_stored_lb] *)
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  0.  THE FILED BLOCK'S CURSOR, at the round's own state (pure)         *)
(*                                                                        *)
(*  [LineModelLinks.lm_wr_blk_sp_s] asks the alternative to be admissible *)
(*  at EVERY state ([lm_aprs]); a [cat f] pipeline's run is admissible    *)
(*  only at the content it read.  What the cursor needs is the block the  *)
(*  alternative owes AT the round's state, and not a panic.               *)
(* ===================================================================== *)
Lemma lm_wr_blk_sp_run (M : lmodel) (ps cs : list nat) (s0 : lm_st M)
    (I : list (bv 8)) (P a : nat) (pre : list (bv 8)) :
  lm_wr_blk_t M ps cs s0 I P ->
  lm_panic M (lm_dec M a) = false ->
  lm_abs M s0 cs I a = pre ++ u_prompt ->
  lm_wr_sp_t M ps (cs ++ [a]) s0 I (P + S (length pre)).
Proof using.
  intros Hw Hnp Habs.
  destruct (lm_wr_blk_open_s M ps cs s0 I P a Hw Hnp) as [Hop Ht].
  rewrite Habs length_app ll_prompt_len in Hop.
  split; [| exact Ht]. split.
  - replace (S (P + S (length pre))) with (P + (length pre + 2))%nat by lia.
    exact Hop.
  - apply (lm_wr_blk_byte_s M ps cs s0 I P a (S (length pre)) (u_prompt !!! 1%nat)
             (proj1 Hw) Hnp).
    rewrite Habs lookup_app_r; [| lia].
    replace (S (length pre) - length pre)%nat with 1%nat by lia.
    apply list_lookup_lookup_total_lt. rewrite ll_prompt_len. lia.
Qed.

Section union_link_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation pg := (ugn_pipe ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  (* the console ring's names and cameras (seccomp S5b): the residue at a
     [seccomp x] line keeps the line's newline's stored position *)
  Context `{!xv6G Σ} `{FSC : fscfg}.

  (* =================================================================== *)
  (*  1.  THE PARAMETERS: the file's witness and head                     *)
  (* =================================================================== *)

  (* the reader's witness at an era: the boot-ledger entry beside the
     era's file pin *)
  Definition uf0bwk (k : nat) (s0 : fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin gf k vf ∗ f0_bl vf s0)%I.

  Global Instance uf0bwk_persistent k s : Persistent (uf0bwk k s).
  Proof using . rewrite /uf0bwk. apply _. Qed.
  Global Instance uf0bwk_timeless k s : Timeless (uf0bwk k s).
  Proof using . rewrite /uf0bwk. apply _. Qed.

  Lemma uf0bwk_agree (k : nat) (s s' : fstate) :
    uf0bwk k s -∗ uf0bwk k s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "H H'".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_bl_agree with "Hl Hl'").
  Qed.

  Lemma uf0w_bwk (k : nat) (s : fstate) : f0w gf k s -∗ uf0bwk k s.
  Proof using .
    iIntros "[_ H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma uf0w_bwk0 (k : nat) (s : fstate) : f0w gf k s -∗ uf0bwk (S gen_id) s.
  Proof using .
    iIntros "[-> H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma ufhead_cur (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead gf k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & _ & Htn & #Hps & #Hcs & #HE & _ & _)".
    iFrame "Htn Hps Hcs HE". by iPureIntro.
  Qed.

  Lemma ufhead_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead gf k v I -∗ fhead gf k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iSplitL "Htn Hvf Hpre".
    - iFrame "Htn Hps Hcs HE Hvf Hpre". iSplitR; by iPureIntro.
    - iSplitR; [by iPureIntro |]. subst I. iExact "HE".
  Qed.

  (* THE UNION'S WILD LINES: the input's last line is a [seccomp x] one
     (seccomp design 10.7) *)
  Definition uwild_at (I : list (bv 8)) : Prop :=
    I <> [] /\ rest_of I = [] /\ uwild (lm_line_at U I) = true.

  Definition union_params : gen_params U :=
    MkGP U ulmG_laws ulmG_hooks
      UT _ _
      UPIN _ _ (era_pin_agree (fgn_echo gf))
      (f0w gf) _ _
      uf0bwk _ _ (S gen_id) uf0w_bwk uf0w_bwk0 uf0bwk_agree
      (fhead gf) _ ufhead_cur ufhead_inp
      (fun I => uwild (lm_line_at U I) = true).

  (* =================================================================== *)
  (*  2.  THE LINKS ENTAIL THE INTERFACE                                  *)
  (* =================================================================== *)
  Lemma uf0w_cw (k : nat) (s : fstate) : f0w gf k s -∗ f0cw gf k s.
  Proof using . iIntros "[_ H]". iExact "H". Qed.

  Lemma ufhead_boot (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead gf k v I -∗
      turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v []
      ∗ ∃ s0 : fstate, ⌜fstate_ok s0⌝ ∗ (f0boot gf k s0 ∨ UT)
          ∗ (f0cw gf k s0 -∗ f0w gf k s0).
  Proof using .
    rewrite /fhead.
    iIntros "(_ & -> & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iDestruct "Hvf" as (vf) "#Hvf".
    iDestruct "Hpre" as (s0) "(%Hok & Hty & Hbw)".
    iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
    iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
    iFrame "Htn Hps Hcs HE". iExists s0. iSplitR; [by iPureIntro |].
    iSplitL "Hty".
    { iDestruct "Hty" as "[#Hty | #HT]"; [iLeft | by iRight].
      iExists vf. by iFrame "Hvf Hbl Hty". }
    iIntros "Hw". rewrite /f0w. iSplitR; [by iPureIntro | iExact "Hw"].
  Qed.

  (* the links are the claim's: the bundle is the record equation (the
     block-first byte refuses the wild line, seccomp design 10.7) *)
  Lemma union_links_gl : union_links ug -∗ glinks U union_params.
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /glinks /gl_w /gl_blk /gl_pro /gl_head /gl_taint.
    cbn [gT gPIN gW gH gwild union_params].
    iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - iIntros "!>" (k v P0 b ps0 cs0 s0 I0 Φ)
        "%H1 %H2 %H3 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
      iApply (union_write_link ug Hc k v P0 b ps0 cs0 s0 I0 Φ H1 H2 H3
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply uf0w_cw |].
      iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
    - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
        "%H0 %H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
      rewrite /lm_abs /lm_line_at in H0 H6 H8.
      iApply (union_write_link_blk ug Hc k v P0 a b ps0 cs0 s0 I0 Φ
                (not_true_is_false _ H0) H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply uf0w_cw |].
      iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
    - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
        "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
      iApply (union_write_link_pro ug Hc k v P0 a b ps0 cs0 s0 I0 Φ
                H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply uf0w_cw |].
      iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
    - iIntros "!>" (k v I a b Φ) "%H1 %H2 #Hpin Hh HΦ".
      iDestruct (ufhead_boot with "Hh") as "(Ht & #Hps & #Hcs & #HE & %s0 & %Hok & Hbt & Hwb)".
      iApply (union_write_link_first ug Hc k v a b s0 Φ Hok H1 H2
                with "Hpin Ht Hps Hcs HE Hbt [HΦ Hwb]").
      iIntros "[(Ht & Hps' & Hcs' & HE' & Hw) | #HT]"; iApply "HΦ"; [| by iRight].
      iLeft. iExists s0. iFrame "Ht Hps' Hcs' HE'". by iApply "Hwb".
    - iIntros "!>" (k v b Φ) "_ #HT HΦ".
      iApply (union_write_link_taint ug Hc with "HT HΦ").
  Qed.

  (* the taint's byte at the era's own number, for a device at it *)
  Lemma union_links_gl_taint_now :
    union_links ug -∗ gl_taint_at U union_params (S gen_id).
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /gl_taint_at. cbn [gT union_params].
    iIntros "!>" (b Φ) "#HT HΦ".
    iApply (union_write_link_taint ug Hc with "HT HΦ").
  Qed.

  (* =================================================================== *)
  (*  3.  THE READ RECEIPT, THE TURN, THE RESIDUE                         *)
  (* =================================================================== *)
  Lemma uread_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    uread_ret ug k v n ws -∗
    UT ∨ (∃ (ps0 cs0 : list nat) (s0 : fstate) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage U ps0 cs0 s0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before U ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ uf0bwk k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /uread_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & %Hboots & #Hinp & %Hdi & Hrest & _)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0 s0) "(#Hcs0 & #Hps0 & #Hw & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, s0, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0 Htlb".
    iSplitR; [iPureIntro; rewrite length_fmap length_app Hdl; reflexivity |].
    iSplitR; [by iPureIntro |].
    iDestruct "Hw" as (vf) "[#Hvf #Hlb]".
    iExists vf. iFrame "Hvf". iApply (f0_lb_bl with "Hlb").
  Qed.

  Lemma uturn0 (k : nat) :
    fturn_pre gf k -∗
    (∃ v : era_pins, UPIN k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [] ∗ rpos_auth v 0%nat)
    ∗ (∃ v : era_pins, UPIN k v ∗ gwc_ban U union_params k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre /FileOut.fturn_core.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE & Hrp)".
    iSplitL "Hdl Hrp"; [iExists v; by iFrame "Hpin Hdl HE Hrp" |].
    iExists v. iFrame "Hpin". rewrite /gwc_ban. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /gH /union_params /fhead.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  (* THE RECORD'S RESIDUE: the generic cursor bounds, with the typed
     lines' witness beside them ([FileLinksLine.fwc_rresw]'s shape) *)
  (* ...AND, at an input whose last line is a [seccomp x] one, THE ERA'S
     WILD TOKEN (or the taint): the read that completed that line minted it
     (seccomp design 10.4), and the reader's pieces carry it from there *)
  (* ...AND WHERE THE RING STORED THE LINE'S NEWLINE (seccomp design
     10.12, lane S5b): position [length I - 1] of the console ring's stored
     sequence, its push trace's era input the line's own input.  What the
     marked arm of a later read at [I] is refuted against. *)
  Definition uring_at (I : list (bv 8)) : iProp Σ :=
    (∃ (sl : list (list mobs * bv 8)) (h0 : list mobs),
       ucons_stored_lb fsc_cons sl
       ∗ ⌜sl !! (length I - 1)%nat = Some (h0, wl_nl)
          /\ ins (open_seg h0) = I /\ obs_boots h0 = S gen_id⌝)%I.

  Global Instance uring_at_persistent I : Persistent (uring_at I).
  Proof using . rewrite /uring_at. apply _. Qed.
  Global Instance uring_at_timeless I : Timeless (uring_at I).
  Proof using . rewrite /uring_at. apply _. Qed.

  Definition urresw (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (gwc_rres U union_params v I ∗ flw gf I
     ∗ (⌜uwild_at I⌝ → (usecc_tok_at ug (S gen_id) I ∗ uring_at I) ∨ UT))%I.

  Global Instance urresw_persistent v I : Persistent (urresw v I).
  Proof using . rewrite /urresw. apply _. Qed.
  Global Instance urresw_timeless v I : Timeless (urresw v I).
  Proof using . rewrite /urresw. apply _. Qed.

  Lemma urresw_res (v : era_pins) (I : list (bv 8)) :
    urresw v I -∗ gwc_rres U union_params v I.
  Proof using . iIntros "[$ _]". Qed.

  (* =================================================================== *)
  (*  4.  THE N-WRITER ROUND'S LINE ARM, AND ITS PROMPT STEP              *)
  (*                                                                      *)
  (*  [PipesLinkInst.pipes_X] at the union: the credential [pwc_blkU] at  *)
  (*  the block the family merged, a block of the round's line at the     *)
  (*  ROUND'S STATE [sR] -- the state the family's runs read, tied to the *)
  (*  writer's stage by the credential (S7).  The era is the console's.   *)
  (* =================================================================== *)
  Definition union_X (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ :=
    (⌜k = S gen_id⌝
     ∗ ∃ (sR : fstate) (lR : pline') (pre : list (bv 8)),
         ⌜pv_line pview_unionU (lineV U I) = Some lR /\ adm_u_g lR = true
          /\ line_blocks (files_of sR) lR pre⌝
         ∗ pwc_blkU ug v I sR k pre false)%I.

  Global Instance union_X_timeless k v I : Timeless (union_X k v I).
  Proof using .
    rewrite /union_X. apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.exist_timeless; intro sR. apply bi.exist_timeless; intro lR.
    apply bi.exist_timeless; intro pre.
    apply bi.sep_timeless; [apply bi.pure_timeless | apply pwc_blkU_timeless].
  Qed.

  Lemma union_X_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    UPIN k v -∗ union_links ug -∗ union_X k v I -∗
    (gwc_sp_t U union_params k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hx HΦ".
    iDestruct (union_links_eq with "Hlk") as %Hc.
    iDestruct "Hx" as "[%Hk Hx]".
    iDestruct "Hx" as (sR lR pre) "([%HlR [%Ha %Hbl]] & Hpw)".
    iApply (union_file_link ug Hc k v I sR lR pre b Φ HlR Ha Hbl Hb with "Hpw").
    iIntros "Hret". iApply "HΦ". rewrite /gwc_sp_t.
    iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
    iDestruct "Hx" as (ps cs s0 P) "([%Hw %Htie] & #HW & Htn & Hps & Hcs & HE)".
    iLeft. iExists ps, (cs ++ [pv_enc pview_unionU lR (PLRun pre)]), s0,
      (P + S (length pre))%nat.
    iSplitR.
    { iPureIntro. apply lm_wr_blk_sp_run; [exact Hw | |].
      - exact (pv_run_panic pview_unionU lR pre).
      - rewrite /lm_abs Htie.
        exact (pv_run_cont pview_unionU sR (lineV U I) lR pre HlR). }
    rewrite /gcur. rewrite (_ : (P + S (length pre))%nat = S (P + length pre)); [| lia].
    iFrame "Htn Hps Hcs HE". cbn [gW union_params]. rewrite /f0w.
    iSplitR; [by iPureIntro | iExact "HW"].
  Qed.

  (* =================================================================== *)
  (*  5.  THE RECORD                                                      *)
  (* =================================================================== *)
  Definition union_link_inst : LinkRec Σ :=
    gen_link_inst U union_params union_X union_X_timeless
      (union_links ug) (union_links_persistent ug) union_links_gl
      union_X_dollar (uread_ret ug) uread_ret_res (fturn_pre gf)
      uturn0 urresw urresw_persistent urresw_timeless urresw_res
      (ualt_code (UR RFSilent)).

  Lemma union_inst_T : lk_T union_link_inst = UT.
  Proof using . reflexivity. Qed.
  Lemma union_inst_pin : lk_pin union_link_inst = UPIN.
  Proof using . reflexivity. Qed.
  Lemma union_inst_links : lk_links union_link_inst = union_links ug.
  Proof using . reflexivity. Qed.
  Lemma union_inst_rr : lk_rr union_link_inst = uread_ret ug.
  Proof using . reflexivity. Qed.
  Lemma union_inst_rres : lk_rres union_link_inst = urresw.
  Proof using . reflexivity. Qed.
  Lemma union_inst_turn : lk_turn union_link_inst = fturn_pre gf.
  Proof using . reflexivity. Qed.
  Lemma union_inst_lpr :
    lk_lpr union_link_inst = gwc_lpr U union_params union_X.
  Proof using . reflexivity. Qed.
End union_link_inst.

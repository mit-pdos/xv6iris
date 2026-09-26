(* ===================================================================== *)
(*  UShURoundLaws.v -- THE UNION LOOP'S PROMPT AND READ LAWS AT THE       *)
(*  WIDENED CREDENTIAL (cut C9g; design: claude-notes/design/union.md     *)
(*  sections 3-4).                                                        *)
(*                                                                        *)
(*  The round law ([UShUPipes.sh_round_holds_union_closed]) is stated at  *)
(*  the widened credential [UShURoundDefs.uWcu]; the shell's loop owes     *)
(*  two more laws at it before /init can hand the loop its slot:          *)
(*                                                                        *)
(*    - THE PROMPT ([UShKernel.sh_prompt_law]): at the file family        *)
(*      [uWcf] it is [UShRound.sh_prompt_law_file]'s argument at the      *)
(*      union record (the DONE arm framed, the PEND arm's '$' filing the  *)
(*      deed's alternative); at the TERMINAL pipeline shape it is the     *)
(*      terminal writer's two further bytes ([PipeBothN.pprompt_forkN_h]); *)
(*      at the COMMITTED shape the '$' files the family's merged block    *)
(*      ([PipeOutN.pipesV_file], then the record's N-writer arm           *)
(*      [UnionLinkInstAt.union_X_dollar_at]) and the deed goes from its   *)
(*      PRE tie to DONE by the pipeline's identity step;                   *)
(*    - THE READ ([UInitSh.cons_cred_holds_at]'s fifth law): a line read  *)
(*      at the file family moves the deed from DONE to PRE (the file's    *)
(*      [Hwc_f]); after a terminal round it is refuted by the frozen      *)
(*      resolution (the taint).                                           *)
(*                                                                        *)
(*  With the two input readings the cursor's boundary law spends.         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UkRun.
Require Import UexecExecInst.
Require Import WpUart.
Require Import ConsoleInv.
Require Import AppCfg.
Require Import AppInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinksLine.
Require Import FileLinkGen.       (* [f0w_at] *)
Require Import LinkRec.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShFork.
Require Import UCodeShK.
Require Import UShLine.
Require Import UShLineHold.
Require Import UShPanic.
Require Import UShPanicHold.
Require Import UShKernel.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutN.
Require Import PipeOutW.          (* [secc_tok_at]: the wild shape's token *)
Require Import PipesFire.
Require Import UkPipesIface.      (* [pnsN], [pipesNG] *)
Require Import UkShPipesFork.     (* [big_sepL_exist_fun], [alt_forkc_prompt] *)
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionView.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInst.
Require Import UnionLinkInstAt.
Require Import UnionReadInstAt.   (* [union_ep_refl_at] *)
Require Import UShURoundDefs.
Require Import UShURoundShapes.
Require Import CtxIdDefs.
Require PipeDisc.
Require EchoLinks.
Local Open Scope Z_scope.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  S0  THE PURE HALF                                                     *)
(* ===================================================================== *)

(* a pipeline line leaves the state alone, at every alternative *)
Lemma ustep_pipe (s : fstate) (p : producer) (n : list filt) (a : lm_alt U) :
  lm_step U s (LPipe p n) a = s.
Proof using. destruct a; reflexivity. Qed.

(* the '$' at the DEED's alternative: a block whose continuation is the
   bare prompt is written up to its space once the alternative is filed
   ([LineModelLinks.lm_wr_blk_dollar] at an alternative the deed names) *)
Lemma uwr_blk_dollar_at (ps cs : list nat) (s : fstate) (I : list (bv 8)) (P a : nat) :
  lm_wr_blk U ps cs s I P ->
  lm_panic U (lm_dec U a) = false ->
  lm_cont U (ust cs s I) (ul I) (lm_dec U a) = u_prompt ->
  lm_wr_sp U ps (cs ++ [a]) s I (S P).
Proof using.
  intros Hw Hnp Hcont.
  pose proof (lm_wr_blk_started U ps cs s I P Hw) as Hst.
  pose proof Hw as (Hpin & Hm & Hdv & HP).
  assert (Hpend : lm_pending_at U ps (cs ++ [a]) s I = u_prompt).
  { rewrite (lm_wr_blk_pending_s U ps cs s I P a Hw Hnp). exact Hcont. }
  assert (Hlow : lm_proc_before U ps (cs ++ [a]) s I = lm_proc_before U ps cs s I)
    by exact (lm_wr_blk_low U ps cs s I P a Hw).
  assert (Hup : lm_proc_stream U ps (cs ++ [a]) s I
                = lm_proc_before U ps cs s I ++ u_prompt)
    by (rewrite /lm_proc_stream Hlow Hpend; reflexivity).
  assert (Hlen : length (lm_proc_stream U ps (cs ++ [a]) s I) = S (S P)).
  { rewrite Hup (length_app (lm_proc_before U ps cs s I) u_prompt) ll_prompt_len. lia. }
  split.
  - rewrite /lm_wr_open. split_and!.
    + exact (lm_wr_blk_pin_snoc U ps cs s I P a Hw).
    + exact Hm.
    + rewrite length_app Hdv. cbn [length]. lia.
    + rewrite Hdv (lm_pro_idx_snoc_ne U cs a Hnp).
      pose proof (Hpin (length cs) ltac:(rewrite Hst; lia)). lia.
    + by rewrite Hlen.
  - rewrite Hup lookup_app_r; [| lia].
    replace (S P - length (lm_proc_before U ps cs s I))%nat with 1%nat by lia.
    exact ll_prompt_tail.
Qed.

Section UShURoundLaws.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER ([UShRound]'s header) *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ, !pipesNG Σ}.
  #[local] Existing Instance eo_turn | 0.

  Context (ug : union_gn) (r : file_names) (s0 : fstate).
  Local Notation gf := (ugn_file ug).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = ucl ug).

  Local Notation T := (file_taint (fgn_cl gf)).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PT := (upterm_shape ug).
  Local Notation PD := (updone_shape ug).
  Local Notation Wcl := (uWcl ug s0).
  Local Notation Wbl := (uWbl ug s0).
  Local Notation Wcf := (uWcf ug r s0).
  Local Notation Wbf := (uWbf ug r s0).
  Local Notation Wcu := (uWcu ug r s0 PT PD).
  Local Notation PRE := (ush_pre_at ug r s0).
  Local Notation DONE := (ush_done_at ug r s0).
  Local Notation PEND := (ush_pend_at ug r s0).
  Local Notation DPRE := (ush_deed_at ug r upre_tie s0).

  #[local] Instance url_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance url_T_tl0 : Timeless T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.

  (* =================================================================== *)
  (*  S1  THE INPUT READINGS                                              *)
  (* =================================================================== *)

  (* every arm of the record's families carries the input's lower bound,
     or is the era's head (at the empty input), or the taint *)
  Local Lemma ulpr_inp (k : nat) (v : era_pins) (I : list (bv 8)) (p : nat) :
    gwc_lpr U (union_params_at ug s0) (union_X_at ug s0) k v I p ⊢ inp_lb v I ∨ T.
  Proof using .
    destruct p as [| [| [| p']]]; cbn [gwc_lpr].
    - rewrite /gwc_line /gwc_pro /gwc_post /gcur /union_X_at /union_X /pwc_blkU /pwc_blkV.
      cbn [gH gT union_params_at]. rewrite /fhead_at.
      iIntros "[[Hl | [Hh | #HT]] | [Hq | Hx]]".
      + iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
      + iDestruct "Hh" as "(-> & _ & _ & _ & _ & #HE & _)". by iLeft.
      + by iRight.
      + iDestruct "Hq" as (a) "[_ [Hl | #HT]]"; [| by iRight].
        iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
      + iDestruct "Hx" as "[[_ Hx] _]".
        iDestruct "Hx" as (sR lR pre) "[_ [Hl | #HT]]"; [| by iRight].
        iDestruct "Hl" as (ps cs s1 P) "(_ & _ & _ & _ & _ & _ & _ & #HE)". by iLeft.
    - rewrite /gwc_sp_t /gcur. cbn [gT union_params_at].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
    - rewrite /gwc_open_t /gcur. cbn [gT union_params_at].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
    - rewrite /gwc_blk. cbn [gT union_params_at].
      iIntros "[Hl | #HT]"; [| by iRight].
      iDestruct "Hl" as (ps cs s P) "(_ & _ & _ & _ & #HE & _)". by iLeft.
  Qed.

  Lemma uWcl_inp : UShLine.ush_wc_inp (fgn_echo gf) T Wcl.
  Proof using .
    intros I p. iIntros "H".
    iApply (bi.persistent_entails_r with "H").
    rewrite /uWcl /lk_lcred. iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst].
    iDestruct (ulpr_inp (S gen_id) v I p with "Hc") as "[#HE | #HT]".
    - iLeft. iExists v. by iFrame "Hpin HE".
    - by iRight.
  Qed.

  Lemma uWbl_inp : UShLine.ush_wb_inp (fgn_echo gf) T Wbl.
  Proof using .
    intros I. rewrite /uWbl.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hb]".
    iDestruct (lk_ban_inp FI (S gen_id) v I with "Hb") as "[Hb Hi]".
    iSplitL "Hb"; [iExists v; iFrame "Hpin Hb" |].
    iDestruct "Hi" as "[[#HE %Hr] | #HT]"; last first.
    { iRight. iExact "HT". }
    iLeft. iSplitR; [| by iPureIntro]. iExists v. iFrame "Hpin HE".
  Qed.

  (* THE WILD SHAPE carries the era's pin and the input's bound, off its
     token *)
  Lemma ushape_inp (I : list (bv 8)) :
    useccomp_shape ug I -∗
    (∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I) ∗ ⌜rest_of I = []⌝.
  Proof using .
    iIntros "[Htok _]". rewrite /usecc_tok_at /secc_tok_at.
    iDestruct "Htok" as (v) "(#Hp & _ & #HI & %Hn & _)".
    iSplit; [iExists v; iSplit; [iExact "Hp" | iExact "HI"] |].
    iPureIntro. exact (proj1 (proj2 Hn)).
  Qed.

  Lemma uWbf_inp : UShLine.ush_wb_inp (fgn_echo gf) T Wbf.
  Proof using .
    intros I. rewrite /uWbf. iIntros "[Hb | #Hw]".
    - iDestruct (UShLineHold.ush_wb_inp_hold (fgn_echo gf) T Wbl DONE uWbl_inp I
                   with "Hb") as "[Hb $]". by iLeft.
    - iSplitR; [by iRight |]. iLeft. iApply (ushape_inp with "Hw").
  Qed.

  Lemma uWcf_inp : UShLine.ush_wc_inp (fgn_echo gf) T Wcf.
  Proof using .
    intros I p. iIntros "Hc". destruct p as [| [| [| p]]].
    - rewrite uWcf_0. iDestruct "Hc" as "[[Hc Hd] | [Hc Hd]]".
      + iDestruct (uWcl_inp I 0%nat with "Hc") as "[Hc $]". iLeft. iFrame "Hc Hd".
      + iDestruct (uWcl_inp I 3%nat with "Hc") as "[Hc $]". iRight. iFrame "Hc Hd".
    - rewrite uWcf_1. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (uWcl_inp I 1%nat with "Hc") as "[Hc $]". iFrame "Hc Hd".
    - rewrite uWcf_2. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (uWcl_inp I 2%nat with "Hc") as "[Hc $]". iFrame "Hc Hd".
    - rewrite uWcf_S3. iDestruct "Hc" as "[Hc Hd]".
      iDestruct (uWcl_inp I 3%nat with "Hc") as "[Hc $]". iFrame "Hc Hd".
  Qed.

  (* the two pipeline shapes carry the era's pin and the input's bound *)
  Local Lemma upterm_inp (I : list (bv 8)) (c : nat) :
    PT I c -∗ PT I c ∗ ∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I.
  Proof using .
    iIntros "H". iApply (bi.persistent_entails_r with "H"). rewrite /upterm_shape.
    iIntros "H". iDestruct "H" as (v γc γm dep i sw sR lR) "(_ & #Hpin & #Hlb & _)".
    iExists v. by iFrame "Hpin Hlb".
  Qed.

  Local Lemma updone_inp (I : list (bv 8)) :
    PD I -∗ PD I ∗ ∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v ∗ inp_lb v I.
  Proof using .
    iIntros "H". iApply (bi.persistent_entails_r with "H"). rewrite /updone_shape.
    iIntros "H". iDestruct "H" as (v γc γm dep sR lR) "(_ & #Hpin & #Hlb & _)".
    iExists v. by iFrame "Hpin Hlb".
  Qed.

  Lemma uWcu_inp : UShLine.ush_wc_inp (fgn_echo gf) T Wcu.
  Proof using .
    intros I p. iIntros "Hc". rewrite {1}/uWcu.
    iDestruct "Hc" as "[Hc | [[%Hlt Hsh] | [(%Hz & Hsh & Hd & #Hcw) | #Hw]]]".
    - iDestruct (uWcf_inp I p with "Hc") as "[Hc $]".
      iApply (uWcu_of ug r s0 PT PD I p with "Hc").
    - iDestruct (upterm_inp with "Hsh") as "[Hsh Hi]".
      iSplitR "Hi"; [| by iLeft].
      rewrite /uWcu. iRight. iLeft. iFrame "Hsh". by iPureIntro.
    - iDestruct (updone_inp with "Hsh") as "[Hsh Hi]".
      iSplitR "Hi"; [| by iLeft].
      rewrite /uWcu. iRight. iRight. iLeft. iFrame "Hsh Hd Hcw". by iPureIntro.
    - iSplitR; [iApply (uWcu_wild ug r s0 PT PD I p with "Hw") |]. iLeft.
      iDestruct (ushape_inp with "Hw") as "[$ _]".
  Qed.

  (* =================================================================== *)
  (*  S2  THE READ                                                        *)
  (* =================================================================== *)
  Section read.
  Context (γp : gname).
  Local Notation Pm := (UShLine.ush_mid_at (lk_rres FI) (fgn_echo gf) γp).

  (* the reader's pieces carry the typed lines' witness in their residue *)
  Lemma umid_flw (I : list (bv 8)) :
    Pm I -∗ Pm I ∗ FileLinksLine.flw gf I.
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hu & Hua & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #HE & #Hres & Hrp)".
    iAssert (FileLinksLine.flw gf I) as "#Hw".
    { iEval (cbn [lk_rres union_link_inst_at gen_link_inst]; rewrite /urresw) in "Hres".
      iDestruct "Hres" as "(_ & $ & _)". }
    iSplitL; [| iExact "Hw"]. iFrame "Hu Hua Hrd". iExists v.
    iSplitR; [iExact "Hpin" |]. iSplitL "Hdl"; [iExact "Hdl" |].
    iSplitR; [iExact "HE" | iFrame "Hres Hrp"].
  Qed.

  (* ...and the era's pin *)
  Lemma umid_pin (J : list (bv 8)) :
    Pm J -∗ Pm J ∗ ∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v.
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hu & Hua & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #HE & #Hres & Hrp)".
    iSplitL; [| iExists v; iExact "Hpin"].
    iFrame "Hu Hua Hrd". iExists v.
    iSplitR; [iExact "Hpin" |]. iSplitL "Hdl"; [iExact "Hdl" |].
    iSplitR; [iExact "HE" | iFrame "Hres Hrp"].
  Qed.

  (* ...and the TRANSITION'S RECEIPT: at a [seccomp x] line the read
     completed, the era's wild token at that line (or the taint) *)
  Lemma umid_wild (J : list (bv 8)) :
    Pm J -∗ Pm J
    ∗ (⌜uwild_at J⌝ → (usecc_tok_at ug (S gen_id) J ∗ uring_at J) ∨ T)
    (* ...and the reader's position at [J] (seccomp S5b) *)
    ∗ ∃ v : era_pins, era_pin (fgn_echo gf) (S gen_id) v ∗ rpos_lb v (length J).
  Proof using .
    rewrite /UShLine.ush_mid_at. iIntros "(Hu & Hua & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #HE & #Hres & Hrp)".
    iAssert (⌜uwild_at J⌝ → (usecc_tok_at ug (S gen_id) J ∗ uring_at J) ∨ T)%I
      as "#Hw".
    { iEval (cbn [lk_rres union_link_inst_at gen_link_inst]; rewrite /urresw) in "Hres".
      iDestruct "Hres" as "(_ & _ & $)". }
    iDestruct (rpos_lb_get with "Hrp") as "#Hlb".
    iSplitL; [| iSplitR; [iExact "Hw" | iExists v; iSplitR; [iExact "Hpin" | iExact "Hlb"]]]. iFrame "Hu Hua Hrd". iExists v.
    iSplitR; [iExact "Hpin" |]. iSplitL "Hdl"; [iExact "Hdl" |].
    iSplitR; [iExact "HE" | iFrame "Hres Hrp"].
  Qed.

  (* THE READ AFTER THE WILD SHAPE IS VACUOUS: the token froze the choice
     list one short of its line, which the new line's read residue
     contradicts ([uterm_read_law]'s argument; seccomp design 10.5) *)
  Lemma uwild_read_absurd (I l : list (bv 8)) :
    Pm (I ++ l ++ [wl_nl]) -∗ useccomp_shape ug I -∗ False.
  Proof using .
    iIntros "Hpm [Htok _]".
    rewrite /UShLine.ush_mid_at. iDestruct "Hpm" as "(_ & _ & _ & Hv)".
    iDestruct "Hv" as (v') "(#Hpin' & _ & _ & #Hres & _)".
    rewrite /usecc_tok_at /secc_tok_at.
    iDestruct "Htok" as (v) "(#Hpin & _ & _ & %Hn & #Hfz & _)".
    destruct Hn as (Hpos & _).
    iDestruct (era_pin_agree with "Hpin' Hpin") as %->.
    iEval (cbn [lk_rres union_link_inst_at gen_link_inst]; rewrite /urresw /gwc_rres) in "Hres".
    iDestruct "Hres" as "[Hres _]".
    iDestruct "Hres" as (ps0 cs0 s1) "(%Hrd & _ & _ & #Hcs0 & _)".
    destruct Hrd as (_ & _ & _ & Hle).
    assert (Hrl : removelast (I ++ l ++ [wl_nl]) = (I ++ l)%list).
    { rewrite app_assoc. apply epu_removelast_snoc. }
    rewrite Hrl in Hle.
    pose proof (nlines_app_le I l) as Hmono.
    iApply (cs_frozen_at_lb_absurd v (nlines I - 1)%nat cs0 ltac:(lia) with "Hfz Hcs0").
  Qed.

  (* the open credential says the input has no partial line *)
  Local Lemma uWcl2_rest (I : list (bv 8)) :
    Wcl I 2%nat -∗ Wcl I 2%nat ∗ (⌜rest_of I = []⌝ ∨ T).
  Proof using .
    rewrite /uWcl /lk_lcred. iIntros "Hc".
    iDestruct "Hc" as (v) "[#Hpin Hc]".
    cbn [lk_pin lk_lpr union_link_inst_at gen_link_inst gwc_lpr].
    rewrite /gwc_open_t. iDestruct "Hc" as "[Hc | #HT]".
    - iDestruct "Hc" as (ps cs sw P) "(%Hw & Hcur)". iSplitL "Hcur".
      + iExists v. iSplitR; [iExact "Hpin" |]. iLeft. iExists ps, cs, sw, P.
        iFrame "Hcur". by iPureIntro.
      + iLeft. iPureIntro. destruct Hw as [(_ & Hr & _) _]. exact Hr.
    - iSplitL ""; [iExists v; iSplitR; [iExact "Hpin" | by iRight] | by iRight].
  Qed.

  (* at the deed: the read that completed a line *)
  Lemma ush_pre_of_done_u (I l : list (bv 8)) :
    rest_of I = [] -> wl_nl ∉ l -> uwild (ul (I ++ l ++ [wl_nl])) = false ->
    uline_wit ug (I ++ l ++ [wl_nl]) -∗ DONE I -∗ PRE (I ++ l ++ [wl_nl]).
  Proof using .
    intros Hr Hl HnwJ. rewrite /ush_pre_at /ush_done_at /ush_deed_at.
    iIntros "#Hlw Hd". iSplitL; [| iExact "Hlw"].
    iDestruct "Hd" as "[Hd | #HT]"; last by iRight.
    iDestruct "Hd" as (cs s v) "(Hd & %Htie & #Hty & #Hpin & #Hcs & %Hnw)".
    iLeft. iExists cs, s, v. iFrame "Hd Hty Hpin Hcs %". iPureIntro.
    exact (upre_tie_of_done cs s0 I l _ Hr Hl Htie).
  Qed.

  (* THE READ AT THE FILE FAMILY: 2 at the old input to the lend at the
     new one, the deed from DONE to PRE *)
  Lemma uHwc_f : forall I l : list (bv 8), wl_nl ∉ l ->
    uwild (ul (I ++ l ++ [wl_nl])) = false ->
    ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wcf I 2%nat ={⊤}=∗
      Pm (I ++ l ++ [wl_nl]) ∗ Wcf (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros I l Hl HnwJ. rewrite uWcf_2 uWcf_S3. iIntros "Hmid [Hc Hd]". iModIntro.
    iDestruct (umid_flw (I ++ l ++ [wl_nl]) with "Hmid") as "[Hmid #Hw]".
    iDestruct (uWcl2_rest I with "Hc") as "[Hc Hr]".
    iDestruct (UShLine.ush_mid_wc_read_t_at FI (fgn_echo gf) γp (S gen_id) I l Hl
                 (union_ep_refl_at ug s0) with "Hmid Hc") as "[$ $]".
    iDestruct "Hr" as "[%Hr | #HT]"; last (iApply (ush_pre_taint ug r with "HT")).
    iApply (ush_pre_of_done_u I l Hr Hl HnwJ with "[] Hd"). rewrite /uline_wit. iLeft. iExact "Hw".
  Qed.

  (* THE READ AFTER A TERMINAL ROUND IS THE TAINT: the terminal byte froze
     the claim's resolution at the round's line, which the new line's read
     residue contradicts *)
  Lemma uterm_read_law : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ Pm (I ++ l ++ [wl_nl]) -∗ PT I 7%nat ={⊤}=∗ Pm (I ++ l ++ [wl_nl]) ∗ T.
  Proof using .
    intros I l Hnl. iIntros "Hpm Hsh".
    rewrite /UShLine.ush_mid_at. iDestruct "Hpm" as "(Hu & Hua & Hrd & Hv)".
    iDestruct "Hv" as (v') "(#Hpin' & Hdl & #HE & #Hres & Hrp)".
    rewrite /upterm_shape.
    iDestruct "Hsh" as (v γc γm dep i sw sR lR) "(%Hp & #Hpin & _ & Hfe & _)".
    destruct Hp as (_ & _ & _ & _ & _ & Hpos & _).
    iDestruct (era_pin_agree with "Hpin' Hpin") as %->.
    iModIntro. iSplitL "Hu Hua Hrd Hdl Hrp".
    { iFrame "Hu Hua Hrd". iExists v.
      iSplitR; [iExact "Hpin" |]. iSplitL "Hdl"; [iExact "Hdl" |].
      iSplitR; [iExact "HE" | iFrame "Hres Hrp"]. }
    rewrite /pwc_fork_exitN. iDestruct "Hfe" as "(_ & _ & _ & [#Hfz | #HT])";
      [| iExact "HT"].
    iExFalso.
    iEval (cbn [lk_rres union_link_inst_at gen_link_inst]; rewrite /urresw /gwc_rres) in "Hres".
    iDestruct "Hres" as "[Hres _]".
    iDestruct "Hres" as (ps0 cs0 s1) "(%Hrd & _ & _ & #Hcs0 & _)".
    destruct Hrd as (_ & _ & _ & Hle).
    assert (Hrl : removelast (I ++ l ++ [wl_nl]) = (I ++ l)%list).
    { rewrite app_assoc. apply epu_removelast_snoc. }
    rewrite Hrl in Hle.
    pose proof (nlines_app_le I l) as Hmono.
    iApply (cs_frozen_at_lb_absurd v (nlines I - 1)%nat cs0 ltac:(lia) with "Hfz Hcs0").
  Qed.

  (* THE READ AT THE WIDENED CREDENTIAL *)
  Lemma uWcu_read : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wcu I 2%nat ={⊤}=∗
      Pm (I ++ l ++ [wl_nl]) ∗ Wcu (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros I l Hnl. iIntros "Hpm Hc".
    rewrite {1}/uWcu. iDestruct "Hc" as "[Hc | [[_ Hsh] | [[%Hz _] | #Hw]]]"; [| | lia |].
    - destruct (decide (uwild (ul (I ++ l ++ [wl_nl])) = true)) as [Hwl | Hwl].
      + (* THE TRANSITION'S LANDING: the read completed a [seccomp x] line,
           the residue hands over the era's wild token (seccomp design
           10.4, 10.10) *)
        iDestruct (umid_wild with "Hpm") as "(Hpm & #Hwt & #Hlb)".
        iDestruct (umid_pin with "Hpm") as "[Hpm Hv]". iDestruct "Hv" as (v) "#Hpin".
        iModIntro. iFrame "Hpm".
        assert (HJne : (I ++ l ++ [wl_nl])%list <> []).
        { intros Hq. apply (f_equal length) in Hq. rewrite !length_app in Hq.
          cbn [length] in Hq. lia. }
        iDestruct ("Hwt" with "[%]") as "[[#Htok _] | #HT]".
        { split; [exact HJne |]. split; [rewrite app_assoc; apply rest_of_snoc_nl |].
          exact Hwl. }
        * iApply (uWcu_wild ug r s0 PT PD _ 3%nat). rewrite /useccomp_shape.
          iSplitR; [iExact "Htok" |]. iSplitR; [by iPureIntro |]. iExact "Hlb".
        * iApply (uWcu_taint ug r s0 PT PD _ 3%nat v with "Hpin HT").
      + iMod (uHwc_f I l Hnl (not_true_is_false _ Hwl) with "Hpm Hc") as "[$ Hw]".
        iModIntro. iApply (uWcu_of ug r s0 PT PD _ 3%nat with "Hw").
    - iMod (uterm_read_law I l Hnl with "Hpm Hsh") as "[Hpm #HT]".
      iDestruct (umid_pin with "Hpm") as "[$ Hv]". iDestruct "Hv" as (v) "#Hpin".
      iModIntro. iApply (uWcu_taint ug r s0 PT PD _ 3%nat v with "Hpin HT").
    - iExFalso. iApply (uwild_read_absurd I l with "Hpm Hw").
  Qed.
  End read.

  (* =================================================================== *)
  (*  S3  THE PROMPT AT THE FILE FAMILY                                   *)
  (* =================================================================== *)

  (* the write call at a disjunctive precondition: each arm its own walk *)
  Local Lemma uksh_w_or (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (St A B Co : iProp Σ) :
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ A) Co -∗
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ B) Co -∗
    UkSh.ksh_w (PS := uprogSG_free) N fdw ua nb (St ∗ (A ∨ B)) Co.
  Proof using .
    iIntros "HA HB" (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hs [HA' | HB']] Hrun Hcont".
    - iApply ("HA" $! h m avail with "[%] [%] [%] Hcode [$Hs $HA'] Hrun Hcont");
        assumption.
    - iApply ("HB" $! h m avail with "[%] [%] [%] Hcode [$Hs $HB'] Hrun Hcont");
        assumption.
  Qed.

  (* a tainted round writes its prompt on the record's own law, DONE := T *)
  Local Lemma uksh_w_prompt_taint (N : uk_names Σ) (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
    T -∗ union_links ug -∗ UCodeShK.shk_rodata (ukn_t N) -∗
    UkSh.ksh_w (PS := uprogSG_free) N (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd N) l vw ∗ Wcl I 0%nat)
      (UserFd.ustd_at (ukn_fd N) l vw ∗ (Wcl I 2%nat ∗ DONE I)).
  Proof using .
    intros Hl2. iIntros "#HT #Hlk #Hro".
    iApply (UShPanicHold.ksh_w_mono (PS := uprogSG_free) N _ _ _
              (UserFd.ustd_at (ukn_fd N) l vw ∗ lk_lcred FI (S gen_id) I 0%nat)%I _
              (UserFd.ustd_at (ukn_fd N) l vw ∗ lk_lcred FI (S gen_id) I 2%nat)%I
              with "[] []").
    { iIntros "[Hs Hc]". iFrame "Hs". rewrite /uWcl. iExact "Hc". }
    { iIntros "[Hs Hc]". iFrame "Hs". iSplitL "Hc";
        [rewrite /uWcl; iExact "Hc" | iApply (ush_deed_taint ug r with "HT")]. }
    iApply (UShPanic.ksh_w_of_link_lcred_at (PS := uprogSG_free) FI N I l vw rb
              Hl2 with "[] [] Hro"); [by iRight |].
    cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk".
  Qed.

  (* THE PEND ARM'S STEP FAMILY: position 0 is the round's cursor with the
     deed beside it; positions 1 and 2 are the record's settled shapes with
     the deed DONE *)
  Local Definition upfam (v : era_pins) (P : nat) (I : list (bv 8)) (s : dst)
      (p : nat) : iProp Σ :=
    match p with
    | O => (turn v P ∗ fown r s)%I
    | S p' => (lk_lpr FI (S gen_id) v I (S p') ∗ DONE I)%I
    end.

  Local Lemma upfam_step (v : era_pins) (ps cs : list nat) (P a : nat)
      (I : list (bv 8)) (s : dst) :
    lm_wr_blk_t U ps cs s0 I P ->
    upend_tie_at cs s0 I (dst_content s) a ->
    uwild (ul I) = false ->
    union_links ug -∗
    era_pin (fgn_echo gf) (S gen_id) v -∗
    ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗ f0cw gf (S gen_id) s0 -∗
    f_typed (fgn_cl gf) s -∗
    UShPanic.prompt_step (upfam v P I s).
  Proof using Hcons.
    intros Hw Htie Hnw. pose proof Htie as (Hlen & Hpos & Hok & Hterm & Hcont & Hc).
    pose proof (ucont_prompt_nopanic _ _ _ Hcont) as Hnp.
    pose proof Hw as [Hwb Ht].
    iIntros "#Hlk #Hpin #Hps #Hcs #HE #Hcw #Hty".
    rewrite /UShPanic.prompt_step. iIntros "!>" (p b Φ) "%Hb %Hp Hc HΦ".
    destruct p as [| [| p]]; [| | exfalso; lia].
    - (* '$': the block-first byte files the deed's alternative *)
      assert (Hb0 : b = u_prompt !!! 0%nat)
        by (rewrite EchoLinks.wr_prompt_head in Hb; by injection Hb).
      subst b. cbn [upfam]. iDestruct "Hc" as "[Htn Hd]".
      pose proof Hwb as (Hpin0 & Hr & Hn & HP).
      assert (Hne : I <> []) by exact (lm_wr_blk_nonnil U ps cs s0 I P Hwb).
      assert (Hhead : lm_cont U (lm_upto U cs s0 (bodies_of I) (nlines I - 1))
                        (lm_of U (bodies_of I !!! (nlines I - 1)%nat)) (lm_dec U a) !! 0%nat
                      = Some (u_prompt !!! 0%nat)).
      { change (lm_cont U (ust cs s0 I) (ul I) (lm_dec U a) !! 0%nat
                = Some (u_prompt !!! 0%nat)).
        rewrite Hcont. exact EchoLinks.wr_prompt_head. }
      iApply (union_write_link_blk ug Hcons (S gen_id) v P a (u_prompt !!! 0%nat) ps cs s0 I Φ
                Hnw Hne Hr ltac:(lia) Hpin0 HP Hok Hterm Hhead
                with "Hpin Htn Hps Hcs HE Hcw [HΦ Hd]").
      iIntros "Hres". iApply "HΦ". cbn [upfam].
      iDestruct "Hres" as "[(Htn' & _ & #Hcs' & _ & _) | #HT]"; last first.
      { iSplitL "";
          [ iApply (lk_lpr_taint FI (S gen_id) v I 1%nat with "HT")
          | iApply (ush_deed_taint ug r with "HT") ]. }
      iSplitL "Htn'".
      + (* the space owed, at the stage the '$' left *)
        rewrite (lk_lpr_1 FI). cbn [lk_sp_t union_link_inst_at gen_link_inst].
        rewrite /gwc_sp_t /gcur. cbn [gW gT union_params_at]. rewrite /f0w_at.
        iLeft. iExists ps, (cs ++ [a]), s0, (S P).
        iSplitR.
        { iPureIntro. split;
            [ exact (uwr_blk_dollar_at ps cs s0 I P a Hwb Hnp Hcont)
            | exact (lm_wr_tail_snoc U ps cs a Hnp Ht) ]. }
        iFrame "Htn' Hps Hcs' HE". iSplitL; [| by iPureIntro].
        rewrite /f0w /f0cw. iSplitR; [by iPureIntro | iExact "Hcw"].
      + (* the deed, DONE: the filed alternative is the deed's own *)
        rewrite /ush_done_at /ush_deed_at. iLeft. iExists (cs ++ [a]), s, v.
        iFrame "Hd Hty Hpin Hcs' %". iPureIntro.
        exact (udone_tie_of_pend cs s0 I _ a Htie).
    - (* ' ': the record's own step, the deed framed *)
      cbn [upfam]. iDestruct "Hc" as "[Hc Hd]".
      iApply (lk_lpr_step FI (S gen_id) v I 1%nat b Φ Hb Hp
                with "[] Hpin Hlk Hc [HΦ Hd]").
      { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
      iIntros "Hc". iApply "HΦ". cbn [upfam]. iFrame "Hc Hd".
  Qed.

  (* the PEND arm of the prompt call *)
  Local Lemma uksh_w_prompt_pend (N : uk_names Σ) (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
    union_links ug -∗ UCodeShK.shk_rodata (ukn_t N) -∗
    UkSh.ksh_w (PS := uprogSG_free) N (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd N) l vw ∗ (Wcl I 3%nat ∗ PEND I))
      (UserFd.ustd_at (ukn_fd N) l vw ∗ (Wcl I 2%nat ∗ DONE I)).
  Proof using Hcons.
    intros Hl2. iIntros "#Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd [Hc Hp]] Hrun Hcont".
    (* a tainted deed: the record's law, DONE := T *)
    rewrite {1}/ush_pend_at /ush_deed_at.
    iDestruct "Hp" as "[Hp | #HT]"; last first.
    { iDestruct (lk_lcred_blk_line FI (S gen_id) I with "Hc") as "Hc".
      iApply (uksh_w_prompt_taint N I l vw rb Hl2
                with "HT Hlk Hro [%] [%] [%] Hcode [$Hstd $Hc] Hrun Hcont");
        assumption. }
    iDestruct "Hp" as (cs' s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs' & %Hnw)".
    destruct Htie as (a & Htie).
    (* the console: the block owed at the round's stage, or the taint *)
    rewrite /uWcl.
    iDestruct (lk_lcred_blk_lend FI (S gen_id) I with "Hc") as (v) "[#Hpin Hl]".
    cbn [lk_pin lk_lend union_link_inst_at gen_link_inst]. rewrite /gwc_lend.
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iDestruct (uHcltaint ug s0 I 0%nat v with "Hpin HT") as "Hc0".
      iApply (uksh_w_prompt_taint N I l vw rb Hl2
                with "HT Hlk Hro [%] [%] [%] Hcode [$Hstd $Hc0] Hrun Hcont");
        assumption. }
    iDestruct "Hl" as (ps cs sw P) "(%Hw & Hcur)".
    iEval (rewrite /gcur; cbn [gW gT union_params_at]; rewrite /f0w_at) in "Hcur".
    iDestruct "Hcur" as "(Htn & #Hps & #Hcs & #HE & #[Hf0 %Hs])".
    subst sw.
    iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
    pose proof Hw as [(_ & _ & Hn & _) _].
    pose proof Htie as (Hlen & _).
    iDestruct (ucs_lb_agree_len v cs cs' ltac:(lia) with "Hcs Hcs'") as %<-.
    iAssert (f0cw gf (S gen_id) s0) as "#Hcw".
    { rewrite /f0w. iDestruct "Hf0" as "[_ Hf]". rewrite /f0cw. iExact "Hf". }
    iPoseProof (upfam_step v ps cs P a I s Hw Htie Hnw
                  with "Hlk Hpin Hps Hcs HE Hcw Hty") as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) N
              (upfam v P I s) l vw rb Hl2
              with "Hst Hro [%] [%] [%] Hcode [$Hstd Htn Hd] Hrun [Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | cbn [upfam]; iFrame "Htn Hd" | ].
    iIntros (h' ret) "[Hstd Hc] Hrun".
    iApply ("Hcont" $! h' ret with "[$Hstd Hc] Hrun").
    cbn [upfam]. iDestruct "Hc" as "[Hc Hd]". iFrame "Hd".
    rewrite /uWcl /lk_lcred. iExists v. iSplitR; [iExact "Hpin" | iExact "Hc"].
  Qed.

  (* THE PROMPT LAW, at the file family *)
  Lemma ush_prompt_law_f :
    ⊢ union_links ug -∗ UShKernel.sh_prompt_law (PS := uprogSG_free) Wcf.
  Proof using Hcons.
    iIntros "#Hlk".
    iPoseProof (UShPanic.sh_prompt_law_hold_line_at (PS := uprogSG_free) FI DONE
                  (ush_deed_nw ug r s0 udone_tie s0) with "[]") as "#Hpld".
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    rewrite /UShKernel.sh_prompt_law. iIntros "!>" (N) "#Hro".
    iDestruct ("Hpld" $! N with "Hro") as "#Hd". rewrite /UkSh.ush_prompt_law.
    iDestruct "Hd" as "#[Hdopen Hdclosed]". iModIntro. iSplitL "".
    - iIntros (I l vw) "%Hfd". pose proof Hfd as [rb Hl2].
      rewrite uWcf_0 uWcf_2.
      iApply (uksh_w_or N _ _ _ (UserFd.ustd_at (ukn_fd N) l vw)
                (Wcl I 0%nat ∗ DONE I)%I (Wcl I 3%nat ∗ PEND I)%I
                with "[] []").
      + iApply ("Hdopen" $! I l vw). by iPureIntro.
      + iApply (uksh_w_prompt_pend N I l vw rb Hl2 with "Hlk Hro").
    - iIntros (l vw) "%Hcl". iApply ("Hdclosed" $! l vw). by iPureIntro.
  Qed.

  (* =================================================================== *)
  (*  S4  THE PROMPT AT THE PIPELINE'S TWO SHAPES                         *)
  (* =================================================================== *)

  (* THE TERMINAL ROUND: the terminal writer's two further bytes *)
  Lemma uterm_prompt_step (I : list (bv 8)) :
    ⊢ UShPanic.prompt_step (fun p : nat => PT I (5 + p)%nat).
  Proof using Hcons.
    rewrite /UShPanic.prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hsh HΦ".
    rewrite /upterm_shape.
    iDestruct "Hsh" as (v γc γm dep i sw sR lR) "(%Hpp & #Hpin & #Hlb & Hfe & Hh)".
    destruct Hpp as (Hdtl & HlR & Ha & Hl & Hi & Hpos & Hfc).
    pose proof (alt_forkc_prompt p b Hb) as Hb5.
    assert (Hlt : (5 + p < length PipeDisc.alt_forkc)%nat)
      by exact (lookup_lt_Some _ _ _ Hb5).
    assert (Hhin : forall x, x ∈ heldN i sw -> x.1.1 ∈ wids (lcats lR)).
    { intros x Hx. rewrite /heldN elem_of_list_fmap in Hx.
      destruct Hx as (j & -> & Hj). apply elem_of_seq in Hj.
      cbn [fst]. apply wids_elem. lia. }
    iApply (pprompt_forkN_h (wids (lcats lR)) (wids_NoDup _) (ucl ug) Hcons
              (runN (files_of sR) lR) (pwc_blkU ug v I sR) (pwc_blkU_timeless ug v I sR)
              (ptkU ug v I) (ptkU_persistent ug v I) (pwitU I sR)
              (pipesV_HWIT U pview_unionU I sR lR HlR Hfc Ha Hl)
              termw (tokN (files_of sR) lR) dep Hdtl
              pnsN (S gen_id) γc γm (WSh i) PipeDisc.alt_forkc (5 + p)%nat b
              (heldN i sw) Φ
              ltac:(solve_ndisj) ltac:(apply wids_elem; lia) ltac:(lia) Hb5 Hhin
              (cstep_okVh_prompt U pview_unionU I sR lR HlR Ha i sw (5 + p)%nat
                 ltac:(lia) Hlt)
              with "[] Hfe Hh [HΦ]").
    { iApply (pblkU_ecl_holds ug v I sR (uwild_pv _ _ HlR)). }
    iIntros "Hfe Hh". iApply "HΦ".
    iExists v, γc, γm, dep, i, sw, sR, lR.
    iSplitR; [iPureIntro; split_and!; assumption |].
    rewrite (_ : (5 + S p)%nat = S (5 + p)); [| lia].
    by iFrame "Hpin Hlb Hfe Hh".
  Qed.

  Lemma uterm_prompt_arm (Np : uk_names Σ) (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    shk_rodata (ukn_t Np) -∗
    UkSh.ksh_w (PS := uprogSG_free) Np (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd Np) l vw ∗ PT I 5%nat)
      (UserFd.ustd_at (ukn_fd Np) l vw ∗ PT I 7%nat).
  Proof using Hcons.
    intros Hl2. iIntros "#Hro".
    iPoseProof (uterm_prompt_step I) as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
              (fun p : nat => PT I (5 + p)%nat) l vw rb Hl2
              with "Hst Hro").
  Qed.

  (* THE COMMITTED ROUND: its first byte files the family's merged block
     through the record's N-writer arm and turns the deed's PRE tie into
     DONE (a pipeline's step is the identity); its second is the record's
     space *)
  Definition udone_fam (I : list (bv 8)) (p : nat) : iProp Σ :=
    match p with
    | O => (PD I ∗ DPRE I ∗ f0cw gf (S gen_id) s0)%I
    | S _ => (Wcl I p ∗ DONE I)%I
    end.

  Lemma udone_prompt_step (I : list (bv 8)) :
    ⊢ UShPanic.prompt_step (udone_fam I).
  Proof using Hcons.
    rewrite /UShPanic.prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hsh HΦ".
    assert (Hbt : b = u_prompt !!! p)
      by (symmetry; exact (list_lookup_total_correct u_prompt p b Hb)).
    iAssert (union_links ug) as "#Hlk"; [by iApply (union_links_holds ug Hcons) |].
    destruct p as [| [| p]]; [| | exfalso; lia].
    - (* the '$': file, then the N-writer arm *)
      cbn [udone_fam]. iDestruct "Hsh" as "(Hsh & Hdp & #Hcw)".
      rewrite /updone_shape.
      iDestruct "Hsh" as (v γc γm dep sR lR) "(%Hpp & #Hpin & #Hlb & #Hinv & Hall)".
      destruct Hpp as (Hdtl & HlR & Ha & Hl & Hfc).
      iDestruct (big_sepL_exist_fun [] _ _ (wids_NoDup _) with "Hall") as (sw) "Hall".
      iDestruct (big_sepL_sep with "Hall") as "[Hc Hrest]".
      iDestruct (big_sepL_sep with "Hrest") as "[Hm Hterm]".
      iDestruct (big_sepL_pure_1 with "Hterm") as %Hterm.
      rewrite /out_link. iIntros (o H) "#Hlbo Hres".
      iMod (pipesV_file (ugn_pipe ug) U pview_unionU (ucparams ug) v I sR lR HlR Hfc Ha Hl
              (⊤ ∖ ↑uartN Uart0) pnsN (S gen_id) γc γm termw (tokN (files_of sR) lR)
              dep Hdtl sw ltac:(solve_ndisj)
              ltac:(intros w Hw; apply elem_of_list_lookup in Hw as [j Hj];
                    exact (Hterm j w Hj))
              with "Hinv [Hc Hm]") as (pre) "[HPW %Hbl]".
      { iApply big_sepL_sep. iFrame "Hc Hm". }
      iPoseProof (union_X_dollar_at ug s0 (S gen_id) v I b Φ Hbt
                    with "Hpin Hlk [HPW] [HΦ Hdp]") as "Hol".
      { rewrite /union_X_at /union_X. iSplitL; [| iExact "Hcw"].
        iSplitR; [done |]. iExists sR, lR, pre.
        iSplitR; [iPureIntro; split_and!; [exact HlR | exact Ha | exact Hbl] |].
        iExact "HPW". }
      { iIntros "Hsp". iApply "HΦ". cbn [udone_fam].
        rewrite {1}/gwc_sp_t. iDestruct "Hsp" as "[Hx | #HT]"; last first.
        { iSplitL "".
          - rewrite /uWcl /lk_lcred. iExists v. iSplitR; [iExact "Hpin" |].
            iApply (lk_lpr_taint FI (S gen_id) v I 1%nat with "HT").
          - iApply (ush_deed_taint ug r with "HT"). }
        iDestruct "Hx" as (ps cs'' s' P') "[%Hw Hcur]".
        rewrite /gcur. iDestruct "Hcur" as "(Htn & #Hps & #Hcs & #HE & #HW)".
        (* the credential back, at the record's space *)
        iAssert (Wcl I 1%nat) with "[Htn]" as "Hwc".
        { rewrite /uWcl /lk_lcred. iExists v. iSplitR; [iExact "Hpin" |].
          rewrite (lk_lpr_1 FI). cbn [lk_sp_t union_link_inst_at gen_link_inst].
          rewrite /gwc_sp_t. iLeft. iExists ps, cs'', s', P'.
          iSplitR; [by iPureIntro |]. rewrite /gcur. iFrame "Htn Hps Hcs HE HW". }
        iFrame "Hwc".
        (* the deed: its PRE tie, the filed list one longer, the pipeline's
           identity step *)
        rewrite /ush_deed_at.
        iDestruct "Hdp" as "[Hdp | #HT]"; last first.
        { iApply (ush_deed_taint ug r with "HT"). }
        iDestruct "Hdp" as (cs s v') "(Hd & %Htie & #Hty & #Hpin' & #Hcs' & %Hnw)".
        iDestruct (era_pin_agree (fgn_echo gf) (S gen_id) v v' with "Hpin Hpin'") as %<-.
        destruct Hw as [[(_ & _ & Hn & _ & _) _] _].
        pose proof Htie as [Hlen _].
        iDestruct (ucs_lb_prefix_len v cs'' cs ltac:(lia) with "Hcs Hcs'") as %Hpre.
        rewrite /ush_done_at /ush_deed_at. iLeft. iExists cs'', s, v.
        iFrame "Hd Hty Hpin Hcs %". iPureIntro.
        apply (udone_tie_of_pre_prefix cs'' cs s0 I _ Htie ltac:(lia) Hpre).
        intros _.
        assert (HlR' : uv_line (lineV U I) = Some lR) by exact HlR.
        destruct (uv_line_some _ _ HlR') as (p0 & n0 & Hul & _).
        change (lm_step U (ust cs s0 I) (lineV U I) (lm_at U cs'' (nlines I - 1)%nat)
                = ust cs s0 I).
        rewrite Hul. apply ustep_pipe. }
      rewrite /out_link. iApply ("Hol" $! o H with "Hlbo Hres").
    - (* the space: the record's own step, the deed framed *)
      cbn [udone_fam]. iDestruct "Hsh" as "[Hc Hd]".
      iDestruct (ush_deed_nw ug r s0 with "Hd") as "[#Hnw Hd]".
      rewrite /uWcl /lk_lcred. iDestruct "Hc" as (v) "[#Hpin Hc]".
      iApply (lk_lpr_step FI (S gen_id) v I 1%nat b Φ Hb Hp
                with "Hnw Hpin Hlk Hc [HΦ Hd]").
      iIntros "Hc". iApply "HΦ". cbn [udone_fam]. iFrame "Hd".
      rewrite /uWcl /lk_lcred. iExists v. iSplitR; [iExact "Hpin" | iExact "Hc"].
  Qed.

  Lemma udone_prompt_arm (Np : uk_names Σ) (I : list (bv 8))
      (l vw : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    shk_rodata (ukn_t Np) -∗
    UkSh.ksh_w (PS := uprogSG_free) Np (mword_of_int 2 : mword 64)
      (mword_of_int UkSh.sh_prompt_pv) 2%nat
      (UserFd.ustd_at (ukn_fd Np) l vw ∗ udone_fam I 0%nat)
      (UserFd.ustd_at (ukn_fd Np) l vw ∗ udone_fam I 2%nat).
  Proof using Hcons.
    intros Hl2. iIntros "#Hro".
    iPoseProof (udone_prompt_step I) as "#Hst".
    iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
              (udone_fam I) l vw rb Hl2 with "Hst Hro").
  Qed.

  (* =================================================================== *)
  (*  S5  THE PROMPT LAW AT THE WIDENED CREDENTIAL                        *)
  (* =================================================================== *)
  Lemma ush_prompt_law_u :
    ⊢ union_links ug -∗ UShKernel.sh_prompt_law (PS := uprogSG_free) Wcu.
  Proof using Hcons.
    iIntros "#Hlk".
    iPoseProof (ush_prompt_law_f with "Hlk") as "#Hpl0".
    rewrite /UShKernel.sh_prompt_law. iIntros "!>" (Np) "#Hro".
    iPoseProof ("Hpl0" $! Np with "Hro") as "#Hlaw".
    rewrite {1}/UkSh.ush_prompt_law.
    iDestruct "Hlaw" as "[#Hplaw #Hclaw]".
    rewrite /UkSh.ush_prompt_law. iModIntro. iSplitR "".
    - iIntros (I l vw) "%Hfd2". destruct Hfd2 as [rb Hl2].
      iPoseProof (uterm_prompt_arm Np I l vw rb Hl2 with "Hro") as "Hta".
      iPoseProof (udone_prompt_arm Np I l vw rb Hl2 with "Hro") as "Hda".
      iIntros (h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
      rewrite {1}/uWcu.
      iDestruct "Hc" as "[Hc | [[_ Hsh] | [[_ Hsh] | #Hw]]]".
      + iApply ("Hplaw" $! I l vw with "[%] [%] [%] [%] Hcode [$Hstd $Hc] Hrun [Hcont]");
          [ by exists rb | exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (uWcu_of ug r s0 PT PD I 2%nat with "Hw").
      + iApply ("Hta" $! h m avail with "[%] [%] [%] Hcode [$Hstd Hsh] Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | | ].
        { rewrite Nat.add_0_r. iExact "Hsh". }
        iIntros (h' ret) "[Hstd Hsh'] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hsh'] Hrun").
        rewrite /uWcu. iRight. iLeft.
        iSplitR; [iPureIntro; lia |]. iExact "Hsh'".
      + iApply ("Hda" $! h m avail with "[%] [%] [%] Hcode [$Hstd Hsh] Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | | ].
        { cbn [udone_fam]. iExact "Hsh". }
        iIntros (h' ret) "[Hstd Hw] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd Hw] Hrun").
        iApply (uWcu_of ug r s0 PT PD I 2%nat). rewrite uWcf_2. iExact "Hw".
      + (* THE WILD ARM: "$ " through the era's licence (seccomp design
           10.5), the shape unmoved *)
        iAssert (UShPanic.prompt_step
                   (fun _ : nat => useccomp_shape ug I)) as "#Hst".
        { rewrite /UShPanic.prompt_step. iIntros "!>" (p b Φ) "_ _ #Hs HΦ".
          iDestruct "Hs" as "[Htok _]".
          iApply (union_write_link_wild ug Hcons (S gen_id) b Φ with "[Htok] [HΦ]");
            [by iApply (usecc_tok_of_at ug) | by iApply "HΦ"]. }
        iApply (UShPanic.ksh_w_of_link_prompt_fam (PS := uprogSG_free) Np
                  (fun _ : nat => useccomp_shape ug I) l vw rb Hl2
                  with "Hst Hro [%] [%] [%] Hcode [$Hstd $Hw] Hrun [Hcont]");
          [ exact Ha0 | exact Ha1 | exact Ha2 | ].
        iIntros (h' ret) "[Hstd _] Hrun".
        iApply ("Hcont" $! h' ret with "[$Hstd] Hrun").
        iApply (uWcu_wild ug r s0 PT PD I 2%nat with "Hw").
    - iExact "Hclaw".
  Qed.
End UShURoundLaws.

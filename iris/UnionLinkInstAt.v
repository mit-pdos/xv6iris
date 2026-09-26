(* ===================================================================== *)
(*  UnionLinkInstAt.v -- THE UNION LINK RECORD AT A NAMED BOOT STATE      *)
(*  (cut C9f1; design: claude-notes/design/union.md section 3, 'The       *)
(*  credential the main loop carries').                                    *)
(*                                                                        *)
(*  [UnionLinkInst.union_link_inst] with the writer's witness pinned to   *)
(*  the era's boot state [s0] -- [FileLinkGen.f0w_at] -- and the head at  *)
(*  that state -- [FileLinkGen.fhead_at]: RULING H' of the file round     *)
(*  ([FileLinkGen.file_link_gen_at]), at the union model.  The shell's    *)
(*  round names [s0] and ties the deed to it by a SHARED INDEX, so every  *)
(*  block the record hands back is at [s0] structurally.                   *)
(*                                                                        *)
(*  The one field that is not [file_link_gen_at]'s shape is the N-writer  *)
(*  arm: [union_X_at s0] is [UnionLinkInst.union_X] beside a witness of   *)
(*  the era's boot state [f0cw k s0], which is what turns the filing      *)
(*  link's returned witness (at SOME boot state) into the record's (at    *)
(*  [s0]).                                                                *)
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
Require Import FileLinksLine.
Require Import FileLinkGen.       (* [f0w_at], [fhead_at_boot], [fhead_at_cur] *)
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
Require Import UnionLinkInst.
Require Import GenLinksLine.
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation U := ulmG.

Section union_link_inst_at.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  (* =================================================================== *)
  (*  1.  THE PARAMETERS AT [s0]                                          *)
  (* =================================================================== *)
  Lemma uf0w_at_bwk (s0 : fstate) (k : nat) (s : fstate) :
    f0w_at gf s0 k s -∗ uf0bwk ug k s.
  Proof using . iIntros "[H _]". iApply (uf0w_bwk ug with "H"). Qed.

  Lemma uf0w_at_bwk0 (s0 : fstate) (k : nat) (s : fstate) :
    f0w_at gf s0 k s -∗ uf0bwk ug (S gen_id) s.
  Proof using . iIntros "[H _]". iApply (uf0w_bwk0 ug with "H"). Qed.

  Definition union_params_at (s0 : fstate) : gen_params U :=
    MkGP U ulmG_laws ulmG_hooks
      (uT ug) _ _
      (upin ug) _ _ (upin_agree ug)
      (f0w_at gf s0) _ _
      (uf0bwk ug) _ _ (S gen_id) (uf0w_at_bwk s0) (uf0w_at_bwk0 s0) (uf0bwk_agree ug)
      (fhead_at gf s0) _ (fhead_at_cur gf s0) (fhead_at_inp gf s0).

  Lemma union_params_at_T (s0 : fstate) : gT (union_params_at s0) = uT ug.
  Proof using . reflexivity. Qed.
  Lemma union_params_at_PIN (s0 : fstate) : gPIN (union_params_at s0) = upin ug.
  Proof using . reflexivity. Qed.
  Lemma union_params_at_W (s0 : fstate) : gW (union_params_at s0) = f0w_at gf s0.
  Proof using . reflexivity. Qed.

  (* the links entail the interface at [s0] ([UnionLinkInst.union_links_gl]'s
     proof, at the witness pinned to [s0]) *)
  Lemma union_links_gl_at (s0 : fstate) : union_links ug -∗ glinks U (union_params_at s0).
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /glinks /gl_w /gl_blk /gl_pro /gl_head /gl_taint.
    cbn [gT gPIN gW gH union_params_at].
    iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
    - iIntros "!>" (k v P0 b ps0 cs0 s0' I0 Φ)
        "%H1 %H2 %H3 [#Hpin _] #Hw Ht #Hps #Hcs #HE HΦ".
      iApply (union_write_link ug Hc k v P0 b ps0 cs0 s0' I0 Φ H1 H2 H3
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply f0w_at_cw |].
      iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | iRight; by iLeft].
    - iIntros "!>" (k v P0 a b ps0 cs0 s0' I0 Φ)
        "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 [#Hpin %Hk] #Hw Ht #Hps #Hcs #HE HΦ".
      rewrite /lm_abs /lm_line_at in H6 H8.
      iApply (union_write_link_blk ug Hc k v P0 a b ps0 cs0 s0' I0 Φ H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply f0w_at_cw |].
      iIntros "[[(Ht & Hps' & Hcs' & HE' & _) | #HT] | (#Htok & _ & _)]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | iRight; by iLeft |].
      iRight. iRight. subst k. iExact "Htok".
    - iIntros "!>" (k v P0 a b ps0 cs0 s0' I0 Φ)
        "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 [#Hpin _] #Hw Ht #Hps #Hcs #HE HΦ".
      iApply (union_write_link_pro ug Hc k v P0 a b ps0 cs0 s0' I0 Φ
                H1 H2 H3 H4 H5 H6 H7 H8
                with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply f0w_at_cw |].
      iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
        [iLeft; by iFrame "Ht Hps' Hcs' HE'" | iRight; by iLeft].
    - iIntros "!>" (k v I a b Φ) "%H1 %H2 [#Hpin _] Hh HΦ".
      iDestruct (fhead_at_boot gf s0 with "Hh")
        as "(Ht & #Hps & #Hcs & #HE & %s1 & %Hok & Hbt & Hwb)".
      iApply (union_write_link_first ug Hc k v a b s1 Φ Hok H1 H2
                with "Hpin Ht Hps Hcs HE Hbt [HΦ Hwb]").
      iIntros "[(Ht & Hps' & Hcs' & HE' & Hw) | #HT]"; iApply "HΦ"; [| iRight; by iLeft].
      iLeft. iExists s1. iFrame "Ht Hps' Hcs' HE'". by iApply "Hwb".
    - iIntros "!>" (k v b Φ) "[_ %Hk] #HT HΦ". rewrite /uT.
      iDestruct "HT" as "[#HU | #Htok]".
      + iApply (union_write_link_taint ug Hc with "HU"). iIntros "_". iApply "HΦ". by iLeft.
      + subst k. iApply (union_write_link_wild ug Hc with "Htok"). iApply "HΦ". by iRight.
  Qed.

  Lemma union_links_gl_w_at (s0 : fstate) : union_links ug -∗ gl_w U (union_params_at s0).
  Proof using .
    iIntros "Hlk". iDestruct (union_links_gl_at s0 with "Hlk") as "(H & _)". iExact "H".
  Qed.
  Lemma union_links_gl_blk_at (s0 : fstate) : union_links ug -∗ gl_blk U (union_params_at s0).
  Proof using .
    iIntros "Hlk". iDestruct (union_links_gl_at s0 with "Hlk") as "(_ & H & _)". iExact "H".
  Qed.
  (* the taint's byte at the era's own number, for a device at it *)
  Lemma union_links_gl_taint_at (s0 : fstate) :
    union_links ug -∗ gl_taint_at U (union_params_at s0) (S gen_id).
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /gl_taint_at. cbn [gT union_params_at].
    iIntros "!>" (b Φ) "#HT HΦ". rewrite /uT.
    iDestruct "HT" as "[#HU | #Htok]".
    - iApply (union_write_link_taint ug Hc with "HU"). iIntros "_". iApply "HΦ". by iLeft.
    - iApply (union_write_link_wild ug Hc with "Htok"). iApply "HΦ". by iRight.
  Qed.

  (* =================================================================== *)
  (*  2.  THE TURN AND THE RESIDUE                                        *)
  (* =================================================================== *)
  Lemma uturn0_at (s0 : fstate) (k : nat) :
    fturn_pre_at gf s0 k -∗
    (∃ v : era_pins, upin ug k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, upin ug k v ∗ gwc_ban U (union_params_at s0) k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre_at /FileOut.fturn_core.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; iFrame "Hpin Hdl HE"; by iPureIntro |].
    iExists v. iSplitR; [iFrame "Hpin"; by iPureIntro |]. rewrite /gwc_ban. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /gH /union_params_at /fhead_at.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  (* the residue is the unindexed record's: the reader's witness is the
     same at both parameter records *)
  Lemma urresw_res_at (s0 : fstate) (v : era_pins) (I : list (bv 8)) :
    urresw ug v I -∗ gwc_rres U (union_params_at s0) v I.
  Proof using . rewrite /urresw /gwc_rres. iIntros "[$ _]". Qed.

  (* =================================================================== *)
  (*  3.  THE N-WRITER ARM AT [s0]                                        *)
  (* =================================================================== *)
  Definition union_X_at (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      : iProp Σ :=
    (union_X ug k v I ∗ f0cw gf k s0)%I.

  Global Instance union_X_at_timeless s0 k v I : Timeless (union_X_at s0 k v I).
  Proof using .
    rewrite /union_X_at. apply bi.sep_timeless; [apply union_X_timeless | apply _].
  Qed.

  Lemma union_X_dollar_at (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    upin ug k v -∗ union_links ug -∗ union_X_at s0 k v I -∗
    (gwc_sp_t U (union_params_at s0) k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk [Hx #Hw0] HΦ".
    iApply (union_X_dollar ug k v I b Φ Hb with "Hpin Hlk Hx").
    iIntros "Hsp". iApply "HΦ". rewrite /gwc_sp_t.
    iDestruct "Hsp" as "[Hx | #HT]"; [| by iRight].
    iDestruct "Hx" as (ps cs s P) "[%Hw Hc]". iLeft. iExists ps, cs, s, P.
    iSplitR; [by iPureIntro |]. rewrite /gcur.
    iDestruct "Hc" as "(Htn & Hps & Hcs & HE & #HW)". iFrame "Htn Hps Hcs HE".
    cbn [gW union_params union_params_at]. rewrite /f0w_at.
    iAssert (⌜s = s0⌝)%I as %->.
    { rewrite /f0w /f0cw. iDestruct "HW" as "[_ HW]".
      iDestruct "HW" as (vf) "[#Hvf #Hlb]". iDestruct "Hw0" as (vf') "[#Hvf' #Hlb']".
      iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
      iApply (f0_lb_agree with "Hlb Hlb'"). }
    iSplitL; [iExact "HW" | done].
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECORD                                                      *)
  (* =================================================================== *)
  Definition union_link_inst_at (s0 : fstate) : LinkRec Σ :=
    gen_link_inst U (union_params_at s0) (union_X_at s0) (union_X_at_timeless s0)
      (union_links ug) (union_links_persistent ug) (union_links_gl_at s0)
      (union_X_dollar_at s0) (uread_ret ug) (uread_ret_res ug) (fturn_pre_at gf s0)
      (uturn0_at s0) (urresw ug) (urresw_persistent ug) (urresw_timeless ug)
      (urresw_res_at s0) (ualt_code (UR RFSilent)).

  Lemma union_at_T (s0 : fstate) : lk_T (union_link_inst_at s0) = uT ug.
  Proof using . reflexivity. Qed.
  Lemma union_at_pin (s0 : fstate) : lk_pin (union_link_inst_at s0) = upin ug.
  Proof using . reflexivity. Qed.
  Lemma union_at_links (s0 : fstate) : lk_links (union_link_inst_at s0) = union_links ug.
  Proof using . reflexivity. Qed.
  Lemma union_at_rres (s0 : fstate) : lk_rres (union_link_inst_at s0) = urresw ug.
  Proof using . reflexivity. Qed.
  Lemma union_at_lpr (s0 : fstate) :
    lk_lpr (union_link_inst_at s0) = gwc_lpr U (union_params_at s0) (union_X_at s0).
  Proof using . reflexivity. Qed.
End union_link_inst_at.

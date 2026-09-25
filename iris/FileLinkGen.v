(* ===================================================================== *)
(*  FileLinkGen.v -- THE FILE APPLICATION'S CONSOLE FAMILIES AS THE       *)
(*  GENERIC ONES (app-both milestone M2c, first cut).                    *)
(*                                                                       *)
(*  [GenLinksLine] at the file model: the taint is [file_taint], the pin  *)
(*  the era's echo-side pin, the writer's witness [f0w] (the boot-ledger  *)
(*  entry beside the era's file pin, at the console era), the reader's   *)
(*  the entry alone at an era, the head [fhead].  [FileLinks.file_links] *)
(*  entails the links interface (its laws carry the witness's two halves *)
(*  by name; the interface carries the witness), the read receipt        *)
(*  exposes the reader's residue, and the turn comes apart into the      *)
(*  generic banner-owed credential.  [file_link_gen] is then             *)
(*  [gen_link_inst] -- the record's ~60 laws at the file, from the       *)
(*  generic proofs.                                                      *)
(*                                                                       *)
(*  Section 0 holds the file's own pieces AT A NAMED BOOT STATE (they    *)
(*  were [FileLinksAt.v] until union cut C9h folded that file in): the   *)
(*  head [fhead_at] and the turn [fturn_pre_at] over [f0pre_at].         *)
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
Require Import EchoDisc.
Require Import FileState.
Require Import FileDisc.
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import FileHooks.         (* S0 of [FileLinksLine], moved *)
Require Import FileOutPure.
Require Import GenLinksGl.      (* [fhead_at], [f0pre_at], the indexed residue *)
Require Import LinkRec.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope list_scope.

Section file_link_gen.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.
  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  0a. THE ERA'S HEAD, AT A NAMED STATE (RULING H: the era's boot     *)
  (*      state hoisted out of the families' existential, so /init names *)
  (*      its deed's content once and reads the same name back)          *)
  (* =================================================================== *)
  Definition f0pre_at (s0 : fstate) : iProp Σ :=
    (⌜fstate_ok s0⌝ ∗ (f0_typed g s0 ∨ FT) ∗ f0bw g (S gen_id) s0)%I.

  Global Instance f0pre_at_timeless s0 : Timeless (f0pre_at s0).
  Proof using . rewrite /f0pre_at. apply _. Qed.
  Global Instance f0pre_at_persistent s0 : Persistent (f0pre_at s0).
  Proof using . rewrite /f0pre_at. apply _. Qed.

  (* THE DISPATCH, NOT [apply _].  The tree carries 455 [Timeless]
     instances, and because most of the definitions under them are
     transparent the hint net cannot discriminate: a search tries nearly
     all of them, measured ~1.3s per GOAL at this altitude -- which is
     what made a twelve-instance block 78s of an 86s file.
     Descend through the CONNECTIVES and name the leaf instance, so no
     search runs at all.  The dispatch must be SYNTACTIC: a [first [...]]
     spelling unifies up to delta and peels straight through a name that
     has its own instance.  [tl_leaf] is what a body bottoms out in;
     [tl_at] adds the head and the families below can reach it. *)
  Local Ltac tl_leaf :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_leaf
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_or _ _) => apply bi.or_timeless; [tl_leaf | tl_leaf]
    | |- Timeless (bi_pure _) => apply bi.pure_timeless
    | |- Timeless (f0pre_at _) => apply f0pre_at_timeless
    | |- Timeless (fcur _ _ _ _ _ _ _ _) => apply fcur_timeless
    | |- Timeless (f0w _ _ _) => apply f0w_timeless
    | |- Timeless (f0bw _ _ _) => apply f0bw_timeless
    | |- Timeless (f0_typed _ _) => apply f0_typed_timeless
    | |- Timeless (file_taint _) => apply file_taint_timeless
    | |- Timeless (turn _ _) => apply turn_timeless
    | |- Timeless (turn_lb _ _) => apply turn_lb_timeless
    | |- Timeless (ps_lb _ _) => apply ps_lb_timeless
    | |- Timeless (cs_lb _ _) => apply cs_lb_timeless
    | |- Timeless (inp_lb _ _) => apply inp_lb_timeless
    | |- Timeless (file_era_pin _ _ _) => apply file_era_pin_timeless
    | |- Persistent (bi_exist _) => apply bi.exist_persistent; intro; tl_leaf
    | |- Persistent (bi_sep _ _) => apply bi.sep_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_or _ _) => apply bi.or_persistent; [tl_leaf | tl_leaf]
    | |- Persistent (bi_pure _) => apply bi.pure_persistent
    | |- Persistent (turn_lb _ _) => apply turn_lb_persistent
    | |- Persistent (ps_lb _ _) => apply ps_lb_persistent
    | |- Persistent (cs_lb _ _) => apply cs_lb_persistent
    | |- Persistent (inp_lb _ _) => apply inp_lb_persistent
    | |- Persistent (f0w _ _ _) => apply f0w_persistent
    | |- Persistent (f0bw _ _ _) => apply f0bw_persistent
    | |- Persistent (f0_typed _ _) => apply f0_typed_persistent
    | |- Persistent (file_taint _) => apply file_taint_persistent
    | |- Persistent (file_era_pin _ _ _) => apply file_era_pin_persistent
    | |- _ => apply _
    end.

  Definition fhead_at (s0 : fstate) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    (⌜I = []⌝ ∗ ⌜k = S gen_id⌝ ∗ turn v 0%nat ∗ ps_lb v [] ∗ cs_lb v []
     ∗ inp_lb v [] ∗ (∃ vf : file_era, file_era_pin g k vf)
     ∗ f0pre_at s0)%I.

  Global Instance fhead_at_timeless s0 k v I : Timeless (fhead_at s0 k v I).
  Proof using . rewrite /fhead_at. tl_leaf. Qed.

  (* =================================================================== *)
  (*  0b. THE ERA'S TURN, AT THE NAMED STATE                              *)
  (* =================================================================== *)
  Definition fturn_pre_at (s0 : fstate) (k : nat) : iProp Σ :=
    (⌜k = S gen_id⌝ ∗ FileOut.fturn_core g k ∗ f0pre_at s0)%I.


  (* =================================================================== *)
  (*  1.  THE PARAMETERS                                                  *)
  (* =================================================================== *)

  (* the reader's witness at an era: the boot-ledger entry beside the
     era's file pin, with no index pin ([FileLinksLine.f0bw] is it at the
     console era with the pin) *)
  Definition f0bwk (k : nat) (s0 : fstate) : iProp Σ :=
    (∃ vf : file_era, file_era_pin g k vf ∗ f0_bl vf s0)%I.

  Global Instance f0bwk_persistent k s : Persistent (f0bwk k s).
  Proof using . rewrite /f0bwk. apply _. Qed.
  Global Instance f0bwk_timeless k s : Timeless (f0bwk k s).
  Proof using . rewrite /f0bwk. apply _. Qed.

  Lemma f0bwk_agree (k : nat) (s s' : fstate) :
    f0bwk k s -∗ f0bwk k s' -∗ ⌜s = s'⌝.
  Proof using .
    iIntros "H H'".
    iDestruct "H" as (vf) "[#Hp #Hl]". iDestruct "H'" as (vf') "[#Hp' #Hl']".
    iDestruct (file_era_pin_agree with "Hp Hp'") as %<-.
    iApply (f0_bl_agree with "Hl Hl'").
  Qed.

  Lemma f0w_bwk (k : nat) (s : fstate) : f0w g k s -∗ f0bwk k s.
  Proof using .
    iIntros "[_ H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0w_bwk0 (k : nat) (s : fstate) : f0w g k s -∗ f0bwk (S gen_id) s.
  Proof using .
    iIntros "[-> H]". iDestruct "H" as (vf) "[#Hp #Hl]".
    iExists vf. iFrame "Hp". iApply (f0_lb_bl with "Hl").
  Qed.

  Lemma f0bw_bwk (k : nat) (s : fstate) : f0bw g k s -∗ f0bwk k s.
  Proof using . iIntros "[_ H]". iExact "H". Qed.

  (* the head's two readings *)
  Lemma fhead_cur (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead g k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & _ & Htn & #Hps & #Hcs & #HE & _ & _)".
    iFrame "Htn Hps Hcs HE". by iPureIntro.
  Qed.

  Lemma fhead_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead g k v I -∗ fhead g k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using .
    rewrite /fhead. iIntros "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iSplitL "Htn Hvf Hpre".
    - iFrame "Htn Hps Hcs HE Hvf Hpre". iSplitR; by iPureIntro.
    - iSplitR; [by iPureIntro |]. subst I. iExact "HE".
  Qed.

  Definition file_params : gen_params file_lm :=
    MkGP file_lm file_lm_laws file_hooks
      FT _ _
      FPIN _ _ (era_pin_agree (fgn_echo g))
      (f0w g) _ _
      f0bwk _ _ (S gen_id) f0w_bwk f0w_bwk0 f0bwk_agree
      (fhead g) _ fhead_cur fhead_inp.

  (* =================================================================== *)
  (*  2.  THE LINKS ENTAIL THE INTERFACE                                  *)
  (* =================================================================== *)
  (* the claim's writer's witness, and the head's boot evidence, in the
     claim's words ([GenLinksGl.gcl_glinks]' two bridges) *)
  Lemma f0w_cw (k : nat) (s : fstate) : f0w g k s -∗ f0cw g k s.
  Proof using . iIntros "[_ H]". iExact "H". Qed.

  Lemma fhead_boot (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead g k v I -∗
      turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v []
      ∗ ∃ s0 : fstate, ⌜fstate_ok s0⌝ ∗ (f0boot g k s0 ∨ FT)
          ∗ (f0cw g k s0 -∗ f0w g k s0).
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

  (* the links are the claim's: the bundle is the record equation *)
  Lemma file_links_gl : file_links g -∗ glinks file_lm file_params.
  Proof using .
    iIntros "%Hc".
    iApply (gcl_glinks file_lm (file_cparams g) file_lm_byte_laws None (file_wa g) Hc file_params eq_refl eq_refl f0w_cw
              (or_introl I) fhead_boot).
  Qed.
  (* =================================================================== *)
  (*  3.  THE READ RECEIPT, THE TURN, THE RESIDUE                         *)
  (* =================================================================== *)
  Lemma fread_ret_res (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) :
    (0 < length ws)%nat ->
    fread_ret g k v n ws -∗
    FT ∨ (∃ (ps0 cs0 : list nat) (s0 : fstate) (J : list (bv 8)),
            ⌜length J = (n + length ws)%nat⌝ ∗ ⌜lm_rd_stage file_lm ps0 cs0 s0 J⌝
            ∗ inp_lb v J ∗ turn_lb v (length (lm_proc_before file_lm ps0 cs0 s0 J))
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ f0bwk k s0).
  Proof using .
    intros Hws. iIntros "Hr". rewrite /fread_ret.
    iDestruct "Hr" as "[[#HT _] | [_ Hfacts]]"; [by iLeft |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & %Hboots & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0 vf s0)
      "(#Hcs0 & #Hps0 & #Hvf & #Hf0 & %Hbd & #Htlb & %Hrs)".
    iRight. iExists ps0, cs0, s0, (snd <$> (dl ++ ws)).
    iFrame "Hinp Hps0 Hcs0".
    iSplitR; [iPureIntro; rewrite length_fmap length_app Hdl; reflexivity |].
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_f_lm _ _ _ _) Hrs) |].
    iSplitR; [rewrite -proc_before_f_lm; iExact "Htlb" |].
    iExists vf. iFrame "Hvf". iApply (f0_lb_bl with "Hf0").
  Qed.

  Lemma fturn0_gen (k : nat) :
    fturn_pre g k -∗
    (∃ v : era_pins, FPIN k v ∗ dl_cnt v (1/2) 0%nat ∗ inp_lb v [])
    ∗ (∃ v : era_pins, FPIN k v ∗ gwc_ban file_lm file_params k v [] 0%nat).
  Proof using .
    rewrite /fturn_pre /FileOut.fturn_core.
    iIntros "(%Hk & Ht & Hpre)".
    iDestruct "Ht" as (v vf) "(#Hpin & #Hvf & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [iExists v; by iFrame "Hpin Hdl HE" |].
    iExists v. iFrame "Hpin". rewrite /gwc_ban. iRight. iLeft.
    iSplitR; [by iPureIntro |]. rewrite /gH /file_params /fhead.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Htn Hps Hcs HE Hpre". iExists vf. iExact "Hvf".
  Qed.

  Lemma fwc_rresw_res (v : era_pins) (I : list (bv 8)) :
    fwc_rresw g v I -∗ gwc_rres file_lm file_params v I.
  Proof using .
    rewrite /fwc_rresw /fwc_rres /gwc_rres. iIntros "[Hr _]".
    iDestruct "Hr" as (ps0 cs0 s0) "(%Hrs & #Htlb & #Hps0 & #Hcs0 & #Hbw)".
    iExists ps0, cs0, s0. iFrame "Hps0 Hcs0".
    iSplitR; [iPureIntro; exact (proj1 (rd_stage_f_lm _ _ _ _) Hrs) |].
    iSplitR; [rewrite -proc_before_f_lm; iExact "Htlb" |].
    iApply (f0bw_bwk with "Hbw").
  Qed.

  (* =================================================================== *)
  (*  4.  THE RECORD                                                      *)
  (* =================================================================== *)
  (* no shape of the file application writes outside the block family *)
  Definition file_X (k : nat) (v : era_pins) (I : list (bv 8)) : iProp Σ := False%I.
  Lemma file_X_tl k v I : Timeless (file_X k v I).
  Proof using . rewrite /file_X. apply _. Qed.
  Lemma file_X_dollar (k : nat) (v : era_pins) (I : list (bv 8)) (b : bv 8)
      (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    FPIN k v -∗ file_links g -∗ file_X k v I -∗
    (gwc_sp_t file_lm file_params k v I -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using . intros _. iIntros "_ _ [] _". Qed.

  Definition file_link_gen : LinkRec Σ :=
    gen_link_inst file_lm file_params file_X file_X_tl (file_links g)
      (file_links_persistent g) file_links_gl file_X_dollar (fread_ret g)
      fread_ret_res (fturn_pre g) fturn0_gen (fwc_rresw g)
      (fwc_rresw_persistent g) (fwc_rresw_timeless g) fwc_rresw_res fnoc.
  (* =================================================================== *)
  (*  5.  THE SAME SECTION AT A NAMED BOOT STATE (RULING H')              *)
  (*                                                                     *)
  (*  No second set of families: the generic section instantiated at the *)
  (*  witness [f0w ∗ ⌜s = s0⌝] and the head [fhead_at s0] IS the record   *)
  (*  with [s0] shared by every field, and its laws come with it.        *)
  (* =================================================================== *)
  Definition f0w_at (s0 : fstate) (k : nat) (s : fstate) : iProp Σ :=
    (f0w g k s ∗ ⌜s = s0⌝)%I.

  Global Instance f0w_at_persistent s0 k s : Persistent (f0w_at s0 k s).
  Proof using . rewrite /f0w_at. apply _. Qed.
  Global Instance f0w_at_timeless s0 k s : Timeless (f0w_at s0 k s).
  Proof using . rewrite /f0w_at. apply _. Qed.

  Lemma f0w_at_bwk (s0 : fstate) (k : nat) (s : fstate) : f0w_at s0 k s -∗ f0bwk k s.
  Proof using . iIntros "[H _]". iApply (f0w_bwk with "H"). Qed.
  Lemma f0w_at_bwk0 (s0 : fstate) (k : nat) (s : fstate) :
    f0w_at s0 k s -∗ f0bwk (S gen_id) s.
  Proof using . iIntros "[H _]". iApply (f0w_bwk0 with "H"). Qed.

  Lemma fhead_at_cur (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead_at s0 k v I -∗ ⌜I = []⌝ ∗ turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v [].
  Proof using .
    rewrite /fhead_at. iIntros "(%HI & _ & Htn & #Hps & #Hcs & #HE & _ & _)".
    iFrame "Htn Hps Hcs HE". by iPureIntro.
  Qed.

  Lemma fhead_at_inp (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead_at s0 k v I -∗ fhead_at s0 k v I ∗ ⌜I = []⌝ ∗ inp_lb v [].
  Proof using .
    rewrite /fhead_at. iIntros "(%HI & %Hk & Htn & #Hps & #Hcs & #HE & Hvf & Hpre)".
    iSplitL "Htn Hvf Hpre".
    - iFrame "Htn Hps Hcs HE Hvf Hpre". iSplitR; by iPureIntro.
    - iSplitR; [by iPureIntro |]. subst I. iExact "HE".
  Qed.

  Definition file_params_at (s0 : fstate) : gen_params file_lm :=
    MkGP file_lm file_lm_laws file_hooks
      FT _ _
      FPIN _ _ (era_pin_agree (fgn_echo g))
      (f0w_at s0) _ _
      f0bwk _ _ (S gen_id) (f0w_at_bwk s0) (f0w_at_bwk0 s0) f0bwk_agree
      (fhead_at s0) _ (fhead_at_cur s0) (fhead_at_inp s0).

  Lemma f0w_at_cw (s0 : fstate) (k : nat) (s : fstate) :
    f0w_at s0 k s -∗ f0cw g k s.
  Proof using . iIntros "[[_ H] _]". iExact "H". Qed.

  Lemma fhead_at_boot (s0 : fstate) (k : nat) (v : era_pins) (I : list (bv 8)) :
    fhead_at s0 k v I -∗
      turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v []
      ∗ ∃ s1 : fstate, ⌜fstate_ok s1⌝ ∗ (f0boot g k s1 ∨ FT)
          ∗ (f0cw g k s1 -∗ f0w_at s0 k s1).
  Proof using .
    rewrite /fhead_at /f0pre_at.
    iIntros "(_ & -> & Htn & #Hps & #Hcs & #HE & Hvf & (%Hok & Hty & Hbw))".
    iDestruct "Hvf" as (vf) "#Hvf".
    iDestruct "Hbw" as "[_ Hbw]". iDestruct "Hbw" as (vf') "[#Hvf' #Hbl]".
    iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
    iFrame "Htn Hps Hcs HE". iExists s0. iSplitR; [by iPureIntro |].
    iSplitL "Hty".
    { iDestruct "Hty" as "[#Hty | #HT]"; [iLeft | by iRight].
      iExists vf. by iFrame "Hvf Hbl Hty". }
    iIntros "Hw". rewrite /f0w_at /f0w.
    iSplitL; [iSplitR; [by iPureIntro | iExact "Hw"] | by iPureIntro].
  Qed.

  (* =================================================================== *)
  (*  6.  THE CLOSED FAMILIES ARE THE EXISTENTIAL CLOSURES OF THE INDEXED *)
  (*      ONES (the packing lemmas the consumers spend)                   *)
  (* =================================================================== *)
  Local Notation GP := file_params.
  Local Notation GA := file_params_at.
End file_link_gen.

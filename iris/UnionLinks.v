(* ===================================================================== *)
(*  UnionLinks.v -- THE UNION APPLICATION'S CONSOLE LINKS (cut C9e';      *)
(*  design: claude-notes/design/union.md section 3).                      *)
(*                                                                        *)
(*  The links at the union claim [UnionOut.ucl] (three arms): the taint   *)
(*  route, the four single-writer writes (the era head filing the boot    *)
(*  state out of [f0boot]), the read link and its receipt, the close and  *)
(*  the byte, the FILING link of an N-writer round through the union's    *)
(*  view, and [App.al_echo] as a closed entailment at the union's tag.    *)
(*                                                                        *)
(*  THE BUNDLE a program holds is the record equation itself, as a pure   *)
(*  persistent fact ([union_links]), and the links are read off it where  *)
(*  they are spent, as at [FileLinks] and [PipesLinks].                    *)
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
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesLinksV.
Require Import GenOutWild.
Require Import PipeOutW.         (* [rd_retV]/[rd_retW], the wild licence *)
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionView.
Require Import UnionOutPure.
Require Import UnionOut.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
From stdpp Require Import list.
Local Open Scope list_scope.

Local Notation U := ulmG.
Local Notation UB := (ulm_byte_laws adm_u_g adm_s_on).

Section union_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation pg := (ugn_pipe ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.

  (* the record equations, as section parameters *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug).

  Lemma uchist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = ucl ug kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ---- the taint route ---- *)
  Lemma union_cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    UT -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
    iModIntro. iExists o. iSplitR; [iExact "Hlb" |]. iSplitR "HΦ"; [| iExact "HΦ"].
    rewrite !uchist_at0. by iApply (ucl_taint with "HT").
  Qed.

  Lemma union_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    UT -∗ (UT -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres".
    iModIntro. iExists o. iSplitR; [iExact "Hlb" |]. iSplitR "HΦ"; [| by iApply "HΦ"].
    rewrite !uchist_at0. by iApply (ucl_taint with "HT").
  Qed.

  (* ---- the WILD route: the era's wild token licenses its own era's
          process events (seccomp design 10.2) ---- *)
  Lemma union_write_link_wild (k : nat) (b : bv 8) (Φ : iProp Σ) :
    usecc_tok ug k -∗ Φ -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#Htok HΦ" (o H) "#Hlb Hres".
    iDestruct (ucl_wild_lic ug k with "Htok") as "#Hlic".
    rewrite !uchist_at0.
    iMod ("Hlic" $! (default [] o) H (ConsLog.EvOut b) with "[%] [%] Hres") as "Hres";
      [by left; exists b | done |].
    iModIntro. iExists o. rewrite uchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma union_read_link_wild (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    usecc_tok ug k -∗ Φ -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    iIntros "#Htok HΦ" (o H) "#Hlb Hres _ %Hev".
    iDestruct (ucl_wild_lic ug k with "Htok") as "#Hlic".
    rewrite !uchist_at0.
    iMod ("Hlic" $! (default [] o) H (ConsLog.EvRead ws) with "[%] [%] Hres") as "Hres";
      [by right; exists ws | done |].
    iModIntro. iExists o. rewrite uchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  (* (H) THE ERA'S HEAD WRITE: the first process byte files the boot
     state out of the deed's typed witness ([f0boot]) *)
  Lemma union_write_link_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : fstate) (Φ : iProp Σ) :
    fstate_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (f0boot gf k s0 ∨ UT) -∗
    (((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt HΦ" (o H) "#Hlb Hres".
    rewrite !uchist_at0.
    iMod (ucl_step_write_first ug k v a b s0 (default [] o) H Hok Halt Hhead
            with "Hpin Ht Hpslb Hcslb Hilb Hbt Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres". by iApply "HΦ".
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND *)
  Lemma union_write_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    lm_proc_stream U ps0 cs0 s0 I0 !! P = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ f0cw gf k s0) ∨ UT)
     -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !uchist_at0.
    iMod (ucl_step_write ug k v P b ps0 cs0 s0 I0 (default [] o) H Hn Hpin0 Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres". by iApply "HΦ".
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, filing the round's alternative, at a line
     that is not a [seccomp x] line (premise) *)
  Lemma union_write_link_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    uwild (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) = false ->
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    P = length (lm_proc_before U ps0 cs0 s0 I0) ->
    lm_ok U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) ->
    lm_term U (lm_dec U a) = false ->
    lm_cont U (lm_upto U cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of U (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec U a) !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hnw Hne Hr Hn Hpin0 HP Hok Hfk Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !uchist_at0.
    iMod (ucl_step_write_blk ug k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hnw Hne Hr Hn Hpin0 HP Hok Hfk Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres". by iApply "HΦ".
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE (the file's witness is strict) *)
  Lemma union_write_link_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic U (lm_at U cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin U ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx U cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream U ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    UPIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    f0cw gf k s0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ f0cw gf k s0) ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hr Hop Hn Hpin0 Hnd HP Halt Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !uchist_at0.
    iMod (ucl_step_write_pro ug k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hr Hop Hn Hpin0 Hnd HP Halt Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres". by iApply "HΦ".
  Qed.

  (* (R) THE READ LINK AND ITS RECEIPT: the window, the era's input at its
     far end, its discipline, and the writer's stage with the state's
     witness ([f0cw]: the era's file pin and the boot state's bound) --
     and, at a read that completes a [seccomp x] line, the era's wild
     token *)
  Definition uread_wild (I : list (bv 8)) (ws : list (list mobs * bv 8)) : Prop :=
    ws <> [] /\ I <> [] /\ rest_of I = [] /\ uwild (lm_line_at U I) = true.

  Global Instance uread_wild_dec I ws : Decision (uread_wild I ws).
  Proof using . rewrite /uread_wild. apply _. Qed.

  Definition uread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((UT ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜lm_E_disc U (seg_of (echoed pops))⌝
           ∗ ⌜forall x : list mobs * bv 8, x ∈ dl ++ ws -> obs_boots x.1 = k⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜lm_disc_input U (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (s0 : fstate),
                  cs_lb v cs0 ∗ ps_lb v ps0 ∗ f0cw gf k s0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (lm_proc_before U ps0 cs0 s0
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜lm_rd_stage U ps0 cs0 s0 (snd <$> (dl ++ ws))⌝)
           ∗ (⌜uread_wild (snd <$> (dl ++ ws)) ws⌝
              -∗ (usecc_tok_at ug k (snd <$> (dl ++ ws))
                  ∗ ⌜exists h0 : list mobs, list_basics.last ws = Some (h0, wl_nl)
                      /\ ins (open_seg h0) = snd <$> (dl ++ ws)
                      /\ obs_boots h0 = k⌝)
                 ∨ UT))%I.

  Lemma union_read_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    UPIN k v -∗ dl_cnt v (1/2) n -∗ (uread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
    rewrite !uchist_at0.
    iMod (ucl_step_read ug k v n (default [] o) H ws Hread
            with "Hpin Hdlr Hres") as "(Hres & Hret & Htok)".
    iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /uread_ret /rd_retV.
    iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte
                               & %Hboots & Hilb & %Hdi & Hrest)]"; [by iLeft |].
    iRight. iFrame "Hdlr".
    iExists (LogEntryDefs.ch_log H), (LogEntryDefs.ch_dl H).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [iPureIntro; exact Hboots |].
    iSplitL "Hilb"; [iExact "Hilb" |].
    iSplitR; [by iPureIntro |]. iFrame "Hrest".
    iIntros "%Hw". iApply "Htok". iPureIntro. exact Hw.
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma union_close_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite uchist_at0.
    iDestruct (ucl_close ug k (default [] o) H Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite uchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma union_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite uchist_at0.
    iMod (ucl_step_byte ug k (default [] o) H b Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite uchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma union_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using Hcons.
    iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ); cbn [cons_run].
    - by iApply union_close_link.
    - iSplit.
      + by iApply union_close_link.
      + iApply union_byte_link. by iApply "IH".
  Qed.

  (* (F) THE FILING LINK OF AN N-WRITER ROUND, through the union's view *)
  Lemma union_file_link (k : nat) (v : era_pins) (I : list (bv 8)) (sR : fstate)
      (lR : pline') (pre : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    pv_line pview_unionU (lineV U I) = Some lR -> adm_u_g lR = true ->
    line_blocks (files_of sR) lR pre -> b = u_prompt !!! 0%nat ->
    pwc_blkU ug v I sR k pre false -∗
    (((∃ (ps cs : list nat) (s0 : fstate) (P : nat),
         ⌜wr_blkV U ps cs s0 I P /\ lm_upto U cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
         ∗ f0cw gf k s0 ∗ turn v (S (P + length pre))%nat
         ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc pview_unionU lR (PLRun pre)]) ∗ inp_lb v I)
      ∨ UT) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros HlR Ha Hbl Hbv. iIntros "Hpw HΦ" (o H) "#Hlb Hres".
    rewrite !uchist_at0.
    destruct (decide (pre = [])) as [-> | Hne].
    - iMod (pwc_blkU_file_empty ug v I sR lR k (default [] o) H b HlR Hbv
              with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres".
      iApply "HΦ". iDestruct "Hret" as "[Hx | HT]"; [| by iRight].
      iLeft. iDestruct "Hx" as (ps cs s0 P) "(%Hw & HW & Htn & Hps & Hcs & HE)".
      iExists ps, cs, s0, P. cbn [length]. rewrite Nat.add_0_r.
      iFrame "HW Htn Hps Hcs HE". by iPureIntro.
    - iMod (pwc_blkU_file ug v I sR lR k (default [] o) H pre b HlR Ha Hbl Hne Hbv
              with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite uchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
  Qed.

  (* THE ECHO SHIFT -- [App.al_echo], a CLOSED entailment at the union's
     tag *)
  Lemma union_happ_echo
      (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = utag ug) :
    ⊢ ∀ (GEN : GenId) (XI : CurCtx),
        @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
  Proof using Hcons.
    iIntros (GEN XI).
    rewrite /SpecConsoleintr.cons_echo_shift Htag.
    iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
    iDestruct "Htg" as "(%Hsh & [%Hdisc | #HT] & _)"; last first.
    { iApply (union_cons_link_of_taint with "HT [HΦ]").
      by iApply union_cons_run. }
    iIntros (o H) "#Hlb Hres %Hok %Hev".
    rewrite uchist_at0.
    destruct (um_disc_open_seg U h Hsh Hdisc) as (s & _ & Hseg).
    iDestruct (ucl_open ug (S gen_id) (default [] o) H h c cs Hok Hev (proj1 Hseg) Hk
                 Hdisc Hsh with "Hres") as "Hres".
    iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
    rewrite uchist_at0.
    iFrame "Hlbh Hres".
    by iApply union_cons_run.
  Qed.
End union_links.

(* ===================================================================== *)
(*  THE BUNDLE: the record equation, as a pure persistent fact            *)
(* ===================================================================== *)
Section union_links_bundle.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation UPIN := (era_pin (fgn_echo gf)).
  Context `{HRg : !riscvGS Σ}.

  Definition union_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        UPIN k v -∗ dl_cnt v (1/2) n -∗
        (uread_ret ug k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition union_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        UT -∗ (UT -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition union_links : iProp Σ :=
    ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug⌝%I.

  Global Instance union_link_rd_persistent : Persistent union_link_rd | 0.
  Proof using . rewrite /union_link_rd. apply bi.intuitionistically_persistent. Qed.
  Global Instance union_link_rd_taint_persistent : Persistent union_link_rd_taint | 0.
  Proof using . rewrite /union_link_rd_taint. apply bi.intuitionistically_persistent. Qed.
  Global Instance union_links_persistent : Persistent union_links | 0.
  Proof using . rewrite /union_links. apply bi.pure_persistent. Qed.

  Lemma union_links_eq :
    union_links -∗ ⌜@riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug⌝.
  Proof using . rewrite /union_links. by iIntros "%Hc". Qed.

  Lemma union_links_rd : union_links -∗ union_link_rd.
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /union_link_rd. iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
    iApply (union_read_link ug Hc with "Hpin Hdl HΦ").
  Qed.

  Lemma union_links_rd_taint : union_links -∗ union_link_rd_taint.
  Proof using .
    iIntros "Hlk". iDestruct (union_links_eq with "Hlk") as %Hc.
    rewrite /union_link_rd_taint. iIntros "!>" (k ws Φ) "#HT HΦ".
    iApply (union_cons_link_of_taint ug Hc with "HT [HΦ]").
    by iApply "HΦ".
  Qed.

  Lemma union_links_holds
      (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug) :
    ⊢ union_links.
  Proof using . by iPureIntro. Qed.
End union_links_bundle.

(* THE BUNDLE IS OPAQUE TO THE INSTANCE SEARCH ([PipeLinks]'s measured
   rule): a [Persistent (union_links _)] goal is settled by its own
   instance and nothing else is tried. *)
#[global] Typeclasses Opaque union_links.

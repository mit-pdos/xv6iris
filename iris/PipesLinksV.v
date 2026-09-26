(* ===================================================================== *)
(*  PipesLinksV.v -- THE CONSOLE LINKS AT THE N-WRITER CLAIM OF ANY LINE  *)
(*  MODEL (cut C9e'; design: claude-notes/design/union.md section 3).     *)
(*                                                                        *)
(*  [GenLinks] is the link tier at [GenOut.gcl]; [PipesLinks] is it at    *)
(*  the pipeline application's [peclE].  This file is the tier ONCE at    *)
(*  [PipeOutN.peclV g M G sd WA] -- the generic claim between rounds, the *)
(*  open N-writer round while one is open -- for any model, witness and   *)
(*  view, so that an application whose claim is [peclV] (the union's      *)
(*  [UnionOut.ucl]) names its links by instantiation:                     *)
(*                                                                        *)
(*  1. THE ERA'S HEAD WRITE at the claim ([peclV_step_write_first]): the  *)
(*     generic claim's, the open round refuted (it has written a byte,   *)
(*     the head writer's turn is at zero).                                *)
(*  2. The links: the taint route, the four single-writer writes (the    *)
(*     open round refuted by [PipesOut.peclV_step_write] and twins), the  *)
(*     read with [GenLinks]' receipt, the close, the byte, the run, the   *)
(*     OPEN of the echo shift, and the FILING link of an N-writer round   *)
(*     through a pipeline view ([PipeOutN.pwc_blkV_file] /                *)
(*     [PipeOutNEv.pwc_blkV_file_empty]).                                 *)
(*  3. [GenLinksLine.glinks] from the claim ([peclV_glinks]), the twin of *)
(*     [GenLinksGl.gcl_glinks].                                           *)
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
Require Import GenOutHist.
Require Import GenOut.
Require Import PipeOut.            (* [pipe_gn], [pext] *)
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesOut.
Require Import GenLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE ERA'S HEAD WRITE, AT THE CLAIM                                *)
(* ===================================================================== *)
Section peclV_first.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Context (M : lmodel) (G : gen_cparams M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation PCV := (peclV g M G sd WA).

  (* (H) THE ERA'S FIRST PROCESS BYTE files the boot state
     ([GenOut.gcl_step_write_first]); an open round has already written a
     byte, and the head writer's turn is at zero *)
  Lemma peclV_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    lm_st_ok M s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot WA k s0 ∨ T) -∗
    PCV k ho H ==∗
      PCV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ gcW G k s0) ∨ T).
  Proof using .
    intros Hok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt Hcl". rewrite !peclV_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iMod (gcl_step_write_first M G sd WA k v a b s0 ho H Hok Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb Hbt Hc") as "[Hc Hr]".
      iModIntro. iFrame "Hr". by iLeft.
    - iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre & Hne & _).
      assert (Hwne : (1 <= length (gs_w M so))%nat).
      { rewrite Hwpre. destruct pre; [by destruct (Hne eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP. exfalso. lia.
  Qed.
End peclV_first.

(* ===================================================================== *)
(*  2.  THE LINKS                                                         *)
(* ===================================================================== *)
Section peclV_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  (* the stream extension is the pipe's era ledger *)
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Context `{HRg : !riscvGS Σ}.
  (* the record equation: the console record's claim IS [peclV] *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g M G sd WA).

  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation W := (gcW G).
  Local Notation PCV := (peclV g M G sd WA).

  Lemma vchist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = PCV kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ---- the taint route ---- *)
  Lemma vcons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    T -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| iExact "HΦ"].
    rewrite !vchist_at0. by iApply (peclV_taint with "HT").
  Qed.

  Lemma vwrite_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| by iApply "HΦ"].
    rewrite !vchist_at0. by iApply (peclV_taint with "HT").
  Qed.

  (* (H) THE ERA'S FIRST PROCESS BYTE *)
  Lemma vwrite_link_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (Φ : iProp Σ) :
    lm_st_ok M s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot WA k s0 ∨ T) -∗
    (((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt HΦ" (o H) "#Hlb Hres".
    rewrite !vchist_at0.
    iMod (peclV_step_write_first g M G sd WA k v a b s0 (default [] o) H
            Hok Halt Hhead with "Hpin Ht Hpslb Hcslb Hilb Hbt Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND *)
  Lemma vwrite_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    W k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ W k s0) ∨ T)
     -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !vchist_at0.
    iMod (peclV_step_write g M G sd WA k v P b ps0 cs0 s0 I0 (default [] o) H
            Hn Hpin0 Hb with "Hpin Ht Hpslb Hcslb Hilb HW Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, which files the round's alternative *)
  Lemma vwrite_link_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec M a) ->
    lm_term M (lm_dec M a) = false ->
    lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec M a) !! 0%nat = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    W k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using B Hcons.
    intros Hne Hr Hn Hpin0 HP Hok Hfk Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !vchist_at0.
    iMod (peclV_step_write_blk g M G B sd WA k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hne Hr Hn Hpin0 HP Hok Hfk Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE *)
  Lemma vwrite_link_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    0 < P \/ gwa_strict WA \/ gwa_free WA ->
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic M (lm_at M cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream M ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    W k s0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hfr Hr Hop Hn Hpin0 Hnd HP Halt Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !vchist_at0.
    iMod (peclV_step_write_pro g M G sd WA k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hfr Hr Hop Hn Hpin0 Hnd HP Halt Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (R) THE READ LINK AND ITS RECEIPT ([GenLinks.gread_ret]'s shape) *)
  Definition vread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((T ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜lm_E_disc M (seg_of (echoed pops))⌝
           ∗ ⌜forall x : list mobs * bv 8, x ∈ dl ++ ws -> obs_boots x.1 = k⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜lm_disc_input M (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (s0 : lm_st M),
                  cs_lb v cs0 ∗ ps_lb v ps0 ∗ W k s0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (lm_proc_before M ps0 cs0 s0
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜lm_rd_stage M ps0 cs0 s0 (snd <$> (dl ++ ws))⌝))%I.

  Lemma vread_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    PIN k v -∗ dl_cnt v (1/2) n -∗ (vread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using B Hcons.
    iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
    rewrite !vchist_at0.
    iMod (peclV_step_read g M G B sd WA k v n (default [] o) H ws Hread
            with "Hpin Hdlr Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /vread_ret /rd_retV.
    iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte
                               & %Hboots & Hilb & %Hdi & Hrest)]"; [by iLeft |].
    iRight. iFrame "Hdlr".
    iExists (LogEntryDefs.ch_log H), (LogEntryDefs.ch_dl H).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [iPureIntro; exact Hboots |].
    iSplitL "Hilb"; [iExact "Hilb" |].
    iSplitR; [by iPureIntro |]. iExact "Hrest".
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma vclose_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite vchist_at0.
    iDestruct (peclV_close g M G sd WA k (default [] o) H Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite vchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma vbyte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using B Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite vchist_at0.
    iMod (peclV_step_byte g M G B sd WA (gcL G) k (default [] o) H b Hok Hev
            with "Hres") as "Hres".
    iModIntro. iExists o. rewrite vchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma vcons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using B Hcons.
    iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ); cbn [cons_run].
    - by iApply vclose_link.
    - iSplit.
      + by iApply vclose_link.
      + iApply vbyte_link. by iApply "IH".
  Qed.

  (* (F) THE FILING LINK OF AN N-WRITER ROUND, through a pipeline view:
     the prompt's first byte files the block the family handed back as
     the view's [PLRun pre] -- the empty block included *)
  Lemma vfile_link (V : pview M) (k : nat) (v : era_pins) (I : list (bv 8))
      (sR : lm_st M) (lR : pline') (pre : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    pv_line V (lineV M I) = Some lR -> pv_adm V lR = true ->
    line_blocks (pv_fc V sR) lR pre -> b = u_prompt !!! 0%nat ->
    pwc_blkV g M PIN W T v I sR k pre false -∗
    (((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
         ⌜wr_blkV M ps cs s0 I P /\ lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
         ∗ W k s0 ∗ turn v (S (P + length pre))%nat
         ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc V lR (PLRun pre)]) ∗ inp_lb v I)
      ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using B Hcons Hext.
    intros HlR Ha Hbl Hbv. iIntros "Hpw HΦ" (o H) "#Hlb Hres".
    rewrite !vchist_at0.
    destruct (decide (pre = [])) as [-> | Hne].
    - iMod (pwc_blkV_file_empty g M G B sd WA V v I sR lR k (default [] o) H b
              HlR Hbv with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
      iApply "HΦ". iDestruct "Hret" as "[Hx | HT]"; [| by iRight].
      iLeft. iDestruct "Hx" as (ps cs s0 P) "(%Hw & HW & Htn & Hps & Hcs & HE)".
      iExists ps, cs, s0, P. cbn [length]. rewrite Nat.add_0_r.
      iFrame "HW Htn Hps Hcs HE". by iPureIntro.
    - iMod (pwc_blkV_file g M G B sd WA Hext V v I sR lR k (default [] o) H pre b
              HlR Ha Hbl Hne Hbv with "Hpw Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite vchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
  Qed.

  (* ================================================================== *)
  (*  3.  THE LINKS INTERFACE, FROM THE CLAIM                            *)
  (*                                                                     *)
  (*  [GenLinksGl.gcl_glinks] at [peclV]: link parameters [P] whose taint *)
  (*  and pin are the claim's, whose writer's witness gives the claim's,  *)
  (*  and whose head hands the era's first writer the boot evidence.     *)
  (* ================================================================== *)
  Section glinks_of_peclV.
    Context (P : gen_params M).
    Context (HPT : gT P = T) (HPIN : gPIN P = PIN).
    Context (HW : forall k s, gW P k s -∗ W k s).
    Context (Hsf : gwa_strict WA \/ gwa_free WA).
    Context (Hhd : forall k v I, gH P k v I -∗
               turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v []
               ∗ ∃ s0 : lm_st M, ⌜lm_st_ok M s0⌝ ∗ (gwa_boot WA k s0 ∨ T)
                   ∗ (W k s0 -∗ gW P k s0)).

    Lemma peclV_glinks : ⊢ glinks M P.
    Proof using B HPIN HPT HW Hcons Hhd Hsf.
      rewrite /glinks /gl_w /gl_blk /gl_pro /gl_head /gl_taint HPT HPIN.
      iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
      - iIntros "!>" (k v P0 b ps0 cs0 s0 I0 Φ)
          "%H1 %H2 %H3 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        iApply (vwrite_link k v P0 b ps0 cs0 s0 I0 Φ H1 H2 H3
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
          "_ %H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        rewrite /lm_abs /lm_line_at in H6 H8.
        iApply (vwrite_link_blk k v P0 a b ps0 cs0 s0 I0 Φ H1 H2 H3 H4 H5 H6 H7 H8
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
          "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        iApply (vwrite_link_pro k v P0 a b ps0 cs0 s0 I0 Φ (or_intror Hsf)
                  H1 H2 H3 H4 H5 H6 H7 H8
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v I a b Φ) "%H1 %H2 #Hpin Hh HΦ".
        iDestruct (Hhd with "Hh") as "(Ht & #Hps & #Hcs & #HE & %s0 & %Hok & Hbt & Hwb)".
        iApply (vwrite_link_first k v a b s0 Φ Hok H1 H2
                  with "Hpin Ht Hps Hcs HE Hbt [HΦ Hwb]").
        iIntros "[(Ht & Hps' & Hcs' & HE' & Hw) | #HT]"; iApply "HΦ"; [| by iRight].
        iLeft. iExists s0. iFrame "Ht Hps' Hcs' HE'". by iApply "Hwb".
      - iIntros "!>" (k v b Φ) "_ #HT HΦ".
        iApply (vwrite_link_taint with "HT HΦ").
    Qed.
  End glinks_of_peclV.
End peclV_links.

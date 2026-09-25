(* ===================================================================== *)
(*  GenLinks.v -- THE CONSOLE LINKS, ONCE OVER THE GENERIC CLAIM         *)
(*  (app-both M3c, first cut).                                           *)
(*                                                                       *)
(*  [FileLinks] and [PipeLinks] wrap the claim's steps onto the kernel's  *)
(*  own console contracts ([WpUart.out_link], [WpUart.cons_link]): a     *)
(*  link opens nothing but the port invariant, finds the era's claim in  *)
(*  the console record ([riscv_cons_res], which the record equation      *)
(*  [Hcons] names), takes the step and hands the claim back.  With the   *)
(*  claim generic ([GenOut.gcl]) the wrapping is one proof per step: the *)
(*  taint links, the four writes (head, inside a block, a block's first  *)
(*  byte, a prologue round's), the read with its receipt [gread_ret],    *)
(*  the arm's close and byte, and a whole echo run.                      *)
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
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import EchoOut.
Require Import GenOut.
Require Import RiscvPtsto.
Require Import WpUart.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Section gen_links.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).
  Context `{HRg : !riscvGS Σ}.

  (* the record equation: the console record's claim IS the generic one *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = gcl M G sd A).

  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation W := (gcW G).

  Lemma gchist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = gcl M G sd A kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ---- the taint route: once the era is off the discipline every link of
          every run is free ---- *)
  Lemma gcons_link_of_taint (k : nat) (ev : ConsLog.cons_ev) (Φ : iProp Σ) :
    T -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| iExact "HΦ"].
    rewrite !gchist_at0 /gcl. by iLeft.
  Qed.

  Lemma gwrite_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| by iApply "HΦ"].
    rewrite !gchist_at0 /gcl. by iLeft.
  Qed.

  (* (H) THE ERA'S FIRST PROCESS BYTE, which files the boot state *)
  Lemma gwrite_link_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (Φ : iProp Σ) :
    lm_st_ok M s0 ->
    a < length pro_alts ->
    pro_alts !!! a !! 0 = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot A k s0 ∨ T) -∗
    (((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt HΦ" (o H) "#Hlb Hres".
    rewrite !gchist_at0.
    iMod (gcl_step_write_first M G sd A k v a b s0 (default [] o) H
            Hok Halt Hhead with "Hpin Ht Hpslb Hcslb Hilb Hbt Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite gchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W) A BYTE INSIDE A BLOCK *)
  Lemma gwrite_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    nlines I0 <= length cs0 ->
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
    rewrite !gchist_at0.
    iMod (gcl_step_write M G sd A k v P b ps0 cs0 s0 I0 (default [] o) H
            Hn Hpin0 Hb with "Hpin Ht Hpslb Hcslb Hilb HW Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite gchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, which files the round's alternative *)
  Lemma gwrite_link_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    nlines I0 <= S (length cs0) ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a) ->
    lm_term M (lm_dec M a) = false ->
    lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a) !! 0 = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    W k s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using B Hcons.
    intros Hne Hr Hn Hpin0 HP Hok Hfk Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !gchist_at0.
    iMod (gcl_step_write_blk M G B sd A k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hne Hr Hn Hpin0 HP Hok Hfk Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite gchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (P) A PROLOGUE ROUND'S CHOICE BYTE *)
  Lemma gwrite_link_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (Φ : iProp Σ) :
    0 < P \/ gwa_strict A \/ gwa_free A ->
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic M (lm_at M cs0 (nlines I0 - 1)) = true) ->
    nlines I0 <= length cs0 ->
    lm_pro_pin M ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream M ps0 cs0 s0 I0) ->
    a < length pro_alts ->
    pro_alts !!! a !! 0 = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    W k s0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ W k s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hfr Hr Hop Hn Hpin0 Hnd HP Halt Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW HΦ" (o H) "#Hlb Hres".
    rewrite !gchist_at0.
    iMod (gcl_step_write_pro M G sd A k v P a b ps0 cs0 s0 I0 (default [] o) H
            Hfr Hr Hop Hn Hpin0 Hnd HP Halt Hb
            with "Hpin Ht Hpslb Hcslb Hilb HW Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite gchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (R) THE READ LINK AND ITS RECEIPT: beside the window, the era's input
     at the window's far end, its discipline and the stage the writer has
     reached, with the claim's choice list cut to the window *)
  Definition gread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((T ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)
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
                  ∗ ⌜nlines (snd <$> (dl ++ ws)) <= S (length cs0)⌝
                  ∗ turn_lb v (length (lm_proc_before M ps0 cs0 s0
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜lm_rd_stage M ps0 cs0 s0 (snd <$> (dl ++ ws))⌝))%I.

  Lemma gread_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    PIN k v -∗ dl_cnt v (1/2) n -∗ (gread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using B Hcons.
    iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
    rewrite !gchist_at0.
    iMod (gcl_step_read M G B sd A k v n (default [] o) H ws Hread
            with "Hpin Hdlr Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite gchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /gread_ret.
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
  Lemma gclose_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite gchist_at0.
    iDestruct (gcl_close M G sd A k (default [] o) H Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite gchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma gbyte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using B Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite gchist_at0.
    iMod (gcl_step_byte M G B sd A k (default [] o) H b Hok Hev with "Hres")
      as "Hres".
    iModIntro. iExists o. rewrite gchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma gcons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using B Hcons.
    iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ); cbn [cons_run].
    - by iApply gclose_link.
    - iSplit.
      + by iApply gclose_link.
      + iApply gbyte_link. by iApply "IH".
  Qed.
End gen_links.

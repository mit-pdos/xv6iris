(* ===================================================================== *)
(*  PipesOut.v -- THE N-STAGE CLAIM'S SINGLE-WRITER STEPS, AND THE        *)
(*  PIPELINE APPLICATION'S LEDGER AT ITS MODEL (cut C8).                  *)
(*                                                                       *)
(*  [PipeOutN.pecl'] -- the generic claim between rounds, [popenN] while *)
(*  a round of any number of writers is open -- answers the writes a     *)
(*  SINGLE writer makes (a prologue round's bytes, a block's bytes and   *)
(*  its first byte): out of the generic claim, and never while a round   *)
(*  is open, because such a round has already written a byte the writer's *)
(*  own turn is behind ([pecl'_step_write] / [_blk] / [_pro]).           *)
(*                                                                       *)
(*  At the application's model [PipesDisc.pipes_lmE] the claim is        *)
(*  [PipeOutNEv.peclE] and this file adds what the application record    *)
(*  needs beside it: the rx TAG ([ptagE]), the era's FOUNDING            *)
(*  ([era_full_splitE]) and the LEDGER ([pipesE_led]), whose taint       *)
(*  counter sits at [decide (lm_disc pipes_lmE h)] and whose conclusion  *)
(*  is [Forall (lm_good_out pipes_lmE tt)] over the cycles.              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
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
Require Import AppEcho.
Require Import PipeOut.            (* [pipe_gn], the byte ledger's ghosts *)
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.       (* [pipes_hooksE] *)
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipesLedPure.
Require Import RiscvPtsto.
Require Import WpUart.
(* stdpp's list names over the ones the Stdlib import above re-exports *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE SINGLE-WRITER STEPS, over any line model (cut C9c'), and at  *)
(*      the pipeline application's                                       *)
(* ===================================================================== *)
Section pipes_writes_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation PCV := (peclV g M G sd WA).

  (* (W) THE WRITE INSIDE A BLOCK OR A PROLOGUE ROUND.  An open round has
     already written its block's first byte, so the writer's byte -- one
     the stream owes BEFORE the input's end -- cannot be the open round's
     next one: the writer's input would have to be the whole echoed list,
     which ends at the open round's line. *)
  Lemma peclV_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    PCV k ho H ==∗
      PCV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gcW G k s0) ∨ T).
  Proof using .
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite !peclV_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iMod (gcl_step_write M G sd WA k v P b ps0 cs0 s0 I0 ho H Hn Hpin0 Hb
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]".
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & HW2) | HT]";
        [iLeft; by iFrame | by iRight].
    - iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
      iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
      assert (Hst' : gs_state M sd so = s0) by exact Hst.
      clear Hst. subst s0.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen)]. }
      destruct (lm_write_stage_byte M ps0 (gs_ps M so) cs0 (gs_cs M so)
                  (gs_state M sd so) (gs_E M so) (gs_w M so) I0 P b
                  Hpsp Hpin0 Hcsp Hn HI0 HP Hb) as [HlenE _].
      destruct Hopen as (_ & Hop & _).
      destruct (lm_blk_open_cs M sd so r pre Hop) as (Hq & Hrr & Hnn).
      pose proof (prefix_length _ _ Hcsp) as Hcl0.
      rewrite HlenE in Hq, Hrr, Hnn.
      pose proof (nlines_pos_of_rest_nil I0 Hnn Hrr) as Hpos0.
      exfalso. lia.
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE, which FILES the alternative:
     a single-writer round (an echo line's).  An open round has already
     written a byte of the block this writer would open. *)
  Lemma peclV_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
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
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    PCV k ho H ==∗
      PCV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0 ∗ gcW G k s0) ∨ T).
  Proof using B.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite !peclV_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iMod (gcl_step_write_blk M G B sd WA k v P a b ps0 cs0 s0 I0 ho H
              Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]".
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & HW2) | HT]";
        [iLeft; by iFrame | by iRight].
    - iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
      iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
      assert (Hst' : gs_state M sd so = s0) by exact Hst.
      clear Hst. subst s0.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen)]. }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _).
      assert (Hs2 : lm_proc_before M ps0 cs0 (gs_state M sd so) I0
                    = lm_proc_before M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0).
      { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so) (gs_state M sd so) I0
                 Hpsp Hcsp Hpin0).
        rewrite (ll_nlines_removelast I0 Hr0). lia. }
      pose proof (prefix_length _ _
        (lm_proc_before_prefix M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0
           (snd <$> gs_E M so) HI0)) as Hle2.
      assert (Hwne : (1 <= length (gs_w M so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP. rewrite HPeq Hs2 in HP.
      exfalso. lia.
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE.  It comes after
     the whole stream through [I0], which an open round's own bytes run
     past already. *)
  Lemma peclV_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    0 < P \/ gwa_strict WA \/ gwa_free WA ->
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic M (lm_at M cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream M ps0 cs0 s0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    PCV k ho CH ==∗
      PCV k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gcW G k s0) ∨ T).
  Proof using .
    intros HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite !peclV_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iMod (gcl_step_write_pro M G sd WA k v P a b ps0 cs0 s0 I0 ho CH
              HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]".
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & HW2) | HT]";
        [iLeft; by iFrame | by iRight].
    - iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen2)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
      iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
      assert (Hst' : gs_state M sd so = s0) by exact Hst.
      clear Hst. subst s0.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen2)]. }
      destruct Hopen2 as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _).
      destruct (lm_blk_open_cs M sd so r pre Hop) as (Hqq & Hrr & Hne0').
      assert (Hwne : (1 <= length (gs_w M so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP.
      destruct (decide ((snd <$> gs_E M so) = I0)) as [Heq | Hne2].
      + rewrite Heq in Hqq, Hrr, Hne0'.
        pose proof (nlines_pos_of_rest_nil I0 Hne0' Hrr) as Hpos0.
        pose proof (prefix_length _ _ Hcsp) as Hcl0.
        exfalso. lia.
      + pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0
                      (snd <$> gs_E M so) HI0
                      ltac:(intros Hq; apply Hne2; symmetry; exact Hq)) as Hpre2.
        apply prefix_length in Hpre2.
        pose proof (prefix_length _ _
          (lm_proc_stream_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so) (gs_state M sd so) I0
             Hpsp Hcsp Hpin0 Hdiv)) as Hle3.
        exfalso. lia.
  Qed.
End pipes_writes_v.

(* ===================================================================== *)
(*  2.  AT THE APPLICATION'S MODEL: THE TAG, THE FOUNDING, THE LEDGER     *)
(* ===================================================================== *)
Section pipes_led.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  (* the ledger's counter CASES on the discipline; nothing evaluates it *)
  Context `{Hdd : forall h : list mobs, Decision (lm_disc pipes_lmE h)}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Notation T := (echo_taint γ).
  Local Notation PME := pipes_lmE.

  (* THE RX TAG: the trace's shape and the discipline, or the taint *)
  Definition ptagE (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜lm_disc PME h⌝ ∨ T))%I.

  Global Instance ptagE_persistent h : Persistent (ptagE h).
  Proof using . rewrite /ptagE. apply _. Qed.
  Global Instance ptagE_timeless h : Timeless (ptagE h).
  Proof using . rewrite /ptagE. apply _. Qed.

  (* ================================================================= *)
  (*  THE LEDGER                                                        *)
  (* ================================================================= *)
  Definition pipesE_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1
       (if decide (lm_disc PME h) then 0%nat else 1%nat)
     ∗ pin_map γ h
     ∗ pera_map g h
     ∗ (⌜Forall (lm_good_out PME tt) (cycles_of h)⌝ ∨ T))%I.

  Global Instance pipesE_led_timeless h : Timeless (pipesE_led h).
  Proof using . rewrite /pipesE_led. apply _. Qed.
End pipes_led.

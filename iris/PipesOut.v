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

Section pipes_writes.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Notation T := (echo_taint γ).
  Context (fc : bytes -> option bytes) (adm : pline' -> bool).
  Context (Lw : lm_laws (pipes_lm fc adm)).
  Local Notation PM := (pipes_lm fc adm).
  Local Notation PB := (pipes_lm_byte_laws fc adm).
  Local Notation PC := (pecl' g fc adm Lw).
  Local Notation GP := (pipesN_cparams g fc adm Lw).
  Local Notation GA := (pipesN_wa g fc adm Lw).

  Lemma pipes_st_tt (so : gstage PM) : gs_state PM tt so = tt.
  Proof using. by destruct (gs_state PM tt so). Qed.

  (* (W) THE WRITE INSIDE A BLOCK OR A PROLOGUE ROUND.  An open round has
     already written its block's first byte, so the writer's byte -- one
     the stream owes BEFORE the input's end -- cannot be the open round's
     next one: the writer's input would have to be the whole echoed list,
     which ends at the open round's line. *)
  Lemma pecl'_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin PM ps0 cs0 I0 ->
    lm_proc_stream PM ps0 cs0 tt I0 !! P = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    PC k ho H ==∗
      PC k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hn Hpin0 Hb. iIntros "Hpin Ht Hpslb Hcslb Hilb Hcl".
    iMod (peclV_step_write g PM GP tt GA k v P b ps0 cs0 tt I0 ho H Hn Hpin0 Hb
            with "Hpin Ht Hpslb Hcslb Hilb [] Hcl") as "[Hc Hr]"; [done |].
    iModIntro. iSplitL "Hc"; [iExact "Hc" |].
    iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE, which FILES the alternative:
     a single-writer round (an echo line's).  An open round has already
     written a byte of the block this writer would open. *)
  Lemma pecl'_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin PM ps0 cs0 I0 ->
    P = length (lm_proc_before PM ps0 cs0 tt I0) ->
    lm_ok PM tt (lm_of PM (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec PM a) ->
    lm_term PM (lm_dec PM a) = false ->
    lm_cont PM (lm_upto PM cs0 tt (bodies_of I0) (nlines I0 - 1))
      (lm_of PM (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec PM a) !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    PC k ho H ==∗
      PC k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead.
    iIntros "Hpin Ht Hpslb Hcslb Hilb Hcl".
    iMod (peclV_step_write_blk g PM GP PB tt GA k v P a b ps0 cs0 tt I0 ho H
            Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead
            with "Hpin Ht Hpslb Hcslb Hilb [] Hcl") as "[Hc Hr]"; [done |].
    iModIntro. iSplitL "Hc"; [iExact "Hc" |].
    iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE.  It comes after
     the whole stream through [I0], which an open round's own bytes run
     past already. *)
  Lemma pecl'_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic PM (lm_at PM cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin PM ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx PM cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream PM ps0 cs0 tt I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    PC k ho CH ==∗
      PC k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "Hpin Ht Hpslb Hcslb Hilb Hcl".
    iMod (peclV_step_write_pro g PM GP tt GA k v P a b ps0 cs0 tt I0 ho CH
            (or_intror (or_intror I)) Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
            with "Hpin Ht Hpslb Hcslb Hilb [] Hcl") as "[Hc Hr]"; [done |].
    iModIntro. iSplitL "Hc"; [iExact "Hc" |].
    iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
  Qed.
End pipes_writes.

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
  Local Notation PBE := (pipes_lm_byte_laws (fun _ => None) adm_echo).

  (* THE RX TAG: the trace's shape and the discipline, or the taint *)
  Definition ptagE (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜lm_disc PME h⌝ ∨ T))%I.

  Global Instance ptagE_persistent h : Persistent (ptagE h).
  Proof using . rewrite /ptagE. apply _. Qed.
  Global Instance ptagE_timeless h : Timeless (ptagE h).
  Proof using . rewrite /ptagE. apply _. Qed.

  (* THE FOUNDING, as a resource split: the era's ghosts become the
     claim at the start of its era -- the generic claim at the empty
     stage, the byte ledger's current round at nothing -- and init's
     console credential *)
  Lemma era_full_splitE (k : nat) (v : era_pins) (w : pipe_era) (gb : gname) :
    era_pin γ k v -∗ pera_pin g k w -∗ blk_auth w [] -∗
    rblk_auth gb [] -∗ cur_half w 1 0%nat gb false -∗ era_full v -∗
      peclE g k [] (LogEntryDefs.MkCH [] [] [] None) ∗ pturn g k.
  Proof using .
    iIntros "#Hpin #Hpera Hblk Hrb Hcur1 (Ht & Hcs & Hps & HE & Hdl & Hdll)".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll Hblk Hcur1 Hrb".
    { rewrite /peclE pecl'_gen /gcl. iLeft. iRight.
      iExists v, (gstage0 (pipes_lm (fun _ => None) adm_echo)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st gstage0 LogEntryDefs.ch_dl length].
      iSplitR; [iExact "Hpin" |]. iSplitR; [done |].
      iSplitL "Hblk Hcur1 Hrb".
      { unfold pipesN_wa. cbn [gext]. rewrite /pext.
        iExists w, 0%nat, gb, [], false. iFrame "Hpera Hcur1 Hrb".
        rewrite (_ : lm_stream (pipes_lm (fun _ => None) adm_echo) tt _ = []); [iExact "Hblk" | reflexivity]. }
      rewrite (_ : lm_pcount (pipes_lm (fun _ => None) adm_echo) _ _ _ _ _ = 0%nat); [| reflexivity].
      iFrame "Ht1 Hcs Hps HE Hdl1 Hdll".
      iPureIntro.
      rewrite /gcl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (lm_out_pure_0 (pipes_lm (fun _ => None) adm_echo) tt k [] I).
      - exact (lm_cs_len_ok_0 (pipes_lm (fun _ => None) adm_echo)).
      - exact (lm_ps_len_ok_0 (pipes_lm (fun _ => None) adm_echo) tt).
      - exact (gin_pure_0 (pipes_lm (fun _ => None) adm_echo) k).
      - by rewrite /garm_era.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of fmap_nil. reflexivity.
      - exact (lm_dl_ok_0 (pipes_lm (fun _ => None) adm_echo)). }
    rewrite /pturn /eturn. iExists v. iFrame "Hpin Ht2 Hdl2 Hcslb Hpslb".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

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

  Lemma pipesE_st_ok : exists s, lm_st_ok PME s.
  Proof using. by exists tt. Qed.

  Lemma pipesE_led_init : pipe_cl_all g -∗ pipesE_led [].
  Proof using .
    rewrite /pipe_cl_all /echo_cl /pipesE_led /pin_map /pera_map.
    rewrite decide_True; [| exact (lm_disc_nil PME)].
    iIntros "[[Ht Hm] Hme]". iFrame "Ht".
    iSplitL "Hm".
    { iExists ∅. iFrame "Hm". iPureIntro. apply pin_dom_empty. }
    iSplitL "Hme".
    { iExists ∅. iFrame "Hme". iPureIntro. apply pin_dom_empty. }
    iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
  Qed.

  Lemma pipesE_led_pow (h : list mobs) (on : bool) :
    pipesE_led h ==∗
      pipesE_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else peclE g (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ pturn g (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hme & Hphi)". rewrite /pipesE_led.
    rewrite (decide_ext _ (lm_disc PME h) 0%nat 1%nat
               (lm_disc_power PME h on pipesE_st_ok)).
    iAssert (⌜Forall (lm_good_out PME tt)
               (cycles_of (h ++ [if on then ObsPowerOff else ObsPowerOn]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro. exact (lm_phi_step_power PME tt h on Hg). }
    destruct on.
    - iDestruct (pin_map_step γ h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iDestruct (pera_map_step g h ObsPowerOff eq_refl with "Hme") as "Hme".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hme Hphi".
    - iMod era_full_alloc as (v) "Hfull".
      iMod (pin_map_on γ h v with "Hpm") as "[Hpm #Hpin]".
      iMod blk_alloc as (w gb) "(Hblk & Hrb & Hcur1)".
      iMod (pera_map_on g h w with "Hme") as "[Hme #Hpera]".
      iDestruct (era_full_splitE (S (obs_boots h)) v w gb
                   with "Hpin Hpera Hblk Hrb Hcur1 Hfull") as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn"; [iFrame "Ht Hpm Hme Hphi" | iFrame "Hcl Hturn"].
  Qed.

  Lemma pipesE_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜i = Uart0 -> lm_good_out PME tt (open_seg h ++ [ObsUartOut i b])⌝) -∗
    pipesE_led h ==∗ pipesE_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Hcnt & Hpm & Hme & Hphi)".
    iDestruct (pin_map_step γ h (ObsUartOut i b) eq_refl with "Hpm") as "Hpm".
    iDestruct (pera_map_step g h (ObsUartOut i b) eq_refl with "Hme") as "Hme".
    rewrite /pipesE_led.
    rewrite (decide_ext _ (lm_disc PME h) 0%nat 1%nat (lm_disc_out PME h i b Hsh)).
    iModIntro. iFrame "Hcnt Hpm Hme".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. destruct i.
    - exact (lm_phi_step_cons PME tt h (ObsUartOut Uart0 b) Hsh eq_refl
               (Hgo eq_refl) Hg).
    - exact (lm_phi_step_io PME PBE pipes_hooksE tt h (ObsUartOut Uart1 b) Hsh eq_refl
               (obs_wire_out_other Uart1 b ltac:(discriminate)) Hg).
  Qed.

  Lemma pipesE_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    pipesE_led h ==∗
      pipesE_led (h ++ [ObsUartIn i b])
      ∗ (⌜lm_disc PME (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hme & Hphi)".
    iDestruct (pin_map_step γ h (ObsUartIn i b) eq_refl with "Hpm") as "Hpm".
    iDestruct (pera_map_step g h (ObsUartIn i b) eq_refl with "Hme") as "Hme".
    iAssert (⌜Forall (lm_good_out PME tt) (cycles_of (h ++ [ObsUartIn i b]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro.
      exact (lm_phi_step_io PME PBE pipes_hooksE tt h (ObsUartIn i b) Hsh eq_refl
               (obs_wire_in i b) Hg). }
    rewrite /pipesE_led.
    destruct (decide (lm_disc PME (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (lm_disc_in PME PBE h b Hsh Hd')
          | exact (proj1 (lm_disc_other PME h (ObsUartIn Uart1 b) eq_refl I Hsh) Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hme Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (lm_disc PME h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hme Hphi". iRight. iExact "Hlb".
  Qed.

  (* THE CONCLUSION'S read at the end of the run: [T] IS the counter's
     lower bound at 1 *)
  Lemma pipesE_led_phi (h : list mobs) :
    pipesE_led h -∗ ⌜lm_disc PME h -> Forall (lm_good_out PME tt) (cycles_of h)⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & [%Hg | HT'])".
    { iPureIntro. by intros _. }
    rewrite /echo_taint.
    iDestruct (mono_nat_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.
End pipes_led.

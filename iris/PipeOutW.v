(* ===================================================================== *)
(*  PipeOutW.v -- THE CLAIM'S TERMINAL ARM, OVER ANY LINE MODEL (seccomp  *)
(*  lane S2; design: claude-notes/design/seccomp.md section 10).          *)
(*                                                                        *)
(*  [PipeOutN.peclV] (the generic claim between rounds, the open         *)
(*  N-writer round while one is open) gains a THIRD ARM for the era in   *)
(*  which a WILD line ran ([GenOutWild.lm_wild]; at the union, the       *)
(*  [seccomp x] line):                                                    *)
(*                                                                        *)
(*    pwclV k ho H := T ∨ (PIN k v ∗ secc_flag v 0 ∗ peclV k ho H)        *)
(*                      ∨ wildV k ho H                                    *)
(*                                                                        *)
(*  1. THE FLAG AND THE TOKEN (10.1): the era's [ep_secc] mono_nat, whose *)
(*     whole authority the claim holds; the token [secc_tok k] is a lower *)
(*     bound at 1 and CARRIES THE FREEZE (the delivered input up to the  *)
(*     wild line and the frozen choice list).                             *)
(*  2. THE ARM [wildV]: the stage at the moment of the transition (the    *)
(*     frozen [cs], the delivered input all of the echoed one, nothing of *)
(*     the line's block written), the turn's authority at the stage's     *)
(*     cursor, and an arbitrary tail [u] of the wire after the echoed     *)
(*     line.  The log is FROZEN: an open is refuted by D4.                *)
(*  3. EVERY STEP of [peclV] at the new claim: the middle arm is the old  *)
(*     step; the third arm is closed by REFUTING the presenter off the    *)
(*     turn agreement ([GenOutWild]'s pins).  The block-first byte AT    *)
(*     the wild line itself (a non-terminal alternative the model admits) *)
(*     is REFUSED BY PREMISE: [pwclV_step_write_blk] takes               *)
(*     [WL (line) = false] (owner's ruling (d), no escape: the shell     *)
(*     never presents a block-first byte at a wild line; its diagnostics *)
(*     there go through the licence [pwclV_wild_lic]).                    *)
(*  4. THE TRANSITION (10.4) inside the read: a read whose window         *)
(*     completes a wild line bumps the flag, freezes [cs] and re-closes   *)
(*     the claim at [wildV]; the reader's receipt carries the token.     *)
(*  5. THE DRAIN at the arm, and THE WILD LICENCE (10.2): the token moves *)
(*     the claim by any process event (an output byte, a read).           *)
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
Require Import GenOutWild.
Require Import GenOut.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesView.
Require Import PipeOutN.
Require Import PipeOutNEv.
Require Import PipeBothN.
Require Import PipesOut.
Require Import PipesLinksV.       (* [peclV_step_write_first] *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  0.  PURE: an open round never delivers a new byte                     *)
(* ===================================================================== *)
Lemma lm_rd_open_nows (M : lmodel) (sd : lm_st M) (k : nat) (ho : list mobs)
    (so : gstage M) (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist)
    (ws : list (list mobs * bv 8)) :
  gcl_pure_o M sd k ho so r pre H ->
  (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
  ws = [].
Proof.
  intros (Hout & Hop & _ & _ & _ & HEt & Hdlok) Hpref.
  destruct (lm_blk_open_cs M sd so r pre Hop) as (_ & Hr & _).
  pose proof Hop as (_ & Hwp & Hne & _).
  rewrite /lm_dl_ok decide_False in Hdlok; [| intros [_ Hq]; apply Hne; by rewrite -Hwp].
  pose proof (lines_bytes_rest (snd <$> gs_E M so)) as Hlb.
  rewrite Hr length_fmap in Hlb. cbn [length] in Hlb.
  assert (HEpre : (snd <$> (LogEntryDefs.ch_dl H ++ ws)) `prefix_of` (snd <$> gs_E M so)).
  { rewrite HEt /ch_E.
    etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
    rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
    apply epu_fmap_prefix. by apply prefix_app_r. }
  apply prefix_length in HEpre. rewrite !length_fmap length_app in HEpre.
  destruct ws; [done | cbn [length] in HEpre; lia].
Qed.

Section pipes_wild_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  (* THE WILD LINES, decided: the transition fires at a read whose window
     completes one *)
  Context (WL : lm_line M -> bool).
  Hypothesis HWL : forall l, WL l = true -> lm_wild M l.
  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation L := (gcL G).
  Local Notation K := (gcK G).
  Local Notation st so := (gs_state M sd so).
  Local Notation POV := (popenV g M (gcPIN G) (gwa WA) sd).
  Local Notation PCV := (peclV g M G sd WA).
  Local Notation GCV := (gcl M G sd WA).
  Local Notation PWV := (pwc_blkV g M (gcPIN G) (gcW G) (gcT G)).

  (* ================================================================== *)
  (*  1.  THE FLAG AND THE TOKEN                                         *)
  (* ================================================================== *)
  Definition secc_flag (v : era_pins) (n : nat) : iProp Σ :=
    mono_nat_auth_own (ep_secc v) 1 n.

  (* THE TOKEN CARRIES THE FREEZE: the era's input up to and including the
     wild line, and the choice list frozen one short of it *)
  Definition secc_tok (k : nat) : iProp Σ :=
    (∃ (v : era_pins) (I0 : list (bv 8)),
       PIN k v ∗ mono_nat_lb_own (ep_secc v) 1 ∗ inp_lb v I0
       ∗ ⌜(0 < nlines I0)%nat /\ rest_of I0 = []⌝
       ∗ cs_frozen_at v (nlines I0 - 1)%nat)%I.

  (* ...AT ITS OWN LINE: the input the read completed, named -- and the
     seccomp NEWLINE's push trace [h0] (the delivered list's last entry,
     [(h0, wl_nl)]), whose era input IS [I0] (seccomp design 10.12, lane
     S5a): what lets the wild shape's read refute a byte the ring stored
     after it ([GenOutWild.lm_placed_wild_undisc]) *)
  Definition secc_tok_at (k : nat) (I0 : list (bv 8)) : iProp Σ :=
    (∃ v : era_pins,
       PIN k v ∗ mono_nat_lb_own (ep_secc v) 1 ∗ inp_lb v I0
       ∗ ⌜(0 < nlines I0)%nat /\ rest_of I0 = [] /\ lm_disc_input M I0⌝
       ∗ cs_frozen_at v (nlines I0 - 1)%nat
       ∗ ∃ (D : list (list mobs * bv 8)) (h0 : list mobs),
           dl_list_lb v D
           ∗ ⌜(snd <$> D) = I0 /\ list_basics.last D = Some (h0, wl_nl)
              /\ ins (open_seg h0) = I0 /\ obs_boots h0 = k
              /\ trace_shape h0 true⌝)%I.

  Global Instance secc_flag_timeless v n : Timeless (secc_flag v n).
  Proof using . rewrite /secc_flag. apply _. Qed.
  Global Instance secc_tok_persistent k : Persistent (secc_tok k).
  Proof using . rewrite /secc_tok. apply _. Qed.
  Global Instance secc_tok_timeless k : Timeless (secc_tok k).
  Proof using . rewrite /secc_tok. apply _. Qed.
  Global Instance secc_tok_at_persistent k I0 : Persistent (secc_tok_at k I0).
  Proof using . rewrite /secc_tok_at. apply _. Qed.
  Global Instance secc_tok_at_timeless k I0 : Timeless (secc_tok_at k I0).
  Proof using . rewrite /secc_tok_at. apply _. Qed.

  Lemma secc_tok_of_at (k : nat) (I0 : list (bv 8)) : secc_tok_at k I0 -∗ secc_tok k.
  Proof using .
    iIntros "(%v & Hp & Hlb & HI & %Hn & Hf & _)". iExists v, I0. iFrame.
    iPureIntro. split; [exact (proj1 Hn) | exact (proj1 (proj2 Hn))].
  Qed.

  (* THE TOKEN REFUTES THE MIDDLE ARM *)
  Lemma secc_tok_flag0 (k : nat) (v : era_pins) :
    secc_tok k -∗ PIN k v -∗ secc_flag v 0 -∗ False.
  Proof using .
    iIntros "(%v0 & %I0 & #Hp0 & #Hlb & _) #Hp Hf".
    iDestruct (gcPIN_agree G with "Hp Hp0") as %<-.
    iDestruct (mono_nat_lb_own_valid with "Hf Hlb") as %[_ Hle]. lia.
  Qed.

  (* ================================================================== *)
  (*  2.  THE ARM                                                        *)
  (* ================================================================== *)
  (* the transcript the frozen stage accounts for *)
  Definition wild_acc (so : gstage M) : list (bv 8) :=
    lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) ++ gs_w M so.

  Definition wild_pure (k : nat) (ho : list mobs) (so : gstage M) (u : list (bv 8))
      (H : LogEntryDefs.cons_hist) : Prop :=
    gcl_pure M sd k ho so
      (LogEntryDefs.MkCH (wild_acc so) (LogEntryDefs.ch_log H)
         (LogEntryDefs.ch_dl H) (LogEntryDefs.ch_arm H))
    /\ LogEntryDefs.ch_acc H = wild_acc so ++ u
    /\ gs_w M so = []
    /\ LogEntryDefs.ch_arm H = None
    /\ LogEntryDefs.ch_dl H = echoed (LogEntryDefs.ch_log H)
    /\ (snd <$> gs_E M so) = (snd <$> LogEntryDefs.ch_dl H)
    /\ (snd <$> gs_E M so) <> []
    /\ rest_of (snd <$> gs_E M so) = []
    /\ WL (lm_line_at M (snd <$> gs_E M so)) = true.

  Definition wildV (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) : iProp Σ :=
    (∃ (v : era_pins) (so : gstage M) (u : list (bv 8)),
       PIN k v ∗ secc_flag v 1 ∗ gwa WA k (gs_st M so) ∗ (∃ l, gext WA k l)
       ∗ turn_auth v (lm_pcount M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so)
                        (gs_w M so))
       ∗ cs_frozen v (gs_cs M so) ∗ ps_auth v (gs_ps M so) ∗ Elist_auth v (gs_E M so)
       ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
       ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
       ∗ ⌜wild_pure k ho so u H⌝)%I.

  (* THE CLAIM *)
  Definition pwclV (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) : iProp Σ :=
    (T ∨ (∃ v : era_pins, PIN k v ∗ secc_flag v 0 ∗ PCV k ho H) ∨ wildV k ho H)%I.

  Global Instance wildV_timeless k ho H : Timeless (wildV k ho H).
  Proof using . rewrite /wildV. apply _. Qed.
  Global Instance pwclV_timeless k ho H : Timeless (pwclV k ho H).
  Proof using . rewrite /pwclV. apply _. Qed.

  Lemma pwclV_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    T -∗ pwclV k ho H.
  Proof using . iIntros "#HT". rewrite /pwclV. by iLeft. Qed.

  Lemma pwclV_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ pwclV k ho H ==∗ pwclV k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. by iApply pwclV_taint. Qed.


  (* the middle arm, packed by name (a bare [iFrame] would unfold [peclV]
     and frame the pin into it) *)
  Lemma pwclV_mid (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) (v : era_pins) :
    PIN k v -∗ secc_flag v 0 -∗ PCV k ho H -∗ pwclV k ho H.
  Proof using .
    iIntros "Hp Hf Hc". rewrite /pwclV. iRight. iLeft. iExists v.
    iSplitL "Hp"; [iExact "Hp" |]. iSplitL "Hf"; [iExact "Hf" | iExact "Hc"].
  Qed.

  (* the arm's pure facts, read back *)
  Lemma wild_pure_facts k ho so u H :
    wild_pure k ho so u H ->
    let I0 := snd <$> gs_E M so in
    lm_out_pure M sd k ho so (wild_acc so)
    /\ gs_w M so = [] /\ I0 <> [] /\ rest_of I0 = []
    /\ length (gs_cs M so) = (nlines I0 - 1)%nat
    /\ lm_wild M (lm_line_at M I0)
    /\ gs_st M so = Some (st so)
    /\ lm_pcount M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) (gs_w M so)
       = length (lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) I0).
  Proof using HWL.
    intros (Hall & _ & Hw & _ & _ & _ & Hne & Hr & Hwl) I0.
    destruct Hall as (Hout & Hcsl & _).
    split_and!; [exact Hout | exact Hw | exact Hne | exact Hr | | exact (HWL _ Hwl) | |].
    - rewrite /lm_cs_len_ok decide_True in Hcsl; [exact Hcsl | by split].
    - destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0n & _).
      rewrite /gs_state. destruct (gs_st M so) as [s1 |] eqn:Hf; [reflexivity |].
      exfalso. destruct (proj1 Hf0n eq_refl) as [HE _]. apply Hne.
      by rewrite /I0 HE fmap_nil.
    - rewrite /lm_pcount Hw. unfold I0. cbn [length]. lia.
  Qed.

  (* ---- the process events the arm absorbs ---- *)
  Lemma wildV_out (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) (b : bv 8) :
    wildV k ho H -∗ wildV k ho (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using .
    iIntros "(%v & %so & %u & Hpn & Hfl & Hwa & Hx & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hp)". iExists v, so, (u ++ [b]).
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. iFrame "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll".
    iPureIntro. destruct Hp as (Hg & Hacc & Hrest).
    split; [exact Hg |]. split; [| exact Hrest].
    cbn [LogEntryDefs.ch_acc]. rewrite Hacc. by rewrite -app_assoc.
  Qed.

  (* a read in the wild era delivers nothing: every echoed entry already
     has been *)
  Lemma wild_read_nil k ho so u H (ws : list (list mobs * bv 8)) :
    wild_pure k ho so u H ->
    read_ok (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) ws -> ws = [].
  Proof using B.
    intros (Hall & _ & _ & _ & Hdl & _) Hread.
    destruct Hall as (_ & _ & _ & Hin & _).
    cbn [LogEntryDefs.ch_log LogEntryDefs.ch_dl] in Hin.
    destruct (gin_read_pure M B k _ _ ws _ Hread Hin) as (Hpref & _ & _).
    rewrite -Hdl in Hpref. apply prefix_length in Hpref.
    rewrite length_app in Hpref. destruct ws; [done | cbn [length] in Hpref; lia].
  Qed.

  Lemma wildV_read (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) ws ->
    wildV k ho H -∗ ⌜ws = []⌝ ∗ wildV k ho (ConsLog.cons_step H (ConsLog.EvRead ws)).
  Proof using B.
    intros Hread. iIntros "(%v & %so & %u & Hpn & Hfl & Hwa & Hx & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hp)".
    pose proof (wild_read_nil k ho so u H ws Hp Hread) as ->.
    iSplitR; [done |]. iExists v, so, u.
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. rewrite app_nil_r.
    iFrame "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll". iPureIntro. destruct H. exact Hp.
  Qed.

  (* ---- the kernel's own events: no arm is ever open in the wild era ---- *)
  Lemma pwclV_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    pwclV k ho H -∗ pwclV k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite /pwclV.
    iIntros "[#HT | [(%v & Hp & Hf & Hc) | Hw]]"; [by iLeft | |].
    - iApply (pwclV_mid with "Hp Hf").
      iApply (peclV_close g M G sd WA with "Hc"); done.
    - iExFalso. iDestruct "Hw" as (v so u) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hp)".
      destruct Hp as (_ & _ & _ & Harm & _).
      destruct Hev as (a & Ha & _). by rewrite Harm in Ha.
  Qed.

  Lemma pwclV_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    pwclV k ho CH -∗ pwclV k ho CH ∗ (T ∨ ⌜garm_era M k ho CH⌝).
  Proof using .
    rewrite /pwclV. iIntros "[#HT | [(%v & Hp & Hf & Hc) | Hw]]".
    - iSplitR; by iLeft.
    - iDestruct (peclV_arm g M G sd WA with "Hc") as "[Hc Ha]".
      iFrame "Ha". iApply (pwclV_mid with "Hp Hf Hc").
    - iDestruct "Hw" as (v so u) "(Hpn & Hfl & Hwa & Hx & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hp)".
      pose proof Hp as (_ & _ & _ & Harm & _).
      iSplitL "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll"; [iRight; iRight; iExists v, so, u; by iFrame "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll" |].
      iRight. iPureIntro. by rewrite /garm_era Harm.
  Qed.

  Lemma pwclV_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input M (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc M h -> trace_shape h true ->
    pwclV k ho H -∗ pwclV k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using B HWL.
    intros Hok Hev Hd Hb Hdh Hsh. rewrite /pwclV.
    iIntros "[#HT | [(%v & Hp & Hf & Hc) | Hw]]"; [by iLeft | |].
    - iApply (pwclV_mid with "Hp Hf").
      iApply (peclV_open g M G B sd WA with "Hc"); done.
    - (* THE LOG IS FROZEN: the new byte follows the wild line, which D4
         forbids *)
      iExFalso. iDestruct "Hw" as (v so u) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hp)".
      iPureIntro.
      pose proof Hp as (Hall & _ & _ & Harm & _ & _ & Hne & Hr & Hwl).
      destruct (wild_pure_facts k ho so u H Hp) as (Hout & _).
      destruct Hall as (_ & _ & _ & Hin & _ & HEt & _).
      cbn [LogEntryDefs.ch_log LogEntryDefs.ch_dl LogEntryDefs.ch_arm] in Hin, HEt.
      pose proof Hev as (_ & _ & _ & Hord & _ & HK1f & _).
      destruct HK1f as (f & Hfl & Hcnt).
      rewrite (lm_flush_lost_zero M h f Hsh Hdh Hfl) Nat.add_0_r -ins_obs_ins in Hcnt.
      assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = gs_E M so).
      { rewrite HEt /ch_E. cbn [LogEntryDefs.ch_arm]. rewrite Harm /ch_arm_E.
        by rewrite app_nil_r. }
      assert (HlenE : (length (gs_E M so) <= length (LogEntryDefs.ch_log H))%nat).
      { rewrite -Hseg /seg_of length_fmap /echoed length_fmap. apply length_filter. }
      pose proof (lm_out_pure_move M sd k ho h so (wild_acc so)
                    (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
                    Hsh Hb Hord Hin Hseg ltac:(lia) Hout) as Hout'.
      destruct Hout' as (_ & _ & Hidx & _ & _ & _ & _ & _ & Hpre1 & Hpre2 & _).
      assert (Hpl : forall j x, gs_E M so !! j = Some x -> x.1 `prefix_of` open_seg h)
        by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
      pose proof (E_bytes_of_hist (gs_E M so) (open_seg h) Hidx Hpl Hpre2) as HEB.
      assert (HEo : (snd <$> gs_E M so) `prefix_of` ins (open_seg h))
        by (rewrite HEB; apply prefix_take).
      destruct (wild_prefix_strict_snoc (snd <$> gs_E M so) _ HEo
                  ltac:(rewrite length_fmap; lia)) as [x Hx].
      exact (lm_disc_wild_last M h _ x Hdh Hsh Hne Hr (HWL _ Hwl) Hx).
  Qed.

  Lemma pwclV_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    lm_disc M h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    pwclV k ho CH ==∗ pwclV k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using B.
    intros Hdisc Hsh Hk Hends Hwire Hord HK1 Harm. rewrite /pwclV.
    iIntros "[#HT | [(%v & Hp & Hf & Hc) | Hw]]"; [by iLeft | |].
    - iMod (peclV_step_echo g M G B sd WA L with "Hc") as "Hc"; try done.
      iModIntro. iApply (pwclV_mid with "Hp Hf Hc").
    - iExFalso. iDestruct "Hw" as (v so u) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hp)".
      destruct Hp as (_ & _ & _ & Harm' & _). by rewrite Harm' in Harm.
  Qed.

  Lemma pwclV_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    pwclV k ho CH ==∗ pwclV k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using B.
    intros Hok Hev. rewrite /pwclV.
    iIntros "[#HT | [(%v & Hp & Hf & Hc) | Hw]]"; [by iLeft | |].
    - iMod (peclV_step_byte g M G B sd WA L with "Hc") as "Hc"; try done.
      iModIntro. iApply (pwclV_mid with "Hp Hf Hc").
    - iExFalso. iDestruct "Hw" as (v so u) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hp)".
      destruct Hp as (_ & _ & _ & Harm & _).
      destruct Hev as (a & Ha & _). by rewrite Harm in Ha.
  Qed.


  (* ================================================================== *)
  (*  4.  THE WRITES: the middle arm's step, the third arm refuted        *)
  (* ================================================================== *)

  (* WHAT A PRESENTER'S HALVES SAY OF THE ARM: the cursor is the frozen
     stage's, the bounds are below its lists, the witness is its state *)
  Lemma wildV_turn (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (v : era_pins) (P : nat) :
    PIN k v -∗ turn v P -∗ wildV k ho H -∗
    ⌜exists so u, wild_pure k ho so u H
       /\ P = length (lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) (snd <$> gs_E M so))⌝.
  Proof using HWL.
    iIntros "#Hp Ht (%v' & %so & %u & #Hpn & _ & _ & _ & Hta & _ & _ & _ & _ & _ & %Hw)".
    iDestruct (gcPIN_agree G with "Hp Hpn") as %<-.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iPureIntro. exists so, u. split; [exact Hw |].
    destruct (wild_pure_facts k ho so u H Hw) as (_ & _ & _ & _ & _ & _ & _ & Hpc).
    by rewrite HP Hpc.
  Qed.

  Lemma wildV_pins (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (v : era_pins) (P : nat) (ps0 cs0 : list nat) (I0 : list (bv 8)) (s0 : lm_st M) :
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    wildV k ho H -∗
    ⌜exists so u, wild_pure k ho so u H
       /\ P = length (lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) (snd <$> gs_E M so))
       /\ ps0 `prefix_of` gs_ps M so /\ cs0 `prefix_of` gs_cs M so
       /\ I0 `prefix_of` (snd <$> gs_E M so) /\ s0 = st so⌝.
  Proof using HWL.
    iIntros "#Hp Ht #Hps0 #Hcs0 #HI0 #HW
             (%v' & %so & %u & #Hpn & _ & Hwa & _ & Hta & #Hcs & Hps & _ & _ & Hdll & %Hw)".
    iDestruct (gcPIN_agree G with "Hp Hpn") as %<-.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
    iDestruct (ps_lb_prefix with "Hps Hps0") as %Hpsp.
    iDestruct (cs_frozen_prefix with "Hcs Hcs0") as %Hcsp.
    iDestruct (inp_lb_le with "Hdll HI0") as %HIp.
    iPureIntro. exists so, u.
    destruct (wild_pure_facts k ho so u H Hw) as (_ & _ & _ & _ & _ & _ & _ & Hpc).
    pose proof Hw as (_ & _ & _ & _ & _ & HEd & _).
    split_and!; [exact Hw | by rewrite HP Hpc | exact Hpsp | exact Hcsp | by rewrite HEd |].
    by rewrite -Hst.
  Qed.

  (* (H) THE ERA'S HEAD WRITE: the arm's cursor is past the settled
     prologue ([lm_proc_before_pos]) *)
  Lemma pwclV_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    lm_st_ok M s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot WA k s0 ∨ T) -∗
    pwclV k ho H ==∗
      pwclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ gcW G k s0) ∨ T).
  Proof using HWL.
    intros Hok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt Hcl". rewrite /pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iLeft | by iRight].
    - iMod (peclV_step_write_first g M G sd WA k v a b s0 ho H Hok Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb Hbt Hc") as "[Hc $]".
      iModIntro. iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct (wildV_turn with "Hpin Ht Hw") as %(so & u & Hw & HP).
      exfalso.
      destruct (wild_pure_facts k ho so u H Hw) as (Hout & _ & Hne & _).
      destruct Hout as (_ & _ & _ & _ & Hpsb & Hpinf & _).
      pose proof (lm_proc_before_pos M (gs_ps M so) (gs_cs M so) (st so) _ Hpsb Hpinf Hne).
      lia.
  Qed.

  (* (W) A BYTE INSIDE A BLOCK OR A PROLOGUE ROUND: the stream pins the
     writer's input at the arm's ([lm_write_stage_byte]), and the arm's
     input has one line more than any choice list below the frozen one *)
  Lemma pwclV_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    pwclV k ho H ==∗
      pwclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gcW G k s0) ∨ T).
  Proof using HWL.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite /pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iLeft | by iRight].
    - iMod (peclV_step_write g M G sd WA k v P b ps0 cs0 s0 I0 ho H Hn Hpin0 Hb
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc $]".
      iModIntro. iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct (wildV_pins with "Hpin Ht Hpslb Hcslb Hilb HW Hw")
        as %(so & u & Hw & HP & Hpsp & Hcsp & HIp & ->).
      exfalso.
      destruct (wild_pure_facts k ho so u H Hw) as (_ & Hw0 & Hne & Hr & Hlen & _).
      destruct (lm_write_stage_byte M ps0 (gs_ps M so) cs0 (gs_cs M so) (st so)
                  (gs_E M so) (gs_w M so) I0 P b Hpsp Hpin0 Hcsp Hn HIp
                  ltac:(rewrite /lm_pcount Hw0 HP; cbn [length]; lia) Hb) as [HEI _].
      pose proof (nlines_pos_of_rest_nil _ Hne Hr) as H0.
      pose proof (prefix_length _ _ Hcsp). rewrite HEI in Hlen H0. lia.
  Qed.

  (* (B) A BLOCK'S FIRST BYTE, at a line that is NOT wild (premise): the
     wild arm is refuted -- the cursor pins the presenter's line to the
     frozen one ([lm_blk_stage_inp]), which is wild *)
  Lemma pwclV_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    WL (lm_of M (bodies_of I0 !!! (nlines I0 - 1)%nat)) = false ->
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
    pwclV k ho H ==∗
      pwclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ gcW G k s0) ∨ T).
  Proof using B HWL.
    intros Hnw Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite /pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iLeft | by iRight].
    - iMod (peclV_step_write_blk g M G B sd WA k v P a b ps0 cs0 s0 I0 ho H
              Hne0 Hr0 Hdiv Hpin0 HPeq Hok Hterm Hhead
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]".
      iModIntro. iSplitR "Hr"; [| done].
      iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct "Hw" as (v' so u)
        "(#Hpn & Hfl & Hwa & Hx & Hta & #Hcs & Hps & HE & Hdl & Hdll & %Hw)".
      iDestruct (gcPIN_agree G with "Hpin Hpn") as %<-.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (cs_frozen_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HIp.
      destruct (wild_pure_facts k ho so u H Hw)
        as (Hout & Hw0 & Hne & Hr & Hlen & _ & _ & Hpc).
      pose proof Hw as (_ & _ & _ & _ & _ & HEd & _).
      rewrite -HEd in HIp.
      pose proof Hout as (_ & _ & _ & _ & _ & _ & Hcsb & _).
      assert (Hs0 : s0 = st so) by (rewrite -Hst; reflexivity). subst s0.
      pose proof (lm_blk_stage_inp M K ps0 (gs_ps M so) cs0 (gs_cs M so) (st so)
                    I0 (snd <$> gs_E M so) Hpsp Hcsp Hpin0 Hne0 Hr0 Hdiv HIp Hcsb
                    ltac:(rewrite -HPeq HP Hpc; reflexivity)) as HIE.
      pose proof Hw as (_ & _ & _ & _ & _ & _ & _ & _ & Hwl).
      rewrite -HIE /lm_line_at in Hwl. by rewrite Hwl in Hnw.
  Qed.


  (* (P) A PROLOGUE ROUND'S CHOICE BYTE: the writer's stream pins its input
     at the arm's ([lm_pro_stage_inp]), whose lines outnumber the frozen
     list *)
  Lemma pwclV_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
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
    pwclV k ho CH ==∗
      pwclV k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gcW G k s0) ∨ T).
  Proof using HWL.
    intros HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl". rewrite /pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iLeft | by iRight].
    - iMod (peclV_step_write_pro g M G sd WA k v P a b ps0 cs0 s0 I0 ho CH
              HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc $]".
      iModIntro. iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct (wildV_pins with "Hpin Ht Hpslb Hcslb Hilb HW Hw")
        as %(so & u & Hw & HP & Hpsp & Hcsp & HIp & ->).
      exfalso.
      destruct (wild_pure_facts k ho so u CH Hw) as (Hout & _ & Hne & Hr & Hlen & _).
      pose proof Hout as (_ & _ & _ & _ & Hpsb & Hpinf & _).
      pose proof (lm_pro_stage_inp M L ps0 (gs_ps M so) cs0 (gs_cs M so) (st so)
                    I0 (snd <$> gs_E M so) 0 Hpsp Hcsp Hpsb Hpin0 Hr0 Hopen Hdiv Hnd
                    HIp Hpinf ltac:(rewrite -HPeq HP; lia)) as HIE.
      pose proof (nlines_pos_of_rest_nil _ Hne Hr) as H0.
      pose proof (prefix_length _ _ Hcsp). rewrite -HIE in Hlen H0. lia.
  Qed.

  (* ================================================================== *)
  (*  5.  THE DRAIN                                                      *)
  (* ================================================================== *)
  Lemma pwclV_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    pwclV k ho CH -∗ pwclV k ho CH ∗ gdrain_ret M G sd WA k seg.
  Proof using B HWL.
    intros Hsh Hk Hpre Hins Hwire Hne0. rewrite /pwclV.
    iIntros "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iSplitR; [by iLeft | rewrite /gdrain_ret; by iLeft].
    - iDestruct (peclV_drain g M G B sd WA k h ho CH seg Hsh Hk Hpre Hins Hwire Hne0
                   with "Hc") as "[Hc $]".
      iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct "Hw" as (v so u)
        "(#Hpn & Hfl & Hwa & Hx & Hta & #Hcs & Hps & HE & Hdl & Hdll & %Hw)".
      destruct (wild_pure_facts k ho so u CH Hw)
        as (Hout & Hw0 & Hne & Hr & Hlen & Hwild & Hsome & _).
      pose proof Hw as (_ & Hacc & _).
      destruct Hout as (_ & _ & Hidx & Hbyte & Hpsb & Hpinf & Hcsb & _ & Hpre1 & Hpre2
                        & Hpre3 & _ & _ & Hfok).
      iEval (rewrite Hsome) in "Hwa".
      iDestruct (gwa_W WA _ (st so) with "Hwa") as "(Hwa & #HW & #Hty)".
      iEval (rewrite -Hsome) in "Hwa".
      iSplitR "".
      { iRight. iRight. iExists v, so, u.
        iFrame "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll". by iPureIntro. }
      rewrite /gdrain_ret. iRight. iExists (st so). iFrame "Hty HW".
      iSplitR; [| by iPureIntro]. iPureIntro.
      assert (Hbytes : (snd <$> gs_E M so) `prefix_of` ins seg).
      { destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil fmap_nil. apply prefix_nil.
        - assert (Hpl : forall j x, gs_E M so !! j = Some x ->
                          x.1 `prefix_of` open_seg ho)
            by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
          rewrite (E_bytes_of_hist (gs_E M so) (open_seg ho) Hidx Hpl Hpre2).
          etrans; [apply prefix_take |].
          rewrite Hins. apply ins_prefix_of, open_seg_prefix_boots;
            [exact Hpre | by rewrite Hbo | exact Hsh]. }
      apply (lm_good_out_wild M L K B (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) u seg
               Hpsb Hcsb Hpinf Hbyte Hne Hr Hlen Hwild); [| exact Hbytes].
      rewrite Hacc /wild_acc Hw0 app_nil_r in Hwire. exact Hwire.
  Qed.

  (* ================================================================== *)
  (*  6.  THE READ, AND THE TRANSITION                                   *)
  (* ================================================================== *)
  (* THE WINDOW COMPLETES A WILD LINE *)
  Definition rd_wild (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) : Prop :=
    ws <> []
    /\ (snd <$> (LogEntryDefs.ch_dl CH ++ ws)) <> []
    /\ rest_of (snd <$> (LogEntryDefs.ch_dl CH ++ ws)) = []
    /\ WL (lm_line_at M (snd <$> (LogEntryDefs.ch_dl CH ++ ws))) = true.

  Global Instance rd_wild_dec CH ws : Decision (rd_wild CH ws).
  Proof using . rewrite /rd_wild. apply _. Qed.

  (* THE READER'S RECEIPT: the generic one, and -- at a read that completes
     a wild line -- the era's wild token (or the taint) *)
  Definition rd_retW (k : nat) (v : era_pins) (n : nat) (CH : LogEntryDefs.cons_hist)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    (rd_retV M G k v n CH ws
     ∗ (⌜rd_wild CH ws⌝ -∗
          (secc_tok_at k (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           (* ...and the newline is the window's own last entry (S5b) *)
           ∗ ⌜exists h0 : list mobs, list_basics.last ws = Some (h0, wl_nl)
               /\ ins (open_seg h0) = snd <$> (LogEntryDefs.ch_dl CH ++ ws)
               /\ obs_boots h0 = k⌝)
          ∨ T))%I.

  Lemma pwclV_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    PIN k v -∗ dl_cnt v (1/2) n -∗ pwclV k ho CH ==∗
      pwclV k ho (ConsLog.cons_step CH (ConsLog.EvRead ws)) ∗ rd_retW k v n CH ws.
  Proof using B HWL.
    intros Hread. iIntros "#Hpinr Hdlr Hcl". rewrite /pwclV /rd_retW.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - (* the taint *)
      iModIntro. iSplitR; [by iLeft |]. iSplitL "Hdlr".
      + rewrite /rd_retV. iLeft. by iFrame "HT Hdlr".
      + iIntros "_". by iRight.
    - iDestruct (gcPIN_agree G with "Hp1 Hpinr") as %->.
      destruct (decide (rd_wild CH ws)) as [Hwd | Hnw]; last first.
      { (* no transition: the old step *)
        iMod (peclV_step_read g M G B sd WA k v n ho CH ws Hread
                with "Hpinr Hdlr Hc") as "[Hc Hr]".
        iModIntro. iSplitL "Hp1 Hf Hc"; [iApply (pwclV_mid with "Hp1 Hf Hc") |].
        iFrame "Hr". iIntros "%Hq". by destruct (Hnw Hq). }
      destruct Hwd as (Hws & Hne & Hr & Hwl).
      rewrite peclV_gen. iDestruct "Hc" as "[Hg | Hp]"; last first.
      { (* an open round delivers nothing *)
        iExFalso.
        iDestruct "Hp" as (v2 w so r gb pre tm)
          "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hall)".
        pose proof Hall as (_ & _ & _ & Hin & _).
        destruct (gin_read_pure M B k _ _ ws _ Hread Hin) as (Hpref & _ & _).
        by pose proof (lm_rd_open_nows M sd k ho so r pre CH ws Hall Hpref). }
      iDestruct "Hg" as "[#HT | Hg]".
      { iModIntro. iSplitR; [by iLeft |]. iSplitL "Hdlr".
        + rewrite /rd_retV. iLeft. by iFrame "HT Hdlr".
        + iIntros "_". by iRight. }
      (* THE TRANSITION *)
      iDestruct "Hg" as (v2 so)
        "(#Hpin2 & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpinr") as %->.
      iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
      pose proof Hall as Hall0.
      destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
      pose proof Hin as Hin2.
      destruct Hin2 as (_ & _ & Hbt & _ & Hidx & Hbyte & _ & _ & Hdh).
      destruct (gin_read_pure M B k _ _ ws _ Hread Hin) as (Hpref & _ & _).
      (* THE SECCOMP NEWLINE: the delivered list's last trace, whose era
         input is the whole delivered input (lane S5a) *)
      destruct (lm_rd_last_hist k (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH ++ ws)
                  Hpref Hidx Hbt (fun e He => proj2 (Hdh e He)) (proj1 (proj2 Hread))
                  ltac:(intros Hq; apply Hne; by rewrite Hq))
        as (h0 & c0 & Hl0 & Hins0 & Hb0 & Hs0).
      assert (Hc0 : c0 = wl_nl).
      { destruct (rest_of_end _ Hr) as [Hq | Hq]; [by destruct Hne |].
        rewrite fmap_last Hl0 /= in Hq. by injection Hq. }
      subst c0.
      destruct (lm_rd_wild_stage M sd k ho so CH ws Hall0 Hpref Hws Hne Hr (HWL _ Hwl))
        as (Harm & Hdlall & HEI & Hw0 & Hcslen).
      pose proof Hpure as (Hacc & _ & _ & HEdisc & _ & _ & _ & _ & _ & _ & _ & _ & Hf0n & _).
      set (I' := snd <$> (LogEntryDefs.ch_dl CH ++ ws)) in *.
      assert (Hboots : forall x : list mobs * bv 8,
                x ∈ LogEntryDefs.ch_dl CH ++ ws -> obs_boots x.1 = k).
      { intros x Hx.
        destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) x
                    (elem_of_prefix _ _ _ Hx Hpref)) as (e & He & _ & <-).
        exact (Hbt e He). }
      assert (Hdi : lm_disc_input M I') by (rewrite -HEI; exact HEdisc).
      pose proof (gcl_pure_rd_stage M sd k ho so CH Hall0) as Hrd.
      rewrite HEI in Hrd.
      assert (Hsome : gs_st M so = Some (st so)).
      { rewrite /gs_state. destruct (gs_st M so) as [s1 |] eqn:Hf; [reflexivity |].
        exfalso. destruct (proj1 Hf0n eq_refl) as [HE0 _]. apply Hne.
        by rewrite -HEI HE0 fmap_nil. }
      iEval (rewrite Hsome) in "Hwa".
      iDestruct (gwa_W WA _ (st so) with "Hwa") as "(Hwa & #HW & _)".
      iEval (rewrite -Hsome) in "Hwa".
      iMod (mono_nat_own_update 1 with "Hf") as "[Hf #Hlb]"; [lia |].
      iMod (cs_freeze v with "Hcs") as "#Hfz".
      iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
      iDestruct (turn_lb_get with "Hta") as "#Htlb".
      iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n (n + length ws)
              with "Hdl Hdlr") as "[Hdl Hdlr]".
      iMod (dl_list_auth_grow v (LogEntryDefs.ch_dl CH) ws with "Hdll")
        as "[Hdll #Hdllb]".
      iAssert (inp_lb v I')%I as "#HI'".
      { iApply (inp_lb_of_dl_lb v (LogEntryDefs.ch_dl CH ++ ws) _ (reflexivity _)).
        iExact "Hdllb". }
      pose proof (nlines_pos_of_rest_nil I' Hne Hr) as Hpos.
      iAssert (cs_frozen_at v (nlines I' - 1)%nat)%I as "#Hfzat".
      { iApply (cs_frozen_at_of with "Hfz"). by rewrite Hcslen HEI. }
      iModIntro. iSplitL "Hf Hwa Hext Hta Hps HE Hdl Hdll".
      { iRight. iRight. iExists v, so, [].
        rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
        rewrite length_app Hdleq.
        iFrame "Hpin2 Hf Hwa Hta Hfz Hps HE Hdl Hdll".
        iSplitL "Hext"; [by iExists _ |].
        iPureIntro. cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_arm].
        assert (Hwa' : wild_acc so = LogEntryDefs.ch_acc CH) by (rewrite Hacc; reflexivity).
        split_and!.
        - rewrite Hwa'. exact (gcl_pure_read M sd k ho so CH ws Hpref Hall0).
        - by rewrite app_nil_r Hwa'.
        - exact Hw0.
        - exact Harm.
        - exact Hdlall.
        - exact HEI.
        - by rewrite HEI.
        - by rewrite HEI.
        - by rewrite HEI. }
      iSplitL "Hdlr".
      + rewrite /rd_retV. iRight. iFrame "Hdlr".
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [iPureIntro; by destruct Hin as (_ & _ & _ & _ & ? & _) |].
        iSplitR; [iPureIntro; by destruct Hin as (_ & _ & _ & _ & _ & ? & _) |].
        iSplitR; [iPureIntro; exact Hboots |].
        iSplitR; [iExact "HI'" |].
        iSplitR; [by iPureIntro |].
        iRight. iExists (gs_cs M so), (gs_ps M so), (st so).
        iSplitR; [iApply (cs_frozen_lb with "Hfz") |].
        iFrame "Hpslb HW".
        iSplitR; [iPureIntro; rewrite Hcslen HEI; unfold I' in *; lia |].
        iSplitR; [| by iPureIntro].
        iApply (turn_lb_weaken with "Htlb").
        rewrite /lm_pcount Hw0 HEI. cbn [length]. unfold I' in *. lia.
      + iIntros "_". iLeft.
        assert (Hlw : list_basics.last ws = Some (h0, wl_nl)).
        { destruct (exists_last Hws) as (ws0 & x & ->).
          rewrite app_assoc last_snoc in Hl0. rewrite last_snoc. exact Hl0. }
        iSplitR; last first.
        { iPureIntro. exists h0. split_and!; [exact Hlw | exact Hins0 | exact Hb0]. }
        iExists v. iFrame "Hpin2 Hlb HI' Hfzat".
        iSplit; [iPureIntro; split_and!; [exact Hpos | exact Hr | exact Hdi] |].
        iExists (LogEntryDefs.ch_dl CH ++ ws), h0. iFrame "Hdllb".
        iPureIntro. split_and!; [reflexivity | exact Hl0 | exact Hins0 | exact Hb0
                                | exact Hs0].
    - (* THE WILD ERA: nothing is delivered *)
      iDestruct "Hw" as (v2 so u)
        "(#Hpn & Hfl & Hwa & Hx & Hta & #Hcs & Hps & HE & Hdl & Hdll & %Hw)".
      iDestruct (gcPIN_agree G with "Hpn Hpinr") as %->.
      iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
      pose proof (wild_read_nil k ho so u CH ws Hw Hread) as ->.
      pose proof Hw as (Hall & _ & _ & _ & Hdl_e & _).
      destruct Hall as (_ & _ & _ & Hin & _).
      cbn [LogEntryDefs.ch_log LogEntryDefs.ch_dl] in Hin.
      destruct Hin as (_ & _ & Hbt & _ & Hidx & Hbyte & _ & _).
      iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
      iModIntro. iSplitR "Hdlr".
      { iRight. iRight. iExists v, so, u.
        rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. rewrite app_nil_r.
        iFrame "Hpn Hfl Hwa Hx Hta Hcs Hps HE Hdl Hdll". iPureIntro.
        destruct CH. exact Hw. }
      iSplitL "Hdlr".
      + rewrite /rd_retV. iRight. rewrite Nat.add_0_r app_nil_r. iFrame "Hdlr".
        iSplitR; [by iPureIntro |].
        iSplitR; [iPureIntro; rewrite Hdl_e; reflexivity |].
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR.
        { iPureIntro. intros x Hx. rewrite Hdl_e in Hx.
          destruct (echoed_elem_inv _ x Hx) as (e & He & _ & <-). exact (Hbt e He). }
        iSplitR; [iApply (inp_lb_of_dl_lb with "Hdllb"); reflexivity |].
        iSplitR; [iPureIntro | by iLeft].
        rewrite /lm_E_disc seg_of_snd -Hdl_e in Hbyte. exact Hbyte.
      + iIntros "(%Hq & _)". by destruct Hq.
  Qed.


  (* ================================================================== *)
  (*  7.  THE N-WRITER FAMILY: its obligation, its filing                *)
  (* ================================================================== *)
  (* a further byte of an open round: the arm keeps the pipe ledger's
     whole cursor, which no half survives *)
  Lemma wild_cur_refute (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (w : pipe_era) (r : nat) (gb : gname) (tm : bool) :
    wildV k ho H -∗ pera_pin g k w -∗ cur_half w (1/2) r gb tm -∗ False.
  Proof using Hext.
    iIntros "(%v & %so & %u & _ & _ & _ & [%l Hx] & _) #Hpe Hc".
    rewrite Hext. iDestruct "Hx" as (w' r' gb' pre' tm') "(#Hpe' & _ & Hc' & _)".
    iDestruct (pera_pin_agree with "Hpe Hpe'") as %<-.
    iApply (cur_half_excl with "Hc' Hc").
  Qed.

  (* a block's first byte at a line that is not wild: below the wild line
     the cursor refutes it, and the wild line is the arm's own *)
  Lemma wild_blk_refute (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (v : era_pins) (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) :
    wr_blkV M ps cs s0 I P -> WL (lineV M I) = false ->
    PIN k v -∗ gcW G k s0 -∗ turn v P -∗ ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗
    wildV k ho H -∗ False.
  Proof using HWL.
    intros ((Hpp & Hr & Hn & HP) & _) Hnw.
    iIntros "#Hpin #HW Ht #Hps #Hcs #HE Hw".
    iDestruct (wildV_pins with "Hpin Ht Hps Hcs HE HW Hw")
      as %(so & u & Hw & HPs & Hpsp & Hcsp & HIp & ->).
    iPureIntro.
    destruct (wild_pure_facts k ho so u H Hw) as (Hout & _).
    pose proof Hout as (_ & _ & _ & _ & _ & _ & Hcsb & _).
    assert (HneI : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    pose proof (lm_blk_stage_inp M K ps (gs_ps M so) cs (gs_cs M so) (st so) I
                  (snd <$> gs_E M so) Hpsp Hcsp Hpp HneI Hr ltac:(lia) HIp Hcsb
                  ltac:(rewrite -HP HPs; reflexivity)) as HIE.
    pose proof Hw as (_ & _ & _ & _ & _ & _ & _ & _ & Hwl).
    rewrite -HIE in Hwl. rewrite /lineV in Hnw. rewrite /lm_line_at in Hwl.
    by rewrite Hwl in Hnw.
  Qed.

  (* THE CLAIM PAYS THE FAMILY'S ONE OBLIGATION, at a line that is not
     wild (the family's lines are pipelines) *)
  Theorem pwclV_ecl_holds (v : era_pins) (I : list (bv 8)) (sR : lm_st M) :
    WL (lineV M I) = false ->
    ⊢ eclN pwclV (PWV v I sR) (ptkV T v I) (pwitV M I sR).
  Proof using Hext HWL.
    intros Hnw. rewrite /eclN. iModIntro.
    iIntros (k ho H pre b tm tm' Htmt Hwit) "Hpw Hcl".
    iPoseProof (pblkV_ecl_holds g M G sd WA Hext v I sR) as "He".
    rewrite /eclN. iDestruct "He" as "#He".
    rewrite {1}/pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iApply pwclV_taint |].
      iSplitR; [rewrite /pwc_blkV; by iRight | iRight; rewrite /ptkV; by iRight].
    - iMod ("He" $! k ho H pre b tm tm' Htmt Hwit with "Hpw Hc") as "(Hc & Hpw & Htk)".
      iModIntro. iFrame "Hpw Htk". iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct "Hpw" as "[Hx | #HT]"; last first.
      { iModIntro. iSplitL "Hw"; [rewrite /pwclV; iRight; iRight; by iApply wildV_out |].
        iSplitR; [rewrite /pwc_blkV; by iRight | iRight; rewrite /ptkV; by iRight]. }
      iExFalso.
      iDestruct "Hx" as (ps cs s0 P) "([%Hw %Htie] & #Hpin & #HW & Htn & #Hps & #Hcs & Hled & #HE)".
      iDestruct "Hled" as "[%Hnil | Hled]".
      + subst pre. cbn [length] in *. rewrite Nat.add_0_r.
        iApply (wild_blk_refute k ho H v ps cs s0 I P Hw Hnw
                  with "Hpin HW Htn Hps Hcs HE Hw").
      + iDestruct "Hled" as (w gb) "(#Hpera & Hcur & _)".
        iApply (wild_cur_refute with "Hw Hpera Hcur").
  Qed.

  (* THE FILING at the credential: a block the family wrote -- the arm
     keeps the pipe ledger's whole cursor *)
  Lemma pwclV_blk_file (V : pview M) (v : era_pins) (I : list (bv 8)) (sR : lm_st M)
      (lR : pline') (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (pre : list (bv 8)) (b : bv 8) :
    pv_line V (lineV M I) = Some lR -> pv_adm V lR = true ->
    line_blocks (pv_fc V sR) lR pre -> pre <> [] -> b = u_prompt !!! 0%nat ->
    PWV v I sR k pre false -∗ pwclV k ho H ==∗
      pwclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
            ⌜wr_blkV M ps cs s0 I P /\ lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ gcW G k s0 ∗ turn v (S (P + length pre))%nat
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc V lR (PLRun pre)]) ∗ inp_lb v I) ∨ T).
  Proof using B Hext.
    intros HlR Ha Hbl Hne Hbv. iIntros "Hpw Hcl". rewrite {1}/pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iApply pwclV_taint | by iRight].
    - iMod (pwc_blkV_file g M G B sd WA Hext V v I sR lR k ho H pre b HlR Ha Hbl Hne Hbv
              with "Hpw Hc") as "[Hc $]".
      iModIntro. iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct "Hpw" as "[Hx | #HT]"; last first.
      { iModIntro. iSplitL "Hw"; [rewrite /pwclV; iRight; iRight; by iApply wildV_out |].
        by iRight. }
      iExFalso.
      iDestruct "Hx" as (ps cs s0 P) "(_ & _ & _ & _ & _ & _ & Hled & _)".
      iDestruct "Hled" as "[%Hnil | Hled]"; [by destruct (Hne Hnil) |].
      iDestruct "Hled" as (w gb) "(#Hpera & Hcur & _)".
      iApply (wild_cur_refute with "Hw Hpera Hcur").
  Qed.

  (* ...and the EMPTY block: a pipeline line is not wild *)
  Lemma pwclV_blk_file_empty (V : pview M) (v : era_pins) (I : list (bv 8)) (sR : lm_st M)
      (lR : pline') (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) (b : bv 8) :
    (forall l lR', pv_line V l = Some lR' -> WL l = false) ->
    pv_line V (lineV M I) = Some lR ->
    b = u_prompt !!! 0%nat ->
    PWV v I sR k [] false -∗ pwclV k ho H ==∗
      pwclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
            ⌜wr_blkV M ps cs s0 I P /\ lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ gcW G k s0 ∗ turn v (S P)
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc V lR (PLRun [])]) ∗ inp_lb v I) ∨ T).
  Proof using B HWL.
    intros HV HlR Hbv. iIntros "Hpw Hcl". rewrite {1}/pwclV.
    iDestruct "Hcl" as "[#HT | [(%v1 & #Hp1 & Hf & Hc) | Hw]]".
    - iModIntro. iSplitR; [by iApply pwclV_taint | by iRight].
    - iMod (pwc_blkV_file_empty g M G B sd WA V v I sR lR k ho H b HlR Hbv
              with "Hpw Hc") as "[Hc $]".
      iModIntro. iApply (pwclV_mid with "Hp1 Hf Hc").
    - iDestruct "Hpw" as "[Hx | #HT]"; last first.
      { iModIntro. iSplitL "Hw"; [rewrite /pwclV; iRight; iRight; by iApply wildV_out |].
        by iRight. }
      iExFalso.
      iDestruct "Hx" as (ps cs s0 P) "([%Hw %Htie] & #Hpin & #HW & Htn & #Hps & #Hcs & _ & #HE)".
      rewrite Nat.add_0_r.
      iApply (wild_blk_refute k ho H v ps cs s0 I P Hw (HV _ _ HlR)
                with "Hpin HW Htn Hps Hcs HE Hw").
  Qed.

  (* ================================================================== *)
  (*  3.  THE WILD LICENCE                                               *)
  (* ================================================================== *)
  Lemma pwclV_wild_lic (k : nat) :
    secc_tok k -∗
    □ ∀ (h : list mobs) (H : LogEntryDefs.cons_hist) (ev : ConsLog.cons_ev),
        ⌜(exists b, ev = ConsLog.EvOut b) \/ (exists ws, ev = ConsLog.EvRead ws)⌝ -∗
        ⌜ConsLog.cons_ev_ok H ev⌝ -∗
        pwclV k h H ==∗ pwclV k h (ConsLog.cons_step H ev).
  Proof using B.
    iIntros "#Htok !>" (h H ev) "%Hwev %Hev Hcl". rewrite /pwclV.
    iDestruct "Hcl" as "[#HT | [(%v & Hp & Hf & _) | Hw]]"; [by iLeft | |].
    - iExFalso. iApply (secc_tok_flag0 with "Htok Hp Hf").
    - iModIntro. iRight. iRight.
      destruct Hwev as [[b ->] | [ws ->]].
      + by iApply wildV_out.
      + iDestruct (wildV_read k h H ws Hev with "Hw") as "[_ $]".
  Qed.
End pipes_wild_v.

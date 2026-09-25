(* ===================================================================== *)
(*  GenOut.v -- THE PER-CYCLE CONSOLE CLAIM, ONCE OVER A LINE MODEL      *)
(*  (app-both M3b, second cut).                                          *)
(*                                                                       *)
(*  [EchoOut.ecl], [FileOut.fecl] and [PipeOut.pecl] are one shape:      *)
(*                                                                       *)
(*    T ∨ ∃ v so, PIN k v ∗ WA k (st so)                                 *)
(*          ∗ turn_auth v (pcount so) ∗ cs_auth v (cs so)                *)
(*          ∗ ps_auth v (ps so) ∗ Elist_auth v (E so)                    *)
(*          ∗ dl_cnt v ½ |ch_dl H| ∗ dl_list_auth v (ch_dl H)            *)
(*          ∗ ⌜gcl_pure k ho so H⌝                                       *)
(*                                                                       *)
(*  with the taint [T] and the pin [PIN] of [gen_cparams] (a sub-record *)
(*  of M2's [GenLinksLine.gen_params])                                   *)
(*  and the pure claim [GenOutHist.gcl_pure].  What the applications add *)
(*  is the STATE WITNESS'S AUTHORITY [WA k st] -- at the file, the era's *)
(*  second record, the filed-ledger authority, the claim's copy of the  *)
(*  boot witness and the deed's typed witness; [emp] where no line      *)
(*  touches the file system -- so it is the one hook here.  Its laws are *)
(*  what the steps read off it: the writer's witness [gW] agrees with    *)
(*  the stage's state ([gwa_agree]), a filed state hands [gW] out again  *)
(*  to the read and the drain ([gwa_W]), and the era's first process    *)
(*  byte files the state out of the boot evidence ([gwa_file]).          *)
(*                                                                       *)
(*  The claim's whole step list, once: the steps that take nothing (the  *)
(*  taint's supply, the close, the open, the arm), the four writes, the  *)
(*  read, the echo, the byte and the drain.                               *)
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
Require Import GenOutHist.
Local Open Scope nat_scope.

(* WHAT THE CLAIM READS OF AN APPLICATION: its taint, its era pin, the
   writer's state witness, the model's laws and hooks.  A sub-record of M2's
   [GenLinksLine.gen_params]; the claim needs neither the reader's witness
   nor the head, so an application's claim can be stated below its link
   families.  This file does NOT load the link tier ([GenLinksLine],
   [LinkRec]): their projection-headed global instances made instance
   search on an unrelated [Persistent (□ …)] goal in [FileLinks] diverge. *)
Record gen_cparams {Σ : gFunctors} `{!echoOutG Σ} (M : lmodel) := MkGCP {
  gcL : lm_laws M;
  gcK : lm_hooks M;
  gcT : iProp Σ;
  gcT_pers : Persistent gcT;
  gcT_tl : Timeless gcT;
  gcPIN : nat -> era_pins -> iProp Σ;
  gcPIN_pers : forall k v, Persistent (gcPIN k v);
  gcPIN_tl : forall k v, Timeless (gcPIN k v);
  gcPIN_agree : forall k v v', gcPIN k v -∗ gcPIN k v' -∗ ⌜v = v'⌝;
  gcW : nat -> lm_st M -> iProp Σ;
  gcW_pers : forall k s, Persistent (gcW k s);
  gcW_tl : forall k s, Timeless (gcW k s);
}.
Global Arguments MkGCP {Σ _} M.
Global Arguments gcL {Σ _ M} _.
Global Arguments gcK {Σ _ M} _.
Global Arguments gcT {Σ _ M} _.
Global Arguments gcT_pers {Σ _ M} _.
Global Arguments gcT_tl {Σ _ M} _.
Global Arguments gcPIN {Σ _ M} _ _ _.
Global Arguments gcPIN_pers {Σ _ M} _ _ _.
Global Arguments gcPIN_tl {Σ _ M} _ _ _.
Global Arguments gcPIN_agree {Σ _ M} _ _ _ _.
Global Arguments gcW {Σ _ M} _ _ _.
Global Arguments gcW_pers {Σ _ M} _ _ _.
Global Arguments gcW_tl {Σ _ M} _ _ _.
#[export] Existing Instances gcT_pers gcT_tl gcPIN_pers gcPIN_tl gcW_pers gcW_tl.

(* THE STATE WITNESS'S AUTHORITY, and what the steps read off it.  [sd] is
   the instance's default state ([GenOutPure.gs_state]'s): the stage reads
   it until the era's first process byte files the boot state. *)
Record gen_wa {Σ : gFunctors} `{!echoOutG Σ} (M : lmodel) (G : gen_cparams M)
    (sd : lm_st M) := MkGWA {
  gwa : nat -> option (lm_st M) -> iProp Σ;
  gwa_tl : forall k st, Timeless (gwa k st);
  (* the writer's witness pins the state the stage reads *)
  gwa_agree : forall k st s0,
    gwa k st -∗ gcW G k s0 -∗ ⌜default sd st = s0⌝;
  (* THE STATE'S TYPED WITNESS the drain hands the ledger (at the file,
     the deed's evidence for the boot content), and a filed state hands
     the writer's witness and it out again *)
  gwa_ty : lm_st M -> iProp Σ;
  gwa_ty_pers : forall s, Persistent (gwa_ty s);
  gwa_W : forall k s0,
    gwa k (Some s0) -∗ gwa k (Some s0) ∗ gcW G k s0 ∗ gwa_ty s0;
  (* THE BOOT EVIDENCE the era's first writer holds (at the file: the era's
     second record, the boot ledger's entry, the deed's typed witness), and
     THE FILING LAW: the era's first process byte files the state out of it
     and yields the writer's witness *)
  gwa_boot : nat -> lm_st M -> iProp Σ;
  gwa_file : forall k s0,
    gwa k None -∗ gwa_boot k s0 ==∗ gwa k (Some s0) ∗ gcW G k s0;  (* ...and, where the writer's witness itself says the state is FILED
     (the file's carries the filed ledger's lower bound), that: then the
     prologue write needs no cursor premise ([gcl_step_write_pro]).  [False]
     where the witness is [emp]. *)
  gwa_strict : Prop;
  gwa_agree_strict : gwa_strict -> forall k st s0,
    gwa k st -∗ gcW G k s0 -∗ ⌜st = Some s0⌝;
  (* THE STREAM EXTENSION: the application's own ledger of the era's
     process stream ([emp] where it keeps none; the pipe's block ledger and
     round ghosts).  Every process byte grows it by that byte. *)
  (* ...and, where the state needs NO evidence (echo, the pipe: [unit]),
     that: then any first process byte may file the default state *)
  gwa_free : Prop;
  gwa_file_free : gwa_free -> forall k, gwa k None ==∗ gwa k (Some sd);
  gext : nat -> list (bv 8) -> iProp Σ;
  gext_tl : forall k l, Timeless (gext k l);
  gext_grow : forall k l b, gext k l ==∗ gext k (l ++ [b]);
}.
Global Arguments MkGWA {Σ _ M G sd}.
Global Arguments gwa {Σ _ M G sd} _ _ _.
Global Arguments gwa_tl {Σ _ M G sd} _ _ _.
Global Arguments gwa_agree {Σ _ M G sd} _ _ _ _.
Global Arguments gwa_W {Σ _ M G sd} _ _ _.
Global Arguments gwa_ty {Σ _ M G sd} _ _.
Global Arguments gwa_ty_pers {Σ _ M G sd} _ _.
Global Arguments gwa_boot {Σ _ M G sd} _ _ _.
Global Arguments gwa_file {Σ _ M G sd} _ _ _.
Global Arguments gwa_strict {Σ _ M G sd} _.
Global Arguments gwa_agree_strict {Σ _ M G sd} _ _ _ _ _.
Global Arguments gwa_free {Σ _ M G sd} _.
Global Arguments gwa_file_free {Σ _ M G sd} _ _ _.
Global Arguments gext {Σ _ M G sd} _ _ _.
Global Arguments gext_tl {Σ _ M G sd} _ _ _.
Global Arguments gext_grow {Σ _ M G sd} _ _ _ _.
#[export] Existing Instances gwa_tl gwa_ty_pers gext_tl.

(* the reader's range condition grows by the alternative a block files
   (the file's former law, once) *)
Lemma lm_alts_pre_snoc (M : lmodel) s0 I cs a :
  lm_alts_pre M s0 I cs -> length cs < nlines I ->
  lm_ok M (lm_upto M cs s0 (bodies_of I) (length cs))
    (lm_of M (bodies_of I !!! length cs)) (lm_dec M a) ->
  lm_alts_pre M s0 I (cs ++ [a]).
Proof using.
  intros H Hlt Hok i c Hc.
  assert (Hup : forall j, j <= length cs ->
            lm_upto M (cs ++ [a]) s0 (bodies_of I) j = lm_upto M cs s0 (bodies_of I) j).
  { intros j Hj. apply (lm_upto_ext M); [| intros j' _; reflexivity].
    intros j' Hj'. rewrite !list_lookup_total_alt lookup_app_l; [done | lia]. }
  destruct (decide (i < length cs)) as [Hi | Hi].
  - rewrite lookup_app_l in Hc; [| lia]. rewrite (Hup i ltac:(lia)). exact (H i c Hc).
  - rewrite lookup_app_r in Hc; [| lia].
    assert (Hie : i = length cs).
    { apply lookup_lt_Some in Hc. cbn [length] in Hc. lia. }
    subst i. rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-.
    rewrite (Hup (length cs) ltac:(lia)). by split.
Qed.

Local Lemma gop_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> i < length cs0 -> cs !!! i = cs0 !!! i.
Proof.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Local Lemma gop_prefix_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> removelast l `prefix_of` removelast l'.
Proof.
  intros Hp. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Ht : take (length l - 1) l = take (length l - 1) l').
  { destruct Hp as [z ->].
    rewrite (take_app_le l z (length l - 1)); [done | lia]. }
  rewrite !ll_removelast_take Ht. apply prefix_take_le. lia.
Qed.

Local Lemma gop_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : length l < length l').
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite ll_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

Local Lemma gop_prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

Section gen_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).

  Local Lemma gop_pending_at_nil ps cs s :
    lm_pending_at M ps cs s [] = pro_of ps.
  Proof using. exact (lm_pending_nil M ps cs s). Qed.

  (* AN EMPTY STAGE HAS AN EMPTY PROLOGUE RESOLUTION: nothing is written,
     so no shorter resolution may give a different prologue *)
  Local Lemma gop_empty_stage_ps (so : gstage M) :
    lm_ps_len_ok M sd so ->
    Forall (fun a => a < length pro_alts) (gs_ps M so) ->
    gs_E M so = [] -> gs_w M so = [] -> gs_ps M so = [].
  Proof using.
    intros [_ HpsB] Hpsb HEnil Hwnil.
    assert (Hopens : lm_ps_opens M so) by (left; by rewrite HEnil fmap_nil).
    assert (Hround : lm_ps_round M so = 0)
      by (rewrite /lm_ps_round HEnil fmap_nil nlines_nil; reflexivity).
    assert (Hproeq : pro_of (gs_ps M so) = []).
    { destruct (decide (pro_of (pro_from (lm_ps_round M so) [])
                        = pro_of (pro_from (lm_ps_round M so) (gs_ps M so))))
        as [Heq | Hne].
      - rewrite Hround in Heq. cbn [pro_from] in Heq.
        by rewrite -Heq pro_of_nil.
      - exfalso. pose proof (HpsB Hopens [] (prefix_nil _) Hne) as Hlt.
        rewrite Hwnil in Hlt. cbn [length] in Hlt. lia. }
    destruct (decide (gs_ps M so = [])) as [? | Hne]; [done | exfalso].
    pose proof (pro_of_pos (gs_ps M so) Hpsb Hne) as Hpp.
    rewrite Hproeq in Hpp. cbn [length] in Hpp. lia.
  Qed.

  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation WA := (gwa A).

  (* THE ERA'S PROCESS STREAM, as the stage records it: everything the
     programs have written this era, in order.  Its length is the cursor. *)
  Definition lm_stream (so : gstage M) : list (bv 8) :=
    lm_proc_before M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
      (snd <$> gs_E M so) ++ gs_w M so.

  Lemma lm_stream_write (so : gstage M) (b : bv 8) :
    lm_stream (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) (gs_w M so ++ [b])
                 (gs_st M so)) = lm_stream so ++ [b].
  Proof using. rewrite /lm_stream /=. by rewrite app_assoc. Qed.

  Lemma lm_stream_blk (so : gstage M) (a : nat) (b : bv 8) :
    lm_pro_pin M (gs_ps M so) (gs_cs M so) (snd <$> gs_E M so) ->
    nlines (removelast (snd <$> gs_E M so)) <= length (gs_cs M so) ->
    gs_w M so = [] ->
    lm_stream (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) [b]
                 (gs_st M so)) = lm_stream so ++ [b].
  Proof using.
    intros Hpin Hrl Hw. rewrite /lm_stream Hw /=.
    rewrite -(lm_proc_before_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
                (gs_cs M so ++ [a]) (gs_state M sd so) (snd <$> gs_E M so)
                ltac:(reflexivity) ltac:(by eexists) Hpin Hrl).
    by rewrite app_nil_r.
  Qed.

  Lemma lm_stream_pro (so : gstage M) (a : nat) (b : bv 8) :
    lm_pro_pin M (gs_ps M so) (gs_cs M so) (snd <$> gs_E M so) ->
    nlines (removelast (snd <$> gs_E M so)) <= length (gs_cs M so) ->
    lm_stream (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                 (gs_w M so ++ [b]) (gs_st M so)) = lm_stream so ++ [b].
  Proof using.
    intros Hpin Hrl. rewrite /lm_stream /=.
    rewrite -(lm_proc_before_cs_prefix M (gs_ps M so) (gs_ps M so ++ [a])
                (gs_cs M so) (gs_cs M so) (gs_state M sd so) (snd <$> gs_E M so)
                ltac:(by eexists) ltac:(reflexivity) Hpin Hrl).
    by rewrite app_assoc.
  Qed.

  Lemma lm_stream_echo (so : gstage M) (x : list mobs * bv 8) :
    gs_w M so = lm_pending M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                  (gs_E M so) ->
    lm_stream (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so ++ [x]) []
                 (gs_st M so)) = lm_stream so.
  Proof using.
    intros Hw. rewrite /lm_stream /= fmap_app /= lm_proc_before_snoc Hw.
    by rewrite /lm_proc_stream /lm_pending app_nil_r.
  Qed.

  (* ================================================================== *)
  (*  1.  THE CLAIM                                                      *)
  (* ================================================================== *)
  Definition gcl (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    ( T
    ∨ ∃ (v : era_pins) (so : gstage M),
        PIN k v
        ∗ WA k (gs_st M so)
        ∗ gext A k (lm_stream so)
        ∗ turn_auth v (lm_pcount M (gs_ps M so) (gs_cs M so)
                         (gs_state M sd so) (gs_E M so) (gs_w M so))
        ∗ cs_auth v (gs_cs M so)
        ∗ ps_auth v (gs_ps M so)
        ∗ Elist_auth v (gs_E M so)
        ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
        ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
        ∗ ⌜gcl_pure M sd k ho so H⌝)%I.

  Global Instance gcl_timeless k ho H : Timeless (gcl k ho H).
  Proof using . rewrite /gcl. apply _. Qed.

  (* ================================================================== *)
  (*  2.  THE STEPS THAT TAKE NOTHING                                    *)
  (* ================================================================== *)

  (* THE SUPPLY'S LAW: a tainted era answers any event out of its taint *)
  Lemma gcl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ gcl k ho H ==∗ gcl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. rewrite /gcl. by iLeft. Qed.

  (* FILING THE LOG ENTRY *)
  Lemma gcl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    gcl k ho H -∗ gcl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite /gcl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so)
      "(Hpin & Hwa & Hext & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Hwa Hext Htn Hcs Hps HE".
    rewrite ch_dl_close. iFrame "Hdl Hdll". iPureIntro.
    by apply (gcl_pure_close M sd k ho so H Hok Hev Hpure).
  Qed.

  (* OPENING ONE: the pure step records (K1) and the arm's echo, and
     refutes the drop and the receive flush *)
  Lemma gcl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input M (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc M h -> trace_shape h true ->
    gcl k ho H -∗ gcl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using B.
    intros Hok Hev Hd Hb Hdh Hsh. rewrite /gcl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so)
      "(Hpin & Hwa & Hext & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Hwa Hext Htn Hcs Hps HE".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
    iFrame "Hdl Hdll". iPureIntro.
    by apply (gcl_pure_open M B sd k ho so H h c cs Hok Hev Hd Hb Hdh Hsh Hpure).
  Qed.

  (* what the claim says about an open arm, read back out *)
  Lemma gcl_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    gcl k ho CH -∗ gcl k ho CH ∗ (T ∨ ⌜garm_era M k ho CH⌝).
  Proof using .
    rewrite /gcl. iIntros "[#HT | Hp]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hp" as (v so)
      "(#Hpin & Hwa & Hext & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iSplitL.
    - iRight. iExists v, so.
      iFrame "Hpin Hwa Hext Htn Hcs Hps HE Hdl Hdll". by iPureIntro.
    - iRight. iPureIntro. exact (gcl_pure_arm M sd k ho so CH Hall).
  Qed.

  (* ================================================================== *)
  (*  3.  THE WRITES                                                     *)
  (* ================================================================== *)

  (* (H) THE ERA'S HEAD WRITE: nothing is written and nothing echoed, so
     the stage is empty; the first process byte files the boot state
     ([gwa_file]) and opens the prologue at the alternative [a] the
     writer chose.  The file's former [fecl_step_write_first], once. *)
  Lemma gcl_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    lm_st_ok M s0 ->
    a < length pro_alts ->
    pro_alts !!! a !! 0 = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot A k s0 ∨ T) -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ gcW G k s0)
         ∨ T).
  Proof using .
    intros Hfok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hbt" as "[Hbt | #HT]"; last first.
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    assert (Hpb : length (lm_proc_before M (gs_ps M so) (gs_cs M so)
                            (gs_state M sd so) (snd <$> gs_E M so)) = 0
                  /\ length (gs_w M so) = 0)
      by (rewrite /lm_pcount in HP; lia).
    assert (Hwnil : gs_w M so = []) by (apply nil_length_inv; lia).
    assert (HEnil : gs_E M so = []).
    { destruct (decide (gs_E M so = [])) as [? | Hne]; [done | exfalso].
      assert (Hin : (snd <$> gs_E M so) <> []).
      { intro Hq. apply Hne. by apply fmap_nil_inv in Hq. }
      assert (Hst : 0 < nstarted (snd <$> gs_E M so)) by (by apply nstarted_pos).
      pose proof (Hpin 0 Hst) as Hlt.
      assert (Hps0 : gs_ps M so <> []).
      { intros Hq. rewrite Hq in Hlt. cbn [pro_rounds] in Hlt. lia. }
      pose proof (pro_of_pos (gs_ps M so) Hpsb Hps0) as Hpp.
      pose proof (prefix_length _ _
                    (lm_proc_before_head M (gs_ps M so) (gs_cs M so)
                       (gs_state M sd so) (snd <$> gs_E M so) Hin)) as Hle.
      rewrite gop_pending_at_nil in Hle.
      lia. }
    assert (Hf0nil : gs_st M so = None) by (apply Hf0n; by split).
    assert (Hpsnil : gs_ps M so = [])
      by exact (gop_empty_stage_ps so Hpsl Hpsb HEnil Hwnil).
    assert (Hcsnil : gs_cs M so = []).
    { apply nil_length_inv.
      destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]].
      - rewrite Hq HEnil fmap_nil nlines_nil. lia.
      - exfalso. apply Hne. split; [exact Hwnil |].
        by rewrite HEnil fmap_nil rest_of_nil. }
    iEval (rewrite Hf0nil) in "Hwa".
    iMod (gwa_file A k s0 with "Hwa Hbt") as "[Hwa #HW]".
    iMod (turn_update v 0
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            1 ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (gs_ps M so) a with "Hps") as "[Hps #Hpslb2]".
    iMod (gext_grow A k _ b with "Hext") as "Hext".
    assert (Hs0 : lm_stream so = []).
    { rewrite /lm_stream HEnil Hwnil fmap_nil lm_proc_before_nil. reflexivity. }
    rewrite Hs0.
    rewrite Hpsnil. cbn [app].
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M [a] [] [] [b] (Some s0)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : lm_pcount M [a] [] (gs_state M sd (MkGS M [a] [] [] [b] (Some s0)))
                     [] [b] = 1); last first.
      { rewrite /lm_pcount fmap_nil lm_proc_before_nil. reflexivity. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite (_ : lm_stream (MkGS M [a] [] [] [b] (Some s0)) = [] ++ [b]);
        [| by rewrite /lm_stream /= ?lm_proc_before_nil].
      rewrite Hcsnil. iFrame "Hpin Hwa Hext Hta Hcs Hps Hdl Hdll".
      rewrite HEnil. iFrame "HE".
      iPureIntro.
      apply (gcl_pure_out M sd k ho so (MkGS M [a] [] [] [b] (Some s0)) H b);
        [cbn [gs_cs]; rewrite Hcsnil; cbn [length]; lia
        | cbn [gs_E]; by rewrite HEnil | | |
        | (* (A2): an era with no input owes nothing *)
          rewrite /lm_dl_ok; cbn [gs_E gs_w]; rewrite fmap_nil lines_bytes_nil; lia
        | exact Hall0].
      + rewrite /lm_out_pure. unfold gs_state.
        cbn [gs_ps gs_cs gs_E gs_w gs_st default]. split_and!.
        * rewrite Hacc Hwnil HEnil Hpsnil !lm_D_nil. reflexivity.
        * rewrite (lm_pending_nil M [a] [] s0) pro_of_singleton.
          apply (gop_prefix_snoc_lookup [] _ b); [apply prefix_nil | exact Hhead].
        * intros j x Hx. by rewrite lookup_nil in Hx.
        * rewrite /lm_E_disc fmap_nil. split_and!; [constructor | constructor |].
          rewrite rest_of_nil. cbn [length]. rewrite /line_max. lia.
        * by apply Forall_singleton.
        * rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
        * apply lm_alts_pre_nil.
        * constructor.
        * constructor.
        * cbn [length]. lia.
        * by left.
        * constructor.
        * split; [discriminate | intros [_ Hq]; discriminate].
        * exact Hfok.
      + apply lm_cs_len_ok_intro; intros Hq; [by destruct Hq |].
        rewrite fmap_nil nlines_nil. reflexivity.
      + rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens.
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite fmap_nil nlines_nil.
        cbn [lm_pro_idx]. split.
        * cbn [pro_from pro_tail]. by case_decide.
        * intros _ ps' Hp Hne. cbn [pro_from] in Hne |- *.
          assert (Hcases : ps' = [] \/ ps' = [a]).
          { destruct ps' as [| x [| y ps'']]; [by left | | ].
            - right. destruct Hp as [z Hz]. by injection Hz as -> _.
            - exfalso. pose proof (prefix_length _ _ Hp) as Hl.
              cbn [length] in Hl. lia. }
          destruct Hcases as [-> | ->]; [| by destruct (Hne eq_refl)].
          rewrite gop_pending_at_nil pro_of_nil. cbn [length]. lia.
    - iLeft. iFrame "Ht HW Hcslb Hilb". iExact "Hpslb2".
  Qed.

  (* (W) THE ORDINARY WRITE: the writer's witness pins the state the stage
     reads ([gwa_agree]), so the byte it computes from the stream is the
     byte the claim owes.  The file's former [fecl_step_write], once. *)
  Lemma gcl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    nlines I0 <= length cs0 ->
    lm_pro_pin M ps0 cs0 I0 ->
    lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    gcW G k s0 -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gcW G k s0)
         ∨ T).
  Proof using .
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so H Hall0)]. }
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    rewrite -Hst in Hb.
    destruct (lm_write_stage_byte M ps0 (gs_ps M so) cs0 (gs_cs M so)
                (gs_state M sd so) (gs_E M so) (gs_w M so) I0 P b
                Hpsp Hpin0 Hcsp Hn HI0 HP Hb)
      as [HlenE Hnext].
    assert (Hcase : gs_w M so <> []
                    \/ rest_of (snd <$> gs_E M so) <> []
                    \/ (snd <$> gs_E M so) = []).
    { destruct (decide (gs_w M so = [])) as [Hw | Hw]; [| by left].
      destruct (decide (rest_of (snd <$> gs_E M so) = [])) as [Hm | Hm];
        [| by right; left].
      right; right.
      destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]]; last first.
      { exfalso. by apply Hne. }
      destruct (decide ((snd <$> gs_E M so) = [])) as [Hz | Hz]; [exact Hz |].
      exfalso.
      pose proof (prefix_length _ _ Hcsp) as Hlen0.
      pose proof (nlines_pos_of_rest_nil (snd <$> gs_E M so) Hz Hm) as Hpos.
      rewrite -HlenE in Hn. lia. }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (gext_grow A k _ b with "Hext") as "Hext".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v,
        (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) (gs_w M so ++ [b])
           (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                    (gs_w M so ++ [b]) (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      rewrite lm_pcount_write -HP.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite lm_stream_write.
      iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) (gs_w M so ++ [b])
                  (gs_st M so)) H b);
        [cbn [gs_cs]; lia | reflexivity | | |
        | (* (A2): the writer is now inside a block *)
          apply (lm_dl_ok_out M so (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so)));
          [reflexivity
          | cbn [gs_w]; intro Hq; by destruct (app_eq_nil _ _ Hq) as [_ Hq2]
          | exact Hcase | exact Hdlok]
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply gop_prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split; [| intros [_ Hq]; exfalso;
                    by destruct (app_eq_nil (gs_w M so) [b] Hq) as [_ Hb2]].
          (* an EMPTY stage owes nothing: its prologue resolution is empty
             ([gop_empty_stage_ps]), so there was no byte to write *)
          intros Hnone. exfalso.
          destruct (proj1 Hf0n Hnone) as [HE0 Hw0].
          pose proof (gop_empty_stage_ps so Hpsl Hpsb HE0 Hw0) as Hps0.
          rewrite /lm_pending HE0 fmap_nil gop_pending_at_nil Hps0 pro_of_nil
            lookup_nil in Hnext.
          discriminate Hnext.
        * exact Hfok0.
      + exact (lm_cs_len_ok_write M so b Hcsl Hcase).
      + exact (lm_ps_len_ok_write M sd so b Hpsl).
    - iLeft. iFrame "Ht Hpslb Hcslb Hilb HW".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE: the alternative [a] is the
     program's knowledge and this step files it; the block is read at the
     state the writer's witness pins.  The file's former [fecl_step_write_blk], once,
     with the model's no-coverage-ending clause as a premise (the pipe's
     terminal arm is its own step). *)
  Lemma gcl_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
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
    gcW G k s0 -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ gcW G k s0) ∨ T).
  Proof using B.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hterm Hhead.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so H Hall0)]. }
    rewrite -Hst in HPeq.
    assert (Hstream : lm_proc_before M ps0 cs0 (gs_state M sd so) I0
                      = lm_proc_before M (gs_ps M so) (gs_cs M so)
                          (gs_state M sd so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so)
               (gs_state M sd so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (HlenE : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (lm_pending_at_nonnil_at M (gcK G) (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hne0 Hr0)
        as Hne1.
      assert (Hlen1 : 1 <= length (lm_pending_at M (gs_ps M so) (gs_cs M so)
                                     (gs_state M sd so) I0)).
      { destruct (lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hwnil : gs_w M so = []).
    { assert (Hz : length (gs_w M so) = 0).
      { rewrite /lm_pcount in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = gs_cs M so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    assert (Hidx0 : lm_at M (gs_cs M so ++ [a]) (nlines I0 - 1) = lm_dec M a).
    { rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. reflexivity. }
    (* the block below the last line does not read the new entry, so the
       state the block starts in is the writer's own *)
    assert (Hfst : lm_upto M (gs_cs M so ++ [a]) s0 (bodies_of I0) (nlines I0 - 1)
                   = lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1)).
    { apply lm_upto_cs_ext. intros j Hj.
      rewrite Hcs0 !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (Hpend : lm_pending M (gs_ps M so) (gs_cs M so ++ [a])
                      (gs_state M sd so) (gs_E M so) !! 0 = Some b).
    { rewrite /lm_pending HlenE /lm_pending_at.
      rewrite decide_False; [| exact Hne0]. rewrite decide_True; [| exact Hr0].
      rewrite /lm_cont_at Hidx0 Hst Hfst.
      rewrite lookup_app_l; [exact Hhead |].
      destruct (lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
                  (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a))
        as [| z zs] eqn:Hz;
        [ exfalso; revert Hz; apply (lmh_cont_nonnil (gcK G)); by left
        | cbn; lia ]. }
    assert (Hpinq : lm_pro_pin M (gs_ps M so) (gs_cs M so ++ [a])
                      (snd <$> gs_E M so)).
    { intros qq Hqq. rewrite lm_pro_idx_app_le; [by apply Hpin |].
      rewrite HlenE (nstarted_rest_nil I0 Hr0) in Hqq. rewrite Hq. lia. }
    assert (HD : lm_D M (gs_ps M so) (gs_cs M so ++ [a]) (gs_state M sd so)
                   (gs_E M so)
                 = lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                     (gs_E M so)).
    { symmetry. apply (lm_D_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
                         (gs_cs M so ++ [a]) (gs_state M sd so) (gs_E M so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpceq : lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                      (gs_E M so) [b]
                    = lm_pcount M (gs_ps M so) (gs_cs M so ++ [a])
                        (gs_state M sd so) (gs_E M so) [b]).
    { apply (lm_pcount_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
               (gs_cs M so ++ [a]) (gs_state M sd so) (gs_E M so) [b]);
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpc2 : lm_pcount M (gs_ps M so) (gs_cs M so ++ [a])
                     (gs_state M sd so) (gs_E M so) [b] = S P).
    { rewrite -Hpceq /lm_pcount HlenE -Hstream. cbn [length]. lia. }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (gs_cs M so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    iMod (gext_grow A k _ b with "Hext") as "Hext".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) [b]
                    (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                    (gs_E M so) [b] (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite (lm_stream_blk so a b Hpin ltac:(rewrite HlenE Hrl0 Hq; lia) Hwnil).
      iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) [b]
                  (gs_st M so)) H b);
        [cbn [gs_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | |
        | (* (A2) AT A BLOCK'S FIRST BYTE, paid by the writer's own bound
             on the DELIVERED input, which is the whole era's input *)
          apply (lm_dl_ok_out_full M so (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                           (gs_E M so) [b] (gs_st M so)));
          [reflexivity | cbn [gs_w]; discriminate | by rewrite HlenE |];
          pose proof (prefix_length _ _ HI0dl) as Hlp;
          rewrite !length_fmap in Hlp; rewrite HlenE; lia
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                      (gs_E M so) [b] (gs_st M so))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (gop_prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * apply lm_alts_pre_snoc; [exact Hcsb' | rewrite HlenE Hq; lia |].
          rewrite HlenE Hq Hst -Hcs0. exact Halt.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * apply Forall_app. split; [exact Hnofk | by apply Forall_singleton].
        * split; [| intros [_ Hq2]; discriminate].
          intros Hnone. exfalso. destruct (proj1 Hf0n Hnone) as [HE0 _].
          apply Hne0. by rewrite -HlenE HE0.
        * exact Hfok0.
      + apply (lm_cs_len_ok_blk M so a b);
          [by rewrite HlenE | by rewrite HlenE | exact Hwnil | exact Hcsl].
      + apply (lm_ps_len_ok_blk M B sd so a b);
          [by rewrite HlenE | by rewrite HlenE | by rewrite HlenE | exact Hpsl].
    - iLeft. rewrite Hcs0. iFrame "Ht Hilb Hcslb2 Hpslb HW".
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE: init's own
     knowledge of which alternative its restart loop is taking, filed into
     the claim.  The file's former [fecl_step_write_pro], once.  ONE PREMISE MORE than
     the file's: [0 < P] (the writer is past the era's head), OR the
     instance's witness forces filing ([gwa_strict], the file's case), OR
     the state needs no evidence and this byte files it ([gwa_free], echo's
     and the pipe's -- whose era opens with a prologue byte, not a head
     write).  The byte always leaves the stage FILED at the state it reads. *)
  Lemma gcl_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
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
    gcW G k s0 -∗
    gcl k ho CH ==∗
      gcl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ gcW G k s0) ∨ T).
  Proof using .
    intros HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    iAssert (⌜0 < P \/ gs_st M so <> None \/ gwa_free A⌝)%I as %HP0'.
    { destruct HP0 as [HP0 | [Hstr | Hfree]]; [by iLeft | | by iRight; iRight].
      iDestruct (gwa_agree_strict A Hstr with "Hwa HW") as %Hs. iRight. iLeft. iPureIntro. by rewrite Hs. }
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so CH Hall0)]. }
    rewrite -Hst in HPeq.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    (* the writer's own list is bounded, and its round index is the claim's *)
    assert (Hpsb0 : Forall (fun x => x < length pro_alts) ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2. by apply Forall_app in Hpsb2 as [? _]. }
    assert (Hlk : forall j, j < nlines I0 -> gs_cs M so !!! j = cs0 !!! j)
      by (intros j Hj; apply (gop_lta_prefix cs0 (gs_cs M so) j Hcsp); lia).
    assert (Hidxeq : lm_pro_idx M (gs_cs M so) (nlines I0)
                     = lm_pro_idx M cs0 (nlines I0))
      by exact (lm_pro_idx_ext M (gs_cs M so) cs0 (nlines I0) Hlk (nlines I0)
                  ltac:(lia)).
    rewrite -Hidxeq in Hnd.
    assert (HopenC : I0 = [] \/
              lm_panic M (lm_at M (gs_cs M so) (nlines I0 - 1)) = true).
    { destruct (decide (I0 = [])) as [Hz | Hne0]; [by left | right].
      pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
      destruct Hopen as [Hz | H3]; [by destruct (Hne0 Hz) |].
      rewrite /lm_at (Hlk (nlines I0 - 1) ltac:(lia)). exact H3. }
    assert (Hstream : lm_proc_before M ps0 cs0 (gs_state M sd so) I0
                      = lm_proc_before M (gs_ps M so) (gs_cs M so)
                          (gs_state M sd so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so)
               (gs_state M sd so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (Hpend0 : lm_pending_at M ps0 cs0 (gs_state M sd so) I0
                     = lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0)
      by exact (lm_pending_at_cs_ext M ps0 cs0 (gs_cs M so) (gs_state M sd so)
                  I0 Hcsp Hdiv).
    assert (Hpmono : lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0
                     `prefix_of` lm_pending_at M (gs_ps M so) (gs_cs M so)
                                   (gs_state M sd so) I0)
      by (by apply lm_pending_at_ps_mono).
    assert (HPval : P = length (lm_proc_before M ps0 cs0 (gs_state M sd so) I0)
                        + length (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)).
    { rewrite HPeq /lm_proc_stream.
      by rewrite (length_app (lm_proc_before M ps0 cs0 (gs_state M sd so) I0)
                    (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)). }
    rewrite /lm_pcount in HP.
    (* the era's input IS [I0] *)
    assert (HlenE : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done | exfalso].
      assert (Hnei : I0 <> (snd <$> gs_E M so))
        by (intros Hq; apply Hne; symmetry; exact Hq).
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hnei) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (prefix_length _ _ Hpmono) as Hlp. rewrite -Hpend0 in Hlp.
      assert (Hpe : lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0
                    = lm_pending_at M (gs_ps M so) (gs_cs M so)
                        (gs_state M sd so) I0).
      { apply prefix_length_eq; [exact Hpmono | rewrite -Hpend0; lia]. }
      pose proof (lm_pending_at_round_det M (gcL G) ps0 (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 Hr0 HopenC Hpe) as Hpro.
      assert (Hdone : pro_done (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                        (gs_ps M so))).
      { apply pro_from_done.
        apply Hpinf.
        exact (nstarted_strict I0 (snd <$> gs_E M so) HI0 Hnei). }
      apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hlenw : length (gs_w M so)
                    = length (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)).
    { rewrite HlenE -Hstream in HP. lia. }
    assert (Hweq : gs_w M so = lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0).
    { assert (Hw1 : gs_w M so
                    `prefix_of` lm_pending_at M (gs_ps M so) (gs_cs M so)
                                  (gs_state M sd so) I0)
        by (rewrite -HlenE; exact Hwpre).
      assert (Hlen2 : length (gs_w M so)
                      = length (lm_pending_at M ps0 (gs_cs M so)
                                  (gs_state M sd so) I0))
        by (rewrite -Hpend0; exact Hlenw).
      destruct (prefix_weak_total (gs_w M so)
                  (lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0)
                  (lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0)
                  Hw1 Hpmono) as [Hq | Hq].
      - apply prefix_length_eq; [exact Hq | lia].
      - symmetry. apply prefix_length_eq; [exact Hq | lia]. }
    assert (Hopens : lm_ps_opens M so).
    { rewrite /lm_ps_opens HlenE.
      destruct HopenC as [Hz | H3]; [by left | right; by split]. }
    pose proof Hpsl as [HpsA HpsB].
    assert (Hproeq : pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                     = pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                         (gs_ps M so))).
    { destruct (decide (pro_of (pro_from
                          (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                        = pro_of (pro_from
                            (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))))
        as [Heq | Hne]; [exact Heq | exfalso].
      pose proof (HpsB Hopens ps0 Hpsp) as Hlt.
      rewrite /lm_ps_round HlenE in Hlt.
      pose proof (Hlt Hne) as Hlt2. rewrite Hweq in Hlt2. lia. }
    assert (Hndps : ~ pro_done (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                      (gs_ps M so))).
    { intros Hdone. apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hproeq; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hround0 : lm_pro_idx M (gs_cs M so) (nlines I0) <= pro_rounds ps0).
    { rewrite Hidxeq.
      by apply (lm_pro_pin_round_le M ps0 cs0 I0 Hr0 Hopen Hpin0). }
    assert (Hpseq : gs_ps M so = ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2.
      assert (Hzb : Forall (fun x => x < length pro_alts) z)
        by (by apply Forall_app in Hpsb2 as [_ ?]).
      pose proof Hproeq as Hpe2. rewrite Hz in Hpe2.
      rewrite (pro_from_app_le _ ps0 z Hround0) in Hpe2.
      assert (Hzn : z = []).
      { apply (pro_of_open_app_inj _ z Hnd Hzb). by rewrite -Hpe2. }
      rewrite Hz Hzn. by rewrite app_nil_r. }
    assert (HRle : lm_pro_idx M (gs_cs M so) (nlines I0) <= pro_rounds (gs_ps M so))
      by (rewrite Hpseq; exact Hround0).
    assert (Hshape2 : lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                        (gs_state M sd so) I0
                      = lm_wr_pre I0
                        ++ pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                             (gs_ps M so ++ [a])))
      by (apply (lm_pending_at_round_pre M (gcL G)); [exact Hr0 | exact HopenC]).
    assert (Hshape : lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0
                     = lm_wr_pre I0
                       ++ pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                            (gs_ps M so)))
      by (apply (lm_pending_at_round_pre M (gcL G)); [exact Hr0 | exact HopenC]).
    assert (Hpendb : lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                       (gs_state M sd so) I0 !! length (gs_w M so) = Some b).
    { pose proof (pro_of_snoc_head
                    (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                    a b Hndps Hhead) as Hph.
      assert (Hpre3' :
        (lm_wr_pre I0
         ++ (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
             ++ [b]))
        `prefix_of` lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                      (gs_state M sd so) I0).
      { rewrite Hshape2 (pro_from_snoc_le _ (gs_ps M so) a HRle).
        by apply prefix_app. }
      assert (Hwl : length (gs_w M so)
                    = length (lm_wr_pre I0)
                      + length (pro_of (pro_from
                          (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so)))).
      { rewrite Hweq -Hpseq Hshape.
        by rewrite (length_app (lm_wr_pre I0)
                      (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                         (gs_ps M so)))). }
      rewrite Hwl. eapply prefix_lookup_Some; [| exact Hpre3'].
      rewrite (lookup_app_shift (lm_wr_pre I0)).
      replace (length (pro_of (pro_from
                 (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))))
        with (length (pro_of (pro_from
                 (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))) + 0)
        by lia.
      by rewrite (lookup_app_shift
                    (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                       (gs_ps M so)))). }
    assert (Hcase : gs_w M so <> []
                    \/ rest_of (snd <$> gs_E M so) <> []
                    \/ (snd <$> gs_E M so) = []).
    { destruct (decide (I0 = [])) as [Hz | Hnz].
      { right; right. by rewrite HlenE. }
      left. rewrite Hweq -Hpseq.
      exact (lm_pending_at_nonnil_at M (gcK G) (gs_ps M so) (gs_cs M so)
               (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hnz Hr0). }
    assert (HD : lm_D M (gs_ps M so ++ [a]) (gs_cs M so) (gs_state M sd so)
                   (gs_E M so)
                 = lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so) (gs_E M so)).
    { symmetry. apply (lm_D_ps_ext M (gs_ps M so) (gs_ps M so ++ [a]) (gs_cs M so)
                         (gs_state M sd so) (gs_E M so)); [by eexists | exact Hpinf]. }
    assert (Hpceq : lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                      (gs_E M so) (gs_w M so ++ [b])
                    = lm_pcount M (gs_ps M so ++ [a]) (gs_cs M so)
                        (gs_state M sd so) (gs_E M so) (gs_w M so ++ [b])).
    { apply (lm_pcount_cs_prefix M (gs_ps M so) (gs_ps M so ++ [a]) (gs_cs M so)
               (gs_cs M so) (gs_state M sd so) (gs_E M so) (gs_w M so ++ [b]));
        [by eexists | reflexivity | exact Hpinf |].
      pose proof (prefix_length _ _ Hcsp) as Hle2.
      rewrite HlenE Hrl0. lia. }
    assert (Hpc2 : lm_pcount M (gs_ps M so ++ [a]) (gs_cs M so) (gs_state M sd so)
                     (gs_E M so) (gs_w M so ++ [b]) = S P).
    { rewrite -Hpceq /lm_pcount (length_app (gs_w M so) [b]). cbn [length]. lia. }
    (* the stage is not empty: an empty one has an empty prologue, so the
       cursor would be at zero -- and the writer is past the head *)
    (* the stage is FILED after this byte: it was already, or the cursor
       says the era is past its head, or the instance files its default *)
    iAssert (|==> WA k (Some (gs_state M sd so)))%I with "[Hwa]" as ">Hwa".
    { rewrite /gs_state. destruct (gs_st M so) as [s1 |] eqn:Hstn;
        [by iModIntro |].
      destruct HP0' as [HP0' | [Hs | Hfree]]; [exfalso | by destruct Hs |].
      - destruct (proj1 Hf0n eq_refl) as [HE0 Hw0].
        pose proof (gop_empty_stage_ps so Hpsl Hpsb HE0 Hw0) as Hps0.
        rewrite HE0 Hw0 Hps0 fmap_nil lm_proc_before_nil in HP.
        cbn [length] in HP. lia.
      - iApply (gwa_file_free A Hfree k with "Hwa"). }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(rewrite /lm_pcount; lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (gs_ps M so) a with "Hps") as "[Hps #Hpslb2]".
    iMod (gext_grow A k _ b with "Hext") as "Hext".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                    (gs_w M so ++ [b]) (Some (gs_state M sd so))).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                    (gs_E M so) (gs_w M so ++ [b]) (Some (gs_state M sd so)))
                   = gs_state M sd so); [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite (_ : lm_stream (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                                 (gs_w M so ++ [b]) (Some (gs_state M sd so)))
                   = lm_stream so ++ [b]);
        [| exact (lm_stream_pro so a b Hpinf
                    ltac:(pose proof (prefix_length _ _ Hcsp); rewrite HlenE Hrl0; lia))].
      iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                  (gs_w M so ++ [b]) (Some (gs_state M sd so))) CH b);
        [cbn [gs_cs]; lia | reflexivity | | |
        | (* (A2): the writer is now inside the block's prologue round *)
          apply (lm_dl_ok_out M so (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                      (gs_E M so) (gs_w M so ++ [b]) (Some (gs_state M sd so))));
          [reflexivity
          | cbn [gs_w]; intro Hq; by destruct (app_eq_nil _ _ Hq) as [_ Hq2]
          | exact Hcase | exact Hdlok]
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                      (gs_E M so) (gs_w M so ++ [b]) (Some (gs_state M sd so)))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * apply gop_prefix_snoc_lookup.
          { etrans; [exact Hwpre |]. rewrite /lm_pending.
            by apply lm_pending_at_ps_mono; eexists. }
          { rewrite /lm_pending HlenE. exact Hpendb. }
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app.
          split; [exact Hpsb | by rewrite Forall_singleton].
        * apply (lm_pro_pin_mono M (gs_ps M so) (gs_ps M so ++ [a]));
            [by eexists | exact Hpinf].
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split; [discriminate |].
          intros [_ Hq]. exfalso.
          by destruct (app_eq_nil (gs_w M so) [b] Hq) as [_ Hb2].
        * exact Hfok0.
      + apply (lm_cs_len_ok_write M
                 (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so) (gs_w M so)
                    (Some (gs_state M sd so))) b); [exact Hcsl | exact Hcase].
      + apply (lm_ps_len_ok_pro M sd so a b);
          [ rewrite /lm_ps_round HlenE; exact HRle
          | rewrite /lm_ps_round HlenE; exact Hndps
          | rewrite /lm_pending HlenE Hweq; by rewrite -Hpseq
          | exact (conj HpsA HpsB) ].
    - iLeft. rewrite -Hpseq. iFrame "Ht Hpslb2 Hcslb Hilb HW".
  Qed.

  (* ================================================================== *)
  (*  4.  THE READ                                                       *)
  (* ================================================================== *)

  Local Lemma gop_cs_lb_weaken (v : era_pins) (l l' : list nat) :
    l' `prefix_of` l -> cs_lb v l -∗ cs_lb v l'.
  Proof using .
    intros Hp. rewrite /cs_lb. iIntros "H".
    iApply (own_mono with "H"). by apply mono_list_lb_mono.
  Qed.

  (* the read's window is a prefix of the echoed list: a disciplined entry
     is never an edit byte *)
  Lemma gin_read_pure (k : nat) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (cs0 : list nat) :
    read_ok pops dl ws -> gin_pure M k pops dl cs0 ->
    (dl ++ ws) `prefix_of` echoed pops
    /\ gin_pure M k pops (dl ++ ws) cs0
    /\ nlines (snd <$> (dl ++ ws)) <= S (length cs0).
  Proof using B.
    intros Hread (Hlog & Hdisc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd & Hall).
    assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
    { intros e He.
      assert (Hends : obs_ends_in Uart0 (open_seg (le_hist e)) (le_byte e)).
      { apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
      assert (Hcin : le_byte e ∈ ins (open_seg (le_hist e))).
      { destruct Hends as [h0 Hh0]. rewrite Hh0 ins_app ins_in.
        apply elem_of_app. right. apply elem_of_list_here. }
      by destruct (lm_disc_drop_byte M B _ _ (Hdisc e He) Hcin) as (_ & _ & ?). }
    assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
      by (eapply read_window_prefix;
          [exact Hlog | exact Hread | exact Hnoer | exact Hdlp]).
    split; [exact Hpref |]. split.
    - rewrite /gin_pure. split_and!;
        [exact Hlog | exact Hdisc | exact Hstamp | exact Hpref | exact Hidx
         | exact Hbyte | exact Hbnd | exact Hall].
    - etrans; [| exact Hbnd]. apply nlines_prefix, epu_fmap_prefix, Hpref.
  Qed.

  (* THE READ.  The reader's receipt carries the window's facts and, past
     an empty window, the writer's witness at the filed state ([gwa_W]),
     with the claim's choice list cut to the window's own line count.
     The file's former [fecl_step_read], once. *)
  Lemma gcl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    PIN k v -∗ dl_cnt v (1/2) n -∗ gcl k ho CH ==∗
      gcl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ ((T ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)
           ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
           ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws)
              `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
           ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜lm_E_disc M (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜forall x : list mobs * bv 8,
                x ∈ LogEntryDefs.ch_dl CH ++ ws -> obs_boots x.1 = k⌝
           ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           ∗ ⌜lm_disc_input M (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (s0 : lm_st M),
                  cs_lb v cs0 ∗ ps_lb v ps0 ∗ gcW G k s0
                  ∗ ⌜nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                     <= S (length cs0)⌝
                  ∗ turn_lb v (length (lm_proc_before M ps0 cs0 s0
                                 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
                  ∗ ⌜lm_rd_stage M ps0 cs0 s0
                       (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝)).
  Proof using B.
    intros Hread. iIntros "#Hpinr Hdlr Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft |]. iLeft. by iFrame "Hdlr". }
    iDestruct "Hp" as (v2 so)
      "(#Hpin & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gcPIN_agree G with "Hpin Hpinr") as %->.
    iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hin as Hin2.
    destruct Hin2 as (_ & _ & Hbt & _ & Hidx & Hbyte & Hbnd0 & _).
    destruct (gin_read_pure k (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH)
                ws (gs_cs M so) Hread Hin) as (Hpref & Hp' & Hbnd').
    assert (Hboots : forall x : list mobs * bv 8,
              x ∈ LogEntryDefs.ch_dl CH ++ ws -> obs_boots x.1 = k).
    { intros x Hx.
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) x
                  (elem_of_prefix _ _ _ Hx Hpref)) as (e & He & _ & <-).
      exact (Hbt e He). }
    assert (HEpre : (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                    `prefix_of` (snd <$> gs_E M so)).
    { rewrite (gcl_pure_E M sd k ho so CH Hall0) /ch_E.
      etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
      rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log CH))).
      apply epu_fmap_prefix. by apply prefix_app_r. }
    assert (Hdi : lm_disc_input M (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    { apply (lm_disc_input_prefix M B _ (snd <$> gs_E M so) HEpre).
      by destruct Hpure as (_ & _ & _ & Hd & _). }
    pose proof (gcl_pure_rd_stage M sd k ho so CH Hall0) as Hrd.
    pose proof Hrd as (Hpsb & Hcsb' & Hpinf & Hbd).
    (* the reader's own list: the claim's, cut to its own line count *)
    set (Iw := (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    set (q := nlines Iw).
    set (csq := take q (gs_cs M so)).
    assert (Hqle : nlines (removelast Iw) <= length csq).
    { rewrite /csq length_take.
      assert (H1 : nlines (removelast Iw) <= q)
        by (apply nlines_prefix, gop_removelast_prefix).
      assert (H2 : nlines (removelast Iw) <= length (gs_cs M so)).
      { etrans; [| exact Hbd].
        apply nlines_prefix, gop_prefix_removelast, HEpre. }
      lia. }
    assert (Hagree : forall j, j < q -> csq !!! j = gs_cs M so !!! j).
    { intros j Hj. rewrite /csq !list_lookup_total_alt.
      destruct (decide (j < length (gs_cs M so))) as [Hl | Hl].
      - rewrite lookup_take; [done | lia].
      - rewrite (lookup_ge_None_2 (gs_cs M so) j ltac:(lia)).
        rewrite (lookup_ge_None_2 (take q (gs_cs M so)) j);
          [done | rewrite length_take; lia]. }
    assert (Hqbnd : q <= S (length csq)).
    { rewrite /csq length_take.
      destruct (decide (q <= length (gs_cs M so))) as [Hl | Hl]; [lia |].
      rewrite /q /Iw. lia. }
    assert (Hpbq : lm_proc_before M (gs_ps M so) csq (gs_state M sd so) Iw
                   = lm_proc_before M (gs_ps M so) (gs_cs M so)
                       (gs_state M sd so) Iw).
    { apply (lm_proc_before_ext M). intros J HJ Hne.
      apply (lm_pending_at_cs_ext M (gs_ps M so) csq (gs_cs M so)
               (gs_state M sd so) J).
      - rewrite /csq. apply prefix_take.
      - etrans; [| exact Hqle].
        apply nlines_prefix, (gop_prefix_of_removelast J Iw HJ Hne). }
    assert (Hrdq : lm_rd_stage M (gs_ps M so) csq (gs_state M sd so) Iw).
    { rewrite /lm_rd_stage. split_and!; [exact Hpsb | | | exact Hqle].
      - intros i c Hc.
        assert (Hci : gs_cs M so !! i = Some c)
          by (rewrite /csq in Hc; by apply lookup_take_Some in Hc as [? _]).
        assert (Hiq : i < q).
        { apply lookup_lt_Some in Hc. rewrite /csq length_take in Hc. lia. }
        destruct (Hcsb' i c Hci) as [_ Hok].
        split; [exact Hiq |].
        destruct (bodies_of_prefix Iw (snd <$> gs_E M so) HEpre) as [z Hz].
        assert (Hbod : forall j, j < q ->
                  bodies_of (snd <$> gs_E M so) !!! j = bodies_of Iw !!! j).
        { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
            [done | rewrite /q /nlines in Hj; lia]. }
        rewrite (Hbod i Hiq) in Hok.
        rewrite (lm_upto_ext M csq (gs_cs M so) (gs_state M sd so) (bodies_of Iw)
                   (bodies_of (snd <$> gs_E M so)) i
                   ltac:(intros j Hj; apply Hagree; lia)
                   ltac:(intros j Hj; symmetry; apply Hbod; lia)).
        exact Hok.
      - intros q' Hq'.
        assert (Hq'q : q' <= q).
        { pose proof (nstarted_le_S Iw). rewrite /q. lia. }
        rewrite (lm_pro_idx_ext M csq (gs_cs M so) q
                   ltac:(intros j Hj; apply Hagree; lia) q' Hq'q).
        apply Hpinf. pose proof (nstarted_prefix Iw (snd <$> gs_E M so) HEpre).
        lia. }
    iAssert (WA k (gs_st M so)
             ∗ (⌜gs_st M so = None⌝
                ∨ ∃ s1 : lm_st M, ⌜gs_st M so = Some s1⌝ ∗ gcW G k s1))%I
      with "[Hwa]" as "[Hwa #Hf0w]".
    { destruct (gs_st M so) as [s1 |] eqn:Hf0.
      - iDestruct (gwa_W A k s1 with "Hwa") as "(Hwa & #Hlb & _)".
        iFrame "Hwa". iRight. iExists s1.
        iSplitR; [by iPureIntro | iExact "Hlb"].
      - iFrame "Hwa". iLeft. by iPureIntro. }
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (gop_cs_lb_weaken v (gs_cs M so) csq
                 ltac:(rewrite /csq; apply prefix_take) with "Hcslb") as "#Hcslbq".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iDestruct (turn_lb_get with "Hta") as "#Htlb".
    iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n
            (n + length ws) with "Hdl Hdlr") as "[Hdl Hdlr]".
    iMod (dl_list_auth_grow v (LogEntryDefs.ch_dl CH) ws with "Hdll")
      as "[Hdll #Hdllb]".
    (* the reader sees the era's state only once it has been filed, and a
       NONEMPTY window means the era has echoed a byte, so it has *)
    iAssert (⌜ws = []⌝ ∨ ⌜exists s0 : lm_st M, gs_st M so = Some s0⌝)%I as %Hf0c.
    { destruct (decide (ws = [])) as [-> | Hne]; [by iLeft |].
      iRight. destruct (gs_st M so) as [s0 |] eqn:Hf0;
        [iPureIntro; by exists s0 |].
      iExFalso. iPureIntro.
      destruct Hpure as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0n & _).
      destruct (proj1 Hf0n Hf0) as [HEn _]. apply Hne.
      assert (Hz : Iw = []).
      { apply prefix_nil_inv. rewrite /Iw. rewrite HEn fmap_nil in HEpre.
        exact HEpre. }
      rewrite /Iw fmap_app in Hz. apply app_eq_nil in Hz as [_ Hz].
      by apply fmap_nil_inv in Hz. }
    iModIntro. iSplitL "Hta Hcs Hps HE Hdl Hdll Hwa Hext".
    { rewrite /gcl. iRight. iExists v, so.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite length_app Hdleq. iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll".
      iPureIntro. exact (gcl_pure_read M sd k ho so CH ws Hpref Hall0). }
    iRight. iFrame "Hdlr".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; exact Hboots |].
    iSplitR.
    { iApply (inp_lb_of_dl_lb v (LogEntryDefs.ch_dl CH ++ ws) _
                (reflexivity _)). iExact "Hdllb". }
    iSplitR; [by iPureIntro |].
    destruct Hf0c as [-> | [s0 Hf0]]; [by iLeft |].
    iRight. iExists csq, (gs_ps M so), s0.
    iFrame "Hcslbq Hpslb".
    iSplitR.
    { iDestruct "Hf0w" as "[%Hn | (%s1 & %Hs1 & Hlb)]".
      - rewrite Hf0 in Hn. discriminate.
      - rewrite Hf0 in Hs1. injection Hs1 as <-. iExact "Hlb". }
    iSplitR; [iPureIntro; exact Hqbnd |].
    iSplitR.
    { assert (Hst : gs_state M sd so = s0) by (rewrite /gs_state Hf0; reflexivity).
      assert (Hle2 : length (lm_proc_before M (gs_ps M so) csq s0 Iw)
                     <= lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                          (gs_E M so) (gs_w M so)).
      { rewrite -Hst in Hpbq |- *. rewrite /lm_pcount Hpbq.
        pose proof (prefix_length _ _
                      (lm_proc_before_prefix M (gs_ps M so) (gs_cs M so)
                         (gs_state M sd so) Iw (snd <$> gs_E M so) HEpre)) as Hlp.
        lia. }
      iApply (turn_lb_weaken with "Htlb"). exact Hle2. }
    iPureIntro.
    rewrite (_ : s0 = gs_state M sd so); [exact Hrdq | by rewrite /gs_state Hf0].
  Qed.

  (* ================================================================== *)
  (*  5.  THE ECHO                                                       *)
  (* ================================================================== *)

  (* D4 AT A SEGMENT READ BELOW ITS LAST BYTE: a coverage-ending
     continuation cannot be mergeable at a line strictly below the input's
     last, since D4 puts such a line at the input's very end *)
  Lemma lm_d4_nomerge_snoc (cs : list nat) (s : lm_st M) (I : list (bv 8))
      (b : bv 8) :
    lm_d4 M cs s (I ++ [b]) ->
    forall i, i < nlines I ->
      (exists c, lm_ok M (lm_upto M cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i)) c
                 /\ lm_term M c = true) ->
      ~ lm_merge M (lm_of M (bodies_of I !!! i))
          (lm_cont M (lm_upto M cs s (bodies_of I) i)
             (lm_of M (bodies_of I !!! i)) (lm_at M cs i)).
  Proof using.
    intros Hd4 i Hi Hex Hm.
    destruct (bodies_of_prefix I (I ++ [b]) ltac:(by eexists)) as [z Hz].
    assert (Hbod : forall j, j < nlines I ->
              bodies_of (I ++ [b]) !!! j = bodies_of I !!! j).
    { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hj; lia]. }
    assert (Hup : lm_upto M cs s (bodies_of (I ++ [b])) i
                  = lm_upto M cs s (bodies_of I) i).
    { apply (lm_upto_ext M); [done | intros j Hj; apply Hbod; lia]. }
    rewrite -Hup -(Hbod i Hi) in Hm. rewrite -Hup -(Hbod i Hi) in Hex.
    assert (Hle : nlines I <= nlines (I ++ [b])) by (apply nlines_prefix; by eexists).
    destruct (Hd4 i ltac:(lia) Hex Hm) as [Hn Hr].
    destruct (decide (b = wl_nl)) as [-> | Hne].
    - rewrite nlines_snoc_nl in Hn. lia.
    - rewrite (rest_of_snoc_other I b Hne) in Hr.
      apply app_eq_nil in Hr as [_ Hr]. discriminate.
  Qed.

  (* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT, at the
     cycle's own boot state and at the COMPLETE LINES of the input before
     that byte, with D4 read there (the file's former lemma and
     [PipeOutPure.disc_seg_p'_pt_last] once) *)
  Lemma lm_disc_seg'_pt_last (s : lm_st M) (seg : list mobs) (c : bv 8) :
    lm_disc_seg' M s seg -> obs_ends_in Uart0 seg c ->
    exists ps' cs' : list nat,
      lm_pro_ok M ps' cs' (nlines (done_of (removelast (ins seg))))
      /\ lm_alts_ok M s (done_of (removelast (ins seg))) cs'
      /\ (forall i, i < nlines (done_of (removelast (ins seg))) ->
            (exists a, lm_ok M
                          (lm_upto M cs' s (bodies_of (done_of (removelast (ins seg)))) i)
                          (lm_of M (bodies_of
                          (done_of (removelast (ins seg))) !!! i)) a
                       /\ lm_term M a = true) ->
            ~ lm_merge M (lm_of M (bodies_of (done_of (removelast (ins seg))) !!! i))
                (lm_cont M
                 (lm_upto M cs' s (bodies_of (done_of (removelast (ins seg)))) i)
                 (lm_of M (bodies_of (done_of (removelast (ins seg))) !!! i))
                 (lm_at M cs' i)))
      /\ lm_sess M ps' cs' s (done_of (removelast (ins seg)))
           `prefix_of` obs_wire Uart0 seg.
  Proof using.
    intros [Hd (ps & cs & Hao & Hd4 & Hall)] [seg0 ->].
    assert (Hip : seg0 ∈ in_pres (seg0 ++ [ObsUartIn Uart0 c])).
    { rewrite in_pres_in. apply elem_of_app. right. apply elem_of_list_here. }
    destruct (Hall _ Hip) as [Hok Hpt]. rewrite /lm_disc_pt in Hpt.
    rewrite ins_app ins_in epu_removelast_snoc.
    rewrite ins_app ins_in in Hao Hd4.
    rewrite nlines_done bodies_of_done.
    set (n := nlines (ins seg0)).
    assert (Hle : n <= nlines (ins seg0 ++ [c]))
      by (apply nlines_prefix; by eexists).
    assert (Hlen : length cs = nlines (ins seg0 ++ [c]))
      by exact (lm_alts_ok_len M s _ _ Hao).
    assert (Htk : forall j, j < n -> take n cs !!! j = cs !!! j).
    { intros j Hj. rewrite !list_lookup_total_alt lookup_take; [done | lia]. }
    exists ps, (take n cs). split_and!.
    - destruct Hok as [HF Hlt]. split; [exact HF |].
      rewrite (lm_pro_idx_ext M (take n cs) cs n Htk n ltac:(lia)). exact Hlt.
    - pose proof (lm_alts_ok_prefix M s (done_of (ins seg0)) (ins seg0 ++ [c]) cs
                    ltac:(etrans; [apply done_of_prefix | by eexists]) Hao) as Hp.
      rewrite nlines_done in Hp. exact Hp.
    - intros i Hi Hex.
      rewrite /lm_at (Htk i Hi).
      rewrite (lm_upto_cs_ext M (take n cs) cs s (bodies_of (ins seg0)) i
                 ltac:(intros j Hj; apply Htk; lia)) in Hex |- *.
      exact (lm_d4_nomerge_snoc cs s (ins seg0) c Hd4 i Hi Hex).
    - rewrite (lm_sess_cs_ext M ps (take n cs) cs s (done_of (ins seg0))
                 ltac:(rewrite nlines_done; intros j Hj; apply Htk; lia)).
      etrans; [exact Hpt |]. rewrite obs_wire_app. by eexists.
  Qed.

  (* F2: the process output owed at this stage is complete.  That the
     echoed list holds every earlier input of the era is the KERNEL's FIFO
     discipline and a premise; that the output is complete is the
     discipline's, read at [LineWords.done_of] (the file's former F2 lemma once) *)
  Lemma lm_next_input_of_complete (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) (w W : list (bv 8)) (h : list mobs)
      (c : bv 8) (m : nat) :
    lm_E_disc M E -> E_index E ->
    (forall x, x ∈ E -> hist_ext x.1 h) ->
    obs_ends_in Uart0 h c ->
    length (ins h) = m ->
    length E = m - 1 ->
    w `prefix_of` lm_pending M ps cs s E ->
    lm_sess M ps cs s (done_of (take (m - 1) (ins h))) `prefix_of` W ->
    W `prefix_of` (lm_D M ps cs s E ++ w) ->
    w = lm_pending M ps cs s E.
  Proof using B.
    intros HEb HEi Hnew Hends Hm HlenE Hw Hlow Hup.
    assert (Hprefix : forall j x, E !! j = Some x -> x.1 `prefix_of` h).
    { intros j x Hx. apply (Hnew x). by eapply elem_of_list_lookup_2. }
    pose proof (E_length_le_hist E h HEi Hprefix) as Hle.
    pose proof (E_bytes_of_hist E h HEi Hprefix Hle) as HEq.
    rewrite HlenE in HEq.
    destruct (decide (rest_of (snd <$> E) = [])) as [Hr | Hr].
    - apply (anti_symm list_relations.prefix); [exact Hw |].
      eapply (prefix_app_cancel (lm_D M ps cs s E)).
      rewrite (lm_D_pending_sess M B ps cs s E HEb).
      etrans; [| etrans; [exact Hlow | exact Hup] ].
      rewrite -HEq (done_of_rest_nil (snd <$> E) Hr). reflexivity.
    - assert (Hne : (snd <$> E) <> []).
      { intro Hq. rewrite Hq rest_of_nil in Hr. by apply Hr. }
      assert (Hp : lm_pending M ps cs s E = []).
      { rewrite /lm_pending /lm_pending_at decide_False; [| exact Hne].
        by rewrite decide_False. }
      rewrite Hp in Hw. rewrite Hp. by apply prefix_nil_inv.
  Qed.

  (* THE ECHO'S STEP: the discipline's witness is compared with the
     claim's at ITS OWN boot state (the model's determinacy theorem at two
     states), the claim's resolution PADDED to a full one first, and (K1)
     with (A1) make the era's input the segment's minus the byte being
     echoed.  The file's former [fecl_step_echo], once; D4's two side conditions are
     discharged by the claim's no-coverage-ending clause (and the pad's)
     and by the discipline's own D4 below its last byte. *)
  Lemma gcl_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    lm_disc M h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    length (LogEntryDefs.ch_log CH) + 1 = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0) ->
    gcl k ho CH ==∗
      gcl k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using B.
    intros Hdisc Hsh Hk Hends Hwire Hord HK1 Harm. subst k.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. rewrite /gcl. by iLeft. }
    iDestruct "Hp" as (v so)
      "(#Hpin & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & Halle).
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log CH)) = gs_E M so).
    { rewrite HEtie /ch_E Harm ch_arm_E_open app_nil_r. reflexivity. }
    (* the byte's own facts *)
    destruct (lm_disc_open_seg M h Hsh Hdisc) as (sdd & Hsdok & Hd').
    pose proof (proj1 Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (lm_disc_seg'_pt_last sdd (open_seg h) c Hd' Hends')
      as (ps' & cs' & Hok' & Hao' & Hnm' & Hlow').
    assert (Hup : obs_wire Uart0 (open_seg h)
                  `prefix_of` (lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                                 (gs_E M so) ++ gs_w M so))
      by (rewrite -Hacc; exact Hwire).
    (* the era's state HAS been filed: otherwise nothing is on the wire and
       the discipline's own transcript, which begins with a settled
       prologue, would be empty *)
    assert (Hf0ne : gs_st M so <> None).
    { intros Hn. destruct (proj1 Hf0n Hn) as [HEn Hwn].
      assert (Hacc0 : lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                        (gs_E M so) ++ gs_w M so = [])
        by (rewrite HEn Hwn lm_D_nil; reflexivity).
      rewrite Hacc0 in Hup. apply prefix_nil_inv in Hup.
      rewrite Hup in Hlow'. apply prefix_nil_inv in Hlow'.
      destruct Hok' as [Hps'b Hlt'].
      exact (lm_sess_nonnil M ps' cs' sdd (done_of (removelast (ins (open_seg h))))
               Hps'b ltac:(apply pro_done_rounds; lia) Hlow'). }
    (* the same-cycle prefixes of E, and the index facts *)
    assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (gs_E M so)).
    { rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed (LogEntryDefs.ch_log CH) !! j) as [y |] eqn:Hy;
        [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
      assert (Hyin : y ∈ echoed (LogEntryDefs.ch_log CH))
        by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) y Hyin)
        as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      - rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
      - rewrite -Hye. cbn [fst]. exact (Hstamp e He).
      - exact Hsh. }
    assert (Hpl : forall j x, gs_E M so !! j = Some x -> x.1 `prefix_of` open_seg h)
      by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hprefixes Hx)).
    assert (Hoi : length (gs_E M so) = length (echoed (LogEntryDefs.ch_log CH)))
      by (by rewrite -Hseg seg_of_length).
    (* (K1) + (A1): the log is complete below this input, and every entry
       of it is echoed -- the era's input IS the segment's minus the byte *)
    assert (Hcnt : length (gs_E M so) = length (ins (open_seg h)) - 1)
      by (rewrite Hoi (echoed_all_len _ Halle); lia).
    assert (Hbytes : (snd <$> gs_E M so)
                     = take (length (gs_E M so)) (ins (open_seg h)))
      by (apply (E_bytes_of_hist (gs_E M so) (open_seg h) Hidx Hpl); lia).
    assert (HI : removelast (ins (open_seg h)) = (snd <$> gs_E M so)).
    { rewrite Hbytes epu_removelast_take.
      replace (length (ins (open_seg h)) - 1) with (length (gs_E M so)) by lia.
      reflexivity. }
    assert (Hnew' : forall x, x ∈ gs_E M so -> hist_ext x.1 (open_seg h)).
    { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
      destruct (Hidx jj x Hj) as [Hxe Hxlen].
      pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
      apply lookup_lt_Some in Hj.
      split; [exact Hpx |].
      destruct Hpx as [z Hz]. destruct z as [| aa z'].
      - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
      - rewrite Hz length_app /=. lia. }
    (* the stage's resolution, padded to a full one *)
    assert (Hrl : nlines (removelast (snd <$> gs_E M so)) <= length (gs_cs M so)).
    { pose proof (gcl_pure_rd_stage M sd _ ho so CH Hall0) as (_ & _ & _ & Hb).
      exact Hb. }
    assert (Hlast : nlines (snd <$> gs_E M so) <= length (gs_cs M so)
                    \/ gs_w M so = []).
    { destruct (lm_cs_len_ok_inv M so Hcsl) as [[[Hw _] _] | [_ Hq]];
        [by right | left; lia]. }
    set (csP := lm_alts_pad M (gcK G) (snd <$> gs_E M so) (gs_cs M so)).
    destruct (lm_stage_sess_pad M (gcK G) B (gs_ps M so) (gs_cs M so)
                (gs_state M sd so) (gs_E M so) (gs_w M so)
                Hcsb' Hrl Hlast Hbyte Hpinf Hwpre)
      as (HokP & HpinP & HDP & HwP & HstP).
    (* the discipline's bound, moved to the claim's own resolution *)
    assert (Hdi1 : lm_disc_input M (done_of (removelast (ins (open_seg h))))).
    { apply (lm_disc_input_prefix M B _ (ins (open_seg h))); [| exact Hdseg].
      etrans; [apply done_of_prefix | apply gop_removelast_prefix]. }
    assert (Hbelow : lm_sess M ps' cs' sdd (done_of (removelast (ins (open_seg h))))
                     `prefix_of` lm_sess M (gs_ps M so) csP (gs_state M sd so)
                       (snd <$> gs_E M so)).
    { etrans; [exact Hlow' |]. etrans; [exact Hup |]. exact HstP. }
    (* D4's first side: the claim's padded list names no coverage-ending
       alternative on the input's lines *)
    assert (HlenP : length csP = nlines (snd <$> gs_E M so)).
    { apply lm_alts_pad_length. exact (lm_alts_pre_le M _ _ _ Hcsb'). }
    assert (Hd4c : forall i, i < nlines (done_of (removelast (ins (open_seg h)))) ->
              lm_term M (lm_at M csP i) = true ->
              S i = nlines (snd <$> gs_E M so) /\ rest_of (snd <$> gs_E M so) = []).
    { intros i Hi Ht. exfalso. revert Ht.
      rewrite nlines_done HI in Hi.
      destruct (decide (i < length (gs_cs M so))) as [Hlt | Hge].
      - rewrite /lm_at /csP /lm_alts_pad list_lookup_total_alt lookup_app_l;
          [| lia].
        rewrite -list_lookup_total_alt.
        destruct (lookup_lt_is_Some_2 (gs_cs M so) i Hlt) as [a Ha].
        rewrite (list_lookup_total_correct _ _ _ Ha).
        by rewrite (Forall_lookup_1 _ _ _ _ Hnofk Ha).
      - rewrite /csP (lm_alts_pad_term M (gcK G) (snd <$> gs_E M so) (gs_cs M so) i
                        ltac:(lia) Hi).
        done. }
    destruct (lm_sess_prefix_det M (gcL G) (gs_ps M so) ps' csP cs'
                (gs_state M sd so) sdd
                (done_of (removelast (ins (open_seg h)))) (snd <$> gs_E M so)
                Hpsb Hok' HokP Hao' HpinP Hbyte Hdi1 Hfok0 Hsdok Hd4c Hnm' Hbelow)
      as (_ & HokPres & Heq & _).
    assert (Hlow : lm_sess M (gs_ps M so) csP (gs_state M sd so)
                     (done_of (removelast (ins (open_seg h))))
                   `prefix_of` obs_wire Uart0 (open_seg h))
      by (rewrite -Heq; exact Hlow').
    (* F2 at the padded resolution *)
    assert (HupP : obs_wire Uart0 (open_seg h)
                   `prefix_of` (lm_D M (gs_ps M so) csP (gs_state M sd so)
                                  (gs_E M so) ++ gs_w M so))
      by (rewrite -HDP; exact Hup).
    pose proof (lm_next_input_of_complete (gs_ps M so) csP (gs_state M sd so)
                  (gs_E M so) (gs_w M so) (obs_wire Uart0 (open_seg h))
                  (open_seg h) c (length (ins (open_seg h)))
                  Hbyte Hidx Hnew' Hends' eq_refl ltac:(lia) HwP
                  ltac:(rewrite -ll_removelast_take; exact Hlow) HupP)
      as HweqP.
    (* ...and back at the claim's own resolution *)
    assert (Hweq : gs_w M so = lm_pending M (gs_ps M so) (gs_cs M so)
                                 (gs_state M sd so) (gs_E M so)).
    { destruct (decide (nlines (snd <$> gs_E M so) <= length (gs_cs M so)))
        as [Hle | Hgt].
      - rewrite HweqP /lm_pending /csP.
        symmetry. apply (lm_pending_at_cs_ext M (gs_ps M so) (gs_cs M so)
                           (lm_alts_pad M (gcK G) (snd <$> gs_E M so) (gs_cs M so))
                           (gs_state M sd so) (snd <$> gs_E M so));
          [apply lm_alts_pad_prefix | exact Hle].
      - exfalso.
        destruct (lm_cs_len_ok_inv M so Hcsl) as [[[Hwn Hr] Hq] | [_ Hq]];
          [| lia].
        assert (HEn : (snd <$> gs_E M so) = []).
        { apply (lm_pending_nil_inv M (gcK G) (gs_ps M so) csP (gs_state M sd so)
                   (gs_E M so));
            [exact (lm_alts_pre_of_alts_ok M _ _ _ HokP) | exact Hr
            | by rewrite -HweqP Hwn]. }
        apply Hf0ne. apply (proj2 Hf0n).
        split; [by apply fmap_nil_inv in HEn | exact Hwn]. }
    assert (Hrnd : lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))
                   < pro_rounds (gs_ps M so)).
    { destruct HokPres as [_ Hres]. rewrite nlines_done HI in Hres.
      rewrite (lm_alts_pad_pro_idx M (gcK G) B (snd <$> gs_E M so) (gs_cs M so)
                 (nlines (snd <$> gs_E M so)) ltac:(lia)) in Hres.
      exact Hres. }
    (* the two laws at the new entry *)
    assert (Hidx2 : E_index (gs_E M so ++ [(open_seg h, c)])).
    { intros jj y Hy.
      destruct (decide (jj < length (gs_E M so))) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. by apply Hidx. }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (gs_E M so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [fst snd].
      split; [exact Hends' | lia]. }
    assert (Hpl2 : forall j x, (gs_E M so ++ [(open_seg h, c)]) !! j = Some x ->
                     x.1 `prefix_of` open_seg h).
    { intros jj y Hy.
      destruct (decide (jj < length (gs_E M so))) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. exact (Hpl jj y Hy). }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (gs_E M so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [fst]. reflexivity. }
    assert (Hdisc2 : lm_E_disc M (gs_E M so ++ [(open_seg h, c)]))
      by exact (lm_E_disc_of_hist M B _ (open_seg h) Hidx2 Hpl2 Hdseg).
    pose proof (lm_cs_len_ok_echo M (gcK G) sd so (open_seg h, c) Hcsb' Hweq Hcsl)
      as Hcsl2.
    assert (Hpin2 : lm_pro_pin M (gs_ps M so) (gs_cs M so)
                      ((snd <$> gs_E M so) ++ [c])).
    { intros q Hq. rewrite ll_nstarted_snoc in Hq.
      destruct (decide (q < nstarted (snd <$> gs_E M so))) as [Hq2 | Hq2];
        [by apply Hpinf |].
      assert (Hqe : q = nlines (snd <$> gs_E M so)).
      { pose proof (nlines_le_nstarted (snd <$> gs_E M so)). lia. }
      subst q. exact Hrnd. }
    iMod (Elist_auth_grow v (gs_E M so) (open_seg h, c) with "HE")
      as "[HE #HElb2]".
    iModIntro. rewrite /gcl. iRight.
    iExists v,
      (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so ++ [(open_seg h, c)]) []
         (gs_st M so)).
    cbn [gs_ps gs_cs gs_E gs_w gs_st].
    rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so)
                                  (gs_E M so ++ [(open_seg h, c)]) [] (gs_st M so))
                 = gs_state M sd so); [| reflexivity].
    rewrite (lm_pcount_echo M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (open_seg h, c) (gs_w M so) Hweq).
    rewrite ch_dl_byte.
    rewrite (lm_stream_echo so (open_seg h, c) Hweq).
    iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll". iPureIntro.
    apply (gcl_pure_byte M sd (obs_boots h) ho h so
             (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so ++ [(open_seg h, c)]) []
                (gs_st M so))
             CH (echo_of c) h c Harm eq_refl);
      [cbn [gs_cs]; lia | reflexivity | | |
      | (* (A2): the echo leaves the writer owing a whole block *)
        exact (lm_dl_ok_echo M (gcK G) sd so (open_seg h, c) (LogEntryDefs.ch_dl CH)
                 Hcsb' Hweq Hdlok)
      | exact Hall0].
    - rewrite /lm_out_pure.
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so)
                                    (gs_E M so ++ [(open_seg h, c)]) [] (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
      + rewrite Hacc Hweq (lm_D_app M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                             (gs_E M so) (open_seg h, c)).
        cbn [snd]. by rewrite app_nil_r app_assoc.
      + apply prefix_nil.
      + exact Hidx2.
      + exact Hdisc2.
      + exact Hpsb.
      + rewrite fmap_app. cbn [snd fmap list_fmap]. exact Hpin2.
      + apply (lm_alts_pre_mono M _ (snd <$> gs_E M so)); [| exact Hcsb'].
        rewrite fmap_app. by eexists.
      + rewrite Forall_app. split; [exact Hdsc |].
        rewrite Forall_singleton. cbn [fst]. exact Hdseg.
      + rewrite Forall_app. split; [exact Hprefixes |].
        rewrite Forall_singleton. cbn [fst]. reflexivity.
      + rewrite length_app. cbn [length]. lia.
      + by right.
      + exact Hnofk.
      + split.
        * intros Hq. by destruct (Hf0ne Hq).
        * intros [Hq _]. exfalso.
          by destruct (app_eq_nil (gs_E M so) [(open_seg h, c)] Hq) as [_ Hb].
      + exact Hfok0.
    - exact Hcsl2.
    - exact (lm_ps_len_ok_echo M sd so (open_seg h, c) Hpsl).
  Qed.

  (* ...AND THE BYTE, which takes NOTHING: the arm is the history's own
     field, and everything the step needs is inside the claim and the
     event's premises.  The file's former [fecl_step_byte], once. *)
  Lemma gcl_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    gcl k ho CH ==∗ gcl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using B.
    intros Hok Hev. iIntros "Hcl".
    iDestruct (gcl_arm with "Hcl") as "[Hcl [#HT | %Hera]]".
    { iModIntro. rewrite /gcl. by iLeft. }
    pose proof Hev as Hev0.
    destruct Hev0 as (a & Ha & Hlk). destruct a as [[[ha ca] csa] ja].
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Hlk.
    rewrite /garm_era Ha in Hera.
    destruct Hera as (Hdseg & Hbts & Hdisc & Hsh & Hw & Hcsa0 & HK1).
    subst ha.
    destruct Hok as [_ Harm]. rewrite Ha in Harm.
    cbn [from_option LogEntryDefs.ca_hist LogEntryDefs.ca_byte
         LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Harm.
    destruct Harm as (Hends & Hecho & _ & Hord & Hwire).
    assert (Hshape : csa = [echo_of ca] /\ ja = 0 /\ b = echo_of ca).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]].
      - exfalso. rewrite Hnil in Hlk. by rewrite lookup_nil in Hlk.
      - rewrite Hech in Hlk.
        destruct ja as [| j']; cbn in Hlk; [| by rewrite lookup_nil in Hlk].
        injection Hlk as <-. by split_and!.
      - exfalso.
        assert (Hcin : ca ∈ ins (open_seg ho)).
        { destruct (open_seg_ends_in ho ca Hends) as [h0 Hh0].
          rewrite Hh0 ins_app ins_in.
          apply elem_of_app. right. apply elem_of_list_here. }
        destruct (lm_disc_drop_byte M B _ ca Hdseg Hcin) as (_ & _ & Hno).
        rewrite Hno in Herase. discriminate. }
    destruct Hshape as (Hcsa & Hja & Hb).
    subst b. rewrite Hcsa Hja in Ha.
    iApply (gcl_step_echo k ho ca ho CH Hdisc Hsh Hbts Hends Hwire Hord HK1 Ha
              with "Hcl").
  Qed.

  (* ================================================================== *)
  (*  6.  THE DRAIN                                                      *)
  (* ================================================================== *)

  (* WHAT THE DRAIN HANDS THE LEDGER: the trace fact at the era's own
     state, the state's typed witness, and the writer's witness at it
     (which carries the era's pin, and how the ledger recognises a later
     drain of the SAME era).  The state IS filed, because the wire is not
     empty: a stage that has not filed has written nothing. *)
  Definition gdrain_ret (k : nat) (seg : list mobs) : iProp Σ :=
    (T ∨ ∃ s0 : lm_st M,
          ⌜lm_good_out M s0 seg⌝ ∗ ⌜lm_st_ok M s0⌝ ∗ gwa_ty A s0 ∗ gcW G k s0)%I.

  Lemma gcl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    gcl k ho CH -∗ gcl k ho CH ∗ gdrain_ret k seg.
  Proof using B.
    intros Hsh Hk Hpre Hins Hwire Hne. subst k. rewrite /gcl /gdrain_ret.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    - iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iDestruct "Hp" as (v so)
        "(#Hpin & Hwa & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
      pose proof Hall as Hall2.
      destruct Hall2 as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie & _).
      destruct Hpure as (Hacc & Hwp & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                         & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
      assert (Hsome : gs_st M so = Some (gs_state M sd so)).
      { rewrite /gs_state. destruct (gs_st M so) as [sx |] eqn:Hfx; [reflexivity |].
        exfalso. destruct (proj1 Hf0n eq_refl) as [HE0 Hw0].
        assert (Hz : LogEntryDefs.ch_acc CH = []).
        { rewrite Hacc HE0 Hw0 lm_D_nil. reflexivity. }
        apply Hne, prefix_nil_inv. rewrite -Hz. exact Hwire. }
      iEval (rewrite Hsome) in "Hwa".
      iDestruct (gwa_W A _ (gs_state M sd so) with "Hwa") as "(Hwa & #HW & #Hty)".
      iEval (rewrite -Hsome) in "Hwa".
      iSplitL "Hwa Hext Hta Hcs Hps HE Hdl Hdll".
      { iRight. iExists v, so.
        iFrame "Hpin Hwa Hext Hta Hcs Hps HE Hdl Hdll". by iPureIntro. }
      iRight. iExists (gs_state M sd so).
      iFrame "Hty HW".
      iSplitR; [| by iPureIntro].
      iPureIntro.
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
      apply (lm_good_out_of_stage M (gcK G) B (gs_ps M so) (gs_cs M so)
               (gs_state M sd so) (gs_E M so) (gs_w M so) seg Hpsb).
      + apply (lm_alts_pre_mono M _ (snd <$> gs_E M so)); [exact Hbytes | exact Hcsb'].
      + pose proof (gcl_pure_rd_stage M sd _ ho so CH Hall) as (_ & _ & _ & Hb).
        exact Hb.
      + destruct (lm_cs_len_ok_inv M so Hcsl) as [[[Hw _] _] | [_ Hq]];
          [by right | left; lia].
      + exact Hbyte.
      + exact Hpinf.
      + exact Hwp.
      + rewrite -Hacc. exact Hwire.
      + exact Hbytes.
  Qed.
End gen_out.

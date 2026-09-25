(* PipeOut.v -- THE PIPELINE APPLICATION'S CONSOLE CLAIM, ITS TAG, ITS
   TURN, ITS STEPS AND ITS LEDGER.

   Design of record: claude-notes/design/app-pipe.md sections 4.1 and 5.5,
   lane PIPE-STAGE, deliverable 2.  This is [EchoOut.v]'s Iris half at
   [PipeDisc.sessp]: the same merged console claim over one
   [ConsLog.cons_hist], the same per-era authorities, the same ledger shape.

   WHAT IS REUSED AND WHAT IS NEW.

   - THE FIXED PART IS THE ECHO APPLICATION'S, unchanged: [EchoOut.echo_gn]
     (the taint counter's gname and the era map's).  Upstream's FILE
     application needed a SECOND gname for its own per-era map; a pipe dies
     with its era, so there is no second map, no second per-era record, no
     boot value and no typed witness.  [pipe_cl_all] IS [AppEcho.echo_cl]
     and [pipe_birth_all] IS [AppEcho.echo_birth].
   - THE STAGE RECORD IS [EchoOut.ostage], REUSED VERBATIM.  Nothing is
     added per era, so [postage] below is a definitional alias and every
     one of [EchoOut]'s [cs_len_ok] lemmas applies unchanged -- only
     [cs_len_ok_echo], which reads the block a completed line owes, needs a
     twin ([cs_len_ok_p_echo]), because the "no alternative prints nothing"
     fact is the pipeline model's.
   - THE PROLOGUE LENGTH LAW NEEDS A TWIN ([ps_len_ok_p]): it names
     [pro_idx] and the round-opening test [cs !!! _ = 3], which at this
     model are [PipeDisc.pro_idx_p] and [palt_panic (palt_at cs _)].
   - THE GHOST ALGEBRA IS IMPORTED WHOLE: [EchoOut.era_pins], [era_pin],
     [turn]/[turn_auth]/[turn_lb], [cs_auth]/[cs_lb], [ps_auth]/[ps_lb],
     [Elist_auth]/[Elist_lb]/[inp_lb], [dl_cnt], [eturn], [pin_map],
     [era_full] and the whole [ch_E] layer (which is about the console log
     and knows no discipline).  [pturn] IS [EchoOut.eturn].
   - THE RANGE CONDITION is [PipeOutPure.alts_pre_p] where the echo claim
     carried [Forall (fun i => i < 4) (o_cs so)].  Out of range [!!!] reads
     [0], which decodes to [PipeDisc.PEcho 0], and after PIPE-MODEL-2's
     ruling [palt_ok (LPipe _) (PEcho 0)] is FALSE -- so no total condition
     works and the pointwise one plus [alts_pad_p] is the route, exactly as
     at the file application.

   NOTHING IS TAKEN AS A HYPOTHESIS: the ledger's counter reads
   [PipeDiscDec.disc_p_dec] (lane PIPE-DEC).  Per that lane's warning, no
   [decide] on this file's path is ever EVALUATED -- every ledger step
   rewrites with [decide_ext] at one of [PipeOutPure]'s closure laws, and
   the birth step rewrites with [decide_True] at [PipeDisc.disc_p_nil]. *)
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
Require Import PipeDisc.
Require Import PipeDiscDec.      (* [disc_p_dec]: the ledger's counter *)
Require Import PipeOutPure.
Require Import PipeBothPure.
Require Import EchoOut.           (* the ghost algebra, [ch_E] and its laws *)
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.     (* the stream equations at [pipe_lm] *)
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.            (* the claim once *)
Require Import PipeHooks.         (* [pipe_hooks] *)
Require Import AppEcho.           (* [echo_fixed], [echo_taint], [echo_cl] *)
Local Open Scope list_scope.

(* ====================================================================== *)
(*  0.  THE FIXED PART, AND THE SECOND PER-ERA RECORD (lane PIPE-2W-2)     *)
(*                                                                        *)
(*  The pipeline round's block is written by TWO processes (design 4.3d),  *)
(*  so its alternative cannot be filed in [cs] at the block's first byte   *)
(*  and the claim must read the block off a LEDGER instead.  That ledger   *)
(*  is per ERA and its authority needs a gname that outlives every era, so *)
(*  -- exactly as [FileOut.file_gn] does for the file application's boot   *)
(*  state -- the RECORD's fixed part is [pipe_gn], [AppEcho]'s paired with *)
(*  it, and [pgn_cl g] reads the echo half.  Nothing in [AppEcho] moves.   *)
(*                                                                        *)
(*  WHAT THE LEDGER HOLDS: the era's PROCESS BYTES, all of them --         *)
(*  [pstream so] below, whose length is exactly the era's cursor [turn].   *)
(*  That is what makes a writer's lower bound EXACT (a prefix of equal     *)
(*  length is the list), which is the tie design 4.3d's family needs and   *)
(*  the reason the ledger is not per ROUND: a per-round ledger would still *)
(*  have to prove the writer's round IS the claim's, and the era-wide one  *)
(*  gets that from [turn] alone.                                           *)
(* ====================================================================== *)

Record pipe_era := MkPEra {
  pe_blk : gname;   (* mono_list (bv 8), carried at [EchoOut.eo_El]'s camera:
                       the era's process bytes in wire order *)
  pe_cur : gname;   (* ghost_var (nat * gname * bool): THE ROUND IN PROGRESS
                       -- its index, its own block ledger's gname, and the
                       TERMINAL FLAG (lane PIPE-STAGE-4, design SS4.3m).  One half is
                       in the claim and one in the round's family, so
                       [ghost_var_agree] forces a writer's round and ledger
                       to be the claim's: a family minted for an EARLIER
                       round cannot exist beside the claim (lane PIPE-2W-3,
                       design 4.3e; PIPE-2W-2 showed neither the byte
                       ledger nor [turn] excludes one). *)
}.

Record pipe_gn := MkPipeGn {
  pgn_cl  : echo_fixed;   (* AppEcho's: the taint counter and the era map *)
  pgn_era : gname;        (* ghost_map nat pipe_era: the era's BYTE LEDGER *)
}.

Class pipeOutG (Σ : gFunctors) := PipeOutG {
  pog_era : ghost_mapG Σ nat pipe_era;
  pog_cur : ghost_varG Σ (nat * gname * bool);
}.
#[global] Existing Instances pog_era pog_cur.

Definition pipeOutΣ : gFunctors :=
  #[ ghost_mapΣ nat pipe_era; ghost_varΣ (nat * gname * bool) ].

Global Instance subG_pipeOutΣ {Σ} : subG pipeOutΣ Σ -> pipeOutG Σ.
Proof. solve_inG. Qed.

(* a byte, as the era's echoed-list camera carries it: no new functor is
   added by the ledger *)
Definition blk_enc (b : bv 8) : list mobs * bv 8 := ([], b).

Lemma blk_enc_inj (b c : bv 8) : blk_enc b = blk_enc c -> b = c.
Proof using. rewrite /blk_enc. by intros [= <-]. Qed.

Lemma blk_fmap_prefix_inv (l1 l2 : list (bv 8)) :
  (blk_enc <$> l1) `prefix_of` (blk_enc <$> l2) -> l1 `prefix_of` l2.
Proof using.
  revert l2. induction l1 as [| b l1 IH]; intros l2 Hp; [apply prefix_nil |].
  destruct l2 as [| c l2].
  { exfalso. rewrite fmap_nil in Hp. apply prefix_length in Hp.
    rewrite fmap_cons in Hp. cbn [length] in Hp. lia. }
  rewrite !fmap_cons in Hp.
  pose proof (prefix_cons_inv_1 _ _ _ _ Hp) as Hhd.
  pose proof (prefix_cons_inv_2 _ _ _ _ Hp) as Htl.
  rewrite (blk_enc_inj b c Hhd). by apply prefix_cons, IH.
Qed.

(* ====================================================================== *)
(*  1.  THE STAGE RECORD, REUSED                                           *)
(*                                                                        *)
(*  [EchoOut.ostage] with NOTHING ADDED: a pipe dies with its era, so the  *)
(*  stage is the echo application's four components exactly.  The alias is *)
(*  definitional, which is what lets every [cs_len_ok] lemma apply.        *)
(* ====================================================================== *)
Definition postage : Type := ostage.

(* THE ERA'S PROCESS BYTES, as the stage records them: everything the
   programs have put on the wire in this era, in order.  Its LENGTH is
   [pcount_p], i.e. the era's cursor, which is what ties a writer's lower
   bound to the claim's own list. *)
Definition pstream (so : postage) : list (bv 8) :=
  proc_before_p (o_ps so) (o_cs so) (snd <$> o_E so) ++ o_w so.

Lemma pstream_0 : pstream ostage0 = [].
Proof using.
  rewrite /pstream /ostage0. cbn [o_ps o_cs o_E o_w].
  by rewrite fmap_nil proc_before_p_nil.
Qed.

(* A WRITE inside a block appends its byte and moves nothing else. *)
Lemma pstream_write (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) (b : bv 8) :
  pstream (MkO ps cs E (w ++ [b])) = pstream (MkO ps cs E w) ++ [b].
Proof using. rewrite /pstream. cbn [o_ps o_cs o_E o_w]. by rewrite app_assoc. Qed.

(* ...and the FILING write, which moves BOTH: the choice list grows by the
   round's code and the block by the prompt's first byte. *)
Lemma pstream_blk_w (ps cs : list nat) (E : list (list mobs * bv 8))
    (a : nat) (wq : list (bv 8)) (b : bv 8) :
  pro_pin_p ps cs (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs)%nat ->
  pstream (MkO ps (cs ++ [a]) E (wq ++ [b]))
  = pstream (MkO ps cs E wq) ++ [b].
Proof using.
  intros Hpin Hn. rewrite /pstream. cbn [o_ps o_cs o_E o_w].
  rewrite -(proc_before_p_cs_prefix ps ps cs (cs ++ [a]) (snd <$> E)
              ltac:(reflexivity) ltac:(by eexists) Hpin Hn).
  by rewrite app_assoc.
Qed.

(* ====================================================================== *)
(*  2.  THE PURE HISTORY LAYER                                             *)
(*                                                                        *)
(*  [EchoOut]'s [eout_pure], [ps_len_ok], [ein_pure], [rd_stage],          *)
(*  [ch_arm_era] and [ecl_pure] at the PIPELINE discipline.  [ch_E] itself *)
(*  is reused verbatim, and so is [cs_len_ok].                             *)
(* ====================================================================== *)

(* NO FILED ROUND IS THE TERMINAL FORK-FAILURE ONE (lane PIPE-MODEL-3).
   A round whose [fork1] failed NEVER files its code -- the stray never
   signals completion -- so the claim's [cs] is free of [PForkS], and
   that is exactly discipline rule D4's unprimed reading, which
   [PipeDisc.sessp_prefix_det] asks of the claim at every step that
   compares it with the discipline's own resolution. *)
Definition cs_nofork (so : postage) : Prop :=
  Forall (fun c => palt_isforkS (palt_of c) = false) (o_cs so).

Definition pout_pure (k : nat) (ho : list mobs) (so : postage)
    (acc : list (bv 8)) : Prop :=
  acc = D_p (o_ps so) (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending_p (o_ps so) (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_disc_p (o_E so)
  /\ Forall (fun a => (a < length pro_alts)%nat) (o_ps so)
  /\ pro_pin_p (o_ps so) (o_cs so) (snd <$> o_E so)
  /\ alts_pre_p (snd <$> o_E so) (o_cs so)
  /\ Forall (fun x => disc_seg_p x.1) (o_E so)
  /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (o_E so)
  /\ (length (o_E so) <= length (ins (open_seg ho)))%nat
  /\ (o_E so = [] \/ obs_boots ho = k)
  /\ cs_nofork so.

Lemma pout_pure_0 k ho : pout_pure k ho ostage0 [].
Proof using.
  rewrite /pout_pure /ostage0. cbn [o_ps o_cs o_E o_w]. split_and!.
  - rewrite D_p_nil. done.
  - rewrite pending_p_nil. apply prefix_nil.
  - intros j x Hx. by rewrite lookup_nil in Hx.
  - rewrite /E_disc_p fmap_nil. exact disc_input_p_nil.
  - constructor.
  - rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
  - rewrite fmap_nil. apply alts_pre_p_nil.
  - constructor.
  - constructor.
  - cbn [length]. lia.
  - by left.
  - rewrite /cs_nofork. cbn [o_cs]. constructor.
Qed.

(* ---- the choice list's length law is [EchoOut.cs_len_ok] VERBATIM; only
       the ECHO move needs a twin, because the fact that a completed line's
       block is nonempty is the PIPELINE model's ---- *)
Lemma cs_len_ok_p_echo (so : postage) (x : list mobs * bv 8) :
  alts_pre_p (snd <$> o_E so) (o_cs so) ->
  o_w so = pending_p (o_ps so) (o_cs so) (o_E so) ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []).
Proof using.
  intros Hao Hw Hc.
  assert (Hq : length (o_cs so) = nlines (snd <$> o_E so)).
  { destruct (cs_len_ok_inv so Hc) as [[[Hw' Hm] Hq] | [_ Hq]]; [| exact Hq].
    pose proof (pending_p_nil_inv (o_ps so) (o_cs so) (o_E so)
                  Hao Hm ltac:(by rewrite -Hw)) as Hz.
    rewrite Hz in Hq |- *. rewrite nlines_nil in Hq |- *. lia. }
  apply cs_len_ok_intro; rewrite (fmap_snd_snoc (o_E so) x) Hq.
  - intros [_ Hm]. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + rewrite Hx nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other _ _ Hx) in Hm.
      by destruct (app_eq_nil (rest_of (snd <$> o_E so)) [x.2] Hm) as [_ Hb].
  - intros Hne. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + exfalso. apply Hne. split; [reflexivity |].
      rewrite Hx. apply rest_of_snoc_nl.
    + by rewrite (nlines_snoc_other _ _ Hx).
Qed.

(* ---- the prologue resolution's length law, at [pro_idx_p] ---- *)

Definition ps_round_p (so : postage) : nat :=
  pro_idx_p (o_cs so) (nlines (snd <$> o_E so)).

Definition ps_opens_p (so : postage) : Prop :=
  (snd <$> o_E so) = []
  \/ (rest_of (snd <$> o_E so) = []
      /\ palt_panic (palt_at (o_cs so)
                       (nlines (snd <$> o_E so) - 1)%nat) = true).

Definition ps_len_ok_p (so : postage) : Prop :=
  pro_from (S (ps_round_p so)) (o_ps so) = []
  /\ (ps_opens_p so ->
      forall ps' : list nat, ps' `prefix_of` o_ps so ->
        pro_of (pro_from (ps_round_p so) ps')
          <> pro_of (pro_from (ps_round_p so) (o_ps so)) ->
        (length (pending_at_p ps' (o_cs so) (snd <$> o_E so))
         < length (o_w so))%nat).

Lemma ps_len_ok_p_empty_above (so : postage) (R : nat) :
  ps_len_ok_p so -> (ps_round_p so <= R)%nat -> pro_from (S R) (o_ps so) = [].
Proof using.
  intros [HA _] HR.
  replace (S R) with (S (ps_round_p so) + (R - ps_round_p so))%nat by lia.
  rewrite -pro_from_add HA. apply pro_from_nil.
Qed.

Lemma ps_len_ok_p_0 : ps_len_ok_p ostage0.
Proof using.
  rewrite /ps_len_ok_p /ps_round_p /ostage0.
  cbn [o_ps o_cs o_E o_w]. split.
  - apply pro_from_nil.
  - intros _ ps' Hp Hne. exfalso. apply Hne.
    by rewrite (prefix_nil_inv ps' Hp).
Qed.

Lemma ps_len_ok_p_write (so : postage) (b : bv 8) :
  ps_len_ok_p so ->
  ps_len_ok_p (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof using.
  intros [HA HB]. rewrite /ps_len_ok_p /ps_round_p /ps_opens_p in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *. split; [exact HA |].
  intros Ho ps' Hp Hne. rewrite (length_app (o_w so) [b]). cbn [length].
  pose proof (HB Ho ps' Hp Hne). lia.
Qed.

Lemma ps_len_ok_p_blk_w (so : postage) (a : nat) (wq : list (bv 8)) :
  rest_of (snd <$> o_E so) = [] ->
  (snd <$> o_E so) <> [] ->
  length (o_cs so) = (nlines (snd <$> o_E so) - 1)%nat ->
  ps_len_ok_p so ->
  ps_len_ok_p (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) wq).
Proof using.
  intros Hr Hne Hq Hok.
  pose proof (nlines_pos_of_rest_nil (snd <$> o_E so) Hne Hr) as Hpos.
  pose proof Hok as [HA HB].
  rewrite /ps_len_ok_p /ps_round_p /ps_opens_p in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *.
  assert (Hold : pro_idx_p (o_cs so) (nlines (snd <$> o_E so))
                 = pro_idx_p (o_cs so) (nlines (snd <$> o_E so) - 1)%nat).
  { replace (nlines (snd <$> o_E so))
      with (S (nlines (snd <$> o_E so) - 1))%nat at 1 by lia.
    apply pro_idx_p_Sn. apply palt_panic_ge. lia. }
  assert (Hnew : (pro_idx_p (o_cs so) (nlines (snd <$> o_E so))
                  <= pro_idx_p (o_cs so ++ [a])
                       (nlines (snd <$> o_E so)))%nat).
  { rewrite Hold.
    replace (nlines (snd <$> o_E so))
      with (S (nlines (snd <$> o_E so) - 1))%nat at 2 by lia.
    rewrite pro_idx_p_S
      (pro_idx_p_app_le (o_cs so) [a] (nlines (snd <$> o_E so) - 1)%nat
         ltac:(lia)).
    destruct (palt_panic _); lia. }
  split.
  - apply (ps_len_ok_p_empty_above so); [exact Hok |].
    rewrite /ps_round_p. exact Hnew.
  - intros Ho ps' Hp Hne2. exfalso.
    destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
    assert (Ha3 : palt_panic (palt_of a) = true).
    { rewrite /palt_at list_lookup_total_alt lookup_app_r in H3; [| lia].
      rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
    assert (Heq : pro_idx_p (o_cs so ++ [a]) (nlines (snd <$> o_E so))
                  = S (pro_idx_p (o_cs so) (nlines (snd <$> o_E so)))).
    { rewrite Hold
        -(pro_idx_p_app_le (o_cs so) [a] (nlines (snd <$> o_E so) - 1)%nat
            ltac:(lia)).
      replace (nlines (snd <$> o_E so))
        with (S (nlines (snd <$> o_E so) - 1))%nat at 1 by lia.
      apply pro_idx_p_Sp.
      rewrite /palt_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. by cbn. }
    rewrite Heq in Hne2. apply Hne2.
    assert (Hnil : pro_from
                     (S (pro_idx_p (o_cs so) (nlines (snd <$> o_E so))))
                     (o_ps so) = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx_p (o_cs so) (nlines (snd <$> o_E so))))
                      ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

(* ---- the log's own account of the era, at the pipeline discipline ---- *)

Definition pein_pure (k : nat) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) (cs0 : list nat) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg_p (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ E_index (seg_of (echoed pops))
  /\ E_disc_p (seg_of (echoed pops))
  /\ (nlines (snd <$> echoed pops) <= S (length cs0))%nat
  (* (A1) EVERY LOG ENTRY IS ECHOED ([EchoOut.ein_pure]'s clause): the
     store arm sends its byte before it files the entry, and the arms that
     file nothing are refuted at the OPEN from the ring bound. *)
  /\ Forall log_echoed pops.

Lemma pein_pure_0 k : pein_pure k [] [] [].
Proof using.
  rewrite /pein_pure. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
    by rewrite lookup_nil in Hx.
  - rewrite /E_disc_p /seg_of echoed_nil !fmap_nil. exact disc_input_p_nil.
  - rewrite echoed_nil fmap_nil nlines_nil. cbn [length]. lia.
  - constructor.
Qed.

(* WHAT THE CLAIM KNOWS OF THE WRITER'S STAGE at the input its log has
   echoed.  [EchoOut.rd_stage] with [alts_pre_p] where [Forall (< 4) cs0]
   was -- so, unlike the echo one, it NAMES the input. *)
Definition rd_stage_p (ps0 cs0 : list nat) (I : list (bv 8)) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps0
  /\ alts_pre_p I cs0
  /\ pro_pin_p ps0 cs0 I
  /\ (nlines (removelast I) <= length cs0)%nat.

Lemma rd_stage_p_0 : rd_stage_p [] [] [].
Proof using.
  rewrite /rd_stage_p. split_and!.
  - constructor.
  - apply alts_pre_p_nil.
  - intros q Hq. rewrite nstarted_nil in Hq. lia.
  - cbn [removelast]. rewrite nlines_nil. cbn [length]. lia.
Qed.

(* [EchoOut.rd_stage_le] HAS NO TWIN, and the reason is the range
   condition: [alts_pre_p I cs] ties every entry of [cs] to the LINE AT ITS
   INDEX in [I], so shortening [I] can leave an entry with no line to
   answer.  Upstream's [FileOut] has no [rd_stage_f_le] either, for the same
   reason, and what replaces it at the read is the TRUNCATION of the choice
   list to the window's own line count -- see [pecl_step_read]. *)

(* WHAT THE CLAIM REMEMBERS ABOUT AN OPEN ARM.  [EchoOut.ch_arm_era] with
   the PIPELINE discipline in the third clause. *)
Definition ch_arm_era_p (k : nat) (ho : list mobs)
    (H : LogEntryDefs.cons_hist) : Prop :=
  match LogEntryDefs.ch_arm H with
  | Some (h, c, cs, j) =>
      disc_seg_p (open_seg h) /\ obs_boots h = k
      /\ disc_p h /\ trace_shape h true
      /\ h = ho
      (* the arm ECHOES its byte (the drop and erase arms refuted at the
         open), and its input number (K1), both [EchoOut.ch_arm_era]'s *)
      /\ cs = [echo_of c]
      /\ (length (LogEntryDefs.ch_log H) + 1)%nat = length (ins (open_seg h))
  | None => True
  end.

Definition pcl_pure (k : nat) (ho : list mobs) (so : postage)
    (H : LogEntryDefs.cons_hist) : Prop :=
  pout_pure k ho so (LogEntryDefs.ch_acc H)
  /\ cs_len_ok so
  /\ ps_len_ok_p so
  /\ pein_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (o_cs so)
  /\ ch_arm_era_p k ho H
  /\ o_E so = ch_E H
  (* (A2) THE DELIVERED-COUNT LAW, [EchoOut.dl_ok] verbatim ([postage] is
     [ostage]): every completed line whose block has begun is consumed *)
  /\ dl_ok so (LogEntryDefs.ch_dl H).

(* ====================================================================== *)
(*  2c. THE ROUND IN PROGRESS (lane PIPE-2W-3)                             *)
(*                                                                        *)
(*  While a pipeline round's block is being written by TWO processes its   *)
(*  alternative cannot be filed in [cs] (design 4.3b), so the stage's own  *)
(*  reading of the block -- [pending_p] at the filed entry -- is not what  *)
(*  is on the wire: the ROUND'S LEDGER's [pre] is.  Everything else in     *)
(*  [pout_pure] holds verbatim, which is why the claim's pure part is ONE  *)
(*  disjunction and not a second arm.                                      *)
(* ====================================================================== *)

Definition pout_pure_o (k : nat) (ho : list mobs) (so : postage)
    (acc : list (bv 8)) : Prop :=
  acc = D_p (o_ps so) (o_cs so) (o_E so) ++ o_w so
  /\ E_index (o_E so)
  /\ E_disc_p (o_E so)
  /\ Forall (fun a => (a < length pro_alts)%nat) (o_ps so)
  /\ pro_pin_p (o_ps so) (o_cs so) (snd <$> o_E so)
  /\ alts_pre_p (snd <$> o_E so) (o_cs so)
  /\ Forall (fun x => disc_seg_p x.1) (o_E so)
  /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (o_E so)
  /\ (length (o_E so) <= length (ins (open_seg ho)))%nat
  /\ (o_E so = [] \/ obs_boots ho = k)
  /\ cs_nofork so.

(* THE BLOCK IN PROGRESS: the round's index, the bytes written so far, and
   the fact that they are a `$`-free prefix of an alternative the line
   admits.  The `$`-freeness is what refutes an ECHO here (the discipline
   wants the round's whole block, prompt included, on the wire before the
   next input byte). *)
Definition pblk_open (so : postage) (r : nat) (pre : list (bv 8)) : Prop :=
  r = (nlines (snd <$> o_E so) - 1)%nat
  /\ o_w so = pre
  /\ pre <> []
  /\ exists a : nat,
       pblk2_at (o_cs so) (snd <$> o_E so) pre a
       /\ ((palt_isforkS (palt_of a) = false /\ Forall nodollar pre)
           \/ palt_isforkS (palt_of a) = true).

(* the claim's pure part WHILE A ROUND IS OPEN -- [pcl_pure] with the
   block read off the round's ledger instead of off [cs].  It is a
   DEFINITION and not a raw conjunction on purpose: every step's tactic
   script below is [pcl_pure]'s, and those scripts unfold the goal's own
   name. *)
Definition pcl_pure_o (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) : Prop :=
  pout_pure_o k ho so (LogEntryDefs.ch_acc H)
  /\ pblk_open so r pre
  /\ ps_len_ok_p so
  /\ pein_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (o_cs so)
  /\ ch_arm_era_p k ho H
  /\ o_E so = ch_E H
  /\ dl_ok so (LogEntryDefs.ch_dl H).

Lemma pcl_pure_o_E (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  pcl_pure_o k ho so r pre H -> o_E so = ch_E H.
Proof using. by intros (_ & _ & _ & _ & _ & HE & _). Qed.

Lemma pcl_pure_o_pein (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  pcl_pure_o k ho so r pre H ->
  pein_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (o_cs so).
Proof using. by intros (_ & _ & _ & Hin & _). Qed.

(* the open round's own length law, which is [cs_len_ok]'s boundary case *)
Lemma pblk_open_cs (so : postage) (r : nat) (pre : list (bv 8)) :
  pblk_open so r pre ->
  length (o_cs so) = (nlines (snd <$> o_E so) - 1)%nat
  /\ rest_of (snd <$> o_E so) = []
  /\ (snd <$> o_E so) <> [].
Proof using.
  intros (_ & _ & _ & a & (Hne & Hr & Hq & _) & _). by split_and!.
Qed.

(* THE DELIVERED BYTES ARE INSIDE THE ERA'S INPUT.  [EchoOut.inp_lb] is a
   lower bound of the DELIVERED list, and the read never hands out more than
   the log has echoed -- so a writer's bound is a bound on the era's input
   too.  [EchoOut.ecl_pure_dl_E] at this claim. *)
Lemma pcl_pure_dl_E (k : nat) (ho : list mobs) (so : postage)
    (H : LogEntryDefs.cons_hist) :
  pcl_pure k ho so H ->
  (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> o_E so).
Proof using.
  intros (_ & _ & _ & Hin & _ & HE & _).
  destruct Hin as (_ & _ & _ & Hdlp & _).
  rewrite HE /ch_E.
  etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
  rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
  apply epu_fmap_prefix. by apply prefix_app_r.
Qed.

(* ...AND WHILE A ROUND IS OPEN: the open reading carries [pein_pure] and
   the [E]-tie too, which is all [pcl_pure_dl_E] reads. *)
Lemma pcl_pure_o_dl_E (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  pcl_pure_o k ho so r pre H ->
  (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> o_E so).
Proof using.
  intro Hc.
  pose proof (pcl_pure_o_pein k ho so r pre H Hc) as Hin.
  pose proof (pcl_pure_o_E k ho so r pre H Hc) as HE.
  destruct Hin as (_ & _ & _ & Hdlp & _).
  rewrite HE /ch_E.
  etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
  rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
  apply epu_fmap_prefix. by apply prefix_app_r.
Qed.

Lemma pcl_pure_o_rd_stage (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  pcl_pure_o k ho so r pre H ->
  rd_stage_p (o_ps so) (o_cs so) (snd <$> o_E so).
Proof using.
  intros (Hout & Hop & _).
  destruct Hout as (_ & _ & _ & Hpsb & Hpin & Hcsb & _).
  destruct (pblk_open_cs so r pre Hop) as (Hq & Hr & _).
  rewrite /rd_stage_p. split_and!;
    [exact Hpsb | exact Hcsb | exact Hpin |].
  rewrite (pop_nlines_removelast _ Hr) Hq. lia.
Qed.


(* ---- the five event steps of the pure part ---- *)

Lemma pcl_pure_o_close (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H ConsLog.EvClose ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k ho so r pre (ConsLog.cons_step H ConsLog.EvClose).
Proof using.
  intros Hok Hev Hecl.
  pose proof (ch_E_close H) as Hclose.
  pose proof (ch_E_close_len H) as Hlen.
  pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
  unfold ConsLog.cons_hist_ok in Hok'. destruct Hok' as [Hlog' _].
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; cycle 1.
  { rewrite /ConsLog.cons_step Ha. exact Hecl. }
  destruct Hecl as (Hout & Hop & Hps & Hin & Hera & HE & Hdlok).
  destruct Hin as (_ & Hdsc & Hbts & Hdl & _ & _ & _ & Hall).
  rewrite /ch_arm_era_p Ha in Hera.
  destruct Hera as (Hdseg & Hboots & _ & _ & _ & Hcsa & _).
  destruct Hev as (a & Ha2 & _ & HK3). rewrite Ha in Ha2.
  injection Ha2 as <-.
  cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_byte LogEntryDefs.ca_sent
       le_echo le_byte fst snd] in HK3.
  assert (Hj : j = 1%nat) by (apply HK3; exact Hcsa).
  assert (Hech : log_echoed (h, c, take j cs)).
  { rewrite Hcsa Hj. cbn [take]. exact (log_echoed_echo h c). }
  destruct Hout as (Hacc & HEi & HEb & Hpsf & Hpin & Hcsf & Hdse & Hpre0
                    & Hle & Hbo & Hnofk).
  destruct (pblk_open_cs so r pre Hop) as (Hqq & Hrr & Hnn).
  pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposn.
  rewrite /ConsLog.cons_step Ha in Hlog', Hlen |- *.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm] in Hlog', Hlen |- *.
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H ++ [(h, c, take j cs)]))
                 = o_E so).
  { rewrite HE -Hclose /ch_E /ConsLog.cons_step Ha.
    cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
    by rewrite app_nil_r. }
  rewrite /pcl_pure_o.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!.
  - by split_and!.
  - exact Hop.
  - exact Hps.
  - split_and!.
    + exact Hlog'.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hdsc e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist fst snd]. exact Hdseg.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hbts e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist fst snd]. exact Hboots.
    + rewrite (echoed_snoc_yes _ _ Hech).
      by apply (prefix_app_r _ _ [(le_hist (h, c, take j cs),
                                   le_byte (h, c, take j cs))]).
    + by rewrite Hseg.
    + by rewrite Hseg.
    + rewrite -(seg_of_snd (echoed _)) Hseg. rewrite Hqq. lia.
    + apply Forall_app. split; [exact Hall | by rewrite Forall_singleton].
  - exact I.
  - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
    rewrite app_nil_r. by rewrite Hseg.
  - exact Hdlok.
Qed.

Lemma pcl_pure_out (k : nat) (ho : list mobs) (so so' : postage)
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (o_cs so) <= length (o_cs so'))%nat -> o_E so' = o_E so ->
  pout_pure k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok so' -> ps_len_ok_p so' ->
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  pcl_pure k ho so H ->
  pcl_pure k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof using.
  intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  rewrite /pcl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia | exact Hall].
  - by rewrite HE' HE /ch_E.
Qed.

(* MOVING THE WITNESS, [EchoOut.eout_pure_move]'s twin. *)
Lemma pcl_pure_o_read (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8))
    (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
  (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k ho so r pre (ConsLog.cons_step H (ConsLog.EvRead ws)).
Proof using.
  intros Hpre (Hout & Hop & Hp & Hin & Hera & HE & Hdlok).
  destruct Hin as (Hlog & Hdsc & Hbts & _ & HEi & HEb & Hcnt & Hall).
  rewrite /pcl_pure_o /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera
              | by rewrite HE /ch_E |].
  - by split_and!.
  - apply (dl_ok_mono so (LogEntryDefs.ch_dl H)); [| exact Hdlok].
    rewrite length_app. lia.
Qed.

(* the same move at the ROUND-IN-PROGRESS reading: [pout_pure_o] is
   [pout_pure] minus the conjunct that reads the block off [cs], and that
   conjunct is the only one this move does not touch. *)
(* THE OUT STEP AT AN OPENING ROUND: the old reading is the ordinary one
   (the block had not started), the new one is the round-in-progress
   reading.  [pcl_pure_out]'s script with the two conjuncts that read the
   block off [cs] replaced by [pblk_open]. *)
Lemma pcl_pure_o_out (k : nat) (ho : list mobs) (so so' : postage)
    (r : nat) (pre : list (bv 8))
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (o_cs so) <= length (o_cs so'))%nat -> o_E so' = o_E so ->
  pout_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  pblk_open so' r pre -> ps_len_ok_p so' ->
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  pcl_pure k ho so H ->
  pcl_pure_o k ho so' r pre (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof using.
  intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  rewrite /pcl_pure_o /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia | exact Hall].
  - by rewrite HE' HE /ch_E.
Qed.

(* ...and the step that KEEPS a round open: both readings are the
   round-in-progress one. *)
Lemma pcl_pure_o_out2 (k : nat) (ho : list mobs) (so so' : postage)
    (r r' : nat) (pre pre' : list (bv 8))
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (o_cs so) <= length (o_cs so'))%nat -> o_E so' = o_E so ->
  pout_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  pblk_open so' r' pre' -> ps_len_ok_p so' ->
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k ho so' r' pre' (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof using.
  intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  rewrite /pcl_pure_o /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia | exact Hall].
  - by rewrite HE' HE /ch_E.
Qed.

(* ...and the FILING step's, which closes the round: the new reading is
   the ordinary one again, at the choice list the code was filed in. *)
Lemma pcl_pure_of_o_out (k : nat) (ho : list mobs) (so so' : postage)
    (r : nat) (pre : list (bv 8))
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (o_cs so) <= length (o_cs so'))%nat -> o_E so' = o_E so ->
  pout_pure k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok so' -> ps_len_ok_p so' ->
  dl_ok so' (LogEntryDefs.ch_dl H) ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof using.
  intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
  rewrite /pcl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia | exact Hall].
  - by rewrite HE' HE /ch_E.
Qed.

Lemma pout_pure_o_move (k : nat) (ho h : list mobs) (so : postage)
    (acc : list (bv 8)) (L : list log_entry)
    (dl : list (list mobs * bv 8)) :
  trace_shape h true ->
  obs_boots h = k ->
  (forall e, e ∈ L -> hist_ext (le_hist e) h) ->
  pein_pure k L dl (o_cs so) ->
  seg_of (echoed L) = o_E so ->
  (length (o_E so) <= length (ins (open_seg h)))%nat ->
  pout_pure_o k ho so acc -> pout_pure_o k h so acc.
Proof using.
  intros Hsh Hk Hord Hin Hseg Hle
    (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc & _ & _ & _ & Hnofk).
  destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & _).
  split_and!; [exact Hacc | exact Hidx | exact Hbyte
              | exact Hpsb | exact Hpin | exact Hcsb | exact Hdsc
              | | exact Hle | | exact Hnofk].
  - rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
    rewrite /seg_of list_lookup_fmap in Hx.
    destruct (echoed L !! j) as [y |] eqn:Hy; [| discriminate].
    cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
    assert (Hyin : y ∈ echoed L) by (by eapply elem_of_list_lookup_2).
    destruct (echoed_elem_inv L y Hyin) as (e & He & _ & Hye).
    apply open_seg_prefix_boots.
    + rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
    + rewrite -Hye. cbn [fst]. rewrite (Hstamp e He). by rewrite Hk.
    + exact Hsh.
  - right. exact Hk.
Qed.

Lemma pcl_pure_o_open (k : nat) (ho : list mobs) (so : postage)
    (r : nat) (pre : list (bv 8))
    (H : LogEntryDefs.cons_hist) (h : list mobs) (c : bv 8)
    (cs : list (bv 8)) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
  disc_seg_p (open_seg h) -> obs_boots h = k ->
  disc_p h -> trace_shape h true ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k h so r pre (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
Proof using.
  intros Hok Hev Hd Hb Hdh Hsh (Hout & Hop & Hp & Hin & _ & HE & Hdlok).
  pose proof Hev as (Hn & Hends & Hecho & Hord & Hwire & HK1f & HK2).
  pose proof (ch_E_open H h c cs Hn) as Hopen.
  assert (HK1 : (length (LogEntryDefs.ch_log H) + 1)%nat
                = length (ins (open_seg h))).
  { destruct HK1f as (f & Hfl & Hcnt).
    rewrite (flush_lost_zero_p h f Hsh Hdh Hfl) Nat.add_0_r in Hcnt.
    by rewrite -ins_obs_ins in Hcnt. }
  pose proof (open_seg_ends_in h c Hends) as Hends'.
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = o_E so).
  { rewrite HE /ch_E Hn. cbn [ch_arm_E]. by rewrite app_nil_r. }
  assert (Hall : Forall log_echoed (LogEntryDefs.ch_log H))
    by (by destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hq)).
  assert (Hcnt : length (o_E so) = (length (ins (open_seg h)) - 1)%nat).
  { rewrite -Hseg seg_of_length (echoed_all_len _ Hall). lia. }
  assert (Hle : (length (o_E so) <= length (ins (open_seg h)))%nat) by lia.
  pose proof (pout_pure_o_move k ho h so (LogEntryDefs.ch_acc H)
                (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
                Hsh Hb Hord Hin Hseg Hle Hout) as Hout'.
  assert (Hpl : forall j x, o_E so !! j = Some x -> x.1 `prefix_of` open_seg h).
  { destruct Hout' as (_ & _ & _ & _ & _ & _ & _ & Hpre1 & _).
    intros j x Hx. exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx). }
  assert (Hidx : E_index (o_E so)) by (by destruct Hout as (_ & Hq & _)).
  assert (Hbytes : (snd <$> o_E so)
                   = take (length (LogEntryDefs.ch_log H)) (ins (open_seg h))).
  { rewrite (E_bytes_of_hist (o_E so) (open_seg h) Hidx Hpl Hle).
    by replace (length (o_E so)) with (length (LogEntryDefs.ch_log H)) by lia. }
  assert (Hcin : c ∈ ins (open_seg h)).
  { destruct Hends' as [h0 Hh0]. rewrite Hh0 ins_app ins_in.
    apply elem_of_app. right. apply elem_of_list_here. }
  pose proof (disc_drop_byte_p _ c Hd Hcin) as (_ & _ & Hner).
  assert (Hcs : cs = [echo_of c]).
  { destruct Hecho as [Hnil | [Hech | [Herase _]]]; [| exact Hech |];
      last first.
    { exfalso. rewrite Hner in Herase. discriminate. }
    exfalso.
    exact (cons_drop_refuted_p h c (LogEntryDefs.ch_log H)
             (LogEntryDefs.ch_dl H) (snd <$> o_E so) (o_w so)
             HK1 Hall Hdlok Hbytes Hd Hcin (HK2 Hnil)). }
  rewrite /pcl_pure_o /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout' | exact Hop | exact Hp | exact Hin | | | exact Hdlok].
  - rewrite /ch_arm_era_p. cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
    split_and!; [exact Hd | exact Hb | exact Hdh | exact Hsh | reflexivity
                | exact Hcs | exact HK1].
  - rewrite HE -Hopen /ConsLog.cons_step /ch_E.
    by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
Qed.

(* ---- the two PHI steps, at [good_out_p] ---- *)

Lemma phi_step_io_p (h : list mobs) (e : mobs) :
  trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
  Forall good_out_p (cycles_of h) -> Forall good_out_p (cycles_of (h ++ [e])).
Proof using.
  intros Hsh Hio Hw HF.
  destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
  rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs Hlast].
  apply Forall_app. split; [exact Hcs |].
  rewrite Forall_singleton in Hlast. rewrite Forall_singleton.
  apply good_out_p_step; [exact Hw | exact Hlast].
Qed.

Lemma phi_step_cons_p (h : list mobs) (e : mobs) :
  trace_shape h true -> is_io e = true ->
  good_out_p (open_seg h ++ [e]) ->
  Forall good_out_p (cycles_of h) -> Forall good_out_p (cycles_of (h ++ [e])).
Proof using.
  intros Hsh Hio Hgo HF.
  destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
  rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs _].
  apply Forall_app. split; [exact Hcs |].
  rewrite Forall_singleton. exact Hgo.
Qed.

(* ====================================================================== *)
(*  2d. THE STAGE AS THE MODEL'S (app-both M3b)                            *)
(*                                                                        *)
(*  The pipeline's stage is [EchoOut.ostage], with no state slot; the      *)
(*  model's is [GenOutPure.gstage pipe_lm], whose state ([unit]) is filed  *)
(*  exactly when something is written.  Every stage function and the whole *)
(*  closed-round pure claim are the model's under that map.                *)
(* ====================================================================== *)

Definition pstage_g (so : postage) : gstage pipe_lm :=
  MkGS pipe_lm (o_ps so) (o_cs so) (o_E so) (o_w so)
    (if decide (o_E so = [] /\ o_w so = []) then None else Some tt).

Definition pstage_o (so : gstage pipe_lm) : postage :=
  MkO (gs_ps pipe_lm so) (gs_cs pipe_lm so) (gs_E pipe_lm so) (gs_w pipe_lm so).

Lemma pstage_o_g (so : postage) : pstage_o (pstage_g so) = so.
Proof using. by destruct so. Qed.

(* a model stage whose state is filed exactly when something is written IS
   a pipeline stage *)
Lemma pstage_g_o (so : gstage pipe_lm) :
  (gs_st pipe_lm so = None <-> (gs_E pipe_lm so = [] /\ gs_w pipe_lm so = [])) ->
  pstage_g (pstage_o so) = so.
Proof using.
  destruct so as [ps cs E w st]. cbn [gs_st gs_E gs_w]. intros Hst.
  rewrite /pstage_g /pstage_o /=. f_equal.
  destruct st as [[] |].
  - rewrite decide_False; [done |]. intros Hq. discriminate (proj2 Hst Hq).
  - rewrite decide_True; [done |]. by apply Hst.
Qed.

Lemma pipe_st_tt (s : lm_st pipe_lm) : s = tt.
Proof using. by destruct s. Qed.

Lemma D_p_lm ps cs (s : lm_st pipe_lm) E : D_p ps cs E = lm_D pipe_lm ps cs s E.
Proof using.
  rewrite (pipe_st_tt s) /D_p /lm_D. generalize (@nil (bv 8)) as pre.
  induction E as [| x E IH]; intros pre; [reflexivity |].
  cbn [D_from_p lm_D_from]. by rewrite IH.
Qed.

Lemma pending_p_lm ps cs (s : lm_st pipe_lm) E :
  pending_p ps cs E = lm_pending pipe_lm ps cs s E.
Proof using. by rewrite (pipe_st_tt s). Qed.

Lemma pending_at_p_lm_s ps cs (s : lm_st pipe_lm) I :
  pending_at_p ps cs I = lm_pending_at pipe_lm ps cs s I.
Proof using. by rewrite (pipe_st_tt s). Qed.

Lemma proc_before_p_lm_s ps cs (s : lm_st pipe_lm) I :
  proc_before_p ps cs I = lm_proc_before pipe_lm ps cs s I.
Proof using. rewrite (pipe_st_tt s). apply proc_before_p_lm. Qed.

Lemma pcount_p_lm ps cs (s : lm_st pipe_lm) E w :
  pcount_p ps cs E w = lm_pcount pipe_lm ps cs s E w.
Proof using. by rewrite /pcount_p /lm_pcount (proc_before_p_lm_s ps cs s). Qed.

Lemma pout_pure_lm (k : nat) (ho : list mobs) (so : postage) (acc : list (bv 8)) :
  pout_pure k ho so acc <-> lm_out_pure pipe_lm tt k ho (pstage_g so) acc.
Proof using.
  rewrite /pout_pure /lm_out_pure /pstage_g /cs_nofork /=.
  set (st := gs_state pipe_lm tt _).
  rewrite (D_p_lm _ _ st) (pending_p_lm _ _ st).
  split.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
    split_and!; try done; try (by apply pro_pin_p_lm); by case_decide.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _ & _).
    split_and!; try done; by apply pro_pin_p_lm.
Qed.

Lemma cs_len_ok_lm (so : postage) : cs_len_ok so <-> lm_cs_len_ok pipe_lm (pstage_g so).
Proof using. done. Qed.

Lemma ps_len_ok_p_lm (so : postage) :
  ps_len_ok_p so <-> lm_ps_len_ok pipe_lm tt (pstage_g so).
Proof using.
  rewrite /ps_len_ok_p /lm_ps_len_ok /ps_round_p /lm_ps_round /ps_opens_p
    /lm_ps_opens /pstage_g /= pro_idx_p_lm.
  set (st := gs_state pipe_lm tt _).
  split; intros [HA HB]; (split; [exact HA |]); intros Hop ps' Hp Hne.
  - rewrite -(pending_at_p_lm_s ps' _ st). exact (HB Hop ps' Hp Hne).
  - rewrite (pending_at_p_lm_s ps' _ st). exact (HB Hop ps' Hp Hne).
Qed.

Lemma pein_pure_lm k pops dl cs0 : pein_pure k pops dl cs0 <-> gin_pure pipe_lm k pops dl cs0.
Proof using. done. Qed.

Lemma rd_stage_p_lm ps0 cs0 s0 I : rd_stage_p ps0 cs0 I <-> lm_rd_stage pipe_lm ps0 cs0 s0 I.
Proof using.
  rewrite /rd_stage_p /lm_rd_stage.
  split; intros (H1 & H2 & H3 & H4);
    (split_and!; [exact H1 | exact H2 | by apply pro_pin_p_lm | exact H4]).
Qed.

Lemma ch_arm_era_p_lm k ho H : ch_arm_era_p k ho H <-> garm_era pipe_lm k ho H.
Proof using.
  rewrite /ch_arm_era_p /garm_era.
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |]; [| done].
  split; intros (H1 & H2 & H3 & H4 & H5 & H6 & H7); split_and!; try done;
    by apply disc_p_lm.
Qed.

Lemma dl_ok_lm (so : postage) dl : dl_ok so dl <-> lm_dl_ok pipe_lm (pstage_g so) dl.
Proof using. done. Qed.

(* THE CLOSED-ROUND PURE CLAIM IS THE MODEL'S *)
Lemma pcl_pure_lm (k : nat) (ho : list mobs) (so : postage)
    (H : LogEntryDefs.cons_hist) :
  pcl_pure k ho so H <-> gcl_pure pipe_lm tt k ho (pstage_g so) H.
Proof using.
  rewrite /pcl_pure /gcl_pure.
  rewrite pout_pure_lm cs_len_ok_lm ps_len_ok_p_lm pein_pure_lm ch_arm_era_p_lm
    dl_ok_lm.
  done.
Qed.


(* ====================================================================== *)
(*  2b. THE ERA'S BYTE LEDGER: the ghosts and their laws                   *)
(*                                                                        *)
(*  [FileOut]'s second per-era record one application over.  The map is    *)
(*  pinned in the fixed part, the era's record is inserted at the          *)
(*  POWER-ON (where the era's other ghosts are born), and the era's list   *)
(*  is a [mono_list] of its process bytes: the claim holds the authority   *)
(*  and a writer a lower bound, and at EQUAL LENGTH -- which [turn] pins   *)
(*  exactly -- the bound IS the list.                                      *)
(* ====================================================================== *)
Section pipe_ledger.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).

  Definition pera_pin (k : nat) (w : pipe_era) : iProp Σ :=
    ghost_map_elem (pgn_era g) k DfracDiscarded w.

  Global Instance pera_pin_persistent k w : Persistent (pera_pin k w).
  Proof using . rewrite /pera_pin. apply _. Qed.
  Global Instance pera_pin_timeless k w : Timeless (pera_pin k w).
  Proof using . rewrite /pera_pin. apply _. Qed.

  Lemma pera_pin_agree k w w' : pera_pin k w -∗ pera_pin k w' -∗ ⌜w = w'⌝.
  Proof using .
    rewrite /pera_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Definition blk_auth (w : pipe_era) (l : list (bv 8)) : iProp Σ :=
    own (pe_blk w)
      (●ML ((blk_enc <$> l) : list (leibnizO (list mobs * bv 8)))).
  Definition blk_lb (w : pipe_era) (l : list (bv 8)) : iProp Σ :=
    own (pe_blk w)
      (◯ML ((blk_enc <$> l) : list (leibnizO (list mobs * bv 8)))).

  Global Instance blk_lb_persistent w l : Persistent (blk_lb w l).
  Proof using . rewrite /blk_lb. apply _. Qed.
  Global Instance blk_lb_timeless w l : Timeless (blk_lb w l).
  Proof using . rewrite /blk_lb. apply _. Qed.
  Global Instance blk_auth_timeless w l : Timeless (blk_auth w l).
  Proof using . rewrite /blk_auth. apply _. Qed.

  Lemma blk_auth_grow w l b :
    blk_auth w l ==∗ blk_auth w (l ++ [b]) ∗ blk_lb w (l ++ [b]).
  Proof using .
    rewrite /blk_auth /blk_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((blk_enc <$> (l ++ [b]))
                                 : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. rewrite fmap_app. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _ (◯ML ((blk_enc <$> (l ++ [b]))
                                    : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  (* ---- THE ROUND'S OWN BLOCK LEDGER, at a gname minted per round ---- *)

  Definition rblk_auth (gb : gname) (l : list (bv 8)) : iProp Σ :=
    own gb (●ML ((blk_enc <$> l) : list (leibnizO (list mobs * bv 8)))).
  Definition rblk_lb (gb : gname) (l : list (bv 8)) : iProp Σ :=
    own gb (◯ML ((blk_enc <$> l) : list (leibnizO (list mobs * bv 8)))).

  Global Instance rblk_lb_persistent gb l : Persistent (rblk_lb gb l).
  Proof using . rewrite /rblk_lb. apply _. Qed.
  Global Instance rblk_lb_timeless gb l : Timeless (rblk_lb gb l).
  Proof using . rewrite /rblk_lb. apply _. Qed.
  Global Instance rblk_auth_timeless gb l : Timeless (rblk_auth gb l).
  Proof using . rewrite /rblk_auth. apply _. Qed.

  Lemma rblk_auth_grow gb l b :
    rblk_auth gb l ==∗ rblk_auth gb (l ++ [b]) ∗ rblk_lb gb (l ++ [b]).
  Proof using .
    rewrite /rblk_auth /rblk_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((blk_enc <$> (l ++ [b]))
                                 : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. rewrite fmap_app. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _ (◯ML ((blk_enc <$> (l ++ [b]))
                                    : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma rblk_lb_prefix gb l l' :
    rblk_auth gb l -∗ rblk_lb gb l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /rblk_auth /rblk_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. apply mono_list_both_valid_L in Hv.
    exact (blk_fmap_prefix_inv l' l Hv).
  Qed.

  Lemma rblk_alloc : ⊢ |==> ∃ gb : gname, rblk_auth gb [].
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (gb) "Ha"; [by apply mono_list_auth_valid |].
    iModIntro. iExists gb. rewrite /rblk_auth. by rewrite fmap_nil.
  Qed.

  (* ---- THE CURRENT ROUND, in two exclusive halves ---- *)

  (* ...AND ITS THIRD COMPONENT, THE TERMINAL FLAG (lane PIPE-STAGE-4,
     design claude-notes/design/app-pipe.md SS4.3m).  [tm] is the ONE
     thing the claim has to know about the family that is writing the open
     round: whether the round is a FORK-FAILURE round.  It is set when the
     block's first PForkS byte is written and it never goes back, and the
     writer's own half PINS it -- which is what refutes [pecl_blk2_file]
     at a terminal round (the filer has to present [tm = false]) and so
     makes the claim's resolution FREEZABLE there. *)
  Definition cur_half (w : pipe_era) (q : Qp) (r : nat) (gb : gname)
      (tm : bool) : iProp Σ := ghost_var (pe_cur w) q (r, gb, tm).

  Global Instance cur_half_timeless w q r gb tm :
    Timeless (cur_half w q r gb tm).
  Proof using . rewrite /cur_half. apply _. Qed.

  (* THE EXCLUSION a stale family runs into: the claim's half and the
     family's half agree on the round, on its ledger AND on the flag. *)
  Lemma cur_half_agree w q1 q2 r1 gb1 tm1 r2 gb2 tm2 :
    cur_half w q1 r1 gb1 tm1 -∗ cur_half w q2 r2 gb2 tm2 -∗
    ⌜r1 = r2 /\ gb1 = gb2 /\ tm1 = tm2⌝.
  Proof using .
    rewrite /cur_half. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq.
    iPureIntro. injection Heq as Hr Hg Ht. by split_and!.
  Qed.

  Lemma cur_half_excl w r gb tm r' gb' tm' :
    cur_half w 1 r gb tm -∗ cur_half w (1/2) r' gb' tm' -∗ False.
  Proof using .
    rewrite /cur_half. iIntros "H1 H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  Lemma cur_half_update w r1 gb1 tm1 r2 gb2 tm2 r gb tm :
    cur_half w (1/2) r1 gb1 tm1 -∗ cur_half w (1/2) r2 gb2 tm2 ==∗
      cur_half w (1/2) r gb tm ∗ cur_half w (1/2) r gb tm.
  Proof using .
    rewrite /cur_half. iIntros "H1 H2".
    by iMod (ghost_var_update_halves (r, gb, tm) with "H1 H2") as "[$ $]".
  Qed.

  (* the era is born with BOTH halves at a round nobody is writing *)
  Lemma blk_alloc : ⊢ |==> ∃ (w : pipe_era) (gb : gname),
      blk_auth w [] ∗ rblk_auth gb [] ∗ cur_half w 1 0%nat gb false.
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (ge) "Ha"; [by apply mono_list_auth_valid |].
    iMod rblk_alloc as (gb) "Hr".
    iMod (ghost_var_alloc (0%nat, gb, false)) as (gc) "Hc".
    iModIntro. iExists (MkPEra ge gc), gb.
    rewrite /blk_auth /cur_half. cbn [pe_blk pe_cur].
    rewrite fmap_nil. iFrame "Ha Hr Hc".
  Qed.

  (* the opening of a round SPLITS it; the filing rejoins it *)
  Lemma cur_split w r gb tm :
    cur_half w 1 r gb tm -∗ cur_half w (1/2) r gb tm ∗ cur_half w (1/2) r gb tm.
  Proof using .
    rewrite /cur_half. iIntros "H".
    iEval (rewrite -Qp.half_half) in "H".
    by iDestruct (ghost_var_split with "H") as "[$ $]".
  Qed.

  Lemma cur_join w r gb tm :
    cur_half w (1/2) r gb tm -∗ cur_half w (1/2) r gb tm -∗
    cur_half w 1 r gb tm.
  Proof using .
    rewrite /cur_half. iIntros "H1 H2".
    iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* ...and a WHOLE current-round ghost may be retargeted at the round the
     block that is opening belongs to *)
  Lemma cur_retarget w r gb tm r' gb' tm' :
    cur_half w 1 r gb tm ==∗ cur_half w 1 r' gb' tm'.
  Proof using .
    rewrite /cur_half. iIntros "H".
    by iMod (ghost_var_update (r', gb', tm') with "H") as "$".
  Qed.

  (* the map, and its two moves -- [FileOut.f0_map] verbatim *)
  Definition pera_map (h : list mobs) : iProp Σ :=
    (∃ M : gmap nat pipe_era,
       ghost_map_auth (pgn_era g) 1 M ∗ ⌜pin_dom M (obs_boots h)⌝)%I.

  Global Instance pera_map_timeless h : Timeless (pera_map h).
  Proof using . rewrite /pera_map. apply _. Qed.

  Lemma pera_map_step (h : list mobs) (e : mobs) :
    obs_boots [e] = 0%nat -> pera_map h -∗ pera_map (h ++ [e]).
  Proof using .
    intros He. rewrite /pera_map obs_boots_app He Nat.add_0_r. by iIntros "$".
  Qed.

  Lemma pera_map_on (h : list mobs) (w : pipe_era) :
    pera_map h ==∗
      pera_map (h ++ [ObsPowerOn]) ∗ pera_pin (S (obs_boots h)) w.
  Proof using .
    rewrite /pera_map /pera_pin obs_boots_app. cbn [obs_boots].
    rewrite Nat.add_1_r.
    iIntros "H". iDestruct "H" as (M) "[Hm %Hd]".
    iMod (ghost_map_insert_persist (S (obs_boots h)) w
            (pin_dom_absent _ _ Hd) with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists _. iFrame "Hm".
    iPureIntro. by apply pin_dom_insert.
  Qed.

End pipe_ledger.

(* ====================================================================== *)
(*  3.  THE CLAIM, THE TAG, THE TURN AND THE LEDGER                        *)
(* ====================================================================== *)

Section pipe_out.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  (* THE FIXED PART IS THE ECHO APPLICATION'S, and the taint is
     [AppEcho.echo_taint] -- not a parameter, because the pipeline
     application's claim about the FILE SYSTEM is echo's verbatim, so the
     two share the counter. *)
  (* THE FIXED PART IS [pipe_gn] (lane PIPE-2W-2): AppEcho's, paired with
     the byte ledger's map.  [pgn_cl g] reads the echo half, and every
     statement below names [γ] exactly as it did. *)
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).

  Notation T := (echo_taint γ).

  (* ===================================================================== *)
  (*  THE RESOLUTION, FROZEN (design claude-notes/design/app-pipe.md        *)
  (*  SS4.3l, lane SH-PIPE-ROUND-5 part 4).                                 *)
  (*                                                                       *)
  (*  A read site holds only LOWER bounds of the claim's resolution list    *)
  (*  ([EchoOut.cs_lb]), and a lower bound can never refute a LONGER        *)
  (*  resolution -- which is why the terminal round's refutation could not  *)
  (*  be taken there (part 3).  A PERSISTED AUTHORITY can: [mono_list]'s    *)
  (*  [dq]-indexed authority may be frozen to [DfracDiscarded]              *)
  (*  ([mono_list_auth_persist]), the frozen form is [CoreId] and therefore *)
  (*  persistent, and [mono_list_both_dfrac_valid_L] reads it against any   *)
  (*  lower bound.  A round that is never FILED never grows [cs], so a      *)
  (*  terminal round may hand the writer this, and the writer may hand it   *)
  (*  to the read.                                                         *)
  (* ===================================================================== *)
  Definition cs_frozen (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gcs v) (●ML□ (l : list (leibnizO nat))).

  Global Instance cs_frozen_persistent v l : Persistent (cs_frozen v l).
  Proof using . rewrite /cs_frozen. apply _. Qed.
  Global Instance cs_frozen_timeless v l : Timeless (cs_frozen v l).
  Proof using . rewrite /cs_frozen. apply _. Qed.

  Lemma cs_freeze (v : era_pins) (l : list nat) :
    cs_auth v l ==∗ cs_frozen v l.
  Proof using .
    rewrite /cs_auth /cs_frozen. iIntros "H".
    iMod (own_update _ _ (●ML□ (l : list (leibnizO nat))) with "H") as "$";
      [ apply mono_list_auth_persist | done ].
  Qed.

  Lemma cs_frozen_prefix (v : era_pins) (l l' : list nat) :
    cs_frozen v l -∗ cs_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /cs_frozen /cs_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_dfrac_valid_L in Hv as [_ Hv].
  Qed.

  (* ...AND THE CONTRADICTION THE TERMINAL READ SPENDS: a resolution
     LONGER than the frozen one cannot be a lower bound of it. *)
  Lemma cs_frozen_lb_absurd (v : era_pins) (l l' : list nat) :
    (length l < length l')%nat ->
    cs_frozen v l -∗ cs_lb v l' -∗ False.
  Proof using .
    intro Hlt. iIntros "Ha Hl".
    iDestruct (cs_frozen_prefix v l l' with "Ha Hl") as %Hp.
    iPureIntro. pose proof (prefix_length _ _ Hp) as Hle. lia.
  Qed.

  (* the frozen authority still HANDS OUT its own lower bound *)
  Lemma cs_frozen_lb (v : era_pins) (l : list nat) :
    cs_frozen v l -∗ cs_lb v l.
  Proof using .
    rewrite /cs_frozen /cs_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (l : list (leibnizO nat))) with "H")
      as "#Hl"; [apply mono_list_included |].
    iExact "Hl".
  Qed.

  (* WHAT A WRITER CARRIES AWAY FROM A TERMINAL ROUND.  The list itself is
     not interesting to the writer -- only its LENGTH is, because that is
     what a later line's read residue contradicts.  Persistent and
     timeless, so a [LinkRec] boundary field may hold it. *)
  Definition cs_frozen_at (v : era_pins) (n : nat) : iProp Σ :=
    (∃ l : list nat, ⌜length l = n⌝ ∗ cs_frozen v l)%I.

  Global Instance cs_frozen_at_persistent v n : Persistent (cs_frozen_at v n).
  Proof using . rewrite /cs_frozen_at. apply _. Qed.
  Global Instance cs_frozen_at_timeless v n : Timeless (cs_frozen_at v n).
  Proof using . rewrite /cs_frozen_at. apply _. Qed.

  Lemma cs_frozen_at_of (v : era_pins) (l : list nat) (n : nat) :
    length l = n -> cs_frozen v l -∗ cs_frozen_at v n.
  Proof using .
    intros Hn. iIntros "H". rewrite /cs_frozen_at. iExists l. by iFrame "H".
  Qed.

  (* ...AND THE CONTRADICTION THE TERMINAL READ SPENDS, at that reading:
     a resolution LONGER than the frozen one cannot be a lower bound. *)
  Lemma cs_frozen_at_lb_absurd (v : era_pins) (n : nat) (l' : list nat) :
    (n < length l')%nat -> cs_frozen_at v n -∗ cs_lb v l' -∗ False.
  Proof using .
    intro Hlt. iIntros "Ha Hl". rewrite /cs_frozen_at.
    iDestruct "Ha" as (l) "[%Hn Ha]". subst n.
    iApply (cs_frozen_lb_absurd v l l' Hlt with "Ha Hl").
  Qed.

  (* ===================================================================== *)
  (*  THE CLAIM'S RESOLUTION AUTHORITY, FLAG-INDEXED (lane PIPE-STAGE-4).   *)
  (*                                                                       *)
  (*  While a FORK-FAILURE round is open the claim holds the resolution     *)
  (*  FROZEN and not merely authoritative: the round will never be filed,   *)
  (*  so [cs] never grows again, and the persisted authority is the one     *)
  (*  non-monotone reading a writer may carry to a later read.  Both forms  *)
  (*  answer the two things every other step asks of the authority -- a     *)
  (*  lower bound's prefix, and a lower bound of its own.                   *)
  (* ===================================================================== *)
  Definition pcs (v : era_pins) (l : list nat) (fz : bool) : iProp Σ :=
    (if fz then cs_frozen v l else cs_auth v l)%I.

  Global Instance pcs_timeless v l fz : Timeless (pcs v l fz).
  Proof using . rewrite /pcs. destruct fz; apply _. Qed.

  Lemma pcs_lb_prefix v l l' fz :
    pcs v l fz -∗ cs_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof using .
    rewrite /pcs. destruct fz;
      [ iApply cs_frozen_prefix | iApply cs_lb_prefix ].
  Qed.

  Lemma pcs_lb_get v l fz : pcs v l fz -∗ pcs v l fz ∗ cs_lb v l.
  Proof using .
    rewrite /pcs. destruct fz; [| iApply cs_lb_get ].
    iIntros "H". iDestruct (cs_frozen_lb with "H") as "#Hl". by iFrame "H Hl".
  Qed.

  (* ...and the two readings the two cs-GROWING steps need: at a flag the
     claim can show to be [false] the authority is the landed one. *)
  Lemma pcs_auth v l fz : fz = false -> pcs v l fz -∗ cs_auth v l.
  Proof using . intros ->. rewrite /pcs /=. by iIntros "$". Qed.

  Lemma pcs_of_auth v l fz : fz = false -> cs_auth v l -∗ pcs v l fz.
  Proof using . intros ->. rewrite /pcs /=. by iIntros "$". Qed.

  (* THE FIRE.  [cs_freeze] at the claim's own authority, at any flag --
     a second fire is a no-op, which is what lets the terminal byte step
     be stated uniformly over the flag it finds. *)
  Lemma pcs_freeze v l fz : pcs v l fz ==∗ pcs v l true ∗ cs_frozen v l.
  Proof using .
    destruct fz; rewrite /pcs /=.
    - iIntros "#H". iModIntro. by iFrame "H".
    - iIntros "H". iMod (cs_freeze v l with "H") as "#H". iModIntro.
      by iFrame "H".
  Qed.

  (* [EchoOut.ecl] at the pipeline stage: the same four authorities, the
     same delivered count, no extra per-era ghost. *)
  (* ==================================================================== *)
  (*  3b. THE CLAIM AS THE GENERIC ONE, AND THE OPEN ROUND (app-both M3b)  *)
  (*                                                                      *)
  (*  Between rounds the claim is [GenOut.gcl] at [pipe_lm]: no state      *)
  (*  witness ([unit], filed by the era's first byte), and the STREAM      *)
  (*  EXTENSION is the byte ledger with the round ghosts held whole.       *)
  (*  While a two-writer round is open it is [popen], pipe-only.  Owner    *)
  (*  ruling 2026-09-23: a claim-level disjunct.                           *)
  (* ==================================================================== *)
  Definition pipe_cparams : gen_cparams pipe_lm :=
    MkGCP pipe_lm pipe_lm_laws pipe_hooks T _ _ (era_pin γ) _ _ (era_pin_agree γ)
      (fun _ _ => emp%I) _ _.

  Definition pext (k : nat) (l : list (bv 8)) : iProp Σ :=
    (∃ (w : pipe_era) (r : nat) (gb : gname) (pre : list (bv 8)) (tm : bool),
       pera_pin g k w ∗ blk_auth w l ∗ cur_half w 1 r gb tm ∗ rblk_auth gb pre)%I.

  Global Instance pext_timeless k l : Timeless (pext k l).
  Proof using . rewrite /pext. apply _. Qed.

  Lemma pext_grow (k : nat) (l : list (bv 8)) (b : bv 8) :
    pext k l ==∗ pext k (l ++ [b]).
  Proof using .
    iIntros "(%w & %r & %gb & %pre & %tm & #Hpe & Hblk & Hcur & Hrb)".
    iMod (blk_auth_grow w l b with "Hblk") as "[Hblk _]".
    iModIntro. iExists w, r, gb, pre, tm. iFrame "Hpe Hblk Hcur Hrb".
  Qed.

  Lemma pipe_wa_agree (k : nat) (st : option (lm_st pipe_lm)) (s0 : lm_st pipe_lm) :
    (emp : iProp Σ) -∗ emp -∗ ⌜default tt st = s0⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct (default tt st), s0. Qed.

  Lemma pipe_wa_W (k : nat) (s0 : lm_st pipe_lm) :
    (emp : iProp Σ) -∗ emp ∗ emp ∗ emp.
  Proof using . iIntros "_". by iSplit; [| iSplit]. Qed.

  Lemma pipe_wa_file (k : nat) (s0 : lm_st pipe_lm) :
    (emp : iProp Σ) -∗ emp ==∗ emp ∗ emp.
  Proof using . iIntros "_ _". by iModIntro; iSplit. Qed.

  Lemma pipe_wa_free (k : nat) : (emp : iProp Σ) ==∗ emp.
  Proof using . by iIntros "_". Qed.

  Definition pipe_wa : gen_wa pipe_lm pipe_cparams tt :=
    @MkGWA Σ _ pipe_lm pipe_cparams tt (fun _ _ => emp%I) _ pipe_wa_agree
      (fun _ => emp%I) _ pipe_wa_W (fun _ _ => emp%I) pipe_wa_file
      False (fun Hf => match Hf with end)
      True (fun _ => pipe_wa_free)
      pext _ pext_grow.

  (* THE OPEN ROUND: the writer family holds the other half of the round
     ghost, and the block is read off the round's ledger *)
  Definition popen (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (∃ (v : era_pins) (w : pipe_era) (so : postage)
       (r : nat) (gb : gname) (pre : list (bv 8)) (tm : bool),
       era_pin γ k v ∗ pera_pin g k w ∗ blk_auth w (pstream so)
       ∗ cur_half w (1/2) r gb tm ∗ rblk_auth gb pre
       ∗ turn_auth v (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
       ∗ pcs v (o_cs so) tm
       ∗ ps_auth v (o_ps so)
       ∗ Elist_auth v (o_E so)
       ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
       ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
       ∗ ⌜pcl_pure_o k ho so r pre H⌝)%I.

  Lemma pstream_lm_g (so : gstage pipe_lm) :
    pstream (pstage_o so) = lm_stream pipe_lm tt so.
  Proof using.
    rewrite /pstream /lm_stream /pstage_o /=.
    by rewrite (proc_before_p_lm_s _ _ (gs_state pipe_lm tt so)).
  Qed.

  (* THE CLAIM BETWEEN ROUNDS, IN THE PIPELINE'S TERMS: [gcl] at the
     instance, read through [pstage_o].  The claim holds the current-round
     ghost WHOLE, so it can retarget it when a round opens.  This is what
     the pipe-only round steps open from and file back into. *)
  Definition pclosed (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (∃ (v : era_pins) (w : pipe_era) (so : postage)
       (r : nat) (gb : gname) (pre : list (bv 8)) (tm : bool),
       era_pin γ k v ∗ pera_pin g k w ∗ blk_auth w (pstream so)
       ∗ cur_half w 1 r gb tm ∗ rblk_auth gb pre
       ∗ turn_auth v (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
       ∗ cs_auth v (o_cs so)
       ∗ ps_auth v (o_ps so)
       ∗ Elist_auth v (o_E so)
       ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
       ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
       ∗ ⌜pcl_pure k ho so H⌝)%I.

  Lemma gcl_pipe_view (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    gcl pipe_lm pipe_cparams tt pipe_wa k ho H ⊣⊢ T ∨ pclosed k ho H.
  Proof using .
    rewrite /gcl /pclosed. iSplit.
    - iIntros "[#HT | Hp]"; [by iLeft |].
      iDestruct "Hp" as (v so)
        "(#Hpin & _ & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
      iDestruct "Hext" as (w r gb pre tm) "(#Hpe & Hblk & Hcur & Hrb)".
      assert (Hst : gs_st pipe_lm so = None
                    <-> (gs_E pipe_lm so = [] /\ gs_w pipe_lm so = [])).
      { by destruct Hall as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H13 & _)
                             & _). }
      iRight. iExists v, w, (pstage_o so), r, gb, pre, tm.
      iFrame "Hpin Hpe Hrb".
      rewrite pstream_lm_g. iFrame "Hblk Hcur".
      rewrite (pcount_p_lm _ _ (gs_state pipe_lm tt so)).
      iFrame "Hta Hcs Hps HE Hdl Hdll".
      iPureIntro. apply pcl_pure_lm. by rewrite pstage_g_o.
    - iIntros "[#HT | Hp]"; [by iLeft |].
      iDestruct "Hp" as (v w so r gb pre tm)
        "(#Hpin & #Hpe & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hc)".
      iRight. iExists v, (pstage_g so).
      iFrame "Hpin". iSplitR; [done |].
      iSplitL "Hblk Hcur Hrb".
      { rewrite /pipe_wa /=. iExists w, r, gb, pre, tm.
        rewrite -(pstream_lm_g (pstage_g so)) pstage_o_g.
        iFrame "Hpe Hblk Hcur Hrb". }
      cbn [gs_ps gs_cs gs_E gs_w pstage_g].
      rewrite -(pcount_p_lm _ _ (gs_state pipe_lm tt (pstage_g so))).
      iFrame "Hta Hcs Hps HE Hdl Hdll".
      iPureIntro. by apply pcl_pure_lm.
  Qed.

  (* THE PIPELINE'S CLAIM: the generic one between rounds, [popen] while
     a two-writer round is open (owner ruling 2026-09-23) *)
  Definition pecl (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (gcl pipe_lm pipe_cparams tt pipe_wa k ho H ∨ popen k ho H)%I.

  Global Instance pecl_timeless k ho H : Timeless (pecl k ho H).
  Proof using . rewrite /pecl. apply _. Qed.

  Lemma pecl_gen (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    pecl k ho H ⊣⊢ gcl pipe_lm pipe_cparams tt pipe_wa k ho H ∨ popen k ho H.
  Proof using . done. Qed.

  (* the claim's three readings *)
  Lemma pecl_view (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    pecl k ho H ⊣⊢ T ∨ pclosed k ho H ∨ popen k ho H.
  Proof using .
    rewrite /pecl gcl_pipe_view. iSplit.
    - iIntros "[[H | H] | H]"; [by iLeft | by iRight; iLeft | by iRight; iRight].
    - iIntros "[H | [H | H]]"; [by iLeft; iLeft | by iLeft; iRight | by iRight].
  Qed.

  (* the era's turn authority, from either reading: what the refutations
     that count a third writer's turn read *)
  Lemma pecl_turn_auth (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    pecl k ho H -∗ T ∨ ∃ (v : era_pins) (n : nat), era_pin γ k v ∗ turn_auth v n.
  Proof using .
    rewrite pecl_view. iIntros "[#HT | [Hp | Hp]]"; [by iLeft | |].
    - iDestruct "Hp" as (v w so r gb pre tm) "(#Hpin & _ & _ & _ & _ & Hta & _)".
      iRight. iExists v. iExists _. iFrame "Hpin Hta".
    - iDestruct "Hp" as (v w so r gb pre tm) "(#Hpin & _ & _ & _ & _ & Hta & _)".
      iRight. iExists v. iExists _. iFrame "Hpin Hta".
  Qed.

  (* a tainted era's claim is free *)
  Lemma pecl_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    T -∗ pecl k ho H.
  Proof using . iIntros "#HT". rewrite /pecl /gcl. iLeft. by iLeft. Qed.

  (* THE TAG: [EchoOut.etag] at the PIPELINE discipline, on STAGE's
     corrected shape -- the trace's shape, and either the console is still
     pipe-disciplined or the taint is a permanent fact.  The design page's
     first guess ([etag h ∗ …]) is WRONG and is reported: [etag] carries
     [⌜disc h⌝ ∨ T], which says nothing about the pipeline session, and
     [disc_p h] does NOT imply [disc h] (a pipeline line is not an echo
     line -- [PipeDisc.disc_p_disc] needs the echo-only premise). *)
  Definition ptag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜disc_p h⌝ ∨ T))%I.

  Global Instance ptag_persistent h : Persistent (ptag h).
  Proof using . rewrite /ptag. apply _. Qed.
  Global Instance ptag_timeless h : Timeless (ptag h).
  Proof using . rewrite /ptag. apply _. Qed.

  (* THE CREDENTIAL INIT IS HANDED AT ITS ERA'S FIRST INSTRUCTION.  There
     is nothing to add to [EchoOut.eturn]: the era has no second record. *)
  Definition pturn (k : nat) : iProp Σ := eturn γ k.

  Global Instance pturn_timeless k : Timeless (pturn k).
  Proof using . rewrite /pturn. apply _. Qed.

  (* ---- FILING THE LOG ENTRY, AND OPENING ONE, TAKE NOTHING ---- *)

  (* the open round's side of each: the resources ride along untouched *)
  Lemma popen_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    popen k ho H -∗ popen k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev.
    iIntros "Hp". iDestruct "Hp" as (v w so r gb pre tm) "(Hpin & Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE".
    rewrite ch_dl_close. iFrame "Hdl Hdll". iPureIntro.
    by apply (pcl_pure_o_close k ho so r pre H Hok Hev Hpure).
  Qed.

  Lemma popen_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    disc_seg_p (open_seg h) -> obs_boots h = k ->
    disc_p h -> trace_shape h true ->
    popen k ho H -∗ popen k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh.
    iIntros "Hp". iDestruct "Hp" as (v w so r gb pre tm) "(Hpin & Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. iFrame "Hdl Hdll".
    iPureIntro.
    by apply (pcl_pure_o_open k ho so r pre H h c cs Hok Hev Hd Hb Hdh Hsh Hpure).
  Qed.

  Lemma popen_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    popen k ho CH -∗ popen k ho CH ∗ ⌜ch_arm_era_p k ho CH⌝.
  Proof using .
    iIntros "Hp". iDestruct "Hp" as (v w so r gb pre tm) "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iSplitL.
    - iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE Hdl Hdll". by iPureIntro.
    - iPureIntro. by destruct Hall as (_ & _ & _ & _ & Hera & _).
  Qed.

  Lemma pecl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    pecl k ho H -∗ pecl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite !pecl_gen. iIntros "[Hc | Hc]".
    - iLeft. by iApply (gcl_close with "Hc").
    - iRight. by iApply (popen_close with "Hc").
  Qed.

  Lemma pecl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    disc_seg_p (open_seg h) -> obs_boots h = k ->
    disc_p h -> trace_shape h true ->
    pecl k ho H -∗ pecl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh. rewrite !pecl_gen. iIntros "[Hc | Hc]".
    - iLeft.
      assert (Hd' : lm_disc_input pipe_lm (ins (open_seg h))).
      { by rewrite /disc_seg_p disc_input_p_lm in Hd. }
      apply disc_p_lm in Hdh.
      iApply (gcl_open with "Hc"); first [exact pipe_lm_byte_laws | done].
    - iRight. by iApply (popen_open with "Hc").
  Qed.

  (* THE SUPPLY'S LAW: a tainted era answers any event out of its taint
     arm, which is the whole of [App.al_sup]. *)
  Lemma pecl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ pecl k ho H ==∗ pecl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. rewrite pecl_gen. iLeft. by iLeft. Qed.

  (* what the claim says about an open arm, read back out *)
  Lemma pecl_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    pecl k ho CH -∗
      pecl k ho CH ∗ (T ∨ ⌜ch_arm_era_p k ho CH⌝).
  Proof using .
    rewrite !pecl_gen. iIntros "[Hc | Hc]".
    - iDestruct (gcl_arm with "Hc") as "[Hc Ha]". iSplitL "Hc"; [by iLeft |].
      rewrite ch_arm_era_p_lm. done.
    - iDestruct (popen_arm with "Hc") as "[Hc Ha]". iSplitL "Hc"; [by iRight |].
      by iRight.
  Qed.

  (* ====================================================================== *)
  (*  4.  THE STEPS THE LINKS SPEND                                         *)
  (* ====================================================================== *)

  Lemma pecl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    pro_pin_p ps0 cs0 I0 ->
    proc_stream_p ps0 cs0 I0 !! P = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl". rewrite !pecl_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iAssert (gcW pipe_cparams k tt) as "HW"; [done |].
      iMod (gcl_step_write pipe_lm pipe_cparams tt pipe_wa with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]";
        [exact Hn | by apply pro_pin_p_lm | by rewrite -proc_stream_p_lm |].
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
    (* THE ROUND'S BLOCK CANNOT BE OPEN HERE: an unfiled entry leaves the
       choice list ONE SHORT, and this writer's own bound already needs a
       filed one. *)
    - iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
      { etrans; [exact HI0dl |].
        exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen). }
      destruct (write_stage_byte_p ps0 (o_ps so) cs0 (o_cs so) (o_E so)
                  (o_w so) I0 P b Hpsp Hpin0 Hcsp Hn HI0 HP Hb)
        as [HlenE _].
      destruct Hopen as (_ & Hop & _).
      destruct (pblk_open_cs so r pre Hop) as (Hq & Hrr & Hnn).
      pose proof (prefix_length _ _ Hcsp) as Hcl0.
      rewrite HlenE in Hq, Hrr, Hnn.
      pose proof (nlines_pos_of_rest_nil I0 Hnn Hrr) as Hpos0.
      exfalso. lia.
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE.  Where echo asked for [a < 4]
     and [line_alts_of (last_ws I0) !!! a !! 0 = Some b], the pipeline asks
     for [PipeDisc.palt_ok] at the LINE the block answers and for the first
     byte of THAT alternative's continuation -- which is what "whatever you
     type is echoed back" becomes once a line has two shapes and eight
     alternatives, one of them an interleaving. *)
  Lemma pecl_step_write_blk (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a) ->
    palt_isforkS (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
      !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
         ∨ T).
  Proof using .
    intros Hne0 Hr0 Hn Hpin0 HPeq Hok Hfk Hb.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (pop_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl". rewrite !pecl_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iAssert (gcW pipe_cparams k tt) as "HW"; [done |].
      iMod (gcl_step_write_blk pipe_lm pipe_cparams pipe_lm_byte_laws tt pipe_wa
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]";
        first [exact pipe_lm_byte_laws | done | by apply pro_pin_p_lm
              | by rewrite -(proc_before_p_lm_s _ _ tt) | idtac].
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
    (* THE ROUND'S BLOCK CANNOT BE OPEN HERE EITHER: this writer stands at
       a block's FIRST byte, and an open round has already written one. *)
    - iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
      { etrans; [exact HI0dl |].
        exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen). }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _ & _).
      assert (Hs2 : proc_before_p ps0 cs0 I0
                    = proc_before_p (o_ps so) (o_cs so) I0).
      { apply (proc_before_p_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
                 Hpsp Hcsp Hpin0). lia. }
      pose proof (prefix_length _ _
        (proc_before_p_prefix (o_ps so) (o_cs so) I0 (snd <$> o_E so) HI0))
        as Hle2.
      assert (Hwne : (1 <= length (o_w so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /pcount_p in HP. rewrite HPeq Hs2 in HP.
      exfalso. lia.
  Qed.


  (* (W-open) THE ROUND'S BLOCK OPENS (lane PIPE-2W-3).  The alternative
     is NOT filed -- two processes decide it byte by byte -- so instead of
     growing [cs] the claim MINTS the round's own ledger, points the
     current-round ghost at it, and hands the writer HALF of that ghost
     with the ledger's first bound.  From here the claim reads the block
     off the ledger ([pcl_pure_o]) until the prompt files the code. *)
  Lemma pecl_blk2_open_gen (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
      !! 0%nat = Some b ->
    ((palt_isforkS (palt_of a) = false /\ nodollar b)
     \/ palt_isforkS (palt_of a) = true) ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (w : pipe_era) (gb : gname),
            turn v (S P) ∗ pera_pin g k w
            ∗ cur_half w (1/2) (nlines I0 - 1)%nat gb
                (palt_isforkS (palt_of a))
            ∗ rblk_lb gb [b]
            ∗ (⌜palt_isforkS (palt_of a) = false⌝
               ∨ cs_frozen_at v (nlines I0 - 1)%nat)
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hpan Hhead Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (pop_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iEval (rewrite pecl_view) in "Hcl".
    iDestruct "Hcl" as "[#HT | [Hp | Hp]]".
    { iModIntro. iSplitR; [by iApply pecl_taint | by iRight]. }
    2: { (* THE ROUND'S BLOCK CANNOT BE OPEN HERE EITHER: this writer stands
           at a block's FIRST byte, and an open round has already written
           one. *)
      iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
      { etrans; [exact HI0dl | exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen)]. }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _ & _).
      assert (Hs2 : proc_before_p ps0 cs0 I0
                    = proc_before_p (o_ps so) (o_cs so) I0).
      { apply (proc_before_p_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
                 Hpsp Hcsp Hpin0). lia. }
      pose proof (prefix_length _ _
        (proc_before_p_prefix (o_ps so) (o_cs so) I0 (snd <$> o_E so) HI0))
        as Hle2.
      assert (Hwne : (1 <= length (o_w so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /pcount_p in HP. rewrite HPeq Hs2 in HP.
      exfalso. lia. }
    iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (pcs_of_auth v2 (o_cs so) false eq_refl with "Hcs") as "Hcs".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (pcl_pure_dl_E _ _ _ _ Hall)]. }
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk).
    pose proof Hcsb' as Hcsb.
    assert (Hstream : proc_before_p ps0 cs0 I0
                      = proc_before_p (o_ps so) (o_cs so) I0).
    { apply (proc_before_p_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
               Hpsp Hcsp Hpin0). lia. }
    (* the era's input is exactly [I0] *)
    assert (HlenE : (snd <$> o_E so) = I0).
    { destruct (decide ((snd <$> o_E so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (proc_stream_p_before (o_ps so) (o_cs so) I0 (snd <$> o_E so)
                    HI0 ltac:(intros Hq; apply Hne; symmetry; exact Hq))
        as Hpre.
      apply prefix_length in Hpre.
      rewrite /proc_stream_p length_app -Hstream in Hpre.
      assert (Hne1 : pending_at_p (o_ps so) (o_cs so) I0 <> [])
        by (exact (pending_at_p_nonnil_pre (o_ps so) (o_cs so) I0
                     (snd <$> o_E so) HI0 Hcsb' Hne0 Hr0)).
      assert (Hlen1 : (1 <= length (pending_at_p (o_ps so) (o_cs so) I0))%nat).
      { destruct (pending_at_p (o_ps so) (o_cs so) I0); [done | cbn; lia] . }
      rewrite /pcount_p in HP. lia. }
    (* ...and the writer stands at the line's first byte *)
    assert (Hwnil : o_w so = []).
    { assert (Hz : length (o_w so) = 0%nat).
      { rewrite /pcount_p in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = o_cs so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    assert (Hpc2 : pcount_p (o_ps so) (o_cs so) (o_E so) [b] = S P).
    { rewrite /pcount_p HlenE -Hstream. cbn [length]. lia. }
    (* the round's OWN ledger, minted here and nowhere else *)
    iMod rblk_alloc as (gb2) "Hrb2".
    iMod (rblk_auth_grow gb2 [] b with "Hrb2") as "[Hrb2 #Hrlb]".
    iMod (cur_retarget w r gb tm (nlines I0 - 1)%nat gb2
            (palt_isforkS (palt_of a)) with "Hcur") as "Hcur".
    iDestruct (cur_split w (nlines I0 - 1)%nat gb2
                 (palt_isforkS (palt_of a)) with "Hcur")
      as "[Hcur1 Hcur2]".
    (* THE TERMINAL FIRE (design SS4.3m): a round whose alternative is a
       [PForkS] is never filed, so its resolution is FROZEN here and the
       writer carries the persisted authority away. *)
    iAssert (|==> pcs v (o_cs so) (palt_isforkS (palt_of a))
                  ∗ (⌜palt_isforkS (palt_of a) = false⌝
                     ∨ cs_frozen_at v (nlines I0 - 1)%nat))%I
      with "[Hcs]" as ">[Hcs #Hfz]".
    { destruct (palt_isforkS (palt_of a)) eqn:Hfk2.
      - iMod (pcs_freeze v (o_cs so) false with "Hcs") as "[Hcs #Hf]".
        iModIntro. iFrame "Hcs". iRight.
        iApply (cs_frozen_at_of v (o_cs so) (nlines I0 - 1)%nat with "Hf").
        by rewrite Hq.
      - iModIntro. iFrame "Hcs". iLeft. by iPureIntro. }
    iMod (turn_update v P (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (pstream so) b with "Hblk") as "[Hblk _]".
    iModIntro. iSplitR "Ht Hcur2".
    - rewrite pecl_view. iRight. iRight.
      iExists v, w, (MkO (o_ps so) (o_cs so) (o_E so) [b]),
              (nlines I0 - 1)%nat, gb2, [b],
              (palt_isforkS (palt_of a)).
      cbn [o_ps o_cs o_E o_w]. rewrite Hpc2.
      rewrite (_ : pstream (MkO (o_ps so) (o_cs so) (o_E so) [b])
                   = pstream so ++ [b]); last first.
      { rewrite /pstream. cbn [o_ps o_cs o_E o_w]. by rewrite Hwnil app_nil_r. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hblk Hcur1 Hrb2 Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (pcl_pure_o_out k ho so (MkO (o_ps so) (o_cs so) (o_E so) [b])
               (nlines I0 - 1)%nat [b] H b);
        [cbn [o_cs]; lia | reflexivity | | | | | exact Hall0].
      + rewrite /pout_pure_o. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc Hwnil app_nil_r. reflexivity.
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
      + rewrite /pblk_open. cbn [o_ps o_cs o_E o_w].
        split_and!; [by rewrite HlenE | reflexivity | done |].
        exists a. split.
        { rewrite /pblk2_at. rewrite HlenE.
          split_and!; [exact Hne0 | exact Hr0 | exact Hq | exact Halt
                      | exact Hpan |].
          apply (pop_prefix_snoc_lookup [] _ b);
            [apply prefix_nil | exact Hhead]. }
        destruct Hfarm as [[Hfk Hnd] | Hfk];
          [left; split; [exact Hfk | by apply Forall_singleton, Hnd]
           | by right].
      + pose proof (ps_len_ok_p_write so b Hpsl) as Hx.
        rewrite Hwnil in Hx. exact Hx.
      + apply (dl_ok_out_full so (MkO (o_ps so) (o_cs so) (o_E so) [b]));
          [reflexivity | cbn [o_w]; discriminate | by rewrite HlenE |].
        pose proof (prefix_length _ _ HI0dl) as Hlp.
        rewrite !length_fmap in Hlp. rewrite HlenE. lia.
    - iLeft. iExists w, gb2.
      iFrame "Ht Hpera Hcur2 Hrlb Hfz Hpslb Hcslb Hilb".
  Qed.

  (* (W-blk2) A FURTHER BYTE OF AN OPEN ROUND.  The writer's half of the
     current-round ghost is what says its round and its ledger ARE the
     claim's -- a family minted for an earlier round agrees with neither
     ([cur_half_agree]), and between rounds the claim holds the ghost
     WHOLE, so an ordinary state and a writer's half cannot coexist
     ([cur_half_excl]).  The ledger then pins the block's BYTES, which
     [turn] alone cannot (PIPE-2W's [pend_both_not_inj]). *)
  Lemma pecl_blk2_byte_gen (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (tmi : bool) (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    (pre0 ++ [b]) `prefix_of`
      pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    ((palt_isforkS (palt_of a) = false /\ Forall nodollar pre0 /\ nodollar b)
     \/ palt_isforkS (palt_of a) = true) ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb tmi -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat
          ∗ cur_half w (1/2) r gb (tmi || palt_isforkS (palt_of a))
          ∗ rblk_lb gb (pre0 ++ [b])
          ∗ (⌜palt_isforkS (palt_of a) = false⌝ ∨ cs_frozen_at v r)) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hpref Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iEval (rewrite pecl_view) in "Hcl".
    iDestruct "Hcl" as "[#HT | [Hp | Hp]]".
    { iModIntro. iSplitR; [by iApply pecl_taint | by iRight]. }
    (* the claim cannot be BETWEEN rounds: it would hold the whole ghost *)
    { iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm) "(_ & #Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    (* the ledger pins the block's bytes: a lower bound of equal length *)
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    assert (Hlen0 : length pre0 = length (o_w so)).
    { rewrite /pcount_p in HP.
      assert (Hs2 : proc_before_p ps0 cs0 I0
                    = proc_before_p (o_ps so) (o_cs so) I0).
      { apply (proc_before_p_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
                 Hpsp Hcsp Hpin0).
        rewrite (pop_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
      assert (HIeq : (snd <$> o_E so) = I0).
      { destruct (decide ((snd <$> o_E so) = I0)) as [? | Hne]; [done |].
        exfalso.
        pose proof (proc_stream_p_before (o_ps so) (o_cs so) I0
                      (snd <$> o_E so) HI0
                      ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
        apply prefix_length in Hp2.
        rewrite /proc_stream_p length_app -Hs2 in Hp2.
        assert (Hne1 : pending_at_p (o_ps so) (o_cs so) I0 <> [])
          by (exact (pending_at_p_nonnil_pre (o_ps so) (o_cs so) I0
                       (snd <$> o_E so) HI0 Hcsb' Hne0 Hr0)).
        assert (Hlen1 : (1 <= length (pending_at_p (o_ps so) (o_cs so) I0))%nat)
          by (destruct (pending_at_p (o_ps so) (o_cs so) I0); [done | cbn; lia]).
        lia. }
      rewrite HIeq -Hs2 HPeq in HP. lia. }
    assert (Hpre0 : pre0 = o_w so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    (* THE TERMINAL FIRE (design SS4.3m).  A byte whose alternative is a
       [PForkS] sets the round's TERMINAL FLAG -- both halves are here, so
       the update is available -- and FREEZES the claim's resolution: the
       round is never filed, so [cs] never grows again, and the writer
       carries the persisted authority away.  At a non-fork byte the flag
       is left exactly where it was. *)
    iAssert (|==> pcs v (o_cs so) (tmi || palt_isforkS (palt_of a))
                  ∗ cur_half w (1/2) r gb (tmi || palt_isforkS (palt_of a))
                  ∗ cur_half w (1/2) r gb (tmi || palt_isforkS (palt_of a))
                  ∗ (⌜palt_isforkS (palt_of a) = false⌝
                     ∨ cs_frozen_at v r))%I
      with "[Hcs Hcur Hcw]" as ">(Hcs & Hcur & Hcw & #Hfz)".
    { destruct (palt_isforkS (palt_of a)) eqn:Hfk2.
      - rewrite (orb_true_r tmi).
        iMod (pcs_freeze v (o_cs so) tmi with "Hcs") as "[Hcs #Hf]".
        iMod (cur_half_update w r gb tmi r gb tmi r gb true
                with "Hcur Hcw") as "[Hcur Hcw]".
        iModIntro. iFrame "Hcs Hcur Hcw". iRight.
        iApply (cs_frozen_at_of v (o_cs so) r with "Hf").
        by rewrite Hqq Hreq2.
      - rewrite (orb_false_r tmi).
        iModIntro. iFrame "Hcs Hcur Hcw". iLeft. by iPureIntro. }
    iMod (rblk_auth_grow gb pre b with "Hrb") as "[Hrb #Hrlb1]".
    iMod (turn_update v (P + length pre0)%nat
            (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
            (S (P + length pre0)) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (pstream so) b with "Hblk") as "[Hblk _]".
    (* the round's line is the writer's line *)
    assert (Hbod : bodies_of (snd <$> o_E so) !!! r = bodies_of I0 !!! r).
    { destruct (bodies_of_prefix I0 (snd <$> o_E so) HI0) as [z Hz].
      rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite Hreq /nlines in Hpos0 |- *; lia]. }
    iModIntro. iSplitR "Ht Hcw".
    - rewrite pecl_view. iRight. iRight.
      iExists v, w, (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])),
              r, gb, (pre ++ [b]),
              (tmi || palt_isforkS (palt_of a)).
      cbn [o_ps o_cs o_E o_w]. rewrite pcount_p_write -HP.
      rewrite (pstream_write (o_ps so) (o_cs so) (o_E so) (o_w so) b).
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (pcl_pure_o_out2 k ho so
               (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b]))
               r r pre (pre ++ [b]) H b);
        [cbn [o_cs]; lia | reflexivity | | | | | exact Hopen].
      + rewrite /pout_pure_o. cbn [o_ps o_cs o_E o_w]. split_and!.
        * by rewrite Hacc app_assoc.
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
      + rewrite /pblk_open. cbn [o_ps o_cs o_E o_w].
        split_and!; [exact Hreq2 | by rewrite Hwp'
                    | by destruct (pre ++ [b]) eqn:Hz;
                      [ destruct (app_eq_nil pre [b] Hz) as [_ Hb2']
                      | done ] |].
        exists a. split.
        { rewrite /pblk2_at -Hreq2 Hbod.
          split_and!; [exact Hnn | exact Hrr | by rewrite Hqq Hreq2
                      | exact Halt | exact Hpan |].
          rewrite -Hwp' -Hpre0. exact Hpref. }
        destruct Hfarm as [(Hfk & Hnd0 & Hnd) | Hfk]; [| by right].
        left. split; [exact Hfk |].
        apply Forall_app. split; [| by apply Forall_singleton, Hnd].
        rewrite -Hwp' -Hpre0. exact Hnd0.
      + exact (ps_len_ok_p_write so b Hpsl).
      + apply (dl_ok_out so (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])));
          [reflexivity | cbn [o_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite Hpre0 -Hwp'. iFrame "Ht Hcw Hrlb1 Hfz".
  Qed.

  (* ---- THE TWO STEPS AT THE NON-TERMINAL ARM (the landed statements,
          byte for byte): an ordinary round's block is `$'-free and its
          alternative is not a [PForkS]. ---- *)
  Lemma pecl_blk2_open (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
      !! 0%nat = Some b ->
    nodollar b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (w : pipe_era) (gb : gname),
            turn v (S P) ∗ pera_pin g k w
            ∗ cur_half w (1/2) (nlines I0 - 1)%nat gb false ∗ rblk_lb gb [b]
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hpan Hfk Hhead Hnd.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iMod (pecl_blk2_open_gen k v P a b ps0 cs0 I0 ho H Hne0 Hr0 Hdiv Hpin0
            HPeq Halt Hpan Hhead (or_introl (conj Hfk Hnd))
            with "Hpin Ht Hpslb Hcslb Hilb Hcl") as "[Hcl Hr]".
    iModIntro. iFrame "Hcl". rewrite Hfk.
    iDestruct "Hr" as "[Hx | #HT]"; [| by iRight]. iLeft.
    iDestruct "Hx" as (w gb) "(Ht & Hpera & Hcur & Hrlb & _ & Hps & Hcs & Hi)".
    iExists w, gb. iFrame "Ht Hpera Hcur Hrlb Hps Hcs Hi".
  Qed.

  Lemma pecl_blk2_byte (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = false ->
    (pre0 ++ [b]) `prefix_of`
      pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    Forall nodollar pre0 ->
    nodollar b ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat ∗ cur_half w (1/2) r gb false
          ∗ rblk_lb gb (pre0 ++ [b])) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hpref Hnd0 Hnd.
    iIntros "#Hpin #Hpera Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iMod (pecl_blk2_byte_gen k v w gb false P r a b pre0 ps0 cs0 I0 ho H
            Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hpref
            (or_introl (conj Hfk (conj Hnd0 Hnd)))
            with "Hpin Hpera Ht Hcw Hrlb0 Hpslb Hcslb Hilb Hcl")
      as "[Hcl Hr]".
    iModIntro. iFrame "Hcl". rewrite Hfk. cbn [orb].
    iDestruct "Hr" as "[Hx | #HT]"; [| by iRight]. iLeft.
    iDestruct "Hx" as "(Ht & Hcw & Hrlb & _)". iFrame "Ht Hcw Hrlb".
  Qed.

  (* ===================================================================== *)
  (*  THE TERMINAL ROUND'S TWO BYTE STEPS (lane PIPE-STAGE-3, design        *)
  (*  section 4.3h).  The twins of the two above at a [PForkS]              *)
  (*  alternative: the block MAY carry the prompt's `$' (it is inside       *)
  (*  [alt_forkc]) and the round's bytes are NOT `$'-free, so the claim      *)
  (*  reconstructs [pblk_open]'s RIGHT arm -- where D4, and not              *)
  (*  `$'-freeness, is what refutes the next input ([pecl_step_echo]'s       *)
  (*  terminal case).  THERE IS NO TERMINAL FILING STEP: a fork-failure     *)
  (*  round never signals completion, so its code never enters [cs] and     *)
  (*  the claim's [cs_nofork] is untouched.                                 *)
  (* ===================================================================== *)
  Lemma pecl_blk2_open_t (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = true ->
    pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
      !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (w : pipe_era) (gb : gname),
            turn v (S P) ∗ pera_pin g k w
            ∗ cur_half w (1/2) (nlines I0 - 1)%nat gb true ∗ rblk_lb gb [b]
            ∗ cs_frozen_at v (nlines I0 - 1)%nat
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hpan Hfk Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iMod (pecl_blk2_open_gen k v P a b ps0 cs0 I0 ho H Hne0 Hr0 Hdiv Hpin0
            HPeq Halt Hpan Hhead (or_intror Hfk)
            with "Hpin Ht Hpslb Hcslb Hilb Hcl") as "[Hcl Hr]".
    iModIntro. iFrame "Hcl". rewrite Hfk.
    iDestruct "Hr" as "[Hx | #HT]"; [| by iRight]. iLeft.
    iDestruct "Hx"
      as (w gb) "(Ht & Hpera & Hcur & Hrlb & Hfz & Hps & Hcs & Hi)".
    iDestruct "Hfz" as "[%Hbad | #Hfz]"; [discriminate Hbad |].
    iExists w, gb. iFrame "Ht Hpera Hcur Hrlb Hfz Hps Hcs Hi".
  Qed.

  Lemma pecl_blk2_byte_t (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (tmi : bool) (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = true ->
    (pre0 ++ [b]) `prefix_of`
      pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb tmi -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat ∗ cur_half w (1/2) r gb true
          ∗ rblk_lb gb (pre0 ++ [b]) ∗ cs_frozen_at v r) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hpref.
    iIntros "#Hpin #Hpera Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iMod (pecl_blk2_byte_gen k v w gb tmi P r a b pre0 ps0 cs0 I0 ho H
            Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hpref (or_intror Hfk)
            with "Hpin Hpera Ht Hcw Hrlb0 Hpslb Hcslb Hilb Hcl")
      as "[Hcl Hr]".
    iModIntro. iFrame "Hcl". rewrite Hfk (orb_true_r tmi).
    iDestruct "Hr" as "[Hx | #HT]"; [| by iRight]. iLeft.
    iDestruct "Hx" as "(Ht & Hcw & Hrlb & Hfz)".
    iDestruct "Hfz" as "[%Hbad | #Hfz]"; [discriminate Hbad |].
    iFrame "Ht Hcw Hrlb Hfz".
  Qed.

  Lemma pecl_blk2_file (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) = pre0 ++ u_prompt ->
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho H ==∗
      pecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat ∗ ps_lb v ps0
          ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T).
  Proof using .
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hcont Hbv.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iEval (rewrite pecl_view) in "Hcl".
    iDestruct "Hcl" as "[#HT | [Hp | Hp]]".
    { iModIntro. iSplitR; [by iApply pecl_taint | by iRight]. }
    (* the claim cannot be BETWEEN rounds: it would hold the whole ghost *)
    { iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm) "(_ & #Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
    { etrans; [exact HI0dl | exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    (* the ledger pins the block's bytes: a lower bound of equal length *)
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    assert (Hlen0 : length pre0 = length (o_w so)).
    { rewrite /pcount_p in HP.
      assert (Hs2 : proc_before_p ps0 cs0 I0
                    = proc_before_p (o_ps so) (o_cs so) I0).
      { apply (proc_before_p_cs_prefix ps0 (o_ps so) cs0 (o_cs so) I0
                 Hpsp Hcsp Hpin0).
        rewrite (pop_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
      assert (HIeq : (snd <$> o_E so) = I0).
      { destruct (decide ((snd <$> o_E so) = I0)) as [? | Hne]; [done |].
        exfalso.
        pose proof (proc_stream_p_before (o_ps so) (o_cs so) I0
                      (snd <$> o_E so) HI0
                      ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
        apply prefix_length in Hp2.
        rewrite /proc_stream_p length_app -Hs2 in Hp2.
        assert (Hne1 : pending_at_p (o_ps so) (o_cs so) I0 <> [])
          by (exact (pending_at_p_nonnil_pre (o_ps so) (o_cs so) I0
                       (snd <$> o_E so) HI0 Hcsb' Hne0 Hr0)).
        assert (Hlen1 : (1 <= length (pending_at_p (o_ps so) (o_cs so) I0))%nat)
          by (destruct (pending_at_p (o_ps so) (o_cs so) I0); [done | cbn; lia]).
        lia. }
      rewrite HIeq -Hs2 HPeq in HP. lia. }
    assert (Hpre0 : pre0 = o_w so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    iMod (turn_update v (P + length pre0)%nat
            (pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so))
            (S (P + length pre0)) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (pstream so) b with "Hblk") as "[Hblk _]".
    (* THE FILING IS REFUTED AT A TERMINAL ROUND (design SS4.3m): the filer
       presents its own half of the current-round ghost at [tm = false],
       and [cur_half_agree] has already forced the CLAIM's flag to match,
       so the authority here is the landed [cs_auth] and never the frozen
       one.  This is the step the freeze was waiting for. *)
    iDestruct (pcs_auth v (o_cs so) false eq_refl with "Hcs") as "Hcs".
    iMod (cs_auth_grow v (o_cs so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    (* the writer's half comes home *)
    iDestruct (cur_join w r gb false with "Hcur Hcw") as "Hcur".
    (* the round's line is the writer's line *)
    assert (Hbod : bodies_of (snd <$> o_E so) !!! r = bodies_of I0 !!! r).
    { destruct (bodies_of_prefix I0 (snd <$> o_E so) HI0) as [z Hz].
      rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite Hreq /nlines in Hpos0 |- *; lia]. }
    pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposc.
    assert (Hcseq2 : length cs0 = length (o_cs so))
      by (rewrite Hcseq Hreq2 Hqq; reflexivity).
    assert (Hcs0 : cs0 = o_cs so)
      by exact (prefix_length_eq cs0 (o_cs so) Hcsp ltac:(lia)).
    assert (HpendA : pending_p (o_ps so) (o_cs so ++ [a]) (o_E so)
                     = pre0 ++ u_prompt).
    { rewrite /pending_p
        (pending_at_p_filed_gen (o_ps so) (o_cs so) (snd <$> o_E so) a
           Hnn Hrr Hqq Hpan).
      by rewrite -Hreq2 Hbod Hcont. }
    assert (Hpinq : pro_pin_p (o_ps so) (o_cs so ++ [a]) (snd <$> o_E so)).
    { intros qq Hqq2. rewrite pro_idx_p_app_le; [by apply Hpin |].
      rewrite (pop_nstarted_rest_nil _ Hrr) in Hqq2. rewrite Hqq. lia. }
    assert (Hrlbnd : (nlines (removelast (snd <$> o_E so))
                      <= length (o_cs so))%nat).
    { rewrite (pop_nlines_removelast _ Hrr) Hqq. lia. }
    assert (HD : D_p (o_ps so) (o_cs so ++ [a]) (o_E so)
                 = D_p (o_ps so) (o_cs so) (o_E so)).
    { symmetry. apply (D_p_cs_prefix (o_ps so) (o_ps so) (o_cs so)
                         (o_cs so ++ [a]) (o_E so));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hpceq : pcount_p (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])
                    = pcount_p (o_ps so) (o_cs so ++ [a]) (o_E so)
                        (o_w so ++ [b])).
    { apply (pcount_p_cs_prefix (o_ps so) (o_ps so) (o_cs so)
               (o_cs so ++ [a]) (o_E so) (o_w so ++ [b]));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hao2 : alts_pre_p (snd <$> o_E so) (o_cs so ++ [a])).
    { apply alts_pre_p_snoc; [exact Hcsb' | rewrite Hqq; lia |].
      rewrite Hqq -Hreq2 Hbod. exact Halt. }
    iModIntro. iSplitR "Ht".
    - rewrite pecl_view. iRight. iLeft.
      iExists v, w, (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) (o_w so ++ [b])),
              r, gb, pre, false.
      cbn [o_ps o_cs o_E o_w]. rewrite -Hpceq pcount_p_write -HP.
      rewrite (pstream_blk_w (o_ps so) (o_cs so) (o_E so) a (o_w so) b
                 Hpin Hrlbnd).
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (pcl_pure_of_o_out k ho so
               (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) (o_w so ++ [b]))
               r pre H b);
        [cbn [o_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | | | | exact Hopen].
      + rewrite /pout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * rewrite HpendA -Hpre0 Hbv. apply prefix_app.
          exists (drop 1 u_prompt).
          rewrite -{1}(take_drop 1 u_prompt). f_equal.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * exact Hao2.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * rewrite /cs_nofork. cbn [o_cs].
          apply Forall_app. split; [exact Hnofk |].
          apply Forall_singleton. exact Hfk.
      + rewrite /cs_len_ok. cbn [o_ps o_cs o_E o_w].
        rewrite decide_False; [rewrite length_app Hqq; cbn [length]; lia |].
        intros [Hz _]. by destruct (app_eq_nil (o_w so) [b] Hz) as [_ Hb2'].
      + exact (ps_len_ok_p_blk_w so a (o_w so ++ [b]) Hrr Hnn Hqq Hpsl).
      + apply (dl_ok_out so (MkO (o_ps so) (o_cs so ++ [a]) (o_E so)
                               (o_w so ++ [b])));
          [reflexivity | cbn [o_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite Hcs0. iFrame "Ht Hpslb Hcslb2 Hilb".
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE.  The
     round-opening test is [palt_panic] of the last line's alternative, so
     an [LPipe] line reaches it exactly as an [LEcho] one does (PIPE-MODEL-2's
     ruling: [PEcho 3] is admitted at BOTH shapes). *)
  Lemma pecl_step_write_pro (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ palt_panic (palt_at cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    pro_pin_p ps0 cs0 I0 ->
    ~ pro_done (pro_from (pro_idx_p cs0 (nlines I0)) ps0) ->
    P = length (proc_stream_p ps0 cs0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl k ho CH ==∗
      pecl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
         ∨ T).
  Proof using .
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    pose proof (pop_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl". rewrite !pecl_gen.
    iDestruct "Hcl" as "[Hc | Hp]".
    - iAssert (gcW pipe_cparams k tt) as "HW"; [done |].
      iMod (gcl_step_write_pro pipe_lm pipe_cparams tt pipe_wa
              with "Hpin Ht Hpslb Hcslb Hilb HW Hc") as "[Hc Hr]";
        first [exact (or_intror (or_intror I)) | done | by apply pro_pin_p_lm
              | by rewrite -pro_idx_p_lm | by rewrite -proc_stream_p_lm | idtac].
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[(Ht & Hps & Hcs & Hi & _) | HT]"; [iLeft; by iFrame | by iRight].
    (* AND NOT HERE: a prologue round's byte comes after the whole stream
       through [I0], which an open round's own bytes already run past. *)
    - iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen2)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> o_E so)).
      { etrans; [exact HI0dl |].
        exact (pcl_pure_o_dl_E _ _ _ _ _ _ Hopen2). }
      pose proof Hopen2 as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & a0 & Hb2 & _).
      pose proof Hb2 as (Hne0' & Hrr & Hqq & _).
      assert (Hwne : (1 <= length (o_w so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /pcount_p in HP.
      destruct (decide ((snd <$> o_E so) = I0)) as [Heq | Hne2].
      + rewrite Heq in Hqq, Hrr, Hne0'.
        pose proof (nlines_pos_of_rest_nil I0 Hne0' Hrr) as Hpos0.
        pose proof (prefix_length _ _ Hcsp) as Hcl0.
        exfalso. lia.
      + pose proof (proc_stream_p_before (o_ps so) (o_cs so) I0
                      (snd <$> o_E so) HI0
                      ltac:(intros Hq; apply Hne2; symmetry; exact Hq))
          as Hpre2.
        apply prefix_length in Hpre2.
        pose proof (prefix_length _ _
          (proc_stream_p_prefix ps0 (o_ps so) cs0 (o_cs so) I0
             Hpsp Hcsp Hpin0 Hdiv)) as Hle3.
        exfalso. lia.
  Qed.

  (* ---- THE READ ---- *)

  Lemma cs_lb_weaken_p (v : era_pins) (l l' : list nat) :
    l' `prefix_of` l -> cs_lb v l -∗ cs_lb v l'.
  Proof using .
    intros Hp. rewrite /cs_lb. iIntros "H".
    iApply (own_mono with "H"). by apply mono_list_lb_mono.
  Qed.

  Lemma pein_read_pure (k : nat) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (cs0 : list nat) :
    read_ok pops dl ws -> pein_pure k pops dl cs0 ->
    (dl ++ ws) `prefix_of` echoed pops
    /\ pein_pure k pops (dl ++ ws) cs0
    /\ (nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat.
  Proof using .
    intros Hread (Hlog & Hdisc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd & Hall).
    assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
    { intros e He. eapply disc_seg_p_no_erase; [by apply Hdisc |].
      apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
    assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
      by (eapply read_window_prefix;
          [exact Hlog | exact Hread | exact Hnoer | exact Hdlp]).
    split; [exact Hpref |]. split.
    - rewrite /pein_pure. split_and!;
        [exact Hlog | exact Hdisc | exact Hstamp | exact Hpref | exact Hidx
         | exact Hbyte | exact Hbnd | exact Hall].
    - etrans; [| exact Hbnd]. apply nlines_prefix, epu_fmap_prefix, Hpref.
  Qed.

  Lemma popen_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ popen k ho CH ==∗
      popen k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ ((T ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)%nat
           ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
           ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws)
              `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
           ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜E_disc_p (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           ∗ ⌜disc_input_p (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ ⌜(nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                      <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_p ps0 cs0
                                 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
                  ∗ ⌜rd_stage_p ps0 cs0
                       (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝)).
  Proof using .
    intros Hread. iIntros "#Hpinr Hdlr Hp".
    iDestruct "Hp" as (v2 w so r gb pre tm) "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hpo)".
    iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
    iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
    pose proof (pcl_pure_o_pein k ho so r pre CH Hpo) as Hin.
    pose proof Hin as Hin2.
    destruct Hin2 as (_ & _ & _ & _ & Hidx & Hbyte & _).
    destruct (pein_read_pure k (LogEntryDefs.ch_log CH)
                (LogEntryDefs.ch_dl CH) ws (o_cs so) Hread Hin)
      as (Hpref & Hp' & Hbnd').
    assert (HEpre : (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                    `prefix_of` (snd <$> o_E so)).
    { rewrite (pcl_pure_o_E k ho so r pre CH Hpo) /ch_E.
      etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
      rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log CH))).
      apply epu_fmap_prefix. by apply prefix_app_r. }
    assert (Hdi : disc_input_p (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    { apply (disc_input_p_prefix _ (snd <$> o_E so) HEpre).
      by destruct (proj1 Hpo)
        as (_ & _ & Hd & _). }
    pose proof (pcl_pure_o_rd_stage k ho so r pre CH Hpo) as Hrd.
    pose proof Hrd as (Hpsb & Hcsb' & Hpinf & Hbd).
    (* THE READER EXPORTS A TRUNCATED CHOICE LIST: the claim's list may run
       past the window's far end, and [alts_pre_p] ties every entry to the
       line at its index -- so what comes out is the claim's list cut to the
       WINDOW's own line count.  With [EchoOut]'s input-free
       [Forall (fun c => c < 4) cs] there was nothing to truncate; this is
       upstream STAGE's finding at the pipeline session. *)
    set (Iw := (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    set (q := nlines Iw).
    set (csq := take q (o_cs so)).
    assert (Hqle : (nlines (removelast Iw) <= length csq)%nat).
    { rewrite /csq length_take.
      assert (H1 : (nlines (removelast Iw) <= q)%nat)
        by (apply nlines_prefix, pop_removelast_prefix).
      assert (H2 : (nlines (removelast Iw) <= length (o_cs so))%nat).
      { etrans; [| exact Hbd].
        apply nlines_prefix, pop_prefix_removelast, HEpre. }
      lia. }
    assert (Hagree : forall j, (j < q)%nat -> csq !!! j = o_cs so !!! j).
    { intros j Hj. rewrite /csq !list_lookup_total_alt.
      destruct (decide (j < length (o_cs so))%nat) as [Hl | Hl].
      - rewrite lookup_take; [done | lia].
      - rewrite (lookup_ge_None_2 (o_cs so) j ltac:(lia)).
        rewrite (lookup_ge_None_2 (take q (o_cs so)) j);
          [done | rewrite length_take; lia]. }
    assert (Hqbnd : (q <= S (length csq))%nat).
    { rewrite /csq length_take.
      destruct (decide (q <= length (o_cs so))%nat) as [Hl | Hl]; [lia |].
      rewrite /q /Iw. lia. }
    assert (Hpbq : proc_before_p (o_ps so) csq Iw
                   = proc_before_p (o_ps so) (o_cs so) Iw).
    { apply proc_before_p_ext. intros J HJ Hne.
      apply (pending_at_p_cs_ext (o_ps so) csq (o_cs so) J).
      - rewrite /csq. apply prefix_take.
      - etrans; [| exact Hqle].
        apply nlines_prefix, (pop_prefix_of_removelast J Iw HJ Hne). }
    assert (Hrdq : rd_stage_p (o_ps so) csq Iw).
    { rewrite /rd_stage_p. split_and!; [exact Hpsb | | | exact Hqle].
      - intros i c Hc.
        assert (Hci : o_cs so !! i = Some c)
          by (rewrite /csq in Hc; by apply lookup_take_Some in Hc as [? _]).
        assert (Hiq : (i < q)%nat).
        { apply lookup_lt_Some in Hc. rewrite /csq length_take in Hc. lia. }
        destruct (Hcsb' i c Hci) as [_ Hok].
        split; [exact Hiq |].
        destruct (bodies_of_prefix Iw (snd <$> o_E so) HEpre) as [z Hz].
        rewrite Hz !list_lookup_total_alt lookup_app_l in Hok;
          [| rewrite /q /nlines in Hiq; lia].
        by rewrite -!list_lookup_total_alt in Hok.
      - intros q' Hq'.
        assert (Hq'q : (q' <= q)%nat).
        { pose proof (nstarted_le_S Iw). rewrite /q. lia. }
        rewrite (pro_idx_p_ext csq (o_cs so) q
                   ltac:(intros j Hj; apply Hagree; lia) q' Hq'q).
        apply Hpinf. pose proof (nstarted_prefix Iw (snd <$> o_E so) HEpre).
        lia. }
    iDestruct (pcs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (cs_lb_weaken_p v (o_cs so) csq
                 ltac:(rewrite /csq; apply prefix_take) with "Hcslb")
      as "#Hcslbq".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iDestruct (turn_lb_get with "Hta") as "#Htlb".
    iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n
            (n + length ws)%nat with "Hdl Hdlr") as "[Hdl Hdlr]".
    iMod (dl_list_auth_grow v (LogEntryDefs.ch_dl CH) ws with "Hdll")
      as "[Hdll #Hdllb]".
    iModIntro. iSplitL "Hta Hcs Hps HE Hdl Hdll Hblk Hcur Hrb".
    { iExists v, w, so, r, gb, pre, tm.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite length_app Hdleq.
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      exact (pcl_pure_o_read k ho so r pre CH ws Hpref Hpo). }
    iRight. iFrame "Hdlr".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR.
    { iApply (inp_lb_of_dl_lb v (LogEntryDefs.ch_dl CH ++ ws) _
                (reflexivity _)). iExact "Hdllb". }
    iSplitR; [by iPureIntro |].
    iRight. iExists csq, (o_ps so). iFrame "Hcslbq Hpslb".
    iSplitR; [by iPureIntro |].
    iSplitR.
    { assert (Hle2 : (length (proc_before_p (o_ps so) csq Iw)
                      <= pcount_p (o_ps so) (o_cs so) (o_E so)
                           (o_w so))%nat).
      { rewrite /pcount_p Hpbq.
        pose proof (prefix_length _ _
                      (proc_before_p_prefix (o_ps so) (o_cs so) Iw
                         (snd <$> o_E so) HEpre)) as Hlp. lia. }
      iApply (turn_lb_weaken with "Htlb"). exact Hle2. }
    iPureIntro. exact Hrdq.
  Qed.

  Lemma pecl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ pecl k ho CH ==∗
      pecl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ ((T ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)%nat
           ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
           ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws)
              `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
           ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜E_disc_p (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           ∗ ⌜disc_input_p (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ ⌜(nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                      <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_p ps0 cs0
                                 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
                  ∗ ⌜rd_stage_p ps0 cs0
                       (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝)).
  Proof using .
    intros Hread. iIntros "#Hpin Hdl Hcl". rewrite !pecl_gen.
    iDestruct "Hcl" as "[Hc | Hc]".
    - iMod (gcl_step_read pipe_lm pipe_cparams pipe_lm_byte_laws tt pipe_wa
              with "Hpin Hdl Hc") as "[Hc Hr]"; [exact Hread |].
      iModIntro. iSplitL "Hc"; [by iLeft |].
      iDestruct "Hr" as "[Hr | (Hdl & %Hlen & %Hpref & %Hidx & %HEd & %_ & Hilb & %Hdi & Hr)]";
        [by iLeft |].
      iRight. iSplitL "Hdl"; [done |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitR; [iPureIntro; by rewrite /E_disc_p disc_input_p_lm |].
      iSplitL "Hilb"; [done |].
      iSplitR; [iPureIntro; by rewrite disc_input_p_lm |].
      iDestruct "Hr" as "[%Hws | (%cs0 & %ps0 & %s0 & Hcs & Hps & _ & %Hnl & Htl & %Hrd)]";
        [by iLeft |].
      iRight. iExists cs0, ps0. iFrame "Hcs Hps".
      iSplitR; [by iPureIntro |].
      rewrite (proc_before_p_lm_s _ _ s0). iFrame "Htl".
      iPureIntro. by apply (rd_stage_p_lm _ _ s0).
    - iMod (popen_step_read with "Hpin Hdl Hc") as "[Hc Hr]"; [exact Hread |].
      iModIntro. iFrame "Hr". by iRight.
  Qed.

  (* ---- THE ECHO'S STEP ---- *)

    (* AN ECHO CANNOT HAPPEN WHILE A ROUND'S BLOCK IS OPEN, and the reason
       is the DISCIPLINE's, not the stage's: [disc_pt] wants the round's
       whole block -- its PROMPT included -- on the wire before the next
       input byte, and an open round's bytes are `$`-free. *)
  Lemma pcl_pure_o_no_echo (h : list mobs) (c : bv 8) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (so : postage) (r : nat) (pre : list (bv 8)) :
    disc_p h ->
    trace_shape h true ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    pcl_pure_o (obs_boots h) ho so r pre CH -> False.
  Proof using .
    intros Hdisc Hsh Hends Hwire Hord HK1 Harm Hopen.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & _).
      destruct Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk).
      destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & Halle).
      pose proof Hop as (Hreq & Hwp' & Hne' & ao & Hb2 & Hoarm).
      pose proof Hb2 as (Hnn & Hrr & Hqq & Hokaa & Hpanaa & Hprefaa).
      pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposn.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log CH)) = o_E so).
      { rewrite HEtie /ch_E Harm ch_arm_E_open app_nil_r. reflexivity. }
      pose proof (disc_seg_p'_open_seg h Hsh Hdisc) as Hd'.
      pose proof (proj1 Hd') as Hdseg.
      pose proof (open_seg_ends_in h c Hends) as Hends'.
      destruct (disc_seg_p'_pt_last (open_seg h) c Hd' Hends')
        as (ps' & cs' & Hok' & Hcs'b & Hnm' & Hlow').
      assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)).
      { rewrite -Hseg.
        apply Forall_lookup_2. intros j x Hx.
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
      assert (Hpl : forall j x, o_E so !! j = Some x ->
                      x.1 `prefix_of` open_seg h)
        by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hprefixes Hx)).
      assert (Hoi : length (o_E so) = length (echoed (LogEntryDefs.ch_log CH)))
        by (by rewrite -Hseg seg_of_length).
      assert (Hcnt : length (o_E so) = (length (ins (open_seg h)) - 1)%nat)
        by (rewrite Hoi (echoed_all_len _ Halle); lia).
      assert (Hbytes : (snd <$> o_E so)
                       = take (length (o_E so)) (ins (open_seg h)))
        by (apply (E_bytes_of_hist (o_E so) (open_seg h) Hidx Hpl); lia).
      assert (Hnew' : forall x, x ∈ o_E so -> hist_ext x.1 (open_seg h)).
      { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
        destruct (Hidx jj x Hj) as [Hxe Hxlen].
        pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
        apply lookup_lt_Some in Hj.
        split; [exact Hpx |].
        destruct Hpx as [z Hz]. destruct z as [| aa z'].
        - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
        - rewrite Hz length_app /=. lia. }
      assert (Hup : obs_wire Uart0 (open_seg h)
                    `prefix_of` (D_p (o_ps so) (o_cs so) (o_E so) ++ o_w so))
        by (rewrite -Hacc; exact Hwire).
      assert (Hdi1 : disc_input_p (done_of (removelast (ins (open_seg h))))).
      { apply (disc_input_p_prefix _ (ins (open_seg h)));
          [etrans; [apply done_of_prefix | apply pop_removelast_prefix]
          | exact Hdseg]. }
      (* the claim's own resolution, PADDED to a full one -- which is what
         [PipeDisc.sessp_prefix_det] is stated at, and F2 is run THERE and
         carried back ([FileOut.fecl_step_echo]'s route) *)
      (* the claim's resolution PADDED WITH THE ROUND'S OWN CODE: that is
         the resolution the block in progress is a prefix of. *)
      set (csA := (o_cs so ++ [ao])%list).
      assert (HlenA : length csA = nlines (snd <$> o_E so))
        by (rewrite /csA length_app Hqq; cbn [length]; lia).
      assert (HaoA : alts_pre_p (snd <$> o_E so) csA).
      { apply (alts_pre_p_snoc (snd <$> o_E so) (o_cs so) ao Hcsb');
          [rewrite Hqq; lia |].
        rewrite Hqq. exact Hokaa. }
      assert (HpinA : pro_pin_p (o_ps so) csA (snd <$> o_E so)).
      { intros qq Hqq2. rewrite /csA pro_idx_p_app_le; [by apply Hpin |].
        rewrite (pop_nstarted_rest_nil _ Hrr) in Hqq2. rewrite Hqq. lia. }
      assert (HpendA : pending_p (o_ps so) csA (o_E so)
                       = pcont (pline_of (bodies_of (snd <$> o_E so)
                                  !!! (nlines (snd <$> o_E so) - 1)%nat))
                           (palt_of ao)).
      { rewrite /pending_p /csA.
        exact (pending_at_p_filed_gen (o_ps so) (o_cs so) (snd <$> o_E so)
                 ao Hnn Hrr Hqq Hpanaa). }
      assert (HwpreA : o_w so `prefix_of` pending_p (o_ps so) csA (o_E so)).
      { rewrite HpendA Hwp'. exact Hprefaa. }
      assert (HrlA : (nlines (removelast (snd <$> o_E so))
                      <= length csA)%nat).
      { rewrite (pop_nlines_removelast _ Hrr) HlenA. lia. }
      assert (HlastA : (nlines (snd <$> o_E so) <= length csA)%nat
                       \/ o_w so = []) by (left; lia).
      destruct (stage_sessp_pad (o_ps so) csA (o_E so) (o_w so)
                  HaoA HrlA HlastA Hbyte HpinA HwpreA)
        as (HokP & HpinP & HDP & HwP & HstP).
      assert (HDA : D_p (o_ps so) csA (o_E so)
                    = D_p (o_ps so) (o_cs so) (o_E so)).
      { symmetry.
        apply (D_p_cs_prefix (o_ps so) (o_ps so) (o_cs so) csA (o_E so));
          [reflexivity | rewrite /csA; by eexists | exact Hpin |].
        rewrite (pop_nlines_removelast _ Hrr) Hqq. lia. }
      assert (Hbelow : sessp ps' cs' (done_of (removelast (ins (open_seg h))))
                       `prefix_of`
                       sessp (o_ps so) (alts_pad_p (snd <$> o_E so) csA)
                         (snd <$> o_E so)).
      { etrans; [exact Hlow' |]. etrans; [exact Hup |].
        rewrite -HDA. exact HstP. }
      (* THE CLAIM'S OWN SIDE OF D4: its FILED rounds are never terminal
         ([cs_nofork]), its OPEN one may be -- and then it is the last
         line of the era's input with nothing typed after it, which is
         what D4's unprimed reading asks for. *)
      assert (HpadA : alts_pad_p (snd <$> o_E so) csA = csA)
        by (apply alts_pad_p_full; exact HlenA).
      assert (Hd4c : forall i,
                 (i < nlines (done_of (removelast (ins (open_seg h)))))%nat ->
                 palt_isforkS (palt_at (alts_pad_p (snd <$> o_E so) csA) i)
                   = true ->
                 (S i = nlines (snd <$> o_E so)
                  /\ rest_of (snd <$> o_E so) = [])).
      { intros i _ Hfki. rewrite HpadA in Hfki.
        destruct (decide (i < length (o_cs so))%nat) as [Hi | Hi].
        - exfalso.
          rewrite /csA /palt_at
            (pop_lta_prefix (o_cs so) (o_cs so ++ [ao]) i
               ltac:(by eexists) Hi) in Hfki.
          destruct (lookup_lt_is_Some_2 (o_cs so) i Hi) as [ci Hci].
          rewrite (list_lookup_total_correct (o_cs so) i ci Hci) in Hfki.
          by rewrite (Forall_lookup_1 _ _ _ _ Hnofk Hci) in Hfki.
        - destruct (decide (i = length (o_cs so))) as [-> | Hne2]; last first.
          { exfalso. rewrite /csA (palt_at_ge (o_cs so ++ [ao]) i) in Hfki;
              [discriminate | rewrite length_app; cbn [length]; lia]. }
          split; [rewrite Hqq; lia | exact Hrr]. }
      destruct (sessp_prefix_det2 (o_ps so) ps'
                  (alts_pad_p (snd <$> o_E so) csA) cs'
                  (done_of (removelast (ins (open_seg h)))) (snd <$> o_E so)
                  Hpsb Hok' HokP Hcs'b HpinP Hbyte Hdi1 Hd4c Hnm' Hbelow)
        as (_ & HokPres & HeqP & HcntP).
      assert (Hlow : sessp (o_ps so) (alts_pad_p (snd <$> o_E so) csA)
                       (done_of (removelast (ins (open_seg h))))
                     `prefix_of` obs_wire Uart0 (open_seg h)).
      { rewrite -HeqP. exact Hlow'. }
      assert (HupP : obs_wire Uart0 (open_seg h)
                     `prefix_of`
                     (D_p (o_ps so) (alts_pad_p (snd <$> o_E so) csA)
                        (o_E so) ++ o_w so))
        by (rewrite -HDP HDA; exact Hup).
      pose proof (next_input_of_complete_p (o_ps so)
                  (alts_pad_p (snd <$> o_E so) csA) (o_E so) (o_w so)
                  (obs_wire Uart0 (open_seg h)) (open_seg h) c
                  (length (ins (open_seg h)))
                  Hbyte Hidx Hnew' Hends' eq_refl ltac:(lia) HwP
                  ltac:(rewrite -pop_removelast_take; exact Hlow) HupP)
        as HweqP.
      (* ...so the block would have to be COMPLETE.  THE TWO ARMS OF
         [pblk_open] part here, and this is design section 4.3h's
         "the next input is refuted by D4, not by `$`-freeness". *)
      exfalso.
      assert (Hweq2 : o_w so
                      = pcont (pline_of (bodies_of (snd <$> o_E so)
                                 !!! (nlines (snd <$> o_E so) - 1)%nat))
                          (palt_of ao)).
      { rewrite -HpendA HweqP /pending_p. symmetry.
        apply (pending_at_p_cs_ext (o_ps so) csA
                 (alts_pad_p (snd <$> o_E so) csA) (snd <$> o_E so));
          [apply alts_pad_p_prefix | lia]. }
      destruct Hoarm as [[Hfkao Hnd'] | Hfkao].
      { (* NON-TERMINAL: a complete block carries the prompt, and an open
           round's bytes are `$`-free. *)
        apply (pcont_ne_nodollar
                 (pline_of (bodies_of (snd <$> o_E so)
                    !!! (nlines (snd <$> o_E so) - 1)%nat)) (palt_of ao)
                 (o_w so) Hokaa Hpanaa Hfkao
                 ltac:(rewrite Hwp'; exact Hnd')).
        exact Hweq2. }
      (* TERMINAL: the block MAY carry the prompt, so `$`-freeness says
         nothing about it -- and D4 says it instead.  The input before
         [c] is EXACTLY the era's (D2 above), so the discipline's own
         resolution read the terminal round's bytes too; those bytes are
         a SHUFFLE, and D4 forbids a shuffle at any round but the input's
         last -- which this one is not, because [c] was typed. *)
      set (i0 := (nlines (snd <$> o_E so) - 1)%nat).
      assert (HI1 : removelast (ins (open_seg h)) = (snd <$> o_E so)).
      { rewrite pop_removelast_take Hbytes Hcnt. reflexivity. }
      assert (Hi0 : (i0 < nlines (done_of (removelast (ins (open_seg h)))))%nat)
        by (rewrite nlines_done HI1 /i0; lia).
      (* the terminal round is at a PIPELINE line -- D4's guard *)
      assert (Hpipe0 : pline_is_pipe
                         (pline_of (bodies_of (done_of (removelast
                                                (ins (open_seg h)))) !!! i0))
                       = true).
      { rewrite bodies_of_done HI1.
        exact (palt_ok_isforkS_pipe _ (palt_of ao) Hokaa Hfkao). }
      apply (Hnm' i0 Hi0 Hpipe0).
      apply (pmergeable_prefix _
               (alt_cont_p ps' cs'
                  (bodies_of (done_of (removelast (ins (open_seg h))))) i0)).
      { rewrite /alt_cont_p. apply prefix_app_r. reflexivity. }
      rewrite (HcntP i0 Hi0) HpadA /alt_cont_p.
      rewrite (_ : palt_at csA i0 = palt_of ao);
        [| rewrite /csA; apply palt_at_snoc; rewrite Hqq; reflexivity].
      rewrite Hpanaa app_nil_r.
      exact (pmergeable_isforkS _ (palt_of ao) Hokaa Hfkao).
  Qed.

  Lemma pecl_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    disc_p h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (* (K1) + (A1) at this arm, recorded at the open: the log is complete
       below the input being echoed *)
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    pecl k ho CH ==∗
      pecl k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using .
    intros Hdisc Hsh Hk Hends Hwire Hord HK1 Harm. rewrite !pecl_gen.
    iIntros "[Hc | Hp]".
    - apply disc_p_lm in Hdisc.
      iMod (gcl_step_echo pipe_lm pipe_cparams pipe_lm_byte_laws tt pipe_wa
              with "Hc") as "Hc"; try done.
      iModIntro. by iLeft.
    - iDestruct "Hp" as (v w so r gb pre tm) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hopen)".
      subst k. by destruct (pcl_pure_o_no_echo h c ho CH so r pre
                              Hdisc Hsh Hends Hwire Hord HK1 Harm Hopen).
  Qed.

  Lemma pecl_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    pecl k ho CH ==∗ pecl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using .
    intros Hok Hev. iIntros "Hcl".
    iDestruct (pecl_arm with "Hcl") as "[Hcl [#HT | %Hera]]".
    { iModIntro. by iApply pecl_taint. }
    pose proof Hev as Hev0.
    destruct Hev0 as (a & Ha & Hlk). destruct a as [[[ha ca] csa] ja].
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Hlk.
    rewrite /ch_arm_era_p Ha in Hera.
    destruct Hera as (Hdseg & Hbts & Hdisc & Hsh & Hw & _ & HK1).
    subst ha.
    destruct Hok as [_ Harm]. rewrite Ha in Harm.
    cbn [from_option LogEntryDefs.ca_hist LogEntryDefs.ca_byte
         LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Harm.
    destruct Harm as (Hends & Hecho & _ & Hord & Hwire).
    assert (Hshape : csa = [echo_of ca] /\ ja = 0%nat /\ b = echo_of ca).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]].
      - exfalso. rewrite Hnil in Hlk. by rewrite lookup_nil in Hlk.
      - rewrite Hech in Hlk.
        destruct ja as [| j']; cbn in Hlk; [| by rewrite lookup_nil in Hlk].
        injection Hlk as <-. by split_and!.
      - exfalso.
        pose proof (disc_seg_p_no_erase (open_seg ho) ca Hdseg
                      (open_seg_ends_in ho ca Hends)) as Hno.
        rewrite Hno in Herase. discriminate. }
    destruct Hshape as (Hcsa & Hja & Hb).
    subst b. rewrite Hcsa Hja in Ha.
    iApply (pecl_step_echo k ho ca ho CH Hdisc Hsh Hbts Hends Hwire Hord HK1 Ha
              with "Hcl").
  Qed.

  (* ---- THE DRAIN ---- *)
  Lemma popen_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    popen k ho CH -∗ popen k ho CH ∗ ⌜good_out_p seg⌝.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire. subst k.
    iIntros "Hp".
    - iDestruct "Hp" as (v w so r gb pre tm) "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hpo)".
      pose proof (proj1 Hpo)
        as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcs' & Hdsc
            & Hpre1 & Hpre2 & Hpre3 & Hnofk).
      iSplitL "Hta Hcs Hps HE Hdl Hdll Hblk Hcur Hrb".
      { iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
        by iPureIntro. }
      iPureIntro.
      assert (Hbytes : (snd <$> o_E so) `prefix_of` ins seg).
      { destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil fmap_nil. apply prefix_nil.
        - assert (Hpl : forall j x, o_E so !! j = Some x ->
                          x.1 `prefix_of` open_seg ho)
            by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
          rewrite (E_bytes_of_hist (o_E so) (open_seg ho) Hidx Hpl Hpre2).
          etrans; [apply prefix_take |].
          rewrite Hins. apply ins_prefix_of, open_seg_prefix_boots;
            [exact Hpre | by rewrite Hbo | exact Hsh]. }
      assert (Hao : alts_pre_p (ins seg) (o_cs so))
        by exact (alts_pre_p_mono (snd <$> o_E so) (ins seg) (o_cs so)
                    Hbytes Hcs').
      assert (Hwire' : obs_wire Uart0 seg
                       `prefix_of` (D_p (o_ps so) (o_cs so) (o_E so)
                                    ++ o_w so)) by (rewrite -Hacc; exact Hwire).
      pose proof Hpo as Ho.
      (* THE ROUND IN PROGRESS: F4 at an UNFILED block, whose witness is
         the round's own code ([PipeBothPure.good_out_p_of_stage_blk2]). *)
      destruct Ho as (_ & Hop & _).
      pose proof Hop as (_ & Hwp' & _ & ao & Hb2 & _).
      apply (good_out_p_of_stage_blk2 (o_ps so) (o_cs so) (o_E so) (o_w so)
               ao seg Hpsb Hao Hbyte Hpin);
        [by rewrite Hwp' | exact Hwire' | exact Hbytes].
  Qed.

  Lemma pecl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    pecl k ho CH -∗ pecl k ho CH ∗ (T ∨ ⌜good_out_p seg⌝).
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. rewrite !pecl_gen. iIntros "[Hc | Hc]".
    - iDestruct (gcl_drain pipe_lm pipe_cparams pipe_lm_byte_laws tt pipe_wa
                   k h ho CH seg Hsh Hk Hpre Hins Hwire Hne with "Hc") as "[Hc Hd]".
      iSplitL "Hc"; [by iLeft |].
      iDestruct "Hd" as "[#HT | (%s0 & %Hgo & _)]"; [by iLeft |].
      iRight. iPureIntro. apply good_out_p_lm. by rewrite -(pipe_st_tt s0).
    - iDestruct (popen_drain with "Hc") as "[Hc %Hgo]"; try done.
      iSplitL "Hc"; [by iRight |]. by iRight.
  Qed.

  (* ====================================================================== *)
  (*  5.  THE LEDGER                                                        *)
  (*                                                                        *)
  (*  [EchoOut.echo_led] at the PIPELINE discipline and conclusion.  The    *)
  (*  counter sits at [decide (disc_p h)] -- PIPE-DEC's instance -- and     *)
  (*  every step rewrites with [decide_ext] at a closure law, so no         *)
  (*  [Decision] is ever evaluated.                                         *)
  (* ====================================================================== *)

  Definition pipe_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1
       (if decide (disc_p h) then 0%nat else 1%nat)
     ∗ pin_map γ h
     ∗ pera_map g h
     ∗ (⌜Forall good_out_p (cycles_of h)⌝ ∨ T))%I.

  Global Instance pipe_led_timeless h : Timeless (pipe_led h).
  Proof using . rewrite /pipe_led. apply _. Qed.

  (* WHAT THE BIRTH STEP YIELDS: [AppEcho.echo_cl] unchanged, because the
     fixed part is the echo application's. *)
  Definition pipe_cl_all : iProp Σ :=
    (echo_cl γ ∗ ghost_map_auth (pgn_era g) 1 (∅ : gmap nat pipe_era))%I.

  Lemma pipe_led_init : pipe_cl_all -∗ pipe_led [].
  Proof using .
    rewrite /pipe_cl_all /echo_cl /pipe_led /pin_map /pera_map.
    rewrite decide_True; [| exact disc_p_nil].
    iIntros "[[Ht Hm] Hme]". iFrame "Ht".
    iSplitL "Hm".
    { iExists ∅. iFrame "Hm". iPureIntro. apply pin_dom_empty. }
    iSplitL "Hme".
    { iExists ∅. iFrame "Hme". iPureIntro. apply pin_dom_empty. }
    iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
  Qed.

  (* THE FOUNDING, as a resource split: the era's ghosts become the port's
     claim at the start of their era and init's console credential. *)
  Lemma era_full_split_p (k : nat) (v : era_pins) (w : pipe_era)
      (gb : gname) :
    era_pin γ k v -∗ pera_pin g k w -∗ blk_auth w [] -∗
    rblk_auth gb [] -∗ cur_half w 1 0%nat gb false -∗ era_full v -∗
      pecl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ pturn k.
  Proof using .
    iIntros "#Hpin #Hpera Hblk Hrb Hcur1 (Ht & Hcs & Hps & HE & Hdl & Hdll)".
    iAssert (turn_lb v 0%nat) as "#Htlb0".
    { rewrite /turn_lb. iApply (mono_nat_lb_own_get with "Ht"). }
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iDestruct (dl_list_lb_get with "Hdll") as "[Hdll #Hdllb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hdll Hblk Hcur1 Hrb".
    { rewrite pecl_view. iRight. iLeft. iExists v, w, ostage0, 0%nat, gb, [], false.
      rewrite pstream_0.
      cbn [o_ps o_cs o_E o_w ostage0 length LogEntryDefs.ch_dl].
      rewrite /pcount_p fmap_nil proc_before_p_nil. cbn [length].
      iFrame "Hpin Hpera Hblk Hcur1 Hrb Ht1 Hcs Hps HE Hdl1 Hdll". iPureIntro.
      rewrite /pcl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (pout_pure_0 k []).
      - exact cs_len_ok_0.
      - exact ps_len_ok_p_0.
      - exact (pein_pure_0 k).
      - by rewrite /ch_arm_era_p.
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of. by rewrite fmap_nil.
      - exact dl_ok_0. }
    rewrite /pturn /eturn. iExists v. iFrame "Hpin Ht2 Hdl2 Hcslb Hpslb".
    iApply (inp_lb_of_dl_lb v [] []); [apply prefix_nil | iExact "Hdllb"].
  Qed.

  Lemma pipe_led_pow (h : list mobs) (on : bool) :
    pipe_led h ==∗
      pipe_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else pecl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ pturn (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hme & Hphi)". rewrite /pipe_led.
    rewrite (decide_ext _ (disc_p h) 0%nat 1%nat (disc_p_power h on)).
    destruct on.
    - iDestruct (pin_map_step γ h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iDestruct (pera_map_step g h ObsPowerOff eq_refl with "Hme") as "Hme".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hme".
      rewrite cycles_of_off. iExact "Hphi".
    - iMod era_full_alloc as (v) "Hfull".
      iMod (pin_map_on γ h v with "Hpm") as "[Hpm #Hpin]".
      (* the era's BYTE LEDGER is born with the era's other ghosts *)
      iMod blk_alloc as (w gb) "(Hblk & Hrb & Hcur1)".
      iMod (pera_map_on g h w with "Hme") as "[Hme #Hpera]".
      iDestruct (era_full_split_p (S (obs_boots h)) v w gb
                   with "Hpin Hpera Hblk Hrb Hcur1 Hfull") as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn".
      + iFrame "Ht Hpm Hme".
        rewrite cycles_of_on.
        iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
        iLeft. iPureIntro. apply Forall_app. split; [exact Hg |].
        apply Forall_singleton. exact good_out_p_nil.
      + iFrame "Hcl Hturn".
  Qed.

  Lemma pipe_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜i = Uart0 -> good_out_p (open_seg h ++ [ObsUartOut i b])⌝) -∗
    pipe_led h ==∗ pipe_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Hcnt & Hpm & Hme & Hphi)".
    iDestruct (pin_map_step γ h (ObsUartOut i b) eq_refl with "Hpm") as "Hpm".
    iDestruct (pera_map_step g h (ObsUartOut i b) eq_refl with "Hme") as "Hme".
    rewrite /pipe_led.
    rewrite (decide_ext _ (disc_p h) 0%nat 1%nat (disc_p_out h i b Hsh)).
    iModIntro. iFrame "Hcnt Hpm Hme".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. destruct i.
    - exact (phi_step_cons_p h (ObsUartOut Uart0 b) Hsh eq_refl
               (Hgo eq_refl) Hg).
    - exact (phi_step_io_p h (ObsUartOut Uart1 b) Hsh eq_refl
               (obs_wire_out_other Uart1 b ltac:(discriminate)) Hg).
  Qed.

  Lemma pipe_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    pipe_led h ==∗
      pipe_led (h ++ [ObsUartIn i b])
      ∗ (⌜disc_p (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hme & Hphi)".
    iDestruct (pin_map_step γ h (ObsUartIn i b) eq_refl with "Hpm") as "Hpm".
    iDestruct (pera_map_step g h (ObsUartIn i b) eq_refl with "Hme") as "Hme".
    iAssert (⌜Forall good_out_p (cycles_of (h ++ [ObsUartIn i b]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro.
      apply (phi_step_io_p h (ObsUartIn i b) Hsh eq_refl (obs_wire_in i b) Hg). }
    rewrite /pipe_led.
    destruct (decide (disc_p (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_p_in h b Hsh Hd')
          | exact (proj1 (disc_p_other h (ObsUartIn Uart1 b) eq_refl I Hsh)
                     Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hme Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc_p h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hme Hphi". iRight. iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run.  [T] IS the counter's lower bound at
     1, so the lemma's premise is the identity -- as at the echo
     application. *)
  Lemma pipe_led_phi (h : list mobs) :
    pipe_led h -∗ ⌜disc_p h -> Forall good_out_p (cycles_of h)⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & [%Hg | HT'])".
    { iPureIntro. by intros _. }
    rewrite /echo_taint.
    iDestruct (mono_nat_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.

End pipe_out.

(* ====================================================================== *)
(*  6.  THE BIRTH STEP                                                     *)
(*                                                                        *)
(*  The fixed part is the echo application's, so the birth step IS         *)
(*  [AppEcho.echo_birth].                                                  *)
(* ====================================================================== *)
Section pipe_birth.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.

  (* THE BIRTH: echo's fixed part, and the byte ledger's map beside it --
     [FileOut.file_birth_all]'s shape one application over. *)
  Lemma pipe_birth_all : ⊢ |==> ∃ g : pipe_gn, pipe_cl_all g.
  Proof using .
    iMod echo_birth as (γ) "Hcl".
    iMod (ghost_map_alloc_empty (K := nat) (V := pipe_era)) as (gm) "Hm".
    iModIntro. iExists (MkPipeGn γ gm). rewrite /pipe_cl_all. cbn [pgn_cl pgn_era].
    iFrame "Hcl Hm".
  Qed.
End pipe_birth.

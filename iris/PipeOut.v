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
   [PipeDisc.disc_p_dec] (lane PIPE-DEC).  Per that lane's warning, no
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
Require Import PipeDisc.      (* [disc_p_dec]: the ledger's counter *)
Require Import PipeOutPure.
Require Import PipeOutPure.
Require Import EchoOut.           (* the ghost algebra, [ch_E] and its laws *)
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.     (* the stream equations at [pipe_lm] *)
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.            (* the claim once *)
Require Import PipeOutPure.         (* [pipe_hooks] *)
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

  (* THE PIPELINE'S CLAIM: the generic one between rounds, [popen] while
     a two-writer round is open (owner ruling 2026-09-23) *)
  Definition pecl (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (gcl pipe_lm pipe_cparams tt pipe_wa k ho H ∨ popen k ho H)%I.

  Global Instance pecl_timeless k ho H : Timeless (pecl k ho H).
  Proof using . rewrite /pecl. apply _. Qed.

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

End pipe_out.

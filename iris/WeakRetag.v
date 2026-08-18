(** * WeakRetag.v — the CLASS-RETAG simulation (premise-ledger stage A1)

    [WeakMem]'s [wm_ak] (the message class, D-M6-6) is an INERT syntactic
    tag: it exists so that Layer 2's classification is a function of the
    machine state rather than a ghost existential.  This file PROVES that
    inertness, and turns it into the elimination the capstone's premise
    ledger wants ([claude-notes/projects/weak-memory-premises.md], stage
    A1): the [Hcls] premise of [WeakComposeLang.xv6_cone_premises] is not
    an assumption about the machine, it is a property every behavior can
    be BROUGHT INTO by relabelling its log.

    THE KEY FACT, verified rule by rule below.  No rule of
    [WeakPromise.wpstep] ever READS a message's [wm_ak]:

      - [WPPromise] APPENDS a class — it is the rule's own free binder [k],
        so any class may be appended;
      - [WPFulfil]/[WPRmw] require the log entry at the fulfilled position
        to BE [WMsg base data (Some i) k] for SOME [k] — [k] is a rule
        binder there too, never constrained;
      - [read_ok], [excl_ok], [fulfil_ok], [store_post_run],
        [load_post_run], [fence_post] never mention [wm_ak] (they see the
        log only through [msg_byte]/[log_byte]/[writes_in]/[writes_in_by],
        all of which project [wm_pa]/[wm_data]/[wm_tid] only);
      - labels ([wlabel]) carry no class at all, so neither do trace events
        ([WeakRobustTrace.aev] = label + fulfilled timestamp) nor agent
        records ([WeakPromise.wpagent] = program state + [wstate] + promise
        set).

    Hence changing EVERY message's class, uniformly and pointwise by
    position, commutes with every step — [wpstep_retag] — and therefore
    with whole behaviors, traces and the observables [prog_of]/[mem_of].

    A RETAG IS A FUNCTION ON LOG POSITIONS, [nat → wm_class], applied with
    [imap].  Position (not message identity) is the right index: two log
    entries can be identical messages, and the canonical class of each is
    computed at ITS OWN fulfil event.

    FINDING (recorded rather than proved): the CONVERSE simulation
    [wpstep (retag_cfg f c) (retag_cfg f c') → wpstep c c'] is FALSE, and
    not merely hard.  [retag_cfg f] is not injective — two configurations
    differing only in a logged message's class have the same retag — so
    take [c'] to be [c] with one class changed and a silent step of [c]
    that maps an agent to itself; then [wpstep (retag_cfg f c)
    (retag_cfg f c')] holds while [wpstep c c'] cannot (every non-promise
    rule keeps the log literally fixed).  Nothing downstream needs the
    converse: the capstone consumes retagging in the forward direction
    only (a behavior yields a canonical behavior with the same
    conclusion).

    DEPENDENCY-LIGHT by design: stdpp, [WeakMem], [WeakPromise],
    [WeakPromiseFact], [WeakRobust] (for [prog_of]/[mem_of]),
    [WeakRobustTrace].  In particular [WeakSailLTS2.lbl_class] is NOT
    imported — canonicity is stated against a PARAMETER
    [clsf : P → wlabel → wstate → wm_class], which the consumer
    instantiates at [lbl_class_p]; that keeps this file free of Sail and of
    the whole
    model tower. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact
                            WeakRobust WeakRobustTrace.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. The pointwise retag, and the log predicates it fixes *)

(** Re-tag ONE message, at its log position [p]. *)
Definition retag_msg (f : nat → wm_class) (p : nat) (m : wmsg) : wmsg :=
  WMsg (wm_pa m) (wm_data m) (wm_tid m) (f p).

(** Re-tag a whole log, pointwise by position. *)
Definition retag_log (f : nat → wm_class) (log : list wmsg) : list wmsg :=
  imap (retag_msg f) log.

(* ---------------------------------------------------------------- *)
(** ** The three surviving projections, and the one that changes *)

Lemma retag_msg_pa f p m : wm_pa (retag_msg f p m) = wm_pa m.
Proof. done. Qed.

Lemma retag_msg_data f p m : wm_data (retag_msg f p m) = wm_data m.
Proof. done. Qed.

Lemma retag_msg_tid f p m : wm_tid (retag_msg f p m) = wm_tid m.
Proof. done. Qed.

Lemma retag_msg_ak f p m : wm_ak (retag_msg f p m) = f p.
Proof. done. Qed.

(** The one shape that matters to [WPFulfil]/[WPRmw]/[astep_ok]: a
    positional literal keeps its base/data/tid and takes the new class. *)
Lemma retag_msg_lit f p base data tid k :
  retag_msg f p (WMsg base data tid k) = WMsg base data tid (f p).
Proof. done. Qed.

Lemma retag_msg_byte f p m a : msg_byte (retag_msg f p m) a = msg_byte m a.
Proof. done. Qed.

Lemma retag_msg_writesb f p m a : msg_writesb (retag_msg f p m) a = msg_writesb m a.
Proof. done. Qed.

(* ---------------------------------------------------------------- *)
(** ** The list-level laws *)

Lemma retag_log_nil f : retag_log f [] = [].
Proof. done. Qed.

Lemma retag_log_length f log : length (retag_log f log) = length log.
Proof. apply length_imap. Qed.

Lemma retag_log_lookup f log p :
  retag_log f log !! p = retag_msg f p <$> log !! p.
Proof. apply list_lookup_imap. Qed.

Lemma retag_log_lookup_Some f log p m :
  log !! p = Some m → retag_log f log !! p = Some (retag_msg f p m).
Proof. intros H. by rewrite retag_log_lookup H. Qed.

Lemma retag_log_lookup_inv f log p m' :
  retag_log f log !! p = Some m' →
  ∃ m, log !! p = Some m ∧ m' = retag_msg f p m.
Proof.
  rewrite retag_log_lookup. intros (m & ? & ->)%fmap_Some. by exists m.
Qed.

(** THE APPEND LAW — what [WPPromise]'s case needs: the new top's class is
    [f] at the OLD length. *)
Lemma retag_log_app f log m :
  retag_log f (log ++ [m]) = retag_log f log ++ [retag_msg f (length log) m].
Proof. rewrite /retag_log imap_app /=. by rewrite Nat.add_0_r. Qed.

(** Retagging is ABSORBING: the last retag wins. *)
Lemma retag_log_retag f g log :
  retag_log f (retag_log g log) = retag_log f log.
Proof.
  apply list_eq. intros p. rewrite !retag_log_lookup.
  by destruct (log !! p).
Qed.

(** ... and the identity retag exists (positionally computed), so a log is
    always in the image of a retag. *)
Definition untag_f (log : list wmsg) (p : nat) : wm_class :=
  match log !! p with Some m => wm_ak m | None => WCplain end.

Lemma retag_log_untag log : retag_log (untag_f log) log = log.
Proof.
  apply list_eq. intros p. rewrite retag_log_lookup.
  destruct (log !! p) as [m|] eqn:Hm; [|done].
  rewrite /= /retag_msg /untag_f Hm /=. by destruct m.
Qed.

(* ---------------------------------------------------------------- *)
(** ** Every log predicate of the machine is retag-invariant *)

Lemma retag_log_byte f img log t a :
  log_byte img (retag_log f log) t a = log_byte img log t a.
Proof.
  destruct t as [|i]; [done|].
  rewrite !log_byte_S retag_log_lookup. by destruct (log !! i).
Qed.

Lemma retag_writes_in f log a lo hi :
  writes_in (retag_log f log) a lo hi ↔ writes_in log a lo hi.
Proof.
  split.
  - intros (t & Hlo & Hhi & m' & Hm' & Hs).
    apply retag_log_lookup_inv in Hm' as (m & Hm & ->).
    exists t. split_and!; [done|done|]. by exists m.
  - intros (t & Hlo & Hhi & m & Hm & Hs).
    exists t. split_and!; [done|done|].
    exists (retag_msg f (t - 1)%nat m). split; [by apply retag_log_lookup_Some|done].
Qed.

Lemma retag_writes_in_1 f log a lo hi :
  writes_in (retag_log f log) a lo hi → writes_in log a lo hi.
Proof. apply retag_writes_in. Qed.

Lemma retag_writes_in_2 f log a lo hi :
  writes_in log a lo hi → writes_in (retag_log f log) a lo hi.
Proof. apply retag_writes_in. Qed.

Lemma retag_writes_in_by f log Q a lo hi :
  writes_in_by (retag_log f log) Q a lo hi ↔ writes_in_by log Q a lo hi.
Proof.
  split.
  - intros (t & Hlo & Hhi & m' & Hm' & Hs & HQ).
    apply retag_log_lookup_inv in Hm' as (m & Hm & ->).
    exists t. split_and!; [done|done|]. by exists m.
  - intros (t & Hlo & Hhi & m & Hm & Hs & HQ).
    exists t. split_and!; [done|done|].
    exists (retag_msg f (t - 1)%nat m). split_and!;
      [by apply retag_log_lookup_Some|done|done].
Qed.

Lemma retag_writes_in_by_1 f log Q a lo hi :
  writes_in_by (retag_log f log) Q a lo hi → writes_in_by log Q a lo hi.
Proof. apply retag_writes_in_by. Qed.

Lemma retag_writes_in_by_2 f log Q a lo hi :
  writes_in_by log Q a lo hi → writes_in_by (retag_log f log) Q a lo hi.
Proof. apply retag_writes_in_by. Qed.

Lemma retag_latest_ts f log a : latest_ts (retag_log f log) a = latest_ts log a.
Proof.
  induction log as [|m l IH] using rev_ind; [done|].
  rewrite retag_log_app !latest_ts_app retag_msg_writesb retag_log_length.
  by destruct (msg_writesb m a).
Qed.

Lemma retag_latest f img log a t :
  latest img (retag_log f log) a t ↔ latest img log a t.
Proof.
  rewrite /latest retag_log_byte retag_log_length.
  split; intros [? Hn]; (split; [done|]); intros Hw; apply Hn.
  - by eapply retag_writes_in_2.
  - by eapply retag_writes_in_1.
Qed.

Lemma retag_readable f img log ws vpre a t :
  readable img (retag_log f log) ws vpre a t ↔ readable img log ws vpre a t.
Proof.
  rewrite /readable retag_log_byte.
  split; intros [? Hn]; (split; [done|]); intros Hw; apply Hn.
  - by eapply retag_writes_in_2.
  - by eapply retag_writes_in_1.
Qed.

Lemma retag_readable_1 f img log ws vpre a t :
  readable img (retag_log f log) ws vpre a t → readable img log ws vpre a t.
Proof. apply retag_readable. Qed.

Lemma retag_readable_2 f img log ws vpre a t :
  readable img log ws vpre a t → readable img (retag_log f log) ws vpre a t.
Proof. apply retag_readable. Qed.

Lemma retag_read_ok_d f img log ws aq lat base tvs va :
  read_ok_d img (retag_log f log) ws aq lat base tvs va ↔
  read_ok_d img log ws aq lat base tvs va.
Proof.
  rewrite /read_ok_d. split.
  - intros Hr j t v Htv. destruct (Hr j t v Htv) as (Hb & Hrd & Hlat).
    rewrite retag_log_byte in Hb. split_and!.
    + done.
    + by eapply retag_readable_1.
    + intros ->. rewrite -(retag_log_length f log). intros Hw.
      apply (Hlat eq_refl). by eapply retag_writes_in_2.
  - intros Hr j t v Htv. destruct (Hr j t v Htv) as (Hb & Hrd & Hlat).
    split_and!.
    + by rewrite retag_log_byte.
    + by eapply retag_readable_2.
    + intros ->. rewrite retag_log_length. intros Hw.
      apply (Hlat eq_refl). by eapply retag_writes_in_1.
Qed.

Lemma retag_read_ok f img log ws aq lat base tvs :
  read_ok img (retag_log f log) ws aq lat base tvs ↔
  read_ok img log ws aq lat base tvs.
Proof. apply retag_read_ok_d. Qed.

Lemma retag_read_ok_1 f img log ws aq lat base tvs va :
  read_ok_d img (retag_log f log) ws aq lat base tvs va →
  read_ok_d img log ws aq lat base tvs va.
Proof. apply retag_read_ok_d. Qed.

Lemma retag_read_ok_2 f img log ws aq lat base tvs va :
  read_ok_d img log ws aq lat base tvs va →
  read_ok_d img (retag_log f log) ws aq lat base tvs va.
Proof. apply retag_read_ok_d. Qed.

Lemma retag_excl_ok f log i base tvs ts :
  excl_ok (retag_log f log) i base tvs ts ↔ excl_ok log i base tvs ts.
Proof.
  rewrite /excl_ok. split; intros He j t v Htv Hw; eapply He; [done| |done|].
  - by eapply retag_writes_in_by_2.
  - by eapply retag_writes_in_by_1.
Qed.

Lemma retag_excl_ok_1 f log i base tvs ts :
  excl_ok (retag_log f log) i base tvs ts → excl_ok log i base tvs ts.
Proof. apply retag_excl_ok. Qed.

Lemma retag_excl_ok_2 f log i base tvs ts :
  excl_ok log i base tvs ts → excl_ok (retag_log f log) i base tvs ts.
Proof. apply retag_excl_ok. Qed.

(** [fulfil_ok] mentions no log at all — recorded so the audit above is
    complete on the page. *)
Lemma retag_fulfil_ok ws rl base n ts :
  fulfil_ok ws rl base n ts → fulfil_ok ws rl base n ts.
Proof. done. Qed.

(* ====================================================================== *)
(** * 2. Configurations and the step simulation *)

(** Agent records carry NO class ([wpagent] = program state + [wstate] +
    promise set), so a retag touches the log and nothing else. *)
Definition retag_cfg {P D : Type} (f : nat → wm_class) (c : wpcfg P D)
    : wpcfg P D :=
  WPCfg (pc_img c) (retag_log f (pc_log c)) (pc_dev c) (pc_ags c).

Lemma retag_cfg_img {P D} f (c : wpcfg P D) : pc_img (retag_cfg f c) = pc_img c.
Proof. done. Qed.

Lemma retag_cfg_log {P D} f (c : wpcfg P D) :
  pc_log (retag_cfg f c) = retag_log f (pc_log c).
Proof. done. Qed.

Lemma retag_cfg_ags {P D} f (c : wpcfg P D) : pc_ags (retag_cfg f c) = pc_ags c.
Proof. done. Qed.

Lemma retag_cfg_log_length {P D} f (c : wpcfg P D) :
  length (pc_log (retag_cfg f c)) = length (pc_log c).
Proof. apply retag_log_length. Qed.

Lemma retag_cfg_retag {P D} f g (c : wpcfg P D) :
  retag_cfg f (retag_cfg g c) = retag_cfg f c.
Proof. rewrite /retag_cfg /= retag_log_retag //. Qed.

Lemma retag_cfg_untag {P D} (c : wpcfg P D) : retag_cfg (untag_f (pc_log c)) c = c.
Proof. rewrite /retag_cfg retag_log_untag. by destruct c. Qed.

Section machine.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.
  Implicit Types f : nat → wm_class.

  (* ---------------------------------------------------------------- *)
  (** ** THE STEP SIMULATION — all ten rules ([WPDev] since M5, the three
         dependency-only arms since D2) *)

  Lemma wpstep_retag f c c' :
    wpstep pstep c c' → wpstep pstep (retag_cfg f c) (retag_cfg f c').
  Proof.
    intros Hstep.
    destruct Hstep as
      [ cfg i ag base data k Hlk Hne
      | cfg i ag st' d' Hlk Hps
      | cfg i ag aq lat base tvs asrc st' d' Hlk Hps Hr
      | cfg i ag rl base data asrc vsrc k ts st' d' Hlk Hps Hin Hm Hok
      | cfg i ag aq rl base tvs data asrc vsrc k ts st' d'
            Hlk Hps Hlen Hin Hm Hr He Hok
      | cfg i ag pr pw sr sw st' d' Hlk Hps |cfg i ag st' d' Hlk Hps
      | cfg i ag rd srcs st' d' Hlk Hps | cfg i ag srcs st' d' Hlk Hps
      | cfg i ag st' d' Hlk Hps].
    - (* WPPromise: the appended class is the rule's free binder — take
         [f] at the OLD log length *)
      pose proof (WPPromise (P:=P) (D:=D) pstep
                    (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
                    i ag base data (f (length (pc_log cfg))) Hlk Hne) as Hs.
      simpl in Hs. rewrite retag_log_length in Hs.
      rewrite {2}/retag_cfg /= retag_log_app retag_msg_lit. exact Hs.
    - (* WPSilent *)
      exact (WPSilent (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag st' d' Hlk Hps).
    - (* WPLoad *)
      apply (WPLoad (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag aq lat base tvs asrc st' d' Hlk Hps).
      simpl. by apply retag_read_ok_2.
    - (* WPFulfil: the matched entry's class is the rule's free binder *)
      apply (WPFulfil (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag rl base data asrc vsrc (f (ts - 1)%nat) ts st' d'
               Hlk Hps Hin);
        [|exact Hok].
      simpl. by rewrite retag_log_lookup Hm.
    - (* WPRmw *)
      apply (WPRmw (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag aq rl base tvs data asrc vsrc (f (ts - 1)%nat) ts st' d'
               Hlk Hps Hlen Hin); [| | |exact Hok].
      + simpl. by rewrite retag_log_lookup Hm.
      + simpl. by apply retag_read_ok_2.
      + simpl. by apply retag_excl_ok_2.
    - (* WPFence *)
      exact (WPFence (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag pr pw sr sw st' d' Hlk Hps).
    - (* WPDev: [WPSilent]'s twin *)
      exact (WPDev (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag st' d' Hlk Hps).
    - (* WPRegW / WPCtrl / WPInstr: the three dependency-only arms move no
         message, so the retag is [WPSilent]'s argument verbatim. *)
      exact (WPRegW (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag rd srcs st' d' Hlk Hps).
    - exact (WPCtrl (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag srcs st' d' Hlk Hps).
    - exact (WPInstr (P:=P) (D:=D) pstep
               (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
               i ag st' d' Hlk Hps).
  Qed.

  Lemma wpsteps_retag f c c' :
    rtc (wpstep pstep) c c' →
    rtc (wpstep pstep) (retag_cfg f c) (retag_cfg f c').
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    eapply rtc_l; [by apply wpstep_retag|done].
  Qed.

  (** The promise phase alone — the shape the traced factorization
      exports (and the capstone's plumbing consumes). *)
  Lemma wp_promise_step_retag f c c' :
    wp_promise_step c c' →
    wp_promise_step (retag_cfg f c) (retag_cfg f c').
  Proof.
    intros Hstep. destruct Hstep as [cfg i ag base data k Hlk Hne].
    pose proof (WPPromStep (P:=P)
                  (WPCfg (pc_img cfg) (retag_log f (pc_log cfg)) (pc_dev cfg) (pc_ags cfg))
                  i ag base data (f (length (pc_log cfg))) Hlk Hne) as Hs.
    simpl in Hs. rewrite retag_log_length in Hs.
    rewrite {2}/retag_cfg /= retag_log_app retag_msg_lit. exact Hs.
  Qed.

  Lemma wp_promise_steps_retag f c c' :
    rtc (wp_promise_step (P:=P)) c c' →
    rtc (wp_promise_step (P:=P)) (retag_cfg f c) (retag_cfg f c').
  Proof.
    induction 1 as [|x y z Hs _ IH]; [done|].
    eapply rtc_l; [by apply wp_promise_step_retag|done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Initial configurations, promise-freedom, behaviors *)

  Lemma retag_wp_init f img d0 ps :
    retag_cfg f (wp_init (P:=P) (D:=D) img d0 ps) = wp_init img d0 ps.
  Proof. done. Qed.

  Lemma no_promises_retag f c : no_promises c ↔ no_promises (retag_cfg f c).
  Proof. done. Qed.

  Theorem wp_behavior_retag f img d0 ps c :
    wp_behavior pstep img d0 ps c →
    wp_behavior pstep img d0 ps (retag_cfg f c).
  Proof.
    intros [Hrun Hnp]. split; [|by apply no_promises_retag].
    rewrite -(retag_wp_init f img d0 ps). by apply wpsteps_retag.
  Qed.

  (** Well-formedness survives too (nothing in [cfg_wf] reads a class);
      recorded because the canonicity construction below needs [prom_wf]
      on BOTH sides of the retag. *)
  Lemma prom_wf_retag f log i (ag : wpagent P) :
    prom_wf log i ag ↔ prom_wf (retag_log f log) i ag.
  Proof.
    rewrite /prom_wf. split.
    - intros Hp ts Hts. destruct (Hp ts Hts) as (H1 & H2 & m & Hm & Ht).
      rewrite retag_log_length. split_and!; [done|done|].
      exists (retag_msg f (ts - 1)%nat m).
      split; [by apply retag_log_lookup_Some|done].
    - intros Hp ts Hts. destruct (Hp ts Hts) as (H1 & H2 & m' & Hm' & Ht).
      apply retag_log_lookup_inv in Hm' as (m & Hm & ->).
      rewrite retag_log_length in H2. split_and!; [done|done|]. by exists m.
  Qed.

  Lemma cfg_wf_retag f c : cfg_wf c ↔ cfg_wf (retag_cfg f c).
  Proof.
    rewrite /cfg_wf /=. split.
    - intros Hwf i ag Hlk. destruct (Hwf i ag Hlk) as [Hb Hp].
      rewrite retag_log_length. split; [done|by apply prom_wf_retag].
    - intros Hwf i ag Hlk. destruct (Hwf i ag Hlk) as [Hb Hp].
      rewrite retag_log_length in Hb. split; [done|by eapply prom_wf_retag].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 3. Conclusion transport: the observables are class-independent *)

  Lemma prog_of_retag f c : prog_of (retag_cfg f c) = prog_of c.
  Proof. done. Qed.

  Lemma mem_of_retag f c a : mem_of (retag_cfg f c) a = mem_of c a.
  Proof. rewrite /mem_of /= retag_latest_ts retag_log_byte //. Qed.

  (** The capstone's plumbing: a promise-free witness run matched against
      the RETAGGED behavior matches the original behavior too. *)
  Lemma retag_conclusion f (c cf : wpcfg P D) :
    prog_of cf = prog_of (retag_cfg f c) →
    (∀ a, mem_of cf a = mem_of (retag_cfg f c) a) →
    prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
  Proof.
    intros Hp Hm. split.
    - by rewrite Hp prog_of_retag.
    - intros a. by rewrite Hm mem_of_retag.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 4. Trace transport

      Traces carry no classes: [aev] is a label plus a fulfilled
      timestamp, and [wpagent] has no class field.  So a retag moves only
      the [pt_log] component of a bundle. *)

  Definition retag_traces f (TS : ptraces P D) : ptraces P D :=
    PTrs (pt_img TS) (retag_log f (pt_log TS)) (pt_trs TS).

  Lemma retag_traces_img f TS : pt_img (retag_traces f TS) = pt_img TS.
  Proof. done. Qed.

  Lemma retag_traces_log f TS :
    pt_log (retag_traces f TS) = retag_log f (pt_log TS).
  Proof. done. Qed.

  Lemma retag_traces_trs f TS : pt_trs (retag_traces f TS) = pt_trs TS.
  Proof. done. Qed.

  (** [astep_ok]'s ONLY log-reading conjuncts are [read_ok], [excl_ok] and
      the fulfilled-entry match — whose class is an existential binder. *)
  Lemma astep_ok_retag f img log i (ag : wpagent P) l g Dl :
    astep_ok img log i ag l g Dl ↔ astep_ok img (retag_log f log) i ag l g Dl.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc|];
      simpl.
    - done.
    - split.
      + intros (Hr & ? & ?). split_and!; [|done|done]. by apply retag_read_ok_2.
      + intros (Hr & ? & ?). split_and!; [|done|done]. by eapply retag_read_ok_1.
    - split.
      + intros (ts & k & Hin & Hm & Hok & Hf & HD).
        exists ts, (f (ts - 1)%nat). split_and!; [done| |done|done|done].
        by rewrite retag_log_lookup Hm.
      + intros (ts & k & Hin & Hm & Hok & Hf & HD).
        apply retag_log_lookup_inv in Hm as (m & Hm & Heq).
        destruct m as [pa dat tid ak]. rewrite /retag_msg /= in Heq.
        simplify_eq/=.
        exists ts, ak. split_and!; [done|done|done|done|done].
    - split.
      + intros (ts & k & Hlen & Hin & Hm & Hr & He & Hok & Hf & HD).
        exists ts, (f (ts - 1)%nat).
        split_and!; [done|done| | | |done|done|done].
        * by rewrite retag_log_lookup Hm.
        * by apply retag_read_ok_2.
        * by apply retag_excl_ok_2.
      + intros (ts & k & Hlen & Hin & Hm & Hr & He & Hok & Hf & HD).
        apply retag_log_lookup_inv in Hm as (m & Hm & Heq).
        destruct m as [pa dat tid ak]. rewrite /retag_msg /= in Heq.
        simplify_eq/=.
        exists ts, ak. split_and!; [done|done|done| | |done|done|done].
        * by eapply retag_read_ok_1.
        * by eapply retag_excl_ok_1.
    - done.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Lemma asteps_wf_retag f img log i ags evs :
    asteps_wf pstep img log i ags evs ↔
    asteps_wf pstep img (retag_log f log) i ags evs.
  Proof.
    rewrite /asteps_wf. split.
    - intros [Hlen Hst]. split; [done|].
      intros k ev ag ag' Hev Hk Hk'.
      destruct (Hst k ev ag ag' Hev Hk Hk') as (st' & g & Hps & Hok & Heq).
      exists st', g. split_and!; [done| |done]. by apply astep_ok_retag.
    - intros [Hlen Hst]. split; [done|].
      intros k ev ag ag' Hev Hk Hk'.
      destruct (Hst k ev ag ag' Hev Hk Hk') as (st' & g & Hps & Hok & Heq).
      exists st', g. split_and!; [done| |done]. by eapply astep_ok_retag.
  Qed.

  Lemma atrace_wf_retag f img log i T :
    atrace_wf pstep img log i T ↔ atrace_wf pstep img (retag_log f log) i T.
  Proof. apply asteps_wf_retag. Qed.

  Lemma ptraces_of_retag f TS mid c :
    ptraces_of pstep TS mid c →
    ptraces_of pstep (retag_traces f TS) (retag_cfg f mid) (retag_cfg f c).
  Proof.
    intros (Himg & Hlog & Hlen & Hwf & Hfst & Hlst & Hlc & Hic & Hlenc).
    rewrite /ptraces_of /retag_traces /retag_cfg /=.
    split_and!; [done|by rewrite Hlog|done| | | |by rewrite Hlc|done|done].
    - intros i T HT. by apply atrace_wf_retag, (Hwf i T HT).
    - intros i T HT. by apply Hfst.
    - intros i T HT. by apply Hlst.
  Qed.

  (** ... AND THE SAME WITH THE DEVICE WITNESS (M5/B4).  [DS] is untouched:
      the witness is a pure ORDER on trace positions, and every clause of
      [ptraces_dev_of] beyond [ptraces_of] reads only [pt_trs] (through
      [ev_at]/[ev_din]/[ev_dout]/[dev_at]) and [pc_dev] — none of which the
      retag moves, since it rewrites [pt_log]/[pc_log] alone.  Needed
      because a capstone that retag-precomposes must carry its whole
      decomposition, witness included, across the retag. *)
  Lemma ptraces_dev_of_retag f TS DS mid c :
    ptraces_dev_of pstep pdev TS DS mid c →
    ptraces_dev_of pstep pdev (retag_traces f TS) DS
      (retag_cfg f mid) (retag_cfg f c).
  Proof.
    intros (Hof & Hd & HW1 & HW2 & HW3 & HW4 & HW5 & HW6).
    split_and!; [by apply ptraces_of_retag|exact Hd|exact HW1|exact HW2
                |exact HW3|exact HW4|exact HW5|exact HW6].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** 5. THE CANONICAL RETAG

      [cls_canonical] is [WeakComposeLang.xv6_cone_premises]'s [Hcls]
      conjunct verbatim, with [lbl_class] abstracted to the parameter
      [clsf] (the consumer instantiates [clsf :=
      WeakSailLTS2.lbl_class_p], the program-blind wrapper around
      [WeakSailLTS2.lbl_class]). *)

  (** [cls_canonical] MOVED to [WeakRobustTrace] (G6a): the pinned pf
      fragment consumes it in the replay, so it is Layer-1 vocabulary now,
      not this file's.  What stays here is what this file PROVES — that
      every bundle can be brought into that form. *)

  (** THE SCAN.  [f] must be a FUNCTION, and the fulfil event of a log
      position is only known to EXIST — but the trace is a finite list, so
      the event is found by [list_find], not by choice.  Everything here is
      decidable ([option nat] equality), so no axiom enters. *)
  Definition fulfil_at (T : atrace P D) (p : nat) : option (nat * aev D) :=
    list_find (λ ev, ae_ts ev = Some (S p)) (at_evs T).

  Definition canon_f (clsf : P → wlabel → wstate → wm_class)
      (TS : ptraces P D) (p : nat) : wm_class :=
    match pt_log TS !! p with
    | None => WCplain
    | Some m =>
        match wm_tid m with
        | None => WCplain
        | Some i =>
            match pt_trs TS !! i with
            | None => WCplain
            | Some T =>
                match fulfil_at T p with
                | None => WCplain
                | Some (k, ev) =>
                    match at_ags T !! k with
                    | None => WCplain
                    | Some ag => clsf (pa_st ag) (ae_lb ev) (pa_ws ag)
                    end
                end
            end
        end
    end.

  (** The scan's correctness: given the fulfil event and its uniqueness,
      [canon_f] computes exactly that event's class. *)
  Lemma canon_f_spec clsf TS p m i T k ev ag :
    pt_log TS !! p = Some m → wm_tid m = Some i →
    pt_trs TS !! i = Some T →
    at_evs T !! k = Some ev → ae_ts ev = Some (S p) →
    at_ags T !! k = Some ag →
    (∀ k1 k2 ev1 ev2,
       at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
       at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) → k1 = k2) →
    canon_f clsf TS p = clsf (pa_st ag) (ae_lb ev) (pa_ws ag).
  Proof.
    intros Hm Hi HT Hev Hts Hag Huniq.
    rewrite /canon_f Hm Hi HT.
    destruct (fulfil_at T p) as [[k' ev']|] eqn:E.
    - apply list_find_Some in E as (Hev' & Hts' & _).
      have Hkk : k' = k by eapply Huniq.
      subst k'. assert (ev' = ev) as -> by congruence.
      by rewrite Hag.
    - exfalso. rewrite /fulfil_at list_find_None in E.
      by eapply (Forall_lookup_1 _ _ _ _ E Hev).
  Qed.

  (** The one degenerate corner the scan cannot see: a fulfil of timestamp
      [0] would key on log position [0 - 1 = 0] and be indistinguishable
      from a fulfil of timestamp [1].  Promised timestamps are positive
      ([prom_wf]), so this never happens; it is a hypothesis of the
      canonicity lemma and is discharged in [behavior_canonical]. *)
  Definition ts_pos (TS : ptraces P D) : Prop :=
    ∀ i T k ev ts,
      pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
      ae_ts ev = Some ts → (0 < ts)%nat.

  Lemma cls_canonical_canon clsf TS :
    (∀ i T, pt_trs TS !! i = Some T →
       atrace_wf pstep (pt_img TS) (pt_log TS) i T) →
    ts_pos TS →
    cls_canonical clsf (retag_traces (canon_f clsf TS) TS).
  Proof.
    intros Hwf Hpos i T k ev ag ts m HT Hev Hag Hts Hm.
    simpl in HT, Hm.
    apply retag_log_lookup_inv in Hm as (m0 & Hm0 & ->).
    rewrite retag_msg_ak.
    have Hts0 : (0 < ts)%nat by eapply Hpos.
    have Hsp : S (ts - 1)%nat = ts by lia.
    (* the trace's own step at [k] names [i] as the message's author *)
    specialize (Hwf i T HT).
    destruct (asteps_wf_step pstep _ _ _ _ _ _ _ Hwf Hev)
      as (ag1 & ag1' & st1 & g1 & Hag1 & _ & _ & Hok & _).
    assert (ag1 = ag) as -> by congruence.
    have Htid : wm_tid m0 = Some i.
    { destruct (ae_lb ev) as [|aq lat base tvs asrc|rl base data asrc vsrc
                             |aq rl base tvs data asrc vsrc| | | | |];
        simpl in Hok.
      - destruct Hok as [_ HD]. by rewrite HD in Hts.
      - destruct Hok as (_ & _ & HD). by rewrite HD in Hts.
      - destruct Hok as (ts' & k' & _ & Hlk & _ & _ & HD).
        have Hq : ts' = ts by congruence. subst ts'.
        have Hm' : m0 = WMsg base data (Some i) k' by congruence.
        by rewrite Hm'.
      - destruct Hok as (ts' & k' & _ & _ & Hlk & _ & _ & _ & _ & HD).
        have Hq : ts' = ts by congruence. subst ts'.
        have Hm' : m0 = WMsg base data (Some i) k' by congruence.
        by rewrite Hm'.
      - destruct Hok as [_ HD]. by rewrite HD in Hts.
      - destruct Hok as [_ HD]. by rewrite HD in Hts.
      - destruct Hok as [_ HD]. by rewrite HD in Hts.
      - destruct Hok as [_ HD]. by rewrite HD in Hts.
      - destruct Hok as [_ HD]. by rewrite HD in Hts. }
    eapply (canon_f_spec clsf TS (ts - 1)%nat m0 i T k ev ag);
      [done|done|done|done|by rewrite Hsp|done|].
    intros k1 k2 ev1 ev2 He1 Ht1 He2 Ht2.
    rewrite Hsp in Ht1 Ht2.
    by eapply (asteps_fulfil_unique pstep pdev (pt_img TS) (pt_log TS) i
                 (at_ags T) (at_evs T) ts).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** [ts_pos] out of the promise phase

      A trace event's fulfilled timestamp is in the fulfilling agent's
      promise set at that point ([astep_ok_del]); promise sets only shrink
      along a trace ([asteps_prom_le]), so it is in the trace's FIRST
      record's set, which is [mid]'s — and [cfg_wf mid]'s [prom_wf] says
      every promised timestamp is positive. *)

  Lemma cfg_wf_promise_run c c' :
    cfg_wf c → rtc (wp_promise_step (P:=P) (D:=D)) c c' → cfg_wf c'.
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs _ IH]; [done|].
    apply IH. by eapply (cfg_wf_promise_step pstep).
  Qed.

  Lemma ts_pos_of_ptraces TS mid c :
    cfg_wf mid → ptraces_of pstep TS mid c → ts_pos TS.
  Proof.
    intros Hcfg (Himg & Hlog & Hlen & Hwf & Hfst & _ & _ & _ & _).
    intros i T k ev ts HT Hev Hts.
    specialize (Hwf i T HT). specialize (Hfst i T HT).
    rewrite Himg Hlog in Hwf.
    (* the record at [k] holds [ts] *)
    destruct (asteps_wf_step pstep _ _ _ _ _ _ _ Hwf Hev)
      as (ag & ag' & st' & g & Hag & _ & _ & Hok & _).
    have Hin : ts ∈ pa_prom ag by eapply astep_ok_del.
    (* ... hence so does the FIRST record, which is [mid]'s agent [i] *)
    have Hilt : (i < length (pc_ags mid))%nat.
    { rewrite -Hlen. by eapply lookup_lt_Some. }
    have [ag0 Hag0] : is_Some (pc_ags mid !! i) by apply lookup_lt_is_Some_2.
    have Hfst0 : at_ags T !! 0%nat = Some ag0 by rewrite Hfst.
    have Hsub : pa_prom ag ⊆ pa_prom ag0.
    { eapply (asteps_prom_le pstep (pc_img mid) (pc_log mid) i
                (at_ags T) (at_evs T) 0%nat k); [done|lia|done|done]. }
    have Hin0 : ts ∈ pa_prom ag0 by set_solver.
    destruct (Hcfg i ag0 Hag0) as [_ Hp].
    by destruct (Hp ts Hin0) as (? & _ & _).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE DELIVERABLE: every behavior retags to a CANONICAL one *)

  Theorem behavior_canonical (clsf : P → wlabel → wstate → wm_class)
      img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep →
    wp_behavior pstep img d0 ps c →
    ∃ (f : nat → wm_class) mid TS,
      wp_behavior pstep img d0 ps (retag_cfg f c) ∧
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps)
        (retag_cfg f mid) ∧
      ptraces_of pstep (retag_traces f TS) (retag_cfg f mid) (retag_cfg f c) ∧
      cls_canonical clsf (retag_traces f TS) ∧
      prog_of (retag_cfg f c) = prog_of c ∧
      (∀ a, mem_of (retag_cfg f c) a = mem_of c a).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_traced pstep pdev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & Hprom & HTS & Hnp).
    exists (canon_f clsf TS), mid, TS.
    have Hcfg : cfg_wf mid.
    { eapply cfg_wf_promise_run; [apply (cfg_wf_init (P:=P) img d0 ps)|done]. }
    have Hpos : ts_pos TS by eapply ts_pos_of_ptraces.
    split_and!.
    - by apply wp_behavior_retag.
    - rewrite -(retag_wp_init (canon_f clsf TS) img d0 ps).
      by apply wp_promise_steps_retag.
    - by apply ptraces_of_retag.
    - apply cls_canonical_canon; [|done].
      destruct HTS as (_ & _ & _ & Hwf & _). exact Hwf.
    - apply prog_of_retag.
    - apply mem_of_retag.
  Qed.

End machine.

Global Arguments retag_cfg {P D} _ _.
Global Arguments retag_traces {P D} _ _.
Global Arguments canon_f {P D} _ _ _.
Global Arguments fulfil_at {P D} _ _.
Global Arguments ts_pos {P D} _.

(* ====================================================================== *)
(** ** What stage B inherits

    - [behavior_canonical]: a lat-free behavior is matched by a behavior
      of the SAME program with the SAME [prog_of] and [mem_of], whose
      traced factorization satisfies [cls_canonical clsf] — i.e. the
      capstone's [Hcls] premise, at [clsf := WeakSailLTS2.lbl_class_p].
      So
      the capstone may quantify over canonical-class bundles and lose
      nothing: precompose with the retag, transport the conclusion back
      with [retag_conclusion].

    - [wpstep_retag] / [wp_promise_step_retag] / [atrace_wf_retag] /
      [ptraces_of_retag]: the reusable half — any OTHER inert field added
      to [wmsg] later gets the same treatment by the same argument.

    - What is deliberately NOT here: the converse simulation (false — see
      the header), and the instantiation at [lbl_class_p] (that belongs with
      the capstone, which already imports [WeakSailLTS2]). *)

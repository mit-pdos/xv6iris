(** * WeakRvwmoProgress.v — (W-1)'s PROGRESS AND (W-2) [wub], AS ADEQUACY FACTS

    Design: [claude-notes/projects/weak-memory-certification.md], the
    NINTH-PASS checkpoint item 1b — "(W-1)/(W-2) are the EWPs' content
    (progress; the fence hook); state them once against the WP package and
    discharge from the adequacy theorem (a sibling export), not per site".

    [WeakRvwmoWalk] closed (R-2) to a per-state certification policy whose
    honest ledger is two items: (W-1) [wpol] — the read/register policy,
    "carrying (P-4) progress" — and (W-2) [wub] = [WeakRvwmoCert3.wit_fence_ub]
    at the next position.  This leaf does three things.

    ------------------------------------------------------------------------
    §1–§2  PROGRESS, FROM TIER 1.

    The tier-1 capstone's PROGRESS conjunct
    ([WeakSrvwmoCapstone.xv6_srvwmo_safe]'s third bullet) says every thread
    of every erased-reachable configuration is [reducible].  §1 turns that
    into the vocabulary the walk speaks: at every pf-reachable configuration
    the HART's own program state can take a [pstep_ev] step
    ([epf_progress_hart]), and hence — §2 — at every CERTIFIED CANDIDATE
    (a [WeakRvwmoGlue.run_data], realized by [run_erased]'s route with the
    program-state identification KEPT) every hart's current [pexv6] can step
    ([cert_progress]).  That is exactly "the monad is not stuck", which is
    what building the walk's [WeakRvwmoConf.hemit] needs at every block.

    §3 THE BRIDGE the read answer needs.  [reducible] gives SOME step, and a
    pf read step's answer is chosen by the machine; the walk needs the step
    AT A PARTICULAR message (its G-source, or the log's latest).  The
    program half of the language is ANSWER-GENERIC — [WeakEvInst]'s
    [pnode_step] MemRead arm accepts any byte list of the node's own width,
    and only the memory half ([WeakEvInst.elab_ok] / [mstep_ok]) constrains
    which one is admissible.  [step_at_chosen_answer] is that bridge:
    progress + "the node is a plain load node of width [w]" gives a step at
    EVERY [tvs2] of width [w]; [step_at_same_values] is the re-indexing
    twin (same values, different timestamps — the SAME successor node).

    WHAT PROGRESS DOES *NOT* GIVE, recorded: the tier-1 conjunct is
    one-step ("a step exists"), not a termination fact, so it does not by
    itself deliver [WeakRvwmoCert3.at_boundary] of a run's endpoint.  It
    need not: see §5's finding — [wpol] as landed has NO substituted branch
    at all, so [boundary_reconverge_run] is not among its obligations.

    ------------------------------------------------------------------------
    §4  (W-2) [wub], DERIVED — BOTH BRANCHES ANSWERED.

    (b) IN GENERAL: [wit_fence_ub]'s guard [WeakRvwmoFloor.fhook] is a
        [pr]/[sr] fence between the witness and the read whose floor it
        would raise, and rule 4 ([gfence_covers]) then orders the WITNESS
        BEFORE that read in gmo — which is the negation of "the witness is
        the cycle's backward step over it".  So a witness has no publishing
        fence between it and the event it steps back over
        ([wub_of_witness], [no_fence_over_backstep]).

    (a) AT THE WALK, something stronger and cheaper holds.  The walk's
        witness set is LOG-DECIDED ([WeakRvwmoWalk.wwit]) and the segment it
        certifies is SUBSTITUTION-FREE by the graph-side datum
        [WeakRvwmoWalk.wrow_in_log]; extended to row position 0
        ([wrow_in_log'] below — the same decidable datum, one position
        wider) it says NO position of hart [x] is a witness at all.  Since
        [wit_fence_ub] quantifies only over witnesses ON [r]'s OWN HART, it
        is VACUOUS: [wub_of_row].  The same argument kills the
        [wit_fence_ub] conjunct inside [WeakRvwmoCert3.cpol_ctx]
        ([cpol_ctx_of_ctrace]), so the context reduces to the [ctrace]
        bookkeeping.  The witness set does NOT change shape, and
        [W_poloc_closed] is untouched.

    ------------------------------------------------------------------------
    §5  THE RESTATEMENTS.  [wlk_seg_of_cert'] is [WeakRvwmoWalk]'s §4.1 with
    (W-2) GONE; [walk_seg_data] is the per-state residue it leaves;
    [walk_supply_of_wp] and [xv6_rvwmo_safe_modulo_walk'] are the walk's
    theorem and the capstone with (R-2) at that residue.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports
    this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakLitmus.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvLang.
Require Import RiscvAdequacy.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakLang.
Require Import WeakEvCapstone.
Require Import WeakEvAdequacy.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvProv.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoProbeK1.
Require Import WeakRvwmoLinInd.
Require Import WeakGhost.
Require Import WeakRvwmoLock.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import WeakRvwmoGlue2.
Require Import WeakSrvwmoLitmus.
Require Import WeakSrvwmoCapstone.
Require Import WeakRvwmoCapstone.
Require Import WeakRvwmoWalk.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. PROGRESS AT THE MACHINE

    [reducible] in [weak_ev_lang] is a fact about an EXPRESSION; [pstep_ev]
    is a fact about a PROGRAM STATE.  [WeakEvPf] already says the two are
    the same object ([ehexp_sail]: a hart's expression IS [Sail] of its
    monad and parked fence; [ehart_ag]: its agent's program state is that
    pair together with σ's register file and announced bits), and
    [WeakEvInst.ecycle_step_pstep_hart] is the factorization.  So the
    translation is one destruct of [eprim_step]'s five arms. *)

Definition estep_exists (p : pexv6) (d : dev_state) : Prop :=
  ∃ (l : wlabel) (p' : pexv6) (d' : dev_state), pstep_ev p d l p' d'.

(** THE TRANSLATION.  The corpse arm is refuted by [ethread_live] — which
    is why the era hypothesis travels with the run. *)
Lemma reducible_hart_pstep (gen : nat) (c : CPU) (m : M unit) (fn : ofence)
    (σ : wgstate) :
  ethread_live σ gen →
  reducible (Λ := weak_ev_lang) (Sail gen c m fn) σ →
  estep_exists (PHart c m (wgregs σ c) fn (wgib σ c)) (wgdev σ).
Proof.
  intros Hlive (κ & e' & σ' & efs & Hstep).
  destruct Hstep as [(gen0 & cpu0 & m0 & fn0 & He & _ & _ & Harm)
                    |[(gen0 & He & _)
                     |[(gen0 & dp & dws & He & _)
                      |[(gen0 & He & _)|(He & _)]]]];
    [|discriminate He..].
  injection He as -> -> -> ->.
  destruct Harm as [(_ & Hcy)|(Hnl & _)]; [|by destruct (Hnl Hlive)].
  destruct (ecycle_step_pstep_hart gen0 σ cpu0 m0 fn0 e' σ' Hcy)
    as (l & m' & ors & fn' & d' & oib & _ & Hph & _ & _).
  exists l, (PHart cpu0 m' (default (wgregs σ cpu0) ors) fn'
               (default (wgib σ cpu0) oib)), d'.
  split; [reflexivity|]. exists ors, oib.
  split_and!; [reflexivity|reflexivity|exact Hph].
Qed.

(** THE EXPORT.  Under the WP package, at EVERY pf-reachable configuration
    of the fresh era, EVERY hart's own program state can take a [pstep_ev]
    step.  This is [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s progress conjunct
    (through [WeakEvAdequacy.weak_ev_adequacy_reducible]) read at the
    pf machine, with [WeakEvPf.epf_rtc_erased] as the bridge. *)
Theorem epf_progress_hart (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  ∀ (P' : epool) (σ' : wgstate),
    rtc epf_run (ep_init gen, σ0) (P', σ') →
    ∀ c : CPU,
      estep_exists
        (PHart c (ehart_m (ep_h P' c)) (wgregs σ' c) (ehart_fn (ep_h P' c))
           (wgib σ' c))
        (wgdev σ').
Proof.
  intros (Hgen & Hpow & Hgen0 & Hlog & Hws) Hwp P' σ' Hrun c.
  have Hlive0 : ethread_live σ0 gen.
  { rewrite /ethread_live Hpow Hgen0 Hgen. by split. }
  have Hgp : ep_gen (ep_init (gen)) = gen by reflexivity.
  destruct (epf_run_live gen (ep_init gen, σ0) (P', σ') Hlive0 Hgp Hrun)
    as [Hlive' Hgen'].
  simpl in Hlive', Hgen'.
  have Herased :
    rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (epool_list P', σ').
  { pose proof (epf_rtc_erased (ep_init gen, σ0) (P', σ') Hrun) as He.
    by rewrite /= epool_list_init in He. }
  have Hin : ehexpr P' c ∈ epool_list P'.
  { apply elem_of_list_lookup_2 with (fin_to_nat c).
    apply epool_list_hart_lookup. }
  have Hred : reducible (Λ := weak_ev_lang)
                (Sail gen c (ehart_m (ep_h P' c)) (ehart_fn (ep_h P' c))) σ'.
  { rewrite -Hgen' -ehexp_sail.
    exact (weak_ev_adequacy_reducible Σ gen σ0 D Hgen Hpow Hgen0 Hlog Hws Hwp
             (epool_list P') σ' (ehexpr P' c) Herased Hin). }
  exact (reducible_hart_pstep gen c _ _ σ' Hlive' Hred).
Qed.

(* ====================================================================== *)
(** * 2. PROGRESS AT A CERTIFIED CANDIDATE

    [WeakRvwmoGlue.run_erased] realizes a [run_data] as an ERASED run and
    keeps the LOG identification.  Progress needs the OTHER identification
    the same composition establishes and [run_erased] drops: the pf
    configuration's per-hart PROGRAM STATE is the candidate's own
    [pst (length (cd_tr c))], and its fabric is [dv] there.  That is
    [WeakAxRealize.exec_wf_pf_run_prog]'s [pa_st <$> pc_ags] / [pc_dev]
    conjuncts, carried through [WeakEvCapstone.wp_pf_rtc_epf_rtc]'s
    [ecfg_of P' σ' = c]. *)
Theorem cert_progress (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) (G : gexec)
    (c : cand) (pst : nat → list pexv6) (dv : nat → dev_state) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  gx_img G = img_z (wgimg σ0) →
  wp_package Σ gen σ0 D →
  run_data boot d0 N G c pst dv →
  ∀ (cc : CPU) (p : pexv6),
    pst (length (cd_tr c)) !! (fin_to_nat cc) = Some p →
    estep_exists p (dv (length (cd_tr c))).
Proof.
  intros Hfr Hb1 Hb2 Hb3 Hwp [Hcons Himg Hpst0 Hdv0 Hprog] cc p Hp.
  have Hfr' := Hfr.
  destruct Hfr' as (Hgen & Hpow & Hgen0 & Hlog & Hws).
  have Hlive : ethread_live σ0 gen.
  { rewrite /ethread_live Hpow Hgen0 Hgen. by split. }
  destruct (srvwmo_realizable c Hcons) as (Hwf & Htr & Heximg).
  destruct (exec_wf_pf_run_prog pstep_ev pcls_ev pst dv (cand_exec c)
              pcls_ev_eqr Hwf Hprog) as (cf & Hrun & Hpg & Hdev & Hm).
  rewrite Heximg Himg Hb3 Hpst0 Hb1 Hdv0 Hb2 in Hrun.
  rewrite -(ecfg_of_init gen σ0 Hlog Hws) in Hrun.
  destruct (wp_pf_rtc_epf_rtc (ep_init gen) σ0 cf Hlive Hrun)
    as (P' & σ' & Hr & Heq).
  rewrite Htr in Hpg Hdev. rewrite -Heq in Hpg Hdev.
  have Hags : pc_ags (ecfg_of P' σ') = eags P' σ' by reflexivity.
  have Hdv' : pc_dev (ecfg_of P' σ') = wgdev σ' by reflexivity.
  rewrite Hags in Hpg. rewrite Hdv' in Hdev.
  (* the fabric: [dv] at the endpoint IS the reached σ's device state *)
  rewrite -Hdev.
  (* the program state: the candidate's [pst] entry IS the hart's agent *)
  have Hag : pst (length (cd_tr c)) !! (fin_to_nat cc)
           = Some (pa_st (ehart_ag P' σ' cc)).
  { rewrite -Hpg list_lookup_fmap (eags_hart P' σ' cc) //. }
  rewrite Hag in Hp. injection Hp as <-.
  by apply (epf_progress_hart Σ gen σ0 D Hfr Hwp P' σ' Hr cc).
Qed.

(* ====================================================================== *)
(** * 3. THE BRIDGE: THE STEP AT THE CHOSEN ANSWER

    What progress gives: a step exists, at SOME label — and at a memory-read
    node the label's answer is whatever the machine's own nondeterminism
    picked, constrained by the MEMORY half ([WeakEvInst.elab_ok]'s
    [read_ok]) which [pstep_ev] does not see at all.

    What the walk's policy needs: the step at a PARTICULAR message — the
    read's G-source (the re-indexing case) or the log's latest (the witness
    case).  The two are joined by the program half's ANSWER-GENERICITY,
    which is a theorem, not an assumption:

      - same VALUES, different timestamps: [WeakEvInst.pstep_ev_ts_load] —
        the same successor node, so the whole rest of the run is untouched;
      - different values: [WeakRvwmoCert2.pstep_ev_load_subst] — a step
        exists for ANY byte list of the node's own width, at a successor
        node that differs.

    Admissibility of the chosen answer is the OTHER half and is proved per
    case where the walk chooses it ([WeakRvwmoCert3.cpol_read] /
    [WeakRvwmoCert2.cert_read_witness], both giving [mstep_ok]); the two
    halves never interact, which is the point of the factorization. *)

(** "The node is a plain load node of width [w] at [(aq, base)]" — read off
    the steps it admits, so it is a property of the PROGRAM state alone. *)
Definition load_node (p : pexv6) (d : dev_state) (aq : bool) (base : Z)
    (w : nat) : Prop :=
  ∀ (l : wlabel) (p' : pexv6) (d' : dev_state),
    pstep_ev p d l p' d' →
    ∃ tvs : list (nat * bv 8), l = LLoad aq false base tvs [] ∧ length tvs = w.

Theorem step_at_chosen_answer (cpu : CPU) (m : M unit) (rs : regstate)
    (fn : ofence) (ib : oib32) (d : dev_state)
    (aq : bool) (base : Z) (w : nat) (tvs2 : list (nat * bv 8)) :
  estep_exists (PHart cpu m rs fn ib) d →
  load_node (PHart cpu m rs fn ib) d aq base w →
  length tvs2 = w →
  ∃ (m2 : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32)
    (d' : dev_state),
    pstep_ev (PHart cpu m rs fn ib) d (LLoad aq false base tvs2 [])
      (PHart cpu m2 rs' fn' ib') d'.
Proof.
  intros (l & p' & d' & Hst) Hnode Hlen.
  destruct (Hnode l p' d' Hst) as (tvs & -> & Htvs).
  destruct (pstep_ev_phart cpu m rs fn ib d _ p' d' Hst)
    as (m' & rs' & fn' & ib' & ->).
  destruct (pstep_ev_load_subst cpu m rs fn ib d aq base tvs tvs2
              m' rs' fn' ib' d' Hst ltac:(lia)) as (m2 & Hst2).
  by exists m2, rs', fn', ib', d'.
Qed.

(** THE RE-INDEXING TWIN: at the SAME values the successor node does not
    move, which is what makes [WeakRvwmoCert2.lbl_reidx] (values kept,
    timestamps free) the walk's label correspondence. *)
Corollary step_at_same_values (p : pexv6) (d : dev_state) (aq : bool)
    (base : Z) (tvs tvs2 : list (nat * bv 8)) (p' : pexv6) (d' : dev_state) :
  pstep_ev p d (LLoad aq false base tvs []) p' d' →
  tvs2.*2 = tvs.*2 →
  pstep_ev p d (LLoad aq false base tvs2 []) p' d'.
Proof. apply pstep_ev_ts_load. Qed.

(* ====================================================================== *)
(** * 4. (W-2) [wub], DISCHARGED

    ** 4.1 The general fact: a witness has no publishing fence over its own
    backward step.

    [WeakRvwmoFloor.fhook G r k true] is "a [pr]/[sr] fence of [r]'s hart at
    a row position in [[k, r.2)]".  With the witness at position [k - 1]
    that is exactly rule 4's [gfence_covers] from the witness to [r], so
    ppo⁻ orders the witness BEFORE [r] in gmo — and a witness is by
    definition the BACKWARD step of the cycle.  Two strict positions in one
    order cannot both hold. *)

Lemma gmo_lt_asym (G : gexec) (e1 e2 : geid) :
  gmo_lt G e1 e2 → ¬ gmo_lt G e2 e1.
Proof. intros (_ & _ & H1) (_ & _ & H2). lia. Qed.

Theorem no_fence_over_backstep (G : gexec) (e z : geid) :
  gppo_gmo G → gmo_lt G z e → ¬ gfence_covers G e z.
Proof.
  intros Hppo Hlt Hfc.
  apply (gmo_lt_asym G z e Hlt). apply Hppo. by right; left.
Qed.

(** The hook IS rule 4's fence, at a read/read pair of one hart. *)
Lemma fhook_gfence_covers (G : gexec) (e r : geid) :
  e.1 = r.1 → glbl_is G e lb_is_r → glbl_is G r lb_is_r →
  fhook G r (S e.2) true → gfence_covers G e r.
Proof.
  intros Hag He Hr (kf & pr & pw & sr & sw & H1 & H2 & H3 & H4 & H5).
  simpl in H4. exists pr, pw, sr, sw. split_and!.
  - rewrite /gfence_between. split_and!; [exact Hag|lia|].
    exists kf. split_and!; [lia|exact H2|]. by rewrite Hag.
  - left. by split.
  - left. by split.
Qed.

(** (W-2)'s CONTENT, in general: at a witness [e] that steps BACK over [r]
    (i.e. [r] is gmo-before [e], which is what makes [e] a cycle's backward
    step), the guard of [wit_fence_ub] never fires. *)
Theorem wub_of_witness (G : gexec) (e r : geid) :
  gppo_gmo G → e.1 = r.1 →
  glbl_is G e lb_is_r → glbl_is G r lb_is_r →
  gmo_lt G r e →
  ¬ fhook G r (S e.2) true.
Proof.
  intros Hppo Hag He Hr Hlt Hfh.
  apply (no_fence_over_backstep G e r Hppo Hlt).
  by apply fhook_gfence_covers.
Qed.

(** ** 4.2 At the WALK: [wub] is VACUOUS

    [WeakRvwmoWalk.wrow_in_log] is the graph-side datum "hart [x]'s reads at
    row positions [≥ 1] all draw on writes the log has reached".  Widened by
    one position it says NO position of hart [x] is a witness — and
    [wit_fence_ub] quantifies only over witnesses on [r]'s OWN hart, so
    there is nothing to discharge.  The datum stays decidable from [G] and
    the write count; the witness set keeps its shape. *)
Definition wrow_in_log' (G : gexec) (x : agent) (n : nat) : Prop :=
  ∀ k : nat, wsrc_le G n (x, k).

Lemma wrow_in_log'_weaken (G : gexec) (x : agent) (n : nat) :
  wrow_in_log' G x n → wrow_in_log G x n.
Proof. intros H k _. apply H. Qed.

Lemma wrow_no_wit (G : gexec) (x : agent) (n k : nat) :
  wrow_in_log' G x n → ¬ wwit G n (x, k).
Proof. intros H. by apply wsrc_le_not_wwit, H. Qed.

(** THE VACUITY, once: every hypothesis list of [wit_fence_ub] names a
    witness on hart [x], and there is none. *)
Lemma wit_fence_ub_vacuous (G : gexec) (x : agent) (n : nat) (c : cand)
    (ev : nat → geid) (k : nat) :
  wrow_in_log' G x n → wit_fence_ub G c ev (wwit G n) (x, k).
Proof.
  intros Hrow p s Hs HW Hag _. exfalso. simpl in Hag.
  have Heq : ev p = (x, (ev p).2).
  { rewrite -Hag. by destruct (ev p). }
  rewrite Heq in HW. by eapply wrow_no_wit.
Qed.

(** (W-2), DISCHARGED. *)
Theorem wub_of_row (G : gexec) (x : agent) (n : nat) :
  wrow_in_log' G x n → wub G (wwit G n) x.
Proof. intros Hrow c0 lb' ev' _. by apply wit_fence_ub_vacuous. Qed.

(** ... and the same argument removes [wit_fence_ub] from the CONTEXT
    [WeakRvwmoCert3.cpol_ctx] carries, leaving the [ctrace] bookkeeping
    alone. *)
Lemma cpol_ctx_of_ctrace (G : gexec) (x : agent) (n : nat) (c : cand)
    (ev : nat → geid) :
  wrow_in_log' G x n →
  ctrace_prefix G c ev (wwit G n) →
  cpol_ctx G (wwit G n) x c.
Proof.
  intros Hrow Hpc. exists ev. split_and!;
    [exact Hpc|by apply wit_fence_ub_vacuous|by apply wrow_no_wit].
Qed.

(* ====================================================================== *)
(** * 5. THE RESTATEMENTS, AT THE REPAIRED INTERFACE *)

(** ** 5.1 The segment, with (W-2) gone.

    [WeakRvwmoWalk.wlk_seg_of_cert] verbatim, minus the [wub] and [wnw_seg]
    premises: the widened graph-side datum [wrow_in_log'] discharges BOTH
    (that hart has no witness at any position at all).  A hart that DOES
    carry a witness elsewhere in its row is served by the segment-restricted
    form directly ([wlk_seg_of_cert] with [wnw_seg] and an honest [wub]). *)
Theorem wlk_seg_of_cert' (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (k0 kz : nat) (ws0 : wstate) (rowseg : list lbl)
    (es : list eitem) (pfin : pexv6) (m0 : M unit) (rs10 : regstate)
    (fn0 : ofence) (ib0 : oib32) (St : cyc_state) (rs20 : regstate) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  wrow_in_log' G x n →
  hemit (λ _, d0) k0 ws0 rowseg (PHart cpu m0 rs10 fn0 ib0) es pfin →
  (∀ i lb, rowseg !! i = Some lb → wQ G n x k0 kz (k0 + i)%nat lb) →
  cst_ok d0 St →
  wctx G n x kz k0 (cst_c St) →
  cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) →
  dreg_agree (λ nn, nn ∉ []) rs10 rs20 →
  w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 →
  ∃ (St' : cyc_state) (tradd : list estep),
    seg_step d0 (SegOut x rowseg (cd_end (cst_c St)) tradd) St St' ∧
    wctx G n x kz (k0 + length rowseg)%nat (cst_c St') ∧
    cd_img (cst_c St') = cd_img (cst_c St) ∧
    cst_pst St' 0%nat = cst_pst St 0%nat ∧
    cst_dv St' 0%nat = cst_dv St 0%nat.
Proof.
  intros Hcons Hpc Hrow Hem HQ Hok Hctx Hp Hag Hrelp.
  eapply (wlk_seg_of_cert G n x cpu d0 k0 kz ws0 rowseg es pfin m0 rs10
            fn0 ib0 St rs20);
    [exact Hcons|exact Hpc|by apply wub_of_row
    |intros k _ _; by apply wrow_no_wit
    |exact Hem|exact HQ|exact Hok|exact Hctx|exact Hp|exact Hag|exact Hrelp].
Qed.

(** ** 5.2 THE PER-STATE RESIDUE, REPAIRED

    [WeakRvwmoWalk.walk_policy] asks for a certified segment per write.
    [walk_seg_data'] is what §5.1 needs to BUILD one, at the REPAIRED,
    row-position-indexed interface.  Its semantic content is now exactly
    TWO items, since (W-1) [wpol] is discharged outright at an aligned
    candidate ([WeakRvwmoWalk.wpol_of_sites]):

      - the EMISSION [hemit …] of hart [x]'s stretch through [G]'s
        [(n+1)]-st write (where PROGRESS lives, §1–§3);
      - the SITE DATA [wQ] — [G]'s label at each position of the stretch,
        its sources already in the log, and the exit write being the log's
        next entry — together with the walk state's own alignment [wctx]
        and the two witness-set side conditions [wub] / [wnw_seg], which
        are stated only over the positions the segment covers. *)
Definition walk_seg_data' (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) : Prop :=
  ∀ St n, wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
  ∃ (x : agent) (cpu : CPU) (k0 : nat) (ws0 : wstate) (pre : list lbl)
    (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (es : list eitem) (pfin : pexv6) (m0 : M unit) (rs10 rs20 : regstate)
    (fn0 : ofence) (ib0 : oib32) (w : geid),
    (* the graph side: the segment's exit IS [G]'s [(n+1)]-st write *)
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some (WMsg base vs (Some x) kc) ∧
    Forall (λ lb, lb_is_w lb = false) pre ∧
    (* THE EMISSION — the progress-carrying input *)
    hemit (λ _, d0) k0 ws0 (pre ++ [WeakAxiomatic.LStore rl base vs kc])
      (PHart cpu m0 rs10 fn0 ib0) es pfin ∧
    (* THE SITE DATA, INDEXED BY ROW POSITION *)
    (∀ i lb, (pre ++ [WeakAxiomatic.LStore rl base vs kc]) !! i = Some lb →
       wQ G n x k0 (k0 + length pre)%nat (k0 + i)%nat lb) ∧
    (* the walk's state, ALIGNED to the segment's first position *)
    wctx G n x (k0 + length pre)%nat k0 (cst_c St) ∧
    cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) ∧
    dreg_agree (λ nn, nn ∉ []) rs10 rs20 ∧
    w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 ∧
    (* the witness set's side conditions, over the segment only *)
    W_poloc_closed G (wwit G n) ∧
    wub G (wwit G n) x ∧
    wnw_seg G n x k0 (k0 + length pre)%nat.

Theorem walk_policy_of_seg_data' (boot : agent → pexv6) (d0 : dev_state)
    (N : nat) (G : gexec) :
  rvwmo_minus_consistent G → walk_seg_data' boot d0 N G →
  walk_policy boot d0 N G.
Proof.
  intros Hcons Hdata St n Hinv Hn.
  destruct (Hdata St n Hinv Hn)
    as (x & cpu & k0 & ws0 & pre & rl & base & vs & kc & es & pfin &
        m0 & rs10 & rs20 & fn0 & ib0 & w &
        Hw & Hm & Hpre & Hem & HQ & Hctx & Hp & Hag & Hrelp & Hpc & Hub &
        Hnw).
  have Hok : cst_ok d0 St by destruct Hinv as (? & _).
  destruct (wlk_seg_of_cert G n x cpu d0 k0 (k0 + length pre)%nat ws0
              (pre ++ [WeakAxiomatic.LStore rl base vs kc]) es pfin m0 rs10
              fn0 ib0 St rs20 Hcons Hpc Hub Hnw Hem HQ Hok Hctx Hp Hag Hrelp)
    as (St' & tradd & Hstep & _ & Himg & Hpst & Hdv).
  exists x, rl, base, vs, kc, pre, tradd, St', w.
  split_and!; [exact Hw|exact Hm|exact Hpre|exact Hstep|exact Himg|exact Hpst
              |exact Hdv].
Qed.

(** ** 5.3 THE WALK'S THEOREM, at the repaired residue *)
Theorem walk_supply_of_wp' (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     walk_seg_data' boot d0 N (gd_g GD)) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hdata. apply walk_supply_of_policy. intros GD Hcons Hq.
  apply walk_policy_of_seg_data'; [|by apply Hdata].
  by destruct Hcons as (Hc & _ & _).
Qed.

(** ** 5.4 THE CAPSTONE, with (R-2) at the repaired residue *)
Theorem xv6_rvwmo_safe_modulo_walk' (Σ : gFunctors)
    `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) *)
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (* (R-2), at the repaired, position-indexed residue *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     walk_seg_data' (xboot σ0) (wgdev σ0) (xN σ0) (gd_g GD)) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hdata.
  apply (xv6_rvwmo_safe_modulo Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  by apply walk_supply_of_wp'.
Qed.

(** ** 5.5 THE OLD, OVER-QUANTIFIED RESIDUE, kept only as the subject of
    [WeakRvwmoWalk2] §4's machine-checked refutation. *)
Definition walk_seg_data_flat (boot : agent → pexv6) (d0 : dev_state)
    (N : nat) (G : gexec) : Prop :=
  ∀ St n, wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
  ∃ (x : agent) (cpu : CPU) (T : list wreg) (Q : lbl → Prop)
    (k0 : nat) (ws0 : wstate) (pre : list lbl) (rl : bool) (base : Z)
    (vs : list (bv 8)) (kc : wm_class) (es : list eitem) (pfin : pexv6)
    (m0 : M unit) (rs10 rs20 : regstate) (fn0 : ofence) (ib0 : oib32)
    (w : geid),
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some (WMsg base vs (Some x) kc) ∧
    Forall (λ lb, lb_is_w lb = false) pre ∧
    hemit (λ _, d0) k0 ws0 (pre ++ [WeakAxiomatic.LStore rl base vs kc])
      (PHart cpu m0 rs10 fn0 ib0) es pfin ∧
    Forall Q (pre ++ [WeakAxiomatic.LStore rl base vs kc]) ∧
    cpol_ctx G (wwit G n) x (cst_c St) ∧
    cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) ∧
    dreg_agree (λ nn, nn ∉ T) rs10 rs20 ∧
    w_relp (ms_ws (cand_last_st (cst_c St)) x) = w_relp ws0 ∧
    wrow_in_log' G x n ∧
    wpol_flat G (wwit G n) x cpu d0 T Q ∧
    cpolp x cpu d0 T (λ _ : nat, cpol_ctx G (wwit G n) x)
      (wcls_at G (wwit G n) x) (λ _ : nat, Q).

(* ====================================================================== *)
(** * 6. AUDIT *)

Print Assumptions reducible_hart_pstep.
Print Assumptions epf_progress_hart.
Print Assumptions cert_progress.
Print Assumptions step_at_chosen_answer.
Print Assumptions step_at_same_values.
Print Assumptions no_fence_over_backstep.
Print Assumptions wub_of_witness.
Print Assumptions wub_of_row.
Print Assumptions cpol_ctx_of_ctrace.
Print Assumptions wlk_seg_of_cert'.
Print Assumptions walk_policy_of_seg_data'.
Print Assumptions walk_supply_of_wp'.
Print Assumptions xv6_rvwmo_safe_modulo_walk'.

(* ====================================================================== *)
(** * 7. THE LEDGER AFTER THIS LEAF

    (W-2) [wub] IS GONE.  Branch (b) of the analysis holds in general
    ([wub_of_witness]: rule 4 orders a witness before any read a publishing
    fence separates it from, so the hook cannot fire over a backward step),
    and at the WALK the stronger vacuity holds ([wub_of_row]): the walk's
    segments are substitution-free by construction, so hart [x] has no
    witness at all.  The witness set is unchanged — no closure had to be
    added, and [W_poloc_closed] is untouched.

    (P-4) PROGRESS IS AN ADEQUACY FACT.  [cert_progress] derives "the hart's
    monad is not stuck at any certified configuration" from tier 1's
    progress conjunct, once and for the whole walk rather than per site.
    [step_at_chosen_answer] is the missing half: the machine's read step is
    nondeterministic in the ANSWER and the program half accepts any answer
    of the node's width, so "a step exists" plus "the chosen message is
    admissible" (the [mstep_ok] the walk already proves per case) gives the
    step at the chosen message.

    A FINDING ABOUT WHERE PROGRESS LIVES.  [WeakRvwmoWalk]'s §4 header says
    (P-4) rides inside [wpol] and that [WeakRvwmoCert3.boundary_reconverge_run]
    is applied there.  As [wpol] IS STATED that cannot be: its label
    correspondence is [WeakRvwmoCert2.lbl_reidx], which PRESERVES the read's
    values ([vs' = vs]) and only re-times it, and its conclusion lands at
    the SAME successor node [m'] as the emission's block.  So [wpol] admits
    no substituted branch, and the boundary re-convergence — with its
    [at_boundary] hypotheses, a TERMINATION fact that one-step progress does
    not supply — is not among its obligations.  [wpol]'s content is purely
    the read/register policy: the label re-indexing, [mstep_ok], the
    classification [wcls_at], and [dreg_agree] off the taint set.  What
    PROGRESS is needed for in the walk is one level up: the EMISSION
    [hemit …] that [walk_seg_data] supplies per state, which is a chain of
    [pstep_ev] steps and exists only if the hart can actually run its row.
    That is what §1–§3 deliver.

    WHAT REMAINS in [xv6_rvwmo_safe_modulo_walk']:
      (R-1) [l2_claim] — the per-site classification, unchanged;
      (R-2) [walk_seg_data] — per certified state, three items: the
            EMISSION (progress-backed by §1–§3), (W-1) [wpol] (the
            read/register policy), (O-F) [cpolp] (the RMW block). *)

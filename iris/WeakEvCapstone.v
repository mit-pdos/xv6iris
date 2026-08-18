(** * WeakEvCapstone.v — THE ONE-MACHINE CAPSTONE (B3.2 + B4)

    Worklist: [claude-notes/projects/weak-memory-soundness.md] (Phase B,
    items B3.2 and B4).  Design: the event-granular language
    ([claude-notes/design/weak-memory-event-granular.md]) plus M5
    ([claude-notes/design/weak-memory-m5.md]).

    ------------------------------------------------------------------------
    ** WHAT THIS FILE CLOSES **

    The soundness chain of the worklist, with no seam left in it:

      (1) event-language adequacy      [WeakEvAdequacy.weak_ev_adequacy_phi]
      (2) φ ⟹ [epf_violation_free_hart]  [WeakEvAdequacy.weak_ev_pf_violation_free]
      (3) THE INSTANCE (this file, §§1–5): the event language's own
          promise-free machine [WeakEvPf.epf_step] IS
          [WeakPromiseBridge.wp_pf_step pstep_ev pcls_ev] at
          [P := pexv6], [D := dev_state], through the projection
          [WeakEvPf.ecfg_of] — in BOTH directions, for EVERY arm
      (4) Layer 1                       [WeakRobustMain.robust_main]

    and (§7) their composition [xv6_ev_weak_robust].  Compare the archived
    instruction-atomic route ([WeakComposeLang.xv6_weak_robust_lifted]):
    NONE of [rv64d_axiom_shapes], [rv64d_live_residue], [img_total],
    [xv6_cone_premises], [cone_liftable] survives here.  What is left is
    the WP package, the four fresh-era facts about σ0, and the genuine
    Layer-1 robustness package [main_premises] served at canonical
    bundles.

    ------------------------------------------------------------------------
    ** THE ONE ASYMMETRY, RECORDED (§3) **

    ⇒ (a Layer-1 pf step of the projected configuration is an [epf_step])
    holds AT THE SAME LABEL, for every arm.  ⇐ holds at the RUN level
    ([epf_run ⊆ wp_pf_run] under [ecfg_of]) but NOT per-label, and that is
    a property of [WeakEvPf.epf_step], not of the instance: its label is
    only constrained by [WeakEvPf.elabel_ok], which under-determines it.
    The witness is [fence.i]: [WeakEvLang]'s barrier arm re-inserts the
    hart's [wstate] unchanged, so [elabel_ok σ c LSilent σ'] holds there —
    while the program half [pstep_node] emits the inert
    [LFence false false false false] and nothing else (deviation (D2) of
    [WeakEvInst]).  Since every consumer of [epf_step] quantifies the
    label existentially ([epf_run], [epf_violation_free_hart],
    [epf_step_erased]), the run-level statement is the exact one, and
    nothing needs the per-label form.

    ------------------------------------------------------------------------
    ** THE LAYOUT **

      §0  the UNIFORM shape of a [wp_pf_step] (generic in [P]/[D]): its
          side condition, its log effect and its view effect as FUNCTIONS
          of the label — which is exactly [WeakEvInst]'s memory half
      §1  the agent layout: locating an agent, and rebuilding [eags]
      §2  ⇒ : every pf step of [ecfg_of P σ] is an [epf_step] (all arms)
      §3  ⇐ : [epf_run] ⊆ [wp_pf_run] under [ecfg_of]
      §4  the initial configuration
      §5  the Layer-1 side conditions of the instance, and the transport
          of violation-freedom
      §6  the retag plumbing this capstone needs
      §7  THE CAPSTONE *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
From iris.program_logic Require Import language weakestpre lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
(* required BEFORE [WeakInterpProj]: see [WeakEvLang]'s note on [wbytes] *)
Require Import VirtioProg.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakRobust.
Require Import WeakRobustTrace.
Require Import WeakRobustSim.
Require Import WeakRobustMain.
Require Import WeakRetag.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvAdequacy.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakEvAdequacy.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. THE UNIFORM SHAPE OF A [wp_pf_step]

    [WeakPromiseBridge.wp_pf_step] has six arms, but they differ only in
    THREE label-indexed slots: a side condition, a log effect and a view
    effect.  Naming those three collapses the instance proofs from
    "six arms × two agent kinds" to "one shape × two agent kinds" — and
    the three functions are, at the projected configuration, LITERALLY
    [WeakEvInst]'s [elab_ok] / [elab_log] / [elab_ws] (§2). *)

Section pf_uniform.
  Context {P D : Type}.
  Context (pstep : P -> D -> wlabel -> P -> D -> Prop).
  Context (pcls : P -> wlabel -> wstate -> wm_class).

  Definition pf_ok (cfg : wpcfg P D) (i : agent) (ag : wpagent P)
      (l : wlabel) : Prop :=
    match l with
    | LSilent => True
    | LDev => True
    | LFence _ _ _ _ => True
    (* D2: the operand lists are PINNED to [[]] — this is the shape
       [WeakEvInst.elab_ok] has, and [pf_ok_hart] must stay a conversion.
       The pin is discharged from [WeakEvInst.pstep_ev_depfree] wherever
       [wp_pf_step_inv] is used. *)
    | LLoad aq lat base tvs asrc =>
        asrc = [] /\
        read_ok (pc_img cfg) (pc_log cfg) (pa_ws ag) aq lat base tvs
    | LStore _ _ data asrc vsrc => asrc = [] /\ vsrc = [] /\ data <> []
    | LRmw aq rl base tvs data asrc vsrc =>
        asrc = [] /\ vsrc = [] /\
        data <> [] /\ length tvs = length data /\
        read_ok (pc_img cfg) (pc_log cfg) (pa_ws ag) aq false base tvs /\
        excl_ok (pc_log cfg) i base tvs (S (length (pc_log cfg)))
    | LRegW _ _ | LCtrl _ | LInstr => True
    end.

  Definition pf_log (cfg : wpcfg P D) (i : agent) (ag : wpagent P)
      (l : wlabel) : list wmsg :=
    match l with
    | LStore rl base data asrc vsrc =>
        pc_log cfg
        ++ [WMsg base data (Some i)
              (pcls (pa_st ag) (LStore rl base data asrc vsrc) (pa_ws ag))]
    | LRmw aq rl base tvs data asrc vsrc =>
        pc_log cfg
        ++ [WMsg base data (Some i)
              (pcls (pa_st ag) (LRmw aq rl base tvs data asrc vsrc)
                 (pa_ws ag))]
    | _ => pc_log cfg
    end.

  Definition pf_ws (cfg : wpcfg P D) (ag : wpagent P) (l : wlabel) : wstate :=
    match l with
    | LLoad aq lat base tvs _ => load_post_run (pa_ws ag) aq base tvs.*1
    | LStore rl base data _ _ =>
        store_post_run (pa_ws ag) rl base (length data)
          (S (length (pc_log cfg)))
    | LRmw aq rl base tvs data _ _ =>
        store_post_run (load_post_run (pa_ws ag) aq base tvs.*1) rl base
          (length data) (S (length (pc_log cfg)))
    | LFence pr pw sr sw => fence_post (pa_ws ag) pr pw sr sw
    | LRegW rd srcs => regw_post (pa_ws ag) rd (srcs_view (pa_ws ag) srcs)
    | LCtrl srcs => ctrl_post (pa_ws ag) (srcs_view (pa_ws ag) srcs)
    | LInstr => instr_post (pa_ws ag)
    | _ => pa_ws ag
    end.

  Definition pf_cfg (cfg : wpcfg P D) (i : agent) (ag : wpagent P)
      (l : wlabel) (st' : P) (d' : D) : wpcfg P D :=
    WPCfg (pc_img cfg) (pf_log cfg i ag l) d'
          (<[i := WPAgent st' (pf_ws cfg ag l) (pa_prom ag)]> (pc_ags cfg)).

  Lemma wp_pf_step_intro i l cfg ag st' d' :
    pc_ags cfg !! i = Some ag ->
    pstep (pa_st ag) (pc_dev cfg) l st' d' ->
    pf_ok cfg i ag l ->
    wp_pf_step pstep pcls i l cfg (pf_cfg cfg i ag l st' d').
  Proof.
    intros Hlk Hps Hok. rewrite /pf_cfg.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc|].
    - by apply (PFSilent pstep pcls i cfg ag st' d').
    - destruct Hok as (-> & Hrd). rewrite /pf_ws /pf_log.
      rewrite -(load_post_run_d_0 (pa_ws ag) aq base (tvs.*1)).
      by apply (PFLoad pstep pcls i cfg ag aq lat base tvs [] st' d').
    - destruct Hok as (-> & -> & Hne). rewrite /pf_ws /pf_log.
      rewrite -(store_post_run_d_0 (pa_ws ag) rl base (length data)
                  (S (length (pc_log cfg)))).
      by apply (PFStore pstep pcls i cfg ag rl base data [] [] _ st' d').
    - destruct Hok as (-> & -> & Hne & Hlen & Hrd & Hex).
      rewrite /pf_ws /pf_log.
      rewrite -(load_post_run_d_0 (pa_ws ag) aq base (tvs.*1))
              -(store_post_run_d_0
                  (load_post_run_d (pa_ws ag) aq 0%nat base (tvs.*1))
                  rl base (length data) (S (length (pc_log cfg)))).
      by apply (PFRmw pstep pcls i cfg ag aq rl base tvs data [] [] _
                  st' d').
    - by apply (PFFence pstep pcls i cfg ag pr pw sr sw st' d').
    - by apply (PFDev pstep pcls i cfg ag st' d').
    - by apply (PFRegW pstep pcls i cfg ag rdw wsrc st' d').
    - by apply (PFCtrl pstep pcls i cfg ag csrc st' d').
    - by apply (PFInstr pstep pcls i cfg ag st' d').
  Qed.

  (** THE DEPENDENCY-FREE PREMISE (D2).  [pf_ok] pins the operand lists,
      so the inversion needs to know the step emitted none — which is
      [WeakEvInst.pstep_ev_depfree] at the instance. *)
  Lemma wp_pf_step_inv i l cfg c' :
    lb_depfree l ->
    wp_pf_step pstep pcls i l cfg c' ->
    exists ag st' d', pc_ags cfg !! i = Some ag /\
      pstep (pa_st ag) (pc_dev cfg) l st' d' /\
      pf_ok cfg i ag l /\
      c' = pf_cfg cfg i ag l st' d'.
  Proof.
    intros Hdf.
    destruct 1 as [cfg0 ag st' d' Hlk Hps
                  |cfg0 ag aq lat base tvs asrc st' d' Hlk Hps Hrd
                  |cfg0 ag rl base data asrc vsrc k st' d' Hlk Hps Hne Hk
                  |cfg0 ag aq rl base tvs data asrc vsrc k st' d'
                        Hlk Hps Hne Hlen Hrd Hex Hk
                  |cfg0 ag pr pw sr sw st' d' Hlk Hps
                  |cfg0 ag st' d' Hlk Hps
                  |cfg0 ag rdw wsrc st' d' Hlk Hps|cfg0 ag csrc st' d' Hlk Hps
                  |cfg0 ag st' d' Hlk Hps];
      simpl in Hdf;
      repeat (match goal with H : _ /\ _ |- _ => destruct H end); subst;
      do 3 eexists; split_and!; try done;
      rewrite /pf_cfg /pf_log /pf_ws //=;
      rewrite ?srcs_view_nil ?load_post_run_d_0 ?store_post_run_d_0 //;
      by subst k.
  Qed.
End pf_uniform.

(* ====================================================================== *)
(** ** 1. The agent layout

    [WeakEvPf.eags] lays the agents out as [NCPU] harts followed by the
    disk, so an index either names a [CPU] or is [n_disk]; and an update
    of one agent is an [insert] into that list. *)

Lemma eags_lookup_inv P σ i ag :
  eags P σ !! i = Some ag ->
  (exists c : CPU, i = fin_to_nat c /\ ag = ehart_ag P σ c)
  \/ (i = n_disk /\ ag = edisk_ag P).
Proof.
  intros Hi. rewrite /eags in Hi.
  destruct (decide (i < NCPU)%nat) as [Hlt|Hge].
  - rewrite lookup_app_l in Hi;
      [|by rewrite length_fmap enum_CPU_length].
    rewrite list_lookup_fmap in Hi.
    destruct (enum CPU !! i) as [c|] eqn:Hc; simplify_eq/=.
    left. exists c. split; [|reflexivity].
    symmetry. exact (fin_enum_lookup_nat NCPU i c Hc).
  - rewrite lookup_app_r in Hi;
      [|rewrite length_fmap enum_CPU_length; lia].
    rewrite length_fmap enum_CPU_length in Hi.
    destruct (i - NCPU)%nat as [|k] eqn:Hk; [|by rewrite lookup_cons in Hi].
    rewrite lookup_cons in Hi. simplify_eq/=.
    right. split; [rewrite /n_disk; lia|reflexivity].
Qed.

Lemma eags_upd_hart (P P' : epool) (σ σ' : wgstate) (c : CPU) :
  (forall c', c' <> c -> ehart_ag P' σ' c' = ehart_ag P σ c') ->
  edisk_ag P' = edisk_ag P ->
  eags P' σ' = <[fin_to_nat c := ehart_ag P' σ' c]> (eags P σ).
Proof.
  intros Hne Hd. rewrite /eags insert_app_l;
    [|rewrite length_fmap enum_CPU_length; apply fin_to_nat_lt].
  f_equal; [|by rewrite Hd].
  apply list_eq. intros j. rewrite list_lookup_fmap.
  destruct (decide (j = fin_to_nat c)) as [->|Hj].
  - rewrite list_lookup_insert;
      [|rewrite length_fmap enum_CPU_length; apply fin_to_nat_lt].
    by rewrite enum_CPU_lookup.
  - rewrite list_lookup_insert_ne; [|done]. rewrite list_lookup_fmap.
    destruct (enum CPU !! j) as [cj|] eqn:Hcj; [|reflexivity].
    simpl. f_equal. apply Hne. intros ->. apply Hj.
    symmetry. exact (fin_enum_lookup_nat NCPU j c Hcj).
Qed.

Lemma eags_upd_disk (P P' : epool) (σ σ' : wgstate) :
  (forall c, ehart_ag P' σ' c = ehart_ag P σ c) ->
  eags P' σ' = <[n_disk := edisk_ag P']> (eags P σ).
Proof.
  intros Hh. rewrite /eags /n_disk insert_app_r_alt;
    [|rewrite length_fmap enum_CPU_length; lia].
  rewrite length_fmap enum_CPU_length Nat.sub_diag.
  f_equal. apply list_eq. intros j. rewrite !list_lookup_fmap.
  destruct (enum CPU !! j) as [cj|]; [|reflexivity]. simpl. by rewrite Hh.
Qed.

Lemma eags_eq (P P' : epool) (σ σ' : wgstate) :
  (forall c, ehart_ag P' σ' c = ehart_ag P σ c) ->
  edisk_ag P' = edisk_ag P -> eags P' σ' = eags P σ.
Proof.
  intros Hh Hd. rewrite /eags. f_equal; [|by rewrite Hd].
  apply list_eq. intros j. rewrite !list_lookup_fmap.
  destruct (enum CPU !! j) as [cj|]; [|reflexivity]. simpl. by rewrite Hh.
Qed.

(** Pointwise readings of [WeakEvInst]'s two σ-transformer components. *)
Lemma eregs_apply_at σ c ors :
  eregs_apply σ c ors c = default (wgregs σ c) ors.
Proof. destruct ors; [apply greg_insert_eq|reflexivity]. Qed.

Lemma eregs_apply_ne σ c ors c' :
  c' <> c -> eregs_apply σ c ors c' = wgregs σ c'.
Proof. intros Hne. destruct ors; [by apply greg_insert_ne|reflexivity]. Qed.

Lemma elab_ws_ne σ c l c' :
  c' <> c -> elab_ws σ c l c' = wgws σ c'.
Proof. intros Hne. destruct l; rewrite //= gws_insert_ne //. Qed.

(** ... and the D3 twin, for the announced instruction bits. *)
Lemma eib_apply_at σ c oib :
  eib_apply σ c oib c = default (wgib σ c) oib.
Proof. destruct oib; [apply gib_insert_eq|reflexivity]. Qed.

Lemma eib_apply_ne σ c oib c' :
  c' <> c -> eib_apply σ c oib c' = wgib σ c'.
Proof. intros Hne. destruct oib; [by apply gib_insert_ne|reflexivity]. Qed.

(** The two projections of §0's slots, at the two agent kinds.  The side
    condition and the log effect are LITERALLY [WeakEvInst]'s (that is what
    the factorization bought); the view effect differs only by the pointwise
    insert [WeakLang.gws_insert]. *)

Lemma pf_ok_hart P σ (c : CPU) l :
  pf_ok (ecfg_of P σ) (fin_to_nat c) (ehart_ag P σ c) l = elab_ok σ c l.
Proof. by destruct l. Qed.

Lemma pf_log_hart P σ (c : CPU) l :
  pf_log pcls_ev (ecfg_of P σ) (fin_to_nat c) (ehart_ag P σ c) l
  = elab_log σ c l (pcls_ev (pa_st (ehart_ag P σ c)) l (wgws σ c)).
Proof. by destruct l. Qed.

Lemma pf_ws_hart P σ (c : CPU) l :
  pf_ws (ecfg_of P σ) (ehart_ag P σ c) l = elab_ws σ c l c.
Proof. destruct l; rewrite //= gws_insert_eq //. Qed.

Lemma pf_ok_disk P σ l :
  lb_depfree l ->
  (forall aq rl base tvs data, l <> LRmw aq rl base tvs data [] []) ->
  pf_ok (ecfg_of P σ) n_disk (edisk_ag P) l -> edlab_ok σ (ep_dws P) l.
Proof.
  intros Hdf Hnr. destruct l; simpl in Hdf; try done.
  destruct Hdf as (-> & ->). by destruct (Hnr _ _ _ _ _ eq_refl).
Qed.

Lemma pf_log_disk P σ l :
  pf_log pcls_ev (ecfg_of P σ) n_disk (edisk_ag P) l
  = edlab_log σ l (pcls_ev (PDisk (ep_dp P)) l (ep_dws P)).
Proof. by destruct l. Qed.

Lemma pf_ws_disk P σ l :
  pf_ws (ecfg_of P σ) (edisk_ag P) l = edlab_ws σ (ep_dws P) l.
Proof. by destruct l. Qed.

(** ... and the four shapes of a projected configuration after one step. *)
Lemma ecfg_of_hart_upd P σ (c : CPU) (h' : ehst) l k ors oib d' :
  ecfg_of (ep_hset P c h') (elab_apply σ c l k ors oib d')
  = WPCfg (img_z (wgimg σ)) (elab_log σ c l k) d'
      (<[fin_to_nat c
         := WPAgent (PHart c (ehart_m h') (default (wgregs σ c) ors)
                       (ehart_fn h') (default (wgib σ c) oib))
              (elab_ws σ c l c) ∅]> (eags P σ)).
Proof.
  have Hne : forall c', c' <> c ->
    ehart_ag (ep_hset P c h') (elab_apply σ c l k ors oib d') c'
    = ehart_ag P σ c'.
  { intros c' Hc'. rewrite /ehart_ag /ep_hset /=.
    destruct (decide (c' = c)) as [->|_]; [done|].
    by rewrite /elab_apply /= (eregs_apply_ne σ c ors c' Hc')
               (elab_ws_ne σ c l c' Hc') (eib_apply_ne σ c oib c' Hc'). }
  have Hag : ehart_ag (ep_hset P c h') (elab_apply σ c l k ors oib d') c
             = WPAgent (PHart c (ehart_m h') (default (wgregs σ c) ors)
                          (ehart_fn h') (default (wgib σ c) oib))
                 (elab_ws σ c l c) ∅.
  { rewrite /ehart_ag /ep_hset /=.
    destruct (decide (c = c)) as [_|]; [|done].
    by rewrite /elab_apply /= eregs_apply_at eib_apply_at. }
  have Heq := eags_upd_hart P (ep_hset P c h') σ
                (elab_apply σ c l k ors oib d') c Hne eq_refl.
  by rewrite /ecfg_of Heq Hag.
Qed.

Lemma ecfg_of_disk_upd P σ dp' dws' l k d' :
  ecfg_of (ep_dset P dp' dws') (edlab_apply σ l k d')
  = WPCfg (img_z (wgimg σ)) (edlab_log σ l k) d'
      (<[n_disk := WPAgent (PDisk dp') dws' ∅]> (eags P σ)).
Proof.
  have Heq := eags_upd_disk P (ep_dset P dp' dws') σ
                (edlab_apply σ l k d') (fun c => eq_refl).
  by rewrite /ecfg_of Heq.
Qed.

Lemma ecfg_of_dev P σ d' :
  ecfg_of P (ewg_dev σ d') = WPCfg (img_z (wgimg σ)) (wglog σ) d' (eags P σ).
Proof.
  by rewrite /ecfg_of (eags_eq P P σ (ewg_dev σ d')
                         (fun c => eq_refl) eq_refl).
Qed.

Lemma ecfg_of_reg P σ (c : CPU) rs' :
  ecfg_of P (ewg_reg σ c rs')
  = WPCfg (img_z (wgimg σ)) (wglog σ) (wgdev σ)
      (<[fin_to_nat c
         := WPAgent (PHart c (ehart_m (ep_h P c)) rs' (ehart_fn (ep_h P c))
                       (wgib σ c))
              (wgws σ c) ∅]> (eags P σ)).
Proof.
  have Hne : forall c', c' <> c ->
    ehart_ag P (ewg_reg σ c rs') c' = ehart_ag P σ c'.
  { intros c' Hc'. rewrite /ehart_ag /ewg_reg /=. by rewrite greg_insert_ne. }
  have Hag : ehart_ag P (ewg_reg σ c rs') c
             = WPAgent (PHart c (ehart_m (ep_h P c)) rs' (ehart_fn (ep_h P c))
                          (wgib σ c))
                 (wgws σ c) ∅.
  { rewrite /ehart_ag /ewg_reg /=. by rewrite greg_insert_eq. }
  have Heq := eags_upd_hart P P σ (ewg_reg σ c rs') c Hne eq_refl.
  by rewrite /ecfg_of Heq Hag.
Qed.

(* ====================================================================== *)
(** ** 2. ⇒ : EVERY LAYER-1 PF STEP OF THE PROJECTION IS AN [epf_step]

    The direction the capstone needs — it is what turns
    [WeakEvAdequacy.epf_violation_free_hart] into Layer 1's
    [pf_violation_free_hart].  Every arm, no exception: since M5 the disk
    reads through its label like everybody else. *)

Lemma elab_apply_elabel_ok σ c l k ors oib d' :
  elab_ok σ c l ->
  (forall aq base tvs, l <> LLoad aq true base tvs []) ->
  (* D2: the three dependency-only labels have no [elabel_ok] image, so the
     bracket needs to know the step emitted none. *)
  lb_depfree l ->
  elabel_ok σ c l (elab_apply σ c l k ors oib d').
Proof.
  intros Hok Hlat Hdf.
  destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc|];
    rewrite /elabel_ok /elab_apply /=; simpl in Hdf.
  - by split.
  - destruct Hok as (-> & Hrd).
    destruct lat; [by destruct (Hlat aq base tvs eq_refl)|].
    split_and!;
      [reflexivity|reflexivity|exact Hrd|reflexivity|by rewrite gws_insert_eq].
  - destruct Hok as (-> & -> & Hne).
    split_and!;
      [reflexivity|reflexivity|by eexists|exact Hne|by rewrite gws_insert_eq].
  - destruct Hok as (-> & -> & Hne & Hlen & Hrd & Hex).
    split_and!; [reflexivity|reflexivity|exact Hne|exact Hlen|exact Hrd
                |exact Hex|by eexists|by rewrite gws_insert_eq].
  - by split; [|rewrite gws_insert_eq].
  - by split.
  - by destruct Hdf.
  - by destruct Hdf.
  - by destruct Hdf.
Qed.

(** The hart's program half assembles into an [epf_step]: at a boundary
    ([ep_h P c = None], i.e. the program state's monad is [Ret tt]) that is
    [EPFBoundary], otherwise [EPFCycle]. *)
Lemma epf_step_of_hart P σ (c : CPU) l m' ors fn' d' oib :
  ethread_live σ (ep_gen P) ->
  pstep_node c (ehart_m (ep_h P c)) (wgregs σ c) (ehart_fn (ep_h P c))
    (wgib σ c) (wgdev σ) l m' ors fn' d' oib ->
  elab_ok σ c l ->
  epf_step (fin_to_nat c) l (P, σ)
    (ep_hset P c (Some (m', fn')),
     elab_apply σ c l
       (pcls_ev (pa_st (ehart_ag P σ c)) l (wgws σ c)) ors oib d').
Proof.
  intros Hlive Hps Hok.
  set k := pcls_ev (pa_st (ehart_ag P σ c)) l (wgws σ c).
  have Hlat : forall aq base tvs, l <> LLoad aq true base tvs [].
  { intros aq base tvs ->. by eapply pstep_node_lat_free. }
  have Hdf : lb_depfree l by eapply pstep_node_depfree.
  have Hlbl := elab_apply_elabel_ok σ c l k ors oib d' Hok Hlat Hdf.
  have Hcy : ecycle_step (ep_gen P) σ c (ehart_m (ep_h P c))
               (ehart_fn (ep_h P c)) (Sail (ep_gen P) c m' fn')
               (elab_apply σ c l k ors oib d').
  { apply ecycle_step_factor. by exists l, m', ors, fn', d', oib. }
  destruct (ep_h P c) as [[m fn]|] eqn:Hh.
  - by apply (EPFCycle c l P σ m fn (Some (m', fn'))).
  - (* the boundary: the monad is [Ret tt], the program half emits [LSilent]
       and nothing else, and (D3) it CLEARS the announced bits *)
    rewrite /pstep_node /ehart_m /ehart_fn /pnode_step /= in Hps.
    destruct Hps as (tick & -> & -> & -> & -> & -> & ->).
    rewrite (elab_apply_ib σ c k None).
    by apply (EPFBoundary c P σ tick).
Qed.

Lemma epf_step_of_disk P σ l dp' d' :
  ethread_live σ (ep_gen P) ->
  pdisk_prog (ep_dp P) (wgdev σ) l dp' d' ->
  edlab_ok σ (ep_dws P) l ->
  epf_step n_disk l (P, σ)
    (ep_dset P dp' (edlab_ws σ (ep_dws P) l),
     edlab_apply σ l (pcls_ev (PDisk (ep_dp P)) l (ep_dws P)) d').
Proof.
  intros Hlive Hps Hok.
  set k := pcls_ev (PDisk (ep_dp P)) l (ep_dws P).
  have Hst : edisk_step (ep_gen P) (ep_dp P) (ep_dws P) σ
               (EDisk (ep_gen P) dp' (edlab_ws σ (ep_dws P) l))
               (edlab_apply σ l k d').
  { apply edisk_step_factor. by exists l, dp', d'. }
  have Hlbl : edlabel_ok P σ l (edlab_ws σ (ep_dws P) l)
                (edlab_apply σ l k d').
  { have Hdf : lb_depfree l by eapply pstep_disk_depfree; left; exact Hps.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc|];
      simpl in Hdf, Hok.
    - by split.
    - (* the disk's read is lat-free by construction *)
      destruct Hok as (-> & Hrd).
      destruct lat.
      { exfalso. by eapply (pdisk_prog_lat_free (ep_dp P) (wgdev σ)). }
      by split_and!.
    - destruct Hok as (-> & -> & Hne).
      split_and!; [reflexivity|reflexivity|by eexists|exact Hne|reflexivity].
    - by destruct Hdf.
    - by split.
    - by split.
    - by destruct Hdf.
    - by destruct Hdf.
    - by destruct Hdf. }
  by apply (EPFDisk l P σ dp' (edlab_ws σ (ep_dws P) l)).
Qed.

Theorem wp_pf_step_epf_step i l P σ c' :
  ethread_live σ (ep_gen P) ->
  wp_pf_step pstep_ev pcls_ev i l (ecfg_of P σ) c' ->
  exists P' σ', epf_step i l (P, σ) (P', σ') /\ ecfg_of P' σ' = c'.
Proof.
  intros Hlive Hstep.
  have Hdf : lb_depfree l.
  { destruct Hstep; by eapply pstep_ev_depfree. }
  apply (wp_pf_step_inv _ _ i l _ _ Hdf) in Hstep
    as (ag & st' & d' & Hlk & Hps & Hok & ->).
  rewrite /ecfg_of /= in Hlk.
  destruct (eags_lookup_inv P σ i ag Hlk) as [(c & -> & ->)|(-> & ->)].
  - (* A HART *)
    rewrite pf_ok_hart in Hok. rewrite /= in Hps.
    destruct st' as [cpu' m' rs' fn' ib'|dp']; [|by destruct Hps].
    destruct Hps as (-> & ors & oib & -> & -> & [Hnode|Hplic]).
    + (* the cycle event *)
      eexists _, _. split; [by apply epf_step_of_hart|].
      rewrite ecfg_of_hart_upd /pf_cfg /=.
      by rewrite ?pf_log_hart ?pf_ws_hart.
    + (* the PLIC wire *)
      destruct Hplic as (-> & -> & -> & -> & -> & ->).
      eexists P, _. split; [by apply (EPFPlic c P σ)|].
      rewrite ecfg_of_reg /pf_cfg /=. by rewrite ?pf_ws_hart.
  - (* THE DISK AGENT *)
    rewrite /= in Hps.
    destruct st' as [cpu' m' rs' fn' ib'|dp']; [by destruct Hps|].
    have Hnr : forall aq rl base tvs data,
                 l <> LRmw aq rl base tvs data [] [].
    { intros aq rl base tvs data ->. by eapply pstep_disk_no_rmw. }
    have Hok' := pf_ok_disk P σ l Hdf Hnr Hok.
    destruct Hps as [Hprog|(-> & -> & Hu)].
    + eexists _, _. split; [by apply epf_step_of_disk|].
      rewrite ecfg_of_disk_upd /pf_cfg /=.
      by rewrite ?pf_log_disk ?pf_ws_disk.
    + eexists P, (ewg_dev σ d'). split.
      { apply (EPFUart P σ (ewg_dev σ d')); [exact Hlive|by exists d']. }
      have Hid : <[n_disk := WPAgent (PDisk (ep_dp P))
                     (pf_ws (ecfg_of P σ) (edisk_ag P) LDev)
                     (pa_prom (edisk_ag P))]> (eags P σ) = eags P σ
        := list_insert_id (eags P σ) n_disk (edisk_ag P) (eags_disk P σ).
      by rewrite ecfg_of_dev /pf_cfg Hid.
Qed.

(* ====================================================================== *)
(** ** 3. ⇐ : [epf_run] IS A [wp_pf_run] OF THE PROJECTION

    Stated at the RUN level, which is the exact statement — see the header:
    an [epf_step]'s label is only constrained by [WeakEvPf.elabel_ok] and is
    therefore under-determined ([fence.i] admits [LSilent] there while the
    program half emits the inert [LFence false false false false]), so the
    per-label form is false and the existential one is what holds.  Every
    consumer quantifies the label existentially anyway. *)

Lemma ecfg_of_hset P σ (c : CPU) (h' : ehst) :
  ecfg_of (ep_hset P c h') σ
  = WPCfg (img_z (wgimg σ)) (wglog σ) (wgdev σ)
      (<[fin_to_nat c
         := WPAgent (PHart c (ehart_m h') (wgregs σ c) (ehart_fn h')
                       (wgib σ c))
              (wgws σ c) ∅]> (eags P σ)).
Proof.
  have Hne : forall c', c' <> c ->
    ehart_ag (ep_hset P c h') σ c' = ehart_ag P σ c'.
  { intros c' Hc'. rewrite /ehart_ag /ep_hset /=.
    by destruct (decide (c' = c)) as [->|_]. }
  have Hag : ehart_ag (ep_hset P c h') σ c
             = WPAgent (PHart c (ehart_m h') (wgregs σ c) (ehart_fn h')
                          (wgib σ c))
                 (wgws σ c) ∅.
  { rewrite /ehart_ag /ep_hset /=. by destruct (decide (c = c)) as [_|]. }
  have Heq := eags_upd_hart P (ep_hset P c h') σ σ c Hne eq_refl.
  by rewrite /ecfg_of Heq Hag.
Qed.

Lemma edlab_ok_pf_ok P σ l :
  edlab_ok σ (ep_dws P) l -> pf_ok (ecfg_of P σ) n_disk (edisk_ag P) l.
Proof. by destruct l. Qed.

Theorem epf_step_wp_pf_step i l ρ ρ' :
  epf_step i l ρ ρ' ->
  exists l', wp_pf_step pstep_ev pcls_ev i l'
               (ecfg_of ρ.1 ρ.2) (ecfg_of ρ'.1 ρ'.2).
Proof.
  destruct 1 as [c P σ tick Hlive Hh
                |c l0 P σ m0 fn0 h' σ' Hlive Hh Hcy Hl
                |l0 P σ dp' dws' σ' Hlive Hst Hl
                |P σ σ' Hlive Hu
                |c P σ Hlive]; simpl.
  - (* the boundary — D3: it CLEARS the announced bits, which is the
       [elab_apply] shape [elab_apply_ib] names *)
    exists LSilent.
    have Hstep := wp_pf_step_intro pstep_ev pcls_ev (fin_to_nat c) LSilent
                    (ecfg_of P σ) (ehart_ag P σ c)
                    (PHart c (riscv_step tick) (wgregs σ c) None None)
                    (wgdev σ) (eags_hart P σ c).
    rewrite -(elab_apply_ib σ c
                (pcls_ev (pa_st (ehart_ag P σ c)) LSilent (wgws σ c)) None)
            ecfg_of_hart_upd.
    rewrite /pf_cfg /pf_log /pf_ws /= in Hstep.
    apply Hstep; [|exact I].
    rewrite /pstep_ev /= /ehart_ag /= Hh /=.
    split; [reflexivity|]. exists None, (Some None). split_and!;
      [reflexivity|reflexivity|].
    left. rewrite /pstep_node /pnode_step /=. by exists tick.
  - (* one cycle event *)
    apply ecycle_step_factor in Hcy
      as (l1 & m1 & ors & fn1 & d1 & oib & He & Hps & Hok & ->).
    rewrite (ehexp_sail (ep_gen P) c h') in He. simplify_eq.
    exists l1.
    have Hst0 : pa_st (ehart_ag P σ c) = PHart c m0 (wgregs σ c) fn0 (wgib σ c).
    { by rewrite /ehart_ag /= Hh. }
    have Hstep := wp_pf_step_intro pstep_ev pcls_ev (fin_to_nat c) l1
                    (ecfg_of P σ) (ehart_ag P σ c)
                    (PHart c (ehart_m h') (default (wgregs σ c) ors)
                       (ehart_fn h') (default (wgib σ c) oib)) d1
                    (eags_hart P σ c).
    rewrite ecfg_of_hart_upd -Hst0.
    rewrite /pf_cfg pf_log_hart pf_ws_hart in Hstep.
    apply Hstep; [|by rewrite pf_ok_hart].
    rewrite /pstep_ev Hst0 /=.
    split; [reflexivity|]. exists ors, oib. split_and!;
      [reflexivity|reflexivity|]. by left.
  - (* one disk event *)
    apply edisk_step_factor in Hst
      as (l1 & dp1 & d1 & He & Hps & Hok & ->). simplify_eq.
    exists l1.
    have Hstep := wp_pf_step_intro pstep_ev pcls_ev n_disk l1
                    (ecfg_of P σ) (edisk_ag P) (PDisk dp1) d1
                    (eags_disk P σ).
    rewrite ecfg_of_disk_upd.
    rewrite /pf_cfg pf_log_disk pf_ws_disk in Hstep.
    apply Hstep; [|by apply edlab_ok_pf_ok].
    rewrite /pstep_ev /= /edisk_ag /=. by left.
  - (* the UART thread *)
    exists LDev. destruct Hu as (d1 & Hu & ->).
    have Hstep := wp_pf_step_intro pstep_ev pcls_ev n_disk LDev
                    (ecfg_of P σ) (edisk_ag P) (PDisk (ep_dp P)) d1
                    (eags_disk P σ).
    rewrite ecfg_of_dev.
    rewrite /pf_cfg /pf_log /pf_ws /= in Hstep.
    rewrite -(list_insert_id (eags P σ) n_disk (edisk_ag P) (eags_disk P σ)).
    apply Hstep; [|exact I].
    rewrite /pstep_ev /= /edisk_ag /=. by right.
  - (* the PLIC wire *)
    exists LDev.
    have Hstep := wp_pf_step_intro pstep_ev pcls_ev (fin_to_nat c) LDev
                    (ecfg_of P σ) (ehart_ag P σ c)
                    (PHart c (ehart_m (ep_h P c))
                       (register_set sig_seip
                          (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c)))
                          (wgregs σ c)) (ehart_fn (ep_h P c)) (wgib σ c))
                    (wgdev σ) (eags_hart P σ c).
    rewrite ecfg_of_reg.
    rewrite /pf_cfg /pf_log /pf_ws /= in Hstep.
    apply Hstep; [|exact I].
    rewrite /pstep_ev /= /ehart_ag /=.
    split; [reflexivity|].
    eexists (Some _), None. split_and!; [reflexivity|reflexivity|].
    right. by rewrite /pstep_plic.
Qed.

Theorem epf_run_wp_pf_run ρ ρ' :
  epf_run ρ ρ' -> wp_pf_run pstep_ev pcls_ev (ecfg_of ρ.1 ρ.2) (ecfg_of ρ'.1 ρ'.2).
Proof.
  intros (i & l & Hs). destruct (epf_step_wp_pf_step i l ρ ρ' Hs) as (l' & H).
  by exists i, l'.
Qed.

Theorem epf_rtc_wp_pf_rtc ρ ρ' :
  rtc epf_run ρ ρ' ->
  rtc (wp_pf_run pstep_ev pcls_ev) (ecfg_of ρ.1 ρ.2) (ecfg_of ρ'.1 ρ'.2).
Proof.
  induction 1 as [|x y z Hxy _ IH]; [apply rtc_refl|].
  eapply rtc_l; [by apply epf_run_wp_pf_run|exact IH].
Qed.

(** ... and the run-level ⇒, which is what the transport of
    violation-freedom consumes. *)
Theorem wp_pf_rtc_epf_rtc P σ c' :
  ethread_live σ (ep_gen P) ->
  rtc (wp_pf_run pstep_ev pcls_ev) (ecfg_of P σ) c' ->
  exists P' σ', rtc epf_run (P, σ) (P', σ') /\ ecfg_of P' σ' = c'.
Proof.
  intros Hlive Hrun. remember (ecfg_of P σ) as x eqn:Hx.
  revert P σ Hlive Hx.
  induction Hrun as [x|x y z Hxy Hyz IH]; intros P σ Hlive ->.
  - exists P, σ. split; [apply rtc_refl|reflexivity].
  - destruct Hxy as (i & l & Hstep).
    destruct (wp_pf_step_epf_step i l P σ y Hlive Hstep)
      as (P1 & σ1 & Hs & <-).
    have Hlive1 : ethread_live σ1 (ep_gen P1).
    { destruct (epf_step_live (ep_gen P) i l (P, σ) (P1, σ1) Hlive
                  eq_refl Hs) as (H1 & H2). simpl in H1, H2. by rewrite H2. }
    destruct (IH P1 σ1 Hlive1 eq_refl) as (P' & σ' & Hr & <-).
    exists P', σ'. split; [|reflexivity]. eapply rtc_l; [by exists i, l|exact Hr].
Qed.

(* ====================================================================== *)
(** ** 4. The initial configuration

    The program vector of a fresh era: every hart at the monad's terminal
    value ([WeakEvLang.ELoop]'s program state) with the boot register file,
    and the disk with no residual device program. *)

(** D3: the hart's announced bits come off σ exactly as its register file
    does, so the fresh-era premise ledger of the capstone is UNCHANGED — no
    "[wgib σ0 c = None]" fact is needed anywhere. *)
Definition eps_init (σ : wgstate) : list pexv6 :=
  ((fun c : CPU => PHart c (Interface.Ret tt) (wgregs σ c) None (wgib σ c))
   <$> enum CPU)
  ++ [PDisk None].

Lemma map_is_fmap {A B} (f : A -> B) (l : list A) : map f l = f <$> l.
Proof. induction l as [|x l IH]; [reflexivity|]. simpl. by rewrite IH. Qed.

Theorem ecfg_of_init gen σ :
  wglog σ = [] -> (forall c : CPU, wgws σ c = ws_init) ->
  ecfg_of (ep_init gen) σ
  = wp_init (img_z (wgimg σ)) (wgdev σ) (eps_init σ).
Proof.
  intros Hlog Hws. rewrite /ecfg_of /wp_init Hlog. f_equal.
  rewrite /eags /eps_init map_is_fmap fmap_app. f_equal.
  all: try reflexivity.
  rewrite -list_fmap_compose. apply list_eq. intros j.
  rewrite !list_lookup_fmap.
  destruct (enum CPU !! j) as [c|]; [|reflexivity].
  simpl. by rewrite /ehart_ag /ep_init /= Hws.
Qed.

(* ====================================================================== *)
(** ** 5. THE LAYER-1 SIDE CONDITIONS OF THE INSTANCE, AND THE TRANSPORT *)

Lemma pstep_ev_lat_free_prog : lat_free_prog pstep_ev.
Proof.
  intros p d aq base tvs asrc p' d' Hs.
  have Hdf : lb_depfree (LLoad aq true base tvs asrc)
    by eapply pstep_ev_depfree.
  simpl in Hdf. rewrite Hdf in Hs. by eapply pstep_ev_lat_free.
Qed.

Lemma pstep_ev_ts_oblivious : ts_oblivious pstep_ev.
Proof.
  split.
  - intros p d aq lat base tvs tvs' asrc p' d' Hts Hs.
    have Hdf : lb_depfree (LLoad aq lat base tvs asrc)
      by eapply pstep_ev_depfree.
    simpl in Hdf. rewrite Hdf in Hs |- *. destruct lat.
    + by destruct (pstep_ev_lat_free p d aq base tvs p' d' Hs).
    + by eapply pstep_ev_ts_load.
  - intros p d aq rl base tvs tvs' data asrc vsrc p' d' Hts Hs.
    have Hdf : lb_depfree (LRmw aq rl base tvs data asrc vsrc)
      by eapply pstep_ev_depfree.
    destruct Hdf as (-> & ->).
    by eapply pstep_ev_ts_rmw.
Qed.

Lemma wm_class_of_relp ak ws ws' :
  w_relp ws = w_relp ws' -> wm_class_of ak ws = wm_class_of ak ws'.
Proof. intros H. by rewrite /wm_class_of H. Qed.

(** [pcls_obl]: the class function may look only at [w_relp] of the view and
    at the label's non-timestamp data.  [WeakInterp.wm_class_of] reads
    exactly [w_relp], and the [LRmw] class is the constant [WCexcl]. *)
Lemma pcls_ev_obl : pcls_obl pcls_ev.
Proof.
  split.
  - intros p rl base data ws ws' Hrel.
    destruct p as [cpu m rs fn ib|dp]; simpl.
    + rewrite /pnode_wclass. destruct m as [y|T oc k]; [reflexivity|].
      destruct oc; try reflexivity. by apply wm_class_of_relp.
    + rewrite /ddev_class. by apply wm_class_of_relp.
  - intros. reflexivity.
Qed.

(** THE TRANSPORT (B3.2, item 4): the event machine's violation-freedom IS
    Layer 1's, because every pf run of the projected initial configuration
    is the projection of an [epf_run]. *)
Theorem epf_pf_violation_free gen σ :
  ethread_live σ gen -> wglog σ = [] -> (forall c : CPU, wgws σ c = ws_init) ->
  epf_violation_free_hart (ep_init gen, σ) ->
  pf_violation_free_hart cls_of pub_of n_disk pstep_ev pcls_ev
    (img_z (wgimg σ)) (wgdev σ) (eps_init σ).
Proof.
  intros Hlive Hlog Hws Hvf cf Hrun.
  rewrite -(ecfg_of_init gen σ Hlog Hws) in Hrun.
  destruct (wp_pf_rtc_epf_rtc (ep_init gen) σ cf Hlive Hrun)
    as (P' & σ' & Hr & <-).
  exact (Hvf (P', σ') Hr).
Qed.

(* ====================================================================== *)
(** ** 6. The retag plumbing

    [WeakRetag]'s canonical retag moves only [wm_ak], so the FULFIL
    ACCOUNTING (the only component of [wp_behavior_fulfil_once_dev]'s output
    that [WeakRobustMain.robust_main_bundle] consumes and that
    [WeakRetag] does not already transport) survives it verbatim. *)

Definition efulfil_acct (mid : wpcfg pexv6 dev_state)
    (TS : ptraces pexv6 dev_state) : Prop :=
  forall p m i, pc_log mid !! p = Some m -> wm_tid m = Some i ->
    exists T, pt_trs TS !! i = Some T /\
      (exists k ev, at_evs T !! k = Some ev /\ ae_ts ev = Some (S p)) /\
      (forall k1 k2 ev1 ev2,
         at_evs T !! k1 = Some ev1 -> ae_ts ev1 = Some (S p) ->
         at_evs T !! k2 = Some ev2 -> ae_ts ev2 = Some (S p) -> k1 = k2).

Lemma efulfil_acct_retag f mid TS :
  efulfil_acct mid TS ->
  efulfil_acct (retag_cfg f mid) (retag_traces f TS).
Proof.
  intros Hacct p m' i Hp Htid. simpl in Hp.
  apply retag_log_lookup_inv in Hp as (m & Hm & ->).
  rewrite retag_msg_tid in Htid.
  exact (Hacct p m i Hm Htid).
Qed.

(* ====================================================================== *)
(** ** 7. THE CAPSTONE

    Event-language adequacy composed with the generalized Layer 1, with NO
    SEAM between them: the machine the Iris proof talks about IS the machine
    the robustness theorem talks about, projected by [WeakEvPf.ecfg_of].

    THE PREMISE LEDGER, in full:
      (a) four machine facts about a booted σ0 (fresh era, empty log, fresh
          views) — [Hgen]/[Hpow]/[Hgen0]/[Hlog]/[Hws];
      (b) THE WP PACKAGE: from the boot resources, every expression of the
          forked pool has an [EWP].  This is the ONLY Iris-side obligation,
          and it is [WeakEvAdequacy.weak_ev_pf_violation_free]'s verbatim;
      (c) the behavior under consideration;
      (d) THE ROBUSTNESS PACKAGE [WeakRobustMain.main_premises], served at
          CANONICAL traced bundles of any behavior — the genuine Layer-1
          content (the per-edge split, the bad-SCC residue, the E-edge
          obligation, the device-epoch residue and the byte classification),
          whose exhibit-level discharge is the premises worklist's phase 2.
    And that is all.  In particular NONE of the archived route's
    [rv64d_axiom_shapes], [rv64d_live_residue], [img_total],
    [xv6_cone_premises], [cone_liftable], [Hcq], [Hseip], [Hpriv],
    [sail_shaped], [sail_live] appears — nor [cls_canonical], which the
    retag discharges here.

    WHY THE PACKAGE IS QUANTIFIED OVER [cb] (a deviation from the sketch,
    and the archive's shape too): the capstone RETAGS the behavior before
    running Layer 1 on it, because [cls_canonical] is only obtainable for a
    bundle one already holds, so the bundle Layer 1 consumes belongs to
    [WeakRetag.retag_cfg _ c] rather than to [c].  Quantifying the supplier
    over every behavior of the same program is what lets it be applied
    there; in exchange the supplier MAY ASSUME the bundle is canonical. *)

Theorem xv6_ev_weak_robust Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU -> gset register)
    (c : wpcfg pexv6 dev_state)
    (Hgen : gen = 0%nat)
    (Hpow : wgpow σ0 = true) (Hgen0 : wggen σ0 = 0%nat)
    (Hlog : wglog σ0 = [])
    (Hws : forall cc : CPU, wgws σ0 cc = ws_init) :
  (* (b) THE WP PACKAGE *)
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D cc,
            reg_pointsto_at cc r (DfracOwn 1)
              (register_lookup r (wgregs σ0 cc))) ∗
       ([∗ map] a ↦ b ∈ wgimg σ0, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
       wlog_lb [] ∗
       uart_frag (wgdev σ0).(duart) ∗ plic_frag (wgdev σ0).(dplic) ∗
       virtio_frag (wgdev σ0).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
  (* (c) the behavior *)
  wp_behavior pstep_ev (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0) c ->
  (* (d) THE ROBUSTNESS PACKAGE, at canonical bundles *)
  (forall cb mid TS DS,
     wp_behavior pstep_ev (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0) cb ->
     rtc (wp_promise_step (P:=pexv6) (D:=dev_state))
       (wp_init (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)) mid ->
     ptraces_dev_of pstep_ev pdev_ev TS DS mid cb ->
     cls_canonical pcls_ev TS ->
     main_premises n_disk TS DS) ->
  exists cf,
    rtc (wp_pf_run pstep_ev pcls_ev)
      (wp_init (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)) cf /\
    prog_of cf = prog_of c /\ (forall a, mem_of cf a = mem_of c a) /\
    (** ...and the promise-free witness is a RUN OF THE EVENT LANGUAGE *)
    exists P' σ', rtc epf_run (ep_init gen, σ0) (P', σ') /\
                  ecfg_of P' σ' = cf.
Proof.
  intros Hwp Hbeh Hprem.
  have Hlive : ethread_live σ0 gen.
  { rewrite /ethread_live Hpow Hgen0 Hgen. by split. }
  (* (1)+(2): adequacy gives the event machine's violation-freedom *)
  have Hvf0 : epf_violation_free_hart (ep_init gen, σ0).
  { by apply (weak_ev_pf_violation_free Σ gen σ0 D). }
  (* (3): ...which IS Layer 1's, through the instance *)
  have Hvf : pf_violation_free_hart cls_of pub_of n_disk pstep_ev pcls_ev
               (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)
    := epf_pf_violation_free gen σ0 Hlive Hlog Hws Hvf0.
  (* THE TRACED DECOMPOSITION, and the canonical retag of it *)
  destruct (wp_behavior_fulfil_once_dev pstep_ev pdev_ev
              (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0) c
              pdev_ev_ok pstep_ev_lat_free_prog Hbeh)
    as (mid & TS & DS & Hprom & Hofd & Hnp & Hacct).
  set f := canon_f pcls_ev TS.
  have Hbeh' : wp_behavior pstep_ev (img_z (wgimg σ0)) (wgdev σ0)
                 (eps_init σ0) (retag_cfg f c)
    := wp_behavior_retag pstep_ev f _ _ _ _ Hbeh.
  have Hprom' : rtc (wp_promise_step (P:=pexv6) (D:=dev_state))
                  (wp_init (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0))
                  (retag_cfg f mid).
  { rewrite -(retag_wp_init f (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)).
    by apply wp_promise_steps_retag. }
  have Hofd' := ptraces_dev_of_retag pstep_ev pdev_ev f TS DS mid c Hofd.
  have Hcwf : cfg_wf mid.
  { eapply (cfg_wf_promise_run pstep_ev);
      [apply (cfg_wf_init (P:=pexv6) (img_z (wgimg σ0)) (wgdev σ0)
                (eps_init σ0))|exact Hprom]. }
  have Hcanon : cls_canonical pcls_ev (retag_traces f TS).
  { apply (cls_canonical_canon pstep_ev pdev_ev).
    - by destruct Hofd as ((_ & _ & _ & Hwft & _) & _).
    - eapply (ts_pos_of_ptraces pstep_ev pdev_ev);
        [exact Hcwf|by destruct Hofd as (Hof & _)]. }
  (* THE LAYER-1 THEOREM, at the retagged bundle *)
  destruct (robust_main_bundle pstep_ev pcls_ev pdev_ev n_disk
              (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)
              (retag_cfg f c) (retag_cfg f mid) (retag_traces f TS) DS
              pstep_ev_lat_free_prog pstep_ev_ts_oblivious pcls_ev_obl
              Hprom' Hofd' (efulfil_acct_retag f mid TS Hacct)
              (Hprem _ _ _ _ Hbeh' Hprom' Hofd' Hcanon) Hcanon Hvf)
    as (cf & Hrun & Hpg & Hmm).
  (* ...and the conclusion comes back to [c] (the retag moves neither the
     program states nor the flat memory), with the language run attached *)
  have Hrun0 : rtc (wp_pf_run pstep_ev pcls_ev) (ecfg_of (ep_init gen) σ0) cf.
  { by rewrite (ecfg_of_init gen σ0 Hlog Hws). }
  destruct (wp_pf_rtc_epf_rtc (ep_init gen) σ0 cf Hlive Hrun0)
    as (P' & σ' & Hr & Heq).
  exists cf. split_and!.
  - exact Hrun.
  - by rewrite Hpg prog_of_retag.
  - intros a. by rewrite Hmm mem_of_retag.
  - by exists P', σ'.
Qed.

(** THE AUDIT (run at build time, recorded here):

      Print Assumptions xv6_ev_weak_robust.
      Axioms:
      rv64d.valid_reservation : unit -> bool
      rv64d.plat_term_write : ... -> rv64d_types.M unit
      rv64d.match_reservation : ... -> bool
      rv64d.load_reservation : ... -> unit
      rv64d.cancel_reservation : unit -> unit

    i.e. EXACTLY the five generated-model axioms the whole tree carries —
    no functional extensionality, no classical logic, no admitted lemma,
    and none of the archived route's shape/liveness records. *)

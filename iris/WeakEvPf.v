(** * WeakEvPf.v — the definitional correspondence (spike S2)

    Design: [claude-notes/design/weak-memory-event-granular.md]; worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S2).

    The design's one-sentence claim is that [WeakEvLang]'s erased-step
    relation IS the promise-free machine BY CONSTRUCTION.  This file makes
    that precise, in both directions, with NO simulation argument: every
    statement below is proved by structural case analysis on ONE step or by
    induction on an [rtc], and nothing anywhere reconstructs an instruction.

    ------------------------------------------------------------------------
    ** THE S2 ROUTE, AND WHY (this is the spike's S2 core — read it) **

    THE OBSTRUCTION, stated exactly.  [WeakPromise.wpcfg P] has EXACTLY TWO
    shared components — the era-initial image and the write log — plus a LIST
    of per-agent records.  A [WeakPromiseBridge.wp_pf_step] of agent [i]
    reads the two shared components and agent [i], and writes the log and
    agent [i].  There is no third shared component and no arm that writes
    another agent's slot.

    THE EVENT LANGUAGE HAS A THIRD SHARED COMPONENT: the device fabric
    [egdev].  It is genuinely shared — hart A's MMIO write is visible to
    hart B's MMIO read, the PLIC wire hart A reads is driven by state the
    UART and the disk move, and the disk's DMA is a function of it.  So:

      (a) If the pf-side hart carries a PRIVATE copy of the fabric (which is
          what [WeakSailLTS.psail]'s [sp_dev] does, and the only thing
          [wpcfg] can express), then NEITHER containment holds.  ⇒ fails
          because an erased device write updates the one shared fabric while
          a pf step updates one agent's copy; ⇐ fails because a pf hart can
          read a value from its stale private copy that no shared-fabric run
          ever produces, and device read values feed control flow and hence
          the log.
      (b) If the pf-side device answers are left FREE (nondeterministic),
          ⇐ fails for the same reason — the pf machine is then strictly more
          permissive on an axis that reaches the log.
      (c) If the pf-side device arms are STUCK, ⇐ holds but the machine is
          one xv6 does not run on (the kernel does MMIO), so the robustness
          theorem it would feed is vacuous.

    ⇐ — "every pf run is an erased run" — is the direction the φ export needs
    (S3), so the pf machine's device behaviour must be AT MOST the language's,
    i.e. THE FABRIC MUST BE IN THE CONFIGURATION.

    LAYER-1 PARAMETRICITY DOES NOT SUPPLY IT.  [WeakRobustMain]'s [Section
    main] is parametric in the PROGRAM TYPE [P] and the program LTS [pstep]
    — [Context {P : Type}] / [Context (pstep : P → wlabel → P → Prop)] — but
    NOT in the configuration functor: every statement is over [wpcfg P], and
    [wpcfg] is a concrete three-field record.  So a shared fabric cannot be
    threaded in through [P]: whatever [P] is, a step of agent [i] writes
    slot [i] and nothing else.

    THE ROUTE TAKEN: the FABRIC-SHARED promise-free machine, stated over the
    language's own state.  [epf_step i l σ σ'] (§3) is
    [WeakPromiseBridge.wp_pf_step]'s five arms — silent, load, store, rmw,
    fence, with their side conditions [read_ok] / [excl_ok] / [data ≠ []] and
    their view updates [load_post_run] / [store_post_run] / [fence_post]
    VERBATIM — transported to [egstate], whose shared part is (image, log,
    FABRIC).  Because the machine's step IS the language's step decorated
    with the label its memory effect determines, the correspondence is
    definitional in the strongest sense available: ⇐ is a PROJECTION
    ([epf_step_eprim], §4) and ⇒ is a LABEL EXHIBITION ([ehart_step_label],
    §5) — one case analysis, no invariant, no simulation relation.

    WHAT THIS COSTS, RECORDED HONESTLY.  Layer 1 ([WeakRobustMain.robust_main])
    does NOT instantiate at [epf_step]: it would need [wpcfg] generalised to
    carry a shared device component (a mechanical but real change to
    [WeakPromise.v] and to every file above it).  §6 states the projection
    that DOES exist — [ecfg_of : egstate → wpcfg pexv6] — and the precise
    sense in which it is the wrong way round.  This is not a NEW seam: it is
    [WeakCompose]'s seam (4), the retained MMIO/device-fabric assumption,
    unchanged.  THE SPIKE'S FINDING IS THEREFORE THAT THE DESIGN'S "the
    device seam collapses at the definition" IS TRUE OF THE LANGUAGE AND
    FALSE OF THE PF MACHINE: event granularity dissolves the ORACLE
    (there is no [sp_dev] stream, no [sp_irq], no [oracle_consistent], no
    per-path premise) but not the SHARED-CHANNEL mismatch, which is a
    property of [wpcfg]'s shape and not of the granularity.

    ------------------------------------------------------------------------
    ** THE LAYOUT **

    Pool positions ↔ agent indices, exactly [WeakCompose.xv6_ps]'s layout:
    hart [c] at index [fin_to_nat c] (so [0 .. NCPU-1]) and the disk at
    [WeakLang.n_disk = NCPU].  The UART thread has NO agent of its own: its
    arm touches neither the log nor any [wstate] nor any hart's program
    state, so it is a SILENT step of the fabric-owning agent (the disk).
    The PLIC thread likewise has no agent: its arm is the interrupt-delivery
    EVENT of the hart it targets ([WeakEvLang.eplic_step] is
    [∃ c, eirq_step σ c σ']), so it is a silent step of THAT agent. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakPromiseBridge.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakGhost.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. [fin]-indexed lookup, once

    [enum CPU] is [fin_enum NCPU]; the two facts every layout lemma needs
    are that hart [c] sits at index [fin_to_nat c] and that nothing else
    does. *)

Lemma fin_enum_lookup (n : nat) (i : fin n) :
  fin_enum n !! (fin_to_nat i) = Some i.
Proof.
  induction n as [|n IH]; [inversion i|].
  inv_fin i; [done|]. intros i. cbn [fin_enum fin_to_nat].
  rewrite lookup_cons list_lookup_fmap IH //.
Qed.

Lemma fin_enum_lookup_nat (n : nat) :
  forall (j : nat) (x : fin n), fin_enum n !! j = Some x -> @fin_to_nat n x = j.
Proof.
  induction n as [|n IH]; intros j x Hj; [by rewrite lookup_nil in Hj|].
  destruct j as [|j]; cbn [fin_enum] in Hj.
  - rewrite lookup_cons in Hj. by simplify_eq.
  - rewrite lookup_cons list_lookup_fmap in Hj.
    destruct (fin_enum n !! j) as [y|] eqn:Hy; simplify_eq/=.
    cbn [fin_to_nat]. by rewrite (IH j y Hy).
Qed.

Lemma fin_enum_length (n : nat) : length (fin_enum n) = n.
Proof. induction n as [|n IH]; [done|]. cbn. by rewrite length_fmap IH. Qed.

Lemma enum_CPU_lookup (c : CPU) : enum CPU !! (fin_to_nat c) = Some c.
Proof. apply fin_enum_lookup. Qed.

Lemma enum_CPU_length : length (enum CPU) = NCPU.
Proof. apply fin_enum_length. Qed.

(* ====================================================================== *)
(** ** 1. The program type and the agent layout *)

(** A hart's PROGRAM state is exactly what [egstate] keeps per hart minus its
    view: the residual monad, the register file and the parked fence.  There
    is no [sp_dev] and no [sp_irq] — that is the whole point (design doc: the
    oracle components DO NOT EXIST). *)
Inductive pexv6 :=
| EHart (m : option (M unit)) (rs : regstate)
        (fn : option (bool * bool * bool * bool))
| EDisk (pend : list wmsg).

Definition ehart_ag (σ : egstate) (c : CPU) : wpagent pexv6 :=
  WPAgent (EHart (eg_hs σ c) (egregs σ c) (eg_fence σ c)) (egws σ c) ∅.

Definition edisk_ag (σ : egstate) : wpagent pexv6 :=
  WPAgent (EDisk (eg_pend σ)) (eg_dws σ) ∅.

Definition eags (σ : egstate) : list (wpagent pexv6) :=
  (ehart_ag σ <$> enum CPU) ++ [edisk_ag σ].

(** THE PROJECTION to a [WeakPromise] configuration — the fabric is dropped,
    which is exactly the information the pf machine cannot hold (§6). *)
Definition ecfg_of (σ : egstate) : wpcfg pexv6 :=
  WPCfg (img_z (egimg σ)) (eglog σ) (eags σ).

Lemma eags_hart σ (c : CPU) : eags σ !! (fin_to_nat c) = Some (ehart_ag σ c).
Proof.
  rewrite /eags lookup_app_l.
  - rewrite list_lookup_fmap enum_CPU_lookup //.
  - rewrite length_fmap enum_CPU_length. apply fin_to_nat_lt.
Qed.

Lemma eags_disk σ : eags σ !! n_disk = Some (edisk_ag σ).
Proof.
  rewrite /eags /n_disk lookup_app_r.
  2:{ rewrite length_fmap enum_CPU_length. done. }
  rewrite length_fmap enum_CPU_length Nat.sub_diag //.
Qed.

Lemma eags_length σ : length (eags σ) = S NCPU.
Proof.
  rewrite /eags length_app length_fmap enum_CPU_length.
  cbn [length]. lia.
Qed.

(** Every index below [S NCPU] is a hart or the disk, and nothing else is an
    index at all — the layout is exhaustive. *)
Lemma eags_lookup_inv σ i ag :
  eags σ !! i = Some ag ->
  (exists c : CPU, i = fin_to_nat c /\ ag = ehart_ag σ c)
  \/ (i = n_disk /\ ag = edisk_ag σ).
Proof.
  intros Hi. destruct (decide (i < NCPU)%nat) as [Hlt|Hge].
  - rewrite /eags lookup_app_l in Hi.
    2:{ rewrite length_fmap enum_CPU_length. exact Hlt. }
    rewrite list_lookup_fmap in Hi.
    destruct (enum CPU !! i) as [c|] eqn:Hc; simplify_eq/=.
    left. exists c. split; [by rewrite (fin_enum_lookup_nat NCPU i c Hc)|done].
  - right. pose proof (lookup_lt_Some _ _ _ Hi) as Hlen.
    rewrite eags_length in Hlen.
    have Hie : i = n_disk.
    { rewrite /n_disk. unfold NCPU in *. lia. }
    subst i. rewrite eags_disk in Hi. by simplify_eq.
Qed.

(* ====================================================================== *)
(** ** 2. The labels: reading a [wlabel] off a σ-transition

    [elabel_ok σ c l σ'] says "the memory effect of hart [c]'s transition
    [σ ⇝ σ'] IS the label [l]", spelled with EXACTLY the side conditions and
    view updates of [WeakPromiseBridge.wp_pf_step]'s five arms.  The message
    class stays a FREE BINDER, as [PFStore]/[PFRmw] leave it. *)

(** What a step of hart [c] leaves alone.  This is the agent-locality of the
    pf machine, restated over σ: another hart's program state and view, the
    disk's, the image, and the era. *)
Definition eframe (σ : egstate) (c : CPU) (σ' : egstate) : Prop :=
  egimg σ' = egimg σ /\ egpow σ' = egpow σ /\ eggen σ' = eggen σ /\
  eg_pend σ' = eg_pend σ /\ eg_dws σ' = eg_dws σ /\
  (forall c' : CPU, c' <> c ->
     egws σ' c' = egws σ c' /\ egregs σ' c' = egregs σ c' /\
     eg_hs σ' c' = eg_hs σ c' /\ eg_fence σ' c' = eg_fence σ c').

Lemma eframe_ehart_set σ c m rs fn ws lg d :
  eframe σ c (ehart_set σ c m rs fn ws lg d).
Proof.
  rewrite /eframe /ehart_set /=. split_and!; try reflexivity.
  intros c' Hne. by rewrite !eset_at_ne.
Qed.

Definition elabel_ok (σ : egstate) (c : CPU) (l : wlabel) (σ' : egstate)
    : Prop :=
  eframe σ c σ' /\
  match l with
  | LSilent => eglog σ' = eglog σ /\ egws σ' c = egws σ c
  | LLoad aq lat base tvs =>
      lat = false /\
      read_ok (img_z (egimg σ)) (eglog σ) (egws σ c) aq lat base tvs /\
      eglog σ' = eglog σ /\
      egws σ' c = load_post_run (egws σ c) aq base tvs.*1
  | LStore rl base data =>
      (exists k, eglog σ' = eglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]) /\
      data <> [] /\
      egws σ' c = store_post_run (egws σ c) rl base (length data)
                    (S (length (eglog σ)))
  | LRmw aq rl base tvs data =>
      data <> [] /\ length tvs = length data /\
      read_ok (img_z (egimg σ)) (eglog σ) (egws σ c) aq false base tvs /\
      excl_ok (eglog σ) (fin_to_nat c) base tvs (S (length (eglog σ))) /\
      (exists k, eglog σ' = eglog σ ++ [WMsg base data (Some (fin_to_nat c)) k]) /\
      egws σ' c = store_post_run (load_post_run (egws σ c) aq base tvs.*1)
                    rl base (length data) (S (length (eglog σ)))
  | LFence pr pw sr sw =>
      eglog σ' = eglog σ /\ egws σ' c = fence_post (egws σ c) pr pw sr sw
  end.

(** The disk agent's version.  Only two labels ever arise — the burst and a
    UART step are silent, an emit is a store — which is the 1:1 match with
    the pf disk agent the design promises. *)
Definition edframe (σ σ' : egstate) : Prop :=
  egimg σ' = egimg σ /\ egpow σ' = egpow σ /\ eggen σ' = eggen σ /\
  (forall c : CPU, egws σ' c = egws σ c /\ egregs σ' c = egregs σ c /\
                   eg_hs σ' c = eg_hs σ c /\ eg_fence σ' c = eg_fence σ c).

Definition edlabel_ok (σ : egstate) (l : wlabel) (σ' : egstate) : Prop :=
  edframe σ σ' /\
  match l with
  | LSilent => eglog σ' = eglog σ /\ eg_dws σ' = eg_dws σ
  | LStore rl base data =>
      (exists k, eglog σ' = eglog σ ++ [WMsg base data (Some n_disk) k]) /\
      data <> [] /\
      eg_dws σ' = store_post_run (eg_dws σ) rl base (length data)
                    (S (length (eglog σ)))
  | _ => False
  end.

Lemma wbytes_ne (n : N) {w : N} (v : bv w) : n <> 0%N -> wbytes n v <> [].
Proof.
  intros Hn Heq. have Hl := wbytes_length n v. rewrite Heq /= in Hl.
  destruct n as [|pn]; [by apply Hn|]. cbn in Hl.
  by pose proof (Pos2Nat.is_pos pn); lia.
Qed.

(* ====================================================================== *)
(** ** 3. THE FABRIC-SHARED PROMISE-FREE MACHINE

    [wp_pf_step]'s five arms over [egstate].  An arm is "the language's own
    event, plus the label its memory effect determines" — so the machine is
    not a second definition of anything: it is the language, with the pf
    bookkeeping made visible. *)
Inductive epf_step : nat -> wlabel -> egstate -> egstate -> Prop :=
| EPFHart (c : CPU) (l : wlabel) (σ σ' : egstate) :
    (ehart_step σ c σ' \/ eirq_step σ c σ') ->
    elabel_ok σ c l σ' ->
    epf_step (fin_to_nat c) l σ σ'
| EPFDisk (l : wlabel) (σ σ' : egstate) :
    (edisk_step σ σ' \/ euart_step σ σ') ->
    edlabel_ok σ l σ' ->
    epf_step n_disk l σ σ'.

Definition epf_run (σ σ' : egstate) : Prop := exists i l, epf_step i l σ σ'.

(** THE ERA IS FIXED across the pf machine — as it is across Layer 1, which
    is stated per-era.  (The power thread is deliberately NOT a pf arm.) *)
Lemma epf_step_era i l σ σ' :
  epf_step i l σ σ' -> egpow σ' = egpow σ /\ eggen σ' = eggen σ.
Proof.
  destruct 1 as [c l0 σ0 σ0' _ [(? & ? & ? & _) _]
                |l0 σ0 σ0' _ [(? & ? & ? & _) _]]; by split.
Qed.

Lemma epf_step_live gen i l σ σ' :
  ethread_live σ gen -> epf_step i l σ σ' -> ethread_live σ' gen.
Proof.
  intros [Hp Hg] Hs. destruct (epf_step_era _ _ _ _ Hs) as [He1 He2].
  rewrite /ethread_live He1 He2. by split.
Qed.

Lemma epf_run_live gen σ σ' :
  ethread_live σ gen -> rtc epf_run σ σ' -> ethread_live σ' gen.
Proof.
  intros Hl Hr. induction Hr as [|x y z (i & l & Hs) _ IH]; [done|].
  apply IH. by eapply epf_step_live.
Qed.

(* ====================================================================== *)
(** ** 4. ⇐ : EVERY PF STEP IS AN ERASED STEP

    The direction the φ export consumes (S3).  It is a PROJECTION: an
    [epf_step] literally contains the language's own step, so the only work
    is naming the pool position it belongs to. *)

Definition ecpu_pool (gen : nat) : list (expr weak_ev_lang) :=
  (LoopE gen <$> enum CPU)
  ++ [UartLoopE gen; DiskLoopE gen; PlicLoopE gen].

Lemma ecpu_pool_hart gen (c : CPU) : LoopE gen c ∈ ecpu_pool gen.
Proof.
  rewrite /ecpu_pool. apply elem_of_app. left.
  apply elem_of_list_fmap. exists c. split; [done|apply elem_of_enum].
Qed.

Lemma ecpu_pool_uart gen : UartLoopE gen ∈ ecpu_pool gen.
Proof. rewrite /ecpu_pool. apply elem_of_app. right. set_solver. Qed.
Lemma ecpu_pool_disk gen : DiskLoopE gen ∈ ecpu_pool gen.
Proof. rewrite /ecpu_pool. apply elem_of_app. right. set_solver. Qed.
Lemma ecpu_pool_plic gen : PlicLoopE gen ∈ ecpu_pool gen.
Proof. rewrite /ecpu_pool. apply elem_of_app. right. set_solver. Qed.

Theorem epf_step_eprim gen i l σ σ' :
  ethread_live σ gen -> epf_step i l σ σ' ->
  exists e, e ∈ ecpu_pool gen /\ eprim_step e σ [] e σ' [].
Proof.
  intros Hlive Hs. destruct Hs as [c l0 σ0 σ0' [Hh|Hirq] _|l0 σ0 σ0' [Hd|Hu] _].
  - (* a hart event *)
    exists (LoopE gen c). split; [apply ecpu_pool_hart|].
    left. exists gen, c. split_and!; try reflexivity. left. by split.
  - (* an interrupt delivery — the PLIC thread's arm *)
    exists (PlicLoopE gen). split; [apply ecpu_pool_plic|].
    right; right; right; left. exists gen. split_and!; try reflexivity.
    left. split; [exact Hlive|]. by exists c.
  - (* a disk burst or emit *)
    exists (DiskLoopE gen). split; [apply ecpu_pool_disk|].
    right; right; left. exists gen. split_and!; try reflexivity.
    left. by split.
  - (* a UART step — a silent step of the fabric-owning agent *)
    exists (UartLoopE gen). split; [apply ecpu_pool_uart|].
    right; left. exists gen. split_and!; try reflexivity.
    left. by split.
Qed.

(** ... and at the RUN level.  The pool never changes (no arm forks and no
    arm changes its own expression), so the erased run stays at
    [ecpu_pool gen] throughout. *)
Lemma epf_run_erased_step gen σ σ' :
  ethread_live σ gen -> epf_run σ σ' ->
  @erased_step weak_ev_lang (ecpu_pool gen, σ) (ecpu_pool gen, σ').
Proof.
  intros Hlive (i & l & Hs).
  destruct (epf_step_eprim gen i l σ σ' Hlive Hs) as (e & He & Hstep).
  apply elem_of_list_split in He as (t1 & t2 & Hpool).
  exists []. eapply (@step_atomic weak_ev_lang _ _ _ e σ e σ' [] t1 t2).
  - by rewrite Hpool.
  - by rewrite Hpool app_nil_r.
  - exact Hstep.
Qed.

Theorem epf_rtc_erased gen σ σ' :
  ethread_live σ gen -> rtc epf_run σ σ' ->
  rtc (@erased_step weak_ev_lang) (ecpu_pool gen, σ) (ecpu_pool gen, σ').
Proof.
  intros Hlive Hr. revert Hlive.
  induction Hr as [|x y z Hxy _ IH]; intros Hlive; [apply rtc_refl|].
  eapply rtc_l; [by apply epf_run_erased_step|].
  apply IH. destruct Hxy as (i & l & Hs). by eapply epf_step_live.
Qed.

(* ====================================================================== *)
(** ** 5. ⇒ : EVERY ERASED STEP IS A PF STEP (or a stutter)

    The label exhibition.  ONE case analysis over the outcome the residual
    monad sits at — the same analysis [WeakEvLang]'s own frame lemmas do —
    and in each branch the label is READ OFF the σ-update. *)

Lemma eirq_step_label σ c σ' : eirq_step σ c σ' -> elabel_ok σ c LSilent σ'.
Proof.
  intros ->. split; [apply eframe_ehart_set|].
  split; [reflexivity|apply ehart_set_ws_eq].
Qed.

Lemma ehart_step_label σ c σ' :
  ehart_step σ c σ' -> exists l, elabel_ok σ c l σ'.
Proof.
  rewrite /ehart_step.
  destruct (eg_fence σ c) as [[[[pr pw] sr] sw]|].
  { intros ->. exists (LFence pr pw sr sw). split; [apply eframe_ehart_set|].
    split; [reflexivity|apply ehart_set_ws_eq]. }
  intros [Hirq|H]; [exists LSilent; by apply eirq_step_label|].
  destruct (eg_hs σ c) as [m|].
  2:{ destruct H as (tick & ->). exists LSilent.
      split; [apply eframe_ehart_set|].
      split; [reflexivity|apply ehart_set_ws_eq]. }
  destruct m as [y|T oc k].
  { rewrite H. exists LSilent. split; [apply eframe_ehart_set|].
    split; [reflexivity|apply ehart_set_ws_eq]. }
  destruct oc; simpl in H;
    try (rewrite H; exists LSilent; split;
         [apply eframe_ehart_set|split; [reflexivity|apply ehart_set_ws_eq]]);
    try (by destruct H).
  - (* MemRead *)
    destruct (dev_addr _).
    + destruct H as (w & d' & _ & ->). exists LSilent.
      split; [apply eframe_ehart_set|].
      split; [reflexivity|apply ehart_set_ws_eq].
    + destruct H as (_ & [(w & tvs & Hlen & Hbytes & Hrd & ->)
                         |(Hlat & w & tvs & data & rl & m1 & m2 & rs1 &
                           Hlen & Hbytes & Hrd & Hex & Hne & Hlend & Hsil &
                           Hwr & ->)]).
      * eexists (LLoad _ false _ tvs). split; [apply eframe_ehart_set|].
        split_and!; [reflexivity|exact Hrd|reflexivity|apply ehart_set_ws_eq].
      * eexists (LRmw _ rl _ tvs data). split; [apply eframe_ehart_set|].
        split_and!; [exact Hne|exact Hlend|exact Hrd|exact Hex| |].
        { exists WCexcl. reflexivity. }
        apply ehart_set_ws_eq.
        (* the class is [WCexcl] by construction — delta (D2) *)
  - (* MemWrite *)
    destruct (dev_addr _).
    + destruct H as (d' & _ & ->). exists LSilent.
      split; [apply eframe_ehart_set|].
      split; [reflexivity|apply ehart_set_ws_eq].
    + destruct H as (Hn & ->).
      eexists (LStore _ _ _). split; [apply eframe_ehart_set|].
      split_and!.
      * eexists. reflexivity.
      * by apply wbytes_ne.
      * rewrite wbytes_length. apply ehart_set_ws_eq.
  - (* Barrier *)
    rewrite H. destruct b;
      [ eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | eexists (LFence _ _ _ _) | eexists (LFence _ _ _ _)
      | exists LSilent ];
      (split; [apply eframe_ehart_set|]);
      (split; [reflexivity|apply ehart_set_ws_eq]).
  - (* Choose *)
    destruct H as (ch & ->). exists LSilent.
    split; [apply eframe_ehart_set|].
    split; [reflexivity|apply ehart_set_ws_eq].
Qed.

Lemma edisk_step_label σ σ' : edisk_step σ σ' -> exists l, edlabel_ok σ l σ'.
Proof.
  intros [(_ & d' & w & _ & ->)|(m & rest & Hp & Hd & Ht & ->)].
  - exists LSilent. by rewrite /edlabel_ok /edframe /=.
  - destruct m as [mpa mdata mtid mak]. simpl in Hd, Ht. subst mtid.
    exists (LStore false mpa mdata).
    split.
    { rewrite /edframe /=. split_and!; try reflexivity.
      intros c. by split_and!. }
    simpl. split_and!.
    + by exists mak.
    + exact Hd.
    + reflexivity.
Qed.

Lemma euart_step_label σ σ' : euart_step σ σ' -> edlabel_ok σ LSilent σ'.
Proof.
  intros (d' & _ & ->). rewrite /edlabel_ok /edframe /=.
  split_and!; try reflexivity. intros c. by split_and!.
Qed.

(** THE ⇒ THEOREM.  Every erased step of a non-power thread either stutters
    (the corpse arms of a dead generation) or IS a pf step. *)
Theorem eprim_step_epf e σ κ e' σ' efs :
  eprim_step e σ κ e' σ' efs -> e <> PowerLoopE ->
  σ' = σ \/ epf_run σ σ'.
Proof.
  intros Hstep Hnp.
  destruct Hstep as [(gen & cpu & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm) | (-> & _)]]]];
    [| | | |by destruct (Hnp eq_refl)].
  - destruct Harm as [(_ & Hh)|(_ & ->)]; [|by left]. right.
    destruct (ehart_step_label σ cpu σ' Hh) as (l & Hl).
    exists (fin_to_nat cpu), l. by apply EPFHart; [left|].
  - destruct Harm as [(_ & Hu)|(_ & ->)]; [|by left]. right.
    exists n_disk, LSilent. apply EPFDisk; [by right|by apply euart_step_label].
  - destruct Harm as [(_ & Hd)|(_ & ->)]; [|by left]. right.
    destruct (edisk_step_label σ σ' Hd) as (l & Hl).
    exists n_disk, l. by apply EPFDisk; [left|].
  - destruct Harm as [(_ & (c & Hirq))|(_ & ->)]; [|by left]. right.
    exists (fin_to_nat c), LSilent.
    apply EPFHart; [by right|by apply eirq_step_label].
Qed.

(** The pool NEVER MOVES outside the power arm: every arm returns its own
    expression and forks nothing. *)
Lemma eprim_step_shape e σ κ e' σ' efs :
  eprim_step e σ κ e' σ' efs -> e <> PowerLoopE -> e' = e /\ efs = [].
Proof.
  intros Hs Hnp.
  destruct Hs as [(g & c & -> & -> & _ & -> & _)
                 | [(g & -> & -> & _ & -> & _)
                 | [(g & -> & -> & _ & -> & _)
                 | [(g & -> & -> & _ & -> & _) | (-> & _)]]]];
    try (by split). all: by destruct (Hnp eq_refl).
Qed.

Lemma ecpu_pool_no_power gen : PowerLoopE ∉ ecpu_pool gen.
Proof.
  rewrite /ecpu_pool. intros He. apply elem_of_app in He as [He|He].
  - apply elem_of_list_fmap in He as (? & ? & _). discriminate.
  - repeat (apply elem_of_cons in He as [He|He]; [discriminate|]).
    by apply not_elem_of_nil in He.
Qed.

(** ONE ERASED STEP IS ONE PF STEP (or a stutter), with the pool unmoved. *)
Lemma erased_step_epf gen t' σ σ' :
  @erased_step weak_ev_lang (ecpu_pool gen, σ) (t', σ') ->
  t' = ecpu_pool gen /\ (σ' = σ \/ epf_run σ σ').
Proof.
  intros (κ & Hst).
  destruct Hst as [e1 σa e2 σb efs ta tb Ha Hb Hps].
  injection Ha as Hpool Hσa. injection Hb as Ht' Hσb. subst σa σb t'.
  have He1 : e1 ∈ ecpu_pool gen.
  { rewrite Hpool. apply elem_of_app. right. apply elem_of_cons. by left. }
  have Hnp : e1 <> PowerLoopE.
  { intros ->. by apply (ecpu_pool_no_power gen). }
  destruct (eprim_step_shape _ _ _ _ _ _ Hps Hnp) as [-> ->].
  split; [by rewrite app_nil_r -Hpool|].
  exact (eprim_step_epf e1 σ κ e1 σ' [] Hps Hnp).
Qed.

(** ... and at the RUN level, in the shape the correspondence is usually
    quoted in: an erased run of the canonical pool induces a pf run. *)
Lemma erased_rtc_epf_aux (ρ1 ρ2 : cfg weak_ev_lang) :
  rtc (@erased_step weak_ev_lang) ρ1 ρ2 ->
  forall gen σ t2 σ2, ρ1 = (ecpu_pool gen, σ) -> ρ2 = (t2, σ2) ->
  rtc epf_run σ σ2.
Proof.
  induction 1 as [ρ|ρ1 ρ ρ2 Hstep Hrest IH]; intros gen σ t2 σ2 -> Heq.
  - by simplify_eq.
  - destruct ρ as [t' σ'].
    destruct (erased_step_epf gen t' σ σ' Hstep) as [-> Hor].
    destruct Hor as [->|Hpf].
    + by apply (IH gen σ t2 σ2).
    + eapply rtc_l; [exact Hpf|]. by apply (IH gen σ' t2 σ2).
Qed.

Theorem erased_rtc_epf gen (t2 : list (expr weak_ev_lang)) (σ σ2 : egstate) :
  rtc (@erased_step weak_ev_lang) (ecpu_pool gen, σ) (t2, σ2) ->
  rtc epf_run σ σ2.
Proof. intros Hr. by eapply erased_rtc_epf_aux. Qed.

(* ====================================================================== *)
(** ** 6. THE PROJECTION TO [wpcfg], AND WHAT IT DOES NOT GIVE

    [ecfg_of] forgets the fabric.  The two facts a consumer of Layer 1's
    vocabulary needs are here: the observation floor of a hart agent IS that
    hart's coherence floor, and the disk sits at [n_disk].  What is NOT here,
    and cannot be, is the reverse containment — see the header. *)

Lemma obs_flr_hart σ (c : CPU) (a : Z) :
  obs_flr (ecfg_of σ) (fin_to_nat c) a = coh (egws σ c) a.
Proof. rewrite /obs_flr /ecfg_of /= eags_hart //. Qed.

Lemma ecfg_of_log σ : pc_log (ecfg_of σ) = eglog σ.
Proof. reflexivity. Qed.

(** THE φ TRANSPORT: [WeakGhost.no_violation] over σ REFUTES Layer 1's
    [WeakRobust.violation_hart] at the projected configuration, at the hart
    bound [n_disk = NCPU] — the two predicates are the same statement, term for term
    (that alignment is what [WeakRobustMain.pub_of]'s log spelling bought).
    This is the whole of what S3's success criterion needs from the layout. *)
Theorem no_violation_violation_hart σ :
  no_violation (eglog σ) (egws σ) ->
  ~ violation_hart cls_of pub_of n_disk (ecfg_of σ).
Proof.
  intros Hnv (p & m & i & j & a & Hp & Ht & Hth & Hcls & Hpub & Hne & Hjh &
              Hb & Hfl).
  rewrite ecfg_of_log in Hp.
  destruct Hth as (i' & Hti & Hilt).
  assert (i' = i) as -> by (rewrite Ht in Hti; by simplify_eq).
  destruct Hjh as (j' & Hj & Hjlt).
  assert (j' = j) as -> by (by simplify_eq).
  have Hcn : fin_to_nat (nat_to_fin Hilt) = i by apply fin_to_nat_to_fin.
  have Hcn' : fin_to_nat (nat_to_fin Hjlt) = j by apply fin_to_nat_to_fin.
  have Hak : wm_ak m = WCplain.
  { rewrite /cls_of in Hcls. by destruct (wm_ak m). }
  have Hnpub : ~ wpublished (eglog σ) (wm_tid m) p.
  { intros Hw. apply Hpub. rewrite /pub_of. exists p, m.
    rewrite ecfg_of_log. by split_and!. }
  have Hti2 : wm_tid m = Some (fin_to_nat (nat_to_fin Hilt)) by rewrite Hcn.
  have Hnec : nat_to_fin Hjlt <> nat_to_fin Hilt.
  { intros Heq. apply Hne. by rewrite -Hcn -Hcn' Heq. }
  have Hlt := Hnv p m (nat_to_fin Hilt) a Hp Hti2 Hak Hnpub Hb
                (nat_to_fin Hjlt) Hnec.
  rewrite -Hcn' obs_flr_hart in Hfl. lia.
Qed.

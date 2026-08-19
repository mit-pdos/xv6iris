(** * WeakEvAdequacy.v — the interpretation and the φ export (spike S3, revised)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    "expression-resident monad" section); worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S3).

    [WeakAdequacy.weak_system_adequacy_phi] restated over [WeakEvLang]'s
    event-granular language, and then — this is the point of the whole spike —
    the SUCCESS CRITERION derived from it and from [WeakEvPf]'s correspondence
    with ZERO GLUE PREMISES.

    WHAT THE DESIGN REVISION BOUGHT HERE, exactly: the pre-revision draft put
    the residual monad, the parked fence and the disk's two operation fields in
    σ, and therefore had to add FOUR exclusive points-tos ([hart_prog],
    [hart_fence], [disk_pend], [disk_view]), a [weakEvGpreS]/[weakEvGS] functor
    pair, a [wev_extra] conjunct and its allocation block.  With the placement
    rule applied (control state in the EXPRESSION where control flow is
    model-defined), ALL OF THAT IS GONE:

      σ = [WeakLang.wgstate] verbatim, and
      [state_interp] = [WeakGhost.weak_state_interp], VERBATIM.

    So the log auth, the per-hart [wstate] cells, the per-byte latest-write
    map, the C/D/S protocol, the register and device ghosts, the [ws_bounded]
    machine invariant and the φ conjunct are not merely "transferred" — they
    are the same definition, and [weak_state_interp_export] is reused with no
    wrapper at all.  The only thing this file still owns is the [irisGS]
    instance at the new language and the two theorems.

    ------------------------------------------------------------------------
    SCOPE (deliberate, and the same cuts [WeakAdequacy]'s header records):
    single era, no power thread in the pool, no boot carve, placeholder names
    for the unused [riscvGS] ghosts.  In addition, and specific to this file:
    THE POOL'S WPs ARE A HYPOTHESIS — §3's theorem takes the client's proof of
    the pool's WPs exactly as [weak_system_adequacy_phi] does, with the leaves
    ABSTRACT.  What is delivered is the invariant-extraction shape: the
    interpretation is established at the initial state, threaded by the WP, and
    READ OFF at every reachable state. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import csum excl.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import ghost_map ghost_var mono_nat invariants.
From iris.program_logic Require Import language weakestpre lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakViewMono.
Require Import WeakGhost.
Require Import WeakViolation.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvAdequacy.
Require Import WeakEvLang.
Require Import WeakEvPf.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The [irisGS] instance and the Φ-free WP

    [WeakGhost.weak_irisGS]'s twin at the event language.  The notation is
    [EWP], distinct from SC's [WP] and from [WeakGhost]'s [WWP], for exactly
    the reason [WeakGhost]'s header gives: a shared token would let a statement
    elaborate at the wrong language and still compile. *)

Global Program Instance weak_ev_irisGS `{!riscvGS Σ, !weakGS Σ}
    : irisGS weak_ev_lang Σ := {
  iris_invGS := riscvF_invGS;
  state_interp σ _ _ _ := weak_state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

Definition ewp_triv `{!riscvGS Σ, !weakGS Σ}
    (E : coPset) (e : expr weak_ev_lang) : iProp Σ :=
  wp NotStuck E e (fun _ => True%I).

Notation "'EWP' e @ E" := (ewp_triv E e%E) (at level 20, e at level 20) : bi_scope.

(* ====================================================================== *)
(** ** 2. The φ export at the language level *)

Theorem weak_ev_adequacy_phi Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ : wgstate) (D : CPU -> gset register)
    (Hgen : gen = 0%nat)
    (* THE FRESH ERA — [WeakLang.wboot_facts]' machine-side clauses *)
    (Hpow : wgpow σ = true) (Hgen0 : wggen σ = 0%nat)
    (Hlog : wglog σ = [])
    (Hws : forall c : CPU, wgws σ c = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (wgregs σ c))) ∗
       ([∗ map] a ↦ b ∈ wgimg σ, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       wlog_lb [] ∗
       uart_frag (wgdev σ).(duart) ∗ plic_frag (wgdev σ).(dplic) ∗
       virtio_frag (wgdev σ).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
  forall t2 σ2,
    rtc (@erased_step weak_ev_lang) (epower_fork gen, σ) (t2, σ2) ->
    no_violation (wglog σ2) (wgws σ2) /\
    (forall e2, e2 ∈ t2 -> reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hwp t2 σ2 Hrtc.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  (* THE SAFETY FORM ([WeakAdequacy.weak_system_adequacy_phi]'s two lines,
     verbatim).  [wp_strong_adequacy] at [NotStuck] hands out [not_stuck],
     which is "reducible OR a value"; [WeakEvLang.eto_val] is constantly
     [None] (the event language has NO values — [eval := Empty_set]), so the
     value disjunct is refuted outright and [not_stuck] IS reducibility. *)
  cut (no_violation (wglog σ2) (wgws σ2) /\
       (forall e : expr weak_ev_lang, e ∈ t2 -> not_stuck e σ2)).
  { intros [Hnv Hns]. split; [exact Hnv|].
    intros e2 He2. destruct (Hns e2 He2) as [[v Hv]|Hred];
      [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ weak_ev_lang NotStuck (epower_fork gen) σ n κs
            t2 σ2 _ (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  (* ---- allocate the ghost state ([WeakAdequacy]'s bundle, unchanged) ---- *)
  iMod (reg_alloc_cpus (wgregs σ) D (enum CPU) (NoDup_enum CPU)) as (f) "Hcpus".
  iMod (ghost_var_alloc (wgdev σ).(duart)) as (γu) "Hu".
  iMod (ghost_var_alloc (wgdev σ).(dplic)) as (γp) "Hp".
  iMod (ghost_var_alloc (wgdev σ).(dvirtio)) as (γv) "Hv".
  iEval (rewrite -Qp.half_half) in "Hu".
  iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
  iEval (rewrite -Qp.half_half) in "Hp".
  iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
  iEval (rewrite -Qp.half_half) in "Hv".
  iDestruct (ghost_var_split with "Hv") as "[HvA HvF]".
  iMod (own_alloc (●ML ([] : list (leibnizO wmsg))
                   ⋅ ◯ML ([] : list (leibnizO wmsg)))) as (γlog) "[Hlga #Hlgf]".
  { apply mono_list_both_valid_L. reflexivity. }
  iMod (ghost_map_alloc (wlat_init (wgimg σ))) as (γlat) "[Hlatauth Hlatel]".
  iMod (ghost_map_alloc (wcds_init (wgimg σ))) as (γcds) "[Hcdsauth Hcdsel]".
  iMod (ghost_var_alloc_halves_cpus ws_init (enum CPU) (NoDup_enum CPU))
    as (γws) "Hwss".
  (* ---- assemble the two instances ---- *)
  set (E0 := RiscvEraGS f 1%positive 1%positive γu γp γv 1%positive 1%positive
               (fun _ => 1%positive) (fun _ => 1%positive)
               (fun _ => 1%positive) (fun _ => 1%positive)
               (fun _ => 1%positive) (fun _ => 1%positive)
               1%positive 1%positive).
  set (HR := RiscvGS Σ
               (RiscvFixedGS Σ Hinv _ _ _ _ _ _ _ _ _ _ _ 1%positive 1%positive _
                  1%positive _ _ 1%positive (fun _ => True%I) 1%positive)
               E0).
  set (HW := WeakGS Σ _ γlog γlat γcds γws).
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  iDestruct (big_sepL_sep with "Hwss") as "[HwsA HwsF]".
  iPoseProof (Hwp HR HW) as "Hwand".
  iMod ("Hwand" with "[Helems Hlatel Hcdsel HwsF HuF HpF HvF]") as "Hwps".
  { iSplitL "Helems".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "Helems". }
    iSplitL "Hlatel Hcdsel".
    { rewrite /wlat_pointsto /wlat_elem /wclean /wcds_el big_sepM_sep.
      iSplitL "Hlatel".
      - iApply (big_sepM_wlat_init
                  (fun z tv => ghost_map_elem γlat z (DfracOwn 1) tv)).
        iExact "Hlatel".
      - iApply (big_sepM_wcds_init
                  (fun z s => ghost_map_elem γcds z (DfracOwn 1) s)).
        iExact "Hcdsel". }
    iSplitL "HwsF".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
      iApply (big_sepL_mono with "HwsF").
      intros k c Hk. iIntros "H".
      iApply (hart_view_intro c ws_init). iExact "H". }
    iSplitR; [iExact "Hlgf"|].
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|iExact "HvF"]. }
  iModIntro.
  iExists
    (fun (σ' : wgstate) (_ : nat) (_ : list eobs) (_ : nat) =>
       (@weak_state_interp Σ HR HW σ')%I),
    (replicate (length (epower_fork gen)) (fun _ : eval => True%I)),
    (fun _ : eval => True%I),
    (@state_interp_mono HasLc weak_ev_lang Σ (@weak_ev_irisGS Σ HR HW)).
  cbv zeta beta.
  iSplitL "Hauths Hlga Hlatauth Hcdsauth HwsA HuA HpA HvA".
  { rewrite /weak_state_interp.
    iSplitR; [iPureIntro; by split|].
    iSplitR.
    { iPureIntro. intros c. rewrite (Hws c) Hlog. apply ws_bounded_init. }
    iSplitR.
    { iPureIntro. rewrite Hlog. apply no_violation_nil. }
    iSplitR.
    { iPureIntro. rewrite Hlog. apply Forall_nil_2. }
    iSplitL "Hauths".
    { rewrite /gregs_interp.
      iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
      iExact "Hauths". }
    iSplitL "HuA HpA HvA".
    { iSplitL "HuA"; [iExact "HuA"|].
      iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
    iSplitL "Hlga".
    { rewrite /wlog_auth Hlog. iExact "Hlga". }
    iSplitL "Hlatauth Hcdsauth".
    { rewrite /wlat_interp.
      iExists (wlat_init (wgimg σ)), (wcds_init (wgimg σ)).
      iFrame "Hlatauth Hcdsauth".
      iSplitR; [iPureIntro; rewrite Hlog; apply wlat_init_agree|].
      iPureIntro. rewrite Hlog. apply wcds_init_agree. }
    rewrite /wws_interp.
    iApply (big_sepS_mono (fun c => wws_auth c ws_init)).
    { intros c _. rewrite /wws_auth (Hws c). done. }
    iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "HwsA". }
  iSplitL "Hwps".
  { rewrite big_sepL2_replicate_r; [|done]. iExact "Hwps". }
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iDestruct (weak_state_interp_export σ2 with "Hsi") as %Hnv.
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. split; [exact Hnv|].
  intros e He. exact (Hns e eq_refl He).
Qed.

(** THE SAFETY FORM, projected — the event-language twin of
    [WeakAdequacy.weak_system_adequacy].  EVERY thread of EVERY reachable
    configuration can take a step: the WP package is a total correctness
    obligation on each node, and the RMW split's RETRY ARM (design §5) is
    what keeps the conditional-write node reducible even when its
    exclusivity window has gone dirty, so no liveness reasoning enters
    here. *)
Corollary weak_ev_adequacy_reducible Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ : wgstate) (D : CPU -> gset register)
    (Hgen : gen = 0%nat)
    (Hpow : wgpow σ = true) (Hgen0 : wggen σ = 0%nat)
    (Hlog : wglog σ = [])
    (Hws : forall c : CPU, wgws σ c = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (wgregs σ c))) ∗
       ([∗ map] a ↦ b ∈ wgimg σ, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       wlog_lb [] ∗
       uart_frag (wgdev σ).(duart) ∗ plic_frag (wgdev σ).(dplic) ∗
       virtio_frag (wgdev σ).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
  forall t2 σ2 e2,
    rtc (@erased_step weak_ev_lang) (epower_fork gen, σ) (t2, σ2) ->
    e2 ∈ t2 ->
    reducible (Λ := weak_ev_lang) e2 σ2.
Proof.
  intros Hwp t2 σ2 e2 Hrtc He2.
  exact (proj2 (weak_ev_adequacy_phi Σ gen σ D Hgen Hpow Hgen0 Hlog Hws Hwp
                  t2 σ2 Hrtc) e2 He2).
Qed.

(* ====================================================================== *)
(** ** 3. THE SUCCESS CRITERION

    [WeakRobust.violation_hart cls_of pub_of n_disk] for the pf machine of the
    S2 route ([WeakEvPf.epf_step], the fabric-shared promise-free machine),
    derived from the φ export above and from S2's correspondence, with ZERO
    GLUE PREMISES.

    Compare what the instruction-atomic route needed for the same conclusion
    ([WeakComposeLang]'s capstones): the per-trace cone premises, the
    per-segment device seam [cone_liftable], the [sail_shaped] /
    [rv64d_live_residue] records, [Hpriv], [Hcq], [Hseip], [cls_canonical],
    the block-cover residue and the hart-restriction side conditions.  NONE of
    them appears below.  The premises here are: the fresh-era clauses on the
    initial state (four machine facts about a booted [wgstate]) and the WP
    package.  There is no shape fact, no liveness fact, no oracle, no cone
    premise, and no simulation.

    WHAT IT IS STATED AT, and why (see [WeakEvPf]'s header for the full
    argument): the fabric-shared machine [epf_run], NOT
    [WeakPromiseBridge.wp_pf_run] over a [wpcfg].  The predicate itself IS
    Layer 1's — [WeakRobust.violation_hart cls_of pub_of NCPU] at the projected
    configuration [ecfg_of] — so the STATEMENT is the one
    [WeakRobustMain.robust_main] consumes; what is missing for Layer 1 to
    consume it is the generalisation of [WeakPromise.wpcfg] to carry a shared
    device component.  THAT is the Layer-1 instantiation point, and it is the
    spike's S2 finding. *)

Definition epf_violation_free_hart (ρ0 : epool * wgstate) : Prop :=
  forall ρ, rtc epf_run ρ0 ρ ->
    ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2).

Theorem weak_ev_pf_violation_free Σ `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ : wgstate) (D : CPU -> gset register)
    (Hgen : gen = 0%nat)
    (Hpow : wgpow σ = true) (Hgen0 : wggen σ = 0%nat)
    (Hlog : wglog σ = [])
    (Hws : forall c : CPU, wgws σ c = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (wgregs σ c))) ∗
       ([∗ map] a ↦ b ∈ wgimg σ, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       wlog_lb [] ∗
       uart_frag (wgdev σ).(duart) ∗ plic_frag (wgdev σ).(dplic) ∗
       virtio_frag (wgdev σ).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
  epf_violation_free_hart (ep_init gen, σ).
Proof.
  intros Hwp ρ2 Hrun.
  (* S2, ⇐ : a pf run of the fabric-shared machine IS an erased run *)
  pose proof (epf_rtc_erased (ep_init gen, σ) ρ2 Hrun) as Herased.
  rewrite /= epool_list_init in Herased.
  (* S3, the φ export *)
  have Hnv : no_violation (wglog ρ2.2) (wgws ρ2.2).
  { exact (proj1 (weak_ev_adequacy_phi Σ gen σ D Hgen Hpow Hgen0 Hlog Hws Hwp
                    (epool_list ρ2.1) ρ2.2 Herased)). }
  (* the layout transport *)
  exact (no_violation_violation_hart ρ2.1 ρ2.2 Hnv).
Qed.

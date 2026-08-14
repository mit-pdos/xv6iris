(** * WeakEvAdequacy.v — the interpretation and the φ export (spike S3)

    Design: [claude-notes/design/weak-memory-event-granular.md]; worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S3).

    [WeakAdequacy.weak_system_adequacy_phi] restated over [WeakEvLang]'s
    event-granular language, and then — this is the point of the whole spike
    — the SUCCESS CRITERION derived from it and from [WeakEvPf]'s
    correspondence with ZERO GLUE PREMISES.

    THE GHOST DESIGN IS [WeakGhost]'s, UNCHANGED.  The state interpretation
    is literally [WeakGhost.weak_state_interp] composed with
    [WeakEvLang.eg_to_wg] — the log auth, the per-hart [wstate] cells, the
    per-byte latest-write map, the C/D/S protocol, the register and device
    ghosts, the [ws_bounded] machine invariant and the φ conjunct all
    transfer verbatim, because [egstate]'s first seven fields ARE [wgstate].
    That is what the projection was put in [WeakEvLang] §1 for, and it is
    why [weak_state_interp_export] — hence the C/D/S-protocol-implies-φ
    argument behind it — is reused AS IS.

    WHAT IS ADDED are the four exclusive points-tos for the σ-resident
    thread state the event granularity introduced (design doc: "New
    exclusive ghosts mirror [reg_pointsto]"), each a halved [ghost_var]
    exactly like [WeakGhost.hart_ws]:

      [hart_prog c m]  — hart [c]'s residual instruction monad;
      [hart_fence c f] — its parked second fence;
      [disk_pend ms]   — the disk's burst buffer;
      [disk_view w]    — the disk agent's own [wstate] ([WeakEvLang] (D4)).

    A leaf owning [hart_prog c m] knows which event comes next, and the
    lifting rule for one event hands it back at the successor monad; that is
    the resource the S4 instruction-chain lemma will thread.  The three are
    EXCLUSIVE (halves), so no two threads can claim the same hart's program.

    ------------------------------------------------------------------------
    SCOPE (deliberate, and the same cuts [WeakAdequacy]'s header records):
    single era, no power thread in the pool, no boot carve, placeholder
    names for the unused [riscvGS] ghosts.  In addition, and specific to
    this file:

      - THE POOL'S WPs ARE A HYPOTHESIS.  §3's theorem takes the client's
        proof of the pool's WPs exactly as [weak_system_adequacy_phi] does,
        with the leaves ABSTRACT — the spike does not build any leaf (that is
        S4/S5).  What is delivered is the invariant-extraction shape: the
        interpretation is established at the initial state, threaded by the
        WP, and READ OFF at every reachable state.
      - THE FRESH-ERA CLAUSES now include the four new slots (every hart at
        an instruction boundary with no parked fence, an empty burst buffer,
        a fresh disk view) — i.e. exactly [WeakEvLang.eboot_facts]. *)
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
(** ** 1. The four new ghosts *)

Class weakEvGpreS (Σ : gFunctors) := WeakEvGpreS {
  wev_pre_progG :: ghost_varG Σ (option (M unit));
  wev_pre_fenceG :: ghost_varG Σ (option (bool * bool * bool * bool));
  wev_pre_pendG :: ghost_varG Σ (list wmsg);
  (* NO [ghost_varG Σ wstate] here — [WeakGhost.weak_pre_wsG] already supplies
     it, and a SECOND instance for the same type makes the two [ghost_var]s
     non-convertible: instance resolution picks whichever it finds first, and
     the resulting mismatch surfaces far away as an [iExact] that "does not
     match goal" on syntactically identical propositions.  The disk's view
     ghost therefore reuses the weak-memory functor. *)
}.

Definition weakEvΣ : gFunctors :=
  #[ ghost_varΣ (option (M unit));
     ghost_varΣ (option (bool * bool * bool * bool));
     ghost_varΣ (list wmsg) ].

Global Instance subG_weakEvGpreS Σ : subG weakEvΣ Σ -> weakEvGpreS Σ.
Proof. intros H. split; try (revert H; solve_inG). Qed.

Class weakEvGS (Σ : gFunctors) := WeakEvGS {
  wev_preGS :: weakEvGpreS Σ;
  (* PER HART, like [WeakGhost.weak_ws_name] *)
  wev_prog_name : CPU -> gname;
  wev_fence_name : CPU -> gname;
  wev_pend_name : gname;
  wev_dws_name : gname;
}.

Section resources.
  Context `{!riscvGS Σ, !weakGS Σ, !weakEvGS Σ}.

  (** *** The residual instruction monad, per hart. *)
  Definition prog_auth (c : CPU) (m : option (M unit)) : iProp Σ :=
    ghost_var (wev_prog_name c) (1/2) m.
  Definition hart_prog (c : CPU) (m : option (M unit)) : iProp Σ :=
    ghost_var (wev_prog_name c) (1/2) m.

  Lemma hart_prog_agree c m m' :
    prog_auth c m -∗ hart_prog c m' -∗ ⌜m' = m⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->. Qed.

  Lemma hart_prog_update c m m' m'' :
    prog_auth c m -∗ hart_prog c m' ==∗ prog_auth c m'' ∗ hart_prog c m''.
  Proof. iApply ghost_var_update_halves. Qed.

  (** *** The parked second fence, per hart. *)
  Definition fence_auth (c : CPU) (f : option (bool * bool * bool * bool))
      : iProp Σ := ghost_var (wev_fence_name c) (1/2) f.
  Definition hart_fence (c : CPU) (f : option (bool * bool * bool * bool))
      : iProp Σ := ghost_var (wev_fence_name c) (1/2) f.

  Lemma hart_fence_agree c f f' :
    fence_auth c f -∗ hart_fence c f' -∗ ⌜f' = f⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->. Qed.

  Lemma hart_fence_update c f f' f'' :
    fence_auth c f -∗ hart_fence c f' ==∗ fence_auth c f'' ∗ hart_fence c f''.
  Proof. iApply ghost_var_update_halves. Qed.

  (** *** The disk's burst buffer and its own view. *)
  Definition pend_auth (ms : list wmsg) : iProp Σ :=
    ghost_var wev_pend_name (1/2) ms.
  Definition disk_pend (ms : list wmsg) : iProp Σ :=
    ghost_var wev_pend_name (1/2) ms.

  Lemma disk_pend_agree ms ms' :
    pend_auth ms -∗ disk_pend ms' -∗ ⌜ms' = ms⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->. Qed.

  Lemma disk_pend_update ms ms' ms'' :
    pend_auth ms -∗ disk_pend ms' ==∗ pend_auth ms'' ∗ disk_pend ms''.
  Proof. iApply ghost_var_update_halves. Qed.

  Definition dws_auth (w : wstate) : iProp Σ :=
    ghost_var wev_dws_name (1/2) w.
  Definition disk_view (w : wstate) : iProp Σ :=
    ghost_var wev_dws_name (1/2) w.

  Lemma disk_view_agree w w' :
    dws_auth w -∗ disk_view w' -∗ ⌜w' = w⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->. Qed.

  Lemma disk_view_update w w' w'' :
    dws_auth w -∗ disk_view w' ==∗ dws_auth w'' ∗ disk_view w''.
  Proof. iApply ghost_var_update_halves. Qed.

  (** *** The added conjunct, and the whole interpretation. *)
  Definition wev_extra (σ : egstate) : iProp Σ :=
    (([∗ set] c ∈ (fin_to_set CPU : gset CPU), prog_auth c (eg_hs σ c)) ∗
     ([∗ set] c ∈ (fin_to_set CPU : gset CPU), fence_auth c (eg_fence σ c)) ∗
     pend_auth (eg_pend σ) ∗ dws_auth (eg_dws σ))%I.

  (** THE STATE INTERPRETATION.  [WeakGhost]'s, composed with the projection,
      plus the four new authorities.  Nothing about the C/D/S protocol, the
      log authority or the per-hart views changes: [egstate]'s first seven
      fields are [wgstate]'s. *)
  Definition weak_ev_state_interp (σ : egstate) : iProp Σ :=
    (weak_state_interp (eg_to_wg σ) ∗ wev_extra σ)%I.

  (** THE φ EXPORT, unchanged: the reachable state's own interpretation
      certifies that no hart's coherence floor has reached a foreign hart's
      unpublished owned store. *)
  Lemma weak_ev_state_interp_export (σ : egstate) :
    weak_ev_state_interp σ ⊢ ⌜no_violation (eglog σ) (egws σ)⌝.
  Proof.
    iIntros "[Hs _]". by iApply (weak_state_interp_export (eg_to_wg σ)).
  Qed.

  (** ... and the focused per-hart facts the (S4) lifting rules will use. *)
  Lemma wev_extra_prog_acc σ (c : CPU) :
    wev_extra σ ⊢ prog_auth c (eg_hs σ c) ∗
      (prog_auth c (eg_hs σ c) -∗ wev_extra σ).
  Proof.
    iIntros "(Hp & $ & $ & $)".
    iDestruct (big_sepS_delete _ _ c with "Hp") as "[Hc Hrest]";
      [apply elem_of_fin_to_set|].
    iFrame "Hc". iIntros "Hc".
    iApply (big_sepS_delete _ _ c); [apply elem_of_fin_to_set|]. iFrame.
  Qed.
End resources.

(* ====================================================================== *)
(** ** 2. The [irisGS] instance and the Φ-free WP

    [WeakGhost.weak_irisGS]'s twin at the event language.  The notation is
    [EWP], distinct from SC's [WP] and from [WeakGhost]'s [WWP], for exactly
    the reason [WeakGhost]'s header gives: all three languages' [expr] is
    [RiscvLang.mexpr] up to conversion, so a shared token would let a
    statement elaborate at the wrong language and still compile. *)
Global Program Instance weak_ev_irisGS `{!riscvGS Σ, !weakGS Σ, !weakEvGS Σ}
    : irisGS weak_ev_lang Σ := {
  iris_invGS := riscvF_invGS;
  state_interp σ _ _ _ := weak_ev_state_interp σ;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

Definition ewp_triv `{!riscvGS Σ, !weakGS Σ, !weakEvGS Σ}
    (E : coPset) (e : expr weak_ev_lang) : iProp Σ :=
  wp NotStuck E e (fun _ => True%I).

Notation "'EWP' e @ E" := (ewp_triv E e%E) (at level 20, e at level 20) : bi_scope.

(* ====================================================================== *)
(** ** 3. The φ export at the language level *)

Theorem weak_ev_adequacy_phi Σ `{!riscvGpreS Σ, !weakGpreS Σ, !weakEvGpreS Σ}
    (gen : nat) (σ : egstate) (D : CPU -> gset register)
    (Hgen : gen = 0%nat)
    (* THE FRESH ERA — [WeakEvLang.eboot_facts]' machine-side clauses *)
    (Hpow : egpow σ = true) (Hgen0 : eggen σ = 0%nat)
    (Hlog : eglog σ = [])
    (Hws : forall c : CPU, egws σ c = ws_init)
    (Hhs : forall c : CPU, eg_hs σ c = None)
    (Hfn : forall c : CPU, eg_fence σ c = None)
    (Hpend : eg_pend σ = [])
    (Hdws : eg_dws σ = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ) (HE : weakEvGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (egregs σ c))) ∗
       ([∗ map] a ↦ b ∈ egimg σ, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_prog c None) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_fence c None) ∗
       disk_pend [] ∗ disk_view ws_init ∗
       wlog_lb [] ∗
       uart_frag (egdev σ).(duart) ∗ plic_frag (egdev σ).(dplic) ∗
       virtio_frag (egdev σ).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ ecpu_pool gen, EWP e @ ⊤)) ->
  forall t2 σ2,
    rtc (@erased_step weak_ev_lang) (ecpu_pool gen, σ) (t2, σ2) ->
    no_violation (eglog σ2) (egws σ2).
Proof.
  intros Hwp t2 σ2 Hrtc.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  eapply (wp_strong_adequacy Σ weak_ev_lang NotStuck (ecpu_pool gen) σ n κs
            t2 σ2 _ (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  (* ---- allocate the ghost state (WeakAdequacy's bundle, plus the four) ---- *)
  iMod (reg_alloc_cpus (egregs σ) D (enum CPU) (NoDup_enum CPU)) as (f) "Hcpus".
  iMod (ghost_var_alloc (egdev σ).(duart)) as (γu) "Hu".
  iMod (ghost_var_alloc (egdev σ).(dplic)) as (γp) "Hp".
  iMod (ghost_var_alloc (egdev σ).(dvirtio)) as (γv) "Hv".
  iEval (rewrite -Qp.half_half) in "Hu".
  iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
  iEval (rewrite -Qp.half_half) in "Hp".
  iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
  iEval (rewrite -Qp.half_half) in "Hv".
  iDestruct (ghost_var_split with "Hv") as "[HvA HvF]".
  iMod (own_alloc (●ML ([] : list (leibnizO wmsg))
                   ⋅ ◯ML ([] : list (leibnizO wmsg)))) as (γlog) "[Hlga #Hlgf]".
  { apply mono_list_both_valid_L. reflexivity. }
  iMod (ghost_map_alloc (wlat_init (egimg σ))) as (γlat) "[Hlatauth Hlatel]".
  iMod (ghost_map_alloc (wcds_init (egimg σ))) as (γcds) "[Hcdsauth Hcdsel]".
  iMod (ghost_var_alloc_halves_cpus ws_init (enum CPU) (NoDup_enum CPU))
    as (γws) "Hwss".
  (* THE FOUR NEW ONES *)
  iMod (ghost_var_alloc_halves_cpus (None : option (M unit))
          (enum CPU) (NoDup_enum CPU)) as (γpr) "Hprs".
  iMod (ghost_var_alloc_halves_cpus (None : option (bool*bool*bool*bool))
          (enum CPU) (NoDup_enum CPU)) as (γfn) "Hfns".
  iMod (ghost_var_alloc ([] : list wmsg)) as (γpe) "Hpe".
  iEval (rewrite -Qp.half_half) in "Hpe".
  iDestruct (ghost_var_split with "Hpe") as "[HpeA HpeF]".
  iMod (ghost_var_alloc ws_init) as (γdw) "Hdw".
  iEval (rewrite -Qp.half_half) in "Hdw".
  iDestruct (ghost_var_split with "Hdw") as "[HdwA HdwF]".
  (* ---- assemble the three instances ---- *)
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
  set (HE := WeakEvGS Σ _ γpr γfn γpe γdw).
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  iDestruct (big_sepL_sep with "Hwss") as "[HwsA HwsF]".
  iDestruct (big_sepL_sep with "Hprs") as "[HprA HprF]".
  iDestruct (big_sepL_sep with "Hfns") as "[HfnA HfnF]".
  iPoseProof (Hwp HR HW HE) as "Hwand".
  iMod ("Hwand" with
        "[Helems Hlatel Hcdsel HwsF HprF HfnF HpeF HdwF HuF HpF HvF]")
    as "Hwps".
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
    iSplitL "HprF".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "HprF". }
    iSplitL "HfnF".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "HfnF". }
    iSplitL "HpeF"; [iExact "HpeF"|].
    iSplitL "HdwF"; [iExact "HdwF"|].
    iSplitR; [iExact "Hlgf"|].
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|iExact "HvF"]. }
  iModIntro.
  iExists
    (fun (σ' : egstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (@weak_ev_state_interp Σ HR HW HE σ')%I),
    (replicate (length (ecpu_pool gen)) (fun _ : mval => True%I)),
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc weak_ev_lang Σ (@weak_ev_irisGS Σ HR HW HE)).
  cbv zeta beta.
  iSplitL "Hauths Hlga Hlatauth Hcdsauth HwsA HprA HfnA HpeA HdwA HuA HpA HvA".
  { rewrite /weak_ev_state_interp /wev_extra /weak_state_interp.
    iSplitR "HprA HfnA HpeA HdwA".
    - iSplitR; [iPureIntro; by split|].
      iSplitR.
      { iPureIntro. intros c. rewrite /= (Hws c) Hlog. apply ws_bounded_init. }
      iSplitR.
      { iPureIntro. rewrite /= Hlog. apply no_violation_nil. }
      iSplitR.
      { iPureIntro. rewrite /= Hlog. apply Forall_nil_2. }
      iSplitL "Hauths".
      { rewrite /gregs_interp.
        iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
        iExact "Hauths". }
      iSplitL "HuA HpA HvA".
      { iSplitL "HuA"; [iExact "HuA"|].
        iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
      iSplitL "Hlga".
      { rewrite /wlog_auth /= Hlog. iExact "Hlga". }
      iSplitL "Hlatauth Hcdsauth".
      { rewrite /wlat_interp /=.
        iExists (wlat_init (egimg σ)), (wcds_init (egimg σ)).
        iFrame "Hlatauth Hcdsauth".
        iSplitR; [iPureIntro; rewrite Hlog; apply wlat_init_agree|].
        iPureIntro. rewrite Hlog. apply wcds_init_agree. }
      rewrite /wws_interp /=.
      iApply (big_sepS_mono (fun c => wws_auth c ws_init)).
      { intros c _. rewrite /wws_auth (Hws c). done. }
      iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "HwsA".
    - iSplitL "HprA".
      { iApply (big_sepS_mono (fun c => prog_auth c None)).
        { intros c _. rewrite /prog_auth (Hhs c). done. }
        iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
        iExact "HprA". }
      iSplitL "HfnA".
      { iApply (big_sepS_mono (fun c => fence_auth c None)).
        { intros c _. rewrite /fence_auth (Hfn c). done. }
        iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
        iExact "HfnA". }
      iSplitL "HpeA".
      { rewrite /pend_auth Hpend. iExact "HpeA". }
      rewrite /dws_auth Hdws. iExact "HdwA". }
  iSplitL "Hwps".
  { rewrite big_sepL2_replicate_r; [|done]. iExact "Hwps". }
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iDestruct (weak_ev_state_interp_export σ2 with "Hsi") as %Hnv.
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. exact Hnv.
Qed.

(* ====================================================================== *)
(** ** 4. THE SUCCESS CRITERION

    [WeakRobust.pf_violation_free_hart cls_of pub_of n_disk] for the pf
    machine of the S2 route ([WeakEvPf.epf_step], the fabric-shared
    promise-free machine), derived from the φ export above and from S2's
    correspondence, with ZERO GLUE PREMISES.

    Compare what the instruction-atomic route needed for the same conclusion
    ([WeakComposeLang]'s capstones): the per-trace cone premises, the
    per-segment device seam [cone_liftable], the [sail_shaped] /
    [rv64d_live_residue] records, [Hpriv], [Hcq], [Hseip], [cls_canonical],
    the block-cover residue and the hart-restriction side conditions.  NONE
    of them appears below.  The premises here are: the fresh-era clauses on
    the initial state (machine facts about a booted [egstate]) and the WP
    package.  There is no shape fact, no liveness fact, no oracle, no cone
    premise, and no simulation.

    WHAT IT IS STATED AT, and why (see [WeakEvPf]'s header for the full
    argument): the fabric-shared machine [epf_run], NOT
    [WeakPromiseBridge.wp_pf_run] over a [wpcfg].  The predicate itself IS
    Layer 1's — [WeakRobust.violation_hart cls_of pub_of NCPU] at the
    projected configuration [ecfg_of σ] — so the STATEMENT is the one
    [WeakRobustMain.robust_main] consumes; what is missing for Layer 1 to
    consume it is the generalisation of [WeakPromise.wpcfg] to carry a
    shared device component.  THAT is the Layer-1 instantiation point, and
    it is the spike's S2 finding. *)

Definition epf_violation_free_hart (σ0 : egstate) : Prop :=
  forall σ, rtc epf_run σ0 σ ->
    ~ violation_hart cls_of pub_of n_disk (ecfg_of σ).

Theorem weak_ev_pf_violation_free Σ
    `{!riscvGpreS Σ, !weakGpreS Σ, !weakEvGpreS Σ}
    (gen : nat) (σ : egstate) (D : CPU -> gset register)
    (Hgen : gen = 0%nat)
    (Hpow : egpow σ = true) (Hgen0 : eggen σ = 0%nat)
    (Hlog : eglog σ = [])
    (Hws : forall c : CPU, egws σ c = ws_init)
    (Hhs : forall c : CPU, eg_hs σ c = None)
    (Hfn : forall c : CPU, eg_fence σ c = None)
    (Hpend : eg_pend σ = [])
    (Hdws : eg_dws σ = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ) (HE : weakEvGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (egregs σ c))) ∗
       ([∗ map] a ↦ b ∈ egimg σ, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_prog c None) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_fence c None) ∗
       disk_pend [] ∗ disk_view ws_init ∗
       wlog_lb [] ∗
       uart_frag (egdev σ).(duart) ∗ plic_frag (egdev σ).(dplic) ∗
       virtio_frag (egdev σ).(dvirtio)
       ={⊤}=∗ ([∗ list] e ∈ ecpu_pool gen, EWP e @ ⊤)) ->
  epf_violation_free_hart σ.
Proof.
  intros Hwp σ2 Hrun.
  (* S2, ⇐ : a pf run of the fabric-shared machine IS an erased run *)
  have Hlive : ethread_live σ gen by rewrite /ethread_live Hgen Hgen0; split.
  pose proof (epf_rtc_erased gen σ σ2 Hlive Hrun) as Herased.
  (* S3, the φ export *)
  have Hnv : no_violation (eglog σ2) (egws σ2).
  { eapply (weak_ev_adequacy_phi Σ gen σ D Hgen Hpow Hgen0 Hlog Hws Hhs Hfn
              Hpend Hdws Hwp (ecpu_pool gen) σ2 Herased). }
  (* the layout transport *)
  exact (no_violation_violation_hart σ2 Hnv).
Qed.

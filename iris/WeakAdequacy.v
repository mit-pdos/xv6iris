(** * WeakAdequacy.v — whole-system adequacy over the weak machine (M1c)

    [RiscvAdequacy.riscv_system_adequacy] restated over
    [WeakLang.weak_riscv_lang]: pick a hart list [cs] and a FRESH-ERA weak
    state [g] (power on, generation 0, EMPTY log, every hart at [ws_init]);
    if the caller can prove the pool's WPs from the initial resources, then
    every configuration reachable from
    [(LoopE 0 <$> cs) ++ [UartLoop; DiskLoop; PlicLoop]] is reducible.  As in
    the SC theorem the conclusion is META-level ([to_val] is constantly
    [None], so not-stuck IS reducible and the postconditions are vacuous),
    and the device-thread WPs are PREMISES — [WeakExec] supplies the three
    device lifting rules they are proved with, but no device invariant is in
    scope at M1c (devices are M5).

    THE INITIAL RESOURCE BUNDLE, against [riscv_system_adequacy]'s:

      - per-hart [reg_pointsto_at] over the caller's register set [D c] —
        VERBATIM the SC bundle's (the register ghosts are reused unchanged);
      - one [wlat_pointsto (pa_z a) 1 0 b] per byte [a ↦ b] of the
        era-initial image — the weak analogue of "one [a ↦ₘ b] per initial
        memory byte", at timestamp 0 (nothing has been written yet);
      - one [hart_view c] per hart — the client half of that hart's
        weak-state cell, PAIRED with the monotone shadow allocated at the
        same [ws_init] and with the value hidden.  (It used to be the bare
        [hart_ws c ws_init]; the pairing is what lets everything above a
        leaf stop naming [wstate]s.  A client that does want the value back
        cannot have it — but it can have any floor, persistently, via
        [WeakGhost.hart_view_lb].)
      - [uart_frag] / [plic_frag] / [virtio_frag] — VERBATIM;
      - [wlog_lb []] — the (persistent) snapshot of the empty era log.

    SCOPE CUTS, all deliberate (see [WeakGhost]'s header for the ghost-state
    ones):

      - SINGLE ERA / NO POWER THREAD.  [PowerLoopE] is not in the pool, and
        the state interpretation pins power-on/generation-0 — exactly the
        stage [riscv_system_adequacy] was at before the power layer was
        layered on top of it ([RiscvAdequacy.riscv_power_adequacy] is the
        analogous later step here).
      - NO BOOT CARVE.  The SC theorem splits the initial image at
        [text_end] into persisted [↦ₓ□] text and owned [↦ₘ] data (needing
        [Hram] and the [BootCarve] library).  This one hands the client every
        byte as an exclusive weak points-to; the carve is M2's business,
        since it is stated over the [↦ₘ]/[↦ₓ□] surface that M2 defines.
      - THE UNUSED [riscvGS] GHOSTS GET PLACEHOLDER NAMES.  [riscvGS] carries
        the whole SC memory/crash/kmap apparatus; the weak state
        interpretation uses only its register and device ghosts.  The rest
        (heap+meta, kmap, kpt, strans, sie, park, disk image, generation,
        started, registry, FS tie) are given [1%positive] and nothing —
        neither the state interpretation nor the client bundle — owns any
        resource at those names, so nothing can be derived from them.  (The
        same device [RiscvAdequacy] already uses for the proc-slot park
        family when [nproc = 0].)
*)
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
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakViewMono.
Require Import WeakGhost.
Require Import WeakExec.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvAdequacy.   (* [riscvGpreS]/[riscvΣ], [reg_alloc_cpus],
                                   [ghost_var_alloc_halves_cpus] and the
                                   [enum]-to-set bridge, reused verbatim *)

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The initial thread pool: one [LoopE] per chosen hart, plus the three  *)
(*    device execution contexts.  No power thread (see the header).         *)
(* ---------------------------------------------------------------------- *)

Definition wcpu_pool `{GEN : GenId} (cs : list CPU)
    : list (expr weak_riscv_lang) :=
  (LoopE gen_id <$> cs) ++ [UartLoop; DiskLoop; PlicLoop].

(* ---------------------------------------------------------------------- *)
(* 2. The theorem.                                                          *)
(* ---------------------------------------------------------------------- *)

Theorem weak_system_adequacy Σ `{!riscvGpreS Σ, !weakGpreS Σ, !sieG Σ}
    `{GEN : GenId}
    (cs : list CPU) (g : wgstate) (D : CPU -> gset register)
    (Hgid : gen_id = 0%nat)
    (* THE FRESH ERA (WeakLang.wboot_facts's four machine-side clauses):
       power on, generation 0, nothing written, nobody has observed
       anything.  A booted [wgstate] satisfies all four. *)
    (Hpow : wgpow g = true) (Hgen0 : wggen g = 0%nat)
    (Hlog : wglog g = [])
    (Hws : forall c : CPU, wgws g c = ws_init) :
  (forall (HR : riscvGS Σ) (HW : weakGS Σ),
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1)
              (register_lookup r (wgregs g c))) ∗
       ([∗ map] a ↦ b ∈ wgimg g, wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), hart_view c) ∗
       wlog_lb [] ∗
       uart_frag (wgdev g).(duart) ∗ plic_frag (wgdev g).(dplic) ∗
       virtio_frag (wgdev g).(dvirtio)
       ={⊤}=∗
       ([∗ list] c ∈ cs,
          WWP (LoopE gen_id c) @ ⊤) ∗
       WWP UartLoop @ ⊤ ∗
       WWP DiskLoop @ ⊤ ∗
       WWP PlicLoop @ ⊤) ->
  forall t2 g2 e2,
    rtc erased_step (wcpu_pool cs, g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := weak_riscv_lang) e2 g2.
Proof.
  intros Hwp t2 g2 e2 Hrtc He2.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  cut (forall e : expr weak_riscv_lang, e ∈ t2 -> not_stuck e g2).
  { intros Hns. destruct (Hns e2 He2) as [[v Hv]|Hred];
      [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ weak_riscv_lang NotStuck (wcpu_pool cs) g n κs
            t2 g2 _ (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  (* ---- allocate the ghost state ---- *)
  (* the per-hart register maps (reused verbatim from the SC adequacy) *)
  iMod (reg_alloc_cpus (wgregs g) D (enum CPU) (NoDup_enum CPU)) as (f) "Hcpus".
  (* the device fabric, in the halves pattern *)
  iMod (ghost_var_alloc (wgdev g).(duart)) as (γu) "Hu".
  iMod (ghost_var_alloc (wgdev g).(dplic)) as (γp) "Hp".
  iMod (ghost_var_alloc (wgdev g).(dvirtio)) as (γv) "Hv".
  iEval (rewrite -Qp.half_half) in "Hu".
  iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
  iEval (rewrite -Qp.half_half) in "Hp".
  iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
  iEval (rewrite -Qp.half_half) in "Hv".
  iDestruct (ghost_var_split with "Hv") as "[HvA HvF]".
  (* THE WEAK GHOSTS: the log (mono-list, empty), the per-byte latest-write
     map (every byte of the era-initial image at timestamp 0), and one
     halved weak-state cell per hart (at [ws_init]) *)
  iMod (own_alloc (●ML ([] : list (leibnizO wmsg))
                   ⋅ ◯ML ([] : list (leibnizO wmsg)))) as (γlog) "[Hlga #Hlgf]".
  { apply mono_list_both_valid_L. reflexivity. }
  iMod (ghost_map_alloc (wlat_init (wgimg g))) as (γlat) "[Hlatauth Hlatel]".
  iMod (ghost_var_alloc_halves_cpus ws_init (enum CPU) (NoDup_enum CPU))
    as (γws) "Hwss".
  (* the MONOTONE SHADOW of the cell just allocated: one [wview_names] per
     hart, at the SAME [ws_init], which is what makes the [hart_view]
     pairing below true at boot. *)
  iMod (ws_alloc_cpus ws_init (enum CPU) (NoDup_enum CPU)) as (γvw) "Hvws".
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
  set (HW := WeakGS Σ _ γlog γlat γws γvw).
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  iDestruct (big_sepL_sep with "Hwss") as "[HwsA HwsF]".
  (* run the caller's proof to obtain the WPs *)
  iPoseProof (Hwp HR HW) as "Hwand".
  iMod ("Hwand" with "[Helems Hlatel HwsF Hvws HuF HpF HvF]")
    as "[Hwps (Hwpu & Hwpd & Hwpp)]".
  { iSplitL "Helems".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "Helems". }
    iSplitL "Hlatel".
    { iApply (big_sepM_wlat_init
                (fun z tv => ghost_map_elem γlat z (DfracOwn 1) tv)).
      iExact "Hlatel". }
    iSplitL "HwsF Hvws".
    { iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
      (* pair each hart's exact half with its monotone shadow, both at
         [ws_init], and hide the value — that IS [hart_view] *)
      iDestruct (big_sepL_sep_2 with "HwsF Hvws") as "H".
      iApply (big_sepL_mono with "H").
      intros k c Hk. iIntros "[H1 H2]".
      rewrite /hart_view /hart_ws /=. iExists ws_init. iFrame. }
    iSplitR; [iExact "Hlgf"|].
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|iExact "HvF"]. }
  iModIntro.
  iExists
    (fun (g' : wgstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (@weak_state_interp Σ HR HW g')%I),
    (replicate (length (wcpu_pool cs)) (fun _ : mval => True%I)),
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc weak_riscv_lang Σ (@weak_irisGS Σ HR HW)).
  cbv zeta beta.
  iSplitL "Hauths Hlga Hlatauth HwsA HuA HpA HvA".
  { (* the initial state interpretation *)
    rewrite /weak_state_interp.
    iSplitR; [iPureIntro; by split|].
    (* the fresh era: every hart is at [ws_init] over an EMPTY log *)
    iSplitR.
    { iPureIntro. intros c. rewrite (Hws c) Hlog. apply ws_bounded_init. }
    iSplitR.
    { iPureIntro. rewrite Hlog. apply Forall_nil_2. }
    iSplitL "Hauths".
    { rewrite /gregs_interp. iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)).
      iExact "Hauths". }
    iSplitL "HuA HpA HvA".
    { iSplitL "HuA"; [iExact "HuA"|].
      iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
    iSplitL "Hlga".
    { rewrite /wlog_auth Hlog. iExact "Hlga". }
    iSplitL "Hlatauth".
    { rewrite /wlat_interp. iExists (wlat_init (wgimg g)).
      iSplitL "Hlatauth"; [iExact "Hlatauth"|].
      iPureIntro. rewrite Hlog. apply wlat_init_agree. }
    rewrite /wws_interp.
    iApply (big_sepS_mono (fun c => wws_auth c ws_init)).
    { intros c _. rewrite /wws_auth (Hws c). done. }
    iApply (@RiscvAdequacy.big_sepL_enum_to_set (iPropI Σ)). iExact "HwsA". }
  iSplitL "Hwps Hwpu Hwpd Hwpp".
  { rewrite big_sepL2_replicate_r; [|done].
    rewrite /wcpu_pool big_sepL_app big_sepL_fmap /=.
    iSplitL "Hwps"; [iExact "Hwps"|].
    iSplitL "Hwpu"; [iExact "Hwpu"|].
    iSplitL "Hwpd"; [iExact "Hwpd"|].
    iSplitL "Hwpp"; [iExact "Hwpp"|done]. }
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. intros e He. exact (Hns e eq_refl He).
Qed.

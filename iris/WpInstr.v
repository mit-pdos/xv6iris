(* WpInstr.v -- THE M-MODE INSTRUCTION WRAPPER.

   [wp_instr] is the rule the 135 leaf call sites see, and [mm_cycle] is the
   M-mode instance of [HartMCycle.swp_exec_step_decode_execute] it is built
   on.  The fetch-shape dispatch underneath is
   [WpInstrRun.swp_run_hart_active_instr], shared with the config-writing
   wrapper.  Split out of [InstrBytes] purely so that iterating on the
   wrapper does not re-elaborate the [instr] / [instr_bytes] / [decode_hval]
   definitions and the frame bridges, which are stable. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import HartSwp HartLift HartLift2 HartSpan HartSpanChar
        HartRegNode HartMCycle HartMRun HartMFrame RegFile WpGpr.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec MinstretInv.
Require Import MstatusFacts.
Require Import KptPt KMap.
Local Open Scope Z_scope.

Require Import InstrBytes WpInstrRun.

Section WpInstr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* every tower lookup, in one tactic: the [mm_rs_*] equations are complete,
     so any premise of the form [register_lookup r (mm_rs ..) = v] closes. *)
  Local Ltac mmrs :=
    by rewrite ?mm_rs_PC ?mm_rs_nPC ?mm_rs_ms ?mm_rs_mi ?mm_rs_cy ?mm_rs_ti
       ?mm_rs_ip ?mm_rs_priv ?mm_rs_mst ?mm_rs_hart ?mm_rs_pcfg ?mm_rs_mc
       ?mm_rs_micfg ?mm_rs_misa ?mm_rs_sec ?mm_rs_pma ?mm_rs_htif ?mm_rs_elp
       ?mm_rs_senv.

  (* ==================================================================== *)
  (* mm_cycle -- the M-MODE INSTANCE of [swp_exec_step_decode_execute].     *)
  (*                                                                      *)
  (* All it adds is the two bundle<->frame bridges.  Everything about the   *)
  (* cycle itself (boundary, interrupt check, minstret, tick, PC commit)    *)
  (* is in the generic rule, which knows nothing about privilege regimes;   *)
  (* the S-mode wrapper writes its own thirty-line twin of THIS and reuses  *)
  (* that rule unchanged.                                                  *)
  (* ==================================================================== *)
  Lemma mm_cycle (pc npc : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (Psi : iProp Σ)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    eq_vec (_get_Mstatus_MIE mst0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    mstatus_kernel_facts mst0 ->
    hw_config -∗
    hreg_frame (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
    hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
    (hreg_frame (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗ hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ w : mword 32,
                    ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                    hreg_frame (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw ∗
                    hreg_frame_ro (mm_Df dq) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro ∗ Psi)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pc_is npc -∗ Psi -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HmIE HMPRV HSXL HKF.
    iIntros "#Hhw Hrw Hro Hbody Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (swp_exec_step_decode_execute mm_Drw mm_Dro (mm_Df dq)
              (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) Psi
              mm_disj mm_w_cy mm_w_ti mm_w_ip mm_in_priv mm_in_hart mm_in_mc
              mm_in_micfg mm_w_mi mm_in_mi mm_w_ms mm_in_ms mm_w_PC mm_in_PC
              mm_in_nPC ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
              (mm_pre_agree pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0)
              with "Hcert Hrw Hro Hbody [Hcont]").
    iNext. iIntros (rs3) "%Hag Hrw Hro HPsi".
    destruct Hag as (mi & Hag).
    pose proof (mm_tick_agree pc npc ms (minstret_inc_flag mc micfg)
                  cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 senv0
                  pmar0 elp0 mi rs3 Hag) as Hag'.
    iDestruct (mm_rw_ext _ _ Hag' with "Hrw") as "Hrw".
    iDestruct (mm_ro_ext dq _ _ Hag' with "Hro") as "Hro".
    iDestruct (mm_frames_elim dq npc pmpcfg0 mi (minstret_inc_flag mc micfg)
                 _ _ _ mst0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                 HmIE HMPRV HSXL HKF with "Hhw Hrw Hro")
      as "(Hmm & Hpmpc & Hpc)".
    iApply ("Hcont" with "Hmm Hpmpc Hpc HPsi").
  Qed.

  (* ==================================================================== *)
  (* wp_instr_ex -- THE ENGINE BOTH WRAPPERS' LEAVES REACH.                *)
  (*                                                                      *)
  (* ONE call to the cycle rule, with the fetch-shape dispatch underneath  *)
  (* it, where [instr_lift] used to sit.                                   *)
  (*                                                                      *)
  (* The post-GPR-file is EXISTENTIAL.  [csrr rd, time] reads mtime,
     which the clock tick writes -- so it is in the WRAPPER's writable frame
     and no leaf can hold a fraction of it to pin the value before the step.
     Such a leaf cannot name its own post-file, which is what [wp_instr]'s
     [m'] parameter demands; here the obligation produces the file and the
     continuation quantifies it, with the leaf's rider [R] indexed by it.
     [wp_instr] is the instance that names the file. *)
  Lemma wp_instr_ex (pc npc : mword 64) (is_rvc : bool) (i : instruction)
      (m : regfile) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (R : regfile -> iProp Σ) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (* PC rides along read-only: AUIPC and JAL compute from it, and the
       instruction never writes it (tick_pc does, after the instruction). *)
    (gpr_file m -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                   (R_bitvector_64 PC) ↦ᵣ pc ∗
                   (R_bitvector_64 nextPC) ↦ᵣ npc ∗
                   ∃ mf : regfile, gpr_file mf ∗ R mf)) -∗
    ▷ (∀ mf : regfile, mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pc_is npc -∗ gpr_file mf -∗ R mf -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp Hstat.
    iIntros "Hmm Hpmpc Hpc Hgpr Hinstr Hex Hcont".
    iDestruct (mm_frames_intro dq pc pmpcfg0 with "Hmm Hpmpc Hpc")
      as "[#Hhw Hfr]".
    iDestruct "Hfr" as (ms bmi cy ti ip mst0 mc micfg misa0 mseccfg0 senv0
        pmar0 elp0)
      "(%HmIE & %HMPRV & %HSXL & %HKF & %HmS & %HmC & %HmA & %Hmisaval &
        %Hsecval & %Hpmaall & %Helpnp & Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (hw_config_kmap with "Hhw") as "#Hkm".
    (* ONE cycle step.  The fetch-shape dispatch is below it, not above. *)
    iApply (mm_cycle pc npc pmpcfg0 (∃ mf : regfile, gpr_file mf ∗ R mf)%I
              ms bmi cy ti ip mst0
              mc micfg misa0 mseccfg0 senv0 pmar0 elp0 HmIE HMPRV HSXL HKF
              with "Hhw Hrw Hro [Hgpr Hinstr Hex] [Hcont]").
    2:{ iNext. iIntros "Hmm Hpmpc Hpc HEx".
        iDestruct "HEx" as (mf) "[Hgpr HR]".
        iApply ("Hcont" with "Hmm Hpmpc Hpc Hgpr HR"). }
    (* the two pure facts the dispatch wants, at the [wrap_pre] file *)
    assert (Hdok : decode_ok (mm_Drw ∪ mm_Dro) (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)).
    { rewrite /decode_ok. split_and!.
      - exact mm_in_priv.
      - exact mm_in_misa.
      - rewrite mm_rs_priv. vm_compute. reflexivity.
      - rewrite mm_rs_misa. exact HmC.
      - rewrite mm_rs_misa. exact HmA.
      - rewrite mm_rs_misa. exact Hmisaval.
      - left. split_and!.
        + exact mm_in_sec.
        + mmrs.
        + rewrite mm_rs_sec. exact Hsecval. }
    pose proof (hfrun_lpad (mm_Drw ∪ mm_Dro) mm_Drw (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                  mm_in_elp ltac:(rewrite mm_rs_elp; exact Helpnp)) as Hlp.
    iIntros "Hrw Hro".
    iApply (swp_run_hart_active_instr mm_Drw mm_Dro (mm_Df dq)
              (mm_rs pc pc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) (mm_rs pc npc ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) pc is_rvc i pmar0 pmpcfg0 (∃ mf : regfile, gpr_file mf ∗ R mf)%I
              mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
              mm_in_pma mm_in_pcfg mm_in_htif
              ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
              ltac:(rewrite mm_rs_misa; exact HmS)
              ltac:(rewrite mm_rs_misa; exact HmC)
              ltac:(rewrite mm_rs_mst; exact HmIE)
              Hpmp Hpmaall Hstat Hdok Hlp
              with "Hcert Hkm Hinstr Hrw Hro [Hgpr Hex]").
    (* the ONE nextPC transport, at the symbolic width: [mm_npc_agree] is
       stated for an arbitrary written value, so the four shapes need not be
       apart here. *)
    iIntros "Hrw Hro".
    pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg) cy ti ip
                   mst0 pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                   (add_vec_int pc (if is_rvc then 2 else 4))) as Hnp.
    iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
    iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
    iDestruct (mm_rw_open with "Hrw")
      as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
    iApply (swp_mono with "[Hms Hmi Hcy Hti Hip Hro] [-]");
      [| iApply ("Hex" with "Hgpr HPC HnPC") ].
    iIntros (u) "(-> & HPC & HnPC & HEx)".
    iSplitR; [done|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
    { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
    iSplitL "Hro".
    { iApply (mm_ro_ext' dq _ _
                (mm_ro_nPC pc (add_vec_int pc (if is_rvc then 2 else 4)) npc
                   ms (minstret_inc_flag mc micfg) cy ti ip mst0 pmpcfg0 mc
                   micfg misa0 mseccfg0 senv0 pmar0 elp0) with "Hro"). }
    iFrame "HEx".
  Qed.

  (* ==================================================================== *)
  (* wp_instr -- THE WRAPPER THE 135 LEAF CALL SITES SEE.                  *)
  (*                                                                      *)
  (* [wp_instr_ex] at a NAMED post-file.  Same surface as before:          *)
  (* [mmode_config] / [pmpcfg_n] / [pc_is] / [gpr_file] / [instr] in, the  *)
  (* same four back in the continuation.  What changed relative to the     *)
  (* exec-based rule is the OBLIGATION -- one [swp] over [execute i] at    *)
  (* the caller's own resources, instead of handing the caller ALL of      *)
  (* sigma and asking for a successor state in one fupd, which per-node    *)
  (* stepping invalidates.                                                *)
  (* ==================================================================== *)
  Lemma wp_instr (pc npc : mword 64) (is_rvc : bool) (i : instruction)
      (m m' : regfile) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (R : iProp Σ) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (* PC rides along read-only: AUIPC and JAL compute from it, and the
       instruction never writes it (tick_pc does, after the instruction). *)
    (gpr_file m -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m' ∗
                   (R_bitvector_64 PC) ↦ᵣ pc ∗
                   (R_bitvector_64 nextPC) ↦ᵣ npc ∗ R)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pc_is npc -∗ gpr_file m' -∗ R -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp Hstat.
    iIntros "Hmm Hpmpc Hpc Hgpr Hinstr Hex Hcont".
    iApply (wp_instr_ex pc npc is_rvc i m pmpcfg0
              (fun mf => ⌜mf = m'⌝ ∗ R)%I Hpmp Hstat
              with "Hmm Hpmpc Hpc Hgpr Hinstr [Hex] [Hcont]").
    - iIntros "Hf HPC HnPC".
      iApply (swp_mono with "[] [-]"); [| iApply ("Hex" with "Hf HPC HnPC") ].
      iIntros (e) "(-> & Hf & HPC & HnPC & HR)".
      iSplitR; [done|]. iFrame "HPC HnPC".
      iExists m'. iFrame "Hf HR". done.
    - iNext. iIntros (mf) "Hmm Hpmpc Hpc Hf [-> HR]".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hf HR").
  Qed.

End WpInstr.

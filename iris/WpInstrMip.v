(* WpInstrMip.v -- THE M-MODE INSTRUCTION WRAPPER THAT LENDS [mip].

   [WpInstr.wp_instr] cannot lend mip.  mip sits in the cycle wrapper's
   WRITABLE frame [HartMFrame.mm_Drw] (the clock tick writes it), and
   [WpInstr.mm_cycle] is built on
   [HartMCycle.swp_exec_step_decode_execute], whose post-file [rsB] is a
   PARAMETER -- so the body cannot CHOOSE the value mip lands on.  Exactly
   one leaf needs to: [csrw stimecmp] runs [clint_dispatch], which refreshes
   mip from the CLINT out of registers no leaf can own.

   The fix is the predicate-form engines: [HartStepAny.swp_exec_step_any]
   (post-file a predicate [Q], both dispatch arms) under
   [WpInstrRun.swp_run_hart_active_instr_ex] (post-file existential).  Here
   [Q] pins the whole tower EXCEPT mip, which stays existential -- which is
   sound for free, because the continuation's agreement is off [tk_clock3]
   and mip ∈ [tk_clock3]: the tick's own mip write is exactly as
   nondeterministic.

   [mm_cycle_mip] / [wp_instr_mip] are [WpInstr]'s [mm_cycle] / [wp_instr]
   with that one existential added, and the leaf's obligation gains the mip
   cell in and an ARBITRARY one back.  Additive to [WpInstr]; it lives in
   its own file only so that iterating does not re-elaborate that one. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import HartSwp HartLift HartLift2 HartSpan HartSpanChar HartRunGen
        HartRegNode HartMCycle HartStepAny HartMRun HartMFrame RegFile WpGpr.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep
        RiscvFetchExec MinstretInv.
Require Import MstatusFacts.
Require Import KptPt.
Local Open Scope Z_scope.

Require Import InstrBytes WpInstrRun.
Require Import TsoCtx.

(* the read-only frame sees neither the nextPC commit nor the mip refresh:
   both cells are in [mm_Drw].  Discharged POSITIONALLY through
   [mm_rs_ro_agree], exactly as [HartMFrame.mm_ro_nPC] is and for the same
   reason -- a [first [...]] here runs failing [apply]s whose unifier
   delta-expands [mm_rs] into its [register_set] tower. *)
Lemma mm_ro_nPC_ip (pc x y ms : SailStdpp.Values.mword 64) (bmi : bool)
    (cy ti ip ip' mst0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (mc : SailStdpp.Values.mword 32)
    (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
    (pmar0 : type_of_register pma_regions) (elp0 : type_of_register elp) :
  reg_agree_on mm_Dro
    (mm_rs pc x ms bmi cy ti ip mst0 pcfg mc micfg misa0 mseccfg0 pmar0
       elp0 senv0)
    (mm_rs pc y ms bmi cy ti ip' mst0 pcfg mc micfg misa0 mseccfg0 pmar0
       elp0 senv0).
Proof.
  apply mm_rs_ro_agree;
    [ apply mm_rs_priv | apply mm_rs_mst | apply mm_rs_hart | apply mm_rs_pcfg
    | apply mm_rs_mc | apply mm_rs_micfg | apply mm_rs_misa | apply mm_rs_sec
    | apply mm_rs_pma | apply mm_rs_htif | apply mm_rs_elp
    | apply mm_rs_senv ].
Qed.

Section WpInstrMip.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* every tower lookup, in one tactic (clone of [WpInstr]'s) *)
  Local Ltac mmrs :=
    by rewrite ?mm_rs_PC ?mm_rs_nPC ?mm_rs_ms ?mm_rs_mi ?mm_rs_cy ?mm_rs_ti
       ?mm_rs_ip ?mm_rs_priv ?mm_rs_mst ?mm_rs_hart ?mm_rs_pcfg ?mm_rs_mc
       ?mm_rs_micfg ?mm_rs_misa ?mm_rs_sec ?mm_rs_pma ?mm_rs_htif ?mm_rs_elp
       ?mm_rs_senv.

  (* ==================================================================== *)
  (* mm_cycle_mip -- [WpInstr.mm_cycle] with mip EXISTENTIAL after the     *)
  (* body.  The reservation is held aside (this wrapper's leaf never       *)
  (* reaches a memory event) and handed back inside [Psi].                 *)
  (* ==================================================================== *)
  Lemma mm_cycle_mip (pc npc : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (Psi : iProp Σ)
      (ms : mword 64) (bmi : bool) (cy ti ip mst0 : mword 64)
      (mc : mword 32) (micfg misa0 mseccfg0 senv0 : mword 64)
      (pmar0 : list PMA_Region) (elp0 : type_of_register elp) :
    eq_vec (_get_Mstatus_MIE mst0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mst0) ('b"1") = false ->
    _get_Mstatus_SXL mst0 = 'b"10" ->
    mstatus_kernel_facts mst0 ->
    hw_config -∗
    resv_any cpu_id -∗
    hreg_frame (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
    hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
    (hreg_frame (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw -∗
     hreg_frame_ro (mm_Df dq) (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro -∗
       swp (run_hart_active 0)
         (fun st => ∃ (w : mword 32) (ip' : mword 64),
                    ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗
                    hreg_frame (mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip' mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Drw ∗
                    hreg_frame_ro (mm_Df dq) (mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip' mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0) mm_Dro ∗ Psi)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pc_is npc -∗ Psi -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HmIE HMPRV HSXL HKF.
    iIntros "#Hhw Hfrag Hrw Hro Hbody Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iApply (swp_exec_step_any mm_Drw mm_Dro (mm_Df dq)
              (mm_rs pc pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
              (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
              (fun rsx => exists ip' : mword 64,
                 rsx = mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip' mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
              (Psi ∗ resv_any cpu_id)%I
              mm_disj mm_w_cy mm_w_ti mm_w_ip mm_in_priv mm_in_hart mm_in_mc
              mm_in_micfg mm_w_mi mm_in_mi mm_w_ms mm_in_ms mm_w_PC mm_in_PC
              mm_in_nPC ltac:(mmrs)
              ltac:(intros rs2 [ip2 ->]; mmrs)
              ltac:(intros rs2 [ip2 ->]; mmrs)
              (mm_pre_agree pc ms bmi cy ti ip mst0 pmpcfg0 mc micfg misa0
                 mseccfg0 senv0 pmar0 elp0)
              with "Hcert Hfrag Hrw Hro [Hbody] [Hcont]").
    2:{ iNext. iIntros (rs3) "%Hag Hrw Hro [HPsi Hfrag]".
        destruct Hag as (rs2 & mi & (ip2 & ->) & Hag).
        pose proof (mm_tick_agree pc npc ms (minstret_inc_flag mc micfg Machine)
                      cy ti ip2 mst0 pmpcfg0 mc micfg misa0 mseccfg0 senv0
                      pmar0 elp0 mi rs3 Hag) as Hag'.
        iDestruct (mm_rw_ext _ _ Hag' with "Hrw") as "Hrw".
        iDestruct (mm_ro_ext dq _ _ Hag' with "Hro") as "Hro".
        iDestruct (mm_frames_elim dq npc pmpcfg0 mi (minstret_inc_flag mc micfg Machine)
                     _ _ _ mst0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                     HmIE HMPRV HSXL HKF with "Hhw Hfrag Hrw Hro")
          as "(Hmm & Hpmpc & Hpc)".
        iApply ("Hcont" with "Hmm Hpmpc Hpc HPsi"). }
    (* the body never reaches a memory event, so the reservation is held
       aside and handed straight back beside [Psi]. *)
    iIntros "Hfrag Hrw Hro".
    iApply (swp_mono with "[Hfrag] [-]"); [| iApply ("Hbody" with "Hrw Hro") ].
    iIntros (st). iDestruct 1 as (w ip2) "(-> & Hrw & Hro & HPsi)".
    iExists (mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip2 mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0).
    iSplitR; [iPureIntro; by exists ip2|].
    rewrite /RETIRE_SUCCESS. cbn match.
    iFrame "Hrw Hro HPsi".
    iApply (resv_any_intro with "Hfrag").
  Qed.

  (* ==================================================================== *)
  (* wp_instr_mip -- [WpInstr.wp_instr] with the mip cell LENT.            *)
  (*                                                                      *)
  (* Same bundles in and out; the only difference is in the obligation,    *)
  (* which receives [mip ↦ᵣ ip] (at whatever the tick left -- the wrapper  *)
  (* learns [ip] from [mm_frames_intro]'s existential, which is why the    *)
  (* obligation is under a ∀) and gives back an ARBITRARY [mip ↦ᵣ ip'].    *)
  (* ==================================================================== *)
  Lemma wp_instr_mip (pc npc : mword 64) (is_rvc : bool) (i : instruction)
      (m m' : regfile) (pmpcfg0 : type_of_register pmpcfg_n)
      {dq : dfrac} (R : iProp Σ) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add pc j)) KP_rx) ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (∀ ip : mword 64,
     gpr_file m -∗
     (R_bitvector_64 PC) ↦ᵣ pc -∗
     (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int pc (if is_rvc then 2 else 4)) -∗
     (R_bitvector_64 mip) ↦ᵣ ip -∗
       swp (execute i)
         (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m' ∗
                   (R_bitvector_64 PC) ↦ᵣ pc ∗
                   (R_bitvector_64 nextPC) ↦ᵣ npc ∗
                   (∃ ip' : mword 64, (R_bitvector_64 mip) ↦ᵣ ip') ∗ R)) -∗
    ▷ (mmode_config dq -∗ pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pc_is npc -∗ gpr_file m' -∗ R -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpmp Hstat.
    iIntros "Hmm Hpmpc Hpc Hgpr Hinstr Hex Hcont".
    iDestruct (mm_frames_intro dq pc pmpcfg0 with "Hmm Hpmpc Hpc")
      as "(#Hhw & Hfrag & Hfr)".
    iDestruct "Hfr" as (ms bmi cy ti ip mst0 mc micfg misa0 mseccfg0 senv0
        pmar0 elp0)
      "(%HmIE & %HMPRV & %HSXL & %HKF & %HmS & %HmC & %HmA & %Hmisaval &
        %Hsecval & %Hpmaall & %Helpnp & Hrw & Hro)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iDestruct (hw_config_kmap with "Hhw") as "#Hkm".
    iApply (mm_cycle_mip pc npc pmpcfg0 (gpr_file m' ∗ R)%I
              ms bmi cy ti ip mst0
              mc micfg misa0 mseccfg0 senv0 pmar0 elp0 HmIE HMPRV HSXL HKF
              with "Hhw Hfrag Hrw Hro [Hgpr Hinstr Hex] [Hcont]").
    2:{ iNext. iIntros "Hmm Hpmpc Hpc [Hgpr HR]".
        iApply ("Hcont" with "Hmm Hpmpc Hpc Hgpr HR"). }
    (* the two pure facts the dispatch wants, at the [wrap_pre] file *)
    assert (Hdok : decode_ok (mm_Drw ∪ mm_Dro) (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)).
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
    pose proof (hfrun_lpad (mm_Drw ∪ mm_Dro) mm_Drw (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                  mm_in_elp ltac:(rewrite mm_rs_elp; exact Helpnp)) as Hlp.
    iIntros "Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [| iApply (swp_run_hart_active_instr_ex mm_Drw mm_Dro (mm_Df dq)
                   (mm_rs pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                   (fun rsx => exists ip' : mword 64,
                      rsx = mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip' mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0)
                   pc is_rvc i pmar0 pmpcfg0 (gpr_file m' ∗ R)%I
                   mm_disj mm_in_priv mm_in_misa mm_in_mst mm_in_PC mm_w_nPC
                   mm_in_pma mm_in_pcfg mm_in_htif
                   ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs) ltac:(mmrs)
                   ltac:(rewrite mm_rs_misa; exact HmS)
                   ltac:(rewrite mm_rs_misa; exact HmC)
                   ltac:(rewrite mm_rs_mst; exact HmIE)
                   Hpmp Hpmaall Hstat Hdok Hlp
                   with "Hcert Hkm Hinstr Hrw Hro [Hgpr Hex]") ].
    { iIntros (st) "H". iDestruct "H" as (w) "(-> & H)".
      iDestruct "H" as (rs2) "((%ip2 & ->) & Hrw & Hro & HPsi)".
      iExists w, ip2. by iFrame. }
    (* the ONE nextPC transport, at the symbolic width *)
    iIntros "Hrw Hro".
    pose proof (mm_npc_agree pc pc ms (minstret_inc_flag mc micfg Machine) cy ti ip
                   mst0 pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0
                   (add_vec_int pc (if is_rvc then 2 else 4))) as Hnp.
    iDestruct (mm_rw_ext _ _ Hnp with "Hrw") as "Hrw".
    iDestruct (mm_ro_ext dq _ _ Hnp with "Hro") as "Hro".
    iDestruct (mm_rw_open with "Hrw")
      as "(HPC & HnPC & Hms & Hmi & Hcy & Hti & Hip)".
    iApply (swp_mono with "[Hms Hmi Hcy Hti Hro] [-]");
      [| iApply ("Hex" $! ip with "Hgpr HPC HnPC Hip") ].
    iIntros (u) "(-> & Hgpr & HPC & HnPC & Hipx & HR)".
    iDestruct "Hipx" as (ip2) "Hip".
    iSplitR; [done|].
    iExists (mm_rs pc npc ms (minstret_inc_flag mc micfg Machine) cy ti ip2 mst0 pmpcfg0 mc micfg misa0 mseccfg0 pmar0 elp0 senv0).
    iSplitR; [iPureIntro; by exists ip2|].
    iSplitL "HPC HnPC Hms Hmi Hcy Hti Hip".
    { iApply mm_rw_close. iFrame "HPC HnPC Hms Hmi Hcy Hti Hip". }
    iSplitL "Hro".
    { iApply (mm_ro_ext' dq _ _
                (mm_ro_nPC_ip pc (add_vec_int pc (if is_rvc then 2 else 4)) npc
                   ms (minstret_inc_flag mc micfg Machine) cy ti ip ip2 mst0
                   pmpcfg0 mc micfg misa0 mseccfg0 senv0 pmar0 elp0)
                with "Hro"). }
    iFrame "Hgpr HR".
  Qed.

End WpInstrMip.

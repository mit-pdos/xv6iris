(* WpSmodeIntr.v -- the SIE=1 instruction step engine (stage 1 of the
   SIE-agnostic sweep) and the SIE-AGNOSTIC funnel engines over
   [sconf] + [sie_cap] (stages 3-4).

   LAYER 1 [wp_instr_s_intr]: the interrupts-ENABLED mirror of
   [wp_instr_s_tlbinv_pt] (SmodeCorePt.v) -- the same per-instruction
   σ-callback shape, rebased on the interrupt-absorbing step engine
   [wp_exec_step_intr] (WpIntrInv.v).  "No interrupt dispatched" is
   discharged from the PURE fact the absorbing engine hands its
   callback -- an arbitrary number of pending interrupts has already
   been taken and fully handled (trap + handler + sret round trips)
   before the callback runs -- NOT from SIE=0.  Differences forced by
   the absorbing step rule: the config travels as the ONE bundle
   [intr_config]; the caller threads [gpr_file m] and the per-trap
   frame [intr_frame] (each interrupt consumes and re-establishes
   them); the interrupted pc must be a legal sret target; the callback
   receives the nextPC cell explicitly (the whole [pc_is pc] is
   threaded through the absorbing engine; the PC half stays here for
   the retire obligation); and this engine assembles the full
   [run_hart_active] retire witness itself (via
   [exec_hart_active_progress_base_gen]/[_RVC_gen] at Supervisor),
   driving the unified [tlb_inv_pt_fetch] with tlb_inv_pt / menvcfg
   borrowed from [intr_frame].

   LAYER 2 [wp_instr_s_sconf]: THE SIE-AGNOSTIC FUNNEL.  Takes the v2
   bundle [sconf] + the capability [sie_cap] (IntrDefs.v) and
   case-splits on the capability's disjunct -- ghost agreement between
   the bundle's tied half and the capability's quarter pins the live
   SIE bit, replacing every pure SIE premise:
     - quarter-'0': today's dispatch-None body -- delegates to
       [wp_instr_s_config_tlbinv_pt] with SIE=0 derived from the ghost;
     - quarter-'1': delegates to [wp_instr_s_intr], assembling
       [intr_config]/[intr_frame] from the bundle + capability via
       [intr_config_of_v2] and disassembling them back around the
       σ-callback; the sret-target premise is DERIVED from
       [instr_bytes]' 2-alignment ([update_bit0_zero_of_aligned2]), so
       no call site carries it.
   Both arms present the SAME σf-callback, so everything above is
   SIE-blind; the perf-hot σ-level fetch drive is not duplicated (each
   arm reuses its engine's existing one).

   On top: the agnostic gpr-write engines [wp_gpr_write_s_sconf{,_base}]
   (premise [rd <> csp_rs1]: [sie_cap]'s '1' arm is keyed on sp and
   transported by [sie_cap_retarget]; sp-moving instructions re-carve
   their stack explicitly), pilot leaves [wp_addi_s_sconf] /
   [wp_cli_s_sconf], and the straight-line pilot [wp_sconf_pilot3] --
   three chained instructions that run UNCHANGED whether interrupts are
   enabled (arbitrary interrupts absorbed at every step) or disabled.  *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase StackOwn.
Require Import SmodeCore KptTree SmodeCorePt.
Require Import WpSmodeSret AlignBits.
Require Import IntrDefs WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSmodeIntr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* §1 THE STEP ENGINE at SIE=1: the [wp_instr_s_tlbinv_pt] callback     *)
  (* shape over [wp_exec_step_intr].                                      *)
  (* =================================================================== *)
  Lemma wp_instr_s_intr (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (m : gmap regidx (mword 64)) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) :
    sret_tgt pc = pc ->
    menvcfg0 = MENVCFG_S ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       intr_config γ -∗
       gpr_file m -∗
       intr_frame root_ppn menvcfg0 m -∗
       nextPC ↦ᵣ pc -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc0 Hmenvval0) "#Hintr Hhs Hcfg Hpc Hfile HF Hinstr H".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_intr γ handler pc root_ppn menvcfg0 m Φ Hpc0
              with "Hintr Hhs Hcfg Hpc Hfile HF").
    iIntros (σ) "%Hdisp Hcfg Hpc Hfile HF Hsi".
    (* unbundle the config for the σ-level fetch lookups *)
    iDestruct "Hcfg" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hsepcx & Hscausex & Hstvalx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hsie & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HSIE1 & HMPRV0 & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct "HF" as "(Hmenv & Htlbinv & Hstk)".
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpcr")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    (* the unified fetch through the tree invariant (may write A/D back) *)
    iMod (tlb_inv_pt_fetch root_ppn σ pc r
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)".
    (* decode agreement + its side conditions, at σf *)
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid    with "Hreg Hmenv")  as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    assert (Hlpad : eq_vec (register_lookup elp σf.(sregs))
                           (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Help_σf; exact Help_np).
    (* rebundle config + frame; run the caller's execute at σf *)
    iMod ("H" $! σf Lpc_σf
            with "[Hpriv Hms Hsie Hmiex Hsepcx Hscausex Hstvalx]
                  Hfile [Hmenv Htlbinv Hstk] Hnpc [$Hreg $Hmem]")
      as (s_exec) "(%Hexec & [Hreg' Hmem'] & Hcont)".
    { iFrame "Hhw Hminv Hpriv Hmiex Hsepcx Hscausex Hstvalx".
      iExists ms. iFrame "Hms Hsie". iPureIntro. exact Hmsf. }
    { iFrame "Hmenv Htlbinv Hstk". }
    iDestruct (reg_valid with "Hreg' Hpcr") as %Lpc_exec.
    rewrite Lpc_σf in Hexec.
    (* assemble the run_hart_active retire witness *)
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w : direct decode, single execute *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (zero_extend' 32 w), s_exec.
      iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_base_gen Supervisor σ σf s_exec w i
                 pc RETIRE_SUCCESS
                 Lpriv Hdisp Hfetcheq Hdec0 Hlpad Hnlpad Lpc_σf Hexec I). }
      rewrite Lpc_exec. iFrame "Hpcr Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h : indirect decode, ExecuteAs redispatch *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      assert (Hzca : exec (currentlyEnabled Ext_Zca) σf = Some (true, σf))
        by (apply exec_currentlyEnabled_Zca; rewrite Hmisa_σf; exact HmisaC).
      iModIntro. iExists (zero_extend' 32 h), s_exec.
      iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_RVC_gen Supervisor σ σf s_exec h i0 i
                 pc RETIRE_SUCCESS
                 Lpriv Hdisp Hfetcheq Hdec Hlpad Lpc_σf Hzca
                 (Hexp (set_reg σf nextPC (add_vec_int pc 2))) Hexec). }
      rewrite Lpc_exec. iFrame "Hpcr Hreg' Hmem'". iExact "Hcont".
  Qed.

  (* =================================================================== *)
  (* §2 THE SIE-AGNOSTIC FUNNEL over [sconf] + [sie_cap]: ghost agreement *)
  (* picks the arm; both arms present the same σf-callback.               *)
  (* =================================================================== *)
  Lemma wp_instr_s_sconf (γ : gname) (root_ppn : mword 44)
      (m : gmap regidx (mword 64)) (n : nat) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) :
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       sconf γ -∗
       sie_cap γ root_ppn m n -∗
       tlb_inv_pt root_ppn -∗
       gpr_file m -∗
       nextPC ↦ᵣ pc -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr H".
    iDestruct "Hcap" as "[Hstk [Hq0 | (Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx)]]".
    - (* ---- quarter-'0': the dispatch-None engine, SIE=0 from ghost ---- *)
      iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
      iDestruct "Hmsx" as (ms) "(Hms & Hhalf & %Hmsf)".
      pose proof Hmsf as Hmsf'.
      destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP).
      iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
      assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
        by (rewrite Hb0; vm_compute; reflexivity).
      iDestruct "Hmiex" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
      iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
      iDestruct "Hpc" as "[Hpcr Hnpc]".
      iApply (wp_instr_s_config_tlbinv_pt root_ppn Φ pc is_rvc i
                ms mie_v mdv0 menvcfg0 (dq := DfracOwn 1)
                HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                with "Hhw Hminv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcr Hinstr").
      iIntros (σ Hpceq) "Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsi".
      iMod ("H" $! σ Hpceq
              with "[Hpriv Hms Hhalf Hmie Hmdl Hmenv] [Hstk Hq0] Htlbinv Hfile Hnpc Hsi")
        as (s_exec) "(%Hexec & Hsi' & Hcont)".
      { iFrame "Hhw Hminv Hpriv".
        iSplitL "Hms Hhalf".
        { iExists ms. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
        iSplitL "Hmie Hmdl".
        { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
        iExists menvcfg0. iFrame "Hmenv". iPureIntro.
        repeat split; assumption. }
      { iFrame "Hstk". iLeft. iExact "Hq0". }
      iModIntro. iExists s_exec.
      iSplitR; [iPureIntro; exact Hexec |].
      iFrame "Hsi'". iExact "Hcont".
    - (* ---- quarter-'1': the interrupt-absorbing engine ---- *)
      (* split the exact reserved carve off for [intr_frame]; the deep
         [n] available slots ride framed through the absorbing engine *)
      iEval (rewrite stack_own_app) in "Hstk".
      iDestruct "Hstk" as "[Hstk Hdeep]".
      iDestruct "Hhx" as (handler) "#Hintr".
      iAssert (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝)%I as %Hal2.
      { iDestruct "Hinstr" as "[%Hnlpad Hr]".
        iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
        iEval (rewrite /instr_bytes) in "Hbytes".
        iDestruct "Hbytes" as "[%H2al _]". iPureIntro. exact H2al. }
      assert (Hpc0 : sret_tgt pc = pc)
        by (unfold sret_tgt; exact (update_bit0_zero_of_aligned2 pc Hal2)).
      iDestruct (intr_config_of_v2 with "Hsc Hq1 Hsepcx Hscausex Hstvalx")
        as "(Hic & Hq1 & Hmenv)".
      iApply (wp_instr_s_intr γ handler root_ppn MENVCFG_S m Φ pc is_rvc i
                Hpc0 eq_refl
                with "Hintr Hhs Hic Hpc Hfile [Hmenv Htlbinv Hstk] Hinstr").
      { iFrame "Hmenv Htlbinv Hstk". }
      iIntros (σ Hpceq) "Hic Hfile HF Hnpc Hsi".
      iDestruct "HF" as "(Hmenv & Htlbinv & Hstk)".
      iDestruct (v2_of_intr_config with "Hic Hmenv")
        as "(Hsc & Hsepcx & Hscausex & Hstvalx)".
      iMod ("H" $! σ Hpceq
              with "Hsc [Hq1 Hsepcx Hscausex Hstvalx Hstk Hdeep] Htlbinv Hfile Hnpc Hsi")
        as (s_exec) "(%Hexec & Hsi' & Hcont)".
      { iSplitL "Hstk Hdeep".
        { iApply stack_own_app. iFrame "Hstk Hdeep". }
        iRight. iFrame "Hq1 Hsepcx Hscausex Hstvalx".
        iExists handler. iExact "Hintr". }
      iModIntro. iExists s_exec.
      iSplitR; [iPureIntro; exact Hexec |].
      iFrame "Hsi'". iExact "Hcont".
  Qed.

  (* =================================================================== *)
  (* §3 The generic gpr-write engines over the funnel.  [rd <> csp_rs1]:  *)
  (* [sie_cap]'s '1' arm is keyed on sp and transported across non-sp     *)
  (* writes by [sie_cap_retarget]; sp-moving instructions re-carve their  *)
  (* stack explicitly instead.                                            *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hbexec)
      "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m n Φ pc true base
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg wval]> m) n Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' Hsc Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* the 4-byte (base-encoding) variant: pc advances by 4 *)
  Lemma wp_gpr_write_s_sconf_base (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false base -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hbexec)
      "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m n Φ pc false base
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg wval]> m) n Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' Hsc Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* =================================================================== *)
  (* §4 PILOT leaves + the straight-line pilot: the same three chained    *)
  (* instructions as the old SIE=1-only pilot, now SIE-AGNOSTIC -- the    *)
  (* proof is identical at either SIE value, and needs NO sret-target or  *)
  (* menvcfg premises (both derived inside the funnel).                   *)
  (* =================================================================== *)
  Lemma wp_addi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_cli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) = wval ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.

  (* straight line of THREE instructions -- addi a5,a5,imm1 (4 bytes);
     c.li a4,imm2 (2 bytes); addi a4,a4,imm3 (4 bytes) -- at EITHER SIE
     value: with interrupts enabled an arbitrary number of pending
     interrupts is absorbed before each instruction, with them disabled
     this is the ordinary dispatch-None execution; the proof does not
     mention the mode. *)
  Lemma wp_sconf_pilot3 (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc pc2 pc3 : mword 64) (imm1 imm3 : mword 12) (imm2 : mword 6)
      (w1 w2 w3 : mword 64) (m : gmap regidx (mword 64)) (n : nat) :
    pc2 = add_vec_int pc 4 ->
    pc3 = add_vec_int pc2 2 ->
    add_vec (m !!! Regidx (mword_of_int 15)) (sign_extend' 64 imm1) = w1 ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm2)) = w2 ->
    add_vec (regval_into_reg w2) (sign_extend' 64 imm3) = w3 ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc  false (ITYPE (imm1, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) -∗
    instr pc2 true  (ITYPE (sign_extend' 12 imm2, zreg, Regidx (mword_of_int 14), ADDI)) -∗
    instr pc3 false (ITYPE (imm3, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn
        (<[Regidx (mword_of_int 14) := regval_into_reg w3]>
         (<[Regidx (mword_of_int 14) := regval_into_reg w2]>
          (<[Regidx (mword_of_int 15) := regval_into_reg w1]> m))) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc3 4) -∗
      gpr_file (<[Regidx (mword_of_int 14) := regval_into_reg w3]>
                (<[Regidx (mword_of_int 14) := regval_into_reg w2]>
                 (<[Regidx (mword_of_int 15) := regval_into_reg w1]> m))) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc2 Hpc3 Hw1 Hw2 Hw3)
      "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1 Hi2 Hi3 Hcont".
    assert (H15nz : uint (mword_of_int 15 : mword 5) <> 0)
      by (vm_compute; discriminate).
    assert (H14nz : uint (mword_of_int 14 : mword 5) <> 0)
      by (vm_compute; discriminate).
    assert (H15sp : (mword_of_int 15 : mword 5) <> csp_rs1)
      by (intros Hc; apply (f_equal (@uint 5)) in Hc; vm_compute in Hc; discriminate).
    assert (H14sp : (mword_of_int 14 : mword 5) <> csp_rs1)
      by (intros Hc; apply (f_equal (@uint 5)) in Hc; vm_compute in Hc; discriminate).
    (* instruction 1: addi a5, a5, imm1 *)
    iApply (wp_addi_s_sconf γ root_ppn Φ pc
              (mword_of_int 15) (mword_of_int 15) imm1 w1 m n
              H15nz H15sp Hw1
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi1").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    rewrite <- Hpc2.
    (* instruction 2: c.li a4, imm2 *)
    iApply (wp_cli_s_sconf γ root_ppn Φ pc2
              (mword_of_int 14) imm2 w2 _ n
              H14nz H14sp Hw2
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi2").
    iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
    rewrite <- Hpc3.
    (* instruction 3: addi a4, a4, imm3 *)
    unshelve iApply (wp_addi_s_sconf γ root_ppn Φ pc3
              (mword_of_int 14) (mword_of_int 14) imm3 w3 _ n
              H14nz H14sp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hi3").
    { rewrite lookup_total_insert. exact Hw3. }
    iApply "Hcont".
  Qed.

End WpSmodeIntr.

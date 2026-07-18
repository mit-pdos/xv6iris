(* WpSmodeIntr.v -- the SIE=1 S-mode instruction step engine (stage 1 of
   the SIE-agnostic sweep).

   [wp_instr_s_intr] is the interrupts-ENABLED mirror of
   [wp_instr_s_tlbinv_pt] (SmodeCorePt.v): the same per-instruction
   σ-callback shape, but rebased on the interrupt-absorbing step engine
   [wp_exec_step_intr] (WpIntrInv.v) instead of the dispatch=None step
   rule.  "No interrupt dispatched" is discharged from the PURE fact the
   absorbing engine hands its callback -- an arbitrary number of pending
   interrupts has already been taken and fully handled (trap + handler +
   sret round trips) before the callback runs -- NOT from SIE=0.

   Differences from the SIE=0 engine forced by the absorbing step rule:
     - the ambient config is [intr_config γ] (SIE=1 mirror of
       [smode_config]) and travels as ONE bundle through the callback;
     - the caller threads [gpr_file m] and the per-trap frame
       [intr_frame root_ppn menvcfg0 m] (each interrupt consumes and
       re-establishes them);
     - the interrupted pc must be a legal sret target
       ([sret_tgt pc = pc], i.e. instruction-aligned);
     - the callback receives the nextPC cell explicitly (the whole
       [pc_is pc] is threaded through the absorbing engine; the PC half
       stays with this engine for the retire obligation);
     - this engine assembles the full [run_hart_active] retire witness
       itself (via [exec_hart_active_progress_base_gen]/[_RVC_gen] at
       Supervisor) -- the fetch is the unified [tlb_inv_pt_fetch], with
       tlb_inv_pt / menvcfg borrowed from [intr_frame] around it.

   On top: the generic gpr-write engines [wp_gpr_write_s_intr]
   (RVC/2-byte) and [wp_gpr_write_s_intr_base] (base/4-byte), the SIE=1
   mirrors of WpSmodePtLeaves' [wp_gpr_write_s_config(_base)_pt].  A
   non-sp-writing instruction transports the frame by
   [intr_frame_retarget]; sp-moving instructions are NOT covered here
   (they must re-carve their stack, as function proofs already do).      *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree PtTreeAdue KptPt.
Require Import SmodeCore KptTree SmodeCorePt.
Require Import StackOwn WpSmodeSret.
Require Import WpIntrBits WpIntrCore WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

Section WpSmodeIntr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* THE STEP ENGINE at SIE=1: the [wp_instr_s_tlbinv_pt] callback shape  *)
  (* over [wp_exec_step_intr].                                            *)
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
  (* The generic gpr-write engines over [wp_instr_s_intr]: the SIE=1      *)
  (* mirrors of [wp_gpr_write_s_config(_base)_pt] (WpSmodePtLeaves.v).    *)
  (* [rd <> csp_rs1]: the per-trap frame is keyed on sp, so a non-sp      *)
  (* write transports it by [intr_frame_retarget]; sp-moving              *)
  (* instructions re-carve their stack explicitly instead.                *)
  (* =================================================================== *)
  Lemma wp_gpr_write_s_intr (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    sret_tgt pc = pc ->
    menvcfg0 = MENVCFG_S ->
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
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      intr_config γ -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      intr_frame root_ppn menvcfg0 (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc0 Hmenvval0 Hrd Hrdsp Hbexec)
      "#Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont".
    iApply (wp_instr_s_intr γ handler root_ppn menvcfg0 m Φ pc true base
              Hpc0 Hmenvval0
              with "Hintr Hhs Hcfg Hpc Hfile HF Hinstr").
    iIntros (σ Hpceq) "Hcfg [%Hdom Hfmap] HF Hnpc [Hreg Hmem]".
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
    iDestruct (intr_frame_retarget root_ppn menvcfg0 m
                 (<[Regidx rd := regval_into_reg wval]> m) Hsp with "HF") as "HF".
    iApply ("Hcont" with "Hhs' Hcfg [$Hpc' $Hnpc] [Hfmap] HF").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* the 4-byte (base-encoding) variant: pc advances by 4 *)
  Lemma wp_gpr_write_s_intr_base (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    sret_tgt pc = pc ->
    menvcfg0 = MENVCFG_S ->
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
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc false base -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      intr_config γ -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      intr_frame root_ppn menvcfg0 (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc0 Hmenvval0 Hrd Hrdsp Hbexec)
      "#Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont".
    iApply (wp_instr_s_intr γ handler root_ppn menvcfg0 m Φ pc false base
              Hpc0 Hmenvval0
              with "Hintr Hhs Hcfg Hpc Hfile HF Hinstr").
    iIntros (σ Hpceq) "Hcfg [%Hdom Hfmap] HF Hnpc [Hreg Hmem]".
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
    iDestruct (intr_frame_retarget root_ppn menvcfg0 m
                 (<[Regidx rd := regval_into_reg wval]> m) Hsp with "HF") as "HF".
    iApply ("Hcont" with "Hhs' Hcfg [$Hpc' $Hnpc] [Hfmap] HF").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* =================================================================== *)
  (* PILOT leaves (stage 2): the SIE=1 twins of [wp_addi_s_pt] /          *)
  (* [wp_cli_s_pt] (WpSmodePtLeaves.v), over the gpr-write engines.       *)
  (* =================================================================== *)
  Lemma wp_addi_s_intr (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    sret_tgt pc = pc ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      intr_config γ -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      intr_frame root_ppn menvcfg0 (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc0 Hmenvval0 Hrd Hrdsp Hwval)
      "#Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_intr_base γ handler root_ppn menvcfg0 Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) wval m
              Hpc0 Hmenvval0 Hrd Hrdsp _
              with "Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_cli_s_intr (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    sret_tgt pc = pc ->
    menvcfg0 = MENVCFG_S ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) = wval ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      intr_config γ -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      intr_frame root_ppn menvcfg0 (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc0 Hmenvval0 Hrd Hrdsp Hwval)
      "#Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_intr γ handler root_ppn menvcfg0 Φ pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) wval m
              Hpc0 Hmenvval0 Hrd Hrdsp _
              with "Hintr Hhs Hcfg Hpc Hfile HF Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.

  (* =================================================================== *)
  (* PILOT demo (stage 2): a straight line of THREE instructions at       *)
  (* SIE=1 -- addi a5,a5,imm1 (4 bytes); c.li a4,imm2 (2 bytes);          *)
  (* addi a4,a4,imm3 (4 bytes) -- with an arbitrary number of pending     *)
  (* interrupts absorbed before each one.  [intr_frame]/[stack_own] are   *)
  (* threaded end to end; the frame retargets across the a5/a4 writes.    *)
  (* =================================================================== *)
  Lemma wp_intr_pilot3 (γ : gname) (handler : mword 64) (root_ppn : mword 44)
      (menvcfg0 : mword 64) (Φ : mval -> iProp Σ)
      (pc pc2 pc3 : mword 64) (imm1 imm3 : mword 12) (imm2 : mword 6)
      (w1 w2 w3 : mword 64) (m : gmap regidx (mword 64)) :
    pc2 = add_vec_int pc 4 ->
    pc3 = add_vec_int pc2 2 ->
    sret_tgt pc = pc ->
    sret_tgt pc2 = pc2 ->
    sret_tgt pc3 = pc3 ->
    menvcfg0 = MENVCFG_S ->
    add_vec (m !!! Regidx (mword_of_int 15)) (sign_extend' 64 imm1) = w1 ->
    add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm2)) = w2 ->
    add_vec (regval_into_reg w2) (sign_extend' 64 imm3) = w3 ->
    intr_inv γ handler root_ppn menvcfg0 -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    intr_config γ -∗
    pc_is pc -∗
    gpr_file m -∗
    intr_frame root_ppn menvcfg0 m -∗
    instr pc  false (ITYPE (imm1, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) -∗
    instr pc2 true  (ITYPE (sign_extend' 12 imm2, zreg, Regidx (mword_of_int 14), ADDI)) -∗
    instr pc3 false (ITYPE (imm3, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      intr_config γ -∗
      pc_is (add_vec_int pc3 4) -∗
      gpr_file (<[Regidx (mword_of_int 14) := regval_into_reg w3]>
                (<[Regidx (mword_of_int 14) := regval_into_reg w2]>
                 (<[Regidx (mword_of_int 15) := regval_into_reg w1]> m))) -∗
      intr_frame root_ppn menvcfg0
        (<[Regidx (mword_of_int 14) := regval_into_reg w3]>
         (<[Regidx (mword_of_int 14) := regval_into_reg w2]>
          (<[Regidx (mword_of_int 15) := regval_into_reg w1]> m))) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpc2 Hpc3 Hst1 Hst2 Hst3 Hmenvval0 Hw1 Hw2 Hw3)
      "#Hintr Hhs Hcfg Hpc Hfile HF Hi1 Hi2 Hi3 Hcont".
    assert (H15nz : uint (mword_of_int 15 : mword 5) <> 0)
      by (vm_compute; discriminate).
    assert (H14nz : uint (mword_of_int 14 : mword 5) <> 0)
      by (vm_compute; discriminate).
    assert (H15sp : (mword_of_int 15 : mword 5) <> csp_rs1)
      by (intros Hc; apply (f_equal (@uint 5)) in Hc; vm_compute in Hc; discriminate).
    assert (H14sp : (mword_of_int 14 : mword 5) <> csp_rs1)
      by (intros Hc; apply (f_equal (@uint 5)) in Hc; vm_compute in Hc; discriminate).
    (* instruction 1: addi a5, a5, imm1 *)
    iApply (wp_addi_s_intr γ handler root_ppn menvcfg0 Φ pc
              (mword_of_int 15) (mword_of_int 15) imm1 w1 m
              Hst1 Hmenvval0 H15nz H15sp Hw1
              with "Hintr Hhs Hcfg Hpc Hfile HF Hi1").
    iIntros "Hhs Hcfg Hpc Hfile HF".
    rewrite <- Hpc2.
    (* instruction 2: c.li a4, imm2 *)
    iApply (wp_cli_s_intr γ handler root_ppn menvcfg0 Φ pc2
              (mword_of_int 14) imm2 w2 _
              Hst2 Hmenvval0 H14nz H14sp Hw2
              with "Hintr Hhs Hcfg Hpc Hfile HF Hi2").
    iIntros "Hhs Hcfg Hpc Hfile HF".
    rewrite <- Hpc3.
    (* instruction 3: addi a4, a4, imm3 *)
    unshelve iApply (wp_addi_s_intr γ handler root_ppn menvcfg0 Φ pc3
              (mword_of_int 14) (mword_of_int 14) imm3 w3 _
              Hst3 Hmenvval0 H14nz H14sp _
              with "Hintr Hhs Hcfg Hpc Hfile HF Hi3").
    { rewrite lookup_total_insert. exact Hw3. }
    iApply "Hcont".
  Qed.

End WpSmodeIntr.

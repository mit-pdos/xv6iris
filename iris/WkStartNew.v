(** * WkStartNew.v -- the weak-tier [start()] boot chain (M4: the second
      whole-function port, after [wwp_entry]).

    The weak twin of [WpStartNew.wp_start]: xv6's [start()] (39 instructions
    at [KernelSyms.start] .. +0x72, INCLUDING the call to [timerinit()]) as
    ONE [WWP] theorem, with the SC statement's spellings swapped per the
    porting guide (claude-notes/projects/weak-memory-porting.md):

      - [kernel_text] -> [WeakInstr.wkernel_text kbs] + the [wkb_covers]
        coverage premise (WkEntryNew's kernel-text seam);
      - [stack_own_phys sp0 n] -> [hart_ws cpu_id ws] paired with
        [vwp_hold (WkStackOwn.wstack_own_phys sp0 n) ws]; the continuation
        binds the post-boot view [ws'] with [ws_le ws ws'];
      - [WP (Loop : expr riscv_lang)] -> [WWP Loop] (no postcondition
        anywhere -- main removed WP postconditions tree-wide);
      - every [m_*]/[st_m*] register-file definition and every static CSR
        fact ([st_ms1], [st_pmpcfg1], [st_menv_adue], [st_mret_priv], ...) is
        REUSED from [WpStartNew], never restated.

    Composition: every instruction is discharged by its HOISTED weak leaf
    (the batch recorded in weak-memory.md's "THE REMAINING-LEAF BATCH IS
    DONE" block) -- no inline funnel blocks, unlike [WkEntryNew]'s
    pre-hoisting vertical slice. The two prologue [c.sdsp] stores use
    [WeakLeafSdspOff.wwp_sd8_off_rvc_leaf] (the all-OFF boot PMP, NOT the TOR
    leaf -- the [pmpcfg0] write is instruction 58). [csrr mstatus]/
    [csrw mstatus]/[csrw pmpcfg0]/[mret] ride the CONFIG FUNNEL (full,
    unbundled [hart_state]/[cur_privilege]/[mstatus]/[pmpcfg_n] cells) and
    need the SAME "unbundle -> combine halves to full -> apply -> re-split ->
    rebundle" dance [WpStartNew] uses at its three config-writing sites --
    PLUS at [csrr mstatus] too, since the weak leaf needs [mstatus] whole
    (unlike the SC leaf, which only needs the pinned half). Every other CSR
    write/read and every ALU/move instruction is a plain [mmode_config
    (DfracOwn q)]-at-1/2 leaf, exactly mirroring [WpStartNew]'s own
    fraction choreography. The [jal] into [timerinit] is discharged by
    [WeakLeafJump.wwp_jal_leaf]; the call itself applies [WkTimerinit.
    wwp_timerinit].

    FILE LAYOUT: the per-instruction scaffolding (encoding words, kernel-image
    byte windows, decode facts at [dstateM], register/RAM drivers) lives in
    [WkStartAux.v], as [WkEntryEff] sits beside [WkEntryNew] -- that layer is
    stable while this one is iterated, and keeping them apart is the
    difference between a ~50 s and a multi-minute edit-compile loop.  The
    encoding words there are CLOSED LITERALS, not [kb_word_at] applications,
    and that is load-bearing: see [WkStartAux]'s header and the porting
    guide's failure-mode 12. *)

From Stdlib Require Import ZArith Zquot Zwf FunctionalExtensionality.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakWord8.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetchRvc WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr WpMmodeLeafBase.
Require Import WeakLeafWin.
Require Import WeakLeafEff8 WeakLeafLd8.
Require Import ExecCommon WpDecode WpAuipc WpMmodeJal WpMmodeMul.
Require Import WpGprCsrrCommon WpGprCsrwCommon.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMretWp.
Require Import StackOwn WpTimerinit.
Require Import WkStackOwn WkGprAcc WkTimerinit WeakLeafM.
Require Import WeakLeafSdspOff WeakLeafTor.
Require Import WeakLeafItype WeakLeafUtypeShift WeakLeafRtypeW WeakLeafJump.
Require Import WeakLeafCsrrM WeakLeafCsrw WeakLeafCsrw2 WeakLeafCsrw3.
Require Import WeakLeafPmpcfg0 WeakLeafMret.
Require Import CodeEntry CodeEntryAux KernelText.
Require Import KernelDecode00 KernelDecode01 KernelDecode02 KernelDecode03 KernelDecode04.
Require Import KernelDecode05 KernelDecode06 KernelDecode07 KernelDecode08 KernelDecode09.
Require Import KernelDecode10 KernelDecode11 KernelDecode12 KernelDecode13 KernelDecode14.
Require Import KernelDecode15 KernelDecode16 KernelDecode17 KernelDecode18 KernelDecode19.
Require Import KernelDecode20 KernelDecode21 KernelDecode22 KernelDecode23 KernelDecode24.
Require Import KernelDecode25 KernelDecode26 KernelDecode27 KernelDecode28 KernelDecode29.
Require Import KernelDecode30 KernelDecode31.
Require Import CodeStart CodeStartAux WpStartNew MbootVocab CodeTimerinitAux.
Require Import MstatusFacts StackOwn.
Require Import WkEntryEff.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Require Import WkStartAux.

Import SailStdpp.Values.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 4. THE THEOREM: the whole weak [start()] chain (through the
    [timerinit] call), one Qed.  Statement = [WpStartNew.wp_start] under the
    porting guide's swaps (see the file header). *)

Section WkStartThm.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [WkStackOwn.wstack_own_phys_2_intro] as ONE ∗-shaped entailment, so it
     composes with [vwp_hold_ent] at the frame bundling/re-bundling steps
     (the [WkTimerinit.stack_2_intro_ent] twin -- Local there). *)
  Local Lemma wstack2_intro_ent (sp : Arch.pa) (w1 w2 : bv 64) :
    (wpt8 (pa_stk sp 1) (DfracOwn 1) w1 ∗ wpt8 (pa_stk sp 2) (DfracOwn 1) w2)
    ⊢ wstack_own_phys sp 2.
  Proof. iIntros "[H1 H2]". iApply (wstack_own_phys_2_intro with "H1 H2"). Qed.

  Lemma wwp_start
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 mhartid_in : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (n : nat) (kbs : gmap Arch.pa (bv 8)) (ws : wstate) :
    gen_id = 0%nat ->
    (4 <= n)%nat ->
    pmp_all_off pmpcfg0 ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx ti_ra = ra0 ->
    m !!! Regidx ti_s0 = s00 ->
    uint (ti_ea_ra (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    uint (ti_ea_s0 (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    (* the weak twin carries explicit RAM-membership for every symbolic
       stack slot it or [wwp_timerinit] touches -- [phys_word_pointsto]'s
       gen_heap is RAM-backed by construction, but [wpt8] is [Z]-keyed with
       no RAM tie (WkStackOwn.v's header note). *)
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_ra sp0) j)) ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_s0 sp0) j)) ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_ra (ti_sp1 sp0)) j)) ->
    (forall j : nat, (j < 8)%nat -> addr_is_ram (pa_add (ti_ea_s0 (ti_sp1 sp0)) j)) ->
    wkb_covers kbs ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pc_is st_pc30 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    mepc ↦ᵣ mepc0 -∗
    satp ↦ᵣ satp0 -∗
    medeleg ↦ᵣ medeleg0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    mie ↦ᵣ mie0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    hart_ws cpu_id ws -∗
    vwp_hold (wstack_own_phys sp0 n) ws -∗
    wkernel_text kbs -∗
    ( ∀ (tv : mword 64) (ms0 : mword 64)
        (HoIE : eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false)
        (HoPRV : eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false)
        (HoSXL : _get_Mstatus_SXL ms0 = ('b"10"))
        (HoKF : mstatus_kernel_facts ms0) (ws' : wstate),
      ⌜ws_le ws ws'⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ cms5 (st_ms1 ms0) -∗
      pmpcfg_n ↦ᵣ st_pmpcfg1 pmpcfg0 -∗
      pmpaddr_n ↦ᵣ st_pmpaddr1 pmpcfg0 pmpaddr00 -∗
      pc_is st_main -∗
      gpr_file (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      mepc ↦ᵣ st_main -∗
      satp ↦ᵣ satp_legalized satp0 (mword_of_int 0) -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 st_ffff -∗
      mideleg ↦ᵣ st_mdl1 mideleg0 -∗
      mie ↦ᵣ st_mie1 mie0 mideleg0 -∗
      menvcfg ↦ᵣ menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (ti_mcen1 mcounteren0) -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
      hart_ws cpu_id ws' -∗
      vwp_hold (wstack_own_phys sp0 n) ws' -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hn4 Hpmp HlpeE Hsp Hra Hs0 Hbnd_ra Hbnd_s0
           Hram8_ra Hram8_s0 Hram8_ti_ra Hram8_ti_s0 Hcov.
    iIntros "Hmm Hpcf Hpaddr [Hpc Hnpc] Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc Hhws Hstk #Htext Hcont".
    (* ---- split the stack bundle: start's own 4 slots + the deep rest ---- *)
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_split_1 sp0 4 n ltac:(lia)) with "Hstk")
      as "Hstk". iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Htop Hdeep]".
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_split_1 sp0 2 4 ltac:(lia)) with "Htop")
      as "Htop". iEval (rewrite vwp_hold_sep) in "Htop". iDestruct "Htop" as "[Ht12 Ht34]".
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_2_elim sp0) with "Ht12") as "Ht12".
    iEval (rewrite vwp_hold_exist) in "Ht12". iDestruct "Ht12" as (vsra) "Ht12".
    iEval (rewrite vwp_hold_exist) in "Ht12". iDestruct "Ht12" as (vss0) "Ht12".
    iEval (rewrite vwp_hold_sep) in "Ht12". iDestruct "Ht12" as "[Hsra Hss0]".
    iDestruct (vwp_hold_ent _ _ ws (wstack_own_phys_2_elim (pa_stk sp0 2)) with "Ht34") as "Ht34".
    iEval (rewrite vwp_hold_exist) in "Ht34". iDestruct "Ht34" as (vtra) "Ht34".
    iEval (rewrite vwp_hold_exist) in "Ht34". iDestruct "Ht34" as (vts0) "Ht34".
    iEval (rewrite vwp_hold_sep) in "Ht34". iDestruct "Ht34" as "[Htra Hts0]".
    iEval (rewrite (pa_stk_assoc sp0 2 1)) in "Htra".
    iEval (rewrite (pa_stk_assoc sp0 2 2)) in "Hts0".
    assert (Hb1 : ti_ea_ra sp0 = pa_stk sp0 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : ti_ea_s0 sp0 = pa_stk sp0 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : ti_ea_ra (ti_sp1 sp0) = pa_stk sp0 3).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : ti_ea_s0 (ti_sp1 sp0) = pa_stk sp0 4).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* timerinit's own frame, as [pa_stk] offsets OF ITS OWN sp -- the shape
       [wwp_timerinit] wants; and [ti_sp1 sp0] IS [pa_stk sp0 2]. *)
    assert (Hb0 : ti_sp1 sp0 = pa_stk sp0 2).
    { unfold ti_sp1, pa_stk, add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Htb1 : ti_ea_ra (ti_sp1 sp0) = pa_stk (ti_sp1 sp0) 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Htb2 : ti_ea_s0 (ti_sp1 sp0) = pa_stk (ti_sp1 sp0) 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hsra". iEval (rewrite -Hb2) in "Hss0".
    iEval (rewrite -Hb3) in "Htra". iEval (rewrite -Hb4) in "Hts0".
    (* ---- pure side conditions (verbatim off WpStartNew) ---- *)
    pose proof (pmp_all_off_allows_all _ Hpmp) as HpmpU.
    assert (Hpmp1 : pmp_allows_all (st_pmpcfg1 pmpcfg0))
      by (apply pmp_allows_all_written; exact HpmpU).
    assert (Htor_ra : pmp_tor0_grants (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00)
                        (ti_ea_ra (ti_sp1 sp0)) 8)
      by (apply st_pmp_tor0_grants; [exact Hpmp | lia | exact Hbnd_ra]).
    assert (Htor_s0 : pmp_tor0_grants (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00)
                        (ti_ea_s0 (ti_sp1 sp0)) 8)
      by (apply st_pmp_tor0_grants; [exact Hpmp | lia | exact Hbnd_s0]).
    assert (Hnz_sp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hnz_ra : uint ti_ra <> 0) by (vm_compute; discriminate).
    assert (Hnz_s0 : uint ti_s0 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a4 : uint ti_a4 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a5 : uint ti_a5 <> 0) by (vm_compute; discriminate).
    assert (Hnz_tp : uint st_tp <> 0) by (vm_compute; discriminate).
    (* closed-value bridges (pure math, reused verbatim from [WpStartNew]) *)
    assert (Hm1v : add_vec (luival (sign_extend' 20 si35)) (sign_extend' 64 si36) = st_mask_and)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hm2v : add_vec (luival (sign_extend' 20 si38)) (sign_extend' 64 si39) = st_mask_or)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ha42v : add_vec st_pc42 (auipc_off si42) = st_a42v)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ha43v : add_vec st_a42v (sign_extend' 64 si43) = st_main)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hmepcv : mepc_val st_main = st_main)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hz45 : sign_extend' 64 si45 = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hffv : add_vec (luival (sign_extend' 20 si47)) (sign_extend' 64 si48) = st_ffff)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hshv : shift_bits_right (cli_wval si54)
                     (subrange_vec_dec ssh55 (Z.sub log2_xlen 1) 0) = st_pmpw)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (H15v : sign_extend' 64 si57 = (mword_of_int 15 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlinkv : add_vec_int st_pc59 4 = st_ra_link) by (vm_compute; reflexivity).
    assert (Hjal_al : is_aligned_paddr (Physaddr (add_vec st_pc59 (sign_extend' 64 sjimm59))) 4
                      = true) by (vm_compute; reflexivity).
    assert (P59 : add_vec st_pc59 (sign_extend' 64 sjimm59) = ti_pc9)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hcretv : ret_pc st_ra_link = st_pc60) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hctgtv : ret_pc st_main = st_main) by (apply bv_eq; vm_compute; reflexivity).
    pose proof (st_s0_16 sp0) as Hs016.
    (* ---- unbundle the FULL config once, naming the entry mstatus [ms0];
       split all cells in half: a working bundle at 1/2 + pinned halves. ---- *)
    iDestruct (mmode_config_unbundle with "Hmm") as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HoIE & %HoPRV & %HoSXL & %HoKF)".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) ms0 HoIE HoPRV HoSXL HoKF
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    assert (HmIE1 : eq_vec (_get_Mstatus_MIE (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MIE. rewrite st_va5_40_MIE. exact HoIE. }
    assert (HMPRV1 : eq_vec (_get_Mstatus_MPRV (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MPRV. rewrite st_va5_40_MPRV. exact HoPRV. }
    assert (HSXL1 : _get_Mstatus_SXL (st_ms1 ms0) = ('b"10")).
    { unfold st_ms1. rewrite mstatus_legalized_SXL. exact HoSXL. }
    pose proof (st_ms1_kernel_facts ms0 HoKF) as HKF1.

    (* ---- 30. c.addi sp, -16 ---- *)
    assert (Hal2_30 : is_aligned_vaddr (Virtaddr st_pc30) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_30 : is_aligned_vaddr (Virtaddr st_pc30) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_30 : acc_wf st_pc30 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_30 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc30 j)) by ram_win.
    assert (Hcond_30 : subrange_vec_dec stw_30 15 0 = sth_30 /\ isRVC sth_30 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc30 (F_RVC sth_30)) as "#Hbs30".
    { iApply (winstr_bytes_of_text kbs st_pc30 (F_RVC sth_30) stw_30 Hal2_30 Hacc_30 Hram_30
                Hcond_30 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x0) stw_30 Hcov stkb_30). }
    iApply (wwp_addi_rvc_leaf true st_pc30 sth_30 csp_rs1 csp_rs1 (sign_extend' 12 i9)
              (C_ADDI (i9, Regidx csp_rs1)) m st_pc30 pmpcfg0 (1/2)%Qp D_m D_none dstateM ws
              Hgid HpmpU Hal2_30 Hal4_30 Hnz_sp
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDI (i9, Regidx csp_rs1))
                 (conj (kd_1141 t HC) (conj stlpad_30 (exec_execute_C_ADDI i9 (Regidx csp_rs1)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_30 stdec_30 stgoodexp_30 (exec_execute_C_ADDI i9 (Regidx csp_rs1))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs30 Hhws").
    iIntros (ws30) "%Hwsle30 Hmm HpcfA Hpc Hfile Hhws".
    iEval (rewrite sext6_12_64 Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (st_m30 m sp0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P30 : add_vec_int st_pc30 2 = st_pc31) by (vm_compute; reflexivity).
    iEval (rewrite P30) in "Hpc". iEval (rewrite P30) in "Hnpc".

    (* ---- 31. c.sdsp ra, 8(sp) ---- *)
    assert (L31sp : st_m30 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0) by (st_unfold; st_look).
    assert (L31ra : st_m30 m sp0 !!! Regidx ti_ra = ra0) by (st_unfold; st_look).
    assert (Hea31 : add_vec (st_m30 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite L31sp; reflexivity).
    assert (Hal2_31 : is_aligned_vaddr (Virtaddr st_pc31) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_31 : is_aligned_vaddr (Virtaddr st_pc31) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_31 : acc_wf st_pc31 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_31 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc31 j)) by ram_win.
    assert (Hcond_31 : subrange_vec_dec stw_31 15 0 = sth_31 /\ isRVC sth_31 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc31 (F_RVC sth_31)) as "#Hbs31".
    { iApply (winstr_bytes_of_text kbs st_pc31 (F_RVC sth_31) stw_31 Hal2_31 Hacc_31 Hram_31
                Hcond_31 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x2) stw_31 Hcov stkb_31). }
    iDestruct (vwp_hold_mono _ ws ws30 Hwsle30 with "Hsra") as "Hsra".
    iDestruct (gpr_file_acc_2 (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_ra) ltac:(st_reg_neq)
                 with "Hfile") as "(Hspc & Hrac & Hfins31)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp)
             -(rf_lookup (st_m30 m sp0) (Regidx csp_rs1)) L31sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)
             -(rf_lookup (st_m30 m sp0) (Regidx ti_ra)) L31ra) in "Hrac".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws30) as "HR31".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_sd8_off_rvc_leaf false st_pc31 sth_31 csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000"))) (C_SDSP (u10, Regidx ti_ra))
              (ti_ea_ra sp0) vsra (⌜True⌝%I) (1/2)%Qp pmpcfg0
              (ti_sp1 sp0) ra0 st_pc31
              D_m D_none dstateM ws30
              Hgid Hpmp Hal2_31 Hal4_31 Hnz_sp Hnz_ra eq_refl Hram8_ra
              (fun t _ HC _ _ _ => ex_intro _ (C_SDSP (u10, Regidx ti_ra))
                 (conj (kd_e406 t HC) (conj stlpad_31 (exec_execute_C_SDSP u10 (Regidx ti_ra)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_31 stdec_31 stgoodexp_31 (exec_execute_C_SDSP u10 (Regidx ti_ra))
              with "Hmm HpcfA Hpc Hnpc Hspc Hrac Hbs31 Hhws Hsra HR31").
    iIntros (ws31 T31) "%Hwsle31 %HT31 Hmm HpcfA Hpc Hspc Hrac Hhws Hsra _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfins31" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (rf_upd2_same (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
             (ti_sp1 sp0) ra0 ltac:(st_reg_neq) L31sp L31ra)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P31 : add_vec_int st_pc31 2 = st_pc32) by (vm_compute; reflexivity).
    iEval (rewrite P31) in "Hpc". iEval (rewrite P31) in "Hnpc".

    (* ---- 32. c.sdsp s0, 0(sp) ---- *)
    assert (L32s0 : st_m30 m sp0 !!! Regidx ti_s0 = s00) by (st_unfold; st_look).
    assert (Hea32 : add_vec (st_m30 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite L31sp; reflexivity).
    assert (Hal2_32 : is_aligned_vaddr (Virtaddr st_pc32) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_32 : is_aligned_vaddr (Virtaddr st_pc32) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_32 : acc_wf st_pc32 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_32 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc32 j)) by ram_win.
    assert (Hcond_32 : subrange_vec_dec stw_32 15 0 = sth_32 /\ isRVC sth_32 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc32 (F_RVC sth_32)) as "#Hbs32".
    { iApply (winstr_bytes_of_text kbs st_pc32 (F_RVC sth_32) stw_32 Hal2_32 Hacc_32 Hram_32
                Hcond_32 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x4) stw_32 Hcov stkb_32). }
    iDestruct (vwp_hold_mono _ ws ws31 (transitivity Hwsle30 Hwsle31) with "Hss0") as "Hss0".
    iDestruct (gpr_file_acc_2 (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_s0) ltac:(st_reg_neq)
                 with "Hfile") as "(Hspc & Hs0c & Hfins32)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp)
             -(rf_lookup (st_m30 m sp0) (Regidx csp_rs1)) L31sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0)
             -(rf_lookup (st_m30 m sp0) (Regidx ti_s0)) L32s0) in "Hs0c".
    iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws31) as "HR32".
    { rewrite vwp_hold_pure. done. }
    iApply (wwp_sd8_off_rvc_leaf true st_pc32 sth_32 csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000"))) (C_SDSP (u11, Regidx ti_s0))
              (ti_ea_s0 sp0) vss0 (⌜True⌝%I) (1/2)%Qp pmpcfg0
              (ti_sp1 sp0) s00 st_pc32
              D_m D_none dstateM ws31
              Hgid Hpmp Hal2_32 Hal4_32 Hnz_sp Hnz_s0 eq_refl Hram8_s0
              (fun t _ HC _ _ _ => ex_intro _ (C_SDSP (u11, Regidx ti_s0))
                 (conj (kd_e022 t HC) (conj stlpad_32 (exec_execute_C_SDSP u11 (Regidx ti_s0)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_32 stdec_32 stgoodexp_32 (exec_execute_C_SDSP u11 (Regidx ti_s0))
              with "Hmm HpcfA Hpc Hnpc Hspc Hs0c Hbs32 Hhws Hss0 HR32").
    iIntros (ws32 T32) "%Hwsle32 %HT32 Hmm HpcfA Hpc Hspc Hs0c Hhws Hss0 _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iDestruct ("Hfins32" with "Hspc Hs0c") as "Hfile".
    iEval (rewrite (rf_upd2_same (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
             (ti_sp1 sp0) s00 ltac:(st_reg_neq) L31sp L32s0)) in "Hfile".
    iDestruct (vwp_hold_mono _ ws31 ws32 Hwsle32 with "Hsra") as "Hsra".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P32 : add_vec_int st_pc32 2 = st_pc33) by (vm_compute; reflexivity).
    iEval (rewrite P32) in "Hpc". iEval (rewrite P32) in "Hnpc".
    (* the prologue is done: bundle the four frame words and the deep rest into
       ONE [vwp_hold], so the remaining 30 instructions cost a single
       [vwp_hold_mono] bump each (the §2h trap-5 accounting). *)
    pose proof (transitivity Hwsle30 (transitivity Hwsle31 Hwsle32)) as Hle_ws_32.
    iDestruct (vwp_hold_mono _ ws ws32 Hle_ws_32 with "Htra") as "Htra".
    iDestruct (vwp_hold_mono _ ws ws32 Hle_ws_32 with "Hts0") as "Hts0".
    iDestruct (vwp_hold_mono _ ws ws32 Hle_ws_32 with "Hdeep") as "Hdeep".
    iEval (rewrite Htb1) in "Htra". iEval (rewrite Htb2) in "Hts0".
    iAssert (vwp_hold (wstack_own_phys (ti_sp1 sp0) 2) ws32) with "[Htra Hts0]" as "Hti2".
    { iApply (vwp_hold_ent _ _ ws32 (wstack2_intro_ent (ti_sp1 sp0) vtra vts0)).
      iEval (rewrite vwp_hold_sep). iFrame. }
    iAssert (vwp_hold (wpt8 (ti_ea_ra sp0) (DfracOwn 1) ra0 ∗
                       wpt8 (ti_ea_s0 sp0) (DfracOwn 1) s00 ∗
                       wstack_own_phys (ti_sp1 sp0) 2 ∗
                       wstack_own_phys (pa_stk sp0 4) (n - 4)) ws32)
      with "[Hsra Hss0 Hti2 Hdeep]" as "Hstk".
    (* peel ONE [∗] at a time: [rewrite !vwp_hold_sep] would recurse into
       [wpt8]'s own ∗-chain (alignment + wrap-freedom + 8 bytes) and leave
       [iFrame] nothing to match the unshattered [Hsra]/[Hss0] against. *)
    { iEval (rewrite vwp_hold_sep). iSplitL "Hsra"; [iExact "Hsra"|].
      iEval (rewrite vwp_hold_sep). iSplitL "Hss0"; [iExact "Hss0"|].
      iEval (rewrite vwp_hold_sep). iSplitL "Hti2"; [iExact "Hti2"|iExact "Hdeep"]. }

    (* ---- 33. c.addi4spn s0, sp, 16 (s0 := sp0) ---- *)
    assert (Hal2_33 : is_aligned_vaddr (Virtaddr st_pc33) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_33 : is_aligned_vaddr (Virtaddr st_pc33) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_33 : acc_wf st_pc33 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_33 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc33 j)) by ram_win.
    assert (Hcond_33 : subrange_vec_dec stw_33 15 0 = sth_33 /\ isRVC sth_33 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc33 (F_RVC sth_33)) as "#Hbs33".
    { iApply (winstr_bytes_of_text kbs st_pc33 (F_RVC sth_33) stw_33 Hal2_33 Hacc_33 Hram_33
                Hcond_33 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x6) stw_33 Hcov stkb_33). }
    assert (Hexp_33 : forall s : mstate,
              exec (execute (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))) s
              = Some (ExecuteAs (ITYPE (caddi4spn_imm nz12, Regidx csp_rs1,
                                        Regidx ti_s0, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_ADDI4SPN (Cregidx (mword_of_int 0)) nz12).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_addi_rvc_leaf false st_pc33 sth_33 csp_rs1 ti_s0 (caddi4spn_imm nz12)
              (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12)) (st_m30 m sp0) st_pc33
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws32
              Hgid HpmpU Hal2_33 Hal4_33 Hnz_s0
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDI4SPN (Cregidx (mword_of_int 0), nz12))
                 (conj (kd_0800 t HC) (conj stlpad_33 Hexp_33)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_33 stdec_33 stgoodexp_33 Hexp_33
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs33 Hhws").
    iIntros (ws33) "%Hwsle33 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws32 ws33 Hwsle33 with "Hstk") as "Hstk".
    iEval (rewrite L31sp Hs016) in "Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg sp0]> (st_m30 m sp0))
             with (st_m33 m sp0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P33 : add_vec_int st_pc33 2 = st_pc34) by (vm_compute; reflexivity).
    iEval (rewrite P33) in "Hpc". iEval (rewrite P33) in "Hnpc".

    (* ---- 34. csrr a5, mstatus.  The WEAK leaf wants the mstatus cell WHOLE
       (its conclusion names the read value), so this is a config-funnel site
       even though the SC leaf read only the pinned half. ---- *)
    assert (Hal2_34 : is_aligned_vaddr (Virtaddr st_pc34) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_34 : is_aligned_vaddr (Virtaddr st_pc34) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_34 : acc_wf st_pc34 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_34 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc34 j)) by ram_win.
    assert (Hcond_34 : stw_34 = stw_34 /\ isRVC (subrange_vec_dec stw_34 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc34 (F_Base stw_34)) as "#Hbs34".
    { iApply (winstr_bytes_of_text kbs st_pc34 (F_Base stw_34) stw_34 Hal2_34 Hacc_34 Hram_34
                Hcond_34 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x8) stw_34 Hcov stkb_34). }
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms0') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    iDestruct (gpr_file_insert_acc (st_m33 m sp0) (Regidx ti_a5)
                 (regval_into_reg ms0) with "Hfile") as "[Ha5c Hfins34]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_mstatus_leaf true st_pc34 stw_34 ti_a5 ms0
              (st_m33 m sp0 (Regidx ti_a5)) st_pc34 pmpcfg0 D_m dstateM ws33
              Hgid HpmpU Hal2_34 Hal4_34 Hnz_a5 HoIE HoPRV
              (fun t _ _ _ Hmi Hcfg => kd_300027f3 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_34 stdec_34
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Ha5c Hbs34 Hhws").
    iIntros (ws34) "%Hwsle34 Hhs Hpriv Hms Hpcf Hpc Ha5c Hhws".
    iDestruct (vwp_hold_mono _ ws33 ws34 Hwsle34 with "Hstk") as "Hstk".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) ms0 HoIE HoPRV HoSXL HoKF
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins34" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg ms0]> (st_m33 m sp0))
             with (st_m34 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P34 : add_vec_int st_pc34 4 = st_pc35) by (vm_compute; reflexivity).
    iEval (rewrite P34) in "Hpc". iEval (rewrite P34) in "Hnpc".

    (* ---- 35. c.lui a4, 0xffffe.  RE-PORTED against the SC-shaped interface
       ([WeakLeafM.wwp_lui] + the [wsti_35] token): compare the block below
       with [WpStartNew]'s six lines for the same instruction. ---- *)
    iPoseProof (wsti_35 kbs Hcov with "Htext") as "#Hi35".
    iApply (wwp_lui st_pc35 true ti_a4 (sign_extend' 20 si35) (st_m34 m sp0 ms0)
              pmpcfg0 (1/2)%Qp ws34 Hgid HpmpU Hnz_a4
              with "Hmm HpcfA [$Hpc $Hnpc] Hfile Hi35 Hhws").
    iIntros (ws35) "%Hwsle35 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws34 ws35 Hwsle35 with "Hstk") as "Hstk".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si35))]>
                     (st_m34 m sp0 ms0))
             with (st_m35 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P35 : add_vec_int st_pc35 2 = st_pc36) by (vm_compute; reflexivity).
    iEval (rewrite P35) in "Hpc". iEval (rewrite P35) in "Hnpc".

    (* ---- 36. addi a4, a4, 2047 (a4 := 0xffffffffffffe7ff) ---- *)
    assert (L36a4 : st_m35 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si35))
      by (st_unfold; st_look).
    assert (Hal2_36 : is_aligned_vaddr (Virtaddr st_pc36) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_36 : is_aligned_vaddr (Virtaddr st_pc36) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_36 : acc_wf st_pc36 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_36 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc36 j)) by ram_win.
    assert (Hcond_36 : stw_36 = stw_36 /\ isRVC (subrange_vec_dec stw_36 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc36 (F_Base stw_36)) as "#Hbs36".
    { iApply (winstr_bytes_of_text kbs st_pc36 (F_Base stw_36) stw_36 Hal2_36 Hacc_36 Hram_36
                Hcond_36 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0xe) stw_36 Hcov stkb_36). }
    iApply (wwp_addi_leaf false st_pc36 stw_36 ti_a4 ti_a4 si36
              (st_m35 m sp0 ms0) st_pc36 pmpcfg0 (1/2)%Qp D_m dstateM ws35
              Hgid HpmpU Hal2_36 Hal4_36 Hnz_a4
              (fun t _ _ _ Hmi Hcfg => kd_7ff70713 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_36 stdec_36
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs36 Hhws").
    iIntros (ws36) "%Hwsle36 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws35 ws36 Hwsle36 with "Hstk") as "Hstk".
    iEval (rewrite L36a4 Hm1v) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_and]> (st_m35 m sp0 ms0))
             with (st_m36 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P36 : add_vec_int st_pc36 4 = st_pc37) by (vm_compute; reflexivity).
    iEval (rewrite P36) in "Hpc". iEval (rewrite P36) in "Hnpc".

    (* ---- 37. c.and a5, a4 ---- *)
    assert (L37a5 : st_m36 m sp0 ms0 !!! Regidx ti_a5 = ms0) by (st_unfold; st_look).
    assert (L37a4 : st_m36 m sp0 ms0 !!! Regidx ti_a4 = st_mask_and) by (st_unfold; st_look).
    assert (Hal2_37 : is_aligned_vaddr (Virtaddr st_pc37) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_37 : is_aligned_vaddr (Virtaddr st_pc37) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_37 : acc_wf st_pc37 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_37 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc37 j)) by ram_win.
    assert (Hcond_37 : subrange_vec_dec stw_37 15 0 = sth_37 /\ isRVC sth_37 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc37 (F_RVC sth_37)) as "#Hbs37".
    { iApply (winstr_bytes_of_text kbs st_pc37 (F_RVC sth_37) stw_37 Hal2_37 Hacc_37 Hram_37
                Hcond_37 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x12) stw_37 Hcov stkb_37). }
    assert (Hexp_37 : forall s : mstate,
              exec (execute (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
              = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, AND)), s)).
    { intro s. rewrite (exec_execute_C_AND (Cregidx (mword_of_int 7)) (Cregidx (mword_of_int 6))).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_and_rvc_leaf false st_pc37 sth_37 ti_a4 ti_a5 ti_a5
              (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
              (st_m36 m sp0 ms0) st_pc37 pmpcfg0 (1/2)%Qp D_m D_none dstateM ws36
              Hgid HpmpU Hal2_37 Hal4_37 Hnz_a5
              (fun t _ HC _ _ _ =>
                 ex_intro _ (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
                   (conj (kd_8ff9 t HC) (conj stlpad_37 Hexp_37)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_37 stdec_37 stgoodexp_37 Hexp_37
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs37 Hhws").
    iIntros (ws37) "%Hwsle37 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws36 ws37 Hwsle37 with "Hstk") as "Hstk".
    iEval (rewrite L37a5 L37a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (and_vec ms0 st_mask_and)]> (st_m36 m sp0 ms0))
             with (st_m37 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P37 : add_vec_int st_pc37 2 = st_pc38) by (vm_compute; reflexivity).
    iEval (rewrite P37) in "Hpc". iEval (rewrite P37) in "Hnpc".

    (* ---- 38. c.lui a4, 1 ---- *)
    assert (Hal2_38 : is_aligned_vaddr (Virtaddr st_pc38) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_38 : is_aligned_vaddr (Virtaddr st_pc38) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_38 : acc_wf st_pc38 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_38 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc38 j)) by ram_win.
    assert (Hcond_38 : subrange_vec_dec stw_38 15 0 = sth_38 /\ isRVC sth_38 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc38 (F_RVC sth_38)) as "#Hbs38".
    { iApply (winstr_bytes_of_text kbs st_pc38 (F_RVC sth_38) stw_38 Hal2_38 Hacc_38 Hram_38
                Hcond_38 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x14) stw_38 Hcov stkb_38). }
    iApply (wwp_lui_rvc_leaf true st_pc38 sth_38 ti_a4 (sign_extend' 20 si38)
              (C_LUI (si38, Regidx ti_a4)) (st_m37 m sp0 ms0) st_pc38
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws37
              Hgid HpmpU Hal2_38 Hal4_38 Hnz_a4
              (fun t _ HC _ _ _ => ex_intro _ (C_LUI (si38, Regidx ti_a4))
                 (conj (kd_6705 t HC) (conj stlpad_38 (exec_execute_C_LUI si38 (Regidx ti_a4)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_38 stdec_38 stgoodexp_38 (exec_execute_C_LUI si38 (Regidx ti_a4))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs38 Hhws").
    iIntros (ws38) "%Hwsle38 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws37 ws38 Hwsle38 with "Hstk") as "Hstk".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si38))]>
                     (st_m37 m sp0 ms0))
             with (st_m38 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P38 : add_vec_int st_pc38 2 = st_pc39) by (vm_compute; reflexivity).
    iEval (rewrite P38) in "Hpc". iEval (rewrite P38) in "Hnpc".

    (* ---- 39. addi a4, a4, -2048 (a4 := 0x800) ---- *)
    assert (L39a4 : st_m38 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si38))
      by (st_unfold; st_look).
    assert (Hal2_39 : is_aligned_vaddr (Virtaddr st_pc39) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_39 : is_aligned_vaddr (Virtaddr st_pc39) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_39 : acc_wf st_pc39 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_39 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc39 j)) by ram_win.
    assert (Hcond_39 : stw_39 = stw_39 /\ isRVC (subrange_vec_dec stw_39 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc39 (F_Base stw_39)) as "#Hbs39".
    { iApply (winstr_bytes_of_text kbs st_pc39 (F_Base stw_39) stw_39 Hal2_39 Hacc_39 Hram_39
                Hcond_39 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x16) stw_39 Hcov stkb_39). }
    iApply (wwp_addi_leaf false st_pc39 stw_39 ti_a4 ti_a4 si39
              (st_m38 m sp0 ms0) st_pc39 pmpcfg0 (1/2)%Qp D_m dstateM ws38
              Hgid HpmpU Hal2_39 Hal4_39 Hnz_a4
              (fun t _ _ _ Hmi Hcfg => kd_80070713 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_39 stdec_39
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs39 Hhws").
    iIntros (ws39) "%Hwsle39 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws38 ws39 Hwsle39 with "Hstk") as "Hstk".
    iEval (rewrite L39a4 Hm2v) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_or]> (st_m38 m sp0 ms0))
             with (st_m39 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P39 : add_vec_int st_pc39 4 = st_pc40) by (vm_compute; reflexivity).
    iEval (rewrite P39) in "Hpc". iEval (rewrite P39) in "Hnpc".

    (* ---- 40. c.or a5, a4 (a5 := the mstatus write value) ---- *)
    assert (L40a5 : st_m39 m sp0 ms0 !!! Regidx ti_a5 = and_vec ms0 st_mask_and)
      by (st_unfold; st_look).
    assert (L40a4 : st_m39 m sp0 ms0 !!! Regidx ti_a4 = st_mask_or) by (st_unfold; st_look).
    assert (Hal2_40 : is_aligned_vaddr (Virtaddr st_pc40) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_40 : is_aligned_vaddr (Virtaddr st_pc40) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_40 : acc_wf st_pc40 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_40 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc40 j)) by ram_win.
    assert (Hcond_40 : subrange_vec_dec stw_40 15 0 = sth_40 /\ isRVC sth_40 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc40 (F_RVC sth_40)) as "#Hbs40".
    { iApply (winstr_bytes_of_text kbs st_pc40 (F_RVC sth_40) stw_40 Hal2_40 Hacc_40 Hram_40
                Hcond_40 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x1a) stw_40 Hcov stkb_40). }
    assert (Hexp_40 : forall s : mstate,
              exec (execute (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
              = Some (ExecuteAs (RTYPE (Regidx ti_a4, Regidx ti_a5, Regidx ti_a5, OR)), s)).
    { intro s. rewrite (exec_execute_C_OR (Cregidx (mword_of_int 7)) (Cregidx (mword_of_int 6))).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_or_rvc_leaf false st_pc40 sth_40 ti_a4 ti_a5 ti_a5
              (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
              (st_m39 m sp0 ms0) st_pc40 pmpcfg0 (1/2)%Qp D_m D_none dstateM ws39
              Hgid HpmpU Hal2_40 Hal4_40 Hnz_a5
              (fun t _ HC _ _ _ =>
                 ex_intro _ (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
                   (conj (kd_8fd9 t HC) (conj stlpad_40 Hexp_40)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_40 stdec_40 stgoodexp_40 Hexp_40
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs40 Hhws").
    iIntros (ws40) "%Hwsle40 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws39 ws40 Hwsle40 with "Hstk") as "Hstk".
    iEval (rewrite L40a5 L40a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec (and_vec ms0 st_mask_and) st_mask_or)]>
                     (st_m39 m sp0 ms0))
             with (st_m40 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P40 : add_vec_int st_pc40 2 = st_pc41) by (vm_compute; reflexivity).
    iEval (rewrite P40) in "Hpc". iEval (rewrite P40) in "Hnpc".

    (* ---- 41. csrw mstatus, a5: recombine to FULL raw cells and run the
       config-funnel leaf; the written value stays a single symbol. ---- *)
    assert (L41a5 : st_m40 m sp0 ms0 !!! Regidx ti_a5 = st_va5_40 ms0) by (st_unfold; st_look).
    assert (Hal2_41 : is_aligned_vaddr (Virtaddr st_pc41) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_41 : is_aligned_vaddr (Virtaddr st_pc41) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_41 : acc_wf st_pc41 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_41 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc41 j)) by ram_win.
    assert (Hcond_41 : stw_41 = stw_41 /\ isRVC (subrange_vec_dec stw_41 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc41 (F_Base stw_41)) as "#Hbs41".
    { iApply (winstr_bytes_of_text kbs st_pc41 (F_Base stw_41) stw_41 Hal2_41 Hacc_41 Hram_41
                Hcond_41 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x1c) stw_41 Hcov stkb_41). }
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms1') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    iDestruct (gpr_file_lookup_acc (st_m40 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb41]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mstatus_leaf st_pc41 stw_41 ti_a5 ms0
              (st_m40 m sp0 ms0 (Regidx ti_a5)) st_pc41 pmpcfg0 D_m dstateM ws40
              Hgid HpmpU Hal4_41 Hnz_a5 HoIE HoPRV
              (fun t _ _ _ Hmi Hcfg => kd_30079073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_41 stdec_41
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Ha5c Hbs41 Hhws").
    iIntros (ws41) "%Hwsle41 Hhs Hpriv Hms Hpcf Hpc Ha5c Hhws".
    iDestruct (vwp_hold_mono _ ws40 ws41 Hwsle41 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m40 m sp0 ms0) (Regidx ti_a5)) L41a5) in "Hms".
    iEval (change (mstatus_legalized ms0 (st_va5_40 ms0)) with (st_ms1 ms0)) in "Hms".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1 HKF1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb41" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P41 : add_vec_int st_pc41 4 = st_pc42) by (vm_compute; reflexivity).
    iEval (rewrite P41) in "Hpc". iEval (rewrite P41) in "Hnpc".

    (* ---- 42. auipc a5, 1 ---- *)
    assert (Hal2_42 : is_aligned_vaddr (Virtaddr st_pc42) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_42 : is_aligned_vaddr (Virtaddr st_pc42) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_42 : acc_wf st_pc42 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_42 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc42 j)) by ram_win.
    assert (Hcond_42 : stw_42 = stw_42 /\ isRVC (subrange_vec_dec stw_42 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc42 (F_Base stw_42)) as "#Hbs42".
    { iApply (winstr_bytes_of_text kbs st_pc42 (F_Base stw_42) stw_42 Hal2_42 Hacc_42 Hram_42
                Hcond_42 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x20) stw_42 Hcov stkb_42). }
    iApply (wwp_auipc_leaf true st_pc42 stw_42 ti_a5 si42
              (st_m40 m sp0 ms0) st_pc42 pmpcfg0 (1/2)%Qp D_m dstateM ws41
              Hgid HpmpU Hal2_42 Hal4_42 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_00001797 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_42 stdec_42
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs42 Hhws").
    iIntros (ws42) "%Hwsle42 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws41 ws42 Hwsle42 with "Hstk") as "Hstk".
    iEval (rewrite Ha42v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_a42v]> (st_m40 m sp0 ms0))
             with (st_m42 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P42 : add_vec_int st_pc42 4 = st_pc43) by (vm_compute; reflexivity).
    iEval (rewrite P42) in "Hpc". iEval (rewrite P42) in "Hnpc".

    (* ---- 43. addi a5, a5, -506 (a5 := <main>) ---- *)
    assert (L43a5 : st_m42 m sp0 ms0 !!! Regidx ti_a5 = st_a42v) by (st_unfold; st_look).
    assert (Hal2_43 : is_aligned_vaddr (Virtaddr st_pc43) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_43 : is_aligned_vaddr (Virtaddr st_pc43) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_43 : acc_wf st_pc43 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_43 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc43 j)) by ram_win.
    assert (Hcond_43 : stw_43 = stw_43 /\ isRVC (subrange_vec_dec stw_43 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc43 (F_Base stw_43)) as "#Hbs43".
    { iApply (winstr_bytes_of_text kbs st_pc43 (F_Base stw_43) stw_43 Hal2_43 Hacc_43 Hram_43
                Hcond_43 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x24) stw_43 Hcov stkb_43). }
    iApply (wwp_addi_leaf true st_pc43 stw_43 ti_a5 ti_a5 si43
              (st_m42 m sp0 ms0) st_pc43 pmpcfg0 (1/2)%Qp D_m dstateM ws42
              Hgid HpmpU Hal2_43 Hal4_43 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_e0678793 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_43 stdec_43
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs43 Hhws").
    iIntros (ws43) "%Hwsle43 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws42 ws43 Hwsle43 with "Hstk") as "Hstk".
    iEval (rewrite L43a5 Ha43v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_main]> (st_m42 m sp0 ms0))
             with (st_m43 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P43 : add_vec_int st_pc43 4 = st_pc44) by (vm_compute; reflexivity).
    iEval (rewrite P43) in "Hpc". iEval (rewrite P43) in "Hnpc".

    (* ---- 44. csrw mepc, a5 ---- *)
    assert (L44a5 : st_m43 m sp0 ms0 !!! Regidx ti_a5 = st_main) by (st_unfold; st_look).
    assert (Hal2_44 : is_aligned_vaddr (Virtaddr st_pc44) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_44 : is_aligned_vaddr (Virtaddr st_pc44) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_44 : acc_wf st_pc44 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_44 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc44 j)) by ram_win.
    assert (Hcond_44 : stw_44 = stw_44 /\ isRVC (subrange_vec_dec stw_44 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc44 (F_Base stw_44)) as "#Hbs44".
    { iApply (winstr_bytes_of_text kbs st_pc44 (F_Base stw_44) stw_44 Hal2_44 Hacc_44 Hram_44
                Hcond_44 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x28) stw_44 Hcov stkb_44). }
    iDestruct (gpr_file_lookup_acc (st_m43 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb44]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mepc_leaf true st_pc44 stw_44 ti_a5 mepc0
              (st_m43 m sp0 ms0 (Regidx ti_a5)) st_pc44 pmpcfg0 (1/2)%Qp D_m dstateM ws43
              Hgid HpmpU Hal2_44 Hal4_44 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_34179073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_44 stdec_44
              with "Hmm HpcfA Hpc Hnpc Ha5c Hmepc Hbs44 Hhws").
    iIntros (ws44) "%Hwsle44 Hmm HpcfA Hpc Ha5c Hmepc Hhws".
    iDestruct (vwp_hold_mono _ ws43 ws44 Hwsle44 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m43 m sp0 ms0) (Regidx ti_a5)) L44a5 Hmepcv) in "Hmepc".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb44" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P44 : add_vec_int st_pc44 4 = st_pc45) by (vm_compute; reflexivity).
    iEval (rewrite P44) in "Hpc". iEval (rewrite P44) in "Hnpc".

    (* ---- 45. c.li a5, 0 ---- *)
    iDestruct (gpr_file_x0 (st_m43 m sp0 ms0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_45 Hfile]".
    assert (Hal2_45 : is_aligned_vaddr (Virtaddr st_pc45) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_45 : is_aligned_vaddr (Virtaddr st_pc45) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_45 : acc_wf st_pc45 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_45 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc45 j)) by ram_win.
    assert (Hcond_45 : subrange_vec_dec stw_45 15 0 = sth_45 /\ isRVC sth_45 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc45 (F_RVC sth_45)) as "#Hbs45".
    { iApply (winstr_bytes_of_text kbs st_pc45 (F_RVC sth_45) stw_45 Hal2_45 Hacc_45 Hram_45
                Hcond_45 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x2c) stw_45 Hcov stkb_45). }
    assert (Hexp_45 : forall s : mstate, exec (execute (C_LI (si45, Regidx ti_a5))) s
              = Some (ExecuteAs (ITYPE (sign_extend' 12 si45, Regidx cli_rs1,
                                        Regidx ti_a5, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_LI si45 (Regidx ti_a5)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_addi_rvc_leaf true st_pc45 sth_45 cli_rs1 ti_a5 (sign_extend' 12 si45)
              (C_LI (si45, Regidx ti_a5)) (st_m43 m sp0 ms0) st_pc45
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws44
              Hgid HpmpU Hal2_45 Hal4_45 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_LI (si45, Regidx ti_a5))
                 (conj (kd_4781 t HC) (conj stlpad_45 Hexp_45)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_45 stdec_45 stgoodexp_45 Hexp_45
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs45 Hhws").
    iIntros (ws45) "%Hwsle45 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws44 ws45 Hwsle45 with "Hstk") as "Hstk".
    iEval (rewrite Hx0_45 add_vec_zero_l sext6_12_64 Hz45) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 0)]> (st_m43 m sp0 ms0))
             with (st_m45 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P45 : add_vec_int st_pc45 2 = st_pc46) by (vm_compute; reflexivity).
    iEval (rewrite P45) in "Hpc". iEval (rewrite P45) in "Hnpc".

    (* ---- 46. csrw satp, a5 (Bare) ---- *)
    assert (L46a5 : st_m45 m sp0 ms0 !!! Regidx ti_a5 = (mword_of_int 0 : mword 64))
      by (st_unfold; st_look).
    assert (Hal2_46 : is_aligned_vaddr (Virtaddr st_pc46) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_46 : is_aligned_vaddr (Virtaddr st_pc46) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_46 : acc_wf st_pc46 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_46 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc46 j)) by ram_win.
    assert (Hcond_46 : stw_46 = stw_46 /\ isRVC (subrange_vec_dec stw_46 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc46 (F_Base stw_46)) as "#Hbs46".
    { iApply (winstr_bytes_of_text kbs st_pc46 (F_Base stw_46) stw_46 Hal2_46 Hacc_46 Hram_46
                Hcond_46 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x2e) stw_46 Hcov stkb_46). }
    iDestruct (gpr_file_lookup_acc (st_m45 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb46]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_satp_leaf false st_pc46 stw_46 ti_a5 satp0
              (st_m45 m sp0 ms0 (Regidx ti_a5)) st_pc46 pmpcfg0 (1/2)%Qp D_m dstateM ws45
              Hgid HpmpU Hal2_46 Hal4_46 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_18079073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_46 stdec_46
              with "Hmm HpcfA Hpc Hnpc Ha5c Hsatp Hbs46 Hhws").
    iIntros (ws46) "%Hwsle46 Hmm HpcfA Hpc Ha5c Hsatp Hhws".
    iDestruct (vwp_hold_mono _ ws45 ws46 Hwsle46 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m45 m sp0 ms0) (Regidx ti_a5)) L46a5) in "Hsatp".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb46" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P46 : add_vec_int st_pc46 4 = st_pc47) by (vm_compute; reflexivity).
    iEval (rewrite P46) in "Hpc". iEval (rewrite P46) in "Hnpc".

    (* ---- 47. c.lui a5, 0x10 ---- *)
    assert (Hal2_47 : is_aligned_vaddr (Virtaddr st_pc47) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_47 : is_aligned_vaddr (Virtaddr st_pc47) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_47 : acc_wf st_pc47 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_47 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc47 j)) by ram_win.
    assert (Hcond_47 : subrange_vec_dec stw_47 15 0 = sth_47 /\ isRVC sth_47 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc47 (F_RVC sth_47)) as "#Hbs47".
    { iApply (winstr_bytes_of_text kbs st_pc47 (F_RVC sth_47) stw_47 Hal2_47 Hacc_47 Hram_47
                Hcond_47 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x32) stw_47 Hcov stkb_47). }
    iApply (wwp_lui_rvc_leaf false st_pc47 sth_47 ti_a5 (sign_extend' 20 si47)
              (C_LUI (si47, Regidx ti_a5)) (st_m45 m sp0 ms0) st_pc47
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws46
              Hgid HpmpU Hal2_47 Hal4_47 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_LUI (si47, Regidx ti_a5))
                 (conj (kd_67c1 t HC) (conj stlpad_47 (exec_execute_C_LUI si47 (Regidx ti_a5)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_47 stdec_47 stgoodexp_47 (exec_execute_C_LUI si47 (Regidx ti_a5))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs47 Hhws").
    iIntros (ws47) "%Hwsle47 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws46 ws47 Hwsle47 with "Hstk") as "Hstk".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (luival (sign_extend' 20 si47))]>
                     (st_m45 m sp0 ms0))
             with (st_m47 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P47 : add_vec_int st_pc47 2 = st_pc48) by (vm_compute; reflexivity).
    iEval (rewrite P47) in "Hpc". iEval (rewrite P47) in "Hnpc".

    (* ---- 48. c.addi a5, -1 (a5 := 0xffff) ---- *)
    assert (L48a5 : st_m47 m sp0 ms0 !!! Regidx ti_a5 = luival (sign_extend' 20 si47))
      by (st_unfold; st_look).
    assert (Hal2_48 : is_aligned_vaddr (Virtaddr st_pc48) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_48 : is_aligned_vaddr (Virtaddr st_pc48) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_48 : acc_wf st_pc48 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_48 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc48 j)) by ram_win.
    assert (Hcond_48 : subrange_vec_dec stw_48 15 0 = sth_48 /\ isRVC sth_48 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc48 (F_RVC sth_48)) as "#Hbs48".
    { iApply (winstr_bytes_of_text kbs st_pc48 (F_RVC sth_48) stw_48 Hal2_48 Hacc_48 Hram_48
                Hcond_48 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x34) stw_48 Hcov stkb_48). }
    iApply (wwp_addi_rvc_leaf true st_pc48 sth_48 ti_a5 ti_a5 (sign_extend' 12 si48)
              (C_ADDI (si48, Regidx ti_a5)) (st_m47 m sp0 ms0) st_pc48
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws47
              Hgid HpmpU Hal2_48 Hal4_48 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDI (si48, Regidx ti_a5))
                 (conj (kd_17fd t HC) (conj stlpad_48 (exec_execute_C_ADDI si48 (Regidx ti_a5)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_48 stdec_48 stgoodexp_48 (exec_execute_C_ADDI si48 (Regidx ti_a5))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs48 Hhws").
    iIntros (ws48) "%Hwsle48 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws47 ws48 Hwsle48 with "Hstk") as "Hstk".
    iEval (rewrite L48a5 sext6_12_64 Hffv) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_ffff]> (st_m47 m sp0 ms0))
             with (st_m48 m sp0 ms0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P48 : add_vec_int st_pc48 2 = st_pc49) by (vm_compute; reflexivity).
    iEval (rewrite P48) in "Hpc". iEval (rewrite P48) in "Hnpc".

    (* ---- 49. csrw medeleg, a5 ---- *)
    assert (L49a5 : st_m48 m sp0 ms0 !!! Regidx ti_a5 = st_ffff) by (st_unfold; st_look).
    assert (Hal2_49 : is_aligned_vaddr (Virtaddr st_pc49) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_49 : is_aligned_vaddr (Virtaddr st_pc49) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_49 : acc_wf st_pc49 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_49 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc49 j)) by ram_win.
    assert (Hcond_49 : stw_49 = stw_49 /\ isRVC (subrange_vec_dec stw_49 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc49 (F_Base stw_49)) as "#Hbs49".
    { iApply (winstr_bytes_of_text kbs st_pc49 (F_Base stw_49) stw_49 Hal2_49 Hacc_49 Hram_49
                Hcond_49 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x36) stw_49 Hcov stkb_49). }
    iDestruct (gpr_file_lookup_acc (st_m48 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb49]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_medeleg_leaf false st_pc49 stw_49 ti_a5 medeleg0
              (st_m48 m sp0 ms0 (Regidx ti_a5)) st_pc49 pmpcfg0 (1/2)%Qp D_m dstateM ws48
              Hgid HpmpU Hal2_49 Hal4_49 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_30279073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_49 stdec_49
              with "Hmm HpcfA Hpc Hnpc Ha5c Hmede Hbs49 Hhws").
    iIntros (ws49) "%Hwsle49 Hmm HpcfA Hpc Ha5c Hmede Hhws".
    iDestruct (vwp_hold_mono _ ws48 ws49 Hwsle49 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m48 m sp0 ms0) (Regidx ti_a5)) L49a5) in "Hmede".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb49" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P49 : add_vec_int st_pc49 4 = st_pc50) by (vm_compute; reflexivity).
    iEval (rewrite P49) in "Hpc". iEval (rewrite P49) in "Hnpc".

    (* ---- 50. csrw mideleg, a5 ---- *)
    assert (Hal2_50 : is_aligned_vaddr (Virtaddr st_pc50) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_50 : is_aligned_vaddr (Virtaddr st_pc50) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_50 : acc_wf st_pc50 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_50 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc50 j)) by ram_win.
    assert (Hcond_50 : stw_50 = stw_50 /\ isRVC (subrange_vec_dec stw_50 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc50 (F_Base stw_50)) as "#Hbs50".
    { iApply (winstr_bytes_of_text kbs st_pc50 (F_Base stw_50) stw_50 Hal2_50 Hacc_50 Hram_50
                Hcond_50 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x3a) stw_50 Hcov stkb_50). }
    iDestruct (gpr_file_lookup_acc (st_m48 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb50]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mideleg_leaf false st_pc50 stw_50 ti_a5 mideleg0
              (st_m48 m sp0 ms0 (Regidx ti_a5)) st_pc50 pmpcfg0 (1/2)%Qp D_m dstateM ws49
              Hgid HpmpU Hal2_50 Hal4_50 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_30379073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_50 stdec_50
              with "Hmm HpcfA Hpc Hnpc Ha5c Hmdl Hbs50 Hhws").
    iIntros (ws50) "%Hwsle50 Hmm HpcfA Hpc Ha5c Hmdl Hhws".
    iDestruct (vwp_hold_mono _ ws49 ws50 Hwsle50 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m48 m sp0 ms0) (Regidx ti_a5)) L49a5) in "Hmdl".
    iEval (change (mideleg_legalized mideleg0 st_ffff) with (st_mdl1 mideleg0)) in "Hmdl".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb50" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P50 : add_vec_int st_pc50 4 = st_pc51) by (vm_compute; reflexivity).
    iEval (rewrite P50) in "Hpc". iEval (rewrite P50) in "Hnpc".

    (* ---- 51. csrr a5, sie (a view over mie & mideleg) ---- *)
    assert (Hal2_51 : is_aligned_vaddr (Virtaddr st_pc51) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_51 : is_aligned_vaddr (Virtaddr st_pc51) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_51 : acc_wf st_pc51 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_51 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc51 j)) by ram_win.
    assert (Hcond_51 : stw_51 = stw_51 /\ isRVC (subrange_vec_dec stw_51 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc51 (F_Base stw_51)) as "#Hbs51".
    { iApply (winstr_bytes_of_text kbs st_pc51 (F_Base stw_51) stw_51 Hal2_51 Hacc_51 Hram_51
                Hcond_51 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x3e) stw_51 Hcov stkb_51). }
    iDestruct (gpr_file_insert_acc (st_m48 m sp0 ms0) (Regidx ti_a5)
                 (regval_into_reg (lower_mie mie0 (st_mdl1 mideleg0))) with "Hfile")
      as "[Ha5c Hfins51]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_sie_leaf false st_pc51 stw_51 ti_a5 mie0 (st_mdl1 mideleg0)
              (st_m48 m sp0 ms0 (Regidx ti_a5)) st_pc51 pmpcfg0 (1/2)%Qp D_m dstateM ws50
              Hgid HpmpU Hal2_51 Hal4_51 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_104027f3 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_51 stdec_51
              with "Hmm HpcfA Hpc Hnpc Hmie Hmdl Ha5c Hbs51 Hhws").
    iIntros (ws51) "%Hwsle51 Hmm HpcfA Hpc Ha5c Hmie Hmdl Hhws".
    iDestruct (vwp_hold_mono _ ws50 ws51 Hwsle51 with "Hstk") as "Hstk".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins51" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (lower_mie mie0 (st_mdl1 mideleg0))]>
                     (st_m48 m sp0 ms0))
             with (st_m51 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P51 : add_vec_int st_pc51 4 = st_pc52) by (vm_compute; reflexivity).
    iEval (rewrite P51) in "Hpc". iEval (rewrite P51) in "Hnpc".

    (* ---- 52. ori a5, a5, 544 ---- *)
    assert (L52a5 : st_m51 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = lower_mie mie0 (st_mdl1 mideleg0)) by (st_unfold; st_look).
    assert (Hal2_52 : is_aligned_vaddr (Virtaddr st_pc52) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_52 : is_aligned_vaddr (Virtaddr st_pc52) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_52 : acc_wf st_pc52 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_52 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc52 j)) by ram_win.
    assert (Hcond_52 : stw_52 = stw_52 /\ isRVC (subrange_vec_dec stw_52 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc52 (F_Base stw_52)) as "#Hbs52".
    { iApply (winstr_bytes_of_text kbs st_pc52 (F_Base stw_52) stw_52 Hal2_52 Hacc_52 Hram_52
                Hcond_52 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x42) stw_52 Hcov stkb_52). }
    iApply (wwp_ori_leaf false st_pc52 stw_52 ti_a5 ti_a5 si52
              (st_m51 m sp0 ms0 mie0 mideleg0) st_pc52 pmpcfg0 (1/2)%Qp D_m dstateM ws51
              Hgid HpmpU Hal2_52 Hal4_52 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_2207e793 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_52 stdec_52
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs52 Hhws").
    iIntros (ws52) "%Hwsle52 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws51 ws52 Hwsle52 with "Hstk") as "Hstk".
    iEval (rewrite L52a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (lower_mie mie0 (st_mdl1 mideleg0)) (sign_extend' 64 si52))]>
                     (st_m51 m sp0 ms0 mie0 mideleg0))
             with (st_m52 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P52 : add_vec_int st_pc52 4 = st_pc53) by (vm_compute; reflexivity).
    iEval (rewrite P52) in "Hpc". iEval (rewrite P52) in "Hnpc".

    (* ---- 53. csrw sie, a5 ---- *)
    assert (L53a5 : st_m52 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = st_va5_52 mie0 mideleg0) by (st_unfold; st_look).
    assert (Hal2_53 : is_aligned_vaddr (Virtaddr st_pc53) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_53 : is_aligned_vaddr (Virtaddr st_pc53) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_53 : acc_wf st_pc53 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_53 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc53 j)) by ram_win.
    assert (Hcond_53 : stw_53 = stw_53 /\ isRVC (subrange_vec_dec stw_53 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc53 (F_Base stw_53)) as "#Hbs53".
    { iApply (winstr_bytes_of_text kbs st_pc53 (F_Base stw_53) stw_53 Hal2_53 Hacc_53 Hram_53
                Hcond_53 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x46) stw_53 Hcov stkb_53). }
    iDestruct (gpr_file_lookup_acc (st_m52 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb53]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_sie_leaf false st_pc53 stw_53 ti_a5 mie0 (st_mdl1 mideleg0)
              (st_m52 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) st_pc53
              pmpcfg0 (1/2)%Qp D_m dstateM ws52
              Hgid HpmpU Hal2_53 Hal4_53 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_10479073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_53 stdec_53
              with "Hmm HpcfA Hpc Hnpc Ha5c Hmie Hmdl Hbs53 Hhws").
    iIntros (ws53) "%Hwsle53 Hmm HpcfA Hpc Ha5c Hmie Hmdl Hhws".
    iDestruct (vwp_hold_mono _ ws52 ws53 Hwsle53 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m52 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L53a5) in "Hmie".
    iEval (change (sie_new_mie mie0 (st_mdl1 mideleg0) (st_va5_52 mie0 mideleg0))
             with (st_mie1 mie0 mideleg0)) in "Hmie".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb53" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P53 : add_vec_int st_pc53 4 = st_pc54) by (vm_compute; reflexivity).
    iEval (rewrite P53) in "Hpc". iEval (rewrite P53) in "Hnpc".

    (* ---- 54. c.li a5, -1 ---- *)
    iDestruct (gpr_file_x0 (st_m52 m sp0 ms0 mie0 mideleg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_54 Hfile]".
    assert (Hal2_54 : is_aligned_vaddr (Virtaddr st_pc54) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_54 : is_aligned_vaddr (Virtaddr st_pc54) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_54 : acc_wf st_pc54 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_54 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc54 j)) by ram_win.
    assert (Hcond_54 : subrange_vec_dec stw_54 15 0 = sth_54 /\ isRVC sth_54 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc54 (F_RVC sth_54)) as "#Hbs54".
    { iApply (winstr_bytes_of_text kbs st_pc54 (F_RVC sth_54) stw_54 Hal2_54 Hacc_54 Hram_54
                Hcond_54 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x4a) stw_54 Hcov stkb_54). }
    assert (Hexp_54 : forall s : mstate, exec (execute (C_LI (si54, Regidx ti_a5))) s
              = Some (ExecuteAs (ITYPE (sign_extend' 12 si54, Regidx cli_rs1,
                                        Regidx ti_a5, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_LI si54 (Regidx ti_a5)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_addi_rvc_leaf false st_pc54 sth_54 cli_rs1 ti_a5 (sign_extend' 12 si54)
              (C_LI (si54, Regidx ti_a5)) (st_m52 m sp0 ms0 mie0 mideleg0) st_pc54
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws53
              Hgid HpmpU Hal2_54 Hal4_54 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_LI (si54, Regidx ti_a5))
                 (conj (kd_57fd t HC) (conj stlpad_54 Hexp_54)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_54 stdec_54 stgoodexp_54 Hexp_54
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs54 Hhws").
    iIntros (ws54) "%Hwsle54 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws53 ws54 Hwsle54 with "Hstk") as "Hstk".
    iEval (rewrite Hx0_54 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (cli_wval si54)]>
                     (st_m52 m sp0 ms0 mie0 mideleg0))
             with (st_m54 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P54 : add_vec_int st_pc54 2 = st_pc55) by (vm_compute; reflexivity).
    iEval (rewrite P54) in "Hpc". iEval (rewrite P54) in "Hnpc".

    (* ---- 55. c.srli a5, 10 (a5 := 0x3fffffffffffff) ---- *)
    assert (L55a5 : st_m54 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = cli_wval si54)
      by (st_unfold; st_look).
    assert (Hal2_55 : is_aligned_vaddr (Virtaddr st_pc55) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_55 : is_aligned_vaddr (Virtaddr st_pc55) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_55 : acc_wf st_pc55 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_55 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc55 j)) by ram_win.
    assert (Hcond_55 : subrange_vec_dec stw_55 15 0 = sth_55 /\ isRVC sth_55 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc55 (F_RVC sth_55)) as "#Hbs55".
    { iApply (winstr_bytes_of_text kbs st_pc55 (F_RVC sth_55) stw_55 Hal2_55 Hacc_55 Hram_55
                Hcond_55 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x4c) stw_55 Hcov stkb_55). }
    assert (Hexp_55 : forall s : mstate,
              exec (execute (C_SRLI (ssh55, Cregidx (mword_of_int 7)))) s
              = Some (ExecuteAs (SHIFTIOP (ssh55, Regidx ti_a5, Regidx ti_a5, SRLI)), s)).
    { intro s. rewrite (exec_execute_C_SRLI ssh55 (Cregidx (mword_of_int 7))).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_srli_rvc_leaf true st_pc55 sth_55 ti_a5 ti_a5 ssh55
              (C_SRLI (ssh55, Cregidx (mword_of_int 7))) (st_m54 m sp0 ms0 mie0 mideleg0) st_pc55
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws54
              Hgid HpmpU Hal2_55 Hal4_55 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_SRLI (ssh55, Cregidx (mword_of_int 7)))
                 (conj (kd_83a9 t HC) (conj stlpad_55 Hexp_55)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_55 stdec_55 stgoodexp_55 Hexp_55
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs55 Hhws").
    iIntros (ws55) "%Hwsle55 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws54 ws55 Hwsle55 with "Hstk") as "Hstk".
    iEval (rewrite L55a5 Hshv) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_pmpw]> (st_m54 m sp0 ms0 mie0 mideleg0))
             with (st_m55 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P55 : add_vec_int st_pc55 2 = st_pc56) by (vm_compute; reflexivity).
    iEval (rewrite P55) in "Hpc". iEval (rewrite P55) in "Hnpc".

    (* ---- 56. csrw pmpaddr0, a5 ---- *)
    assert (L56a5 : st_m55 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = st_pmpw)
      by (st_unfold; st_look).
    assert (Hal2_56 : is_aligned_vaddr (Virtaddr st_pc56) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_56 : is_aligned_vaddr (Virtaddr st_pc56) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_56 : acc_wf st_pc56 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_56 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc56 j)) by ram_win.
    assert (Hcond_56 : stw_56 = stw_56 /\ isRVC (subrange_vec_dec stw_56 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc56 (F_Base stw_56)) as "#Hbs56".
    { iApply (winstr_bytes_of_text kbs st_pc56 (F_Base stw_56) stw_56 Hal2_56 Hacc_56 Hram_56
                Hcond_56 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x4e) stw_56 Hcov stkb_56). }
    iDestruct (gpr_file_lookup_acc (st_m55 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb56]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_pmpaddr0_leaf false st_pc56 stw_56 ti_a5
              (st_m55 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) st_pc56
              pmpaddr00 pmpcfg0 (1/2)%Qp D_m dstateM ws55
              Hgid HpmpU Hal2_56 Hal4_56 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_3b079073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_56 stdec_56
              with "Hmm HpcfA Hpc Hnpc Ha5c Hpaddr Hbs56 Hhws").
    iIntros (ws56) "%Hwsle56 Hmm HpcfA Hpc Ha5c Hpaddr Hhws".
    iDestruct (vwp_hold_mono _ ws55 ws56 Hwsle56 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m55 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L56a5) in "Hpaddr".
    iEval (change (pmp0_newaddr pmpcfg0 pmpaddr00 st_pmpw)
             with (st_pmpaddr1 pmpcfg0 pmpaddr00)) in "Hpaddr".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb56" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P56 : add_vec_int st_pc56 4 = st_pc57) by (vm_compute; reflexivity).
    iEval (rewrite P56) in "Hpc". iEval (rewrite P56) in "Hnpc".

    (* ---- 57. c.li a5, 15 ---- *)
    iDestruct (gpr_file_x0 (st_m55 m sp0 ms0 mie0 mideleg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_57 Hfile]".
    assert (Hal2_57 : is_aligned_vaddr (Virtaddr st_pc57) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_57 : is_aligned_vaddr (Virtaddr st_pc57) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_57 : acc_wf st_pc57 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_57 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc57 j)) by ram_win.
    assert (Hcond_57 : subrange_vec_dec stw_57 15 0 = sth_57 /\ isRVC sth_57 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc57 (F_RVC sth_57)) as "#Hbs57".
    { iApply (winstr_bytes_of_text kbs st_pc57 (F_RVC sth_57) stw_57 Hal2_57 Hacc_57 Hram_57
                Hcond_57 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x52) stw_57 Hcov stkb_57). }
    assert (Hexp_57 : forall s : mstate, exec (execute (C_LI (si57, Regidx ti_a5))) s
              = Some (ExecuteAs (ITYPE (sign_extend' 12 si57, Regidx cli_rs1,
                                        Regidx ti_a5, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_LI si57 (Regidx ti_a5)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_addi_rvc_leaf false st_pc57 sth_57 cli_rs1 ti_a5 (sign_extend' 12 si57)
              (C_LI (si57, Regidx ti_a5)) (st_m55 m sp0 ms0 mie0 mideleg0) st_pc57
              pmpcfg0 (1/2)%Qp D_m D_none dstateM ws56
              Hgid HpmpU Hal2_57 Hal4_57 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_LI (si57, Regidx ti_a5))
                 (conj (kd_47bd t HC) (conj stlpad_57 Hexp_57)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_57 stdec_57 stgoodexp_57 Hexp_57
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs57 Hhws").
    iIntros (ws57) "%Hwsle57 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws56 ws57 Hwsle57 with "Hstk") as "Hstk".
    iEval (rewrite Hx0_57 add_vec_zero_l sext6_12_64 H15v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 15)]>
                     (st_m55 m sp0 ms0 mie0 mideleg0))
             with (st_m57 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P57 : add_vec_int st_pc57 2 = st_pc58) by (vm_compute; reflexivity).
    iEval (rewrite P57) in "Hpc". iEval (rewrite P57) in "Hnpc".

    (* ---- 58. csrw pmpcfg0, a5: the second config-funnel site ---- *)
    assert (L58a5 : st_m57 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = (mword_of_int 15 : mword 64)) by (st_unfold; st_look).
    assert (Hal2_58 : is_aligned_vaddr (Virtaddr st_pc58) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_58 : is_aligned_vaddr (Virtaddr st_pc58) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_58 : acc_wf st_pc58 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_58 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc58 j)) by ram_win.
    assert (Hcond_58 : stw_58 = stw_58 /\ isRVC (subrange_vec_dec stw_58 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc58 (F_Base stw_58)) as "#Hbs58".
    { iApply (winstr_bytes_of_text kbs st_pc58 (F_Base stw_58) stw_58 Hal2_58 Hacc_58 Hram_58
                Hcond_58 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x54) stw_58 Hcov stkb_58). }
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms2') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    iDestruct (gpr_file_lookup_acc (st_m57 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb58]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_pmpcfg0_leaf true st_pc58 stw_58 ti_a5 (st_ms1 ms0)
              (st_m57 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) st_pc58
              pmpcfg0 D_m dstateM ws57
              Hgid HpmpU Hal2_58 Hal4_58 Hnz_a5 HmIE1 HMPRV1
              (fun t _ _ _ Hmi Hcfg => kd_3a079073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_58 stdec_58
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Ha5c Hbs58 Hhws").
    iIntros (ws58) "%Hwsle58 Hhs Hpriv Hms Hpcf Hpc Ha5c Hhws".
    iDestruct (vwp_hold_mono _ ws57 ws58 Hwsle58 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m57 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L58a5) in "Hpcf".
    iEval (change (pmpcfg_written (mword_of_int 15) pmpcfg0) with (st_pmpcfg1 pmpcfg0)) in "Hpcf".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1 HKF1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb58" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P58 : add_vec_int st_pc58 4 = st_pc_ae0) by (vm_compute; reflexivity).
    iEval (rewrite P58) in "Hpc". iEval (rewrite P58) in "Hnpc".

    (* ---- ae0. csrr a5, menvcfg (the ADUE read-modify-write) ---- *)
    assert (Hal2_ae0 : is_aligned_vaddr (Virtaddr st_pc_ae0) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_ae0 : is_aligned_vaddr (Virtaddr st_pc_ae0) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_ae0 : acc_wf st_pc_ae0 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_ae0 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc_ae0 j)) by ram_win.
    assert (Hcond_ae0 : stw_ae0 = stw_ae0 /\ isRVC (subrange_vec_dec stw_ae0 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc_ae0 (F_Base stw_ae0)) as "#Hbsae0".
    { iApply (winstr_bytes_of_text kbs st_pc_ae0 (F_Base stw_ae0) stw_ae0 Hal2_ae0 Hacc_ae0
                Hram_ae0 Hcond_ae0 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x58) stw_ae0 Hcov stkb_ae0). }
    iDestruct (gpr_file_insert_acc (st_m57 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)
                 (regval_into_reg menvcfg0) with "Hfile") as "[Ha5c Hfinsae0]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_menvcfg_leaf true st_pc_ae0 stw_ae0 ti_a5 menvcfg0
              (st_m57 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) st_pc_ae0
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m dstateM ws58
              Hgid Hpmp1 Hal2_ae0 Hal4_ae0 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_30a027f3 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_ae0 stdec_ae0
              with "Hmm HpcfA Hpc Hnpc Hmenv Ha5c Hbsae0 Hhws").
    iIntros (wsae0) "%Hwsleae0 Hmm HpcfA Hpc Ha5c Hmenv Hhws".
    iDestruct (vwp_hold_mono _ ws58 wsae0 Hwsleae0 with "Hstk") as "Hstk".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfinsae0" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menvcfg0]> (st_m57 m sp0 ms0 mie0 mideleg0))
             with (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (Pae0 : add_vec_int st_pc_ae0 4 = st_pc_ae1) by (vm_compute; reflexivity).
    iEval (rewrite Pae0) in "Hpc". iEval (rewrite Pae0) in "Hnpc".

    (* ---- ae1. c.li a4, 1 ---- *)
    iDestruct (gpr_file_x0 (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_ae1 Hfile]".
    assert (Hal2_ae1 : is_aligned_vaddr (Virtaddr st_pc_ae1) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_ae1 : is_aligned_vaddr (Virtaddr st_pc_ae1) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_ae1 : acc_wf st_pc_ae1 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_ae1 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc_ae1 j)) by ram_win.
    assert (Hcond_ae1 : subrange_vec_dec stw_ae1 15 0 = sth_ae1 /\ isRVC sth_ae1 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc_ae1 (F_RVC sth_ae1)) as "#Hbsae1".
    { iApply (winstr_bytes_of_text kbs st_pc_ae1 (F_RVC sth_ae1) stw_ae1 Hal2_ae1 Hacc_ae1
                Hram_ae1 Hcond_ae1 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x5c) stw_ae1 Hcov stkb_ae1). }
    assert (Hexp_ae1 : forall s : mstate, exec (execute (C_LI (sae_li, Regidx ti_a4))) s
              = Some (ExecuteAs (ITYPE (sign_extend' 12 sae_li, Regidx cli_rs1,
                                        Regidx ti_a4, ADDI)), s)).
    { intro s. rewrite (exec_execute_C_LI sae_li (Regidx ti_a4)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_addi_rvc_leaf true st_pc_ae1 sth_ae1 cli_rs1 ti_a4 (sign_extend' 12 sae_li)
              (C_LI (sae_li, Regidx ti_a4)) (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) st_pc_ae1
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m D_none dstateM wsae0
              Hgid Hpmp1 Hal2_ae1 Hal4_ae1 Hnz_a4
              (fun t _ HC _ _ _ => ex_intro _ (C_LI (sae_li, Regidx ti_a4))
                 (conj (kd_4705 t HC) (conj stlpad_ae1 Hexp_ae1)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_ae1 stdec_ae1 stgoodexp_ae1 Hexp_ae1
              with "Hmm HpcfA Hpc Hnpc Hfile Hbsae1 Hhws").
    iIntros (wsae1) "%Hwsleae1 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ wsae0 wsae1 Hwsleae1 with "Hstk") as "Hstk".
    iEval (rewrite Hx0_ae1 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval sae_li)]>
                     (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (Pae1 : add_vec_int st_pc_ae1 2 = st_pc_ae2) by (vm_compute; reflexivity).
    iEval (rewrite Pae1) in "Hpc". iEval (rewrite Pae1) in "Hnpc".

    (* ---- ae2. c.slli a4, 0x3d (a4 := 1<<61) ---- *)
    assert (L_ae2a4 : st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4
                      = cli_wval sae_li) by (st_unfold; st_look).
    assert (Hal2_ae2 : is_aligned_vaddr (Virtaddr st_pc_ae2) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_ae2 : is_aligned_vaddr (Virtaddr st_pc_ae2) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_ae2 : acc_wf st_pc_ae2 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_ae2 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc_ae2 j)) by ram_win.
    assert (Hcond_ae2 : subrange_vec_dec stw_ae2 15 0 = sth_ae2 /\ isRVC sth_ae2 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc_ae2 (F_RVC sth_ae2)) as "#Hbsae2".
    { iApply (winstr_bytes_of_text kbs st_pc_ae2 (F_RVC sth_ae2) stw_ae2 Hal2_ae2 Hacc_ae2
                Hram_ae2 Hcond_ae2 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x5e) stw_ae2 Hcov stkb_ae2). }
    iApply (wwp_slli_rvc_leaf false st_pc_ae2 sth_ae2 ti_a4 ti_a4 sae_slli
              (C_SLLI (sae_slli, Regidx ti_a4)) (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0)
              st_pc_ae2 (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m D_none dstateM wsae1
              Hgid Hpmp1 Hal2_ae2 Hal4_ae2 Hnz_a4
              (fun t _ HC _ _ _ => ex_intro _ (C_SLLI (sae_slli, Regidx ti_a4))
                 (conj (kd_1776 t HC)
                       (conj stlpad_ae2 (exec_execute_C_SLLI sae_slli (Regidx ti_a4)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_ae2 stdec_ae2 stgoodexp_ae2
              (exec_execute_C_SLLI sae_slli (Regidx ti_a4))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbsae2 Hhws").
    iIntros (wsae2) "%Hwsleae2 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ wsae1 wsae2 Hwsleae2 with "Hstk") as "Hstk".
    iEval (rewrite L_ae2a4 st_Hb61) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_adue_bit]>
                     (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (Pae2 : add_vec_int st_pc_ae2 2 = st_pc_ae3) by (vm_compute; reflexivity).
    iEval (rewrite Pae2) in "Hpc". iEval (rewrite Pae2) in "Hnpc".

    (* ---- ae3. c.or a5, a4 ---- *)
    assert (L_ae3a5 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5 = menvcfg0)
      by (st_unfold; st_look).
    assert (L_ae3a4 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4 = st_adue_bit)
      by (st_unfold; st_look).
    assert (Hal2_ae3 : is_aligned_vaddr (Virtaddr st_pc_ae3) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_ae3 : is_aligned_vaddr (Virtaddr st_pc_ae3) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_ae3 : acc_wf st_pc_ae3 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_ae3 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc_ae3 j)) by ram_win.
    assert (Hcond_ae3 : subrange_vec_dec stw_ae3 15 0 = sth_ae3 /\ isRVC sth_ae3 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc_ae3 (F_RVC sth_ae3)) as "#Hbsae3".
    { iApply (winstr_bytes_of_text kbs st_pc_ae3 (F_RVC sth_ae3) stw_ae3 Hal2_ae3 Hacc_ae3
                Hram_ae3 Hcond_ae3 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x60) stw_ae3 Hcov stkb_ae3). }
    iApply (wwp_or_rvc_leaf true st_pc_ae3 sth_ae3 ti_a4 ti_a5 ti_a5
              (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
              (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0) st_pc_ae3
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m D_none dstateM wsae2
              Hgid Hpmp1 Hal2_ae3 Hal4_ae3 Hnz_a5
              (fun t _ HC _ _ _ =>
                 ex_intro _ (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))
                   (conj (kd_8fd9 t HC) (conj stlpad_ae3 Hexp_40)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_ae3 stdec_ae3 stgoodexp_ae3 Hexp_40
              with "Hmm HpcfA Hpc Hnpc Hfile Hbsae3 Hhws").
    iIntros (wsae3) "%Hwsleae3 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ wsae2 wsae3 Hwsleae3 with "Hstk") as "Hstk".
    iEval (rewrite L_ae3a5 L_ae3a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menvcfg0 st_adue_bit)]>
                     (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (Pae3 : add_vec_int st_pc_ae3 2 = st_pc_ae4) by (vm_compute; reflexivity).
    iEval (rewrite Pae3) in "Hpc". iEval (rewrite Pae3) in "Hnpc".

    (* ---- ae4. csrw menvcfg, a5 ---- *)
    assert (L_ae4a5 : st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5
                      = or_vec menvcfg0 st_adue_bit) by (st_unfold; st_look).
    assert (Hal2_ae4 : is_aligned_vaddr (Virtaddr st_pc_ae4) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_ae4 : is_aligned_vaddr (Virtaddr st_pc_ae4) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_ae4 : acc_wf st_pc_ae4 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_ae4 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc_ae4 j)) by ram_win.
    assert (Hcond_ae4 : stw_ae4 = stw_ae4 /\ isRVC (subrange_vec_dec stw_ae4 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc_ae4 (F_Base stw_ae4)) as "#Hbsae4".
    { iApply (winstr_bytes_of_text kbs st_pc_ae4 (F_Base stw_ae4) stw_ae4 Hal2_ae4 Hacc_ae4
                Hram_ae4 Hcond_ae4 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x62) stw_ae4 Hcov stkb_ae4). }
    iDestruct (gpr_file_lookup_acc (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_a5)
                 with "Hfile") as "[Ha5c Hfbae4]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_menvcfg_leaf false st_pc_ae4 stw_ae4 ti_a5 menvcfg0
              (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 (Regidx ti_a5)) st_pc_ae4
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m dstateM wsae3
              Hgid Hpmp1 Hal2_ae4 Hal4_ae4 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_30a79073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_ae4 stdec_ae4
              with "Hmm HpcfA Hpc Hnpc Ha5c Hmenv Hbsae4 Hhws").
    iIntros (wsae4) "%Hwsleae4 Hmm HpcfA Hpc Ha5c Hmenv Hhws".
    iDestruct (vwp_hold_mono _ wsae3 wsae4 Hwsleae4 with "Hstk") as "Hstk".
    iEval (rewrite -(rf_lookup (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_a5))
             L_ae4a5) in "Hmenv".
    iEval (change (menvcfg_legalized menvcfg0 (or_vec menvcfg0 st_adue_bit))
             with (st_menv_adue menvcfg0)) in "Hmenv".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfbae4" with "Ha5c") as "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (Pae4 : add_vec_int st_pc_ae4 4 = st_pc59) by (vm_compute; reflexivity).
    iEval (rewrite Pae4) in "Hpc". iEval (rewrite Pae4) in "Hnpc".

    (* ---- 59. jal ra, timerinit (PC := timerinit's entry) ---- *)
    assert (Hal2_59 : is_aligned_vaddr (Virtaddr st_pc59) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_59 : is_aligned_vaddr (Virtaddr st_pc59) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_59 : acc_wf st_pc59 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_59 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc59 j)) by ram_win.
    assert (Hcond_59 : stw_59 = stw_59 /\ isRVC (subrange_vec_dec stw_59 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc59 (F_Base stw_59)) as "#Hbs59".
    { iApply (winstr_bytes_of_text kbs st_pc59 (F_Base stw_59) stw_59 Hal2_59 Hacc_59 Hram_59
                Hcond_59 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x66) stw_59 Hcov stkb_59). }
    iDestruct (gpr_file_insert_acc (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_ra)
                 (regval_into_reg (add_vec_int st_pc59 4)) with "Hfile") as "[Hrac Hfins59]".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_jal_leaf false st_pc59 stw_59 ti_ra sjimm59
              (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 (Regidx ti_ra)) st_pc59
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m dstateM wsae4
              Hgid Hpmp1 Hal2_59 Hal4_59 Hnz_ra Hjal_al
              (fun t _ _ _ Hmi Hcfg => kd_f5fff0ef t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_59 stdec_59
              with "Hmm HpcfA Hpc Hnpc Hrac Hbs59 Hhws").
    iIntros (ws59) "%Hwsle59 Hmm HpcfA Hpc Hrac Hhws".
    iDestruct (vwp_hold_mono _ wsae4 ws59 Hwsle59 with "Hstk") as "Hstk".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfins59" with "Hrac") as "Hfile".
    iEval (rewrite Hlinkv) in "Hfile".
    iEval (change (<[Regidx ti_ra := regval_into_reg st_ra_link]>
                     (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iEval (rewrite P59) in "Hpc".

    (* ---- timerinit() (21 instructions), at q = 1/2 ---- *)
    assert (L59sp : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (st_unfold; st_look).
    assert (L59ra : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_ra = st_ra_link)
      by (st_unfold; st_look).
    assert (L59s0 : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_s0 = sp0)
      by (st_unfold; st_look).
    iDestruct "Hpaddr" as "[HpaA HpaK]".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hsra Hstk]".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hss0 Hstk]".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hti2 Hdeep]".
    iApply (wwp_timerinit (1/2)%Qp (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
              st_ra_link sp0 (st_menv_adue menvcfg0) stimecmp0 mcounteren0
              (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00) 2 kbs ws59
              ltac:(lia) Hgid Hpmp1 Htor_ra Htor_s0 Hcov L59sp L59ra L59s0
              Hram8_ti_ra Hram8_ti_s0
              with "Hmm HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Hhws Hti2 Htext").
    iIntros (tv wsti) "%Hwsleti Hmm HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Hhws Hti2".
    iDestruct (vwp_hold_mono _ ws59 wsti Hwsleti with "Hsra") as "Hsra".
    iDestruct (vwp_hold_mono _ ws59 wsti Hwsleti with "Hss0") as "Hss0".
    iDestruct (vwp_hold_mono _ ws59 wsti Hwsleti with "Hdeep") as "Hdeep".
    iAssert (vwp_hold (wpt8 (ti_ea_ra sp0) (DfracOwn 1) ra0 ∗
                       wpt8 (ti_ea_s0 sp0) (DfracOwn 1) s00 ∗
                       wstack_own_phys (ti_sp1 sp0) 2 ∗
                       wstack_own_phys (pa_stk sp0 4) (n - 4)) wsti)
      with "[Hsra Hss0 Hti2 Hdeep]" as "Hstk".
    (* peel ONE [∗] at a time: [rewrite !vwp_hold_sep] would recurse into
       [wpt8]'s own ∗-chain (alignment + wrap-freedom + 8 bytes) and leave
       [iFrame] nothing to match the unshattered [Hsra]/[Hss0] against. *)
    { iEval (rewrite vwp_hold_sep). iSplitL "Hsra"; [iExact "Hsra"|].
      iEval (rewrite vwp_hold_sep). iSplitL "Hss0"; [iExact "Hss0"|].
      iEval (rewrite vwp_hold_sep). iSplitL "Hti2"; [iExact "Hti2"|iExact "Hdeep"]. }
    iEval (rewrite Hcretv) in "Hpc".
    iEval (change (ti_mout (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
                     (st_menv_adue menvcfg0) mcounteren0 tv st_ra_link sp0)
             with (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)) in "Hfile".
    iDestruct (reg_half_join with "HpaA HpaK") as "Hpaddr".
    iDestruct "Hpc" as "[Hpc Hnpc]".

    (* ---- 60. csrr a5, mhartid ---- *)
    assert (Hal2_60 : is_aligned_vaddr (Virtaddr st_pc60) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_60 : is_aligned_vaddr (Virtaddr st_pc60) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_60 : acc_wf st_pc60 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_60 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc60 j)) by ram_win.
    assert (Hcond_60 : stw_60 = stw_60 /\ isRVC (subrange_vec_dec stw_60 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc60 (F_Base stw_60)) as "#Hbs60".
    { iApply (winstr_bytes_of_text kbs st_pc60 (F_Base stw_60) stw_60 Hal2_60 Hacc_60 Hram_60
                Hcond_60 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x6a) stw_60 Hcov stkb_60). }
    iDestruct (gpr_file_insert_acc (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)
                 (Regidx ti_a5) (regval_into_reg mhartid_in) with "Hfile") as "[Ha5c Hfins60]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_mhartid_leaf false st_pc60 stw_60 ti_a5 mhartid_in
              (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv (Regidx ti_a5)) st_pc60
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m dstateM wsti
              Hgid Hpmp1 Hal2_60 Hal4_60 Hnz_a5
              (fun t _ _ _ Hmi Hcfg => kd_f14027f3 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_60 stdec_60
              with "Hmm HpcfA Hpc Hnpc Hmh Ha5c Hbs60 Hhws").
    iIntros (ws60) "%Hwsle60 Hmm HpcfA Hpc Ha5c Hmh Hhws".
    iDestruct (vwp_hold_mono _ wsti ws60 Hwsle60 with "Hstk") as "Hstk".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins60" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg mhartid_in]>
                     (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv))
             with (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P60 : add_vec_int st_pc60 4 = st_pc61) by (vm_compute; reflexivity).
    iEval (rewrite P60) in "Hpc". iEval (rewrite P60) in "Hnpc".

    (* ---- 61. c.addiw a5, 0 (sext.w) ---- *)
    assert (L61a5 : st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = mhartid_in) by (st_unfold; st_look).
    assert (Hal2_61 : is_aligned_vaddr (Virtaddr st_pc61) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_61 : is_aligned_vaddr (Virtaddr st_pc61) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_61 : acc_wf st_pc61 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_61 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc61 j)) by ram_win.
    assert (Hcond_61 : subrange_vec_dec stw_61 15 0 = sth_61 /\ isRVC sth_61 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc61 (F_RVC sth_61)) as "#Hbs61".
    { iApply (winstr_bytes_of_text kbs st_pc61 (F_RVC sth_61) stw_61 Hal2_61 Hacc_61 Hram_61
                Hcond_61 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x6e) stw_61 Hcov stkb_61). }
    iApply (wwp_addiw_rvc_leaf false st_pc61 sth_61 ti_a5 ti_a5 (sign_extend' 12 si61)
              (C_ADDIW (si61, Regidx ti_a5))
              (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in) st_pc61
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m D_none dstateM ws60
              Hgid Hpmp1 Hal2_61 Hal4_61 Hnz_a5
              (fun t _ HC _ _ _ => ex_intro _ (C_ADDIW (si61, Regidx ti_a5))
                 (conj (kd_2781 t HC)
                       (conj stlpad_61 (exec_execute_C_ADDIW si61 (Regidx ti_a5)))))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_61 stdec_61 stgoodexp_61 (exec_execute_C_ADDIW si61 (Regidx ti_a5))
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs61 Hhws").
    iIntros (ws61) "%Hwsle61 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws60 ws61 Hwsle61 with "Hstk") as "Hstk".
    iEval (rewrite sext6_12_64 L61a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (st_tpv mhartid_in)]>
                     (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P61 : add_vec_int st_pc61 2 = st_pc62) by (vm_compute; reflexivity).
    iEval (rewrite P61) in "Hpc". iEval (rewrite P61) in "Hnpc".

    (* ---- 62. c.mv tp, a5 ---- *)
    assert (L62a5 : st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = st_tpv mhartid_in) by (st_unfold; st_look).
    iDestruct (gpr_file_x0 (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
                 cli_rs1 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_62 Hfile]".
    assert (Hal2_62 : is_aligned_vaddr (Virtaddr st_pc62) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_62 : is_aligned_vaddr (Virtaddr st_pc62) 4 = true) by (vm_compute; reflexivity).
    assert (Hacc_62 : acc_wf st_pc62 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_62 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc62 j)) by ram_win.
    assert (Hcond_62 : subrange_vec_dec stw_62 15 0 = sth_62 /\ isRVC sth_62 = true)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc62 (F_RVC sth_62)) as "#Hbs62".
    { iApply (winstr_bytes_of_text kbs st_pc62 (F_RVC sth_62) stw_62 Hal2_62 Hacc_62 Hram_62
                Hcond_62 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x70) stw_62 Hcov stkb_62). }
    assert (Hexp_62 : forall s : mstate,
              exec (execute (C_MV (Regidx st_tp, Regidx ti_a5))) s
              = Some (ExecuteAs (RTYPE (Regidx ti_a5, Regidx cli_rs1, Regidx st_tp, ADD)), s)).
    { intro s. rewrite (exec_execute_C_MV (Regidx st_tp) (Regidx ti_a5)).
      repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]. }
    iApply (wwp_add_rvc_leaf true st_pc62 sth_62 ti_a5 cli_rs1 st_tp
              (C_MV (Regidx st_tp, Regidx ti_a5))
              (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in) st_pc62
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp D_m D_none dstateM ws61
              Hgid Hpmp1 Hal2_62 Hal4_62 Hnz_tp
              (fun t _ HC _ _ _ => ex_intro _ (C_MV (Regidx st_tp, Regidx ti_a5))
                 (conj (kd_823e t HC) (conj stlpad_62 Hexp_62)))
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_62 stdec_62 stgoodexp_62 Hexp_62
              with "Hmm HpcfA Hpc Hnpc Hfile Hbs62 Hhws").
    iIntros (ws62) "%Hwsle62 Hmm HpcfA Hpc Hfile Hhws".
    iDestruct (vwp_hold_mono _ ws61 ws62 Hwsle62 with "Hstk") as "Hstk".
    iEval (rewrite Hx0_62 add_vec_zero_l L62a5) in "Hfile".
    iEval (change (<[Regidx st_tp := regval_into_reg (st_tpv mhartid_in)]>
                     (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    iDestruct "Hpc" as "[Hpc Hnpc]".
    assert (P62 : add_vec_int st_pc62 2 = st_pc63) by (vm_compute; reflexivity).
    iEval (rewrite P62) in "Hpc". iEval (rewrite P62) in "Hnpc".

    (* ---- 63. MRET into Supervisor mode at <main>. ---- *)
    assert (Hal2_63 : is_aligned_vaddr (Virtaddr st_pc63) 2 = true) by (vm_compute; reflexivity).
    assert (Hal4_63 : is_aligned_vaddr (Virtaddr st_pc63) 4 = false) by (vm_compute; reflexivity).
    assert (Hacc_63 : acc_wf st_pc63 4) by (apply acc_wf_of_leb; vm_compute; reflexivity).
    assert (Hram_63 : forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add st_pc63 j)) by ram_win.
    assert (Hcond_63 : stw_63 = stw_63 /\ isRVC (subrange_vec_dec stw_63 15 0) = false)
      by (split; [apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity]).
    iAssert (winstr_bytes st_pc63 (F_Base stw_63)) as "#Hbs63".
    { iApply (winstr_bytes_of_text kbs st_pc63 (F_Base stw_63) stw_63 Hal2_63 Hacc_63 Hram_63
                Hcond_63 with "Htext").
      iPureIntro. exact (wkb_window kbs (KernelSyms.start + 0x72) stw_63 Hcov stkb_63). }
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms3') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    assert (Hnp : privLevel_bits_forwards (_get_Mstatus_MPP (cms2 (st_ms1 ms0)), ('b"0"))
                  = returnM Supervisor) by (apply st_mret_priv).
    assert (HlpeF : _get_MEnvcfg_LPE
                      (menvcfg_legalized (st_menv_adue menvcfg0)
                         (ti_menv1 (st_menv_adue menvcfg0))) = ('b"0"))
      by (apply st_menvcfg_LPE_final; apply st_menv_adue_LPE; exact HlpeE).
    iApply (wwp_mret_leaf false st_pc63 stw_63 Supervisor (st_ms1 ms0) st_main
              (menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)))
              st_pc63 (st_pmpcfg1 pmpcfg0) D_m dstateM ws62
              Hgid Hpmp1 Hal2_63 Hal4_63 HmIE1 HMPRV1 Hnp eq_refl HlpeF
              (fun t _ _ _ Hmi Hcfg => kd_30200073 t Hmi Hcfg)
              (fun rs Hp Hmi Hsec => agree_m_regs rs Hp Hsec Hmi)
              D_m_mi stgood_63 stdec_63
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hnpc Hmenv Hmepc Hbs63 Hhws").
    iIntros (ws63) "%Hwsle63 Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc Hhws".
    iDestruct (vwp_hold_mono _ ws62 ws63 Hwsle63 with "Hstk") as "Hstk".
    iEval (rewrite Hctgtv) in "Hpc".

    (* ---- re-bundle start's own frame and hand everything to the caller ---- *)
    pose proof (transitivity Hle_ws_32 (transitivity Hwsle33 (transitivity Hwsle34
      (transitivity Hwsle35 (transitivity Hwsle36 (transitivity Hwsle37 (transitivity
      Hwsle38 (transitivity Hwsle39 (transitivity Hwsle40 (transitivity Hwsle41
      (transitivity Hwsle42 (transitivity Hwsle43 (transitivity Hwsle44 (transitivity
      Hwsle45 (transitivity Hwsle46 (transitivity Hwsle47 (transitivity Hwsle48
      (transitivity Hwsle49 (transitivity Hwsle50 (transitivity Hwsle51 (transitivity
      Hwsle52 (transitivity Hwsle53 (transitivity Hwsle54 (transitivity Hwsle55
      (transitivity Hwsle56 (transitivity Hwsle57 (transitivity Hwsle58 (transitivity
      Hwsleae0 (transitivity Hwsleae1 (transitivity Hwsleae2 (transitivity Hwsleae3
      (transitivity Hwsleae4 (transitivity Hwsle59 (transitivity Hwsleti (transitivity
      Hwsle60 (transitivity Hwsle61 (transitivity Hwsle62
      (Hwsle63)))))))))))))))))))))))))))))))))))))) as Hle_ws_final.
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hsra Hstk]".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hss0 Hstk]".
    iEval (rewrite vwp_hold_sep) in "Hstk". iDestruct "Hstk" as "[Hti2 Hdeep]".
    iEval (rewrite Hb1) in "Hsra". iEval (rewrite Hb2) in "Hss0".
    iAssert (vwp_hold (wstack_own_phys sp0 2) ws63) with "[Hsra Hss0]" as "Ht12".
    { iApply (vwp_hold_ent _ _ ws63 (wstack2_intro_ent sp0 ra0 s00)).
      iEval (rewrite vwp_hold_sep). iFrame. }
    iEval (rewrite Hb0) in "Hti2".
    iAssert (vwp_hold (wstack_own_phys sp0 4) ws63) with "[Ht12 Hti2]" as "Htop".
    { iApply (vwp_hold_ent _ _ ws63 (wstack_own_phys_split_2 sp0 2 4 ltac:(lia))).
      iEval (rewrite vwp_hold_sep). iFrame. }
    iAssert (vwp_hold (wstack_own_phys sp0 n) ws63) with "[Htop Hdeep]" as "Hstk".
    { iApply (vwp_hold_ent _ _ ws63 (wstack_own_phys_split_2 sp0 4 n ltac:(lia))).
      iEval (rewrite vwp_hold_sep). iFrame. }
    iApply ("Hcont" $! tv ms0 HoIE HoPRV HoSXL HoKF ws63 with
              "[%] Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl
               Hmie Hmenv Hmcen Hstc Hhws Hstk").
    exact Hle_ws_final.
  Qed.

End WkStartThm.


(** * WkStartNew.v -- the weak-tier [start()] boot chain (M4: the second
      whole-function port, after [wwp_entry]).

    The weak twin of [WpStartNew.wp_start]: xv6's [start()] (39 instructions
    at [KernelSyms.start] .. +0x72, INCLUDING the call to [timerinit()]) as
    ONE [WWP] theorem, with the SC statement's spellings swapped per the
    porting guide (claude-notes/projects/weak-memory-porting.md):

      - [kernel_text] -> [WeakInstr.wkernel_text kbs] + the [wkb_covers]
        coverage premise (WkEntryNew's kernel-text seam);
      - [mmode_config (DfracOwn 1)] -> [WeakLeafO.whart_run ξ 1] (the bundle
        with this hart's view token riding inside it);
      - [stack_own_phys sp0 n] -> [cobj ξ (WkStackOwn.wstack_own_phys sp0 n)]
        -- OBJECTIVE ownership at the execution context.  There is NO
        [wstate] in the statement, no [ws_le] and no view inequality in the
        continuation: the frames are [cobj]s, which cross a step untouched,
        so there is nothing for a caller to re-index and nothing for this
        proof to compose.  (The chain that hand-composed 38 [ws_le] facts to
        state one such inequality is gone with them.)
      - the postcondition hands back [wrunning ξ] rather than
        [whart_run ξ q], because the last instruction is [mret]: it moves
        [cur_privilege], i.e. it DISSOLVES [mmode_config] rather than
        preserving it, which is exactly the M->S boundary at which the view
        token stops riding an M-mode bundle and starts riding [sconf];
      - [WP (Loop : expr riscv_lang)] -> [WWP Loop] (no postcondition
        anywhere -- main removed WP postconditions tree-wide);
      - every [m_*]/[st_m*] register-file definition and every static CSR
        fact ([st_ms1], [st_pmpcfg1], [st_menv_adue], [st_mret_priv], ...) is
        REUSED from [WpStartNew], never restated.

    Composition: every instruction is TWO proofmode lines -- one [iApply] of
    its [WeakLeafO] wrapper, one [iIntros] naming the resources back -- over
    a [WkStartAux.wsti_NN] token spent with a single [iPoseProof].  No
    decode fact, no alignment fact and no [wstate] is named anywhere in this
    file; see [WkTimerinit]'s header for what that removes.

    The two prologue [c.sdsp] stores use [wwp_sd8_off_rvc_run] (the all-OFF
    boot PMP, NOT the TOR one -- the [pmpcfg0] write is instruction 58), and
    are RELEASE stores whose two extra outputs this chain drops: a private
    stack slot publishes nothing.

    FOUR instructions do not ride the bundle -- [csrr mstatus],
    [csrw mstatus], [csrw pmpcfg0] and [mret].  Their wrappers take the
    CELLS [mmode_config] is built from (each reads or writes one of them),
    so those sites open [whart_run], do the same "combine halves to full ->
    apply -> re-split -> rebundle" dance [WpStartNew] does at its own
    config-writing sites, and close it again.  That is parity, not a tax:
    the SC chain opens the bundle at exactly these sites too.  Every other
    instruction is a plain [whart_run ξ (1/2)] wrapper, mirroring
    [WpStartNew]'s fraction choreography.  The [jal] into [timerinit] is
    [wwp_jal_run]; the call itself applies [WkTimerinit.wwp_timerinit],
    which is stated on this very interface and so needs no conversion at
    the boundary at all.

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
Require Import WeakViewMono WeakCtx WeakLeafO.
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
     composes with [WeakCtx.cobj_mono] at the frame re-bundling step (the
     [WkTimerinit.stack_2_intro_ent] twin -- Local there). *)
  Local Lemma wstack2_intro_ent (sp : Arch.pa) (w1 w2 : bv 64) :
    (wpt8 (pa_stk sp 1) (DfracOwn 1) w1 ∗ wpt8 (pa_stk sp 2) (DfracOwn 1) w2)
    ⊢ wstack_own_phys sp 2.
  Proof. iIntros "[H1 H2]". iApply (wstack_own_phys_2_intro with "H1 H2"). Qed.

  Lemma wwp_start (ξ : CtxId)
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 mhartid_in : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (n : nat) (kbs : _) :
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
    whart_run ξ 1 -∗
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
    cobj ξ (wstack_own_phys sp0 n) -∗
    wkernel_text kbs -∗
    ( ∀ (tv : mword 64) (ms0 : mword 64)
        (HoIE : eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false)
        (HoPRV : eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false)
        (HoSXL : _get_Mstatus_SXL ms0 = ('b"10"))
        (HoKF : mstatus_kernel_facts ms0),
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
      wrunning ξ -∗
      cobj ξ (wstack_own_phys sp0 n) -∗
      WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hn4 Hpmp HlpeE Hsp Hra Hs0 Hbnd_ra Hbnd_s0
           Hram8_ra Hram8_s0 Hram8_ti_ra Hram8_ti_s0 Hcov.
    iIntros "Hrun Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc
             Hstk #Htext Hcont".
    (* ---- split the stack bundle: start's own 4 slots + the deep rest.
       Every piece stays a [cobj] and is never touched again until the
       re-bundle at the end -- objective ownership crosses a step for
       free. ---- *)
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_1 sp0 4 n ltac:(lia)) with "Hstk")
      as "Hstk". iEval (rewrite cobj_sep) in "Hstk". iDestruct "Hstk" as "[Htop Hdeep]".
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_1 sp0 2 4 ltac:(lia)) with "Htop")
      as "Htop". iEval (rewrite cobj_sep) in "Htop". iDestruct "Htop" as "[Ht12 Ht34]".
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_2_elim sp0) with "Ht12") as "Ht12".
    iEval (rewrite cobj_exist) in "Ht12". iDestruct "Ht12" as (vsra) "Ht12".
    iEval (rewrite cobj_exist) in "Ht12". iDestruct "Ht12" as (vss0) "Ht12".
    iEval (rewrite cobj_sep) in "Ht12". iDestruct "Ht12" as "[Hsra Hss0]".
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_2_elim (pa_stk sp0 2)) with "Ht34") as "Ht34".
    iEval (rewrite cobj_exist) in "Ht34". iDestruct "Ht34" as (vtra) "Ht34".
    iEval (rewrite cobj_exist) in "Ht34". iDestruct "Ht34" as (vts0) "Ht34".
    iEval (rewrite cobj_sep) in "Ht34". iDestruct "Ht34" as "[Htra Hts0]".
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
    (* timerinit's two slots, bundled ONCE here (they are not touched by
       start's own instructions at all). *)
    iEval (rewrite Htb1) in "Htra". iEval (rewrite Htb2) in "Hts0".
    iAssert (cobj ξ (wpt8 (pa_stk (ti_sp1 sp0) 1) (DfracOwn 1) vtra ∗
                     wpt8 (pa_stk (ti_sp1 sp0) 2) (DfracOwn 1) vts0))
      with "[Htra Hts0]" as "Hti2".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (wstack2_intro_ent (ti_sp1 sp0) vtra vts0) with "Hti2")
      as "Hti2".
    (* the release stores' payload: a private stack slot publishes nothing *)
    iAssert (cobj ξ (⌜True⌝ : vProp Σ)) as "HRtrue".
    { rewrite cobj_pure. done. }
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
    assert (Hmepcv : WpGprCsrwA.mepc_val st_main = st_main)
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
       split all cells in half: a working bundle at 1/2 + pinned halves.
       The view token comes out with the bundle and goes back in with it. ---- *)
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
    iDestruct (mmode_config_unbundle with "Hmm") as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HoIE & %HoPRV & %HoSXL & %HoKF)".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) ms0 HoIE HoPRV HoSXL HoKF
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iDestruct (whart_run_close ξ (1/2)%Qp with "Hmm Hview") as "Hrun".
    assert (HmIE1 : eq_vec (_get_Mstatus_MIE (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MIE. rewrite st_va5_40_MIE. exact HoIE. }
    assert (HMPRV1 : eq_vec (_get_Mstatus_MPRV (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MPRV. rewrite st_va5_40_MPRV. exact HoPRV. }
    assert (HSXL1 : _get_Mstatus_SXL (st_ms1 ms0) = ('b"10")).
    { unfold st_ms1. rewrite mstatus_legalized_SXL. exact HoSXL. }
    pose proof (st_ms1_kernel_facts ms0 HoKF) as HKF1.

    (* ---- 30. c.addi sp, -16 ---- *)
    iPoseProof (wsti_30 kbs Hcov with "Htext") as "#Hi30".
    iApply (wwp_addi_run ξ st_pc30 true csp_rs1 csp_rs1 (sign_extend' 12 i9) m
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_sp with "Hrun HpcfA Hpc Hfile Hi30").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite sext6_12_64 Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (st_m30 m sp0)) in "Hfile".
    assert (P30 : add_vec_int st_pc30 2 = st_pc31) by (vm_compute; reflexivity).
    iEval (rewrite P30) in "Hpc".

    (* ---- 31. c.sdsp ra, 8(sp) (RELEASE store, all-OFF PMP) ---- *)
    assert (L31sp : st_m30 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0) by (st_unfold; st_look).
    assert (L31ra : st_m30 m sp0 !!! Regidx ti_ra = ra0) by (st_unfold; st_look).
    iPoseProof (wsti_31 kbs Hcov with "Htext") as "#Hi31".
    iDestruct (gpr_file_acc_2 (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_ra) ltac:(st_reg_neq)
                 with "Hfile") as "(Hspc & Hrac & Hfins31)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp)
             -(rf_lookup (st_m30 m sp0) (Regidx csp_rs1)) L31sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)
             -(rf_lookup (st_m30 m sp0) (Regidx ti_ra)) L31ra) in "Hrac".
    iApply (wwp_sd8_off_rvc_run ξ st_pc31 csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000")))
              (ti_ea_ra sp0) vsra (⌜True⌝ : vProp Σ) (1/2)%Qp pmpcfg0
              (ti_sp1 sp0) ra0
              Hgid Hpmp Hnz_sp Hnz_ra eq_refl Hram8_ra
              with "Hrun HpcfA Hpc Hspc Hrac Hi31 Hsra HRtrue").
    iIntros (T31) "_ Hrun HpcfA Hpc Hspc Hrac Hsra _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfins31" with "Hspc Hrac") as "Hfile".
    iEval (rewrite (rf_upd2_same (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_ra)
             (ti_sp1 sp0) ra0 ltac:(st_reg_neq) L31sp L31ra)) in "Hfile".
    assert (P31 : add_vec_int st_pc31 2 = st_pc32) by (vm_compute; reflexivity).
    iEval (rewrite P31) in "Hpc".

    (* ---- 32. c.sdsp s0, 0(sp) ---- *)
    assert (L32s0 : st_m30 m sp0 !!! Regidx ti_s0 = s00) by (st_unfold; st_look).
    iPoseProof (wsti_32 kbs Hcov with "Htext") as "#Hi32".
    iDestruct (gpr_file_acc_2 (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_s0) ltac:(st_reg_neq)
                 with "Hfile") as "(Hspc & Hs0c & Hfins32)".
    iEval (rewrite (gpr_pt_nz csp_rs1 _ Hnz_sp)
             -(rf_lookup (st_m30 m sp0) (Regidx csp_rs1)) L31sp) in "Hspc".
    iEval (rewrite (gpr_pt_nz ti_s0 _ Hnz_s0)
             -(rf_lookup (st_m30 m sp0) (Regidx ti_s0)) L32s0) in "Hs0c".
    iApply (wwp_sd8_off_rvc_run ξ st_pc32 csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000")))
              (ti_ea_s0 sp0) vss0 (⌜True⌝ : vProp Σ) (1/2)%Qp pmpcfg0
              (ti_sp1 sp0) s00
              Hgid Hpmp Hnz_sp Hnz_s0 eq_refl Hram8_s0
              with "Hrun HpcfA Hpc Hspc Hs0c Hi32 Hss0 HRtrue").
    iIntros (T32) "_ Hrun HpcfA Hpc Hspc Hs0c Hss0 _".
    iEval (rewrite -(gpr_pt_nz csp_rs1 _ Hnz_sp)) in "Hspc".
    iEval (rewrite -(gpr_pt_nz ti_s0 _ Hnz_s0)) in "Hs0c".
    iDestruct ("Hfins32" with "Hspc Hs0c") as "Hfile".
    iEval (rewrite (rf_upd2_same (st_m30 m sp0) (Regidx csp_rs1) (Regidx ti_s0)
             (ti_sp1 sp0) s00 ltac:(st_reg_neq) L31sp L32s0)) in "Hfile".
    assert (P32 : add_vec_int st_pc32 2 = st_pc33) by (vm_compute; reflexivity).
    iEval (rewrite P32) in "Hpc".

    (* ---- 33. c.addi4spn s0, sp, 16 (s0 := sp0) ---- *)
    iPoseProof (wsti_33 kbs Hcov with "Htext") as "#Hi33".
    iApply (wwp_addi_run ξ st_pc33 true csp_rs1 ti_s0 (caddi4spn_imm nz12)
              (st_m30 m sp0) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_s0
              with "Hrun HpcfA Hpc Hfile Hi33").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L31sp Hs016) in "Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg sp0]> (st_m30 m sp0))
             with (st_m33 m sp0)) in "Hfile".
    assert (P33 : add_vec_int st_pc33 2 = st_pc34) by (vm_compute; reflexivity).
    iEval (rewrite P33) in "Hpc".

    (* ---- 34. csrr a5, mstatus.  The first CELL-BASED site: the leaf needs
       [mstatus] whole, so the bundle is opened here exactly as [WpStartNew]
       opens it.  [WeakLeafO] gives these an [_o] (no [_run]) because there
       is no bundle for the view token to ride in. ---- *)
    iPoseProof (wsti_34 kbs Hcov with "Htext") as "#Hi34".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
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
    iApply (wwp_csrr_mstatus_o ξ st_pc34 ti_a5 ms0
              (st_m33 m sp0 (Regidx ti_a5)) pmpcfg0 Hgid HpmpU Hnz_a5 HoIE HoPRV
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Ha5c Hi34 Hview").
    iIntros "Hhs Hpriv Hms Hpcf Hpc Ha5c Hview".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) ms0 HoIE HoPRV HoSXL HoKF
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iDestruct (whart_run_close ξ (1/2)%Qp with "Hmm Hview") as "Hrun".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins34" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg ms0]> (st_m33 m sp0))
             with (st_m34 m sp0 ms0)) in "Hfile".
    assert (P34 : add_vec_int st_pc34 4 = st_pc35) by (vm_compute; reflexivity).
    iEval (rewrite P34) in "Hpc".

    (* ---- 35. c.lui a4, 0xffffe ---- *)
    iPoseProof (wsti_35 kbs Hcov with "Htext") as "#Hi35".
    iApply (wwp_lui_run ξ st_pc35 true ti_a4 (sign_extend' 20 si35) (st_m34 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a4 with "Hrun HpcfA Hpc Hfile Hi35").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si35))]>
                     (st_m34 m sp0 ms0))
             with (st_m35 m sp0 ms0)) in "Hfile".
    assert (P35 : add_vec_int st_pc35 2 = st_pc36) by (vm_compute; reflexivity).
    iEval (rewrite P35) in "Hpc".

    (* ---- 36. addi a4, a4, 2047 ---- *)
    assert (L36a4 : st_m35 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si35))
      by (st_unfold; st_look).
    iPoseProof (wsti_36 kbs Hcov with "Htext") as "#Hi36".
    iApply (wwp_addi_run ξ st_pc36 false ti_a4 ti_a4 si36 (st_m35 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a4 with "Hrun HpcfA Hpc Hfile Hi36").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L36a4 Hm1v) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_and]> (st_m35 m sp0 ms0))
             with (st_m36 m sp0 ms0)) in "Hfile".
    assert (P36 : add_vec_int st_pc36 4 = st_pc37) by (vm_compute; reflexivity).
    iEval (rewrite P36) in "Hpc".

    (* ---- 37. c.and a5, a4 ---- *)
    assert (L37a5 : st_m36 m sp0 ms0 !!! Regidx ti_a5 = ms0) by (st_unfold; st_look).
    assert (L37a4 : st_m36 m sp0 ms0 !!! Regidx ti_a4 = st_mask_and) by (st_unfold; st_look).
    iPoseProof (wsti_37 kbs Hcov with "Htext") as "#Hi37".
    iApply (wwp_and_rvc_run ξ st_pc37 ti_a4 ti_a5 ti_a5 (st_m36 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi37").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L37a5 L37a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (and_vec ms0 st_mask_and)]>
                     (st_m36 m sp0 ms0))
             with (st_m37 m sp0 ms0)) in "Hfile".
    assert (P37 : add_vec_int st_pc37 2 = st_pc38) by (vm_compute; reflexivity).
    iEval (rewrite P37) in "Hpc".

    (* ---- 38. c.lui a4, 1 ---- *)
    iPoseProof (wsti_38 kbs Hcov with "Htext") as "#Hi38".
    iApply (wwp_lui_run ξ st_pc38 true ti_a4 (sign_extend' 20 si38) (st_m37 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a4 with "Hrun HpcfA Hpc Hfile Hi38").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si38))]>
                     (st_m37 m sp0 ms0))
             with (st_m38 m sp0 ms0)) in "Hfile".
    assert (P38 : add_vec_int st_pc38 2 = st_pc39) by (vm_compute; reflexivity).
    iEval (rewrite P38) in "Hpc".

    (* ---- 39. addi a4, a4, -2048 ---- *)
    assert (L39a4 : st_m38 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si38))
      by (st_unfold; st_look).
    iPoseProof (wsti_39 kbs Hcov with "Htext") as "#Hi39".
    iApply (wwp_addi_run ξ st_pc39 false ti_a4 ti_a4 si39 (st_m38 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a4 with "Hrun HpcfA Hpc Hfile Hi39").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L39a4 Hm2v) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_or]> (st_m38 m sp0 ms0))
             with (st_m39 m sp0 ms0)) in "Hfile".
    assert (P39 : add_vec_int st_pc39 4 = st_pc40) by (vm_compute; reflexivity).
    iEval (rewrite P39) in "Hpc".

    (* ---- 40. c.or a5, a4 ---- *)
    assert (L40a5 : st_m39 m sp0 ms0 !!! Regidx ti_a5 = and_vec ms0 st_mask_and)
      by (st_unfold; st_look).
    assert (L40a4 : st_m39 m sp0 ms0 !!! Regidx ti_a4 = st_mask_or) by (st_unfold; st_look).
    iPoseProof (wsti_40 kbs Hcov with "Htext") as "#Hi40".
    iApply (wwp_or_rvc_run ξ st_pc40 ti_a4 ti_a5 ti_a5 (st_m39 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi40").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L40a5 L40a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec (and_vec ms0 st_mask_and) st_mask_or)]>
                     (st_m39 m sp0 ms0))
             with (st_m40 m sp0 ms0)) in "Hfile".
    assert (P40 : add_vec_int st_pc40 2 = st_pc41) by (vm_compute; reflexivity).
    iEval (rewrite P40) in "Hpc".

    (* ---- 41. csrw mstatus, a5 (cell-based) ---- *)
    assert (L41a5 : st_m40 m sp0 ms0 !!! Regidx ti_a5 = st_va5_40 ms0) by (st_unfold; st_look).
    assert (Hal4_41 : is_aligned_vaddr (Virtaddr st_pc41) 4 = true) by (vm_compute; reflexivity).
    iPoseProof (wsti_41 kbs Hcov with "Htext") as "#Hi41".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
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
    iApply (wwp_csrw_mstatus_o ξ st_pc41 ti_a5 ms0
              (st_m40 m sp0 ms0 (Regidx ti_a5)) pmpcfg0
              Hgid HpmpU Hal4_41 Hnz_a5 HoIE HoPRV
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Ha5c Hi41 Hview").
    iIntros "Hhs Hpriv Hms Hpcf Hpc Ha5c Hview".
    iEval (rewrite -(rf_lookup (st_m40 m sp0 ms0) (Regidx ti_a5)) L41a5) in "Hms".
    iEval (change (WpGprCsrwCommon.mstatus_legalized ms0 (st_va5_40 ms0))
             with (st_ms1 ms0)) in "Hms".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1 HKF1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iDestruct (whart_run_close ξ (1/2)%Qp with "Hmm Hview") as "Hrun".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb41" with "Ha5c") as "Hfile".
    assert (P41 : add_vec_int st_pc41 4 = st_pc42) by (vm_compute; reflexivity).
    iEval (rewrite P41) in "Hpc".

    (* ---- 42. auipc a5, 1 ---- *)
    iPoseProof (wsti_42 kbs Hcov with "Htext") as "#Hi42".
    iApply (wwp_auipc_run ξ st_pc42 ti_a5 si42 (st_m40 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi42").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Ha42v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_a42v]> (st_m40 m sp0 ms0))
             with (st_m42 m sp0 ms0)) in "Hfile".
    assert (P42 : add_vec_int st_pc42 4 = st_pc43) by (vm_compute; reflexivity).
    iEval (rewrite P42) in "Hpc".

    (* ---- 43. addi a5, a5, -506 (a5 := <main>) ---- *)
    assert (L43a5 : st_m42 m sp0 ms0 !!! Regidx ti_a5 = st_a42v) by (st_unfold; st_look).
    iPoseProof (wsti_43 kbs Hcov with "Htext") as "#Hi43".
    iApply (wwp_addi_run ξ st_pc43 false ti_a5 ti_a5 si43 (st_m42 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi43").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L43a5 Ha43v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_main]> (st_m42 m sp0 ms0))
             with (st_m43 m sp0 ms0)) in "Hfile".
    assert (P43 : add_vec_int st_pc43 4 = st_pc44) by (vm_compute; reflexivity).
    iEval (rewrite P43) in "Hpc".

    (* ---- 44. csrw mepc, a5 ---- *)
    assert (L44a5 : st_m43 m sp0 ms0 !!! Regidx ti_a5 = st_main) by (st_unfold; st_look).
    iPoseProof (wsti_44 kbs Hcov with "Htext") as "#Hi44".
    iDestruct (gpr_file_lookup_acc (st_m43 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb44]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mepc_run ξ st_pc44 ti_a5 mepc0
              (st_m43 m sp0 ms0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Ha5c Hmepc Hi44").
    iIntros "Hrun HpcfA Hpc Ha5c Hmepc".
    iEval (rewrite -(rf_lookup (st_m43 m sp0 ms0) (Regidx ti_a5)) L44a5 Hmepcv) in "Hmepc".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb44" with "Ha5c") as "Hfile".
    assert (P44 : add_vec_int st_pc44 4 = st_pc45) by (vm_compute; reflexivity).
    iEval (rewrite P44) in "Hpc".

    (* ---- 45. c.li a5, 0 ---- *)
    iDestruct (gpr_file_x0 (st_m43 m sp0 ms0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_45 Hfile]".
    iPoseProof (wsti_45 kbs Hcov with "Htext") as "#Hi45".
    iApply (wwp_addi_run ξ st_pc45 true cli_rs1 ti_a5 (sign_extend' 12 si45)
              (st_m43 m sp0 ms0) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Hfile Hi45").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Hx0_45 add_vec_zero_l sext6_12_64 Hz45) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 0)]> (st_m43 m sp0 ms0))
             with (st_m45 m sp0 ms0)) in "Hfile".
    assert (P45 : add_vec_int st_pc45 2 = st_pc46) by (vm_compute; reflexivity).
    iEval (rewrite P45) in "Hpc".

    (* ---- 46. csrw satp, a5 (Bare) ---- *)
    assert (L46a5 : st_m45 m sp0 ms0 !!! Regidx ti_a5 = (mword_of_int 0 : mword 64))
      by (st_unfold; st_look).
    iPoseProof (wsti_46 kbs Hcov with "Htext") as "#Hi46".
    iDestruct (gpr_file_lookup_acc (st_m45 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb46]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_satp_run ξ st_pc46 ti_a5 satp0
              (st_m45 m sp0 ms0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Ha5c Hsatp Hi46").
    iIntros "Hrun HpcfA Hpc Ha5c Hsatp".
    iEval (rewrite -(rf_lookup (st_m45 m sp0 ms0) (Regidx ti_a5)) L46a5) in "Hsatp".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb46" with "Ha5c") as "Hfile".
    assert (P46 : add_vec_int st_pc46 4 = st_pc47) by (vm_compute; reflexivity).
    iEval (rewrite P46) in "Hpc".

    (* ---- 47. c.lui a5, 0x10 ---- *)
    iPoseProof (wsti_47 kbs Hcov with "Htext") as "#Hi47".
    iApply (wwp_lui_run ξ st_pc47 true ti_a5 (sign_extend' 20 si47) (st_m45 m sp0 ms0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi47").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (luival (sign_extend' 20 si47))]>
                     (st_m45 m sp0 ms0))
             with (st_m47 m sp0 ms0)) in "Hfile".
    assert (P47 : add_vec_int st_pc47 2 = st_pc48) by (vm_compute; reflexivity).
    iEval (rewrite P47) in "Hpc".

    (* ---- 48. c.addi a5, -1 (a5 := 0xffff) ---- *)
    assert (L48a5 : st_m47 m sp0 ms0 !!! Regidx ti_a5 = luival (sign_extend' 20 si47))
      by (st_unfold; st_look).
    iPoseProof (wsti_48 kbs Hcov with "Htext") as "#Hi48".
    iApply (wwp_addi_run ξ st_pc48 true ti_a5 ti_a5 (sign_extend' 12 si48)
              (st_m47 m sp0 ms0) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Hfile Hi48").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L48a5 sext6_12_64 Hffv) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_ffff]> (st_m47 m sp0 ms0))
             with (st_m48 m sp0 ms0)) in "Hfile".
    assert (P48 : add_vec_int st_pc48 2 = st_pc49) by (vm_compute; reflexivity).
    iEval (rewrite P48) in "Hpc".

    (* ---- 49. csrw medeleg, a5 ---- *)
    assert (L49a5 : st_m48 m sp0 ms0 !!! Regidx ti_a5 = st_ffff) by (st_unfold; st_look).
    iPoseProof (wsti_49 kbs Hcov with "Htext") as "#Hi49".
    iDestruct (gpr_file_lookup_acc (st_m48 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb49]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_medeleg_run ξ st_pc49 ti_a5 medeleg0
              (st_m48 m sp0 ms0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Ha5c Hmede Hi49").
    iIntros "Hrun HpcfA Hpc Ha5c Hmede".
    iEval (rewrite -(rf_lookup (st_m48 m sp0 ms0) (Regidx ti_a5)) L49a5) in "Hmede".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb49" with "Ha5c") as "Hfile".
    assert (P49 : add_vec_int st_pc49 4 = st_pc50) by (vm_compute; reflexivity).
    iEval (rewrite P49) in "Hpc".

    (* ---- 50. csrw mideleg, a5 ---- *)
    iPoseProof (wsti_50 kbs Hcov with "Htext") as "#Hi50".
    iDestruct (gpr_file_lookup_acc (st_m48 m sp0 ms0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb50]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_mideleg_run ξ st_pc50 ti_a5 mideleg0
              (st_m48 m sp0 ms0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Ha5c Hmdl Hi50").
    iIntros "Hrun HpcfA Hpc Ha5c Hmdl".
    iEval (rewrite -(rf_lookup (st_m48 m sp0 ms0) (Regidx ti_a5)) L49a5) in "Hmdl".
    iEval (change (WpGprCsrwB.mideleg_legalized mideleg0 st_ffff)
             with (st_mdl1 mideleg0)) in "Hmdl".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb50" with "Ha5c") as "Hfile".
    assert (P50 : add_vec_int st_pc50 4 = st_pc51) by (vm_compute; reflexivity).
    iEval (rewrite P50) in "Hpc".

    (* ---- 51. csrr a5, sie (a view over mie & mideleg) ---- *)
    iPoseProof (wsti_51 kbs Hcov with "Htext") as "#Hi51".
    iDestruct (gpr_file_insert_acc (st_m48 m sp0 ms0) (Regidx ti_a5)
                 (regval_into_reg (lower_mie mie0 (st_mdl1 mideleg0))) with "Hfile")
      as "[Ha5c Hfins51]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_sie_run ξ st_pc51 ti_a5 mie0 (st_mdl1 mideleg0)
              (st_m48 m sp0 ms0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Hmie Hmdl Ha5c Hi51").
    iIntros "Hrun HpcfA Hpc Ha5c Hmie Hmdl".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins51" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (lower_mie mie0 (st_mdl1 mideleg0))]>
                     (st_m48 m sp0 ms0))
             with (st_m51 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    assert (P51 : add_vec_int st_pc51 4 = st_pc52) by (vm_compute; reflexivity).
    iEval (rewrite P51) in "Hpc".

    (* ---- 52. ori a5, a5, 544 ---- *)
    assert (L52a5 : st_m51 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = lower_mie mie0 (st_mdl1 mideleg0)) by (st_unfold; st_look).
    iPoseProof (wsti_52 kbs Hcov with "Htext") as "#Hi52".
    iApply (wwp_ori_run ξ st_pc52 ti_a5 ti_a5 si52 (st_m51 m sp0 ms0 mie0 mideleg0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi52").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L52a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (lower_mie mie0 (st_mdl1 mideleg0)) (sign_extend' 64 si52))]>
                     (st_m51 m sp0 ms0 mie0 mideleg0))
             with (st_m52 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    assert (P52 : add_vec_int st_pc52 4 = st_pc53) by (vm_compute; reflexivity).
    iEval (rewrite P52) in "Hpc".

    (* ---- 53. csrw sie, a5 ---- *)
    assert (L53a5 : st_m52 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = st_va5_52 mie0 mideleg0) by (st_unfold; st_look).
    iPoseProof (wsti_53 kbs Hcov with "Htext") as "#Hi53".
    iDestruct (gpr_file_lookup_acc (st_m52 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb53]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_sie_run ξ st_pc53 ti_a5 mie0 (st_mdl1 mideleg0)
              (st_m52 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) pmpcfg0 (1/2)%Qp
              Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Ha5c Hmie Hmdl Hi53").
    iIntros "Hrun HpcfA Hpc Ha5c Hmie Hmdl".
    iEval (rewrite -(rf_lookup (st_m52 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L53a5) in "Hmie".
    iEval (change (WpGprCsrwB.sie_new_mie mie0 (st_mdl1 mideleg0) (st_va5_52 mie0 mideleg0))
             with (st_mie1 mie0 mideleg0)) in "Hmie".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb53" with "Ha5c") as "Hfile".
    assert (P53 : add_vec_int st_pc53 4 = st_pc54) by (vm_compute; reflexivity).
    iEval (rewrite P53) in "Hpc".

    (* ---- 54. c.li a5, -1 ---- *)
    iDestruct (gpr_file_x0 (st_m52 m sp0 ms0 mie0 mideleg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_54 Hfile]".
    iPoseProof (wsti_54 kbs Hcov with "Htext") as "#Hi54".
    iApply (wwp_addi_run ξ st_pc54 true cli_rs1 ti_a5 (sign_extend' 12 si54)
              (st_m52 m sp0 ms0 mie0 mideleg0) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Hfile Hi54").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Hx0_54 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (cli_wval si54)]>
                     (st_m52 m sp0 ms0 mie0 mideleg0))
             with (st_m54 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    assert (P54 : add_vec_int st_pc54 2 = st_pc55) by (vm_compute; reflexivity).
    iEval (rewrite P54) in "Hpc".

    (* ---- 55. c.srli a5, 10 ---- *)
    assert (L55a5 : st_m54 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = cli_wval si54)
      by (st_unfold; st_look).
    iPoseProof (wsti_55 kbs Hcov with "Htext") as "#Hi55".
    iApply (wwp_srli_rvc_run ξ st_pc55 ti_a5 ti_a5 ssh55 (st_m54 m sp0 ms0 mie0 mideleg0)
              pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Hfile Hi55").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L55a5 Hshv) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_pmpw]> (st_m54 m sp0 ms0 mie0 mideleg0))
             with (st_m55 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    assert (P55 : add_vec_int st_pc55 2 = st_pc56) by (vm_compute; reflexivity).
    iEval (rewrite P55) in "Hpc".

    (* ---- 56. csrw pmpaddr0, a5 ---- *)
    assert (L56a5 : st_m55 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = st_pmpw)
      by (st_unfold; st_look).
    iPoseProof (wsti_56 kbs Hcov with "Htext") as "#Hi56".
    iDestruct (gpr_file_lookup_acc (st_m55 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5) with "Hfile")
      as "[Ha5c Hfb56]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_pmpaddr0_run ξ st_pc56 ti_a5
              (st_m55 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) pmpaddr00 pmpcfg0 (1/2)%Qp
              Hgid HpmpU Hnz_a5 with "Hrun HpcfA Hpc Ha5c Hpaddr Hi56").
    iIntros "Hrun HpcfA Hpc Ha5c Hpaddr".
    iEval (rewrite -(rf_lookup (st_m55 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L56a5) in "Hpaddr".
    iEval (change (WpGprCsrwB.pmp0_newaddr pmpcfg0 pmpaddr00 st_pmpw)
             with (st_pmpaddr1 pmpcfg0 pmpaddr00)) in "Hpaddr".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb56" with "Ha5c") as "Hfile".
    assert (P56 : add_vec_int st_pc56 4 = st_pc57) by (vm_compute; reflexivity).
    iEval (rewrite P56) in "Hpc".

    (* ---- 57. c.li a5, 15 ---- *)
    iDestruct (gpr_file_x0 (st_m55 m sp0 ms0 mie0 mideleg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_57 Hfile]".
    iPoseProof (wsti_57 kbs Hcov with "Htext") as "#Hi57".
    iApply (wwp_addi_run ξ st_pc57 true cli_rs1 ti_a5 (sign_extend' 12 si57)
              (st_m55 m sp0 ms0 mie0 mideleg0) pmpcfg0 (1/2)%Qp Hgid HpmpU Hnz_a5
              with "Hrun HpcfA Hpc Hfile Hi57").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Hx0_57 add_vec_zero_l sext6_12_64 H15v) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 15)]>
                     (st_m55 m sp0 ms0 mie0 mideleg0))
             with (st_m57 m sp0 ms0 mie0 mideleg0)) in "Hfile".
    assert (P57 : add_vec_int st_pc57 2 = st_pc58) by (vm_compute; reflexivity).
    iEval (rewrite P57) in "Hpc".

    (* ---- 58. csrw pmpcfg0, a5 (cell-based) ---- *)
    assert (L58a5 : st_m57 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = (mword_of_int 15 : mword 64)) by (st_unfold; st_look).
    iPoseProof (wsti_58 kbs Hcov with "Htext") as "#Hi58".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
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
    iApply (wwp_csrw_pmpcfg0_o ξ st_pc58 ti_a5 (st_ms1 ms0)
              (st_m57 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) pmpcfg0
              Hgid HpmpU Hnz_a5 HmIE1 HMPRV1
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Ha5c Hi58 Hview").
    iIntros "Hhs Hpriv Hms Hpcf Hpc Ha5c Hview".
    iEval (rewrite -(rf_lookup (st_m57 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)) L58a5) in "Hpcf".
    iEval (change (WpGprCsrwC.pmpcfg_written (mword_of_int 15) pmpcfg0)
             with (st_pmpcfg1 pmpcfg0)) in "Hpcf".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1 HKF1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    iDestruct (whart_run_close ξ (1/2)%Qp with "Hmm Hview") as "Hrun".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfb58" with "Ha5c") as "Hfile".
    assert (P58 : add_vec_int st_pc58 4 = st_pc_ae0) by (vm_compute; reflexivity).
    iEval (rewrite P58) in "Hpc".

    (* ---- ae0. csrr a5, menvcfg (the ADUE read-modify-write) ---- *)
    iPoseProof (wsti_ae0 kbs Hcov with "Htext") as "#Hiae0".
    iDestruct (gpr_file_insert_acc (st_m57 m sp0 ms0 mie0 mideleg0) (Regidx ti_a5)
                 (regval_into_reg menvcfg0) with "Hfile") as "[Ha5c Hfinsae0]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_menvcfg_run ξ st_pc_ae0 ti_a5 menvcfg0
              (st_m57 m sp0 ms0 mie0 mideleg0 (Regidx ti_a5)) (st_pmpcfg1 pmpcfg0) (1/2)%Qp
              Hgid Hpmp1 Hnz_a5 with "Hrun HpcfA Hpc Hmenv Ha5c Hiae0").
    iIntros "Hrun HpcfA Hpc Ha5c Hmenv".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfinsae0" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menvcfg0]> (st_m57 m sp0 ms0 mie0 mideleg0))
             with (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    assert (Pae0 : add_vec_int st_pc_ae0 4 = st_pc_ae1) by (vm_compute; reflexivity).
    iEval (rewrite Pae0) in "Hpc".

    (* ---- ae1. c.li a4, 1 ---- *)
    iDestruct (gpr_file_x0 (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) cli_rs1
                 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_ae1 Hfile]".
    iPoseProof (wsti_ae1 kbs Hcov with "Htext") as "#Hiae1".
    iApply (wwp_addi_run ξ st_pc_ae1 true cli_rs1 ti_a4 (sign_extend' 12 sae_li)
              (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) (st_pmpcfg1 pmpcfg0) (1/2)%Qp
              Hgid Hpmp1 Hnz_a4 with "Hrun HpcfA Hpc Hfile Hiae1").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Hx0_ae1 add_vec_zero_l sext6_12_64) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval sae_li)]>
                     (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    assert (Pae1 : add_vec_int st_pc_ae1 2 = st_pc_ae2) by (vm_compute; reflexivity).
    iEval (rewrite Pae1) in "Hpc".

    (* ---- ae2. c.slli a4, 0x3d (a4 := 1<<61) ---- *)
    assert (L_ae2a4 : st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4
                      = cli_wval sae_li) by (st_unfold; st_look).
    iPoseProof (wsti_ae2 kbs Hcov with "Htext") as "#Hiae2".
    iApply (wwp_slli_rvc_run ξ st_pc_ae2 ti_a4 ti_a4 sae_slli
              (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0) (st_pmpcfg1 pmpcfg0) (1/2)%Qp
              Hgid Hpmp1 Hnz_a4 with "Hrun HpcfA Hpc Hfile Hiae2").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L_ae2a4 st_Hb61) in "Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_adue_bit]>
                     (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    assert (Pae2 : add_vec_int st_pc_ae2 2 = st_pc_ae3) by (vm_compute; reflexivity).
    iEval (rewrite Pae2) in "Hpc".

    (* ---- ae3. c.or a5, a4 ---- *)
    assert (L_ae3a5 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5 = menvcfg0)
      by (st_unfold; st_look).
    assert (L_ae3a4 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4 = st_adue_bit)
      by (st_unfold; st_look).
    iPoseProof (wsti_ae3 kbs Hcov with "Htext") as "#Hiae3".
    iApply (wwp_or_rvc_run ξ st_pc_ae3 ti_a4 ti_a5 ti_a5
              (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0) (st_pmpcfg1 pmpcfg0) (1/2)%Qp
              Hgid Hpmp1 Hnz_a5 with "Hrun HpcfA Hpc Hfile Hiae3").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite L_ae3a5 L_ae3a4) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menvcfg0 st_adue_bit)]>
                     (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    assert (Pae3 : add_vec_int st_pc_ae3 2 = st_pc_ae4) by (vm_compute; reflexivity).
    iEval (rewrite Pae3) in "Hpc".

    (* ---- ae4. csrw menvcfg, a5 ---- *)
    assert (L_ae4a5 : st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5
                      = or_vec menvcfg0 st_adue_bit) by (st_unfold; st_look).
    iPoseProof (wsti_ae4 kbs Hcov with "Htext") as "#Hiae4".
    iDestruct (gpr_file_lookup_acc (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_a5)
                 with "Hfile") as "[Ha5c Hfbae4]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrw_menvcfg_run ξ st_pc_ae4 ti_a5 menvcfg0
              (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 (Regidx ti_a5))
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hgid Hpmp1 Hnz_a5
              with "Hrun HpcfA Hpc Ha5c Hmenv Hiae4").
    iIntros "Hrun HpcfA Hpc Ha5c Hmenv".
    iEval (rewrite -(rf_lookup (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_a5))
             L_ae4a5) in "Hmenv".
    iEval (change (WpGprCsrwA.menvcfg_legalized menvcfg0 (or_vec menvcfg0 st_adue_bit))
             with (st_menv_adue menvcfg0)) in "Hmenv".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfbae4" with "Ha5c") as "Hfile".
    assert (Pae4 : add_vec_int st_pc_ae4 4 = st_pc59) by (vm_compute; reflexivity).
    iEval (rewrite Pae4) in "Hpc".

    (* ---- 59. jal ra, timerinit ---- *)
    iPoseProof (wsti_59 kbs Hcov with "Htext") as "#Hi59".
    iDestruct (gpr_file_insert_acc (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) (Regidx ti_ra)
                 (regval_into_reg (add_vec_int st_pc59 4)) with "Hfile") as "[Hrac Hfins59]".
    iEval (rewrite (gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iApply (wwp_jal_run ξ st_pc59 ti_ra sjimm59
              (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 (Regidx ti_ra))
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hgid Hpmp1 Hnz_ra Hjal_al
              with "Hrun HpcfA Hpc Hrac Hi59").
    iIntros "Hrun HpcfA Hpc Hrac".
    iEval (rewrite -(gpr_pt_nz ti_ra _ Hnz_ra)) in "Hrac".
    iDestruct ("Hfins59" with "Hrac") as "Hfile".
    iEval (rewrite Hlinkv) in "Hfile".
    iEval (change (<[Regidx ti_ra := regval_into_reg st_ra_link]>
                     (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    iEval (rewrite P59) in "Hpc".

    (* ---- timerinit() (21 instructions), at q = 1/2.  Nothing is converted
       at the boundary: [wwp_timerinit] takes the SAME [whart_run] this chain
       already threads, and the frame it needs is a [cobj] this chain already
       holds. ---- *)
    assert (L59sp : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (st_unfold; st_look).
    assert (L59ra : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_ra = st_ra_link)
      by (st_unfold; st_look).
    assert (L59s0 : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_s0 = sp0)
      by (st_unfold; st_look).
    iDestruct "Hpaddr" as "[HpaA HpaK]".
    iApply (wwp_timerinit ξ (1/2)%Qp (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
              st_ra_link sp0 (st_menv_adue menvcfg0) stimecmp0 mcounteren0
              (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00) 2 kbs
              ltac:(lia) Hgid Hpmp1 Htor_ra Htor_s0 Hcov L59sp L59ra L59s0
              Hram8_ti_ra Hram8_ti_s0
              with "Hrun HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Hti2 Htext").
    iIntros (tv) "Hrun HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Hti2".
    iEval (rewrite Hcretv) in "Hpc".
    iEval (change (ti_mout (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
                     (st_menv_adue menvcfg0) mcounteren0 tv st_ra_link sp0)
             with (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)) in "Hfile".
    iDestruct (reg_half_join with "HpaA HpaK") as "Hpaddr".

    (* ---- 60. csrr a5, mhartid ---- *)
    iPoseProof (wsti_60 kbs Hcov with "Htext") as "#Hi60".
    iDestruct (gpr_file_insert_acc (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)
                 (Regidx ti_a5) (regval_into_reg mhartid_in) with "Hfile") as "[Ha5c Hfins60]".
    iEval (rewrite (gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iApply (wwp_csrr_mhartid_run ξ st_pc60 ti_a5 mhartid_in
              (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv (Regidx ti_a5))
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hgid Hpmp1 Hnz_a5
              with "Hrun HpcfA Hpc Hmh Ha5c Hi60").
    iIntros "Hrun HpcfA Hpc Ha5c Hmh".
    iEval (rewrite -(gpr_pt_nz ti_a5 _ Hnz_a5)) in "Ha5c".
    iDestruct ("Hfins60" with "Ha5c") as "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg mhartid_in]>
                     (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv))
             with (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    assert (P60 : add_vec_int st_pc60 4 = st_pc61) by (vm_compute; reflexivity).
    iEval (rewrite P60) in "Hpc".

    (* ---- 61. c.addiw a5, 0 (sext.w) ---- *)
    assert (L61a5 : st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = mhartid_in) by (st_unfold; st_look).
    iPoseProof (wsti_61 kbs Hcov with "Htext") as "#Hi61".
    iApply (wwp_addiw_rvc_run ξ st_pc61 ti_a5 ti_a5 (sign_extend' 12 si61)
              (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hgid Hpmp1 Hnz_a5
              with "Hrun HpcfA Hpc Hfile Hi61").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite sext6_12_64 L61a5) in "Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (st_tpv mhartid_in)]>
                     (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    assert (P61 : add_vec_int st_pc61 2 = st_pc62) by (vm_compute; reflexivity).
    iEval (rewrite P61) in "Hpc".

    (* ---- 62. c.mv tp, a5 ---- *)
    assert (L62a5 : st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = st_tpv mhartid_in) by (st_unfold; st_look).
    iDestruct (gpr_file_x0 (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
                 cli_rs1 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_62 Hfile]".
    iPoseProof (wsti_62 kbs Hcov with "Htext") as "#Hi62".
    iApply (wwp_add_rvc_run ξ st_pc62 ti_a5 cli_rs1 st_tp
              (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hgid Hpmp1 Hnz_tp
              with "Hrun HpcfA Hpc Hfile Hi62").
    iIntros "Hrun HpcfA Hpc Hfile".
    iEval (rewrite Hx0_62 add_vec_zero_l L62a5) in "Hfile".
    iEval (change (<[Regidx st_tp := regval_into_reg (st_tpv mhartid_in)]>
                     (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".
    assert (P62 : add_vec_int st_pc62 2 = st_pc63) by (vm_compute; reflexivity).
    iEval (rewrite P62) in "Hpc".

    (* ---- 63. MRET into Supervisor mode at <main>.  THE BOUNDARY: this
       instruction DISSOLVES [mmode_config] (it moves [cur_privilege]), so
       there is no bundle to hand back and [WeakLeafO] gives [mret] an [_o]
       and no [_run].  What leaves this chain is therefore the raw cells
       plus a bare [wrunning ξ] -- which is exactly the shape S-mode's
       [sconf] will take the view token in. ---- *)
    iPoseProof (wsti_63 kbs Hcov with "Htext") as "#Hi63".
    iDestruct (whart_run_open with "Hrun") as "[Hmm Hview]".
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
    iApply (wwp_mret_o ξ st_pc63 Supervisor (st_ms1 ms0) st_main
              (menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)))
              (st_pmpcfg1 pmpcfg0) Hgid Hpmp1 HmIE1 HMPRV1 Hnp eq_refl HlpeF
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hmenv Hmepc Hi63 Hview").
    iIntros "Hhs Hpriv Hms Hpcf Hmenv Hmepc Hpc Hview".
    iEval (rewrite Hctgtv) in "Hpc".

    (* ---- re-bundle start's own frame and hand everything to the caller.
       No view arithmetic anywhere: each [cobj] has sat untouched in the
       context since the step that produced it. ---- *)
    iEval (rewrite Hb1) in "Hsra". iEval (rewrite Hb2) in "Hss0".
    iAssert (cobj ξ (wpt8 (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
                     wpt8 (pa_stk sp0 2) (DfracOwn 1) s00))
      with "[Hsra Hss0]" as "Ht12".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (wstack2_intro_ent sp0 ra0 s00) with "Ht12") as "Ht12".
    iEval (rewrite Hb0) in "Hti2".
    iAssert (cobj ξ (wstack_own_phys sp0 2 ∗ wstack_own_phys (pa_stk sp0 2) (4 - 2)))
      with "[Ht12 Hti2]" as "Htop".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_2 sp0 2 4 ltac:(lia)) with "Htop")
      as "Htop".
    iAssert (cobj ξ (wstack_own_phys sp0 4 ∗ wstack_own_phys (pa_stk sp0 4) (n - 4)))
      with "[Htop Hdeep]" as "Hstk".
    { iEval (rewrite cobj_sep). iFrame. }
    iDestruct (cobj_mono _ _ _ (wstack_own_phys_split_2 sp0 4 n ltac:(lia)) with "Hstk")
      as "Hstk".
    iApply ("Hcont" $! tv ms0 HoIE HoPRV HoSXL HoKF with
              "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl
               Hmie Hmenv Hmcen Hstc Hview Hstk").
  Qed.

End WkStartThm.

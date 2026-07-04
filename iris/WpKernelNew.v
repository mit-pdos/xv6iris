(* WpKernelNew.v -- THE end-to-end boot theorem [wp_kernel] on the new-style
   WP layer: from CPU reset state (PC = 0x80000000, M-mode, all-OFF PMP)
   through [_entry] (wp_entry, WpEntryNew.v) and [start()] (wp_start,
   WpStartNew.v, which runs timerinit() and ends in the MRET) into
   SUPERVISOR mode at <main> (0x80000e82), as ONE composed WP lemma.

   The composition is purely plumbing:
     - wp_entry's output gpr file [m_jal m v_stack0 mhartid_in] becomes
       wp_start's input file; its sp entry (the loaded+offset stack pointer)
       is wp_start's [sp0], its ra entry is the (irrelevant, overwritten)
       [ra0], and s0 is untouched from the reset file [m].
     - wp_start's stack-geometry side conditions (8-alignment of the four
       frame slots + the TOR bound for timerinit's two slots) are premises
       of wp_kernel, phrased over the SAME symbolic sp0. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpGpr.
Require Import WpAuipc WpGprAuipc WpGprLoad WpGprLui WpGprAddi WpGprShift WpGprLogic WpGprJal WpGprJalr WpGprStore WpGprRvc WpGprRvcTor.
Require Import WpGprCsrrCommon WpGprCsrrA WpGprCsrrB WpGprCsrwCommon WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMret WpGprMretWp WpGprMretNew.
Require Import MinstretInv InstrBytes WpEntryNew WpTimerinit WpStartNew.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
Local Open Scope Z_scope.

Section WpKernelNew.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma wp_kernel E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64)) (v_stack0 : bv 64) (mhartid_in : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 mtime0 stimecmp0 : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (vsra vss0 vtra vts0 : bv 64) {dq : dfrac} :
    (* the stack pointer start() runs on: _entry's computed sp
       (= v_stack0 + 4096 * (mhartid + 1)). *)
    let sp0 : mword 64 := m_jal m v_stack0 mhartid_in !!! Regidx csp_rs1 in
    ↑minstretN ⊆ E ->
    (* boot pmp config: all entries OFF. *)
    pmp_all_off pmpcfg0 ->
    (* boot menvcfg has the Zicfilp landing-pad enable clear. *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    (* stack geometry, over the symbolic sp0: start()'s two frame slots are
       8-aligned; timerinit's two are 8-aligned AND inside the written
       PMP TOR region [0, 0xfffffffffffffc). *)
    is_aligned_paddr (Physaddr (ti_ea_ra sp0)) 8 = true ->
    is_aligned_paddr (Physaddr (ti_ea_s0 sp0)) 8 = true ->
    is_aligned_paddr (Physaddr (ti_ea_ra (ti_sp1 sp0))) 8 = true ->
    is_aligned_paddr (Physaddr (ti_ea_s0 (ti_sp1 sp0))) 8 = true ->
    uint (ti_ea_ra (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    uint (ti_ea_s0 (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pc_is pc_e0 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    mepc ↦ᵣ mepc0 -∗
    satp ↦ᵣ satp0 -∗
    medeleg ↦ᵣ medeleg0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    mie ↦ᵣ mie0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    mtime ↦ᵣ mtime0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    (* the per-CPU stack0 pointer word _entry loads *)
    ([∗ list] j ∈ seq 0 8, (pa_add entry_ld_ea j) ↦ₘ{ dq } nth_byte v_stack0 j) -∗
    (* start()'s frame slots *)
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra sp0) j) ↦ₘ nth_byte vsra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 sp0) j) ↦ₘ nth_byte vss0 j) -∗
    (* timerinit's frame slots *)
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra (ti_sp1 sp0)) j) ↦ₘ nth_byte vtra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 (ti_sp1 sp0)) j) ↦ₘ nth_byte vts0 j) -∗
    kernel_text -∗
    ( ∀ (ms0 : mword 64)
        (HoIE : eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false)
        (HoPRV : eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false)
        (HoSXL : _get_Mstatus_SXL ms0 = ('b"10")),
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ cms5 (st_ms1 ms0) -∗
      pmpcfg_n ↦ᵣ st_pmpcfg1 pmpcfg0 -∗
      pmpaddr_n ↦ᵣ st_pmpaddr1 pmpcfg0 pmpaddr00 -∗
      pc_is st_main -∗
      gpr_file (st_mout (m_jal m v_stack0 mhartid_in) sp0 ms0 mie0 mideleg0
                  menvcfg0 mcounteren0 mtime0 mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      mepc ↦ᵣ st_main -∗
      satp ↦ᵣ satp_legalized satp0 (mword_of_int 0) -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 st_ffff -∗
      mideleg ↦ᵣ st_mdl1 mideleg0 -∗
      mie ↦ᵣ st_mie1 mie0 mideleg0 -∗
      menvcfg ↦ᵣ menvcfg_legalized menvcfg0 (ti_menv1 menvcfg0) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (ti_mcen1 mcounteren0) -∗
      mtime ↦ᵣ mtime0 -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline mtime0) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add entry_ld_ea j) ↦ₘ{ dq } nth_byte v_stack0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra sp0) j) ↦ₘ nth_byte (add_vec_int pc_e7 4) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 sp0) j) ↦ₘ nth_byte (m !!! Regidx ti_s0) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra (ti_sp1 sp0)) j) ↦ₘ nth_byte st_ra_link j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 (ti_sp1 sp0)) j) ↦ₘ nth_byte sp0 j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros sp0 HN Hpmp HlpeE Hal_ra Hal_s0 Hal_tra Hal_ts0 Hbnd_ra Hbnd_s0.
    iIntros "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen
             Hmtime Hstc Hstk Hsra Hss0 Htra Hts0 #Htext Hcont".
    assert (Hld_al : is_aligned_paddr (Physaddr entry_ld_ea) 8 = true)
      by (vm_compute; reflexivity).
    (* ---- _entry: reset -> jal start (PC = 0x80000058) ---- *)
    iApply (wp_entry E Φ m v_stack0 mhartid_in pmpcfg0 (dq := dq) HN Hpmp Hld_al
              with "Hmm Hpcf Hpc Hfile Hmh Hstk Htext").
    iIntros "Hmm Hpcf Hpc Hfile Hmh Hstk".
    iEval (change pc_start with st_pc30) in "Hpc".
    (* wp_start's entry-file lookups over _entry's output map *)
    assert (Hkra : (Regidx i_jal : regidx) = Regidx ti_ra) by (vm_compute; reflexivity).
    assert (HEra : m_jal m v_stack0 mhartid_in !!! Regidx ti_ra = add_vec_int pc_e7 4).
    { unfold m_jal. rewrite Hkra. rewrite lookup_total_insert. reflexivity. }
    assert (HEs0 : m_jal m v_stack0 mhartid_in !!! Regidx ti_s0 = m !!! Regidx ti_s0).
    { unfold m_jal, m_cadd, m_mul, m_caddi, m_csrr, m_clui, m_ld, m_auipc.
      repeat (rewrite lookup_total_insert_ne;
              [ | let H := fresh in intro H;
                  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
                  vm_compute in H; discriminate H ]).
      reflexivity. }
    (* ---- start(): jal-entry -> MRET (Supervisor mode at <main>) ---- *)
    iApply (wp_start E Φ (m_jal m v_stack0 mhartid_in) sp0 (add_vec_int pc_e7 4)
              (m !!! Regidx ti_s0)
              mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 mtime0 stimecmp0 mhartid_in
              mcounteren0 pmpcfg0 pmpaddr00 vsra vss0 vtra vts0
              HN Hpmp HlpeE eq_refl HEra HEs0
              Hal_ra Hal_s0 Hal_tra Hal_ts0 Hbnd_ra Hbnd_s0
              with "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv
                    Hmcen Hmtime Hstc Hsra Hss0 Htra Hts0 Htext [Hcont Hstk]").
    iIntros (ms0 HoIE HoPRV HoSXL)
      "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie
       Hmenv Hmcen Hmtime Hstc Hsra Hss0 Htra Hts0".
    iApply ("Hcont" $! ms0 HoIE HoPRV HoSXL
              with "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl
                    Hmie Hmenv Hmcen Hmtime Hstc Hstk Hsra Hss0 Htra Hts0").
  Qed.

End WpKernelNew.

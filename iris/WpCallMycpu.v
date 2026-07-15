(* The generic "call mycpu" composite (jal ra,mycpu -> whole mycpu -> return).
   Any S-mode function that calls mycpu reuses this — push_off, holding, and
   acquire — so it lives in its own leaf file above WpMycpu rather than inside
   one function's proof, which keeps those callers from depending on each other.
   [wp_call_mycpu] threads raw config cells; [wp_call_mycpu_scfg_cs] is the
   [smode_config] view with the abstract callee_saved post. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv InstrBytes WpGpr WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelText WpGprCsrwCommon WpSmodeJal StackOwn CalleeSaved WpMycpu.
From Kernel Require KernelSyms.

Section WpCallMycpu.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_call_mycpu (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      :
    let ra_idx : mword 5 := mword_of_int 1 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let ra0 := m0 !!! Regidx ra_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    add_vec P (sign_extend' 64 jimm) = pcE ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file m -∗
    instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
    stack_own (m0 !!! Regidx csp_rs1) 2 -∗
    ( ∀ mo,
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mo -∗
      ⌜ callee_saved m mo /\
        mo !!! Regidx (mword_of_int 10 : mword 5)
          = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ⌝ -∗
      stack_own (m0 !!! Regidx csp_rs1) 2 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx m0 pcE ra0 ret_tgt HN Htarget Halign_tgt HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hfiom Hleg Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv #Htext Hpc Hfile Hjal Hstk Hcont".
    iDestruct (kv_cfg_split γ mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_jal_gpr_s_zca root_ppn γ E Φ P (mword_of_int 1) jimm m (1/2)%Qp
              HN  ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halign_tgt)
              with "Hsm Htlbinv Hpc Hfile Hjal [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite Htarget) in "Hpc".
    iDestruct (kv_cfg_recombine γ mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hsie & Hmie & Hmdl & Hmenv)".
    iApply (wp_mycpu root_ppn E Φ m0 2 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              ltac:(lia) HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hstk [Hsie Hcont]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile %Hmcs Hstk".
    iApply ("Hcont" with
              "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile [%] Hstk").
    destruct Hmcs as [Hcs Ha0]. split.
    - exact (callee_saved_insert_ra _ _ _ Hcs).
    - assert (Htp : m0 !!! Regidx (mword_of_int 4 : mword 5)
                    = m !!! Regidx (mword_of_int 4 : mword 5))
        by (rewrite /m0 lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
      rewrite -Htp. exact Ha0.
  Qed.

  (* jal->mycpu->return block, [smode_config] view with the ABSTRACT
     callee_saved post (mirrors the raw [wp_call_mycpu]).  For concrete-
     mstatus0 callers (holding/acquire) that want the returned register
     file abstractly (mo + callee_saved + a0) rather than pinned. *)
  Lemma wp_call_mycpu_scfg_cs (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      :
    let ra_idx : mword 5 := mword_of_int 1 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let ra0 := m0 !!! Regidx ra_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    add_vec P (sign_extend' 64 jimm) = pcE ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γ (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file m -∗
    instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
    stack_own (m0 !!! Regidx csp_rs1) 2 -∗
    ( ∀ mo,
      smode_config γ (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mo -∗
      ⌜ callee_saved m mo /\
        mo !!! Regidx (mword_of_int 10 : mword 5)
          = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ⌝ -∗
      stack_own (m0 !!! Regidx csp_rs1) 2 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx m0 pcE ra0 ret_tgt HN Htarget Halign_tgt Hal0.
    iIntros "Hsm Htlbinv #Htext Hpc Hfile Hjal Hstk Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_call_mycpu root_ppn γ E Φ P jimm m
              mstatus0 mie_v mdv0 menvcfg0
              HN Htarget Halign_tgt
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hfiom Hleg Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hjal Hstk [-]").
    iIntros (mo) "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile %Hcs Hstk".
    iDestruct (smode_config_rebuild γ (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" $! mo with "Hsm Htlbinv Hpc Hfile [] Hstk").
    iPureIntro. exact Hcs.
  Qed.

End WpCallMycpu.

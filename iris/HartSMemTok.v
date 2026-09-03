(* HartSMemTok.v -- TOKEN-THREADED S-mode RAM data-access engines, width 8.

   [HartSMem]'s S-mode LOAD/STORE chains hand their two obligations --
   the translation closure and the memory obligation -- to the engine
   SEPARATELY, so a leaf holding one [TsoCtx.own_context] token cannot
   serve both: the closures are captured before either runs.  For the
   KERNEL-table regimes that is fine (the regime's translate is
   witness-backed and needs no token; the token goes into the memory
   obligation, cf. [WpSmodePtMem.wp_ld_s_r_t]).  The USER-table
   trampoline leaves ([UserretPt.wp_uld_pt] / [UservecPt.wp_usd_pt])
   are different: their data translation is [UptWalkPt.utf_translate],
   whose A/D write-back appends to the ledger and therefore TAKES AND
   RETURNS the running token -- and the trapframe word they then access
   is a ctx-tier word ([TsoCtx.ctx_phys_word_pointsto]), whose
   [Mobl_ram]/[Wobl_ram] discharge needs the token too.

   These variants thread it through the engine: the translation
   closure's post carries [own_context XI] beside [Rt rsf], and the
   memory obligation is taken as a WAND [own_context XI -∗ Mobl/Wobl],
   which the engine fills at the seam between the two stages (the one
   point where it holds both).  The token's way back out is the
   obligation's own rider [R] -- a leaf puts [own_context XI] in [R].

   Everything else is [HartSMem]'s text verbatim, at the RAM instance
   and width 8 (the only width the trampoline trapframe accesses use).
   This lives in its own file because HartSMem's rebuild cone is ~470
   files (durable-notes: additive changes to shared files go in a new
   leaf file). *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents HartMPmp HartMFetch HartMFrame
        HartMLoad HartMStore.
Require Import RiscvExtras RiscvFetchExec.
Require Import RegFile WpGpr.
Require Import TsoCtx.
Require Import HartSMem.
Local Open Scope Z_scope.
Import Defs.

(* HartSMem's glue reducer, verbatim (it is Local there). *)
Local Ltac sm_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR Riscv.rv64d_types.returnR
     andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Section smem_tok.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* the RAM-8 read/write nodes, spelled as HartSMem's own instances do *)
  Local Notation lnode8 :=
    (fun pa bytes R H => swp_read_ram_node8 pa bytes R
                           (addr_is_ram_not_dev pa H)).
  Local Notation snode8 :=
    (fun pa v R rr H => swp_write_ram_node8 pa v R rr
                          (addr_is_ram_not_dev pa H)).

  (* ------------------------------------------------------------------ *)
  (* LOAD side.                                                          *)
  (* ------------------------------------------------------------------ *)

  Lemma swp_translate_and_read_value_S8_tok (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * 8))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Mobl_ram 8 pa bytes R) -∗
    swp (translate_and_read_value (Virtaddr ea) 8 (Load Data)
           false false false)
      (fun r => ⌜r = Values.Ok (Physaddr pa, bytes)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma
      Hpcfg Hpaddr Hep HA Hord HR Hcov Hpallow Hram Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hrw Hro Htr Hmem".
    unfold translate_and_read_value.
    iApply (swp_bind_use (translateAddr (Virtaddr ea) (Load Data)) _ _ _
              with "[Hfrag Hres Htok Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Htok Hrw Hro"). }
    iIntros (v) "(-> & Hland)". cbn beta iota.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Htok & Hany)".
    iSpecialize ("Hmem" with "Htok").
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗
                         hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗ R)%I) _
              with "[Hrw Hro Hmem] [Hres Hany]").
    { iApply (swp_mem_read_S 8 Drw Dro Df rsf (Physaddr pa) bytes R Hdisj
                HDmst HDpriv Hpriv' ltac:(rewrite Hmst'; exact Hep)
                with "Hcert Hrw Hro [Hmem]").
      iIntros "Hrw Hro".
      iApply (swp_checked_mem_read_S 8 vmw8 addr_is_ram pma_allows_ram
                (ram_pma_load 8 vmw8 dvd8) (ram_mmio_r 8 vmw8)
                (ram_pmprange 8 vmw8 dvd8 uintw8) (Mobl_ram 8) lnode8
                Drw Dro Df rsf pa pmar0 pcfg paddr bytes R
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif' Hpma' Hpcfg' Hpaddr'
                HA Hord HR Hcov Hpallow Hram Hpa with "Hcert Hrw Hro Hmem"). }
    iIntros (v) "(-> & Hrw & Hro & HR)". cbn beta iota.
    iApply swp_ret. iSplitR; [done|].
    iExists rsf. iFrame. done.
  Qed.

  Lemma swp_vmem_read_addr_S8_tok (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * 8))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Mobl_ram 8 pa bytes R) -∗
    swp (vmem_read_addr (Virtaddr ea) 8 (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif
      Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read_addr.
    rewrite Hva. sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w ea 8 vmw8 Hva).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode Supervisor) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret.
    match goal with
    | |- context [ if Instances.generic_neq md Bare then ?x else ?y ] =>
        replace (if Instances.generic_neq md Bare then x else y) with x
          by (destruct (Instances.generic_neq md Bare); reflexivity)
    end.
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer
              (translate_and_read_value (Virtaddr ea) 8 (Load Data)
                 false false false) _ _ C HC
              with "[Hfrag Hres Htok Hrw Hro Htr Hmem] [-]").
    { iApply (swp_translate_and_read_value_S8_tok Drw Dro Df rs ea pa pmar0
                pcfg paddr bytes R Rt rr Hdisj HDmst HDpriv HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr Hep HA Hord HR Hcov
                Hpallow Hram Hpa with "Hcert Hfrag Hres Htok Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)". cbn beta iota. sm_glue.
    rewrite mbind0R_ret. sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite (usvd_zeros_full_gen (8 * 8) bytes ltac:(lia)).
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok bytes)). iFrame. done.
  Qed.

  Lemma swp_vmem_read_S8_tok (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * 8))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx i) offset in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Mobl_ram 8 pa bytes R) -∗
    swp (vmem_read (Regidx i) offset 8 (Load Data) false false false)
      (fun r => ⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_read.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Load Data) 8)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen 8 Drw Dro Df rs i m offset
                (Load Data) Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL Htf with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_read_addr (Virtaddr ea) 8 (Load Data) false false false)
              _ C HC with "[Hfrag Hres Htok Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_addr_S8_tok Drw Dro Df rs ea pa pmar0 pcfg paddr
                bytes R Rt rr md Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr
                HDhtif Hpriv Hhtif Hpma Hpcfg Hpaddr HSXL Hmode Hep HA Hord HR
                Hcov Hpallow Hram Hva Hpa
                with "Hcert Hfrag Hres Htok Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)".
    iApply ("Hcont" $! (Values.Ok bytes)). iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_LOAD_ram_S8_tok (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (imm : SailStdpp.Values.mword 12)
      (rs1 rd : SailStdpp.Values.mword 5) (is_unsigned : bool)
      (m : regfile) (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (bytes : SailStdpp.Values.mword (8 * 8))
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Load Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Load Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    uint rd <> 0 ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Load Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Mobl_ram 8 pa bytes R) -∗
    swp (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 8)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd
                            := regval_into_reg (extend_value is_unsigned bytes)]> m) ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ resv_any cpu_id ∗ R).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hhtif Hpma Hpcfg Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR
      Hcov Hpallow Hram Hva Hpa Hrd.
    iIntros "#Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem".
    unfold execute_LOAD.
    change (Z.leb 8 xlen_bytes) with true.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok bytes⌝ ∗ gpr_file m ∗
                         ∃ rsf : regstate,
                           ⌜ rsf = rs \/
                             exists tv, rsf = register_set tlb tv rs ⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rt rsf ∗ resv_any cpu_id ∗ R)%I) _
              with "[Hfrag Hres Htok Hf Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_read_S8_tok Drw Dro Df rs rs1 m (sign_extend' 64 imm) pa
                pmar0 pcfg paddr bytes R Rt rr md Hdisj HDmst HDpriv HDmenv
                HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hhtif Hpma Hpcfg
                Hpaddr Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HR Hcov Hpallow
                Hram Hva Hpa with "Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hf & Hland)". cbn beta iota.
    iApply (swp_bind0_use (wX_bits (Regidx rd) (extend_value is_unsigned bytes))
              _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m (extend_value is_unsigned bytes) Hrd
                with "Hcert Hf"). }
    iIntros (u) "Hf". iApply swp_ret. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* STORE side.                                                         *)
  (* ------------------------------------------------------------------ *)

  Lemma swp_vmem_write_addr_S8_tok (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (ea pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 8))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Wobl_ram 8 pa v R) -∗
    swp (vmem_write_addr (Virtaddr ea) 8 v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif Hpriv Hpma
      Hpcfg Hpaddr Hhtif HSXL Hmode Hep HA Hord HW Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write_addr.
    rewrite Hva. sm_glue.
    rewrite mbind0_ret.
    rewrite (split_on_page_boundary_aligned_w ea 8 vmw8 Hva).
    rewrite /returnM mliftR_ret mbind_ret. sm_glue.
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". rewrite Hpriv.
    rewrite Hep.
    rewrite mliftR_ret mbind_ret. sm_glue.
    unfold Defs.and_boolM.
    iApply (swp_use_cer3 (translationMode Supervisor) _ _ _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj Hmode
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite mbindR_ret.
    match goal with
    | |- context [ if Instances.generic_neq md Bare then ?x else ?y ] =>
        replace (if Instances.generic_neq md Bare then x else y) with x
          by (destruct (Instances.generic_neq md Bare); reflexivity)
    end.
    sm_glue.
    change (Z.gtb 0 0) with false. sm_glue.
    change (sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer (translateAddr (Virtaddr ea) (Store Data)) _ _ C HC
              with "[Hfrag Hres Htok Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hfrag Hres Htok Hrw Hro"). }
    iIntros (v0) "(-> & Hland)". sm_glue.
    iDestruct "Hland" as (rsf) "(%Hland & Hrw & Hro & Hres & Htok & Hany)".
    iSpecialize ("Hmem" with "Htok").
    iDestruct "Hany" as (rr') "Hfrag".
    assert (Hpriv' : register_lookup cur_privilege rsf = Supervisor)
      by (rewrite (sland_lookup rs rsf Hland cur_privilege eq_refl); exact Hpriv).
    assert (Hmst' : register_lookup mstatus rsf = register_lookup mstatus rs)
      by (apply (sland_lookup rs rsf Hland mstatus eq_refl)).
    assert (Hhtif' : register_lookup htif_tohost_base rsf = None)
      by (rewrite (sland_lookup rs rsf Hland htif_tohost_base eq_refl); exact Hhtif).
    assert (Hpma' : register_lookup pma_regions rsf = pmar0)
      by (rewrite (sland_lookup rs rsf Hland pma_regions eq_refl); exact Hpma).
    assert (Hpcfg' : register_lookup pmpcfg_n rsf = pcfg)
      by (rewrite (sland_lookup rs rsf Hland pmpcfg_n eq_refl); exact Hpcfg).
    assert (Hpaddr' : register_lookup pmpaddr_n rsf = paddr)
      by (rewrite (sland_lookup rs rsf Hland pmpaddr_n eq_refl); exact Hpaddr).
    change (Bool.eqb false (is_store_conditional (Store Data))) with true.
    cbn beta iota zeta delta [Defs.assert_exp].
    rewrite /returnM mliftR_ret mbind0_ret. sm_glue.
    iApply (swp_use_cer2
              (mem_write_ea (Physaddr pa) 8 (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_mem_write_ea_S 8 vmw8 addr_is_ram pma_allows_ram
                (ram_pma_store 8 vmw8 dvd8)
                (ram_pmprange 8 vmw8 dvd8 uintw8)
                Drw Dro Df rsf pa pmar0 pcfg paddr Hdisj
                HDmst HDpriv HDpma HDcfg HDaddr Hpriv' Hpma' Hpcfg' Hpaddr'
                ltac:(rewrite Hmst'; exact Hep) HA Hord HW Hcov Hpallow Hram
                Hpa with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". sm_glue.
    rewrite (subrange_full_gen_cast (8 * 8) v ltac:(lia)).
    iApply (swp_use_cer2
              (mem_write_value (Physaddr pa) 8 v (Store Data) PBMT_PMA
                 false false false) _ _ _ C HC with "[Hrw Hro Hmem Hfrag] [-]").
    { iApply (swp_mem_write_value_S 8 vmw8 addr_is_ram pma_allows_ram
                (ram_pma_store 8 vmw8 dvd8) (ram_mmio_w 8 vmw8)
                (ram_pmprange 8 vmw8 dvd8 uintw8) (Wobl_ram 8) snode8
                Drw Dro Df rsf pa v pmar0 pcfg paddr R rr'
                Hdisj HDmst HDpriv HDpma HDcfg HDaddr HDhtif Hpriv' Hpma'
                Hpcfg' Hpaddr' Hhtif' ltac:(rewrite Hmst'; exact Hep)
                HA Hord HW Hcov Hpallow Hram Hpa
                with "Hcert Hfrag Hrw Hro Hmem"). }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". sm_glue.
    rewrite mbindR_ret. sm_glue.
    change (not sys_misaligned_order_decreasing && false) with false. sm_glue.
    rewrite mbindR_ret. sm_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). iSplitR; [done|].
    iExists rsf. iFrame. done.
  Qed.

  Lemma swp_vmem_write_S8_tok (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (i : SailStdpp.Values.mword 5) (m : regfile)
      (offset pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 8))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx i) offset in
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Store Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Wobl_ram 8 pa v R) -∗
    swp (vmem_write (Regidx i) offset 8 v (Store Data) false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros ea Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr HDhtif
      Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HW
      Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold vmem_write.
    iApply (swp_use_cer
              (get_transformed_data_addr (Regidx i) offset (Store Data) 8)
              _ _ C HC with "[Hf Hrw Hro] [-]").
    { iApply (swp_get_transformed_data_addr_S_gen 8 Drw Dro Df rs i m
                offset (Store Data) Hdisj HDmst HDpriv HDmenv HDsatp Hpriv Hep
                ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Hmxr Hpmm HSXL Htf with "Hcert Hf Hrw Hro"). }
    iIntros (v0) "(-> & Hf & Hrw & Hro)". cbn beta iota. sm_glue.
    rewrite mbindR_ret. sm_glue.
    iApply (swp_use_cer0
              (vmem_write_addr (Virtaddr ea) 8 v (Store Data)
                 false false false) _ C HC
              with "[Hfrag Hres Htok Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_write_addr_S8_tok Drw Dro Df rs ea pa v pmar0 pcfg paddr
                R Rt rr md Hdisj HDmst HDpriv HDsatp HDpma HDcfg HDaddr HDhtif
                Hpriv Hpma Hpcfg Hpaddr Hhtif HSXL Hmode Hep HA Hord HW Hcov
                Hpallow Hram Hva Hpa
                with "Hcert Hfrag Hres Htok Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hland)".
    iApply ("Hcont" $! (Values.Ok true)). iSplitR; [done|]. iFrame.
  Qed.

  Lemma swp_execute_STORE_ram_S8_tok (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (imm : SailStdpp.Values.mword 12)
      (rs2 rs1 : SailStdpp.Values.mword 5) (m : regfile)
      (pa : SailStdpp.Values.mword 64)
      (v : SailStdpp.Values.mword (8 * 8))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (R : iProp Σ) (Rt : regstate -> iProp Σ) (rr : option resv)
      (md : SATPMode) :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    autocast (T := mword)
      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 8 8) 1) 0) = v ->
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (menvcfg : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus rs)) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg rs))
      = PMM_Disabled ->
    _get_Mstatus_SXL (register_lookup mstatus rs) = 'b"10" ->
    hval (Drw ∪ Dro) Drw rs
      (transform_effective_address (Virtaddr ea) (Store Data))
      (Virtaddr ea) rs ->
    hval (Drw ∪ Dro) Drw rs (translationMode Supervisor) md rs ->
    effectivePrivilege (Store Data) (register_lookup mstatus rs) Supervisor
      = returnM Supervisor ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    addr_is_ram pa ->
    is_aligned_vaddr (Virtaddr ea) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    Rt rs -∗
    TsoCtx.own_context XI -∗
    gpr_file m -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (resv_frag cpu_id rr -∗ Rt rs -∗ TsoCtx.own_context XI -∗
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translateAddr (Virtaddr ea) (Store Data))
         (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                   ∃ rsf : regstate,
                     ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                     hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                     Rt rsf ∗ TsoCtx.own_context XI ∗ resv_any cpu_id)) -∗
    (TsoCtx.own_context XI -∗ Wobl_ram 8 pa v R) -∗
    swp (execute_STORE imm (Regidx rs2) (Regidx rs1) 8)
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗ gpr_file m ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  Rt rsf ∗ R ∗ resv_frag cpu_id None).
  Proof.
    intros ea Hdata Hdisj HDmst HDpriv HDmenv HDsatp HDpma HDcfg HDaddr
      HDhtif Hpriv Hpma Hpcfg Hpaddr Hhtif Hmxr Hpmm HSXL Htf Hmode Hep HA Hord
      HW Hcov Hpallow Hram Hva Hpa.
    iIntros "#Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem".
    unfold execute_STORE.
    change (Z.leb 8 xlen_bytes) with true.
    cbn beta iota zeta delta [Defs.assert_exp'].
    rewrite /returnM mbind_ret. sm_glue.
    iApply (swp_bind_use (rX_bits (Regidx rs2)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs2 m with "Hcert Hf"). }
    iIntros (v0) "(-> & Hf)". sm_glue.
    rewrite Hdata.
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ gpr_file m ∗
                         ∃ rsf : regstate,
                           ⌜ rsf = rs \/
                             exists tv, rsf = register_set tlb tv rs ⌝ ∗
                           hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                           Rt rsf ∗ R ∗ resv_frag cpu_id None)%I) _
              with "[Hfrag Hres Htok Hf Hrw Hro Htr Hmem] [-]").
    { iApply (swp_vmem_write_S8_tok Drw Dro Df rs rs1 m (sign_extend' 64 imm) pa
                v pmar0 pcfg paddr R Rt rr md Hdisj HDmst HDpriv HDmenv HDsatp
                HDpma HDcfg HDaddr HDhtif Hpriv Hpma Hpcfg Hpaddr Hhtif
                Hmxr Hpmm HSXL Htf Hmode Hep HA Hord HW Hcov Hpallow Hram Hva
                Hpa with "Hcert Hfrag Hres Htok Hf Hrw Hro Htr Hmem"). }
    iIntros (v0) "(-> & Hf & Hland)". cbn beta iota.
    iApply swp_ret. by iFrame.
  Qed.

End smem_tok.

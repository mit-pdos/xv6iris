(* S-mode Store leaf lemmas (smode_config/Supervisor, decode family Store).
   Relocated from function proof files (per-(mode,family) leaf reorg). *)
Require Import WpSmodeLeafBase.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes WpDecode WpLeafCommon WpGpr WpGprCsrwCommon.
Require Import SmodeCore WpSmodeGpr WpEntryNew StackOwn CalleeSaved.
Require Import WpMmodeLeafBase WpSmodeLeafBase.
Import Defs.
Require Import WpSmodeToBeDeleted.
Require Import WpMmodeStore.

(* helper: exec_execute_STORE_4_gpr_S_walk *)
  Lemma exec_execute_STORE_4_gpr_S_walk :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32))).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_4_gpr_S_walk rs1 offset _ region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh)).
    cbn match.
    apply exec_returnM.
  Qed.

Section WpSmodeStore.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_csd_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: X-bit + RAM coverage (geometry derived from instr_bytes) *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_csd_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iApply (wp_csd_s root_ppn E Φ pc rs2 rs1 imm (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_csd_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csd_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign8 & Hbytes)".
    assert (Halign8 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign8.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, sp, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx csp_rs1 = Some (m !!! Regidx csp_rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    (* per-access PMP: derive [pmpRangeMatch] for the store address from the
       folded RAM coverage + [pa]'s RAM-ness (no longer a caller premise). *)
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match a8 (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) as Hrange_st.
    (* the walk's PTE bytes + their RAM-ness (used by the data-miss branch) *)
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    (* tick nextPC := pc+2 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value csp_rs1 (m !!! Regidx csp_rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 (m !!! Regidx rs2))).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, sp, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { change sp with (Regidx csp_rs1).
        rewrite (exec_execute_STORE_8_gpr_S_walk rs2 csp_rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64. reflexivity. }
      (* the data fill, mirrored on the ghost cell *)
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa (m !!! Regidx rs2) vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 (m !!! Regidx rs2))).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, sp, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { change sp with (Regidx csp_rs1).
        rewrite (exec_execute_STORE_8_gpr_S rs2 csp_rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa (m !!! Regidx rs2) vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_csdsp_gpr_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    (* [pmpRangeMatch] and the PMP config are now discharged inside
       [wp_csdsp_gpr_s] from the folded [tlb_inv]; the wrapper only supplies
       the RAM-derived Sv39 geometry. *)
    iApply (wp_csdsp_gpr_s root_ppn E Φ pc uimm rs2 (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_csdsp_gpr_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csdsp_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ pc uimm rs2 m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_csw_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_csw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (ea ↦₄ vold)%I with "[Hbytes]" as "Hbw4".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpal4. }
    iApply (wp_csw_s root_ppn E Φ pc rs2 rs1 imm (svpn_of ea) m vold
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbw4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile Hbw").
  Qed.

  Lemma wp_csw_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗ ea ↦₄ (RiscvExtras.trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_csw_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sb_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 8)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)) in
    let svpn := svpn_of a8 in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) in
    ↑minstretN ⊆ E ->
    (* the superpage-identity geometry facts below (svpn := svpn_of a8) are
       derived internally at this leaf from [addr_is_ram a8]; no caller obligation. *)
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    (pa ↦ₘ vold) -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      (pa ↦ₘ (nth_byte storeval 0)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa svpn storeval HN.
    iIntros "Hsm Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbyte Hcont".
    (* [push to leaf] derive the svpn geometry facts here from [addr_is_ram a8]. *)
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa0.
    { iDestruct (mem_ram with "Hbyte") as %Hr0. iPureIntro. exact Hr0. }
    assert (Hpa_a8 : pa = a8)
      by (unfold pa; rewrite Z.mul_0_l avi0; apply zero_extend'_id).
    assert (Hrama8 : addr_is_ram a8) by (rewrite <- Hpa_a8; exact Hrampa0).
    pose proof (RiscvExtras.ram_canonical a8 Hrama8) as Hcanon.
    assert (Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn)
      by reflexivity.
    pose proof (WpSmodeGpr.ram_ident root_ppn a8 Hrama8) as Hident.
    pose proof (RiscvExtras.ram_mask a8 Hrama8) as Hmask.
    pose proof (RiscvExtras.ram_svpn2 a8 Hrama8) as Hvpn2.
    pose proof (RiscvExtras.ram_mvpn a8 Hrama8) as Hmvpn.
    pose proof (WpSmodeGpr.ram_mppn a8 Hrama8) as Hmppn.
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 1) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 1))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hms1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (mem_ram with "Hbyte") as %Hr0. iPureIntro. exact Hr0. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 1 <= ram_base + ram_size)%Z)
      by (destruct Hrampa as [_ Hh]; unfold ram_base, ram_size in *; lia).
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 1
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    (* the walk's PTE bytes + their RAM-ness (used by the data-miss branch) *)
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 1 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 1 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                   with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
      iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 1 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 1 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                   with "Hhw Hinv Hhs' Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
      iApply ("Hcont" with "Hsm [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sd_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch: X-bit + RAM coverage (geometry derived from instr_bytes) *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
    pose proof Hrange_ld as Hrange_st.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_8_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sd_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := m !!! Regidx rs2 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ pa ↦₈ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iDestruct (ram_bounds_of_bytes pa (DfracOwn 1) vold with "Hbytes") as %(Hr0 & _ & Hlo & Hfit).
    iApply (wp_sd_s root_ppn E Φ pc rs2 rs1 imm (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_sd_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 64) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ea ↦₈ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗ ea ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sd_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := ea in
    let pa := a8 in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    pa ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      pa ↦₄ storeval -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign4 & Hbytes)".
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true) by exact Hpalign4.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 4) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 4))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 region_pte)
      "(Hpmpc & Hpmpa & %Hpmpp & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hmsp : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hrampa3.
    { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb3") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add pa 3 Hnw) as Heq.
      destruct Hrampa3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match_w pa (vec_access_dec pmpaddr00 0) 4
                  ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_st.
    iAssert (⌜ is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ⌝)%I as %Halignp.
    { iDestruct "Hpbytes" as "[$ _]". }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct "Hpbytes" as "[_ Hpbytes]".
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct "Hpbytes" as "[_ Hpbytes]". iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 4 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 4 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 4 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 4 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 4 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 4 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_4_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id; exact Halign4) ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; exact Hpalign4)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul4 subrange_id sign_extend'_id; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul4 subrange_id sign_extend'_id. reflexivity. }
      iMod (upd_window_4 σ.(mem) pa storeval vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₄ storeval)%I with "[Hbytes]" as "Hbw".
      { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign4. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00 region_pte
                  Hpmpp Hpteregion HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  Lemma wp_sw_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             Hpc Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpal4 & Hbytes)".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr.
      iPureIntro. exact Hr. }
    iAssert (ea ↦₄ vold)%I with "[Hbytes]" as "Hbw4".
    { rewrite /word4_pointsto. iFrame "Hbytes". iPureIntro. exact Hpal4. }
    iApply (wp_sw_s root_ppn E Φ pc rs2 rs1 imm (svpn_of ea) m vold
              mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical ea Hr0) ltac:(reflexivity)
              (ram_ident root_ppn ea Hr0) (ram_mask ea Hr0)
              (ram_svpn2 ea Hr0) (ram_mvpn ea Hr0) (ram_mppn ea Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hinstr Hbw4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                          Hpc Hfile Hbw").
  Qed.

  Lemma wp_sw_s_ram_scfg (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : gmap regidx (mword 64)) (vold : bv 32) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ea ↦₄ vold -∗
    ( smode_config γ dq -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      ea ↦₄ (trunc32 (m !!! Regidx rs2)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea HN.
    iIntros "Hsm Htlbinv Hpc Hfile Hinstr Hbw Hcont".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_sw_s_ram root_ppn E Φ pc rs2 rs1 imm m vold mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hbw").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbw".
    iDestruct (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hbw").
  Qed.

End WpSmodeStore.

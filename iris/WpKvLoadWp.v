From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore WpKvLoad.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvLoadWp.v — the kernelvec ld restore WP.  A `c.ldsp rd, uimm(sp)` running
   in Supervisor mode at a kernel-text superpage address va, reading 8 bytes
   from the stack frame (superpage TLB hit) into rd.  Mirror of wp_kv_store_2
   in WpKvStore but reading into a GPR (gpr_file update, memory unchanged). *)

Section KVLW.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

  Lemma wp_kv_load_2 (va : mword 64) (w : mword 16) (uimm : mword 6) (rd : mword 5) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (v : bv 64) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_ld region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let offset := sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) in
    let ea := add_vec vsp offset in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (* fetch superpage-identity bv facts for va *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    (* load superpage-identity bv facts for a8 / svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr va) 2 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_ld ->
    (override_PMA (PMA_Region_attributes region_ld) PBMT_PMA).(PMA_readable) = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC w = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w) s0 = Some (C_LDSP (uimm, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dq} nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dq} nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa data2 HN Hrd Hsp Hmrd HSXL Hmode Hasid Hvec5 Hvecld
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
      Hcanon Hvpn_def Hident Hmask Hmatchf Hexecf Hmatch Hread Hpmm
      HA0 Hord0 Hrange0f Hrange0 HX0 HR0 Halignf Halign8 Hpalign8 HisRVC HmisaC HmisaS HMPRV HMXR
      Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")     as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmenv")    as %Lmenv.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")    as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")     as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")    as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hsp with "Hfile") as "[Hspc Hfb1]".
    iDestruct (reg_valid with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_at_2 root_ppn va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec5 Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
                 HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa' Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b1) = Some (None, set_reg s (R_bool minstret_increment) b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (set_reg s (R_bool minstret_increment) b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (set_reg s (R_bool minstret_increment) b1)).
        replace (register_lookup misa (set_reg s (R_bool minstret_increment) b1).(sregs)) with misa0.
        2:{ unfold set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int va 2)).
    assert (Lsp_pc : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc.(sregs) = vsp).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lsp. }
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpriv. }
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lsatp. }
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Ltlb. }
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lms. }
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmenv. }
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpmpc. }
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpmpaddr. }
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpma. }
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhtif. }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro.
      unfold s_pc, set_reg; cbn [mem]. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_pc Lhtif_pc) as Hwh.
    pose (s_x := set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
    { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8)) with a8
        by (cbn [bits_of_virtaddr]; change (0 * 8) with 0; rewrite avi0; reflexivity).
      replace pa with a8 by (unfold pa; change (0 * 8) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
      apply (exec_translateAddr_load_hit root_ppn a8 svpn satp0 tlbvec s_pc
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
               Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hvecld Hmask). }
    assert (Hload : exec (execute (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { unfold sp.
      rewrite (exec_execute_LOAD_8_gpr_S (zero_extend' 5 ('b"10")) rd
                 (zero_extend' 12 (concat_vec uimm ('b"000"))) v region_ld satp0 s_pc
                 ltac:(vm_compute; discriminate) Hrd Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc
                 Hmode ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lsp_pc; exact Halign8) ltac:(rewrite Lsp_pc; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lsp_pc; exact Hrange0) ltac:(rewrite Lpmpc_pc; exact HR0)
                 ltac:(rewrite Lpma_pc Lsp_pc; exact Hmatch) ltac:(rewrite Lsp_pc; exact Hpalign8)
                 Hread ltac:(rewrite Lsp_pc; apply Hwc) ltac:(rewrite Lsp_pc; apply Hws)
                 ltac:(rewrite Lsp_pc; apply Hwh) ltac:(intros j Hj; rewrite Lsp_pc; exact (Hbytesf j Hj))).
      subst s_x. reflexivity. }
    iModIntro.
    iExists (sFclsg_super s va b1 rd (extend_value false data2) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq_super root_ppn s va b1 w (C_LDSP (uimm, Regidx rd))
                    (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) rd
                    (extend_value false data2)
                    Hfetch_at Hsi_s Hdec (exec_execute_C_LDSP uimm (Regidx rd) s_pc) Hload (register_lookup minstret s.(sregs)) eq_refl).
      apply (forward_exec_cldsp_super root_ppn s va b1 w (C_LDSP (uimm, Regidx rd))
               (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) rd
               (extend_value false data2)
               Hfetch_at Hsi_s Hdec (exec_execute_C_LDSP uimm (Regidx rd) s_pc) Hload Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int va 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFclsg_super, base_upd_lsg_super. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
    - iModIntro.
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
  Qed.


  Lemma wp_kv_load_4 (va : mword 64) (w : mword 32) (uimm : mword 6) (rd : mword 5) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (v : bv 64) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_ld region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let offset := sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) in
    let ea := add_vec vsp offset in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    (* fetch superpage-identity bv facts for va *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (* load superpage-identity bv facts for a8 / svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_ld ->
    (override_PMA (PMA_Region_attributes region_ld) PBMT_PMA).(PMA_readable) = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_LDSP (uimm, Regidx rd), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dq} nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (extend_value false data2)]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dq} nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa data2 HN Hrd Hsp Hmrd HSXL Hmode Hasid Hvec5 Hvecld
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
      Hcanon Hvpn_def Hident Hmask Hmatchf Hexecf Hmatch Hread Hpmm
      HA0 Hord0 Hrange0f Hrange0 HX0 HR0 Halignf Halign8 Hpalign8 HisRVC HmisaC HmisaS HMPRV HMXR
      Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")     as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmenv")    as %Lmenv.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")    as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")     as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")    as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hsp with "Hfile") as "[Hspc Hfb1]".
    iDestruct (reg_valid with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_at_4 root_ppn va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec5 Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
                 HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa' Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b1) = Some (None, set_reg s (R_bool minstret_increment) b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (set_reg s (R_bool minstret_increment) b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (set_reg s (R_bool minstret_increment) b1)).
        replace (register_lookup misa (set_reg s (R_bool minstret_increment) b1).(sregs)) with misa0.
        2:{ unfold set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int va 2)).
    assert (Lsp_pc : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc.(sregs) = vsp).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lsp. }
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpriv. }
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lsatp. }
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Ltlb. }
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lms. }
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmenv. }
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpmpc. }
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpmpaddr. }
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lpma. }
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhtif. }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro.
      unfold s_pc, set_reg; cbn [mem]. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_pc Lhtif_pc) as Hwh.
    pose (s_x := set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
    { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8)) with a8
        by (cbn [bits_of_virtaddr]; change (0 * 8) with 0; rewrite avi0; reflexivity).
      replace pa with a8 by (unfold pa; change (0 * 8) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
      apply (exec_translateAddr_load_hit root_ppn a8 svpn satp0 tlbvec s_pc
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
               Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hvecld Hmask). }
    assert (Hload : exec (execute (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { unfold sp.
      rewrite (exec_execute_LOAD_8_gpr_S (zero_extend' 5 ('b"10")) rd
                 (zero_extend' 12 (concat_vec uimm ('b"000"))) v region_ld satp0 s_pc
                 ltac:(vm_compute; discriminate) Hrd Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc
                 Hmode ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lsp_pc; exact Halign8) ltac:(rewrite Lsp_pc; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lsp_pc; exact Hrange0) ltac:(rewrite Lpmpc_pc; exact HR0)
                 ltac:(rewrite Lpma_pc Lsp_pc; exact Hmatch) ltac:(rewrite Lsp_pc; exact Hpalign8)
                 Hread ltac:(rewrite Lsp_pc; apply Hwc) ltac:(rewrite Lsp_pc; apply Hws)
                 ltac:(rewrite Lsp_pc; apply Hwh) ltac:(intros j Hj; rewrite Lsp_pc; exact (Hbytesf j Hj))).
      subst s_x. reflexivity. }
    iModIntro.
    iExists (sFclsg_super s va b1 rd (extend_value false data2) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq_super root_ppn s va b1 (subrange_vec_dec w 15 0) (C_LDSP (uimm, Regidx rd))
                    (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) rd
                    (extend_value false data2)
                    Hfetch_at Hsi_s Hdec (exec_execute_C_LDSP uimm (Regidx rd) s_pc) Hload (register_lookup minstret s.(sregs)) eq_refl).
      apply (forward_exec_cldsp_super root_ppn s va b1 (subrange_vec_dec w 15 0) (C_LDSP (uimm, Regidx rd))
               (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, Regidx rd, false, 8)) rd
               (extend_value false data2)
               Hfetch_at Hsi_s Hdec (exec_execute_C_LDSP uimm (Regidx rd) s_pc) Hload Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmrd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (extend_value false data2)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int va 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (extend_value false data2)) with "Hrdc") as "Hfile".
    unfold sFclsg_super, base_upd_lsg_super. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
    - iModIntro.
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
  Qed.

  (* ==================================================================== *)
  (* wp_kv_addi16sp_2: the epilogue `c.addi16sp sp, imm` (sp restore) at a   *)
  (* 2-byte-aligned kernel-text superpage address va.  RVC fetch hits the   *)
  (* superpage TLB; the instruction is a pure ALU add to sp (NO data        *)
  (* memory), so there is no data translate.  Reuses forward_exec_cldsp_super*)
  (* (register write) with an ITYPE/ADDI execute.                           *)
  (* ==================================================================== *)
  Lemma wp_kv_addi16sp_2 (va : mword 64) (w : mword 16) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va) 4 = false ->
    matching_pma_region pmar0 (Physaddr va) 2 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 2 = true ->
    isRVC w = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w) s0 = Some (C_ADDI16SP imm6, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN Hsp HSXL Hmode Hasid Hvec5
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4 Hmatchf Hexecf
      HA0 Hord0 Hrange0f HX0 Halignf HisRVC HmisaC HmisaS Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")     as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")    as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")     as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")    as %Lhtif.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hsp with "Hfile") as "[Hspc Hfb1]".
    iDestruct (reg_valid with "Hreg Hspc") as %Lsp.
    iDestruct ("Hfb1" with "Hspc") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_at_2 root_ppn va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec5 Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
                 HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
                 with "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa' Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b1) = Some (None, set_reg s (R_bool minstret_increment) b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (set_reg s (R_bool minstret_increment) b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (set_reg s (R_bool minstret_increment) b1)).
        replace (register_lookup misa (set_reg s (R_bool minstret_increment) b1).(sregs)) with misa0.
        2:{ unfold set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int va 2)).
    assert (Lsp_pc : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc.(sregs) = vsp).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lsp. }
    pose (value := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6))).
    pose (s_x := set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint (zero_extend' 5 ('b"10") : mword 5)))) (regval_into_reg value)).
    assert (Haddi : exec (execute (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { change sp with (Regidx (zero_extend' 5 ('b"10"))).
      rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"10")) (zero_extend' 5 ('b"10")) (caddi16sp_imm imm6) s_pc).
      replace (Z.eqb (uint (zero_extend' 5 ('b"10") : mword 5)) 0) with false by (vm_compute; reflexivity).
      subst s_x. do 3 f_equal.
      rewrite (gpr_addi_val_lookup (zero_extend' 5 ('b"10")) (caddi16sp_imm imm6) s_pc ltac:(vm_compute; discriminate)).
      unfold value. rewrite Lsp_pc. reflexivity. }
    iModIntro.
    iExists (sFclsg_super s va b1 (zero_extend' 5 ('b"10")) value (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq_super root_ppn s va b1 w (C_ADDI16SP imm6)
                    (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) (zero_extend' 5 ('b"10")) value
                    Hfetch_at Hsi_s Hdec (exec_execute_C_ADDI16SP imm6 s_pc) Haddi (register_lookup minstret s.(sregs)) eq_refl).
      apply (forward_exec_cldsp_super root_ppn s va b1 w (C_ADDI16SP imm6)
               (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) (zero_extend' 5 ('b"10")) value
               Hfetch_at Hsi_s Hdec (exec_execute_C_ADDI16SP imm6 s_pc) Haddi Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hsp with "Hfile") as "[Hspc2 Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (zero_extend' 5 ('b"10") : mword 5)))) _
            (regval_into_reg value) with "Hreg Hspc2") as "[Hreg Hspc2]".
    iMod (reg_update _ PC _ (add_vec_int va 2) with "Hreg Hpc") as "[Hreg Hpc]".
    replace (gpr_of_Z (uint (zero_extend' 5 ('b"10") : mword 5))) with (gpr_of_Z 2)
      by (vm_compute; reflexivity).
    iDestruct ("Hfins" $! (regval_into_reg value) with "Hspc2") as "Hfile".
    unfold sFclsg_super, base_upd_lsg_super. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro.
      replace (gpr_of_Z (uint (zero_extend' 5 ('b"10") : mword 5))) with (gpr_of_Z 2)
        by (vm_compute; reflexivity).
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iModIntro.
      replace (gpr_of_Z (uint (zero_extend' 5 ('b"10") : mword 5))) with (gpr_of_Z 2)
        by (vm_compute; reflexivity).
      unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

  (* ==================================================================== *)
  (* wp_kv_loads_12: chain the first TWO ld restores —                      *)
  (*   ld ra, 0(sp)  @va   (4-aligned)  then  ld gp, 16(sp) @va+2 (2-aligned)*)
  (* Validates that the load WPs chain: load 1's gpr_file insert + PC        *)
  (* advance thread into load 2's precondition; each reads its own stack     *)
  (* cell (both hit the same stack-page TLB entry).                          *)
  (* ==================================================================== *)
  Lemma wp_kv_loads_12 (va : mword 64) (w1 : mword 32) (w2 : mword 16) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd1 vd2 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (v1 v2 : bv 64) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_l1 region_l2 region_f1 region_f2 : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let off1 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a81 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off1) (xlen - 0 - 1) 0) in
    let pa1 := zero_extend' 64 (add_vec_int a81 (0 * 8)) in
    let off2 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a82 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off2) (xlen - 0 - 1) 0) in
    let pa2 := zero_extend' 64 (add_vec_int a82 (0 * 8)) in
    let data1 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v1 in
    let vs := add_vec_int va 2 in
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vd1 ->
    m !! gpr_of_Z 3 = Some vd2 ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    (* shared CSR/PMP facts *)
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (* load 1 (ra @ va, 4-aligned) facts *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a81))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub pagesize_bits 1) 0)) = a81 ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f1 ->
    (override_PMA (PMA_Region_attributes region_f1) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa1) 8 = Some region_l1 ->
    (override_PMA (PMA_Region_attributes region_l1) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa1) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    is_aligned_vaddr (Virtaddr a81) 8 = true ->
    is_aligned_paddr (Physaddr pa1) 8 = true ->
    isRVC (subrange_vec_dec w1 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w1 15 0)) s0 = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    (* load 2 (gp @ vs, 2-aligned) facts *)
    neq_vec (bits_of_virtaddr (Virtaddr vs))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vs)) (Z.sub pagesize_bits 1) 0)) = vs ->
    neq_vec (access_vec_dec vs 0) ('b"0") = false ->
    neq_vec (access_vec_dec vs 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr vs) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a82))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub pagesize_bits 1) 0)) = a82 ->
    matching_pma_region pmar0 (Physaddr vs) 2 = Some region_f2 ->
    (override_PMA (PMA_Region_attributes region_f2) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa2) 8 = Some region_l2 ->
    (override_PMA (PMA_Region_attributes region_l2) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vs) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa2) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr vs) 2 = true ->
    is_aligned_vaddr (Virtaddr a82) 8 = true ->
    is_aligned_paddr (Physaddr pa2) 8 = true ->
    isRVC w2 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w2) s0 = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa1 j) ↦ₘ{dq} nth_byte v1 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa2 j) ↦ₘ{dq} nth_byte v2 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vs j) ↦ₘ{dq} nth_byte w2 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int vs 2 -∗
        gpr_file (<[gpr_of_Z 3 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v2))]>
                  (<[gpr_of_Z 1 := regval_into_reg (extend_value false data1)]> m)) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int vs 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa1 j) ↦ₘ{dq} nth_byte v1 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa2 j) ↦ₘ{dq} nth_byte v2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w1 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add vs j) ↦ₘ{dq} nth_byte w2 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros off1 a81 pa1 off2 a82 pa2 data1 vs
      HN Hsp Hra Hgp HSXL Hmode Hasid Hvec5 Hvecld Hmask Hpmm
      HA0 Hord0 HX0 HR0 HmisaC HmisaS HMPRV HMXR Hb1 Hmie_mdl HSIE Help
      Hcanonf1 Hvpndeff1 Hidentf1 Hbit01 Hbit11 Halign41 Hcanon1 Hvpndef1 Hident1
      Hmatchf1 Hexecf1 Hmatch1 Hread1 Hrange0f1 Hrange01 Halignf1 Halign81 Hpalign81 HisRVC1 Hdec1
      Hcanonf2 Hvpndeff2 Hidentf2 Hbit02 Hbit12 Halign42 Hcanon2 Hvpndef2 Hident2
      Hmatchf2 Hexecf2 Hmatch2 Hread2 Hrange0f2 Hrange02 Halignf2 Halign82 Hpalign82 HisRVC2 Hdec2.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hb2c Hib1 Hib2 Hcont".
    (* ---- load 1: ld ra, 0(sp) @va ---- *)
    iApply (wp_kv_load_4 va w1 (mword_of_int 0) (mword_of_int 1) svpn m vsp vd1
              misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v1 npc0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l1 region_f1 E Phi
              HN ltac:(vm_compute; discriminate) Hsp Hra HSXL Hmode Hasid Hvec5 Hvecld
              Hcanonf1 Hvpndeff1 Hidentf1 Hbit01 Hbit11 Halign41 Hcanon1 Hvpndef1 Hident1 Hmask
              Hmatchf1 Hexecf1 Hmatch1 Hread1 Hpmm HA0 Hord0 Hrange0f1 Hrange01 HX0 HR0 Halignf1 Halign81 Hpalign81
              HisRVC1 HmisaC HmisaS HMPRV HMXR Hdec1 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hib1").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hib1".
    (* PC now = va+2 = vs ; gpr_file = <[ra := val1]> m *)
    (* ---- load 2: ld gp, 16(sp) @vs ---- *)
    iApply (wp_kv_load_2 vs w2 (mword_of_int 2) (mword_of_int 3) svpn
              (<[gpr_of_Z 1 := regval_into_reg (extend_value false data1)]> m) vsp vd2
              misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v2 (add_vec_int va 2) mc mcfg
              pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l2 region_f2 E Phi
              HN ltac:(vm_compute; discriminate)
              ltac:(rewrite lookup_insert_ne; [exact Hsp | vm_compute; discriminate])
              ltac:(rewrite lookup_insert_ne; [exact Hgp | vm_compute; discriminate])
              HSXL Hmode Hasid Hvec5 Hvecld
              Hcanonf2 Hvpndeff2 Hidentf2 Hbit02 Hbit12 Halign42 Hcanon2 Hvpndef2 Hident2 Hmask
              Hmatchf2 Hexecf2 Hmatch2 Hread2 Hpmm HA0 Hord0 Hrange0f2 Hrange02 HX0 HR0 Halignf2 Halign82 Hpalign82
              HisRVC2 HmisaC HmisaS HMPRV HMXR Hdec2 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb2c Hib2").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb2c Hib2".
    iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hb2c Hib1 Hib2").
  Qed.

  Lemma wp_kv_loads_all (va : mword 64) (w0 : mword 32) (w1 : mword 16) (w2 : mword 32) (w3 : mword 16) (w4 : mword 32) (w5 : mword 16) (w6 : mword 32) (w7 : mword 16) (w8 : mword 32) (w9 : mword 16) (w10 : mword 32) (w11 : mword 16) (w12 : mword 32) (w13 : mword 16) (w14 : mword 32) (w15 : mword 16) (w16 : mword 32) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vd0 vd1 vd2 vd3 vd4 vd5 vd6 vd7 vd8 vd9 vd10 vd11 vd12 vd13 vd14 vd15 vd16 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : bv 64) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_l0 region_l1 region_l2 region_l3 region_l4 region_l5 region_l6 region_l7 region_l8 region_l9 region_l10 region_l11 region_l12 region_l13 region_l14 region_l15 region_l16 region_f0 region_f1 region_f2 region_f3 region_f4 region_f5 region_f6 region_f7 region_f8 region_f9 region_f10 region_f11 region_f12 region_f13 region_f14 region_f15 region_f16 : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let off0 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a80 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off0) (xlen - 0 - 1) 0) in
    let pa0 := zero_extend' 64 (add_vec_int a80 (0 * 8)) in
    let data0 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v0 in
    let off1 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a81 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off1) (xlen - 0 - 1) 0) in
    let pa1 := zero_extend' 64 (add_vec_int a81 (0 * 8)) in
    let data1 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v1 in
    let off2 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) in
    let a82 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off2) (xlen - 0 - 1) 0) in
    let pa2 := zero_extend' 64 (add_vec_int a82 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v2 in
    let off3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) in
    let a83 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off3) (xlen - 0 - 1) 0) in
    let pa3 := zero_extend' 64 (add_vec_int a83 (0 * 8)) in
    let data3 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v3 in
    let off4 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) in
    let a84 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off4) (xlen - 0 - 1) 0) in
    let pa4 := zero_extend' 64 (add_vec_int a84 (0 * 8)) in
    let data4 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v4 in
    let off5 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) in
    let a85 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off5) (xlen - 0 - 1) 0) in
    let pa5 := zero_extend' 64 (add_vec_int a85 (0 * 8)) in
    let data5 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v5 in
    let off6 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) in
    let a86 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off6) (xlen - 0 - 1) 0) in
    let pa6 := zero_extend' 64 (add_vec_int a86 (0 * 8)) in
    let data6 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v6 in
    let off7 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) in
    let a87 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off7) (xlen - 0 - 1) 0) in
    let pa7 := zero_extend' 64 (add_vec_int a87 (0 * 8)) in
    let data7 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v7 in
    let off8 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) in
    let a88 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off8) (xlen - 0 - 1) 0) in
    let pa8 := zero_extend' 64 (add_vec_int a88 (0 * 8)) in
    let data8 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v8 in
    let off9 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) in
    let a89 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off9) (xlen - 0 - 1) 0) in
    let pa9 := zero_extend' 64 (add_vec_int a89 (0 * 8)) in
    let data9 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v9 in
    let off10 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) in
    let a810 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off10) (xlen - 0 - 1) 0) in
    let pa10 := zero_extend' 64 (add_vec_int a810 (0 * 8)) in
    let data10 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v10 in
    let off11 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) in
    let a811 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off11) (xlen - 0 - 1) 0) in
    let pa11 := zero_extend' 64 (add_vec_int a811 (0 * 8)) in
    let data11 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v11 in
    let off12 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) in
    let a812 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off12) (xlen - 0 - 1) 0) in
    let pa12 := zero_extend' 64 (add_vec_int a812 (0 * 8)) in
    let data12 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v12 in
    let off13 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) in
    let a813 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off13) (xlen - 0 - 1) 0) in
    let pa13 := zero_extend' 64 (add_vec_int a813 (0 * 8)) in
    let data13 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v13 in
    let off14 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) in
    let a814 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off14) (xlen - 0 - 1) 0) in
    let pa14 := zero_extend' 64 (add_vec_int a814 (0 * 8)) in
    let data14 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v14 in
    let off15 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) in
    let a815 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off15) (xlen - 0 - 1) 0) in
    let pa15 := zero_extend' 64 (add_vec_int a815 (0 * 8)) in
    let data15 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v15 in
    let off16 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) in
    let a816 := sign_extend' 64 (subrange_vec_dec (add_vec vsp off16) (xlen - 0 - 1) 0) in
    let pa16 := zero_extend' 64 (add_vec_int a816 (0 * 8)) in
    let data16 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v16 in
    let va1 := add_vec_int va 2 in
    let va2 := add_vec_int va1 2 in
    let va3 := add_vec_int va2 2 in
    let va4 := add_vec_int va3 2 in
    let va5 := add_vec_int va4 2 in
    let va6 := add_vec_int va5 2 in
    let va7 := add_vec_int va6 2 in
    let va8 := add_vec_int va7 2 in
    let va9 := add_vec_int va8 2 in
    let va10 := add_vec_int va9 2 in
    let va11 := add_vec_int va10 2 in
    let va12 := add_vec_int va11 2 in
    let va13 := add_vec_int va12 2 in
    let va14 := add_vec_int va13 2 in
    let va15 := add_vec_int va14 2 in
    let va16 := add_vec_int va15 2 in
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vd0 ->
    m !! gpr_of_Z 3 = Some vd1 ->
    m !! gpr_of_Z 5 = Some vd2 ->
    m !! gpr_of_Z 6 = Some vd3 ->
    m !! gpr_of_Z 7 = Some vd4 ->
    m !! gpr_of_Z 10 = Some vd5 ->
    m !! gpr_of_Z 11 = Some vd6 ->
    m !! gpr_of_Z 12 = Some vd7 ->
    m !! gpr_of_Z 13 = Some vd8 ->
    m !! gpr_of_Z 14 = Some vd9 ->
    m !! gpr_of_Z 15 = Some vd10 ->
    m !! gpr_of_Z 16 = Some vd11 ->
    m !! gpr_of_Z 17 = Some vd12 ->
    m !! gpr_of_Z 28 = Some vd13 ->
    m !! gpr_of_Z 29 = Some vd14 ->
    m !! gpr_of_Z 30 = Some vd15 ->
    m !! gpr_of_Z 31 = Some vd16 ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    neq_vec (bits_of_virtaddr (Virtaddr va)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a80)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a80)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a80)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a80)) (Z.sub pagesize_bits 1) 0)) = a80 ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f0 ->
    (override_PMA (PMA_Region_attributes region_f0) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa0) 8 = Some region_l0 ->
    (override_PMA (PMA_Region_attributes region_l0) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa0) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    is_aligned_vaddr (Virtaddr a80) 8 = true ->
    is_aligned_paddr (Physaddr pa0) 8 = true ->
    isRVC (subrange_vec_dec w0 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w0 15 0)) s0 = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va1)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va1)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va1)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va1)) (Z.sub pagesize_bits 1) 0)) = va1 ->
    neq_vec (access_vec_dec va1 0) ('b"0") = false ->
    neq_vec (access_vec_dec va1 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va1) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a81)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a81)) (Z.sub pagesize_bits 1) 0)) = a81 ->
    matching_pma_region pmar0 (Physaddr va1) 2 = Some region_f1 ->
    (override_PMA (PMA_Region_attributes region_f1) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa1) 8 = Some region_l1 ->
    (override_PMA (PMA_Region_attributes region_l1) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va1) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa1) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va1) 2 = true ->
    is_aligned_vaddr (Virtaddr a81) 8 = true ->
    is_aligned_paddr (Physaddr pa1) 8 = true ->
    isRVC w1 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w1) s0 = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va2)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va2)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va2)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va2)) (Z.sub pagesize_bits 1) 0)) = va2 ->
    neq_vec (access_vec_dec va2 0) ('b"0") = false ->
    neq_vec (access_vec_dec va2 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va2) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a82)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a82)) (Z.sub pagesize_bits 1) 0)) = a82 ->
    matching_pma_region pmar0 (Physaddr va2) 4 = Some region_f2 ->
    (override_PMA (PMA_Region_attributes region_f2) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa2) 8 = Some region_l2 ->
    (override_PMA (PMA_Region_attributes region_l2) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va2) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa2) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va2) 4 = true ->
    is_aligned_vaddr (Virtaddr a82) 8 = true ->
    is_aligned_paddr (Physaddr pa2) 8 = true ->
    isRVC (subrange_vec_dec w2 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w2 15 0)) s0 = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va3)) (Z.sub pagesize_bits 1) 0)) = va3 ->
    neq_vec (access_vec_dec va3 0) ('b"0") = false ->
    neq_vec (access_vec_dec va3 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va3) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a83)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a83)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a83)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a83)) (Z.sub pagesize_bits 1) 0)) = a83 ->
    matching_pma_region pmar0 (Physaddr va3) 2 = Some region_f3 ->
    (override_PMA (PMA_Region_attributes region_f3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa3) 8 = Some region_l3 ->
    (override_PMA (PMA_Region_attributes region_l3) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va3) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va3) 2 = true ->
    is_aligned_vaddr (Virtaddr a83) 8 = true ->
    is_aligned_paddr (Physaddr pa3) 8 = true ->
    isRVC w3 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w3) s0 = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 6)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va4)) (Z.sub pagesize_bits 1) 0)) = va4 ->
    neq_vec (access_vec_dec va4 0) ('b"0") = false ->
    neq_vec (access_vec_dec va4 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va4) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a84)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a84)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a84)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a84)) (Z.sub pagesize_bits 1) 0)) = a84 ->
    matching_pma_region pmar0 (Physaddr va4) 4 = Some region_f4 ->
    (override_PMA (PMA_Region_attributes region_f4) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa4) 8 = Some region_l4 ->
    (override_PMA (PMA_Region_attributes region_l4) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va4) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va4) 4 = true ->
    is_aligned_vaddr (Virtaddr a84) 8 = true ->
    is_aligned_paddr (Physaddr pa4) 8 = true ->
    isRVC (subrange_vec_dec w4 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w4 15 0)) s0 = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 7)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va5)) (Z.sub pagesize_bits 1) 0)) = va5 ->
    neq_vec (access_vec_dec va5 0) ('b"0") = false ->
    neq_vec (access_vec_dec va5 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va5) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a85)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a85)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a85)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a85)) (Z.sub pagesize_bits 1) 0)) = a85 ->
    matching_pma_region pmar0 (Physaddr va5) 2 = Some region_f5 ->
    (override_PMA (PMA_Region_attributes region_f5) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa5) 8 = Some region_l5 ->
    (override_PMA (PMA_Region_attributes region_l5) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va5) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa5) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va5) 2 = true ->
    is_aligned_vaddr (Virtaddr a85) 8 = true ->
    is_aligned_paddr (Physaddr pa5) 8 = true ->
    isRVC w5 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w5) s0 = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 10)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va6)) (Z.sub pagesize_bits 1) 0)) = va6 ->
    neq_vec (access_vec_dec va6 0) ('b"0") = false ->
    neq_vec (access_vec_dec va6 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va6) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a86)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a86)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a86)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a86)) (Z.sub pagesize_bits 1) 0)) = a86 ->
    matching_pma_region pmar0 (Physaddr va6) 4 = Some region_f6 ->
    (override_PMA (PMA_Region_attributes region_f6) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa6) 8 = Some region_l6 ->
    (override_PMA (PMA_Region_attributes region_l6) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va6) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa6) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va6) 4 = true ->
    is_aligned_vaddr (Virtaddr a86) 8 = true ->
    is_aligned_paddr (Physaddr pa6) 8 = true ->
    isRVC (subrange_vec_dec w6 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w6 15 0)) s0 = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 11)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va7)) (Z.sub pagesize_bits 1) 0)) = va7 ->
    neq_vec (access_vec_dec va7 0) ('b"0") = false ->
    neq_vec (access_vec_dec va7 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va7) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a87)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a87)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a87)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a87)) (Z.sub pagesize_bits 1) 0)) = a87 ->
    matching_pma_region pmar0 (Physaddr va7) 2 = Some region_f7 ->
    (override_PMA (PMA_Region_attributes region_f7) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa7) 8 = Some region_l7 ->
    (override_PMA (PMA_Region_attributes region_l7) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va7) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa7) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va7) 2 = true ->
    is_aligned_vaddr (Virtaddr a87) 8 = true ->
    is_aligned_paddr (Physaddr pa7) 8 = true ->
    isRVC w7 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w7) s0 = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 12)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va8)) (Z.sub pagesize_bits 1) 0)) = va8 ->
    neq_vec (access_vec_dec va8 0) ('b"0") = false ->
    neq_vec (access_vec_dec va8 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va8) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a88)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a88)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a88)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a88)) (Z.sub pagesize_bits 1) 0)) = a88 ->
    matching_pma_region pmar0 (Physaddr va8) 4 = Some region_f8 ->
    (override_PMA (PMA_Region_attributes region_f8) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa8) 8 = Some region_l8 ->
    (override_PMA (PMA_Region_attributes region_l8) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va8) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa8) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va8) 4 = true ->
    is_aligned_vaddr (Virtaddr a88) 8 = true ->
    is_aligned_paddr (Physaddr pa8) 8 = true ->
    isRVC (subrange_vec_dec w8 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w8 15 0)) s0 = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 13)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va9)) (Z.sub pagesize_bits 1) 0)) = va9 ->
    neq_vec (access_vec_dec va9 0) ('b"0") = false ->
    neq_vec (access_vec_dec va9 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va9) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a89)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a89)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a89)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a89)) (Z.sub pagesize_bits 1) 0)) = a89 ->
    matching_pma_region pmar0 (Physaddr va9) 2 = Some region_f9 ->
    (override_PMA (PMA_Region_attributes region_f9) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa9) 8 = Some region_l9 ->
    (override_PMA (PMA_Region_attributes region_l9) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va9) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa9) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va9) 2 = true ->
    is_aligned_vaddr (Virtaddr a89) 8 = true ->
    is_aligned_paddr (Physaddr pa9) 8 = true ->
    isRVC w9 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w9) s0 = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 14)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va10)) (Z.sub pagesize_bits 1) 0)) = va10 ->
    neq_vec (access_vec_dec va10 0) ('b"0") = false ->
    neq_vec (access_vec_dec va10 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va10) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a810)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a810)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a810)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a810)) (Z.sub pagesize_bits 1) 0)) = a810 ->
    matching_pma_region pmar0 (Physaddr va10) 4 = Some region_f10 ->
    (override_PMA (PMA_Region_attributes region_f10) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa10) 8 = Some region_l10 ->
    (override_PMA (PMA_Region_attributes region_l10) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va10) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa10) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va10) 4 = true ->
    is_aligned_vaddr (Virtaddr a810) 8 = true ->
    is_aligned_paddr (Physaddr pa10) 8 = true ->
    isRVC (subrange_vec_dec w10 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w10 15 0)) s0 = Some (C_LDSP (mword_of_int 14, Regidx (mword_of_int 15)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va11)) (Z.sub pagesize_bits 1) 0)) = va11 ->
    neq_vec (access_vec_dec va11 0) ('b"0") = false ->
    neq_vec (access_vec_dec va11 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va11) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a811)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a811)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a811)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a811)) (Z.sub pagesize_bits 1) 0)) = a811 ->
    matching_pma_region pmar0 (Physaddr va11) 2 = Some region_f11 ->
    (override_PMA (PMA_Region_attributes region_f11) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa11) 8 = Some region_l11 ->
    (override_PMA (PMA_Region_attributes region_l11) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va11) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa11) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va11) 2 = true ->
    is_aligned_vaddr (Virtaddr a811) 8 = true ->
    is_aligned_paddr (Physaddr pa11) 8 = true ->
    isRVC w11 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w11) s0 = Some (C_LDSP (mword_of_int 15, Regidx (mword_of_int 16)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va12)) (Z.sub pagesize_bits 1) 0)) = va12 ->
    neq_vec (access_vec_dec va12 0) ('b"0") = false ->
    neq_vec (access_vec_dec va12 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va12) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a812)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a812)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a812)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a812)) (Z.sub pagesize_bits 1) 0)) = a812 ->
    matching_pma_region pmar0 (Physaddr va12) 4 = Some region_f12 ->
    (override_PMA (PMA_Region_attributes region_f12) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa12) 8 = Some region_l12 ->
    (override_PMA (PMA_Region_attributes region_l12) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va12) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa12) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va12) 4 = true ->
    is_aligned_vaddr (Virtaddr a812) 8 = true ->
    is_aligned_paddr (Physaddr pa12) 8 = true ->
    isRVC (subrange_vec_dec w12 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w12 15 0)) s0 = Some (C_LDSP (mword_of_int 16, Regidx (mword_of_int 17)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va13)) (Z.sub pagesize_bits 1) 0)) = va13 ->
    neq_vec (access_vec_dec va13 0) ('b"0") = false ->
    neq_vec (access_vec_dec va13 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va13) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a813)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a813)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a813)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a813)) (Z.sub pagesize_bits 1) 0)) = a813 ->
    matching_pma_region pmar0 (Physaddr va13) 2 = Some region_f13 ->
    (override_PMA (PMA_Region_attributes region_f13) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa13) 8 = Some region_l13 ->
    (override_PMA (PMA_Region_attributes region_l13) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va13) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa13) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va13) 2 = true ->
    is_aligned_vaddr (Virtaddr a813) 8 = true ->
    is_aligned_paddr (Physaddr pa13) 8 = true ->
    isRVC w13 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w13) s0 = Some (C_LDSP (mword_of_int 27, Regidx (mword_of_int 28)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va14)) (Z.sub pagesize_bits 1) 0)) = va14 ->
    neq_vec (access_vec_dec va14 0) ('b"0") = false ->
    neq_vec (access_vec_dec va14 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va14) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a814)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a814)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a814)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a814)) (Z.sub pagesize_bits 1) 0)) = a814 ->
    matching_pma_region pmar0 (Physaddr va14) 4 = Some region_f14 ->
    (override_PMA (PMA_Region_attributes region_f14) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa14) 8 = Some region_l14 ->
    (override_PMA (PMA_Region_attributes region_l14) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va14) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa14) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va14) 4 = true ->
    is_aligned_vaddr (Virtaddr a814) 8 = true ->
    is_aligned_paddr (Physaddr pa14) 8 = true ->
    isRVC (subrange_vec_dec w14 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w14 15 0)) s0 = Some (C_LDSP (mword_of_int 28, Regidx (mword_of_int 29)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va15)) (Z.sub pagesize_bits 1) 0)) = va15 ->
    neq_vec (access_vec_dec va15 0) ('b"0") = false ->
    neq_vec (access_vec_dec va15 1) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr va15) 4 = false ->
    neq_vec (bits_of_virtaddr (Virtaddr a815)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a815)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a815)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a815)) (Z.sub pagesize_bits 1) 0)) = a815 ->
    matching_pma_region pmar0 (Physaddr va15) 2 = Some region_f15 ->
    (override_PMA (PMA_Region_attributes region_f15) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa15) 8 = Some region_l15 ->
    (override_PMA (PMA_Region_attributes region_l15) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va15) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa15) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va15) 2 = true ->
    is_aligned_vaddr (Virtaddr a815) 8 = true ->
    is_aligned_paddr (Physaddr pa15) 8 = true ->
    isRVC w15 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w15) s0 = Some (C_LDSP (mword_of_int 29, Regidx (mword_of_int 30)), s0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr va16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr va16)) (Z.sub pagesize_bits 1) 0)) = va16 ->
    neq_vec (access_vec_dec va16 0) ('b"0") = false ->
    neq_vec (access_vec_dec va16 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va16) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr a816)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a816)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a816)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a816)) (Z.sub pagesize_bits 1) 0)) = a816 ->
    matching_pma_region pmar0 (Physaddr va16) 4 = Some region_f16 ->
    (override_PMA (PMA_Region_attributes region_f16) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa16) 8 = Some region_l16 ->
    (override_PMA (PMA_Region_attributes region_l16) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint va16) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa16) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr va16) 4 = true ->
    is_aligned_vaddr (Virtaddr a816) 8 = true ->
    is_aligned_paddr (Physaddr pa16) 8 = true ->
    isRVC (subrange_vec_dec w16 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w16 15 0)) s0 = Some (C_LDSP (mword_of_int 30, Regidx (mword_of_int 31)), s0)) ->
    minstret_inv -∗
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa0 j) ↦ₘ{dq} nth_byte v0 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa1 j) ↦ₘ{dq} nth_byte v1 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa2 j) ↦ₘ{dq} nth_byte v2 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ{dq} nth_byte v3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ{dq} nth_byte v4 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa5 j) ↦ₘ{dq} nth_byte v5 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa6 j) ↦ₘ{dq} nth_byte v6 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa7 j) ↦ₘ{dq} nth_byte v7 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa8 j) ↦ₘ{dq} nth_byte v8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa9 j) ↦ₘ{dq} nth_byte v9 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa10 j) ↦ₘ{dq} nth_byte v10 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa11 j) ↦ₘ{dq} nth_byte v11 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa12 j) ↦ₘ{dq} nth_byte v12 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa13 j) ↦ₘ{dq} nth_byte v13 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa14 j) ↦ₘ{dq} nth_byte v14 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa15 j) ↦ₘ{dq} nth_byte v15 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa16 j) ↦ₘ{dq} nth_byte v16 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w0 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va1 j) ↦ₘ{dq} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va2 j) ↦ₘ{dq} nth_byte w2 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va3 j) ↦ₘ{dq} nth_byte w3 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va4 j) ↦ₘ{dq} nth_byte w4 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va5 j) ↦ₘ{dq} nth_byte w5 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va6 j) ↦ₘ{dq} nth_byte w6 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va7 j) ↦ₘ{dq} nth_byte w7 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va8 j) ↦ₘ{dq} nth_byte w8 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va9 j) ↦ₘ{dq} nth_byte w9 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va10 j) ↦ₘ{dq} nth_byte w10 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va11 j) ↦ₘ{dq} nth_byte w11 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va12 j) ↦ₘ{dq} nth_byte w12 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va13 j) ↦ₘ{dq} nth_byte w13 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va14 j) ↦ₘ{dq} nth_byte w14 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va15 j) ↦ₘ{dq} nth_byte w15 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va16 j) ↦ₘ{dq} nth_byte w16 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va16 2 -∗
        gpr_file (<[gpr_of_Z 31 := regval_into_reg (extend_value false data16)]> (<[gpr_of_Z 30 := regval_into_reg (extend_value false data15)]> (<[gpr_of_Z 29 := regval_into_reg (extend_value false data14)]> (<[gpr_of_Z 28 := regval_into_reg (extend_value false data13)]> (<[gpr_of_Z 17 := regval_into_reg (extend_value false data12)]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))))))))))))) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va16 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa0 j) ↦ₘ{dq} nth_byte v0 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa1 j) ↦ₘ{dq} nth_byte v1 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa2 j) ↦ₘ{dq} nth_byte v2 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ{dq} nth_byte v3 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ{dq} nth_byte v4 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa5 j) ↦ₘ{dq} nth_byte v5 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa6 j) ↦ₘ{dq} nth_byte v6 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa7 j) ↦ₘ{dq} nth_byte v7 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa8 j) ↦ₘ{dq} nth_byte v8 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa9 j) ↦ₘ{dq} nth_byte v9 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa10 j) ↦ₘ{dq} nth_byte v10 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa11 j) ↦ₘ{dq} nth_byte v11 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa12 j) ↦ₘ{dq} nth_byte v12 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa13 j) ↦ₘ{dq} nth_byte v13 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa14 j) ↦ₘ{dq} nth_byte v14 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa15 j) ↦ₘ{dq} nth_byte v15 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa16 j) ↦ₘ{dq} nth_byte v16 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w0 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va1 j) ↦ₘ{dq} nth_byte w1 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va2 j) ↦ₘ{dq} nth_byte w2 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va3 j) ↦ₘ{dq} nth_byte w3 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va4 j) ↦ₘ{dq} nth_byte w4 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va5 j) ↦ₘ{dq} nth_byte w5 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va6 j) ↦ₘ{dq} nth_byte w6 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va7 j) ↦ₘ{dq} nth_byte w7 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va8 j) ↦ₘ{dq} nth_byte w8 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va9 j) ↦ₘ{dq} nth_byte w9 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va10 j) ↦ₘ{dq} nth_byte w10 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va11 j) ↦ₘ{dq} nth_byte w11 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va12 j) ↦ₘ{dq} nth_byte w12 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va13 j) ↦ₘ{dq} nth_byte w13 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va14 j) ↦ₘ{dq} nth_byte w14 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va15 j) ↦ₘ{dq} nth_byte w15 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va16 j) ↦ₘ{dq} nth_byte w16 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros off0 a80 pa0 data0 off1 a81 pa1 data1 off2 a82 pa2 data2 off3 a83 pa3 data3 off4 a84 pa4 data4 off5 a85 pa5 data5 off6 a86 pa6 data6 off7 a87 pa7 data7 off8 a88 pa8 data8 off9 a89 pa9 data9 off10 a810 pa10 data10 off11 a811 pa11 data11 off12 a812 pa12 data12 off13 a813 pa13 data13 off14 a814 pa14 data14 off15 a815 pa15 data15 off16 a816 pa16 data16 va1 va2 va3 va4 va5 va6 va7 va8 va9 va10 va11 va12 va13 va14 va15 va16 HN Hsp Hvd0 Hvd1 Hvd2 Hvd3 Hvd4 Hvd5 Hvd6 Hvd7 Hvd8 Hvd9 Hvd10 Hvd11 Hvd12 Hvd13 Hvd14 Hvd15 Hvd16 HSXL Hmode Hasid Hvec5 Hvecld Hmask Hpmm HA0 Hord0 HX0 HR0 HmisaC HmisaS HMPRV HMXR Hb1 Hmie_mdl HSIE Help Hcanonf0 Hvpndeff0 Hidentf0 Hbit00 Hbit10 Halign40 Hcanon0 Hvpndef0 Hident0 Hmatchf0 Hexecf0 Hmatch0 Hread0 Hrange0f0 Hrange00 Halignf0 Halign80 Hpalign80 HisRVC0 Hdec0 Hcanonf1 Hvpndeff1 Hidentf1 Hbit01 Hbit11 Halign41 Hcanon1 Hvpndef1 Hident1 Hmatchf1 Hexecf1 Hmatch1 Hread1 Hrange0f1 Hrange01 Halignf1 Halign81 Hpalign81 HisRVC1 Hdec1 Hcanonf2 Hvpndeff2 Hidentf2 Hbit02 Hbit12 Halign42 Hcanon2 Hvpndef2 Hident2 Hmatchf2 Hexecf2 Hmatch2 Hread2 Hrange0f2 Hrange02 Halignf2 Halign82 Hpalign82 HisRVC2 Hdec2 Hcanonf3 Hvpndeff3 Hidentf3 Hbit03 Hbit13 Halign43 Hcanon3 Hvpndef3 Hident3 Hmatchf3 Hexecf3 Hmatch3 Hread3 Hrange0f3 Hrange03 Halignf3 Halign83 Hpalign83 HisRVC3 Hdec3 Hcanonf4 Hvpndeff4 Hidentf4 Hbit04 Hbit14 Halign44 Hcanon4 Hvpndef4 Hident4 Hmatchf4 Hexecf4 Hmatch4 Hread4 Hrange0f4 Hrange04 Halignf4 Halign84 Hpalign84 HisRVC4 Hdec4 Hcanonf5 Hvpndeff5 Hidentf5 Hbit05 Hbit15 Halign45 Hcanon5 Hvpndef5 Hident5 Hmatchf5 Hexecf5 Hmatch5 Hread5 Hrange0f5 Hrange05 Halignf5 Halign85 Hpalign85 HisRVC5 Hdec5 Hcanonf6 Hvpndeff6 Hidentf6 Hbit06 Hbit16 Halign46 Hcanon6 Hvpndef6 Hident6 Hmatchf6 Hexecf6 Hmatch6 Hread6 Hrange0f6 Hrange06 Halignf6 Halign86 Hpalign86 HisRVC6 Hdec6 Hcanonf7 Hvpndeff7 Hidentf7 Hbit07 Hbit17 Halign47 Hcanon7 Hvpndef7 Hident7 Hmatchf7 Hexecf7 Hmatch7 Hread7 Hrange0f7 Hrange07 Halignf7 Halign87 Hpalign87 HisRVC7 Hdec7 Hcanonf8 Hvpndeff8 Hidentf8 Hbit08 Hbit18 Halign48 Hcanon8 Hvpndef8 Hident8 Hmatchf8 Hexecf8 Hmatch8 Hread8 Hrange0f8 Hrange08 Halignf8 Halign88 Hpalign88 HisRVC8 Hdec8 Hcanonf9 Hvpndeff9 Hidentf9 Hbit09 Hbit19 Halign49 Hcanon9 Hvpndef9 Hident9 Hmatchf9 Hexecf9 Hmatch9 Hread9 Hrange0f9 Hrange09 Halignf9 Halign89 Hpalign89 HisRVC9 Hdec9 Hcanonf10 Hvpndeff10 Hidentf10 Hbit010 Hbit110 Halign410 Hcanon10 Hvpndef10 Hident10 Hmatchf10 Hexecf10 Hmatch10 Hread10 Hrange0f10 Hrange010 Halignf10 Halign810 Hpalign810 HisRVC10 Hdec10 Hcanonf11 Hvpndeff11 Hidentf11 Hbit011 Hbit111 Halign411 Hcanon11 Hvpndef11 Hident11 Hmatchf11 Hexecf11 Hmatch11 Hread11 Hrange0f11 Hrange011 Halignf11 Halign811 Hpalign811 HisRVC11 Hdec11 Hcanonf12 Hvpndeff12 Hidentf12 Hbit012 Hbit112 Halign412 Hcanon12 Hvpndef12 Hident12 Hmatchf12 Hexecf12 Hmatch12 Hread12 Hrange0f12 Hrange012 Halignf12 Halign812 Hpalign812 HisRVC12 Hdec12 Hcanonf13 Hvpndeff13 Hidentf13 Hbit013 Hbit113 Halign413 Hcanon13 Hvpndef13 Hident13 Hmatchf13 Hexecf13 Hmatch13 Hread13 Hrange0f13 Hrange013 Halignf13 Halign813 Hpalign813 HisRVC13 Hdec13 Hcanonf14 Hvpndeff14 Hidentf14 Hbit014 Hbit114 Halign414 Hcanon14 Hvpndef14 Hident14 Hmatchf14 Hexecf14 Hmatch14 Hread14 Hrange0f14 Hrange014 Halignf14 Halign814 Hpalign814 HisRVC14 Hdec14 Hcanonf15 Hvpndeff15 Hidentf15 Hbit015 Hbit115 Halign415 Hcanon15 Hvpndef15 Hident15 Hmatchf15 Hexecf15 Hmatch15 Hread15 Hrange0f15 Hrange015 Halignf15 Halign815 Hpalign815 HisRVC15 Hdec15 Hcanonf16 Hvpndeff16 Hidentf16 Hbit016 Hbit116 Halign416 Hcanon16 Hvpndef16 Hident16 Hmatchf16 Hexecf16 Hmatch16 Hread16 Hrange0f16 Hrange016 Halignf16 Halign816 Hpalign816 HisRVC16 Hdec16.
    iIntros "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb0c Hb1c Hb2c Hb3c Hb4c Hb5c Hb6c Hb7c Hb8c Hb9c Hb10c Hb11c Hb12c Hb13c Hb14c Hb15c Hb16c Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16 Hcont".
    iApply (wp_kv_load_4 va w0 (mword_of_int 0) (mword_of_int 1) svpn m vsp vd0 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v0 npc0 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l0 region_f0 E Phi
              HN ltac:(vm_compute; discriminate) Hsp Hvd0 HSXL Hmode Hasid Hvec5 Hvecld Hcanonf0 Hvpndeff0 Hidentf0 Hbit00 Hbit10 Halign40 Hcanon0 Hvpndef0 Hident0 Hmask Hmatchf0 Hexecf0 Hmatch0 Hread0 Hpmm HA0 Hord0 Hrange0f0 Hrange00 HX0 HR0 Halignf0 Halign80 Hpalign80 HisRVC0 HmisaC HmisaS HMPRV HMXR Hdec0 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb0c Hib0").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb0c Hib0".
    iApply (wp_kv_load_2 va1 w1 (mword_of_int 2) (mword_of_int 3) svpn (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m) vsp vd1 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v1 va1 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l1 region_f1 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd1) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf1 Hvpndeff1 Hidentf1 Hbit01 Hbit11 Halign41 Hcanon1 Hvpndef1 Hident1 Hmask Hmatchf1 Hexecf1 Hmatch1 Hread1 Hpmm HA0 Hord0 Hrange0f1 Hrange01 HX0 HR0 Halignf1 Halign81 Hpalign81 HisRVC1 HmisaC HmisaS HMPRV HMXR Hdec1 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hib1").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb1c Hib1".
    iApply (wp_kv_load_4 va2 w2 (mword_of_int 4) (mword_of_int 5) svpn (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)) vsp vd2 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v2 va2 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l2 region_f2 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd2) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf2 Hvpndeff2 Hidentf2 Hbit02 Hbit12 Halign42 Hcanon2 Hvpndef2 Hident2 Hmask Hmatchf2 Hexecf2 Hmatch2 Hread2 Hpmm HA0 Hord0 Hrange0f2 Hrange02 HX0 HR0 Halignf2 Halign82 Hpalign82 HisRVC2 HmisaC HmisaS HMPRV HMXR Hdec2 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb2c Hib2").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb2c Hib2".
    iApply (wp_kv_load_2 va3 w3 (mword_of_int 5) (mword_of_int 6) svpn (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))) vsp vd3 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v3 va3 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l3 region_f3 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd3) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf3 Hvpndeff3 Hidentf3 Hbit03 Hbit13 Halign43 Hcanon3 Hvpndef3 Hident3 Hmask Hmatchf3 Hexecf3 Hmatch3 Hread3 Hpmm HA0 Hord0 Hrange0f3 Hrange03 HX0 HR0 Halignf3 Halign83 Hpalign83 HisRVC3 HmisaC HmisaS HMPRV HMXR Hdec3 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb3c Hib3").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb3c Hib3".
    iApply (wp_kv_load_4 va4 w4 (mword_of_int 6) (mword_of_int 7) svpn (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))) vsp vd4 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v4 va4 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l4 region_f4 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd4) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf4 Hvpndeff4 Hidentf4 Hbit04 Hbit14 Halign44 Hcanon4 Hvpndef4 Hident4 Hmask Hmatchf4 Hexecf4 Hmatch4 Hread4 Hpmm HA0 Hord0 Hrange0f4 Hrange04 HX0 HR0 Halignf4 Halign84 Hpalign84 HisRVC4 HmisaC HmisaS HMPRV HMXR Hdec4 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb4c Hib4").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb4c Hib4".
    iApply (wp_kv_load_2 va5 w5 (mword_of_int 9) (mword_of_int 10) svpn (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))) vsp vd5 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v5 va5 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l5 region_f5 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd5) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf5 Hvpndeff5 Hidentf5 Hbit05 Hbit15 Halign45 Hcanon5 Hvpndef5 Hident5 Hmask Hmatchf5 Hexecf5 Hmatch5 Hread5 Hpmm HA0 Hord0 Hrange0f5 Hrange05 HX0 HR0 Halignf5 Halign85 Hpalign85 HisRVC5 HmisaC HmisaS HMPRV HMXR Hdec5 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb5c Hib5").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb5c Hib5".
    iApply (wp_kv_load_4 va6 w6 (mword_of_int 10) (mword_of_int 11) svpn (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))) vsp vd6 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v6 va6 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l6 region_f6 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd6) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf6 Hvpndeff6 Hidentf6 Hbit06 Hbit16 Halign46 Hcanon6 Hvpndef6 Hident6 Hmask Hmatchf6 Hexecf6 Hmatch6 Hread6 Hpmm HA0 Hord0 Hrange0f6 Hrange06 HX0 HR0 Halignf6 Halign86 Hpalign86 HisRVC6 HmisaC HmisaS HMPRV HMXR Hdec6 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb6c Hib6").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb6c Hib6".
    iApply (wp_kv_load_2 va7 w7 (mword_of_int 11) (mword_of_int 12) svpn (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))) vsp vd7 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v7 va7 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l7 region_f7 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd7) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf7 Hvpndeff7 Hidentf7 Hbit07 Hbit17 Halign47 Hcanon7 Hvpndef7 Hident7 Hmask Hmatchf7 Hexecf7 Hmatch7 Hread7 Hpmm HA0 Hord0 Hrange0f7 Hrange07 HX0 HR0 Halignf7 Halign87 Hpalign87 HisRVC7 HmisaC HmisaS HMPRV HMXR Hdec7 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb7c Hib7").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb7c Hib7".
    iApply (wp_kv_load_4 va8 w8 (mword_of_int 12) (mword_of_int 13) svpn (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))))) vsp vd8 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v8 va8 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l8 region_f8 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd8) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf8 Hvpndeff8 Hidentf8 Hbit08 Hbit18 Halign48 Hcanon8 Hvpndef8 Hident8 Hmask Hmatchf8 Hexecf8 Hmatch8 Hread8 Hpmm HA0 Hord0 Hrange0f8 Hrange08 HX0 HR0 Halignf8 Halign88 Hpalign88 HisRVC8 HmisaC HmisaS HMPRV HMXR Hdec8 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb8c Hib8").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb8c Hib8".
    iApply (wp_kv_load_2 va9 w9 (mword_of_int 13) (mword_of_int 14) svpn (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))))) vsp vd9 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v9 va9 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l9 region_f9 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd9) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf9 Hvpndeff9 Hidentf9 Hbit09 Hbit19 Halign49 Hcanon9 Hvpndef9 Hident9 Hmask Hmatchf9 Hexecf9 Hmatch9 Hread9 Hpmm HA0 Hord0 Hrange0f9 Hrange09 HX0 HR0 Halignf9 Halign89 Hpalign89 HisRVC9 HmisaC HmisaS HMPRV HMXR Hdec9 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb9c Hib9").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb9c Hib9".
    iApply (wp_kv_load_4 va10 w10 (mword_of_int 14) (mword_of_int 15) svpn (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))))))) vsp vd10 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v10 va10 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l10 region_f10 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd10) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf10 Hvpndeff10 Hidentf10 Hbit010 Hbit110 Halign410 Hcanon10 Hvpndef10 Hident10 Hmask Hmatchf10 Hexecf10 Hmatch10 Hread10 Hpmm HA0 Hord0 Hrange0f10 Hrange010 HX0 HR0 Halignf10 Halign810 Hpalign810 HisRVC10 HmisaC HmisaS HMPRV HMXR Hdec10 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb10c Hib10").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb10c Hib10".
    iApply (wp_kv_load_2 va11 w11 (mword_of_int 15) (mword_of_int 16) svpn (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))))))) vsp vd11 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v11 va11 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l11 region_f11 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd11) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf11 Hvpndeff11 Hidentf11 Hbit011 Hbit111 Halign411 Hcanon11 Hvpndef11 Hident11 Hmask Hmatchf11 Hexecf11 Hmatch11 Hread11 Hpmm HA0 Hord0 Hrange0f11 Hrange011 HX0 HR0 Halignf11 Halign811 Hpalign811 HisRVC11 HmisaC HmisaS HMPRV HMXR Hdec11 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb11c Hib11").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb11c Hib11".
    iApply (wp_kv_load_4 va12 w12 (mword_of_int 16) (mword_of_int 17) svpn (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))))))))) vsp vd12 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v12 va12 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l12 region_f12 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd12) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf12 Hvpndeff12 Hidentf12 Hbit012 Hbit112 Halign412 Hcanon12 Hvpndef12 Hident12 Hmask Hmatchf12 Hexecf12 Hmatch12 Hread12 Hpmm HA0 Hord0 Hrange0f12 Hrange012 HX0 HR0 Halignf12 Halign812 Hpalign812 HisRVC12 HmisaC HmisaS HMPRV HMXR Hdec12 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb12c Hib12").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb12c Hib12".
    iApply (wp_kv_load_2 va13 w13 (mword_of_int 27) (mword_of_int 28) svpn (<[gpr_of_Z 17 := regval_into_reg (extend_value false data12)]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))))))))) vsp vd13 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v13 va13 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l13 region_f13 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd13) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf13 Hvpndeff13 Hidentf13 Hbit013 Hbit113 Halign413 Hcanon13 Hvpndef13 Hident13 Hmask Hmatchf13 Hexecf13 Hmatch13 Hread13 Hpmm HA0 Hord0 Hrange0f13 Hrange013 HX0 HR0 Halignf13 Halign813 Hpalign813 HisRVC13 HmisaC HmisaS HMPRV HMXR Hdec13 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb13c Hib13").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb13c Hib13".
    iApply (wp_kv_load_4 va14 w14 (mword_of_int 28) (mword_of_int 29) svpn (<[gpr_of_Z 28 := regval_into_reg (extend_value false data13)]> (<[gpr_of_Z 17 := regval_into_reg (extend_value false data12)]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))))))))))) vsp vd14 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v14 va14 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l14 region_f14 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd14) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf14 Hvpndeff14 Hidentf14 Hbit014 Hbit114 Halign414 Hcanon14 Hvpndef14 Hident14 Hmask Hmatchf14 Hexecf14 Hmatch14 Hread14 Hpmm HA0 Hord0 Hrange0f14 Hrange014 HX0 HR0 Halignf14 Halign814 Hpalign814 HisRVC14 HmisaC HmisaS HMPRV HMXR Hdec14 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb14c Hib14").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb14c Hib14".
    iApply (wp_kv_load_2 va15 w15 (mword_of_int 29) (mword_of_int 30) svpn (<[gpr_of_Z 29 := regval_into_reg (extend_value false data14)]> (<[gpr_of_Z 28 := regval_into_reg (extend_value false data13)]> (<[gpr_of_Z 17 := regval_into_reg (extend_value false data12)]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m))))))))))))))) vsp vd15 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v15 va15 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l15 region_f15 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd15) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf15 Hvpndeff15 Hidentf15 Hbit015 Hbit115 Halign415 Hcanon15 Hvpndef15 Hident15 Hmask Hmatchf15 Hexecf15 Hmatch15 Hread15 Hpmm HA0 Hord0 Hrange0f15 Hrange015 HX0 HR0 Halignf15 Halign815 Hpalign815 HisRVC15 HmisaC HmisaS HMPRV HMXR Hdec15 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb15c Hib15").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb15c Hib15".
    iApply (wp_kv_load_4 va16 w16 (mword_of_int 30) (mword_of_int 31) svpn (<[gpr_of_Z 30 := regval_into_reg (extend_value false data15)]> (<[gpr_of_Z 29 := regval_into_reg (extend_value false data14)]> (<[gpr_of_Z 28 := regval_into_reg (extend_value false data13)]> (<[gpr_of_Z 17 := regval_into_reg (extend_value false data12)]> (<[gpr_of_Z 16 := regval_into_reg (extend_value false data11)]> (<[gpr_of_Z 15 := regval_into_reg (extend_value false data10)]> (<[gpr_of_Z 14 := regval_into_reg (extend_value false data9)]> (<[gpr_of_Z 13 := regval_into_reg (extend_value false data8)]> (<[gpr_of_Z 12 := regval_into_reg (extend_value false data7)]> (<[gpr_of_Z 11 := regval_into_reg (extend_value false data6)]> (<[gpr_of_Z 10 := regval_into_reg (extend_value false data5)]> (<[gpr_of_Z 7 := regval_into_reg (extend_value false data4)]> (<[gpr_of_Z 6 := regval_into_reg (extend_value false data3)]> (<[gpr_of_Z 5 := regval_into_reg (extend_value false data2)]> (<[gpr_of_Z 3 := regval_into_reg (extend_value false data1)]> (<[gpr_of_Z 1 := regval_into_reg (extend_value false data0)]> m)))))))))))))))) vsp vd16 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 v16 va16 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec region_l16 region_f16 E Phi
              HN ltac:(vm_compute; discriminate) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hsp) ltac:(repeat (rewrite lookup_insert_ne; [|vm_compute; discriminate]); exact Hvd16) HSXL Hmode Hasid Hvec5 Hvecld Hcanonf16 Hvpndeff16 Hidentf16 Hbit016 Hbit116 Halign416 Hcanon16 Hvpndef16 Hident16 Hmask Hmatchf16 Hexecf16 Hmatch16 Hread16 Hpmm HA0 Hord0 Hrange0f16 Hrange016 HX0 HR0 Halignf16 Halign816 Hpalign816 HisRVC16 HmisaC HmisaS HMPRV HMXR Hdec16 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb16c Hib16").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb16c Hib16".
    iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hb0c Hb1c Hb2c Hb3c Hb4c Hb5c Hb6c Hb7c Hb8c Hb9c Hb10c Hb11c Hb12c Hb13c Hb14c Hb15c Hb16c Hib0 Hib1 Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16").
  Qed.


End KVLW.

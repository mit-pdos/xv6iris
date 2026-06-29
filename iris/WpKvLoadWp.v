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

End KVLW.

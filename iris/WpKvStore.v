From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvStore.v — WP for kernelvec's first c.sdsp whose store-address translation
   is a page WALK that fills the TLB (discharging the Htr hypothesis of
   wp_pagewalk_csdsp).  The post-execute state carries the tlb fill, so the
   forward engine and step folding get one extra irrelevant_register_set layer
   (tlb) relative to the state-preserving ForwardCsdsp. *)

Section KVS.
  Context `{!riscvGS Σ}.

(* forward engine: like WpStoreS2.ForwardCsdsp but the store EXECUTE fills the
   TLB (s_pc -> set_reg s_pc tlb tlbf), so sXsg's sregs differ from s_pc's. *)
Section ForwardCsdspWalk.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (pa : mword 64) (vrs2 : bv 64)
          (tlbf : vec (option TLB_Entry) (2 ^ 6)).
  Let sAl := set_reg s (R_bool minstret_increment) b.
  Let s_pc := set_reg sAl nextPC (add_vec_int pc 2).
  Let s_pc_f := set_reg s_pc tlb tlbf.
  Let sXsg := MState s_pc_f.(sregs) (write_bytes s_pc_f.(mem) pa 8 vrs2).
  Hypothesis Hfetch_at : exec (fetch tt) sAl = Some (F_RVC w16, sAl).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (cinstr, s0).
  Hypothesis Hcexec1 : exec (execute cinstr) s_pc = Some (ExecuteAs base, s_pc).
  Hypothesis Hcexec2 : exec (execute base) s_pc = Some (RETIRE_SUCCESS, sXsg).

  Definition sTsg_w : mstate := set_reg sXsg PC (register_lookup nextPC sXsg.(sregs)).
  Definition sFsg_w : mstate :=
    if b then set_reg sTsg_w minstret (add_vec_int (register_lookup minstret sTsg_w.(sregs)) 1)
         else sTsg_w.

  Lemma forward_exec_csdsp_super_walk :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (dispatchInterrupt Supervisor) sAl = Some (None, sAl) ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFsg_w).
  Proof using All.
    intros Lpc Lpriv Hdisp Lhs LS Lelp Lmisa.
    assert (LpcA : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA : register_lookup cur_privilege sAl.(sregs) = Supervisor).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdecA : exec (ext_decode_compressed w16) sAl = Some (cinstr, sAl))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAl = Some (true, sAl))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXsg)).
    { exact (exec_hart_active_progress_RVC_gen Supervisor sAl sXsg w16 cinstr base pc RETIRE_SUCCESS
               LprivA Hdisp Hfetch_at HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    apply (exec_riscv_step_gen_gen Supervisor s sXsg (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXsg, s_pc_f, s_pc, sAl; cbn [sregs].
      do 3 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhs.
    - unfold sXsg, s_pc_f, s_pc, sAl; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  Variable mst0 : mword 64.
  Definition base_upd_sg_super_w : mstate := set_reg sXsg PC (add_vec_int pc 2).
  Definition sFcsg_super_w : mstate :=
    if b then set_reg base_upd_sg_super_w minstret (add_vec_int mst0 1) else base_upd_sg_super_w.

  Lemma sFs_eq_super_walk : register_lookup minstret s.(sregs) = mst0 -> sFsg_w = sFcsg_super_w.
  Proof using All.
    intro Lmst_s.
    assert (Enpc : register_lookup nextPC sXsg.(sregs) = add_vec_int pc 2).
    { unfold sXsg; cbn [sregs]. unfold s_pc_f, s_pc, sAl.
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite register_lookup_set. reflexivity. }
    unfold sFsg_w, sTsg_w, sFcsg_super_w, base_upd_sg_super_w. rewrite Enpc. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret (set_reg sXsg PC (add_vec_int pc 2)).(sregs) = mst0).
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      unfold sXsg; cbn [sregs]. unfold s_pc_f, s_pc, sAl, set_reg; cbn [sregs].
      do 3 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmst_s. }
    rewrite Emst. reflexivity.
  Qed.
End ForwardCsdspWalk.

  (* ====================================================================== *)
  (* WP for kernelvec's first c.sdsp @0x800053e2 whose store-address          *)
  (* translation WALKS: the stack page (same 1GB superpage, VPN[2]=2) is not   *)
  (* yet in the TLB, so the store re-reads the owned PTE and FILLS the TLB at  *)
  (* tlb_hash vpn. Htr is DISCHARGED (no translation hypothesis).              *)
  (* ====================================================================== *)
  Context (root_ppn : mword 44).

  Lemma wp_pagewalk_csdsp_walk (w : mword 16) (uimm : mword 6) (rs2 : mword 5) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vrs2 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (vold : bv 64) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_st region_f region_pte : PMA_Region)
      E {dq dqp : dfrac} (Phi : mval -> iProp Σ) :
    let offset := sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) in
    let ea := add_vec vsp offset in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    uint rs2 <> 0 ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (store_ppn_out vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (store_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e2)) 2 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    isRVC w = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w) s0 = Some (C_SDSP (uimm, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ (mword_of_int 0x800053e2 : mword 64) -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dqp} nth_byte pte_super j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dqp} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa tlbf Hrs2 Hsp Hmrs2 HSXL Hmode Hppn Hasid Hvec5 Hvecst
      Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn Hmatchf Hexecf Hmatch Hwrite Hmatchpte Hptesup Hpmm HPBMTE
      HA0 Hord0 Hrange0f Hrange0 Hrange0pte HX0 HW0 HR0 Halignf Halign8 Hpalign8 Hpalignpte HisRVC HmisaC HmisaS HMPRV HMXR
      Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hptebytes Hibytes Hcont".
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")     as %Lmst.
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
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmrs2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_super2 root_ppn mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec5 HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
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
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hrampte.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hptebytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytes.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hptebytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2)).
    assert (Lsp_pc : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc.(sregs) = vsp).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lsp. }
    assert (Lrs2_pc : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs) = vrs2).
    { unfold s_pc, set_reg; cbn [sregs]. do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lrs2. }
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
    pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (proj1 Hrampte) ltac:(lia)) as Hwcp.
    pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (proj2 Hrampte) ltac:(lia)) as Hwsp.
    pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
    set (s_pc_f := set_reg s_pc tlb tlbf).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc_f)).
    { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8)) with a8
        by (cbn [bits_of_virtaddr]; change (0 * 8) with 0; rewrite avi0; reflexivity).
      unfold s_pc_f, tlbf.
      replace pa with a8 by (unfold pa; change (0 * 8) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
      apply (exec_translateAddr_store_walk root_ppn a8 vpn region_pte menvcfg0 satp0 tlbvec s_pc
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
               Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident Ltlb_pc
               Hvecst Hvpn2 Hmvpn Hmppn
               ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
               ltac:(rewrite Lpmpaddr_pc; exact Hrange0pte) ltac:(rewrite Lpmpc_pc; exact HR0)
               ltac:(rewrite Lpma_pc; exact Hmatchpte) Hpalignpte Hptesup Hwcp Hwsp Hwhp
               ltac:(unfold s_pc, set_reg; cbn [mem]; exact Hpbytes) Lmenv_pc HPBMTE). }
    assert (Lpriv_pcf : register_lookup cur_privilege s_pc_f.(sregs) = Supervisor).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv_pc | vm_compute; reflexivity ]. }
    assert (Lms_pcf : register_lookup mstatus s_pc_f.(sregs) = mstatus0).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lms_pc | vm_compute; reflexivity ]. }
    assert (Lpmpc_pcf : register_lookup pmpcfg_n s_pc_f.(sregs) = pmpcfg0).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpmpc_pc | vm_compute; reflexivity ]. }
    assert (Lpmpaddr_pcf : register_lookup pmpaddr_n s_pc_f.(sregs) = pmpaddr00).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpmpaddr_pc | vm_compute; reflexivity ]. }
    assert (Lpma_pcf : register_lookup pma_regions s_pc_f.(sregs) = pmar0).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpma_pc | vm_compute; reflexivity ]. }
    assert (Lhtif_pcf : register_lookup htif_tohost_base s_pc_f.(sregs) = None).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhtif_pc | vm_compute; reflexivity ]. }
    assert (Lsp_pcf : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc_f.(sregs) = vsp).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lsp_pc | reg_ne ]. }
    assert (Lrs2_pcf : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc_f.(sregs) = vrs2).
    { unfold s_pc_f, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lrs2_pc | reg_ne ]. }
    pose proof (within_clint_false pa 8 s_pc_f (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc_f (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_pc_f Lhtif_pcf) as Hwh.
    pose (s_x := MState s_pc_f.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2)).
    assert (Hstore : exec (execute (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { unfold sp.
      rewrite (exec_execute_STORE_8_gpr_S_walk rs2 (zero_extend' 5 ('b"10")) (zero_extend' 12 (concat_vec uimm ('b"000")))
                 region_st satp0 tlbf s_pc
                 ltac:(vm_compute; discriminate) Hrs2 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc
                 Hmode ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lsp_pc; exact Halign8) ltac:(rewrite Lsp_pc; exact Htr_pc)
                 Lpriv_pcf ltac:(rewrite Lms_pcf; exact HMPRV)
                 ltac:(rewrite Lpmpc_pcf; exact HA0) ltac:(rewrite Lpmpaddr_pcf; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pcf Lsp_pc; exact Hrange0) ltac:(rewrite Lpmpc_pcf; exact HW0)
                 ltac:(rewrite Lpma_pcf Lsp_pc; exact Hmatch) ltac:(rewrite Lsp_pc; exact Hpalign8)
                 Hwrite ltac:(rewrite Lsp_pc; apply Hwc) ltac:(rewrite Lsp_pc; apply Hws)
                 ltac:(rewrite Lsp_pc; apply Hwh)).
      subst s_x. unfold s_pc_f. do 3 f_equal. rewrite Lsp_pc Lrs2_pc. reflexivity. }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcsg_super_w s (mword_of_int 0x800053e2) b1 pa vrs2 tlbf mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFs_eq_super_walk s (mword_of_int 0x800053e2) b1 w (C_SDSP (uimm, Regidx rs2))
                    (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2 tlbf
                    Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore mst0 Lmst).
      apply (forward_exec_csdsp_super_walk s (mword_of_int 0x800053e2) b1 w (C_SDSP (uimm, Regidx rs2))
               (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2 tlbf
               Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ tlb _ tlbf with "Hreg Htlb") as "[Hreg Htlb]".
    iMod (reg_update _ PC _ (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    unfold sFcsg_super_w, base_upd_sg_super_w. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hptebytes Hibytes").
    - iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hptebytes Hibytes").
  Qed.

End KVS.

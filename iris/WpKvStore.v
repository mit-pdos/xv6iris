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

  (* ====================================================================== *)
  (* Generalized store WP: a c.sdsp executing at ANY instruction address va   *)
  (* in the code page (vpn 0x80005), storing rs2 to sp+uimm*8 in the stack    *)
  (* page (already mapped). The fetch hits the superpage TLB entry; the store *)
  (* address translation HITS (state-preserving). Two versions by alignment.  *)
  (* ====================================================================== *)

  (* instruction-fetch translation at a symbolic code-page address va (TLB hit). *)
  Lemma exec_translateAddr_super_fetch_at (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with sp_vpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_hit_super _ _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

(* generalized 2-byte-aligned RVC fetch at a symbolic code-page address va. *)
Section FetchAt2.
  Context (va : mword 64) (region : PMA_Region) (w : mword 16) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint va) (uint (to_bits 64 2)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr va) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr va) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr va) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr va) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte w j).
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.
  Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
  Hypothesis Halign4 : is_aligned_vaddr (Virtaddr va) 4 = false.

  Lemma exec_fetch_bytes_2_at : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR.
        rewrite (exec_translateAddr_super_fetch_at va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA va region w s
                   HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_RVC_2_at : exec (fetch tt) s = Some (F_RVC w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Halign4. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_2_at).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchAt2.

  (* generalized iris fetch bridge (2-byte-aligned) at symbolic code address va. *)
  Lemma fetch_from_pts_at_2 (va : mword 64)
      (mstatus0 misa0 satp0 : mword 64) (w : mword 16) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr va) 2 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
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
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 2 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC w = true ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ va -∗ cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ misa ↦ᵣ misa0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hmode Hasid Hvec Hcanon Hvpn_def Hident Hbit0 Hbit1 Halign4
             HA0 Hord0 Hrange0 HX0 Halign HmisaC0 HisRVC)
            "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa Hpmpc Hpmpaddr Hpma Hhtif Hbytes".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")   as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
               s.(mem) !! (pa_add va j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 2)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram va⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = va).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Supervisor).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltms : register_lookup mstatus t.(sregs) = mstatus0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity]. }
    assert (Ltsatp : register_lookup satp t.(sregs) = satp0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lsatp | vm_compute; reflexivity]. }
    assert (Lttlb : register_lookup tlb t.(sregs) = tlbvec).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Ltlb | vm_compute; reflexivity]. }
    assert (Ltmisa : register_lookup misa t.(sregs) = misa0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmisa | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpmpaddr : register_lookup pmpaddr_n t.(sregs) = pmpaddr00).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 2)%N ->
              t.(mem) !! (pa_add va j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    exact (exec_fetch_RVC_2_at va region w satp0 tlbvec t Ltpriv Ltpc
             ltac:(rewrite Ltms; exact HSXL0) Ltsatp Hmode Hasid Lttlb Hvec
             Hcanon Hvpn_def Hident
             ltac:(rewrite Ltpmpc; exact HA0)
             ltac:(rewrite Ltpmpaddr; exact Hord0)
             ltac:(rewrite Ltpmpaddr; exact Hrange0)
             ltac:(rewrite Ltpmpc; exact HX0)
             ltac:(rewrite Ltpma; exact Hmatch0)
             Halign Hexec
             (within_clint_false va 2 t Hnc ltac:(lia))
             (within_sig_false  va 2 t Hns ltac:(lia))
             (within_htif_false va 2 t Lthtif)
             Ltmem ltac:(rewrite Ltmisa; exact HmisaC0) HisRVC
             Hbit0 Hbit1 Halign4).
  Qed.

  (* ====================================================================== *)
  (* GENERALIZED store WP (2-byte-aligned fetch): c.sdsp rs2,uimm*8(sp) at    *)
  (* ANY code-page address va. Fetch hits the superpage entry at index 5; the *)
  (* store hits the stack entry at tlb_hash svpn (installed by an earlier     *)
  (* store). Both translations state-preserving; Htr DISCHARGED via the hit.  *)
  (* ====================================================================== *)
  Lemma wp_kv_store_2 (va : mword 64) (w : mword 16) (uimm : mword 6) (rs2 : mword 5) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vrs2 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (vold : bv 64) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_st region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let offset := sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) in
    let ea := add_vec vsp offset in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    uint rs2 <> 0 ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
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
    (* store superpage-identity bv facts for a8 / svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr va) 2 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
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
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
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
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va 2 -∗
        gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa Hrs2 Hsp Hmrs2 HSXL Hmode Hasid Hvec5 Hvecst
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
      Hcanon Hvpn_def Hident Hmask Hmatchf Hexecf Hmatch Hwrite Hpmm
      HA0 Hord0 Hrange0f Hrange0 HX0 HW0 Halignf Halign8 Hpalign8 HisRVC HmisaC HmisaS HMPRV HMXR
      Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes Hcont".
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
    iDestruct (fetch_from_pts_at_2 va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
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
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2)).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
    { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8)) with a8
        by (cbn [bits_of_virtaddr]; change (0 * 8) with 0; rewrite avi0; reflexivity).
      replace pa with a8 by (unfold pa; change (0 * 8) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
      apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec s_pc
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
               Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hvecst Hmask). }
    assert (Hstore : exec (execute (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { unfold sp.
      rewrite (exec_execute_STORE_8_gpr_S rs2 (zero_extend' 5 ('b"10")) (zero_extend' 12 (concat_vec uimm ('b"000")))
                 region_st satp0 s_pc
                 ltac:(vm_compute; discriminate) Hrs2 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc
                 Hmode ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lsp_pc; exact Halign8) ltac:(rewrite Lsp_pc; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lsp_pc; exact Hrange0) ltac:(rewrite Lpmpc_pc; exact HW0)
                 ltac:(rewrite Lpma_pc Lsp_pc; exact Hmatch) ltac:(rewrite Lsp_pc; exact Hpalign8)
                 Hwrite ltac:(rewrite Lsp_pc; apply Hwc) ltac:(rewrite Lsp_pc; apply Hws)
                 ltac:(rewrite Lsp_pc; apply Hwh)).
      subst s_x. do 3 f_equal. rewrite Lsp_pc Lrs2_pc. reflexivity. }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcsg_super s va b1 pa vrs2 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFs_eq_super root_ppn s va b1 w (C_SDSP (uimm, Regidx rs2))
                    (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
                    Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore mst0 Lmst).
      apply (forward_exec_csdsp_super root_ppn s va b1 w (C_SDSP (uimm, Regidx rs2))
               (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
               Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int va 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    unfold sFcsg_super, base_upd_sg_super. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
    - iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
  Qed.

(* generalized 4-byte-aligned RVC fetch at a symbolic code-page address va. *)
Section FetchAt4.
  Context (va : mword 64) (region : PMA_Region) (w : mword 32) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr va) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte w j).
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.
  Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = false.
  Hypothesis Halign4 : is_aligned_vaddr (Virtaddr va) 4 = true.

  Lemma exec_fetch_bytes_4_at : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR.
        rewrite (exec_translateAddr_super_fetch_at va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w s
                   HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_RVC_4_at : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Halign4. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_at).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchAt4.

  (* generalized iris fetch bridge (4-byte-aligned) at symbolic code address va. *)
  Lemma fetch_from_pts_at_4 (va : mword 64)
      (mstatus0 misa0 satp0 : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr va) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
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
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ va -∗ cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ misa ↦ᵣ misa0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC (subrange_vec_dec w 15 0), set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hmode Hasid Hvec Hcanon Hvpn_def Hident Hbit0 Hbit1 Halign4
             HA0 Hord0 Hrange0 HX0 Halign HmisaC0 HisRVC)
            "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa Hpmpc Hpmpaddr Hpma Hhtif Hbytes".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")   as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add va j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram va⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = va).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Supervisor).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltms : register_lookup mstatus t.(sregs) = mstatus0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity]. }
    assert (Ltsatp : register_lookup satp t.(sregs) = satp0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lsatp | vm_compute; reflexivity]. }
    assert (Lttlb : register_lookup tlb t.(sregs) = tlbvec).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Ltlb | vm_compute; reflexivity]. }
    assert (Ltmisa : register_lookup misa t.(sregs) = misa0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmisa | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpmpaddr : register_lookup pmpaddr_n t.(sregs) = pmpaddr00).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add va j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    exact (exec_fetch_RVC_4_at va region w satp0 tlbvec t Ltpriv Ltpc
             ltac:(rewrite Ltms; exact HSXL0) Ltsatp Hmode Hasid Lttlb Hvec
             Hcanon Hvpn_def Hident
             ltac:(rewrite Ltpmpc; exact HA0)
             ltac:(rewrite Ltpmpaddr; exact Hord0)
             ltac:(rewrite Ltpmpaddr; exact Hrange0)
             ltac:(rewrite Ltpmpc; exact HX0)
             ltac:(rewrite Ltpma; exact Hmatch0)
             Halign Hexec
             (within_clint_false va 4 t Hnc ltac:(lia))
             (within_sig_false  va 4 t Hns ltac:(lia))
             (within_htif_false va 4 t Lthtif)
             Ltmem HisRVC Hbit0 Hbit1 Halign4).
  Qed.

  (* ====================================================================== *)
  (* GENERALIZED store WP (4-byte-aligned fetch): c.sdsp rs2,uimm*8(sp) at    *)
  (* ANY code-page address va. Fetch hits the superpage entry at index 5; the *)
  (* store hits the stack entry at tlb_hash svpn (installed by an earlier     *)
  (* store). Both translations state-preserving; Htr DISCHARGED via the hit.  *)
  (* ====================================================================== *)
  Lemma wp_kv_store_4 (va : mword 64) (w : mword 32) (uimm : mword 6) (rs2 : mword 5) (svpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vrs2 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (vold : bv 64) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_st region_f : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let offset := sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) in
    let ea := add_vec vsp offset in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    uint rs2 <> 0 ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z (uint rs2) = Some vrs2 ->
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
    (* store superpage-identity bv facts for a8 / svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr va) 4 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
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
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_SDSP (uimm, Regidx rs2), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ va -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vold j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int va 2 -∗
        gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int va 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa Hrs2 Hsp Hmrs2 HSXL Hmode Hasid Hvec5 Hvecst
      Hcanonf Hvpndeff Hidentf Hbit0 Hbit1 Halign4
      Hcanon Hvpn_def Hident Hmask Hmatchf Hexecf Hmatch Hwrite Hpmm
      HA0 Hord0 Hrange0f Hrange0 HX0 HW0 Halignf Halign8 Hpalign8 HisRVC HmisaC HmisaS HMPRV HMXR
      Hdec Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes Hcont".
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
    iDestruct (fetch_from_pts_at_4 va mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
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
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2)).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
    { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8)) with a8
        by (cbn [bits_of_virtaddr]; change (0 * 8) with 0; rewrite avi0; reflexivity).
      replace pa with a8 by (unfold pa; change (0 * 8) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
      apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec s_pc
               Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
               Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hvecst Hmask). }
    assert (Hstore : exec (execute (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8))) s_pc
                     = Some (RETIRE_SUCCESS, s_x)).
    { unfold sp.
      rewrite (exec_execute_STORE_8_gpr_S rs2 (zero_extend' 5 ('b"10")) (zero_extend' 12 (concat_vec uimm ('b"000")))
                 region_st satp0 s_pc
                 ltac:(vm_compute; discriminate) Hrs2 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc
                 Hmode ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lsp_pc; exact Halign8) ltac:(rewrite Lsp_pc; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lsp_pc; exact Hrange0) ltac:(rewrite Lpmpc_pc; exact HW0)
                 ltac:(rewrite Lpma_pc Lsp_pc; exact Hmatch) ltac:(rewrite Lsp_pc; exact Hpalign8)
                 Hwrite ltac:(rewrite Lsp_pc; apply Hwc) ltac:(rewrite Lsp_pc; apply Hws)
                 ltac:(rewrite Lsp_pc; apply Hwh)).
      subst s_x. do 3 f_equal. rewrite Lsp_pc Lrs2_pc. reflexivity. }
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcsg_super s va b1 pa vrs2 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFs_eq_super root_ppn s va b1 (subrange_vec_dec w 15 0) (C_SDSP (uimm, Regidx rs2))
                    (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
                    Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore mst0 Lmst).
      apply (forward_exec_csdsp_super root_ppn s va b1 (subrange_vec_dec w 15 0) (C_SDSP (uimm, Regidx rs2))
               (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
               Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int va 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int va 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iMod (upd_window_8 s.(mem) pa vrs2 vold with "Hmem Hbytes") as "[Hmem Hbytes]".
    unfold sFcsg_super, base_upd_sg_super. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
    - iMod "Hclose" as "_". iModIntro.
      unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hbytes Hibytes").
  Qed.

End KVS.

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpStoreS2.v — WP for kernelvec's 2nd instruction, c.sdsp rs2,uimm*8(sp)
   @0x800053e2 (an S-mode RVC store).  Capstone wp_pagewalk_csdsp, no admits:
   - the FETCH hits the 1GB-superpage TLB entry that instruction 1's page walk
     installed (fetch_from_pts_super2 over WpStoreS.exec_fetch_RVC_2_super);
   - the store EXECUTE writes rs2 to mem[sp + uimm*8] (WpStoreS.exec_execute_STORE_8_gpr_S);
   - the step is assembled via a store forward engine (forward_exec_csdsp_super,
     reusing the RVC step engines with a memory-update post-state).
   The store's data-address translation is the hypothesis Htr (state-preserving
   identity, i.e. a TLB hit for the stack page). *)

Section SW2.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

(* Store forward engine: RVC store (c.sdsp) with a state-preserving fetch (the
   superpage TLB hit).  Reuses the RVC step engines; the post-execute state has
   memory (not registers) changed. *)
Section ForwardCsdsp.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (pa : mword 64) (vrs2 : bv 64).
  Let sAl := set_reg s (R_bool minstret_increment) b.
  Let s_pc := set_reg sAl nextPC (add_vec_int pc 2).
  Let sXsg := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2).
  Hypothesis Hfetch_at : exec (fetch tt) sAl = Some (F_RVC w16, sAl).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (cinstr, s0).
  Hypothesis Hcexec1 : exec (execute cinstr) s_pc = Some (ExecuteAs base, s_pc).
  Hypothesis Hcexec2 : exec (execute base) s_pc = Some (RETIRE_SUCCESS, sXsg).

  Definition sTsg : mstate := set_reg sXsg PC (register_lookup nextPC sXsg.(sregs)).
  Definition sFsg : mstate :=
    if b then set_reg sTsg minstret (add_vec_int (register_lookup minstret sTsg.(sregs)) 1)
         else sTsg.

  Lemma forward_exec_csdsp_super :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (dispatchInterrupt Supervisor) sAl = Some (None, sAl) ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFsg).
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
    - unfold sXsg, s_pc, sAl; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhs.
    - unfold sXsg, s_pc, sAl; cbn [sregs].
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  Variable mst0 : mword 64.
  Definition base_upd_sg_super : mstate := set_reg sXsg PC (add_vec_int pc 2).
  Definition sFcsg_super : mstate :=
    if b then set_reg base_upd_sg_super minstret (add_vec_int mst0 1) else base_upd_sg_super.

  Lemma sFs_eq_super : register_lookup minstret s.(sregs) = mst0 -> sFsg = sFcsg_super.
  Proof using All.
    intro Lmst_s.
    assert (Enpc : register_lookup nextPC sXsg.(sregs) = add_vec_int pc 2).
    { unfold sXsg; cbn [sregs]. unfold s_pc, sAl. rewrite register_lookup_set. reflexivity. }
    unfold sFsg, sTsg, sFcsg_super, base_upd_sg_super. rewrite Enpc. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret (set_reg sXsg PC (add_vec_int pc 2)).(sregs) = mst0).
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      unfold sXsg; cbn [sregs]. unfold s_pc, sAl, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmst_s. }
    rewrite Emst. reflexivity.
  Qed.
End ForwardCsdsp.

  (* iris-level bridge: instr 2's fetch hits the superpage TLB entry. *)
  Lemma fetch_from_pts_super2
      (mstatus0 misa0 satp0 : mword 64) (w : mword 16) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e2)) 2 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC w = true ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ (mword_of_int 0x800053e2 : mword 64) -∗ cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ misa ↦ᵣ misa0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hmode Hasid Hvec HA0 Hord0 Hrange0 HX0 Halign HmisaC0 HisRVC)
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
               s.(mem) !! (pa_add (mword_of_int 0x800053e2) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 2)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (mword_of_int 0x800053e2)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = mword_of_int 0x800053e2).
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
              t.(mem) !! (pa_add (mword_of_int 0x800053e2) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    exact (exec_fetch_RVC_2_super root_ppn region w satp0 tlbvec t Ltpriv Ltpc
             ltac:(rewrite Ltms; exact HSXL0) Ltsatp Hmode Hasid Lttlb Hvec
             ltac:(rewrite Ltpmpc; exact HA0)
             ltac:(rewrite Ltpmpaddr; exact Hord0)
             ltac:(rewrite Ltpmpaddr; exact Hrange0)
             ltac:(rewrite Ltpmpc; exact HX0)
             ltac:(rewrite Ltpma; exact Hmatch0)
             Halign Hexec
             (within_clint_false (mword_of_int 0x800053e2) 2 t Hnc ltac:(lia))
             (within_sig_false  (mword_of_int 0x800053e2) 2 t Hns ltac:(lia))
             (within_htif_false (mword_of_int 0x800053e2) 2 t Lthtif)
             Ltmem ltac:(rewrite Ltmisa; exact HmisaC0) HisRVC).
  Qed.

  (* ====================================================================== *)
  (* WP for kernelvec's 2nd instruction, c.sdsp rs2,uimm*8(sp) @0x800053e2.     *)
  (* The fetch hits the superpage TLB entry instr 1 installed; the store writes *)
  (* rs2 to mem[sp + uimm*8].  The store's data-address translation is taken as *)
  (* the hypothesis Htr (state-preserving identity — i.e. a TLB hit).           *)
  (* ====================================================================== *)
  Lemma wp_pagewalk_csdsp (w : mword 16) (uimm : mword 6) (rs2 : mword 5)
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
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e2)) 2 = Some region_f ->
    (override_PMA (PMA_Region_attributes region_f) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC w = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s', register_lookup cur_privilege s'.(sregs) = Supervisor ->
       register_lookup satp s'.(sregs) = satp0 ->
       register_lookup tlb s'.(sregs) = tlbvec ->
       _get_Mstatus_SXL (register_lookup mstatus s'.(sregs)) = 'b"10" ->
       exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s'
         = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s')) ->
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
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vrs2 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros offset ea a8 pa Hrs2 Hsp Hmrs2 HSXL Hmode Hasid Hvec Hmatchf Hexecf Hmatch Hwrite Hpmm
      HA0 Hord0 Hrange0f Hrange0 HX0 HW0 Halignf Halign8 Hpalign8 HisRVC HmisaC HmisaS HMPRV HMXR
      Htr Hdec Hb1 Hmie_mdl HSIE Help.
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
    iDestruct (reg_valid with "Hreg Hsec")     as %Lsec.
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
    iDestruct (fetch_from_pts_super2 mstatus0 misa0 satp0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL Hmode Hasid Hvec HA0 Hord0 Hrange0f HX0 Halignf HmisaC HisRVC
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
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2)).
    assert (Lsp_pc : register_lookup (R_bitvector_64 (gpr_of_Z 2)) s_pc.(sregs) = vsp).
    { unfold s_pc, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lsp. }
    assert (Lrs2_pc : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs) = vrs2).
    { unfold s_pc, set_reg; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | reg_ne ]). exact Lrs2. }
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
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
    (* the c.sdsp execute at s_pc: C_SDSP -> STORE -> memory write *)
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 vrs2)).
    assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s_pc
                     = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc))
      by (apply Htr; [ exact Lpriv_pc | exact Lsatp_pc | exact Ltlb_pc | rewrite Lms_pc; exact HSXL ]).
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
    iExists (sFcsg_super s (mword_of_int 0x800053e2) b1 pa vrs2 mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFs_eq_super s (mword_of_int 0x800053e2) b1 w (C_SDSP (uimm, Regidx rs2))
                    (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
                    Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore mst0 Lmst).
      apply (forward_exec_csdsp_super s (mword_of_int 0x800053e2) b1 w (C_SDSP (uimm, Regidx rs2))
               (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), Regidx rs2, sp, 8)) pa vrs2
               Hfetch_at Hsi_s Hdec (exec_execute_C_SDSP uimm (Regidx rs2) s_pc) Hstore Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) with "Hreg Hpc") as "[Hreg Hpc]".
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

End SW2.

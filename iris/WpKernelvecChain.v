From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKernelvecChain.v — chain kernelvec's first TWO instructions into one WP.
   wp_kernelvec_12: from the kernelvec entry (empty TLB + valid identity page
   table), run c.addi16sp sp,imm (which fills the TLB) then c.sdsp ra,0(sp)
   (which writes the stack), reaching PC 0x800053e4.  Composes
   WpPageWalk.wp_pagewalk_caddi16sp and WpStoreS2.wp_pagewalk_csdsp; the TLB the
   first instruction fills is consumed by the second's fetch (vec_access_update_5). *)

(* TLB filled at index 5 ⇒ lookup at index 5 returns the installed entry. *)
Lemma vec_access_update_5 (v : vec (option TLB_Entry) (2 ^ 6)) (e : TLB_Entry) :
  vec_access_dec (vec_update_dec v 5 (Some e)) 5 = Some e.
Proof.
  destruct v as [xs Hlen].
  assert (Hl : length xs = 64%nat) by (rewrite Hlen; reflexivity).
  unfold vec_access_dec, vec_update_dec.
  destruct (sumbool_of_bool (0 <=? 5 <? 2 ^ 6)) as [Heq | Hneq]; [ | discriminate ].
  cbn [projT1].
  unfold access_list_dec, update_list_dec, update_list_inc, list_update, access_list_inc, length_list.
  rewrite Hl.
  change (Z.to_nat (Z.of_nat 64 - 1 - 5)) with 58%nat.
  rewrite length_app. rewrite firstn_length. cbn [length]. rewrite skipn_length. rewrite Hl.
  change (Nat.min 58 64 + S (64 - 59))%nat with 64%nat.
  change (Z.of_nat 64 - 1 - 5 <? 0) with false.
  change (Z.to_nat (Z.of_nat 64 - 1 - 5)) with 58%nat.
  2: { rewrite Hl; lia. }
  replace 58%nat with (length (firstn 58 xs)) at 1 by (rewrite firstn_length; rewrite Hl; reflexivity).
  apply nth_middle.
Qed.


Section Chain.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

  (* Chain kernelvec's first two instructions: from the kernelvec entry (empty
     TLB + valid identity page table), run c.addi16sp sp,imm (fills the TLB) then
     c.sdsp ra,0(sp) (writes the stack), reaching PC 0x800053e4. *)
  Lemma wp_kernelvec_12 (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let spnew := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)) in
    let a8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))) (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let mst1 := if b1 then add_vec_int mst0 1 else mst0 in
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vra ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = None ->
    pma_allows_all pmar0 ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e2)) 2 = Some region_f2 ->
    (override_PMA (PMA_Region_attributes region_f2) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC (subrange_vec_dec w1 15 0) = true ->
    isRVC w2 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s', register_lookup cur_privilege s'.(sregs) = Supervisor ->
       register_lookup satp s'.(sregs) = satp0 ->
       register_lookup tlb s'.(sregs) = tlbf ->
       _get_Mstatus_SXL (register_lookup mstatus s'.(sregs)) = 'b"10" ->
       exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s'
         = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s')) ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w1 15 0)) s0 = Some (C_ADDI16SP imm6, s0)) ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w2) s0 = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ (mword_of_int 0x800053e0 : mword 64) -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg spnew]> m) -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ (if b1 then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w1 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf mst1.
    intros Hsp Hra HSXL Hmode Hppn Hasid Hvec Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Htr Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hcont".
    assert (HPC2 : add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 = mword_of_int 0x800053e2)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- instruction 1: c.addi16sp ---- *)
    iApply (wp_pagewalk_caddi16sp root_ppn w1 imm6 m vsp misa0 mdv0 mstatus0 menvcfg0 satp0 mie_v b1 npc0 mst0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 mi0 elp0 tlbvec region_pte E Phi
              Hsp HSXL Hmode Hppn Hasid Hvec Hpmaall Hmatchp Hpte HPBMTE HA0 Hord0 Hr1 Hrpte HX0 HR0 Hal4 Halpte HisRVC1
              HmisaC HmisaS Hdec1 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1".
    rewrite !HPC2.
    (* ---- instruction 2: c.sdsp ra,0(sp) ---- *)
    iApply (wp_pagewalk_csdsp root_ppn w2 (mword_of_int 0) (mword_of_int 1)
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vra (mword_of_int 0x800053e2) mst1 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf region_st region_f2 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hra | vm_compute; discriminate ])
              HSXL Hmode Hasid (vec_access_update_5 tlbvec (pw_tlb_entry root_ppn (mword_of_int 0)))
              Hmatchf2 Hexecf2 Hmatchst Hwrite Hpmm
              HA0 Hord0 Hr2 Hrst HX0 HW0 Hal2 Hal8 Hpal8 HisRVC2 HmisaC HmisaS HMPRV HMXR
              ltac:(intros s' Hcp Hsa Htl Hsx; apply Htr; assumption)
              Hdec2 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hib2").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hib2".
    assert (HPC4 : add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 = add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) by reflexivity.
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack").
  Qed.

  (* Chain variant where instruction 2's store-address translation WALKS (Htr is
     DISCHARGED): the first instruction's page-walk fills the TLB at index 5, the
     second's fetch hits it, and the store walks the SAME identity PTE to fill the
     TLB at tlb_hash vpn (the stack page), then writes the stack. *)
  Lemma wp_kernelvec_12_walk (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 : PMA_Region)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let spnew := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)) in
    let a8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))) (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let tlbf2 := vec_update_dec tlbf (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let mst1 := if b1 then add_vec_int mst0 1 else mst0 in
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vra ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = None ->
    vec_access_dec tlbf (tlb_hash (__id 39) vpn) = None ->
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (store_ppn_out vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (store_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pma_allows_all pmar0 ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e2)) 2 = Some region_f2 ->
    (override_PMA (PMA_Region_attributes region_f2) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region_st ->
    (override_PMA (PMA_Region_attributes region_st) PBMT_PMA).(PMA_writable) = true ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC (subrange_vec_dec w1 15 0) = true ->
    isRVC w2 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w1 15 0)) s0 = Some (C_ADDI16SP imm6, s0)) ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w2) s0 = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ (mword_of_int 0x800053e0 : mword 64) -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg spnew]> m) -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ (if b1 then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf2 -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf tlbf2 mst1.
    intros Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
      Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hcont".
    assert (HPC2 : add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 = mword_of_int 0x800053e2)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- instruction 1: c.addi16sp (page-walk fills TLB at index 5) ---- *)
    iApply (wp_pagewalk_caddi16sp root_ppn w1 imm6 m vsp misa0 mdv0 mstatus0 menvcfg0 satp0 mie_v b1 npc0 mst0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 mi0 elp0 tlbvec region_pte E Phi
              Hsp HSXL Hmode Hppn Hasid Hvec Hpmaall Hmatchp Hpte HPBMTE HA0 Hord0 Hr1 Hrpte HX0 HR0 Hal4 Halpte HisRVC1
              HmisaC HmisaS Hdec1 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1".
    rewrite !HPC2.
    (* ---- instruction 2: c.sdsp ra,0(sp) — store-address translation WALKS ---- *)
    iApply (wp_pagewalk_csdsp_walk root_ppn w2 (mword_of_int 0) (mword_of_int 1) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vra (mword_of_int 0x800053e2) mst1 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf region_st region_f2 region_pte E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hra | vm_compute; discriminate ])
              HSXL Hmode Hppn Hasid (vec_access_update_5 tlbvec (pw_tlb_entry root_ppn (mword_of_int 0))) Hvecst
              Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
              Hmatchf2 Hexecf2 Hmatchst Hwrite Hmatchp Hpte Hpmm HPBMTE
              HA0 Hord0 Hr2 Hrst Hrpte HX0 HW0 HR0 Hal2 Hal8 Hpal8 Halpte HisRVC2 HmisaC HmisaS HMPRV HMXR
              Hdec2 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hpbytes Hib2").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hpbytes Hib2".
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hpbytes Hib2").
  Qed.

End Chain.

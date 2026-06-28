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
    ↑minstretN ⊆ E ->
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
    minstret_inv -∗
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
    intros HN Hsp Hra HSXL Hmode Hppn Hasid Hvec Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Htr Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help.
    iIntros "Hpc Hfile Hmisa Hnpc #Hinv Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hcont".
    assert (HPC2 : add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 = mword_of_int 0x800053e2)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- instruction 1: c.addi16sp ---- *)
    iApply (wp_pagewalk_caddi16sp root_ppn w1 imm6 m vsp misa0 mdv0 mstatus0 menvcfg0 satp0 mie_v b1 npc0 mst0 mc mcfg
              pmpcfg0 pmpaddr00 pmar0 mi0 elp0 tlbvec region_pte E Phi
              HN Hsp HSXL Hmode Hppn Hasid Hvec Hpmaall Hmatchp Hpte HPBMTE HA0 Hord0 Hr1 Hrpte HX0 HR0 Hal4 Halpte HisRVC1
              HmisaC HmisaS Hdec1 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1".
    rewrite !HPC2.
    (* ---- instruction 2: c.sdsp ra,0(sp) ---- *)
    iApply (wp_pagewalk_csdsp root_ppn w2 (mword_of_int 0) (mword_of_int 1)
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vra (mword_of_int 0x800053e2) mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbf region_st region_f2 E Phi
              HN ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hra | vm_compute; discriminate ])
              HSXL Hmode Hasid (vec_access_update_5 tlbvec (pw_tlb_entry root_ppn (mword_of_int 0)))
              Hmatchf2 Hexecf2 Hmatchst Hwrite Hpmm
              HA0 Hord0 Hr2 Hrst HX0 HW0 Hal2 Hal8 Hpal8 HisRVC2 HmisaC HmisaS HMPRV HMXR
              ltac:(intros s' Hcp Hsa Htl Hsx; apply Htr; assumption)
              Hdec2 Hb1 Hmie_mdl HSIE Help
              with "Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hib2").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hib2".
    assert (HPC4 : add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 = add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) by reflexivity.
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack").
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

  Lemma wp_kernelvec_123 (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16) (w3 : mword 32) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 region_f3 region_st3 : PMA_Region)
      (vgp : mword 64) (vold3 : bv 64)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let spnew := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)) in
    let a8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))) (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let tlbf2 := vec_update_dec tlbf (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let mst1 := if b1 then add_vec_int mst0 1 else mst0 in
    let offset3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_3 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset3) (xlen - 0 - 1) 0) in
    let pa3 := zero_extend' 64 (add_vec_int a8_3 (0 * 8)) in
    let mst2 := if b1 then add_vec_int mst1 1 else mst1 in
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
    m !! gpr_of_Z 3 = Some vgp ->
    vec_access_dec tlbf2 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbf2 (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e4 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_3))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub pagesize_bits 1) 0)) = a8_3 ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e4)) 4 = Some region_f3 ->
    (override_PMA (PMA_Region_attributes region_f3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa3) 8 = Some region_st3 ->
    (override_PMA (PMA_Region_attributes region_st3) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e4)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_3) 8 = true ->
    is_aligned_paddr (Physaddr pa3) 8 = true ->
    isRVC (subrange_vec_dec w3 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w3 15 0)) s0 = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
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
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vold3 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e4 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg spnew]> m) -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e4 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ (if b1 then add_vec_int mst2 1 else mst2) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf2 -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vgp j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf tlbf2 mst1 offset3 a8_3 pa3 mst2.
    intros Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
      Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help
      Hgp Hvec5_2 Hvecst3 Hcanonf3 Hvpndeff3 Hidentf3 Hcanon3 Hvpndef3 Hident3 Hmask3
      Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hr3f Hr3s Hal3f Hal3v Hpal3 HisRVC3 Hdec3.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hib3 Hstack3 Hcont".
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
    assert (HPC4 : add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 = mword_of_int 0x800053e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPC4.
    (* ---- instruction 3: c.sdsp gp,16(sp) @0x800053e4 (4-aligned, TLB HIT) ---- *)
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053e4) w3 (mword_of_int 2) (mword_of_int 3) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vgp misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold3 (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) mst2 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st3 region_f3 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgp | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf3 Hvpndeff3 Hidentf3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon3 Hvpndef3 Hident3 Hmask3
              Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hpmm
              HA0 Hord0 Hr3f Hr3s HX0 HW0 Hal3f Hal3v Hpal3 HisRVC3 HmisaC HmisaS HMPRV HMXR
              Hdec3 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3".
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hstack3 Hpbytes Hib2 Hib3").
  Qed.

  Lemma wp_kernelvec_1234 (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16) (w3 : mword 32) (w4 : mword 16) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 region_f3 region_st3 region_f4 region_st4 : PMA_Region)
      (vgp vt0 : mword 64) (vold3 vold4 : bv 64)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let spnew := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)) in
    let a8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))) (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let tlbf2 := vec_update_dec tlbf (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let mst1 := if b1 then add_vec_int mst0 1 else mst0 in
    let offset3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_3 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset3) (xlen - 0 - 1) 0) in
    let pa3 := zero_extend' 64 (add_vec_int a8_3 (0 * 8)) in
    let mst2 := if b1 then add_vec_int mst1 1 else mst1 in
    let mst3 := if b1 then add_vec_int mst2 1 else mst2 in
    let offset4 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) in
    let a8_4 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset4) (xlen - 0 - 1) 0) in
    let pa4 := zero_extend' 64 (add_vec_int a8_4 (0 * 8)) in
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
    m !! gpr_of_Z 3 = Some vgp ->
    vec_access_dec tlbf2 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbf2 (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e4 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_3))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub pagesize_bits 1) 0)) = a8_3 ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e4)) 4 = Some region_f3 ->
    (override_PMA (PMA_Region_attributes region_f3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa3) 8 = Some region_st3 ->
    (override_PMA (PMA_Region_attributes region_st3) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e4)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_3) 8 = true ->
    is_aligned_paddr (Physaddr pa3) 8 = true ->
    isRVC (subrange_vec_dec w3 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w3 15 0)) s0 = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    m !! gpr_of_Z 5 = Some vt0 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e6 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_4))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub pagesize_bits 1) 0)) = a8_4 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e6)) 2 = Some region_f4 ->
    (override_PMA (PMA_Region_attributes region_f4) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa4) 8 = Some region_st4 ->
    (override_PMA (PMA_Region_attributes region_st4) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e6 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e6)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_4) 8 = true ->
    is_aligned_paddr (Physaddr pa4) 8 = true ->
    isRVC w4 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w4) s0 = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
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
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vold3 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e6) j) ↦ₘ{dq} nth_byte w4 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ nth_byte vold4 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e6 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg spnew]> m) -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e6 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ (if b1 then add_vec_int mst3 1 else mst3) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf2 -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vgp j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ nth_byte vt0 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e6) j) ↦ₘ{dq} nth_byte w4 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf tlbf2 mst1 offset3 a8_3 pa3 mst2 mst3 offset4 a8_4 pa4.
    intros Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
      Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help
      Hgp Hvec5_2 Hvecst3 Hcanonf3 Hvpndeff3 Hidentf3 Hcanon3 Hvpndef3 Hident3 Hmask3
      Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hr3f Hr3s Hal3f Hal3v Hpal3 HisRVC3 Hdec3
      Ht0 Hcanonf4 Hvpndeff4 Hidentf4 Hcanon4 Hvpndef4 Hident4 Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hr4f Hr4s Hal4f Hal4v Hpal4 HisRVC4 Hdec4.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hib3 Hstack3 Hib4 Hstack4 Hcont".
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
    assert (HPC4 : add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 = mword_of_int 0x800053e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPC4.
    (* ---- instruction 3: c.sdsp gp,16(sp) @0x800053e4 (4-aligned, TLB HIT) ---- *)
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053e4) w3 (mword_of_int 2) (mword_of_int 3) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vgp misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold3 (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) mst2 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st3 region_f3 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgp | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf3 Hvpndeff3 Hidentf3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon3 Hvpndef3 Hident3 Hmask3
              Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hpmm
              HA0 Hord0 Hr3f Hr3s HX0 HW0 Hal3f Hal3v Hpal3 HisRVC3 HmisaC HmisaS HMPRV HMXR
              Hdec3 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3".
    assert (HPC6 : add_vec_int (mword_of_int 0x800053e4 : mword 64) 2 = mword_of_int 0x800053e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPC6.
    (* ---- instruction 4: c.sdsp t0,32(sp) @0x800053e6 (2-aligned, TLB HIT) ---- *)
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053e6) w4 (mword_of_int 4) (mword_of_int 5) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vt0 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold4 (add_vec_int (mword_of_int 0x800053e4 : mword 64) 2) mst3 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st4 region_f4 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Ht0 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf4 Hvpndeff4 Hidentf4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon4 Hvpndef4 Hident4 Hmask3
              Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hpmm
              HA0 Hord0 Hr4f Hr4s HX0 HW0 Hal4f Hal4v Hpal4 HisRVC4 HmisaC HmisaS HMPRV HMXR
              Hdec4 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack4 Hib4").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack4 Hib4".
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hstack3 Hstack4 Hpbytes Hib2 Hib3 Hib4").
  Qed.

  Lemma wp_kernelvec_stores (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16) (w3 : mword 32) (w4 : mword 16) (w5 : mword 32) (w6 : mword 16) (w7 : mword 32) (w8 : mword 16) (w9 : mword 32) (w10 : mword 16) (w11 : mword 32) (w12 : mword 16) (w13 : mword 32) (w14 : mword 16) (w15 : mword 32) (w16 : mword 16) (w17 : mword 32) (w18 : mword 16) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 region_f3 region_st3 region_f4 region_st4  region_f5 region_st5  region_f6 region_st6  region_f7 region_st7  region_f8 region_st8  region_f9 region_st9  region_f10 region_st10  region_f11 region_st11  region_f12 region_st12  region_f13 region_st13  region_f14 region_st14  region_f15 region_st15  region_f16 region_st16  region_f17 region_st17  region_f18 region_st18 : PMA_Region)
      (vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 : mword 64) (vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 vold18 : bv 64)
      E {dq : dfrac} (Phi : mval -> iProp Σ) :
    let spnew := add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)) in
    let a8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))) (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let tlbf := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let tlbf2 := vec_update_dec tlbf (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    let mst1 := if b1 then add_vec_int mst0 1 else mst0 in
    let offset3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8_3 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset3) (xlen - 0 - 1) 0) in
    let pa3 := zero_extend' 64 (add_vec_int a8_3 (0 * 8)) in
    let mst2 := if b1 then add_vec_int mst1 1 else mst1 in
    let mst3 := if b1 then add_vec_int mst2 1 else mst2 in
    let offset4 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) in
    let a8_4 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset4) (xlen - 0 - 1) 0) in
    let pa4 := zero_extend' 64 (add_vec_int a8_4 (0 * 8)) in
    let mst4 := if b1 then add_vec_int mst3 1 else mst3 in
    let offset5 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) in
    let a8_5 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset5) (xlen - 0 - 1) 0) in
    let pa5 := zero_extend' 64 (add_vec_int a8_5 (0 * 8)) in
    let mst5 := if b1 then add_vec_int mst4 1 else mst4 in
    let offset6 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) in
    let a8_6 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset6) (xlen - 0 - 1) 0) in
    let pa6 := zero_extend' 64 (add_vec_int a8_6 (0 * 8)) in
    let mst6 := if b1 then add_vec_int mst5 1 else mst5 in
    let offset7 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) in
    let a8_7 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset7) (xlen - 0 - 1) 0) in
    let pa7 := zero_extend' 64 (add_vec_int a8_7 (0 * 8)) in
    let mst7 := if b1 then add_vec_int mst6 1 else mst6 in
    let offset8 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) in
    let a8_8 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset8) (xlen - 0 - 1) 0) in
    let pa8 := zero_extend' 64 (add_vec_int a8_8 (0 * 8)) in
    let mst8 := if b1 then add_vec_int mst7 1 else mst7 in
    let offset9 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) in
    let a8_9 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset9) (xlen - 0 - 1) 0) in
    let pa9 := zero_extend' 64 (add_vec_int a8_9 (0 * 8)) in
    let mst9 := if b1 then add_vec_int mst8 1 else mst8 in
    let offset10 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) in
    let a8_10 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset10) (xlen - 0 - 1) 0) in
    let pa10 := zero_extend' 64 (add_vec_int a8_10 (0 * 8)) in
    let mst10 := if b1 then add_vec_int mst9 1 else mst9 in
    let offset11 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) in
    let a8_11 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset11) (xlen - 0 - 1) 0) in
    let pa11 := zero_extend' 64 (add_vec_int a8_11 (0 * 8)) in
    let mst11 := if b1 then add_vec_int mst10 1 else mst10 in
    let offset12 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) in
    let a8_12 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset12) (xlen - 0 - 1) 0) in
    let pa12 := zero_extend' 64 (add_vec_int a8_12 (0 * 8)) in
    let mst12 := if b1 then add_vec_int mst11 1 else mst11 in
    let offset13 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) in
    let a8_13 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset13) (xlen - 0 - 1) 0) in
    let pa13 := zero_extend' 64 (add_vec_int a8_13 (0 * 8)) in
    let mst13 := if b1 then add_vec_int mst12 1 else mst12 in
    let offset14 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) in
    let a8_14 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset14) (xlen - 0 - 1) 0) in
    let pa14 := zero_extend' 64 (add_vec_int a8_14 (0 * 8)) in
    let mst14 := if b1 then add_vec_int mst13 1 else mst13 in
    let offset15 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) in
    let a8_15 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset15) (xlen - 0 - 1) 0) in
    let pa15 := zero_extend' 64 (add_vec_int a8_15 (0 * 8)) in
    let mst15 := if b1 then add_vec_int mst14 1 else mst14 in
    let offset16 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) in
    let a8_16 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset16) (xlen - 0 - 1) 0) in
    let pa16 := zero_extend' 64 (add_vec_int a8_16 (0 * 8)) in
    let mst16 := if b1 then add_vec_int mst15 1 else mst15 in
    let offset17 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) in
    let a8_17 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset17) (xlen - 0 - 1) 0) in
    let pa17 := zero_extend' 64 (add_vec_int a8_17 (0 * 8)) in
    let mst17 := if b1 then add_vec_int mst16 1 else mst16 in
    let offset18 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) in
    let a8_18 := sign_extend' 64 (subrange_vec_dec (add_vec (regval_into_reg spnew) offset18) (xlen - 0 - 1) 0) in
    let pa18 := zero_extend' 64 (add_vec_int a8_18 (0 * 8)) in
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
    m !! gpr_of_Z 3 = Some vgp ->
    vec_access_dec tlbf2 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbf2 (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e4 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_3))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub pagesize_bits 1) 0)) = a8_3 ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e4)) 4 = Some region_f3 ->
    (override_PMA (PMA_Region_attributes region_f3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa3) 8 = Some region_st3 ->
    (override_PMA (PMA_Region_attributes region_st3) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e4)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_3) 8 = true ->
    is_aligned_paddr (Physaddr pa3) 8 = true ->
    isRVC (subrange_vec_dec w3 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w3 15 0)) s0 = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    m !! gpr_of_Z 5 = Some vt0 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e6 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_4))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub pagesize_bits 1) 0)) = a8_4 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e6)) 2 = Some region_f4 ->
    (override_PMA (PMA_Region_attributes region_f4) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa4) 8 = Some region_st4 ->
    (override_PMA (PMA_Region_attributes region_st4) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e6 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e6)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_4) 8 = true ->
    is_aligned_paddr (Physaddr pa4) 8 = true ->
    isRVC w4 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w4) s0 = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
    m !! gpr_of_Z 6 = Some vR5 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e8 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_5))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub pagesize_bits 1) 0)) = a8_5 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e8)) 4 = Some region_f5 ->
    (override_PMA (PMA_Region_attributes region_f5) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa5) 8 = Some region_st5 ->
    (override_PMA (PMA_Region_attributes region_st5) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e8 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa5) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e8)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_5) 8 = true ->
    is_aligned_paddr (Physaddr pa5) 8 = true ->
    isRVC (subrange_vec_dec w5 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w5 15 0)) s0 = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 6)), s0)) ->
    m !! gpr_of_Z 7 = Some vR6 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ea : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_6))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub pagesize_bits 1) 0)) = a8_6 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ea)) 2 = Some region_f6 ->
    (override_PMA (PMA_Region_attributes region_f6) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa6) 8 = Some region_st6 ->
    (override_PMA (PMA_Region_attributes region_st6) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053ea : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa6) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053ea)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_6) 8 = true ->
    is_aligned_paddr (Physaddr pa6) 8 = true ->
    isRVC w6 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w6) s0 = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 7)), s0)) ->
    m !! gpr_of_Z 10 = Some vR7 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ec : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_7))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub pagesize_bits 1) 0)) = a8_7 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ec)) 4 = Some region_f7 ->
    (override_PMA (PMA_Region_attributes region_f7) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa7) 8 = Some region_st7 ->
    (override_PMA (PMA_Region_attributes region_st7) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053ec : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa7) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053ec)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_7) 8 = true ->
    is_aligned_paddr (Physaddr pa7) 8 = true ->
    isRVC (subrange_vec_dec w7 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w7 15 0)) s0 = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 10)), s0)) ->
    m !! gpr_of_Z 11 = Some vR8 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ee : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub pagesize_bits 1) 0)) = a8_8 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ee)) 2 = Some region_f8 ->
    (override_PMA (PMA_Region_attributes region_f8) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa8) 8 = Some region_st8 ->
    (override_PMA (PMA_Region_attributes region_st8) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053ee : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa8) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053ee)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_8) 8 = true ->
    is_aligned_paddr (Physaddr pa8) 8 = true ->
    isRVC w8 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w8) s0 = Some (C_SDSP (mword_of_int 10, Regidx (mword_of_int 11)), s0)) ->
    m !! gpr_of_Z 12 = Some vR9 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f0 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_9))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub pagesize_bits 1) 0)) = a8_9 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f0)) 4 = Some region_f9 ->
    (override_PMA (PMA_Region_attributes region_f9) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa9) 8 = Some region_st9 ->
    (override_PMA (PMA_Region_attributes region_st9) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053f0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa9) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053f0)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_9) 8 = true ->
    is_aligned_paddr (Physaddr pa9) 8 = true ->
    isRVC (subrange_vec_dec w9 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w9 15 0)) s0 = Some (C_SDSP (mword_of_int 11, Regidx (mword_of_int 12)), s0)) ->
    m !! gpr_of_Z 13 = Some vR10 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f2 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_10))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub pagesize_bits 1) 0)) = a8_10 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f2)) 2 = Some region_f10 ->
    (override_PMA (PMA_Region_attributes region_f10) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa10) 8 = Some region_st10 ->
    (override_PMA (PMA_Region_attributes region_st10) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053f2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa10) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053f2)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_10) 8 = true ->
    is_aligned_paddr (Physaddr pa10) 8 = true ->
    isRVC w10 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w10) s0 = Some (C_SDSP (mword_of_int 12, Regidx (mword_of_int 13)), s0)) ->
    m !! gpr_of_Z 14 = Some vR11 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f4 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_11))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub pagesize_bits 1) 0)) = a8_11 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f4)) 4 = Some region_f11 ->
    (override_PMA (PMA_Region_attributes region_f11) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa11) 8 = Some region_st11 ->
    (override_PMA (PMA_Region_attributes region_st11) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053f4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa11) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053f4)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_11) 8 = true ->
    is_aligned_paddr (Physaddr pa11) 8 = true ->
    isRVC (subrange_vec_dec w11 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w11 15 0)) s0 = Some (C_SDSP (mword_of_int 13, Regidx (mword_of_int 14)), s0)) ->
    m !! gpr_of_Z 15 = Some vR12 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f6 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_12))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub pagesize_bits 1) 0)) = a8_12 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f6)) 2 = Some region_f12 ->
    (override_PMA (PMA_Region_attributes region_f12) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa12) 8 = Some region_st12 ->
    (override_PMA (PMA_Region_attributes region_st12) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053f6 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa12) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053f6)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_12) 8 = true ->
    is_aligned_paddr (Physaddr pa12) 8 = true ->
    isRVC w12 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w12) s0 = Some (C_SDSP (mword_of_int 14, Regidx (mword_of_int 15)), s0)) ->
    m !! gpr_of_Z 16 = Some vR13 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f8 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_13))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub pagesize_bits 1) 0)) = a8_13 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f8)) 4 = Some region_f13 ->
    (override_PMA (PMA_Region_attributes region_f13) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa13) 8 = Some region_st13 ->
    (override_PMA (PMA_Region_attributes region_st13) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053f8 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa13) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053f8)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_13) 8 = true ->
    is_aligned_paddr (Physaddr pa13) 8 = true ->
    isRVC (subrange_vec_dec w13 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w13 15 0)) s0 = Some (C_SDSP (mword_of_int 15, Regidx (mword_of_int 16)), s0)) ->
    m !! gpr_of_Z 17 = Some vR14 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fa : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_14))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub pagesize_bits 1) 0)) = a8_14 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fa)) 2 = Some region_f14 ->
    (override_PMA (PMA_Region_attributes region_f14) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa14) 8 = Some region_st14 ->
    (override_PMA (PMA_Region_attributes region_st14) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053fa : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa14) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053fa)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_14) 8 = true ->
    is_aligned_paddr (Physaddr pa14) 8 = true ->
    isRVC w14 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w14) s0 = Some (C_SDSP (mword_of_int 16, Regidx (mword_of_int 17)), s0)) ->
    m !! gpr_of_Z 28 = Some vR15 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fc : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_15))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub pagesize_bits 1) 0)) = a8_15 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fc)) 4 = Some region_f15 ->
    (override_PMA (PMA_Region_attributes region_f15) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa15) 8 = Some region_st15 ->
    (override_PMA (PMA_Region_attributes region_st15) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053fc : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa15) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053fc)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_15) 8 = true ->
    is_aligned_paddr (Physaddr pa15) 8 = true ->
    isRVC (subrange_vec_dec w15 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w15 15 0)) s0 = Some (C_SDSP (mword_of_int 27, Regidx (mword_of_int 28)), s0)) ->
    m !! gpr_of_Z 29 = Some vR16 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fe : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_16))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub pagesize_bits 1) 0)) = a8_16 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fe)) 2 = Some region_f16 ->
    (override_PMA (PMA_Region_attributes region_f16) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa16) 8 = Some region_st16 ->
    (override_PMA (PMA_Region_attributes region_st16) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053fe : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa16) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053fe)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_16) 8 = true ->
    is_aligned_paddr (Physaddr pa16) 8 = true ->
    isRVC w16 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w16) s0 = Some (C_SDSP (mword_of_int 28, Regidx (mword_of_int 29)), s0)) ->
    m !! gpr_of_Z 30 = Some vR17 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x80005400 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_17))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub pagesize_bits 1) 0)) = a8_17 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x80005400)) 4 = Some region_f17 ->
    (override_PMA (PMA_Region_attributes region_f17) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa17) 8 = Some region_st17 ->
    (override_PMA (PMA_Region_attributes region_st17) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x80005400 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa17) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80005400)) 4 = true ->
    is_aligned_vaddr (Virtaddr a8_17) 8 = true ->
    is_aligned_paddr (Physaddr pa17) 8 = true ->
    isRVC (subrange_vec_dec w17 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w17 15 0)) s0 = Some (C_SDSP (mword_of_int 29, Regidx (mword_of_int 30)), s0)) ->
    m !! gpr_of_Z 31 = Some vR18 ->
    neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64)))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x80005402 : mword 64) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_18))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub pagesize_bits 1) 0)) = a8_18 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x80005402)) 2 = Some region_f18 ->
    (override_PMA (PMA_Region_attributes region_f18) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa18) 8 = Some region_st18 ->
    (override_PMA (PMA_Region_attributes region_st18) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x80005402 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa18) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80005402)) 2 = true ->
    is_aligned_vaddr (Virtaddr a8_18) 8 = true ->
    is_aligned_paddr (Physaddr pa18) 8 = true ->
    isRVC w18 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed w18) s0 = Some (C_SDSP (mword_of_int 30, Regidx (mword_of_int 31)), s0)) ->
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
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vold3 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e6) j) ↦ₘ{dq} nth_byte w4 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ nth_byte vold4 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e8) j) ↦ₘ{dq} nth_byte w5 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa5 j) ↦ₘ nth_byte vold5 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053ea) j) ↦ₘ{dq} nth_byte w6 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa6 j) ↦ₘ nth_byte vold6 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053ec) j) ↦ₘ{dq} nth_byte w7 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa7 j) ↦ₘ nth_byte vold7 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053ee) j) ↦ₘ{dq} nth_byte w8 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa8 j) ↦ₘ nth_byte vold8 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f0) j) ↦ₘ{dq} nth_byte w9 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa9 j) ↦ₘ nth_byte vold9 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053f2) j) ↦ₘ{dq} nth_byte w10 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa10 j) ↦ₘ nth_byte vold10 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f4) j) ↦ₘ{dq} nth_byte w11 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa11 j) ↦ₘ nth_byte vold11 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053f6) j) ↦ₘ{dq} nth_byte w12 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa12 j) ↦ₘ nth_byte vold12 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f8) j) ↦ₘ{dq} nth_byte w13 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa13 j) ↦ₘ nth_byte vold13 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053fa) j) ↦ₘ{dq} nth_byte w14 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa14 j) ↦ₘ nth_byte vold14 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053fc) j) ↦ₘ{dq} nth_byte w15 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa15 j) ↦ₘ nth_byte vold15 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053fe) j) ↦ₘ{dq} nth_byte w16 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa16 j) ↦ₘ nth_byte vold16 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x80005400) j) ↦ₘ{dq} nth_byte w17 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa17 j) ↦ₘ nth_byte vold17 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x80005402) j) ↦ₘ{dq} nth_byte w18 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa18 j) ↦ₘ nth_byte vold18 j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x80005402 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg spnew]> m) -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec_int (mword_of_int 0x80005402 : mword 64) 2 -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗ minstret ↦ᵣ (if b1 then add_vec_int mst17 1 else mst17) -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf2 -∗ menvcfg ↦ᵣ menvcfg0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte vra j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa3 j) ↦ₘ nth_byte vgp j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa4 j) ↦ₘ nth_byte vt0 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa5 j) ↦ₘ nth_byte vR5 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa6 j) ↦ₘ nth_byte vR6 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa7 j) ↦ₘ nth_byte vR7 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa8 j) ↦ₘ nth_byte vR8 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa9 j) ↦ₘ nth_byte vR9 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa10 j) ↦ₘ nth_byte vR10 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa11 j) ↦ₘ nth_byte vR11 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa12 j) ↦ₘ nth_byte vR12 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa13 j) ↦ₘ nth_byte vR13 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa14 j) ↦ₘ nth_byte vR14 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa15 j) ↦ₘ nth_byte vR15 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa16 j) ↦ₘ nth_byte vR16 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa17 j) ↦ₘ nth_byte vR17 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa18 j) ↦ₘ nth_byte vR18 j) -∗
        ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{dq} nth_byte pte_super j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e2) j) ↦ₘ{dq} nth_byte w2 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e4) j) ↦ₘ{dq} nth_byte w3 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053e6) j) ↦ₘ{dq} nth_byte w4 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e8) j) ↦ₘ{dq} nth_byte w5 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053ea) j) ↦ₘ{dq} nth_byte w6 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053ec) j) ↦ₘ{dq} nth_byte w7 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053ee) j) ↦ₘ{dq} nth_byte w8 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f0) j) ↦ₘ{dq} nth_byte w9 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053f2) j) ↦ₘ{dq} nth_byte w10 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f4) j) ↦ₘ{dq} nth_byte w11 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053f6) j) ↦ₘ{dq} nth_byte w12 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053f8) j) ↦ₘ{dq} nth_byte w13 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053fa) j) ↦ₘ{dq} nth_byte w14 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053fc) j) ↦ₘ{dq} nth_byte w15 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x800053fe) j) ↦ₘ{dq} nth_byte w16 j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x80005400) j) ↦ₘ{dq} nth_byte w17 j) -∗
        ([∗ list] j ∈ seq 0 2, (pa_add (mword_of_int 0x80005402) j) ↦ₘ{dq} nth_byte w18 j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf tlbf2 mst1 offset3 a8_3 pa3 mst2 mst3 offset4 a8_4 pa4 mst4 offset5 a8_5 pa5 mst5 offset6 a8_6 pa6 mst6 offset7 a8_7 pa7 mst7 offset8 a8_8 pa8 mst8 offset9 a8_9 pa9 mst9 offset10 a8_10 pa10 mst10 offset11 a8_11 pa11 mst11 offset12 a8_12 pa12 mst12 offset13 a8_13 pa13 mst13 offset14 a8_14 pa14 mst14 offset15 a8_15 pa15 mst15 offset16 a8_16 pa16 mst16 offset17 a8_17 pa17 mst17 offset18 a8_18 pa18.
    intros Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
      Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm
      HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR
      Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help
      Hgp Hvec5_2 Hvecst3 Hcanonf3 Hvpndeff3 Hidentf3 Hcanon3 Hvpndef3 Hident3 Hmask3
      Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hr3f Hr3s Hal3f Hal3v Hpal3 HisRVC3 Hdec3
      Ht0 Hcanonf4 Hvpndeff4 Hidentf4 Hcanon4 Hvpndef4 Hident4 Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hr4f Hr4s Hal4f Hal4v Hpal4 HisRVC4 Hdec4
      Hgpr5 Hcanonf5 Hvpndeff5 Hidentf5 Hcanon5 Hvpndef5 Hident5 Hmatchf5 Hexecf5 Hmatchst5 Hwrite5 Hrf5 Hrs5 Half5 Halv5 Hzpal5 Hisrvc5 Hdec5 Hgpr6 Hcanonf6 Hvpndeff6 Hidentf6 Hcanon6 Hvpndef6 Hident6 Hmatchf6 Hexecf6 Hmatchst6 Hwrite6 Hrf6 Hrs6 Half6 Halv6 Hzpal6 Hisrvc6 Hdec6 Hgpr7 Hcanonf7 Hvpndeff7 Hidentf7 Hcanon7 Hvpndef7 Hident7 Hmatchf7 Hexecf7 Hmatchst7 Hwrite7 Hrf7 Hrs7 Half7 Halv7 Hzpal7 Hisrvc7 Hdec7 Hgpr8 Hcanonf8 Hvpndeff8 Hidentf8 Hcanon8 Hvpndef8 Hident8 Hmatchf8 Hexecf8 Hmatchst8 Hwrite8 Hrf8 Hrs8 Half8 Halv8 Hzpal8 Hisrvc8 Hdec8 Hgpr9 Hcanonf9 Hvpndeff9 Hidentf9 Hcanon9 Hvpndef9 Hident9 Hmatchf9 Hexecf9 Hmatchst9 Hwrite9 Hrf9 Hrs9 Half9 Halv9 Hzpal9 Hisrvc9 Hdec9 Hgpr10 Hcanonf10 Hvpndeff10 Hidentf10 Hcanon10 Hvpndef10 Hident10 Hmatchf10 Hexecf10 Hmatchst10 Hwrite10 Hrf10 Hrs10 Half10 Halv10 Hzpal10 Hisrvc10 Hdec10 Hgpr11 Hcanonf11 Hvpndeff11 Hidentf11 Hcanon11 Hvpndef11 Hident11 Hmatchf11 Hexecf11 Hmatchst11 Hwrite11 Hrf11 Hrs11 Half11 Halv11 Hzpal11 Hisrvc11 Hdec11 Hgpr12 Hcanonf12 Hvpndeff12 Hidentf12 Hcanon12 Hvpndef12 Hident12 Hmatchf12 Hexecf12 Hmatchst12 Hwrite12 Hrf12 Hrs12 Half12 Halv12 Hzpal12 Hisrvc12 Hdec12 Hgpr13 Hcanonf13 Hvpndeff13 Hidentf13 Hcanon13 Hvpndef13 Hident13 Hmatchf13 Hexecf13 Hmatchst13 Hwrite13 Hrf13 Hrs13 Half13 Halv13 Hzpal13 Hisrvc13 Hdec13 Hgpr14 Hcanonf14 Hvpndeff14 Hidentf14 Hcanon14 Hvpndef14 Hident14 Hmatchf14 Hexecf14 Hmatchst14 Hwrite14 Hrf14 Hrs14 Half14 Halv14 Hzpal14 Hisrvc14 Hdec14 Hgpr15 Hcanonf15 Hvpndeff15 Hidentf15 Hcanon15 Hvpndef15 Hident15 Hmatchf15 Hexecf15 Hmatchst15 Hwrite15 Hrf15 Hrs15 Half15 Halv15 Hzpal15 Hisrvc15 Hdec15 Hgpr16 Hcanonf16 Hvpndeff16 Hidentf16 Hcanon16 Hvpndef16 Hident16 Hmatchf16 Hexecf16 Hmatchst16 Hwrite16 Hrf16 Hrs16 Half16 Halv16 Hzpal16 Hisrvc16 Hdec16 Hgpr17 Hcanonf17 Hvpndeff17 Hidentf17 Hcanon17 Hvpndef17 Hident17 Hmatchf17 Hexecf17 Hmatchst17 Hwrite17 Hrf17 Hrs17 Half17 Halv17 Hzpal17 Hisrvc17 Hdec17 Hgpr18 Hcanonf18 Hvpndeff18 Hidentf18 Hcanon18 Hvpndef18 Hident18 Hmatchf18 Hexecf18 Hmatchst18 Hwrite18 Hrf18 Hrs18 Half18 Halv18 Hzpal18 Hisrvc18 Hdec18.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hib3 Hstack3 Hib4 Hstack4 Hib5 Hstack5 Hib6 Hstack6 Hib7 Hstack7 Hib8 Hstack8 Hib9 Hstack9 Hib10 Hstack10 Hib11 Hstack11 Hib12 Hstack12 Hib13 Hstack13 Hib14 Hstack14 Hib15 Hstack15 Hib16 Hstack16 Hib17 Hstack17 Hib18 Hstack18 Hcont".
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
    assert (HPC4 : add_vec_int (mword_of_int 0x800053e2 : mword 64) 2 = mword_of_int 0x800053e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPC4.
    (* ---- instruction 3: c.sdsp gp,16(sp) @0x800053e4 (4-aligned, TLB HIT) ---- *)
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053e4) w3 (mword_of_int 2) (mword_of_int 3) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vgp misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold3 (add_vec_int (mword_of_int 0x800053e2 : mword 64) 2) mst2 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st3 region_f3 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgp | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf3 Hvpndeff3 Hidentf3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon3 Hvpndef3 Hident3 Hmask3
              Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hpmm
              HA0 Hord0 Hr3f Hr3s HX0 HW0 Hal3f Hal3v Hpal3 HisRVC3 HmisaC HmisaS HMPRV HMXR
              Hdec3 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack3 Hib3".
    assert (HPC6 : add_vec_int (mword_of_int 0x800053e4 : mword 64) 2 = mword_of_int 0x800053e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPC6.
    (* ---- instruction 4: c.sdsp t0,32(sp) @0x800053e6 (2-aligned, TLB HIT) ---- *)
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053e6) w4 (mword_of_int 4) (mword_of_int 5) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vt0 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold4 (add_vec_int (mword_of_int 0x800053e4 : mword 64) 2) mst3 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st4 region_f4 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Ht0 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf4 Hvpndeff4 Hidentf4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon4 Hvpndef4 Hident4 Hmask3
              Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hpmm
              HA0 Hord0 Hr4f Hr4s HX0 HW0 Hal4f Hal4v Hpal4 HisRVC4 HmisaC HmisaS HMPRV HMXR
              Hdec4 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack4 Hib4").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack4 Hib4".
    assert (HPCx5 : add_vec_int (mword_of_int 0x800053e6 : mword 64) 2 = mword_of_int 0x800053e8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx5.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053e8) w5 (mword_of_int 5) (mword_of_int 6) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR5 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold5 (add_vec_int (mword_of_int 0x800053e6 : mword 64) 2) mst4 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st5 region_f5 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr5 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf5 Hvpndeff5 Hidentf5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon5 Hvpndef5 Hident5 Hmask3
              Hmatchf5 Hexecf5 Hmatchst5 Hwrite5 Hpmm
              HA0 Hord0 Hrf5 Hrs5 HX0 HW0 Half5 Halv5 Hzpal5 Hisrvc5 HmisaC HmisaS HMPRV HMXR
              Hdec5 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack5 Hib5").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack5 Hib5".
    assert (HPCx6 : add_vec_int (mword_of_int 0x800053e8 : mword 64) 2 = mword_of_int 0x800053ea) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx6.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053ea) w6 (mword_of_int 6) (mword_of_int 7) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR6 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold6 (add_vec_int (mword_of_int 0x800053e8 : mword 64) 2) mst5 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st6 region_f6 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr6 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf6 Hvpndeff6 Hidentf6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon6 Hvpndef6 Hident6 Hmask3
              Hmatchf6 Hexecf6 Hmatchst6 Hwrite6 Hpmm
              HA0 Hord0 Hrf6 Hrs6 HX0 HW0 Half6 Halv6 Hzpal6 Hisrvc6 HmisaC HmisaS HMPRV HMXR
              Hdec6 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack6 Hib6").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack6 Hib6".
    assert (HPCx7 : add_vec_int (mword_of_int 0x800053ea : mword 64) 2 = mword_of_int 0x800053ec) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx7.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053ec) w7 (mword_of_int 9) (mword_of_int 10) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR7 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold7 (add_vec_int (mword_of_int 0x800053ea : mword 64) 2) mst6 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st7 region_f7 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr7 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf7 Hvpndeff7 Hidentf7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon7 Hvpndef7 Hident7 Hmask3
              Hmatchf7 Hexecf7 Hmatchst7 Hwrite7 Hpmm
              HA0 Hord0 Hrf7 Hrs7 HX0 HW0 Half7 Halv7 Hzpal7 Hisrvc7 HmisaC HmisaS HMPRV HMXR
              Hdec7 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack7 Hib7").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack7 Hib7".
    assert (HPCx8 : add_vec_int (mword_of_int 0x800053ec : mword 64) 2 = mword_of_int 0x800053ee) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx8.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053ee) w8 (mword_of_int 10) (mword_of_int 11) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR8 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold8 (add_vec_int (mword_of_int 0x800053ec : mword 64) 2) mst7 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st8 region_f8 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr8 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf8 Hvpndeff8 Hidentf8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon8 Hvpndef8 Hident8 Hmask3
              Hmatchf8 Hexecf8 Hmatchst8 Hwrite8 Hpmm
              HA0 Hord0 Hrf8 Hrs8 HX0 HW0 Half8 Halv8 Hzpal8 Hisrvc8 HmisaC HmisaS HMPRV HMXR
              Hdec8 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack8 Hib8").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack8 Hib8".
    assert (HPCx9 : add_vec_int (mword_of_int 0x800053ee : mword 64) 2 = mword_of_int 0x800053f0) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx9.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053f0) w9 (mword_of_int 11) (mword_of_int 12) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR9 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold9 (add_vec_int (mword_of_int 0x800053ee : mword 64) 2) mst8 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st9 region_f9 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr9 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf9 Hvpndeff9 Hidentf9 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon9 Hvpndef9 Hident9 Hmask3
              Hmatchf9 Hexecf9 Hmatchst9 Hwrite9 Hpmm
              HA0 Hord0 Hrf9 Hrs9 HX0 HW0 Half9 Halv9 Hzpal9 Hisrvc9 HmisaC HmisaS HMPRV HMXR
              Hdec9 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack9 Hib9").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack9 Hib9".
    assert (HPCx10 : add_vec_int (mword_of_int 0x800053f0 : mword 64) 2 = mword_of_int 0x800053f2) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx10.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053f2) w10 (mword_of_int 12) (mword_of_int 13) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR10 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold10 (add_vec_int (mword_of_int 0x800053f0 : mword 64) 2) mst9 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st10 region_f10 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr10 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf10 Hvpndeff10 Hidentf10 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon10 Hvpndef10 Hident10 Hmask3
              Hmatchf10 Hexecf10 Hmatchst10 Hwrite10 Hpmm
              HA0 Hord0 Hrf10 Hrs10 HX0 HW0 Half10 Halv10 Hzpal10 Hisrvc10 HmisaC HmisaS HMPRV HMXR
              Hdec10 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack10 Hib10").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack10 Hib10".
    assert (HPCx11 : add_vec_int (mword_of_int 0x800053f2 : mword 64) 2 = mword_of_int 0x800053f4) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx11.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053f4) w11 (mword_of_int 13) (mword_of_int 14) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR11 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold11 (add_vec_int (mword_of_int 0x800053f2 : mword 64) 2) mst10 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st11 region_f11 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr11 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf11 Hvpndeff11 Hidentf11 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon11 Hvpndef11 Hident11 Hmask3
              Hmatchf11 Hexecf11 Hmatchst11 Hwrite11 Hpmm
              HA0 Hord0 Hrf11 Hrs11 HX0 HW0 Half11 Halv11 Hzpal11 Hisrvc11 HmisaC HmisaS HMPRV HMXR
              Hdec11 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack11 Hib11").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack11 Hib11".
    assert (HPCx12 : add_vec_int (mword_of_int 0x800053f4 : mword 64) 2 = mword_of_int 0x800053f6) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx12.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053f6) w12 (mword_of_int 14) (mword_of_int 15) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR12 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold12 (add_vec_int (mword_of_int 0x800053f4 : mword 64) 2) mst11 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st12 region_f12 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr12 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf12 Hvpndeff12 Hidentf12 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon12 Hvpndef12 Hident12 Hmask3
              Hmatchf12 Hexecf12 Hmatchst12 Hwrite12 Hpmm
              HA0 Hord0 Hrf12 Hrs12 HX0 HW0 Half12 Halv12 Hzpal12 Hisrvc12 HmisaC HmisaS HMPRV HMXR
              Hdec12 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack12 Hib12").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack12 Hib12".
    assert (HPCx13 : add_vec_int (mword_of_int 0x800053f6 : mword 64) 2 = mword_of_int 0x800053f8) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx13.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053f8) w13 (mword_of_int 15) (mword_of_int 16) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR13 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold13 (add_vec_int (mword_of_int 0x800053f6 : mword 64) 2) mst12 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st13 region_f13 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr13 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf13 Hvpndeff13 Hidentf13 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon13 Hvpndef13 Hident13 Hmask3
              Hmatchf13 Hexecf13 Hmatchst13 Hwrite13 Hpmm
              HA0 Hord0 Hrf13 Hrs13 HX0 HW0 Half13 Halv13 Hzpal13 Hisrvc13 HmisaC HmisaS HMPRV HMXR
              Hdec13 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack13 Hib13").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack13 Hib13".
    assert (HPCx14 : add_vec_int (mword_of_int 0x800053f8 : mword 64) 2 = mword_of_int 0x800053fa) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx14.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053fa) w14 (mword_of_int 16) (mword_of_int 17) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR14 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold14 (add_vec_int (mword_of_int 0x800053f8 : mword 64) 2) mst13 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st14 region_f14 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr14 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf14 Hvpndeff14 Hidentf14 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon14 Hvpndef14 Hident14 Hmask3
              Hmatchf14 Hexecf14 Hmatchst14 Hwrite14 Hpmm
              HA0 Hord0 Hrf14 Hrs14 HX0 HW0 Half14 Halv14 Hzpal14 Hisrvc14 HmisaC HmisaS HMPRV HMXR
              Hdec14 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack14 Hib14").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack14 Hib14".
    assert (HPCx15 : add_vec_int (mword_of_int 0x800053fa : mword 64) 2 = mword_of_int 0x800053fc) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx15.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x800053fc) w15 (mword_of_int 27) (mword_of_int 28) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR15 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold15 (add_vec_int (mword_of_int 0x800053fa : mword 64) 2) mst14 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st15 region_f15 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr15 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf15 Hvpndeff15 Hidentf15 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon15 Hvpndef15 Hident15 Hmask3
              Hmatchf15 Hexecf15 Hmatchst15 Hwrite15 Hpmm
              HA0 Hord0 Hrf15 Hrs15 HX0 HW0 Half15 Halv15 Hzpal15 Hisrvc15 HmisaC HmisaS HMPRV HMXR
              Hdec15 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack15 Hib15").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack15 Hib15".
    assert (HPCx16 : add_vec_int (mword_of_int 0x800053fc : mword 64) 2 = mword_of_int 0x800053fe) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx16.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x800053fe) w16 (mword_of_int 28) (mword_of_int 29) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR16 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold16 (add_vec_int (mword_of_int 0x800053fc : mword 64) 2) mst15 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st16 region_f16 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr16 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf16 Hvpndeff16 Hidentf16 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon16 Hvpndef16 Hident16 Hmask3
              Hmatchf16 Hexecf16 Hmatchst16 Hwrite16 Hpmm
              HA0 Hord0 Hrf16 Hrs16 HX0 HW0 Half16 Halv16 Hzpal16 Hisrvc16 HmisaC HmisaS HMPRV HMXR
              Hdec16 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack16 Hib16").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack16 Hib16".
    assert (HPCx17 : add_vec_int (mword_of_int 0x800053fe : mword 64) 2 = mword_of_int 0x80005400) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx17.
    iApply (wp_kv_store_4 root_ppn (mword_of_int 0x80005400) w17 (mword_of_int 29) (mword_of_int 30) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR17 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold17 (add_vec_int (mword_of_int 0x800053fe : mword 64) 2) mst16 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st17 region_f17 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr17 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf17 Hvpndeff17 Hidentf17 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon17 Hvpndef17 Hident17 Hmask3
              Hmatchf17 Hexecf17 Hmatchst17 Hwrite17 Hpmm
              HA0 Hord0 Hrf17 Hrs17 HX0 HW0 Half17 Halv17 Hzpal17 Hisrvc17 HmisaC HmisaS HMPRV HMXR
              Hdec17 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack17 Hib17").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack17 Hib17".
    assert (HPCx18 : add_vec_int (mword_of_int 0x80005400 : mword 64) 2 = mword_of_int 0x80005402) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !HPCx18.
    iApply (wp_kv_store_2 root_ppn (mword_of_int 0x80005402) w18 (mword_of_int 30) (mword_of_int 31) vpn
              (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vR18 misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v
              b1 vold18 (add_vec_int (mword_of_int 0x80005400 : mword 64) 2) mst17 mc mcfg pmpcfg0 pmpaddr00 pmar0 b1 elp0 tlbf2 region_st18 region_f18 E Phi
              ltac:(vm_compute; discriminate)
              (lookup_insert _ _ _) ltac:(rewrite lookup_insert_ne; [ exact Hgpr18 | vm_compute; discriminate ])
              HSXL Hmode Hasid Hvec5_2 Hvecst3
              Hcanonf18 Hvpndeff18 Hidentf18 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hcanon18 Hvpndef18 Hident18 Hmask3
              Hmatchf18 Hexecf18 Hmatchst18 Hwrite18 Hpmm
              HA0 Hord0 Hrf18 Hrs18 HX0 HW0 Half18 Halv18 Hzpal18 Hisrvc18 HmisaC HmisaS HMPRV HMXR
              Hdec18 Hb1 Hmie_mdl HSIE Help
              with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack18 Hib18").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack18 Hib18".
    iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hstack3 Hstack4 Hstack5 Hstack6 Hstack7 Hstack8 Hstack9 Hstack10 Hstack11 Hstack12 Hstack13 Hstack14 Hstack15 Hstack16 Hstack17 Hstack18 Hpbytes Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16 Hib17 Hib18").
  Qed.

End Chain.

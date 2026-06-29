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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore WpKernelvecChain WpGprMret WpGprSret WpKvJal WpKvTrap WpKvLoad WpKvLoadWp WpKvSret WpKvCompose.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ---- arithmetic facts used to show the saved/restored register values
   round-trip back to their originals (so the GPR file is preserved). ---- *)
Lemma kvP_signext_id (v : mword 64) : sign_extend' 64 v = v.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend]. apply bv_sign_extend_idemp.
Qed.
Lemma kvP_addv_zero (a : mword 64) : add_vec a (mword_of_int 0) = a.
Proof. exact (avi0 a). Qed.
Lemma kvP_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc. reflexivity.
Qed.
Lemma kvP_loadrt (v : mword 64) :
  extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v.
Proof.
  unfold extend_value. change (8*1*8) with 64. change (8*(0+1)*8-1) with 63. change (8*0*8) with 0.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend]. rewrite bv_sign_extend_idemp.
  unfold update_subrange_vec_dec, to_word_idx, to_word, get_word, zeros'. rewrite autocast_refl.
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice, zeros.
  bv_simplify. rewrite MachineWord.MachineWord.cast_idx_refl.
  change (MachineWord.Z_idx 64) with 64%N. change (MachineWord.Z_idx 0) with 0%N.
  rewrite bv_zero_extend_idemp. apply bv_eq. rewrite bv_concat_unsigned'.
  rewrite (bv_unsigned_N_0 (bv_extract 0 0 (MachineWord.zeros 64))).
  rewrite Z.lor_0_r. change (Z.of_N 0) with 0%Z. rewrite Z.shiftl_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma kvP_round (v : mword 64) :
  regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v)) = v.
Proof. unfold regval_into_reg. apply kvP_loadrt. Qed.

Section KVALL.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).


  Lemma wp_kernelvec (w1 : mword 32) (imm6 : mword 6) (w2 : mword 16) (w3 : mword 32) (w4 : mword 16) (w5 : mword 32) (w6 : mword 16) (w7 : mword 32) (w8 : mword 16) (w9 : mword 32) (w10 : mword 16) (w11 : mword 32) (w12 : mword 16) (w13 : mword 32) (w14 : mword 16) (w15 : mword 32) (w16 : mword 16) (w17 : mword 32) (w18 : mword 16) (vpn : mword 27)
      (m : gmap register_bitvector_64 (mword 64))
      (vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte region_st region_f2 region_f3 region_st3 region_f4 region_st4  region_f5 region_st5  region_f6 region_st6  region_f7 region_st7  region_f8 region_st8  region_f9 region_st9  region_f10 region_st10  region_f11 region_st11  region_f12 region_st12  region_f13 region_st13  region_f14 region_st14  region_f15 region_st15  region_f16 region_st16  region_f17 region_st17  region_f18 region_st18 : PMA_Region)
      (vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 : mword 64) (vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 vold18 : bv 64)
      (wj : mword 32) (imm : mword 21) (wL0 : mword 32) (wL1 : mword 16) (wL2 : mword 32) (wL3 : mword 16) (wL4 : mword 32) (wL5 : mword 16) (wL6 : mword 32) (wL7 : mword 16) (wL8 : mword 32) (wL9 : mword 16) (wL10 : mword 32) (wL11 : mword 16) (wL12 : mword 32) (wL13 : mword 16) (wL14 : mword 32) (wL15 : mword 16) (wL16 : mword 32) (wA : mword 16) (immA : mword 6) (wS : mword 32) (sepc0 : mword 64) (lpe : bool) (region_j region_A region_S : PMA_Region) (region_fL0 region_lL0 : PMA_Region) (region_fL1 region_lL1 : PMA_Region) (region_fL2 region_lL2 : PMA_Region) (region_fL3 region_lL3 : PMA_Region) (region_fL4 region_lL4 : PMA_Region) (region_fL5 region_lL5 : PMA_Region) (region_fL6 region_lL6 : PMA_Region) (region_fL7 region_lL7 : PMA_Region) (region_fL8 region_lL8 : PMA_Region) (region_fL9 region_lL9 : PMA_Region) (region_fL10 region_lL10 : PMA_Region) (region_fL11 region_lL11 : PMA_Region) (region_fL12 region_lL12 : PMA_Region) (region_fL13 region_lL13 : PMA_Region) (region_fL14 region_lL14 : PMA_Region) (region_fL15 region_lL15 : PMA_Region) (region_fL16 region_lL16 : PMA_Region) E {dq : dfrac} (Phi : mval -> iProp Σ) :
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
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    m !! gpr_of_Z 1 = Some vra ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = None ->
    vec_access_dec tlbf (tlb_hash (__id 39) vpn) = None ->
    neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (store_ppn_out vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
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
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053e2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    isRVC (subrange_vec_dec w1 15 0) = true ->
    isRVC w2 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w1 15 0)) s0 = Some (C_ADDI16SP imm6, s0)) ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w2) s0 = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    m !! gpr_of_Z 3 = Some vgp ->
    vec_access_dec tlbf2 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbf2 (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_3)) (Z.sub pagesize_bits 1) 0)) = a8_3 ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e4)) 4 = Some region_f3 ->
    (override_PMA (PMA_Region_attributes region_f3) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa3) 8 = Some region_st3 ->
    (override_PMA (PMA_Region_attributes region_st3) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053e4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_3) 8 = true ->
    is_aligned_paddr (Physaddr pa3) 8 = true ->
    isRVC (subrange_vec_dec w3 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w3 15 0)) s0 = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    m !! gpr_of_Z 5 = Some vt0 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_4)) (Z.sub pagesize_bits 1) 0)) = a8_4 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e6)) 2 = Some region_f4 ->
    (override_PMA (PMA_Region_attributes region_f4) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa4) 8 = Some region_st4 ->
    (override_PMA (PMA_Region_attributes region_st4) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053e6 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_4) 8 = true ->
    is_aligned_paddr (Physaddr pa4) 8 = true ->
    isRVC w4 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w4) s0 = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
    m !! gpr_of_Z 6 = Some vR5 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_5)) (Z.sub pagesize_bits 1) 0)) = a8_5 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e8)) 4 = Some region_f5 ->
    (override_PMA (PMA_Region_attributes region_f5) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa5) 8 = Some region_st5 ->
    (override_PMA (PMA_Region_attributes region_st5) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053e8 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa5) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_5) 8 = true ->
    is_aligned_paddr (Physaddr pa5) 8 = true ->
    isRVC (subrange_vec_dec w5 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w5 15 0)) s0 = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 6)), s0)) ->
    m !! gpr_of_Z 7 = Some vR6 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_6)) (Z.sub pagesize_bits 1) 0)) = a8_6 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ea)) 2 = Some region_f6 ->
    (override_PMA (PMA_Region_attributes region_f6) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa6) 8 = Some region_st6 ->
    (override_PMA (PMA_Region_attributes region_st6) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053ea : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa6) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_6) 8 = true ->
    is_aligned_paddr (Physaddr pa6) 8 = true ->
    isRVC w6 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w6) s0 = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 7)), s0)) ->
    m !! gpr_of_Z 10 = Some vR7 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_7)) (Z.sub pagesize_bits 1) 0)) = a8_7 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ec)) 4 = Some region_f7 ->
    (override_PMA (PMA_Region_attributes region_f7) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa7) 8 = Some region_st7 ->
    (override_PMA (PMA_Region_attributes region_st7) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053ec : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa7) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_7) 8 = true ->
    is_aligned_paddr (Physaddr pa7) 8 = true ->
    isRVC (subrange_vec_dec w7 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w7 15 0)) s0 = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 10)), s0)) ->
    m !! gpr_of_Z 11 = Some vR8 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_8)) (Z.sub pagesize_bits 1) 0)) = a8_8 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053ee)) 2 = Some region_f8 ->
    (override_PMA (PMA_Region_attributes region_f8) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa8) 8 = Some region_st8 ->
    (override_PMA (PMA_Region_attributes region_st8) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053ee : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa8) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_8) 8 = true ->
    is_aligned_paddr (Physaddr pa8) 8 = true ->
    isRVC w8 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w8) s0 = Some (C_SDSP (mword_of_int 10, Regidx (mword_of_int 11)), s0)) ->
    m !! gpr_of_Z 12 = Some vR9 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_9)) (Z.sub pagesize_bits 1) 0)) = a8_9 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f0)) 4 = Some region_f9 ->
    (override_PMA (PMA_Region_attributes region_f9) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa9) 8 = Some region_st9 ->
    (override_PMA (PMA_Region_attributes region_st9) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053f0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa9) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_9) 8 = true ->
    is_aligned_paddr (Physaddr pa9) 8 = true ->
    isRVC (subrange_vec_dec w9 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w9 15 0)) s0 = Some (C_SDSP (mword_of_int 11, Regidx (mword_of_int 12)), s0)) ->
    m !! gpr_of_Z 13 = Some vR10 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_10)) (Z.sub pagesize_bits 1) 0)) = a8_10 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f2)) 2 = Some region_f10 ->
    (override_PMA (PMA_Region_attributes region_f10) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa10) 8 = Some region_st10 ->
    (override_PMA (PMA_Region_attributes region_st10) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053f2 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa10) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_10) 8 = true ->
    is_aligned_paddr (Physaddr pa10) 8 = true ->
    isRVC w10 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w10) s0 = Some (C_SDSP (mword_of_int 12, Regidx (mword_of_int 13)), s0)) ->
    m !! gpr_of_Z 14 = Some vR11 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_11)) (Z.sub pagesize_bits 1) 0)) = a8_11 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f4)) 4 = Some region_f11 ->
    (override_PMA (PMA_Region_attributes region_f11) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa11) 8 = Some region_st11 ->
    (override_PMA (PMA_Region_attributes region_st11) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053f4 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa11) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_11) 8 = true ->
    is_aligned_paddr (Physaddr pa11) 8 = true ->
    isRVC (subrange_vec_dec w11 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w11 15 0)) s0 = Some (C_SDSP (mword_of_int 13, Regidx (mword_of_int 14)), s0)) ->
    m !! gpr_of_Z 15 = Some vR12 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_12)) (Z.sub pagesize_bits 1) 0)) = a8_12 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f6)) 2 = Some region_f12 ->
    (override_PMA (PMA_Region_attributes region_f12) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa12) 8 = Some region_st12 ->
    (override_PMA (PMA_Region_attributes region_st12) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053f6 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa12) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_12) 8 = true ->
    is_aligned_paddr (Physaddr pa12) 8 = true ->
    isRVC w12 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w12) s0 = Some (C_SDSP (mword_of_int 14, Regidx (mword_of_int 15)), s0)) ->
    m !! gpr_of_Z 16 = Some vR13 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_13)) (Z.sub pagesize_bits 1) 0)) = a8_13 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053f8)) 4 = Some region_f13 ->
    (override_PMA (PMA_Region_attributes region_f13) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa13) 8 = Some region_st13 ->
    (override_PMA (PMA_Region_attributes region_st13) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053f8 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa13) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_13) 8 = true ->
    is_aligned_paddr (Physaddr pa13) 8 = true ->
    isRVC (subrange_vec_dec w13 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w13 15 0)) s0 = Some (C_SDSP (mword_of_int 15, Regidx (mword_of_int 16)), s0)) ->
    m !! gpr_of_Z 17 = Some vR14 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_14)) (Z.sub pagesize_bits 1) 0)) = a8_14 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fa)) 2 = Some region_f14 ->
    (override_PMA (PMA_Region_attributes region_f14) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa14) 8 = Some region_st14 ->
    (override_PMA (PMA_Region_attributes region_st14) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053fa : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa14) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_14) 8 = true ->
    is_aligned_paddr (Physaddr pa14) 8 = true ->
    isRVC w14 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w14) s0 = Some (C_SDSP (mword_of_int 16, Regidx (mword_of_int 17)), s0)) ->
    m !! gpr_of_Z 28 = Some vR15 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_15)) (Z.sub pagesize_bits 1) 0)) = a8_15 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fc)) 4 = Some region_f15 ->
    (override_PMA (PMA_Region_attributes region_f15) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa15) 8 = Some region_st15 ->
    (override_PMA (PMA_Region_attributes region_st15) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053fc : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa15) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_15) 8 = true ->
    is_aligned_paddr (Physaddr pa15) 8 = true ->
    isRVC (subrange_vec_dec w15 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w15 15 0)) s0 = Some (C_SDSP (mword_of_int 27, Regidx (mword_of_int 28)), s0)) ->
    m !! gpr_of_Z 29 = Some vR16 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_16)) (Z.sub pagesize_bits 1) 0)) = a8_16 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053fe)) 2 = Some region_f16 ->
    (override_PMA (PMA_Region_attributes region_f16) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa16) 8 = Some region_st16 ->
    (override_PMA (PMA_Region_attributes region_st16) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x800053fe : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa16) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_16) 8 = true ->
    is_aligned_paddr (Physaddr pa16) 8 = true ->
    isRVC w16 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w16) s0 = Some (C_SDSP (mword_of_int 28, Regidx (mword_of_int 29)), s0)) ->
    m !! gpr_of_Z 30 = Some vR17 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_17)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_17)) (Z.sub pagesize_bits 1) 0)) = a8_17 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x80005400)) 4 = Some region_f17 ->
    (override_PMA (PMA_Region_attributes region_f17) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa17) 8 = Some region_st17 ->
    (override_PMA (PMA_Region_attributes region_st17) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x80005400 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa17) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_17) 8 = true ->
    is_aligned_paddr (Physaddr pa17) 8 = true ->
    isRVC (subrange_vec_dec w17 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec w17 15 0)) s0 = Some (C_SDSP (mword_of_int 29, Regidx (mword_of_int 30)), s0)) ->
    m !! gpr_of_Z 31 = Some vR18 ->
    neq_vec (bits_of_virtaddr (Virtaddr a8_18)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8_18)) (Z.sub pagesize_bits 1) 0)) = a8_18 ->
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x80005402)) 2 = Some region_f18 ->
    (override_PMA (PMA_Region_attributes region_f18) PBMT_PMA).(PMA_executable) = true ->
    matching_pma_region pmar0 (Physaddr pa18) 8 = Some region_st18 ->
    (override_PMA (PMA_Region_attributes region_st18) PBMT_PMA).(PMA_writable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint (mword_of_int 0x80005402 : mword 64)) (uint (to_bits 64 2)) = PMP_Match ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint pa18) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8_18) 8 = true ->
    is_aligned_paddr (Physaddr pa18) 8 = true ->
    isRVC w18 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed w18) s0 = Some (C_SDSP (mword_of_int 30, Regidx (mword_of_int 31)), s0)) ->
    let vaj := (add_vec_int (mword_of_int 0x80005402 : mword 64) 2 : mword 64) in
    let vLj0 := add_vec_int vaj 4 in
    let vLj1 := add_vec_int vLj0 2 in
    let vLj2 := add_vec_int vLj1 2 in
    let vLj3 := add_vec_int vLj2 2 in
    let vLj4 := add_vec_int vLj3 2 in
    let vLj5 := add_vec_int vLj4 2 in
    let vLj6 := add_vec_int vLj5 2 in
    let vLj7 := add_vec_int vLj6 2 in
    let vLj8 := add_vec_int vLj7 2 in
    let vLj9 := add_vec_int vLj8 2 in
    let vLj10 := add_vec_int vLj9 2 in
    let vLj11 := add_vec_int vLj10 2 in
    let vLj12 := add_vec_int vLj11 2 in
    let vLj13 := add_vec_int vLj12 2 in
    let vLj14 := add_vec_int vLj13 2 in
    let vLj15 := add_vec_int vLj14 2 in
    let vLj16 := add_vec_int vLj15 2 in
    let vAj := add_vec_int vLj16 2 in
    let vSj := add_vec_int vAj 2 in
    let offLj0 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8Lj0 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj0) (xlen - 0 - 1) 0) in
    let paLj0 := zero_extend' 64 (add_vec_int a8Lj0 (0 * 8)) in
    let offLj1 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a8Lj1 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj1) (xlen - 0 - 1) 0) in
    let paLj1 := zero_extend' 64 (add_vec_int a8Lj1 (0 * 8)) in
    let offLj2 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) in
    let a8Lj2 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj2) (xlen - 0 - 1) 0) in
    let paLj2 := zero_extend' 64 (add_vec_int a8Lj2 (0 * 8)) in
    let offLj3 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) in
    let a8Lj3 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj3) (xlen - 0 - 1) 0) in
    let paLj3 := zero_extend' 64 (add_vec_int a8Lj3 (0 * 8)) in
    let offLj4 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) in
    let a8Lj4 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj4) (xlen - 0 - 1) 0) in
    let paLj4 := zero_extend' 64 (add_vec_int a8Lj4 (0 * 8)) in
    let offLj5 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) in
    let a8Lj5 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj5) (xlen - 0 - 1) 0) in
    let paLj5 := zero_extend' 64 (add_vec_int a8Lj5 (0 * 8)) in
    let offLj6 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) in
    let a8Lj6 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj6) (xlen - 0 - 1) 0) in
    let paLj6 := zero_extend' 64 (add_vec_int a8Lj6 (0 * 8)) in
    let offLj7 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) in
    let a8Lj7 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj7) (xlen - 0 - 1) 0) in
    let paLj7 := zero_extend' 64 (add_vec_int a8Lj7 (0 * 8)) in
    let offLj8 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) in
    let a8Lj8 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj8) (xlen - 0 - 1) 0) in
    let paLj8 := zero_extend' 64 (add_vec_int a8Lj8 (0 * 8)) in
    let offLj9 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) in
    let a8Lj9 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj9) (xlen - 0 - 1) 0) in
    let paLj9 := zero_extend' 64 (add_vec_int a8Lj9 (0 * 8)) in
    let offLj10 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) in
    let a8Lj10 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj10) (xlen - 0 - 1) 0) in
    let paLj10 := zero_extend' 64 (add_vec_int a8Lj10 (0 * 8)) in
    let offLj11 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) in
    let a8Lj11 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj11) (xlen - 0 - 1) 0) in
    let paLj11 := zero_extend' 64 (add_vec_int a8Lj11 (0 * 8)) in
    let offLj12 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) in
    let a8Lj12 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj12) (xlen - 0 - 1) 0) in
    let paLj12 := zero_extend' 64 (add_vec_int a8Lj12 (0 * 8)) in
    let offLj13 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) in
    let a8Lj13 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj13) (xlen - 0 - 1) 0) in
    let paLj13 := zero_extend' 64 (add_vec_int a8Lj13 (0 * 8)) in
    let offLj14 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) in
    let a8Lj14 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj14) (xlen - 0 - 1) 0) in
    let paLj14 := zero_extend' 64 (add_vec_int a8Lj14 (0 * 8)) in
    let offLj15 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) in
    let a8Lj15 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj15) (xlen - 0 - 1) 0) in
    let paLj15 := zero_extend' 64 (add_vec_int a8Lj15 (0 * 8)) in
    let offLj16 := sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) in
    let a8Lj16 := sign_extend' 64 (subrange_vec_dec (add_vec spnew offLj16) (xlen - 0 - 1) 0) in
    let paLj16 := zero_extend' 64 (add_vec_int a8Lj16 (0 * 8)) in
    matching_pma_region pmar0 (Physaddr vaj) 4 = Some region_j ->
    (override_PMA (PMA_Region_attributes region_j) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vaj) (uint (to_bits 64 4)) = PMP_Match ->
    isRVC (subrange_vec_dec wj 15 0) = false ->
    add_vec vaj (sign_extend' 64 imm) = (mword_of_int 0x800026a2 : mword 64) ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor -> exec (ext_decode wj) s0 = Some (JAL (imm, Regidx (mword_of_int 1)), s0)) ->
    eq_vec (access_vec_dec (add_vec vaj (sign_extend' 64 imm)) 0) ('b"0") = true ->
    matching_pma_region pmar0 (Physaddr vLj0) 4 = Some region_fL0 ->
    (override_PMA (PMA_Region_attributes region_fL0) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj0) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj0)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj0)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj0)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj0)) (Z.sub pagesize_bits 1) 0)) = a8Lj0 ->
    matching_pma_region pmar0 (Physaddr paLj0) 8 = Some region_lL0 ->
    (override_PMA (PMA_Region_attributes region_lL0) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj0) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj0) 8 = true ->
    is_aligned_paddr (Physaddr paLj0) 8 = true ->
    isRVC (subrange_vec_dec wL0 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL0 15 0)) s0 = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 1)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj1) 2 = Some region_fL1 ->
    (override_PMA (PMA_Region_attributes region_fL1) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj1) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj1)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj1)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj1)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj1)) (Z.sub pagesize_bits 1) 0)) = a8Lj1 ->
    matching_pma_region pmar0 (Physaddr paLj1) 8 = Some region_lL1 ->
    (override_PMA (PMA_Region_attributes region_lL1) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj1) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj1) 8 = true ->
    is_aligned_paddr (Physaddr paLj1) 8 = true ->
    isRVC wL1 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL1) s0 = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 3)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj2) 4 = Some region_fL2 ->
    (override_PMA (PMA_Region_attributes region_fL2) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj2) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj2)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj2)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj2)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj2)) (Z.sub pagesize_bits 1) 0)) = a8Lj2 ->
    matching_pma_region pmar0 (Physaddr paLj2) 8 = Some region_lL2 ->
    (override_PMA (PMA_Region_attributes region_lL2) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj2) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj2) 8 = true ->
    is_aligned_paddr (Physaddr paLj2) 8 = true ->
    isRVC (subrange_vec_dec wL2 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL2 15 0)) s0 = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 5)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj3) 2 = Some region_fL3 ->
    (override_PMA (PMA_Region_attributes region_fL3) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj3) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj3)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj3)) (Z.sub pagesize_bits 1) 0)) = a8Lj3 ->
    matching_pma_region pmar0 (Physaddr paLj3) 8 = Some region_lL3 ->
    (override_PMA (PMA_Region_attributes region_lL3) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj3) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj3) 8 = true ->
    is_aligned_paddr (Physaddr paLj3) 8 = true ->
    isRVC wL3 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL3) s0 = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 6)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj4) 4 = Some region_fL4 ->
    (override_PMA (PMA_Region_attributes region_fL4) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj4) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj4)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj4)) (Z.sub pagesize_bits 1) 0)) = a8Lj4 ->
    matching_pma_region pmar0 (Physaddr paLj4) 8 = Some region_lL4 ->
    (override_PMA (PMA_Region_attributes region_lL4) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj4) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj4) 8 = true ->
    is_aligned_paddr (Physaddr paLj4) 8 = true ->
    isRVC (subrange_vec_dec wL4 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL4 15 0)) s0 = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 7)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj5) 2 = Some region_fL5 ->
    (override_PMA (PMA_Region_attributes region_fL5) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj5) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj5)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj5)) (Z.sub pagesize_bits 1) 0)) = a8Lj5 ->
    matching_pma_region pmar0 (Physaddr paLj5) 8 = Some region_lL5 ->
    (override_PMA (PMA_Region_attributes region_lL5) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj5) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj5) 8 = true ->
    is_aligned_paddr (Physaddr paLj5) 8 = true ->
    isRVC wL5 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL5) s0 = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 10)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj6) 4 = Some region_fL6 ->
    (override_PMA (PMA_Region_attributes region_fL6) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj6) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj6)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj6)) (Z.sub pagesize_bits 1) 0)) = a8Lj6 ->
    matching_pma_region pmar0 (Physaddr paLj6) 8 = Some region_lL6 ->
    (override_PMA (PMA_Region_attributes region_lL6) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj6) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj6) 8 = true ->
    is_aligned_paddr (Physaddr paLj6) 8 = true ->
    isRVC (subrange_vec_dec wL6 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL6 15 0)) s0 = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 11)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj7) 2 = Some region_fL7 ->
    (override_PMA (PMA_Region_attributes region_fL7) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj7) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj7)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj7)) (Z.sub pagesize_bits 1) 0)) = a8Lj7 ->
    matching_pma_region pmar0 (Physaddr paLj7) 8 = Some region_lL7 ->
    (override_PMA (PMA_Region_attributes region_lL7) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj7) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj7) 8 = true ->
    is_aligned_paddr (Physaddr paLj7) 8 = true ->
    isRVC wL7 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL7) s0 = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 12)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj8) 4 = Some region_fL8 ->
    (override_PMA (PMA_Region_attributes region_fL8) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj8) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj8)) (Z.sub pagesize_bits 1) 0)) = a8Lj8 ->
    matching_pma_region pmar0 (Physaddr paLj8) 8 = Some region_lL8 ->
    (override_PMA (PMA_Region_attributes region_lL8) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj8) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj8) 8 = true ->
    is_aligned_paddr (Physaddr paLj8) 8 = true ->
    isRVC (subrange_vec_dec wL8 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL8 15 0)) s0 = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 13)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj9) 2 = Some region_fL9 ->
    (override_PMA (PMA_Region_attributes region_fL9) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj9) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj9)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj9)) (Z.sub pagesize_bits 1) 0)) = a8Lj9 ->
    matching_pma_region pmar0 (Physaddr paLj9) 8 = Some region_lL9 ->
    (override_PMA (PMA_Region_attributes region_lL9) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj9) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj9) 8 = true ->
    is_aligned_paddr (Physaddr paLj9) 8 = true ->
    isRVC wL9 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL9) s0 = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 14)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj10) 4 = Some region_fL10 ->
    (override_PMA (PMA_Region_attributes region_fL10) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj10) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj10)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj10)) (Z.sub pagesize_bits 1) 0)) = a8Lj10 ->
    matching_pma_region pmar0 (Physaddr paLj10) 8 = Some region_lL10 ->
    (override_PMA (PMA_Region_attributes region_lL10) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj10) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj10) 8 = true ->
    is_aligned_paddr (Physaddr paLj10) 8 = true ->
    isRVC (subrange_vec_dec wL10 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL10 15 0)) s0 = Some (C_LDSP (mword_of_int 14, Regidx (mword_of_int 15)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj11) 2 = Some region_fL11 ->
    (override_PMA (PMA_Region_attributes region_fL11) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj11) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj11)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj11)) (Z.sub pagesize_bits 1) 0)) = a8Lj11 ->
    matching_pma_region pmar0 (Physaddr paLj11) 8 = Some region_lL11 ->
    (override_PMA (PMA_Region_attributes region_lL11) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj11) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj11) 8 = true ->
    is_aligned_paddr (Physaddr paLj11) 8 = true ->
    isRVC wL11 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL11) s0 = Some (C_LDSP (mword_of_int 15, Regidx (mword_of_int 16)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj12) 4 = Some region_fL12 ->
    (override_PMA (PMA_Region_attributes region_fL12) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj12) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj12)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj12)) (Z.sub pagesize_bits 1) 0)) = a8Lj12 ->
    matching_pma_region pmar0 (Physaddr paLj12) 8 = Some region_lL12 ->
    (override_PMA (PMA_Region_attributes region_lL12) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj12) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj12) 8 = true ->
    is_aligned_paddr (Physaddr paLj12) 8 = true ->
    isRVC (subrange_vec_dec wL12 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL12 15 0)) s0 = Some (C_LDSP (mword_of_int 16, Regidx (mword_of_int 17)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj13) 2 = Some region_fL13 ->
    (override_PMA (PMA_Region_attributes region_fL13) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj13) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj13)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj13)) (Z.sub pagesize_bits 1) 0)) = a8Lj13 ->
    matching_pma_region pmar0 (Physaddr paLj13) 8 = Some region_lL13 ->
    (override_PMA (PMA_Region_attributes region_lL13) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj13) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj13) 8 = true ->
    is_aligned_paddr (Physaddr paLj13) 8 = true ->
    isRVC wL13 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL13) s0 = Some (C_LDSP (mword_of_int 27, Regidx (mword_of_int 28)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj14) 4 = Some region_fL14 ->
    (override_PMA (PMA_Region_attributes region_fL14) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj14) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj14)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj14)) (Z.sub pagesize_bits 1) 0)) = a8Lj14 ->
    matching_pma_region pmar0 (Physaddr paLj14) 8 = Some region_lL14 ->
    (override_PMA (PMA_Region_attributes region_lL14) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj14) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj14) 8 = true ->
    is_aligned_paddr (Physaddr paLj14) 8 = true ->
    isRVC (subrange_vec_dec wL14 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL14 15 0)) s0 = Some (C_LDSP (mword_of_int 28, Regidx (mword_of_int 29)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj15) 2 = Some region_fL15 ->
    (override_PMA (PMA_Region_attributes region_fL15) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj15) (uint (to_bits 64 2)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj15)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj15)) (Z.sub pagesize_bits 1) 0)) = a8Lj15 ->
    matching_pma_region pmar0 (Physaddr paLj15) 8 = Some region_lL15 ->
    (override_PMA (PMA_Region_attributes region_lL15) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj15) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj15) 8 = true ->
    is_aligned_paddr (Physaddr paLj15) 8 = true ->
    isRVC wL15 = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wL15) s0 = Some (C_LDSP (mword_of_int 29, Regidx (mword_of_int 30)), s0)) ->
    matching_pma_region pmar0 (Physaddr vLj16) 4 = Some region_fL16 ->
    (override_PMA (PMA_Region_attributes region_fL16) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vLj16) (uint (to_bits 64 4)) = PMP_Match ->
    neq_vec (bits_of_virtaddr (Virtaddr a8Lj16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj16)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn) (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8Lj16)) (Z.sub pagesize_bits 1) 0)) = a8Lj16 ->
    matching_pma_region pmar0 (Physaddr paLj16) 8 = Some region_lL16 ->
    (override_PMA (PMA_Region_attributes region_lL16) PBMT_PMA).(PMA_readable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint paLj16) (uint (to_bits 64 8)) = PMP_Match ->
    is_aligned_vaddr (Virtaddr a8Lj16) 8 = true ->
    is_aligned_paddr (Physaddr paLj16) 8 = true ->
    isRVC (subrange_vec_dec wL16 15 0) = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed (subrange_vec_dec wL16 15 0)) s0 = Some (C_LDSP (mword_of_int 30, Regidx (mword_of_int 31)), s0)) ->
    matching_pma_region pmar0 (Physaddr vAj) 2 = Some region_A ->
    (override_PMA (PMA_Region_attributes region_A) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vAj) (uint (to_bits 64 2)) = PMP_Match ->
    isRVC wA = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true -> exec (ext_decode_compressed wA) s0 = Some (C_ADDI16SP immA, s0)) ->
    matching_pma_region pmar0 (Physaddr vSj) 4 = Some region_S ->
    (override_PMA (PMA_Region_attributes region_S) PBMT_PMA).(PMA_executable) = true ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4) (uint vSj) (uint (to_bits 64 4)) = PMP_Match ->
    isRVC (subrange_vec_dec wS 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Supervisor -> exec (ext_decode wS) s0 = Some (SRET tt, s0)) ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    (forall sz : mstate, exec (get_xLPE (sret_newpriv mstatus0)) sz = Some (lpe, sz)) ->
    vec_access_dec tlbf2 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    vec_access_dec tlbf2 (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    add_vec (sign_extend' 64 (caddi16sp_imm imm6)) (sign_extend' 64 (caddi16sp_imm immA)) = (mword_of_int 0 : mword 64) ->
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
    sepc ↦ᵣ sepc0 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vaj j) ↦ₘ nth_byte wj j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj0 j) ↦ₘ nth_byte wL0 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj1 j) ↦ₘ nth_byte wL1 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj2 j) ↦ₘ nth_byte wL2 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj3 j) ↦ₘ nth_byte wL3 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj4 j) ↦ₘ nth_byte wL4 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj5 j) ↦ₘ nth_byte wL5 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj6 j) ↦ₘ nth_byte wL6 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj7 j) ↦ₘ nth_byte wL7 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj8 j) ↦ₘ nth_byte wL8 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj9 j) ↦ₘ nth_byte wL9 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj10 j) ↦ₘ nth_byte wL10 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj11 j) ↦ₘ nth_byte wL11 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj12 j) ↦ₘ nth_byte wL12 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj13 j) ↦ₘ nth_byte wL13 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj14 j) ↦ₘ nth_byte wL14 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vLj15 j) ↦ₘ nth_byte wL15 j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vLj16 j) ↦ₘ nth_byte wL16 j) -∗
    ([∗ list] j ∈ seq 0 2, (pa_add vAj j) ↦ₘ nth_byte wA j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add vSj j) ↦ₘ nth_byte wS j) -∗
    ▷ ( ∀ (m' : gmap register_bitvector_64 (mword 64)) (npc' : mword 64),
        ⌜ m' !! gpr_of_Z 2 = Some (regval_into_reg spnew) ⌝ -∗ ⌜ dom m' = dom (<[gpr_of_Z 1 := regval_into_reg (add_vec_int vaj 4)]> (<[gpr_of_Z 2 := regval_into_reg spnew]> m)) ⌝ -∗
        PC ↦ᵣ sret_tgt sepc0 -∗
        gpr_file m -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ sret_tgt sepc0 -∗
        cur_privilege ↦ᵣ sret_newpriv mstatus0 -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ sret_ms5 mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbf2 -∗ mie ↦ᵣ mie_v -∗ sepc ↦ᵣ sepc0 -∗
        elp ↦ᵣ sret_elpv mstatus0 lpe -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros spnew a8 pa tlbf tlbf2 mst1 offset3 a8_3 pa3 mst2 mst3 offset4 a8_4 pa4 mst4 offset5 a8_5 pa5 mst5 offset6 a8_6 pa6 mst6 offset7 a8_7 pa7 mst7 offset8 a8_8 pa8 mst8 offset9 a8_9 pa9 mst9 offset10 a8_10 pa10 mst10 offset11 a8_11 pa11 mst11 offset12 a8_12 pa12 mst12 offset13 a8_13 pa13 mst13 offset14 a8_14 pa14 mst14 offset15 a8_15 pa15 mst15 offset16 a8_16 pa16 mst16 offset17 a8_17 pa17 mst17 offset18 a8_18 pa18 HN Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Halpte Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help Hgp Hvec5_2 Hvecst3 Hcanon3 Hvpndef3 Hident3 Hmask3 Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hr3f Hr3s Hal3v Hpal3 HisRVC3 Hdec3 Ht0 Hcanon4 Hvpndef4 Hident4 Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hr4f Hr4s Hal4v Hpal4 HisRVC4 Hdec4 Hgpr5 Hcanon5 Hvpndef5 Hident5 Hmatchf5 Hexecf5 Hmatchst5 Hwrite5 Hrf5 Hrs5 Halv5 Hzpal5 Hisrvc5 Hdec5 Hgpr6 Hcanon6 Hvpndef6 Hident6 Hmatchf6 Hexecf6 Hmatchst6 Hwrite6 Hrf6 Hrs6 Halv6 Hzpal6 Hisrvc6 Hdec6 Hgpr7 Hcanon7 Hvpndef7 Hident7 Hmatchf7 Hexecf7 Hmatchst7 Hwrite7 Hrf7 Hrs7 Halv7 Hzpal7 Hisrvc7 Hdec7 Hgpr8 Hcanon8 Hvpndef8 Hident8 Hmatchf8 Hexecf8 Hmatchst8 Hwrite8 Hrf8 Hrs8 Halv8 Hzpal8 Hisrvc8 Hdec8 Hgpr9 Hcanon9 Hvpndef9 Hident9 Hmatchf9 Hexecf9 Hmatchst9 Hwrite9 Hrf9 Hrs9 Halv9 Hzpal9 Hisrvc9 Hdec9 Hgpr10 Hcanon10 Hvpndef10 Hident10 Hmatchf10 Hexecf10 Hmatchst10 Hwrite10 Hrf10 Hrs10 Halv10 Hzpal10 Hisrvc10 Hdec10 Hgpr11 Hcanon11 Hvpndef11 Hident11 Hmatchf11 Hexecf11 Hmatchst11 Hwrite11 Hrf11 Hrs11 Halv11 Hzpal11 Hisrvc11 Hdec11 Hgpr12 Hcanon12 Hvpndef12 Hident12 Hmatchf12 Hexecf12 Hmatchst12 Hwrite12 Hrf12 Hrs12 Halv12 Hzpal12 Hisrvc12 Hdec12 Hgpr13 Hcanon13 Hvpndef13 Hident13 Hmatchf13 Hexecf13 Hmatchst13 Hwrite13 Hrf13 Hrs13 Halv13 Hzpal13 Hisrvc13 Hdec13 Hgpr14 Hcanon14 Hvpndef14 Hident14 Hmatchf14 Hexecf14 Hmatchst14 Hwrite14 Hrf14 Hrs14 Halv14 Hzpal14 Hisrvc14 Hdec14 Hgpr15 Hcanon15 Hvpndef15 Hident15 Hmatchf15 Hexecf15 Hmatchst15 Hwrite15 Hrf15 Hrs15 Halv15 Hzpal15 Hisrvc15 Hdec15 Hgpr16 Hcanon16 Hvpndef16 Hident16 Hmatchf16 Hexecf16 Hmatchst16 Hwrite16 Hrf16 Hrs16 Halv16 Hzpal16 Hisrvc16 Hdec16 Hgpr17 Hcanon17 Hvpndef17 Hident17 Hmatchf17 Hexecf17 Hmatchst17 Hwrite17 Hrf17 Hrs17 Halv17 Hzpal17 Hisrvc17 Hdec17 Hgpr18 Hcanon18 Hvpndef18 Hident18 Hmatchf18 Hexecf18 Hmatchst18 Hwrite18 Hrf18 Hrs18 Halv18 Hzpal18 Hisrvc18 Hdec18 vaj vLj0 vLj1 vLj2 vLj3 vLj4 vLj5 vLj6 vLj7 vLj8 vLj9 vLj10 vLj11 vLj12 vLj13 vLj14 vLj15 vLj16 vAj vSj offLj0 a8Lj0 paLj0 offLj1 a8Lj1 paLj1 offLj2 a8Lj2 paLj2 offLj3 a8Lj3 paLj3 offLj4 a8Lj4 paLj4 offLj5 a8Lj5 paLj5 offLj6 a8Lj6 paLj6 offLj7 a8Lj7 paLj7 offLj8 a8Lj8 paLj8 offLj9 a8Lj9 paLj9 offLj10 a8Lj10 paLj10 offLj11 a8Lj11 paLj11 offLj12 a8Lj12 paLj12 offLj13 a8Lj13 paLj13 offLj14 a8Lj14 paLj14 offLj15 a8Lj15 paLj15 offLj16 a8Lj16 paLj16 T6 T7 T8 T10 T11 T12 T13 T20 T21 T22 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T40 T41 T42 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T60 T61 T62 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T80 T81 T82 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T100 T101 T102 T104 T105 T106 T107 T108 T109 T110 T111 T112 T113 T120 T121 T122 T124 T125 T126 T127 T128 T129 T130 T131 T132 T133 T140 T141 T142 T144 T145 T146 T147 T148 T149 T150 T151 T152 T153 T160 T161 T162 T164 T165 T166 T167 T168 T169 T170 T171 T172 T173 T180 T181 T182 T184 T185 T186 T187 T188 T189 T190 T191 T192 T193 T200 T201 T202 T204 T205 T206 T207 T208 T209 T210 T211 T212 T213 T220 T221 T222 T224 T225 T226 T227 T228 T229 T230 T231 T232 T233 T240 T241 T242 T244 T245 T246 T247 T248 T249 T250 T251 T252 T253 T260 T261 T262 T264 T265 T266 T267 T268 T269 T270 T271 T272 T273 T280 T281 T282 T284 T285 T286 T287 T288 T289 T290 T291 T292 T293 T300 T301 T302 T304 T305 T306 T307 T308 T309 T310 T311 T312 T313 T320 T321 T322 T324 T325 T326 T327 T328 T329 T330 T331 T332 T333 T340 T341 T342 T344 T345 T346 T347 T348 T349 T350 T351 T352 T353 T360 T361 T362 T364 T365 T372 T373 T374 T376 T377 T378 T379 Htvec5 Htvecld Hmask_t Hcancel.
    assert (Hal4 : is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true) by (vm_compute; reflexivity).
    assert (Hal2 : is_aligned_paddr (Physaddr (mword_of_int 0x800053e2)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf3 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff3 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf3 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e4 : mword 64)) by (vm_compute; reflexivity).
    assert (Hal3f : is_aligned_paddr (Physaddr (mword_of_int 0x800053e4)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf4 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff4 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf4 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e6 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e6 : mword 64)) by (vm_compute; reflexivity).
    assert (Hal4f : is_aligned_paddr (Physaddr (mword_of_int 0x800053e6)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf5 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff5 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf5 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e8 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053e8 : mword 64)) by (vm_compute; reflexivity).
    assert (Half5 : is_aligned_paddr (Physaddr (mword_of_int 0x800053e8)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf6 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff6 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf6 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ea : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ea : mword 64)) by (vm_compute; reflexivity).
    assert (Half6 : is_aligned_paddr (Physaddr (mword_of_int 0x800053ea)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf7 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff7 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf7 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ec : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ec : mword 64)) by (vm_compute; reflexivity).
    assert (Half7 : is_aligned_paddr (Physaddr (mword_of_int 0x800053ec)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf8 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff8 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf8 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053ee : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053ee : mword 64)) by (vm_compute; reflexivity).
    assert (Half8 : is_aligned_paddr (Physaddr (mword_of_int 0x800053ee)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf9 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff9 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf9 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f0 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f0 : mword 64)) by (vm_compute; reflexivity).
    assert (Half9 : is_aligned_paddr (Physaddr (mword_of_int 0x800053f0)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf10 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff10 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf10 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f2 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f2 : mword 64)) by (vm_compute; reflexivity).
    assert (Half10 : is_aligned_paddr (Physaddr (mword_of_int 0x800053f2)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf11 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff11 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf11 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f4 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f4 : mword 64)) by (vm_compute; reflexivity).
    assert (Half11 : is_aligned_paddr (Physaddr (mword_of_int 0x800053f4)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf12 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff12 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf12 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f6 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f6 : mword 64)) by (vm_compute; reflexivity).
    assert (Half12 : is_aligned_paddr (Physaddr (mword_of_int 0x800053f6)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf13 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff13 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf13 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053f8 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053f8 : mword 64)) by (vm_compute; reflexivity).
    assert (Half13 : is_aligned_paddr (Physaddr (mword_of_int 0x800053f8)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf14 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff14 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf14 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fa : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fa : mword 64)) by (vm_compute; reflexivity).
    assert (Half14 : is_aligned_paddr (Physaddr (mword_of_int 0x800053fa)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf15 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff15 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf15 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fc : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fc : mword 64)) by (vm_compute; reflexivity).
    assert (Half15 : is_aligned_paddr (Physaddr (mword_of_int 0x800053fc)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf16 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff16 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf16 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053fe : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x800053fe : mword 64)) by (vm_compute; reflexivity).
    assert (Half16 : is_aligned_paddr (Physaddr (mword_of_int 0x800053fe)) 2 = true) by (vm_compute; reflexivity).
    assert (Hcanonf17 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff17 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf17 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005400 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x80005400 : mword 64)) by (vm_compute; reflexivity).
    assert (Half17 : is_aligned_paddr (Physaddr (mword_of_int 0x80005400)) 4 = true) by (vm_compute; reflexivity).
    assert (Hcanonf18 : neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (Hvpndeff18 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (Hidentf18 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x80005402 : mword 64))) (Z.sub pagesize_bits 1) 0)) = (mword_of_int 0x80005402 : mword 64)) by (vm_compute; reflexivity).
    assert (Half18 : is_aligned_paddr (Physaddr (mword_of_int 0x80005402)) 2 = true) by (vm_compute; reflexivity).
    assert (T0 : neq_vec (bits_of_virtaddr (Virtaddr vaj)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vaj)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T1 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vaj)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T2 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vaj)) (Z.sub pagesize_bits 1) 0)) = vaj) by (vm_compute; reflexivity).
    assert (T3 : neq_vec (access_vec_dec vaj 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T4 : neq_vec (access_vec_dec vaj 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T5 : is_aligned_vaddr (Virtaddr vaj) 4 = true) by (vm_compute; reflexivity).
    assert (T9 : is_aligned_paddr (Physaddr vaj) 4 = true) by (vm_compute; reflexivity).
    assert (T14 : neq_vec (bits_of_virtaddr (Virtaddr vLj0)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj0)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T15 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj0)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T16 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj0)) (Z.sub pagesize_bits 1) 0)) = vLj0) by (vm_compute; reflexivity).
    assert (T17 : neq_vec (access_vec_dec vLj0 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T18 : neq_vec (access_vec_dec vLj0 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T19 : is_aligned_vaddr (Virtaddr vLj0) 4 = true) by (vm_compute; reflexivity).
    assert (T23 : is_aligned_paddr (Physaddr vLj0) 4 = true) by (vm_compute; reflexivity).
    assert (T34 : neq_vec (bits_of_virtaddr (Virtaddr vLj1)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj1)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T35 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj1)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T36 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj1)) (Z.sub pagesize_bits 1) 0)) = vLj1) by (vm_compute; reflexivity).
    assert (T37 : neq_vec (access_vec_dec vLj1 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T38 : neq_vec (access_vec_dec vLj1 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T39 : is_aligned_vaddr (Virtaddr vLj1) 4 = false) by (vm_compute; reflexivity).
    assert (T43 : is_aligned_paddr (Physaddr vLj1) 2 = true) by (vm_compute; reflexivity).
    assert (T54 : neq_vec (bits_of_virtaddr (Virtaddr vLj2)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj2)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T55 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj2)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T56 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj2)) (Z.sub pagesize_bits 1) 0)) = vLj2) by (vm_compute; reflexivity).
    assert (T57 : neq_vec (access_vec_dec vLj2 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T58 : neq_vec (access_vec_dec vLj2 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T59 : is_aligned_vaddr (Virtaddr vLj2) 4 = true) by (vm_compute; reflexivity).
    assert (T63 : is_aligned_paddr (Physaddr vLj2) 4 = true) by (vm_compute; reflexivity).
    assert (T74 : neq_vec (bits_of_virtaddr (Virtaddr vLj3)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj3)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T75 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj3)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T76 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj3)) (Z.sub pagesize_bits 1) 0)) = vLj3) by (vm_compute; reflexivity).
    assert (T77 : neq_vec (access_vec_dec vLj3 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T78 : neq_vec (access_vec_dec vLj3 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T79 : is_aligned_vaddr (Virtaddr vLj3) 4 = false) by (vm_compute; reflexivity).
    assert (T83 : is_aligned_paddr (Physaddr vLj3) 2 = true) by (vm_compute; reflexivity).
    assert (T94 : neq_vec (bits_of_virtaddr (Virtaddr vLj4)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj4)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T95 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj4)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T96 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj4)) (Z.sub pagesize_bits 1) 0)) = vLj4) by (vm_compute; reflexivity).
    assert (T97 : neq_vec (access_vec_dec vLj4 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T98 : neq_vec (access_vec_dec vLj4 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T99 : is_aligned_vaddr (Virtaddr vLj4) 4 = true) by (vm_compute; reflexivity).
    assert (T103 : is_aligned_paddr (Physaddr vLj4) 4 = true) by (vm_compute; reflexivity).
    assert (T114 : neq_vec (bits_of_virtaddr (Virtaddr vLj5)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj5)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T115 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj5)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T116 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj5)) (Z.sub pagesize_bits 1) 0)) = vLj5) by (vm_compute; reflexivity).
    assert (T117 : neq_vec (access_vec_dec vLj5 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T118 : neq_vec (access_vec_dec vLj5 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T119 : is_aligned_vaddr (Virtaddr vLj5) 4 = false) by (vm_compute; reflexivity).
    assert (T123 : is_aligned_paddr (Physaddr vLj5) 2 = true) by (vm_compute; reflexivity).
    assert (T134 : neq_vec (bits_of_virtaddr (Virtaddr vLj6)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj6)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T135 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj6)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T136 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj6)) (Z.sub pagesize_bits 1) 0)) = vLj6) by (vm_compute; reflexivity).
    assert (T137 : neq_vec (access_vec_dec vLj6 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T138 : neq_vec (access_vec_dec vLj6 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T139 : is_aligned_vaddr (Virtaddr vLj6) 4 = true) by (vm_compute; reflexivity).
    assert (T143 : is_aligned_paddr (Physaddr vLj6) 4 = true) by (vm_compute; reflexivity).
    assert (T154 : neq_vec (bits_of_virtaddr (Virtaddr vLj7)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj7)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T155 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj7)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T156 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj7)) (Z.sub pagesize_bits 1) 0)) = vLj7) by (vm_compute; reflexivity).
    assert (T157 : neq_vec (access_vec_dec vLj7 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T158 : neq_vec (access_vec_dec vLj7 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T159 : is_aligned_vaddr (Virtaddr vLj7) 4 = false) by (vm_compute; reflexivity).
    assert (T163 : is_aligned_paddr (Physaddr vLj7) 2 = true) by (vm_compute; reflexivity).
    assert (T174 : neq_vec (bits_of_virtaddr (Virtaddr vLj8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj8)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T175 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T176 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj8)) (Z.sub pagesize_bits 1) 0)) = vLj8) by (vm_compute; reflexivity).
    assert (T177 : neq_vec (access_vec_dec vLj8 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T178 : neq_vec (access_vec_dec vLj8 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T179 : is_aligned_vaddr (Virtaddr vLj8) 4 = true) by (vm_compute; reflexivity).
    assert (T183 : is_aligned_paddr (Physaddr vLj8) 4 = true) by (vm_compute; reflexivity).
    assert (T194 : neq_vec (bits_of_virtaddr (Virtaddr vLj9)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj9)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T195 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj9)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T196 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj9)) (Z.sub pagesize_bits 1) 0)) = vLj9) by (vm_compute; reflexivity).
    assert (T197 : neq_vec (access_vec_dec vLj9 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T198 : neq_vec (access_vec_dec vLj9 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T199 : is_aligned_vaddr (Virtaddr vLj9) 4 = false) by (vm_compute; reflexivity).
    assert (T203 : is_aligned_paddr (Physaddr vLj9) 2 = true) by (vm_compute; reflexivity).
    assert (T214 : neq_vec (bits_of_virtaddr (Virtaddr vLj10)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj10)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T215 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj10)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T216 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj10)) (Z.sub pagesize_bits 1) 0)) = vLj10) by (vm_compute; reflexivity).
    assert (T217 : neq_vec (access_vec_dec vLj10 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T218 : neq_vec (access_vec_dec vLj10 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T219 : is_aligned_vaddr (Virtaddr vLj10) 4 = true) by (vm_compute; reflexivity).
    assert (T223 : is_aligned_paddr (Physaddr vLj10) 4 = true) by (vm_compute; reflexivity).
    assert (T234 : neq_vec (bits_of_virtaddr (Virtaddr vLj11)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj11)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T235 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj11)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T236 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj11)) (Z.sub pagesize_bits 1) 0)) = vLj11) by (vm_compute; reflexivity).
    assert (T237 : neq_vec (access_vec_dec vLj11 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T238 : neq_vec (access_vec_dec vLj11 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T239 : is_aligned_vaddr (Virtaddr vLj11) 4 = false) by (vm_compute; reflexivity).
    assert (T243 : is_aligned_paddr (Physaddr vLj11) 2 = true) by (vm_compute; reflexivity).
    assert (T254 : neq_vec (bits_of_virtaddr (Virtaddr vLj12)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj12)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T255 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj12)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T256 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj12)) (Z.sub pagesize_bits 1) 0)) = vLj12) by (vm_compute; reflexivity).
    assert (T257 : neq_vec (access_vec_dec vLj12 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T258 : neq_vec (access_vec_dec vLj12 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T259 : is_aligned_vaddr (Virtaddr vLj12) 4 = true) by (vm_compute; reflexivity).
    assert (T263 : is_aligned_paddr (Physaddr vLj12) 4 = true) by (vm_compute; reflexivity).
    assert (T274 : neq_vec (bits_of_virtaddr (Virtaddr vLj13)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj13)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T275 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj13)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T276 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj13)) (Z.sub pagesize_bits 1) 0)) = vLj13) by (vm_compute; reflexivity).
    assert (T277 : neq_vec (access_vec_dec vLj13 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T278 : neq_vec (access_vec_dec vLj13 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T279 : is_aligned_vaddr (Virtaddr vLj13) 4 = false) by (vm_compute; reflexivity).
    assert (T283 : is_aligned_paddr (Physaddr vLj13) 2 = true) by (vm_compute; reflexivity).
    assert (T294 : neq_vec (bits_of_virtaddr (Virtaddr vLj14)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj14)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T295 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj14)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T296 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj14)) (Z.sub pagesize_bits 1) 0)) = vLj14) by (vm_compute; reflexivity).
    assert (T297 : neq_vec (access_vec_dec vLj14 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T298 : neq_vec (access_vec_dec vLj14 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T299 : is_aligned_vaddr (Virtaddr vLj14) 4 = true) by (vm_compute; reflexivity).
    assert (T303 : is_aligned_paddr (Physaddr vLj14) 4 = true) by (vm_compute; reflexivity).
    assert (T314 : neq_vec (bits_of_virtaddr (Virtaddr vLj15)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj15)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T315 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj15)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T316 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj15)) (Z.sub pagesize_bits 1) 0)) = vLj15) by (vm_compute; reflexivity).
    assert (T317 : neq_vec (access_vec_dec vLj15 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T318 : neq_vec (access_vec_dec vLj15 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T319 : is_aligned_vaddr (Virtaddr vLj15) 4 = false) by (vm_compute; reflexivity).
    assert (T323 : is_aligned_paddr (Physaddr vLj15) 2 = true) by (vm_compute; reflexivity).
    assert (T334 : neq_vec (bits_of_virtaddr (Virtaddr vLj16)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj16)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T335 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj16)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T336 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vLj16)) (Z.sub pagesize_bits 1) 0)) = vLj16) by (vm_compute; reflexivity).
    assert (T337 : neq_vec (access_vec_dec vLj16 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T338 : neq_vec (access_vec_dec vLj16 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T339 : is_aligned_vaddr (Virtaddr vLj16) 4 = true) by (vm_compute; reflexivity).
    assert (T343 : is_aligned_paddr (Physaddr vLj16) 4 = true) by (vm_compute; reflexivity).
    assert (T354 : neq_vec (bits_of_virtaddr (Virtaddr vAj)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vAj)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T355 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vAj)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T356 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vAj)) (Z.sub pagesize_bits 1) 0)) = vAj) by (vm_compute; reflexivity).
    assert (T357 : neq_vec (access_vec_dec vAj 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T358 : neq_vec (access_vec_dec vAj 1) ('b"0") = true) by (vm_compute; reflexivity).
    assert (T359 : is_aligned_vaddr (Virtaddr vAj) 4 = false) by (vm_compute; reflexivity).
    assert (T363 : is_aligned_paddr (Physaddr vAj) 2 = true) by (vm_compute; reflexivity).
    assert (T366 : neq_vec (bits_of_virtaddr (Virtaddr vSj)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vSj)) (Z.sub 39 1) 0)) = false) by (vm_compute; reflexivity).
    assert (T367 : autocast (T := mword) (subrange_vec_dec (subrange_vec_dec (bits_of_virtaddr (Virtaddr vSj)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn) by (vm_compute; reflexivity).
    assert (T368 : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44) (subrange_vec_dec (bits_of_virtaddr (Virtaddr vSj)) (Z.sub pagesize_bits 1) 0)) = vSj) by (vm_compute; reflexivity).
    assert (T369 : neq_vec (access_vec_dec vSj 0) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T370 : neq_vec (access_vec_dec vSj 1) ('b"0") = false) by (vm_compute; reflexivity).
    assert (T371 : is_aligned_vaddr (Virtaddr vSj) 4 = true) by (vm_compute; reflexivity).
    assert (T375 : is_aligned_paddr (Physaddr vSj) 4 = true) by (vm_compute; reflexivity).
    iIntros "Hpc Hfile Hmisa Hnpc #Hinv Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hib3 Hstack3 Hib4 Hstack4 Hib5 Hstack5 Hib6 Hstack6 Hib7 Hstack7 Hib8 Hstack8 Hib9 Hstack9 Hib10 Hstack10 Hib11 Hstack11 Hib12 Hstack12 Hib13 Hstack13 Hib14 Hstack14 Hib15 Hstack15 Hib16 Hstack16 Hib17 Hstack17 Hib18 Hstack18 Hsepc Hjb Hlb0 Hlb1 Hlb2 Hlb3 Hlb4 Hlb5 Hlb6 Hlb7 Hlb8 Hlb9 Hlb10 Hlb11 Hlb12 Hlb13 Hlb14 Hlb15 Hlb16 Hab Hsb Hcont".
    iApply (wp_kernelvec_stores root_ppn w1 imm6 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 vpn m vsp vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v b1 npc0 mst0 mc mcfg pmpcfg0 pmpaddr00 pmar0 mi0 elp0 tlbvec region_pte region_st region_f2 region_f3 region_st3 region_f4 region_st4 region_f5 region_st5 region_f6 region_st6 region_f7 region_st7 region_f8 region_st8 region_f9 region_st9 region_f10 region_st10 region_f11 region_st11 region_f12 region_st12 region_f13 region_st13 region_f14 region_st14 region_f15 region_st15 region_f16 region_st16 region_f17 region_st17 region_f18 region_st18 vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 vold18 E Phi HN Hsp Hra HSXL Hmode Hppn Hasid Hvec Hvecst Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn Hpmaall Hmatchp Hpte Hmatchf2 Hexecf2 Hmatchst Hwrite HPBMTE Hpmm HA0 Hord0 Hr1 Hrpte Hr2 Hrst HX0 HR0 HW0 Hal4 Halpte Hal2 Hal8 Hpal8 HisRVC1 HisRVC2 HmisaC HmisaS HMPRV HMXR Hdec1 Hdec2 Hb1 Hmie_mdl HSIE Help Hgp Hvec5_2 Hvecst3 Hcanonf3 Hvpndeff3 Hidentf3 Hcanon3 Hvpndef3 Hident3 Hmask3 Hmatchf3 Hexecf3 Hmatchst3 Hwrite3 Hr3f Hr3s Hal3f Hal3v Hpal3 HisRVC3 Hdec3 Ht0 Hcanonf4 Hvpndeff4 Hidentf4 Hcanon4 Hvpndef4 Hident4 Hmatchf4 Hexecf4 Hmatchst4 Hwrite4 Hr4f Hr4s Hal4f Hal4v Hpal4 HisRVC4 Hdec4 Hgpr5 Hcanonf5 Hvpndeff5 Hidentf5 Hcanon5 Hvpndef5 Hident5 Hmatchf5 Hexecf5 Hmatchst5 Hwrite5 Hrf5 Hrs5 Half5 Halv5 Hzpal5 Hisrvc5 Hdec5 Hgpr6 Hcanonf6 Hvpndeff6 Hidentf6 Hcanon6 Hvpndef6 Hident6 Hmatchf6 Hexecf6 Hmatchst6 Hwrite6 Hrf6 Hrs6 Half6 Halv6 Hzpal6 Hisrvc6 Hdec6 Hgpr7 Hcanonf7 Hvpndeff7 Hidentf7 Hcanon7 Hvpndef7 Hident7 Hmatchf7 Hexecf7 Hmatchst7 Hwrite7 Hrf7 Hrs7 Half7 Halv7 Hzpal7 Hisrvc7 Hdec7 Hgpr8 Hcanonf8 Hvpndeff8 Hidentf8 Hcanon8 Hvpndef8 Hident8 Hmatchf8 Hexecf8 Hmatchst8 Hwrite8 Hrf8 Hrs8 Half8 Halv8 Hzpal8 Hisrvc8 Hdec8 Hgpr9 Hcanonf9 Hvpndeff9 Hidentf9 Hcanon9 Hvpndef9 Hident9 Hmatchf9 Hexecf9 Hmatchst9 Hwrite9 Hrf9 Hrs9 Half9 Halv9 Hzpal9 Hisrvc9 Hdec9 Hgpr10 Hcanonf10 Hvpndeff10 Hidentf10 Hcanon10 Hvpndef10 Hident10 Hmatchf10 Hexecf10 Hmatchst10 Hwrite10 Hrf10 Hrs10 Half10 Halv10 Hzpal10 Hisrvc10 Hdec10 Hgpr11 Hcanonf11 Hvpndeff11 Hidentf11 Hcanon11 Hvpndef11 Hident11 Hmatchf11 Hexecf11 Hmatchst11 Hwrite11 Hrf11 Hrs11 Half11 Halv11 Hzpal11 Hisrvc11 Hdec11 Hgpr12 Hcanonf12 Hvpndeff12 Hidentf12 Hcanon12 Hvpndef12 Hident12 Hmatchf12 Hexecf12 Hmatchst12 Hwrite12 Hrf12 Hrs12 Half12 Halv12 Hzpal12 Hisrvc12 Hdec12 Hgpr13 Hcanonf13 Hvpndeff13 Hidentf13 Hcanon13 Hvpndef13 Hident13 Hmatchf13 Hexecf13 Hmatchst13 Hwrite13 Hrf13 Hrs13 Half13 Halv13 Hzpal13 Hisrvc13 Hdec13 Hgpr14 Hcanonf14 Hvpndeff14 Hidentf14 Hcanon14 Hvpndef14 Hident14 Hmatchf14 Hexecf14 Hmatchst14 Hwrite14 Hrf14 Hrs14 Half14 Halv14 Hzpal14 Hisrvc14 Hdec14 Hgpr15 Hcanonf15 Hvpndeff15 Hidentf15 Hcanon15 Hvpndef15 Hident15 Hmatchf15 Hexecf15 Hmatchst15 Hwrite15 Hrf15 Hrs15 Half15 Halv15 Hzpal15 Hisrvc15 Hdec15 Hgpr16 Hcanonf16 Hvpndeff16 Hidentf16 Hcanon16 Hvpndef16 Hident16 Hmatchf16 Hexecf16 Hmatchst16 Hwrite16 Hrf16 Hrs16 Half16 Halv16 Hzpal16 Hisrvc16 Hdec16 Hgpr17 Hcanonf17 Hvpndeff17 Hidentf17 Hcanon17 Hvpndef17 Hident17 Hmatchf17 Hexecf17 Hmatchst17 Hwrite17 Hrf17 Hrs17 Half17 Halv17 Hzpal17 Hisrvc17 Hdec17 Hgpr18 Hcanonf18 Hvpndeff18 Hidentf18 Hcanon18 Hvpndef18 Hident18 Hmatchf18 Hexecf18 Hmatchst18 Hwrite18 Hrf18 Hrs18 Half18 Halv18 Hzpal18 Hisrvc18 Hdec18 with "Hpc Hfile Hmisa Hnpc Hinv Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hpbytes Hib1 Hib2 Hstack Hib3 Hstack3 Hib4 Hstack4 Hib5 Hstack5 Hib6 Hstack6 Hib7 Hstack7 Hib8 Hstack8 Hib9 Hstack9 Hib10 Hstack10 Hib11 Hstack11 Hib12 Hstack12 Hib13 Hstack13 Hib14 Hstack14 Hib15 Hstack15 Hib16 Hstack16 Hib17 Hstack17 Hib18 Hstack18").
    iNext.
    iIntros "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help2 Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hstack Hstack3 Hstack4 Hstack5 Hstack6 Hstack7 Hstack8 Hstack9 Hstack10 Hstack11 Hstack12 Hstack13 Hstack14 Hstack15 Hstack16 Hstack17 Hstack18 Hpbytes Hib2 Hib3 Hib4 Hib5 Hib6 Hib7 Hib8 Hib9 Hib10 Hib11 Hib12 Hib13 Hib14 Hib15 Hib16 Hib17 Hib18".
    assert (HspT : (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 2 = Some (regval_into_reg spnew)) by (rewrite lookup_insert; reflexivity).
    assert (HraT : (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 1 = Some vra) by (rewrite lookup_insert_ne; [exact Hra | vm_compute; discriminate]).
    assert (HorT1 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 1 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hra | vm_compute; discriminate]).
    assert (HorT3 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 3 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgp | vm_compute; discriminate]).
    assert (HorT5 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 5 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Ht0 | vm_compute; discriminate]).
    assert (HorT6 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 6 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr5 | vm_compute; discriminate]).
    assert (HorT7 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 7 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr6 | vm_compute; discriminate]).
    assert (HorT10 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 10 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr7 | vm_compute; discriminate]).
    assert (HorT11 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 11 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr8 | vm_compute; discriminate]).
    assert (HorT12 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 12 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr9 | vm_compute; discriminate]).
    assert (HorT13 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 13 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr10 | vm_compute; discriminate]).
    assert (HorT14 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 14 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr11 | vm_compute; discriminate]).
    assert (HorT15 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 15 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr12 | vm_compute; discriminate]).
    assert (HorT16 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 16 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr13 | vm_compute; discriminate]).
    assert (HorT17 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 17 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr14 | vm_compute; discriminate]).
    assert (HorT28 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 28 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr15 | vm_compute; discriminate]).
    assert (HorT29 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 29 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr16 | vm_compute; discriminate]).
    assert (HorT30 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 30 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr17 | vm_compute; discriminate]).
    assert (HorT31 : exists vo, (<[gpr_of_Z 2 := regval_into_reg spnew]> m) !! gpr_of_Z 31 = Some vo) by (eexists; rewrite lookup_insert_ne; [exact Hgpr18 | vm_compute; discriminate]).
    iApply (wp_kernelvec_tail root_ppn vaj wj imm wL0 wL1 wL2 wL3 wL4 wL5 wL6 wL7 wL8 wL9 wL10 wL11 wL12 wL13 wL14 wL15 wL16 wA immA wS vpn (<[gpr_of_Z 2 := regval_into_reg spnew]> m) (regval_into_reg spnew) vra misa0 mdv0 mstatus0 menvcfg0 mseccfg0 satp0 mie_v sepc0 b1 lpe vaj mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbf2 region_j region_A region_S region_fL0 region_fL1 region_fL2 region_fL3 region_fL4 region_fL5 region_fL6 region_fL7 region_fL8 region_fL9 region_fL10 region_fL11 region_fL12 region_fL13 region_fL14 region_fL15 region_fL16 region_lL0 region_lL1 region_lL2 region_lL3 region_lL4 region_lL5 region_lL6 region_lL7 region_lL8 region_lL9 region_lL10 region_lL11 region_lL12 region_lL13 region_lL14 region_lL15 region_lL16 vra vgp vt0 vR5 vR6 vR7 vR8 vR9 vR10 vR11 vR12 vR13 vR14 vR15 vR16 vR17 vR18 E Phi with "Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmenv Hsec Hmie Help2 Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hsepc Hjb Hstack Hstack3 Hstack4 Hstack5 Hstack6 Hstack7 Hstack8 Hstack9 Hstack10 Hstack11 Hstack12 Hstack13 Hstack14 Hstack15 Hstack16 Hstack17 Hstack18 Hlb0 Hlb1 Hlb2 Hlb3 Hlb4 Hlb5 Hlb6 Hlb7 Hlb8 Hlb9 Hlb10 Hlb11 Hlb12 Hlb13 Hlb14 Hlb15 Hlb16 Hab Hsb").
    exact HN. exact HspT. exact HraT. exact HorT1. exact HorT3. exact HorT5. exact HorT6. exact HorT7. exact HorT10. exact HorT11. exact HorT12. exact HorT13. exact HorT14. exact HorT15. exact HorT16. exact HorT17. exact HorT28. exact HorT29. exact HorT30. exact HorT31. exact HSXL. exact Hmode. exact Hasid. exact Htvec5. exact Htvecld. exact Hmask_t. exact Hpmm. exact HA0. exact Hord0. exact HX0. exact HR0. exact HmisaC. exact HmisaS. exact HMPRV. exact HMXR. exact Hb1. exact Hmie_mdl. exact HSIE. exact Help. exact T378. exact T379. exact T0. exact T1. exact T2. exact T3. exact T4. exact T5. exact T6. exact T7. exact T8. exact T9. exact T10. exact T11. exact T12. exact T13. exact T14. exact T15. exact T16. exact T17. exact T18. exact T19. exact T24. exact T25. exact T26. exact T20. exact T21. exact T27. exact T28. exact T22. exact T29. exact T23. exact T30. exact T31. exact T32. exact T33. exact T34. exact T35. exact T36. exact T37. exact T38. exact T39. exact T44. exact T45. exact T46. exact T40. exact T41. exact T47. exact T48. exact T42. exact T49. exact T43. exact T50. exact T51. exact T52. exact T53. exact T54. exact T55. exact T56. exact T57. exact T58. exact T59. exact T64. exact T65. exact T66. exact T60. exact T61. exact T67. exact T68. exact T62. exact T69. exact T63. exact T70. exact T71. exact T72. exact T73. exact T74. exact T75. exact T76. exact T77. exact T78. exact T79. exact T84. exact T85. exact T86. exact T80. exact T81. exact T87. exact T88. exact T82. exact T89. exact T83. exact T90. exact T91. exact T92. exact T93. exact T94. exact T95. exact T96. exact T97. exact T98. exact T99. exact T104. exact T105. exact T106. exact T100. exact T101. exact T107. exact T108. exact T102. exact T109. exact T103. exact T110. exact T111. exact T112. exact T113. exact T114. exact T115. exact T116. exact T117. exact T118. exact T119. exact T124. exact T125. exact T126. exact T120. exact T121. exact T127. exact T128. exact T122. exact T129. exact T123. exact T130. exact T131. exact T132. exact T133. exact T134. exact T135. exact T136. exact T137. exact T138. exact T139. exact T144. exact T145. exact T146. exact T140. exact T141. exact T147. exact T148. exact T142. exact T149. exact T143. exact T150. exact T151. exact T152. exact T153. exact T154. exact T155. exact T156. exact T157. exact T158. exact T159. exact T164. exact T165. exact T166. exact T160. exact T161. exact T167. exact T168. exact T162. exact T169. exact T163. exact T170. exact T171. exact T172. exact T173. exact T174. exact T175. exact T176. exact T177. exact T178. exact T179. exact T184. exact T185. exact T186. exact T180. exact T181. exact T187. exact T188. exact T182. exact T189. exact T183. exact T190. exact T191. exact T192. exact T193. exact T194. exact T195. exact T196. exact T197. exact T198. exact T199. exact T204. exact T205. exact T206. exact T200. exact T201. exact T207. exact T208. exact T202. exact T209. exact T203. exact T210. exact T211. exact T212. exact T213. exact T214. exact T215. exact T216. exact T217. exact T218. exact T219. exact T224. exact T225. exact T226. exact T220. exact T221. exact T227. exact T228. exact T222. exact T229. exact T223. exact T230. exact T231. exact T232. exact T233. exact T234. exact T235. exact T236. exact T237. exact T238. exact T239. exact T244. exact T245. exact T246. exact T240. exact T241. exact T247. exact T248. exact T242. exact T249. exact T243. exact T250. exact T251. exact T252. exact T253. exact T254. exact T255. exact T256. exact T257. exact T258. exact T259. exact T264. exact T265. exact T266. exact T260. exact T261. exact T267. exact T268. exact T262. exact T269. exact T263. exact T270. exact T271. exact T272. exact T273. exact T274. exact T275. exact T276. exact T277. exact T278. exact T279. exact T284. exact T285. exact T286. exact T280. exact T281. exact T287. exact T288. exact T282. exact T289. exact T283. exact T290. exact T291. exact T292. exact T293. exact T294. exact T295. exact T296. exact T297. exact T298. exact T299. exact T304. exact T305. exact T306. exact T300. exact T301. exact T307. exact T308. exact T302. exact T309. exact T303. exact T310. exact T311. exact T312. exact T313. exact T314. exact T315. exact T316. exact T317. exact T318. exact T319. exact T324. exact T325. exact T326. exact T320. exact T321. exact T327. exact T328. exact T322. exact T329. exact T323. exact T330. exact T331. exact T332. exact T333. exact T334. exact T335. exact T336. exact T337. exact T338. exact T339. exact T344. exact T345. exact T346. exact T340. exact T341. exact T347. exact T348. exact T342. exact T349. exact T343. exact T350. exact T351. exact T352. exact T353. exact T354. exact T355. exact T356. exact T357. exact T358. exact T359. exact T360. exact T361. exact T362. exact T363. exact T364. exact T365. exact T366. exact T367. exact T368. exact T369. exact T370. exact T371. exact T372. exact T373. exact T374. exact T375. exact T376. exact T377.
    iNext.
    iIntros (mm npc2) "%Hsp2 %Hdom2 %Hpres2 Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Hhelp Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hjb2 Hcc0 Hcc1 Hcc2 Hcc3 Hcc4 Hcc5 Hcc6 Hcc7 Hcc8 Hcc9 Hcc10 Hcc11 Hcc12 Hcc13 Hcc14 Hcc15 Hcc16 Hll0 Hll1 Hll2 Hll3 Hll4 Hll5 Hll6 Hll7 Hll8 Hll9 Hll10 Hll11 Hll12 Hll13 Hll14 Hll15 Hll16 Hab2 Hsb2".
    assert (Hspnew : spnew = add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6))) by reflexivity.
    assert (Hbig : (<[gpr_of_Z 2 := regval_into_reg (add_vec (regval_into_reg spnew) (sign_extend' 64 (caddi16sp_imm immA)))]>(<[gpr_of_Z 31 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR18))]>(<[gpr_of_Z 30 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR17))]>(<[gpr_of_Z 29 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR16))]>(<[gpr_of_Z 28 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR15))]>(<[gpr_of_Z 17 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR14))]>(<[gpr_of_Z 16 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR13))]>(<[gpr_of_Z 15 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR12))]>(<[gpr_of_Z 14 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR11))]>(<[gpr_of_Z 13 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR10))]>(<[gpr_of_Z 12 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR9))]>(<[gpr_of_Z 11 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR8))]>(<[gpr_of_Z 10 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR7))]>(<[gpr_of_Z 7 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR6))]>(<[gpr_of_Z 6 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vR5))]>(<[gpr_of_Z 5 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vt0))]>(<[gpr_of_Z 3 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vgp))]>(<[gpr_of_Z 1 := regval_into_reg (extend_value false (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) vra))]> mm)))))))))))))))))) = m).
    { clear - Hsp Hra Hgp Ht0 Hgpr5 Hgpr6 Hgpr7 Hgpr8 Hgpr9 Hgpr10 Hgpr11 Hgpr12 Hgpr13 Hgpr14 Hgpr15 Hgpr16 Hgpr17 Hgpr18 Hpres2 Hcancel Hspnew.
      unfold regval_into_reg. rewrite !kvP_loadrt.
      rewrite Hspnew kvP_addv_assoc Hcancel kvP_addv_zero.
      apply map_eq. intros i.
      destruct (decide (i ∈ ({[ gpr_of_Z 1 ; gpr_of_Z 2 ; gpr_of_Z 3 ; gpr_of_Z 5 ; gpr_of_Z 6 ; gpr_of_Z 7 ; gpr_of_Z 10 ; gpr_of_Z 11 ; gpr_of_Z 12 ; gpr_of_Z 13 ; gpr_of_Z 14 ; gpr_of_Z 15 ; gpr_of_Z 16 ; gpr_of_Z 17 ; gpr_of_Z 28 ; gpr_of_Z 29 ; gpr_of_Z 30 ; gpr_of_Z 31 ]} : gset register_bitvector_64))) as [Hin|Hout].
      - revert Hin. rewrite !elem_of_union !elem_of_singleton. intros Hin.
        repeat match goal with HH : _ ∨ _ |- _ => destruct HH end;
          subst i; repeat (rewrite lookup_insert_ne; [| vm_compute; discriminate]);
          rewrite lookup_insert; symmetry; assumption.
      - repeat (rewrite lookup_insert_ne; [| intros Heq; apply Hout; rewrite <- Heq; set_solver]).
        (* Hpres2 relates mm to the prologue-updated <[gpr2:=spnew]> m; peel that gpr2 too. *)
        rewrite (Hpres2 i);
          [ rewrite lookup_insert_ne; [reflexivity | intros Heq; apply Hout; rewrite <- Heq; set_solver]
          | set_solver ]. }
    iEval (rewrite Hbig) in "Hfile".
    iApply ("Hcont" $! mm npc2 with "[%] [%] Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Hsepc Hhelp Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif").
    { exact Hsp2. }
    { exact Hdom2. }
  Qed.
End KVALL.

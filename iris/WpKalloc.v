(* WpKalloc.v -- instruction-level proof of the kernel's [kalloc] (0x80000b20)
   and [kfree] (0x80000a38) against the allocator spec in KallocInv.v.

   kalloc/kfree are whole-function S-mode proofs in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): they thread the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALL the sub-functions acquire / release / memset via [jal], discharging each
   callee's whole-function WP.  The novel content is the free-list manipulation,
   which is discharged by KallocInv's transfer lemmas [kmem_res_pop] /
   [kmem_res_push] together with [page_head8_word_at] / [run_page_page_own]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding WpAcquireMem WpAcquireTop.
Require Import WpRvcBridge WpLock WpLockLeaves WpHoldingInv WpPopOff.
Require Import WpAcquireLock WpRelease.
Require Import KallocInv WpKallocDecode WpFreelistMem.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Notation AK := KernelSyms.kalloc.
  Notation AQ := KernelSyms.acquire.
  Notation PO := KernelSyms.push_off.

  (* ============================================================= *)
  (* kalloc: whole-function S-mode WP.  WORK IN PROGRESS -- the     *)
  (* statement's frame windows grow as each callee is reached; the  *)
  (* tail past the prologue is [admit] for now.                     *)
  (* ============================================================= *)
  Lemma wp_kalloc (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname)
      (m : gmap regidx (mword 64))
      (vr24 vr16 vr8 : bv 64)
      (svpn_noff svpn_intena svpn_lk svpn_cpu : mword 27)
      (qvr24 qvr16 qvr8 qpr24 qpr16 qpr8 qpr0 qfraold qfs0old qcpuold : bv 64)
      (qnoff qintena_old : mword 32) (a0f fl : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let pcE : mword 64 := mword_of_int AK in
    let spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_r24 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (* ---- register-map chain through kalloc's prologue + the +0x12 jal ---- *)
    let R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m in
    let R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1 in
    let R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x0a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R2 in
    let R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7fe : mword 12)))]> R3 in
    let mA := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)]> R4 in
    (* ---- acquire's frame + per-cpu + lock addresses (its [let]s, m := mA) ---- *)
    let lkA := mA !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0A := mA !!! Regidx csp_rs1 in
    let spdA := add_vec sp0A (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let q_r24 := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let q_r16 := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let q_r8  := add_vec spdA (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pspdA := add_vec spdA (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let q_p24 := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let q_p16 := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let q_p8  := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let q_p0  := add_vec pspdA (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let pspm10A := add_vec pspdA (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let q_fra := add_vec pspm10A (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let q_fs0 := add_vec pspm10A (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let q_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let q_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let q_cpu := add_vec lkA (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* ---- acquire's internal register chain (A0..PN8), m := mA ---- *)
    let A0 := <[Regidx csp_rs1 := regval_into_reg spdA]> mA in
    let A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0 in
    let A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1 in
    let P0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2 in
    let PN0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> P0 in
    let PN1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (PN0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> PN0 in
    let PN2 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> PN1 in
    let PN3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (PN2 !!! Regidx (mword_of_int 15 : mword 5)))]> PN2 in
    let PN4 := po_mycpu_out (mword_of_int (PO + 0x10)) PN3 in
    let PN5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 qnoff)]> PN4 in
    let PN6 := po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 in
    let PN7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (shift_bits_right (PN6 !!! Regidx (mword_of_int 9 : mword 5))
           (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))]> PN6 in
    let PN8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (PN7 !!! Regidx (mword_of_int 15 : mword 5))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> PN7 in
    let q_storeval32 := (autocast (T := mword)
        (subrange_vec_dec (PN8 !!! Regidx (mword_of_int 15 : mword 5)) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let q_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 qnoff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let q_noff_store := (autocast (T := mword) (subrange_vec_dec q_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let q_ret_tgt := update_vec_dec (add_vec (mA !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    po_mycpu_geom pmpcfg0 pmpaddr00 ->
    (* ---- acquire's extra side conditions (m := mA) ---- *)
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lkA) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    po_mycpu_out (mword_of_int (PO + 0x10)) PN3 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x2c)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN5 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) PN8 !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    eq_vec (qcpuold : mword 64) (mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    po_slot_geom root_ppn pmpaddr00 svpn_noff q_noff 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_intena q_intena 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_lk lkA 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_cpu q_cpu 8 ->
    eq_vec (access_vec_dec q_ret_tgt 0) ('b"0") = true ->
    (* the freelist head lives at &kmem.freelist = kmem+24 *)
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    (* ---- release's extra side conditions (m := R12) ---- *)
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    a0f = mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5)) ->
    neq_vec (and_vec (sstatus_read mstatus0)
       (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 q_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 qnoff) zero_reg then q_storeval32 else qintena_old)) zero_reg = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    a_r24 ↦₈ vr24 -∗
    a_r16 ↦₈ vr16 -∗
    a_r8 ↦₈ vr8 -∗
    (* ---- acquire's scratch-stack windows (below kalloc's own frame) ---- *)
    q_r24 ↦₈ qvr24 -∗
    q_r16 ↦₈ qvr16 -∗
    q_r8  ↦₈ qvr8 -∗
    q_p24 ↦₈ qpr24 -∗
    q_p16 ↦₈ qpr16 -∗
    q_p8  ↦₈ qpr8 -∗
    q_p0  ↦₈ qpr0 -∗
    q_fra ↦₈ qfraold -∗
    q_fs0 ↦₈ qfs0old -∗
    ([∗ list] j ∈ seq 0 4, (pa_add q_noff j) ↦ₘ nth_byte qnoff j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add q_intena j) ↦ₘ nth_byte qintena_old j) -∗
    is_lock γ lkA (kmem_res fl) -∗
    q_cpu ↦₈ qcpuold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ (mr : gmap regidx (mword 64)), gpr_file mr ∗
         kalloc_post (mr !!! Regidx (mword_of_int 10 : mword 5))) -∗
      (∃ u1 u2 u3 : bv 64, a_r24 ↦₈ u1 ∗ a_r16 ↦₈ u2 ∗ a_r8 ↦₈ u3) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE spr a_r24 a_r16 a_r8 ret_tgt
      R1 R2 R3 R4 mA lkA sp0A spdA q_r24 q_r16 q_r8 pspdA q_p24 q_p16 q_p8 q_p0
      pspm10A q_fra q_fs0 q_noff q_intena q_cpu
      A0 A1 A2 P0 PN0 PN1 PN2 PN3 PN4 PN5 PN6 PN7 PN8
      q_storeval32 q_noff_a5 q_noff_store q_ret_tgt
      HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov Hmyg
      Hlegal Hamo Hpin1 Hpin2 Hpin3 Hpin4 Hcpune Hg_noff Hg_int Hg_lk Hg_cpu Hret0 Hfl
      Hfiom Ha0fcpu Hsst Hnoffpos Hintena0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hr24 Hr16 Hr8
             Hqr24 Hqr16 Hqr8 Hqp24 Hqp16 Hqp8 Hqp0 Hqfra Hqfs0 Hnoff Hint #Hlock Hcpu Hcont".
    iPoseProof (kai_00 with "Htext") as "Hi00".
    iPoseProof (kai_02 with "Htext") as "Hi02".
    iPoseProof (kai_04 with "Htext") as "Hi04".
    iPoseProof (kai_06 with "Htext") as "Hi06".
    iPoseProof (kai_08 with "Htext") as "Hi08".
    iPoseProof (kai_0a with "Htext") as "Hi0a".
    iPoseProof (kai_0e with "Htext") as "Hi0e".
    (* +0x00 c.addi16sp sp,-32 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 (mword_of_int 32 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (AK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AK + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AK + 0x02) : mword 64) 2 = mword_of_int (AK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AK + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AK + 0x04) : mword 64) 2 = mword_of_int (AK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (AK + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AK + 0x06) : mword 64) 2 = mword_of_int (AK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (AK + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp0a : add_vec_int (mword_of_int (AK + 0x08) : mword 64) 2 = mword_of_int (AK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a auipc a0,0x11 *)
    iApply (wp_auipc_s root_ppn E Φ (mword_of_int (AK + 0x0a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
              R2 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp0e : add_vec_int (mword_of_int (AK + 0x0a) : mword 64) 4 = mword_of_int (AK + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e addi a0,a0,2046  (a0 := &kmem) *)
    iApply (wp_addi4_s root_ppn E Φ (mword_of_int (AK + 0x0e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7fe : mword 12)
              R3 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp12 : add_vec_int (mword_of_int (AK + 0x0e) : mword 64) 4 = mword_of_int (AK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- a0 = &kmem now (R4 !!! a0) ---- *)
    iPoseProof (kai_12 with "Htext") as "Hi12".
    (* +0x12 jal ra,acquire : link ra := +0x16, jump to acquire's entry *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_jal_gpr_s_zca root_ppn E Φ (mword_of_int (AK + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0xc8 : mword 21)
              R4 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    assert (Htgta : add_vec (mword_of_int (AK + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0xc8 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgta) in "Hpc".
    (* ---- acquire(&kmem): CSL acquire, returns [locked γ ∗ kmem_res fl] ---- *)
    iApply (wp_acquire_lock root_ppn E Φ γ (kmem_res fl) mA
              svpn_noff svpn_intena svpn_lk svpn_cpu
              qvr24 qvr16 qvr8 qpr24 qpr16 qpr8 qfraold qfs0old qcpuold
              qnoff qintena_old a0f
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov
              Hlegal Hamo Hpin1 Hpin2 Hpin3 Hpin4 Hmyg Hcpune Hg_noff Hg_int Hg_lk Hg_cpu Hret0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                    Hqr24 Hqr16 Hqr8 Hqp24 Hqp16 Hqp8 Hqfra Hqfs0 Hnoff Hint Hlock Hcpu [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Htok HRres Hgpr
             Hqr24 Hqr16 Hqr8 Hqjunk Hnoff Hint Hcpu".
    (* ---- acquire returned: [locked γ ∗ kmem_res fl] held, pc = +0x16 ---- *)
    iDestruct "Hgpr" as (mfin) "[Hfile %Hpins]".
    destruct Hpins as (Hmra & Hms0 & Hms1 & Hmsp & Hma0 & Hmtp).
    assert (Hmara : mA !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x12) : mword 64) 4)
      by (rewrite /mA; apply lookup_total_insert).
    assert (Hpc16 : update_vec_dec (add_vec (mA !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AK + 0x16)).
    { rewrite Hmara. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc16) in "Hpc".
    iPoseProof (kai_16 with "Htext") as "Hi16".
    iPoseProof (kai_1a with "Htext") as "Hi1a".
    iPoseProof (kai_1e with "Htext") as "Hi1e".
    (* +0x16 auipc s1,0x12 *)
    iApply (wp_auipc_s root_ppn E Φ (mword_of_int (AK + 0x16)) (mword_of_int 9 : mword 5) (mword_of_int 0x12 : mword 20)
              mfin mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> mfin).
    assert (Hs1R6 : R6 !!! Regidx (mword_of_int 9 : mword 5) = add_vec (mword_of_int (AK + 0x16) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))
      by (rewrite /R6; apply lookup_total_insert).
    assert (Hpp1a : add_vec_int (mword_of_int (AK + 0x16) : mword 64) 4 = mword_of_int (AK + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a ld s1,-2038(s1) : s1 := *(kmem.freelist) = head *)
    iDestruct "HRres" as (head pages) "[Hflw Hchain]".
    assert (Hldaddr : add_vec (R6 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 0x80a : mword 12)) = fl).
    { rewrite Hs1R6 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_ld_s_ram root_ppn E Φ (mword_of_int (AK + 0x1a)) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 0x80a : mword 12)
              R6 head mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (R7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg head]> R6).
    assert (Hs1R7 : R7 !!! Regidx (mword_of_int 9 : mword 5) = head) by (rewrite /R7; apply lookup_total_insert).
    assert (Hpp1e : add_vec_int (mword_of_int (AK + 0x1a) : mword 64) 4 = mword_of_int (AK + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.beqz s1,+0x4c : head=nullp -> empty; else pop *)
    destruct pages as [|p ps].
    - (* ---- EMPTY list: head = nullp, branch taken to +0x4c ---- *)
      iDestruct "Hchain" as %Hhead.
      iApply (wp_cbeqz_taken_s_zca root_ppn E Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7 Hhead; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      (* pc = +0x4c ; empty branch: release, a0:=0, join at +0x40, kalloc_post = nullp *)
      admit.
    - (* ---- NONEMPTY: head = p, page_valid p, p <> nullp, fall through to +0x20 ---- *)
      iDestruct "Hchain" as "(-> & %Hpv & Hrun)".
      iDestruct "Hrun" as (nxt) "[Hrun Hchain]".
      iApply (wp_cbeqz_fall_s_config root_ppn E Φ (mword_of_int (AK + 0x1e)) (mword_of_int 23 : mword 8) (Cregidx (mword_of_int 1)) (mword_of_int 9 : mword 5)
                R7 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs1R7; apply eq_vec_false_iff; intro Hpz;
                      apply (page_valid_ne_null p Hpv); rewrite Hpz; apply bv_eq; vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      (* pc = +0x20 ; run_page p nxt = word_at p nxt ∗ page_rest p *)
      iEval (rewrite /run_page) in "Hrun".
      iDestruct "Hrun" as "[Hpnext Hprest]".
      iPoseProof (kai_20 with "Htext") as "Hi20".
      iPoseProof (kai_22 with "Htext") as "Hi22".
      iPoseProof (kai_26 with "Htext") as "Hi26".
      (* +0x20 c.ld a5,0(s1) : a5 := *p = nxt *)
      assert (Hpaddr : add_vec (R7 !!! Regidx (mword_of_int 9 : mword 5))
                 (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = p).
      { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hs1R7. apply kv_addv_zero. }
      iApply (wp_cld_s_ram root_ppn E Φ (mword_of_int (AK + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
                R7 nxt mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HR
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi20 [Hpnext] [-]").
      { iEval (rewrite Hpaddr). rewrite /word_at. iExact "Hpnext". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hpnext".
      iEval (rewrite Hpaddr) in "Hpnext".
      set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg nxt]> R7).
      assert (Hpp22 : add_vec_int (mword_of_int (AK + 0x20) : mword 64) 2 = mword_of_int (AK + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 auipc a4,0x11 *)
      iApply (wp_auipc_s root_ppn E Φ (mword_of_int (AK + 0x22)) (mword_of_int 14 : mword 5) (mword_of_int 0x11 : mword 20)
                R8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (R9 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R8).
      assert (Ha4R9 : R9 !!! Regidx (mword_of_int 14 : mword 5) = add_vec (mword_of_int (AK + 0x22) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))
        by (rewrite /R9; apply lookup_total_insert).
      assert (Ha5R9 : R9 !!! Regidx (mword_of_int 15 : mword 5) = nxt).
      { rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate]. rewrite /R8; apply lookup_total_insert. }
      assert (Hpp26 : add_vec_int (mword_of_int (AK + 0x22) : mword 64) 4 = mword_of_int (AK + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 sd a5,2046(a4) : kmem.freelist := nxt *)
      assert (Hstaddr : add_vec (R9 !!! Regidx (mword_of_int 14 : mword 5)) (sign_extend' 64 (mword_of_int 0x7fe : mword 12)) = fl).
      { rewrite Ha4R9 Hfl. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_sd_s_ram root_ppn E Φ (mword_of_int (AK + 0x26)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5) (mword_of_int 0x7fe : mword 12)
                R9 p mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HW
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi26 [Hflw] [-]").
      { iEval (rewrite -Hstaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hflw".
      rewrite Ha5R9. iEval (rewrite Hstaddr) in "Hflw".
      (* reclose kmem_res fl on the new head nxt, and reassemble page_own p *)
      iAssert (kmem_res fl) with "[Hflw Hchain]" as "HRres".
      { iApply (kmem_res_close fl nxt ps). rewrite /word_at. iFrame "Hflw Hchain". }
      iAssert (page_own p) with "[Hpnext Hprest]" as "Hpage".
      { iApply (run_page_page_own p nxt). rewrite /run_page /word_at. iFrame "Hpnext Hprest". }
      assert (Hpp2a : add_vec_int (mword_of_int (AK + 0x26) : mword 64) 4 = mword_of_int (AK + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iPoseProof (kai_2a with "Htext") as "Hi2a".
      iPoseProof (kai_2e with "Htext") as "Hi2e".
      (* +0x2a auipc a0,0x11 *)
      iApply (wp_auipc_s root_ppn E Φ (mword_of_int (AK + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 0x11 : mword 20)
                R9 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2a [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (mword_of_int (AK + 0x2a) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> R9).
      assert (Hpp2e : add_vec_int (mword_of_int (AK + 0x2a) : mword 64) 4 = mword_of_int (AK + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* +0x2e addi a0,a0,2014  (a0 := &kmem) *)
      iApply (wp_addi4_s root_ppn E Φ (mword_of_int (AK + 0x2e)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 0x7de : mword 12)
                R10 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      set (R11 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec (R10 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0x7de : mword 12)))]> R10).
      assert (Ha0kmem : R11 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R11 lookup_total_insert /R10 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
      assert (Hpp32 : add_vec_int (mword_of_int (AK + 0x2e) : mword 64) 4 = mword_of_int (AK + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      iPoseProof (kai_32 with "Htext") as "Hi32".
      (* +0x32 jal ra,release : link ra := +0x36, jump to release's entry *)
      iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                   with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
        as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
      iApply (wp_jal_gpr_s_zca root_ppn E Φ (mword_of_int (AK + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x130 : mword 21)
                R11 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
                HN Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi32 [-]").
      iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
      iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                   with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
        as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
      set (R12 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)]> R11).
      assert (Htgtr : add_vec (mword_of_int (AK + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x130 : mword 21)) = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtr) in "Hpc".
      (* pc = release entry, a0 = &kmem, ra = +0x36 ; hold locked γ ∗ kmem_res fl. *)
      (* ---- register-agreement facts across the R6..R12 chain (m := R12) ---- *)
      assert (HR12csp : R12 !!! Regidx csp_rs1 = mA !!! Regidx csp_rs1).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmsp. }
      assert (HR12tp : R12 !!! Regidx (mword_of_int 4 : mword 5) = mA !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hmtp. }
      assert (HR12a0 : R12 !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
      { rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ha0kmem. }
      assert (HR12ra : R12 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AK + 0x32) : mword 64) 4)
        by (rewrite /R12; apply lookup_total_insert).
      assert (HlkAkmem : lkA = mword_of_int KernelSyms.kmem).
      { rewrite /lkA /mA lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /R4 lookup_total_insert /R3 lookup_total_insert.
        apply bv_eq; vm_compute; reflexivity. }
      (* ---- release's window addresses reduce to kalloc's q_* slots ---- *)
      assert (Hacpu : add_vec (R12 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = q_cpu).
      { rewrite HR12a0 /q_cpu HlkAkmem. reflexivity. }
      assert (Hanoff : add_vec (mycpu_ret (R12 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 120 : mword 12)) = q_noff).
      { rewrite HR12tp /q_noff Ha0fcpu. reflexivity. }
      assert (Haint : add_vec (mycpu_ret (R12 !!! Regidx (mword_of_int 4 : mword 5))) (sign_extend' 64 (mword_of_int 124 : mword 12)) = q_intena).
      { rewrite HR12tp /q_intena Ha0fcpu. reflexivity. }
      iDestruct "Hqjunk" as (vp24 vp16 vp8 vfra vfs0) "(Hqp24 & Hqp16 & Hqp8 & Hqfra & Hqfs0)".
      iApply (wp_release root_ppn E Φ γ lkA (kmem_res fl) R12
                svpn_lk svpn_cpu svpn_noff svpn_intena
                (mycpu_ret (mA !!! Regidx (mword_of_int 4 : mword 5)))
                q_noff_store
                (if eq_vec (sign_extend' 64 qnoff) zero_reg then q_storeval32 else qintena_old)
                (mA !!! Regidx (mword_of_int 1 : mword 5))
                (mA !!! Regidx (mword_of_int 8 : mword 5))
                (mA !!! Regidx (mword_of_int 9 : mword 5))
                vp24 vp16 vp8 qpr0 vfra vfs0
                mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dqi:=DfracOwn 1)
                HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hfiom Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov Hmyg
                ltac:(rewrite HR12a0 HlkAkmem; apply bv_eq; vm_compute; reflexivity)
                Hg_lk
                ltac:(rewrite Hacpu; exact Hg_cpu)
                ltac:(rewrite Hanoff; exact Hg_noff)
                ltac:(rewrite Haint; exact Hg_int)
                ltac:(rewrite HR12tp; apply eq_vec_true_iff; reflexivity)
                Hsst Hnoffpos Hintena0
                ltac:(rewrite HR12ra; vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                      Hlock Htok HRres [Hcpu] [Hnoff] [Hint] [Hqr24] [Hqr16] [Hqr8]
                      [Hqp24] [Hqp16] [Hqp8] [Hqp0] [Hqfra] [Hqfs0] [-]").
      { iEval (rewrite Hacpu). iExact "Hcpu". }
      { iEval (rewrite Hanoff). iExact "Hnoff". }
      { iEval (rewrite Haint). iExact "Hint". }
      { iEval (rewrite HR12csp). iExact "Hqr24". }
      { iEval (rewrite HR12csp). iExact "Hqr16". }
      { iEval (rewrite HR12csp). iExact "Hqr8". }
      { iEval (rewrite HR12csp). iExact "Hqp24". }
      { iEval (rewrite HR12csp). iExact "Hqp16". }
      { iEval (rewrite HR12csp). iExact "Hqp8". }
      { iEval (rewrite HR12csp). iExact "Hqp0". }
      { iEval (rewrite HR12csp). iExact "Hqfra". }
      { iEval (rewrite HR12csp). iExact "Hqfs0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgpr2 Hcpu2 Hnoff2 Hint2 Hjunk2".
      (* pc = ret_tgt = +0x36 ; lock released, still hold [page_own p].
         memset(p, 0, 4096); a0 := p; epilogue.  TODO *)
      admit.
  Admitted.

End Kalloc.

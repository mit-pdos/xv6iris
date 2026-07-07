(* WpKfree.v -- instruction-level proof of the kernel's [kfree] (0x80000a38)
   against the allocator spec in KallocInv.v.

   kfree is a whole-function S-mode proof in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): it threads the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALLS the sub-functions memset / acquire / release via [jal], discharging
   each callee's whole-function WP.  The novel content is the free-list PUSH,
   which is discharged by KallocInv's transfer lemma [kmem_res_push] together
   with [page_head8_word_at] / [run_page_page_own].

   Structural sibling: [WpKalloc.v] (same branch).  This file mirrors its
   statement shape (S-mode config + frame windows) and its prologue proof. *)
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
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad WpGprLui.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding WpAcquireMem WpAcquireTop.
Require Import WpRvcBridge WpLock WpLockLeaves WpHoldingInv WpPopOff.
Require Import WpAcquireLock WpRelease WpMemsetPage WpFreelistMem.
Require Import KallocInv WpKallocDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Register-generic execute helpers for SLTU (the bounds-check compares), *)
(* mirroring [exec_execute_RTYPE_OR{,_gpr}] in WpGprLogic.  The model's    *)
(* SLTU writes [zero_extend' 64 (bool_to_bit (a <u b))].                   *)
(* ===================================================================== *)
Definition gpr_sltu_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)))).

Lemma exec_execute_RTYPE_SLTU (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (zero_extend' 64 (bool_to_bit (zopz0zI_u a b)))) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd SLTU) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (zero_extend' 64 (bool_to_bit (zopz0zI_u a b))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

Lemma exec_execute_RTYPE_SLTU_gpr (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg (gpr_sltu_val rs2 rs1 s))).
Proof.
  intro Hrd. unfold gpr_sltu_val.
  change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)))
    with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SLTU).
  eapply exec_execute_RTYPE_SLTU.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - rewrite exec_wX_bits_gpr.
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* [zopz0zI_u x y = Z.ltb (uint x) (uint y)]; a false compare packs to 0. *)
Lemma sltu_false_zero (a b : mword 64) :
  zopz0zI_u a b = false ->
  (zero_extend' 64 (bool_to_bit (zopz0zI_u a b)) : mword 64) = mword_of_int 0.
Proof. intro H. rewrite H. apply bv_eq; vm_compute; reflexivity. Qed.

(* [slli p 0x34] with [p] 4096-aligned is zero: the low 12 bits (all zero)
   are the only ones that survive a 52-bit left shift in 64 bits. *)
Lemma shift_bits_left52_zero (p : mword 64) :
  (uint p) mod 4096 = 0 ->
  shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0) = mword_of_int 0.
Proof.
  intro Hal.
  assert (Hn : shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl p 52).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn. apply bv_eq.
  unfold shiftl, with_word, get_word, MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.N_to_word (MachineWord.Z_idx 64) (MachineWord.Z_idx 52)) = 52).
  { unfold MachineWord.N_to_word, MachineWord.Z_idx. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. unfold bv_modulus. simpl. lia. }
  rewrite Hsh.
  assert (Hup : uint p = bv_unsigned p).
  { unfold uint, MachineWord.word_to_N, get_word. rewrite Z2N.id; [reflexivity|].
    pose proof (bv_unsigned_in_range _ p). lia. }
  rewrite Hup in Hal.
  apply Z.mod_divide in Hal; [| lia]. destruct Hal as [q Hq].
  assert (Hz0 : bv_unsigned (mword_of_int 0 : mword 64) = 0) by reflexivity.
  rewrite Hz0.
  rewrite Z.shiftl_mul_pow2; [| lia].
  rewrite Hq.
  unfold bv_wrap, bv_modulus.
  replace (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (4096 * 2 ^ 52) by (vm_compute; reflexivity).
  rewrite <- Z.mul_assoc. apply Z.mod_mul. vm_compute; discriminate.
Qed.

Section Kfree.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{CID : CpuId}.

  Notation KF := KernelSyms.kfree.
  Notation PO := KernelSyms.push_off.

  (* ============================================================= *)
  (* kfree: whole-function S-mode WP.  COMPLETE (Qed, no admits).     *)
  (* Covers the prologue (four saves + addi4spn), the auipc/addi      *)
  (* loading a5 := <end>, the bounds/alignment check region +14..+2c  *)
  (* (both panic branches shown dead from page_valid), the memset     *)
  (* argument setup and [jal memset] (wp_memset_page), the [jal       *)
  (* acquire] (wp_acquire_lock), the freelist push (p->next := head;  *)
  (* kmem.freelist := p), the [jal release] (wp_release), and the     *)
  (* epilogue (four c.ldsp restores + c.addi16sp + c.ret).            *)
  (* ============================================================= *)
  Lemma wp_kfree (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk fl : mword 64)
      (m : gmap regidx (mword 64))
      (vr24 vr16 vr8 vr0 mvra mvs0 : bv 64)
      (svpn_noff svpn_intena svpn_lk svpn_cpu : mword 27)
      (qvr24 qvr16 qvr8 qpr24 qpr16 qpr8 qpr0 qfraold qfs0old qcpuold : bv 64)
      (qnoff qintena_old : mword 32) (a0f : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) :
    let pcE : mword 64 := mword_of_int KF in
    let p := m !!! Regidx (mword_of_int 10 : mword 5) in
    let spr := add_vec (m !!! Regidx csp_rs1 : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_r24 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_r0  := add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    (* memset's own frame (below kfree's), at sp'=spr-16: ra@sp'+8, s0@sp'+0 *)
    let ms_sp := add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let ms_ra := add_vec ms_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let ms_s0 := add_vec ms_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (* ---- acquire's/release's scratch frame windows (below kfree's frame).
       Since memset preserves sp, the acquire-entry sp is [spr]; acquire's own
       c.addi16sp -32 lands its frame at [spdA = spr - 32], and push_off's frame
       another 32 below.  release reuses the SAME windows. ---- *)
    let spdA := add_vec spr (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
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
    let q_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* push_off's noff increment value (function of the ghost noff alone) *)
    let q_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 qnoff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let q_noff_store := (autocast (T := mword) (subrange_vec_dec q_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
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
    (* ---- acquire's extra side conditions ---- *)
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    (forall pmar0, pma_allows_all pmar0 ->
       exists region_amo,
         matching_pma_region pmar0 (Physaddr lk) 4 = Some region_amo /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_readable) = true /\
         (override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_writable) = true /\
         pma_allows_atomic_op
           ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
           AMOSWAP 4 = true) ->
    (* the mycpu() return pointer depends on the input map only through tp, so
       the a0 pins can be stated over the input map [m]. *)
    po_mycpu_out (mword_of_int (PO + 0x10)) m !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x2c)) m !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    po_mycpu_out (mword_of_int (PO + 0x18)) m !!! Regidx (mword_of_int 10 : mword 5) = a0f ->
    eq_vec (qcpuold : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    po_slot_geom root_ppn pmpaddr00 svpn_noff q_noff 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_intena q_intena 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_lk lk 4 ->
    po_slot_geom root_ppn pmpaddr00 svpn_cpu q_cpu 8 ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    lk = mword_of_int KernelSyms.kmem ->
    fl = mword_of_int (KernelSyms.kmem + 24) ->
    a0f = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ->
    (* ---- release's extra side conditions ---- *)
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    neq_vec (and_vec (sstatus_read mstatus0)
       (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 q_noff_store) = false ->
    eq_vec (sign_extend' 64
       (if eq_vec (sign_extend' 64 qnoff) zero_reg then acq_intena_store mstatus0 else qintena_old)) zero_reg = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    is_kmem γ lk fl -∗
    kfree_pre p -∗
    a_r24 ↦₈ vr24 -∗
    a_r16 ↦₈ vr16 -∗
    a_r8 ↦₈ vr8 -∗
    a_r0 ↦₈ vr0 -∗
    ms_ra ↦₈ mvra -∗
    ms_s0 ↦₈ mvs0 -∗
    (* ---- acquire's/release's scratch-stack windows (below kfree's frame) ---- *)
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
    q_cpu ↦₈ qcpuold -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ (mr : gmap regidx (mword 64)), gpr_file mr) -∗
      (∃ u1 u2 u3 u4 u5 u6 : bv 64, a_r24 ↦₈ u1 ∗ a_r16 ↦₈ u2 ∗ a_r8 ↦₈ u3 ∗ a_r0 ↦₈ u4 ∗ ms_ra ↦₈ u5 ∗ ms_s0 ↦₈ u6) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE p spr a_r24 a_r16 a_r8 a_r0 ms_sp ms_ra ms_s0 ret_tgt
      spdA q_r24 q_r16 q_r8 pspdA q_p24 q_p16 q_p8 q_p0 pspm10A q_fra q_fs0
      q_noff q_intena q_cpu q_noff_a5 q_noff_store
      HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov Hmyg
      Hlegal Hamo Hpin1 Hpin2 Hpin3 Hcpune Hg_noff Hg_int Hg_lk Hg_cpu Hretm Hlk Hfl Ha0fcpu
      Hfiom Hsst Hnoffpos Hintena0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile #Hkmem Hpre Hr24 Hr16 Hr8 Hr0 Hmra Hms0
             Hqr24 Hqr16 Hqr8 Hqp24 Hqp16 Hqp8 Hqp0 Hqfra Hqfs0 Hqnoff Hqint Hqcpu Hcont".
    iPoseProof (kfi_00 with "Htext") as "Hi00".
    iPoseProof (kfi_02 with "Htext") as "Hi02".
    iPoseProof (kfi_04 with "Htext") as "Hi04".
    iPoseProof (kfi_06 with "Htext") as "Hi06".
    iPoseProof (kfi_08 with "Htext") as "Hi08".
    iPoseProof (kfi_0a with "Htext") as "Hi0a".
    iPoseProof (kfi_0c with "Htext") as "Hi0c".
    iPoseProof (kfi_10 with "Htext") as "Hi10".
    iPoseProof (kfi_14 with "Htext") as "Hi14".
    iPoseProof (kfi_18 with "Htext") as "Hi18".
    iPoseProof (kfi_1a with "Htext") as "Hi1a".
    iPoseProof (kfi_1c with "Htext") as "Hi1c".
    iPoseProof (kfi_1e with "Htext") as "Hi1e".
    iPoseProof (kfi_22 with "Htext") as "Hi22".
    iPoseProof (kfi_24 with "Htext") as "Hi24".
    iPoseProof (kfi_26 with "Htext") as "Hi26".
    iPoseProof (kfi_28 with "Htext") as "Hi28".
    iPoseProof (kfi_2c with "Htext") as "Hi2c".
    iPoseProof (kfi_2e with "Htext") as "Hi2e".
    iPoseProof (kfi_30 with "Htext") as "Hi30".
    (* the caller-supplied page precondition: validity + full ownership *)
    iDestruct "Hpre" as "[%Hpv Hpown]".
    assert (Hpal : (uint p) mod 4096 = 0) by (destruct Hpv as [Ha _]; exact Ha).
    assert (Hprlo : 0x80023558 <= uint p) by (destruct Hpv as [_ [Hlo _]]; exact Hlo).
    assert (Hprhi : uint p < 0x88000000) by (destruct Hpv as [_ [_ Hhi]]; exact Hhi).
    assert (Hsltu14 : zopz0zI_u p (mword_of_int 0x80023558 : mword 64) = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x80023558 : mword 64)) with 0x80023558 by (vm_compute; reflexivity).
      lia. }
    assert (Hsltu1e : zopz0zI_u (mword_of_int 0x87FFFFFF : mword 64) p = false).
    { unfold zopz0zI_u. apply Z.ltb_ge.
      replace (uint (mword_of_int 0x87FFFFFF : mword 64)) with 0x87FFFFFF by (vm_compute; reflexivity).
      lia. }
    (* +0x00 c.addi16sp sp,-32 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 (mword_of_int 32 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (KF + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 vr24 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KF + 0x02) : mword 64) 2 = mword_of_int (KF + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KF + 0x04) : mword 64) 2 = mword_of_int (KF + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KF + 0x06) : mword 64) 2 = mword_of_int (KF + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 vr0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [Hr0] [-]").
    { iEval (rewrite HspR1). iExact "Hr0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KF + 0x08) : mword 64) 2 = mword_of_int (KF + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KF + 0x0a) : mword 64) 2 = mword_of_int (KF + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c auipc a5,0x23 *)
    iApply (wp_auipc_s root_ppn E Φ (mword_of_int (KF + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 0x23 : mword 20)
              R2 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x0c) : mword 64) (auipc_off (mword_of_int 0x23 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KF + 0x0c) : mword 64) 4 = mword_of_int (KF + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi a5,a5,-1260  (a5 := <end> = 0x80023558) *)
    iApply (wp_addi4_s root_ppn E Φ (mword_of_int (KF + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0xb14 : mword 12)
              R3 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (mword_of_int 0xb14 : mword 12)))]> R3).
    assert (Hpp14 : add_vec_int (mword_of_int (KF + 0x10) : mword 64) 4 = mword_of_int (KF + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* a0 (= the page p) and a5 (= <end>) after the prologue+auipc/addi *)
    assert (Hp10 : R4 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hend : R4 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x80023558).
    { rewrite /R4 lookup_total_insert. rewrite /R3 lookup_total_insert.
      apply bv_eq; vm_compute; reflexivity. }
    (* +0x14 sltu a4,a0,a5  (a4 := p <u end = 0, since end <= p) *)
    iApply (wp_gpr_write_s_config_base root_ppn E Φ (mword_of_int (KF + 0x14))
              (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 15 : mword 5)
              (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 14), SLTU))
              (mword_of_int 0 : mword 64)
              R4 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_RTYPE_SLTU_gpr (mword_of_int 15) (mword_of_int 10) (mword_of_int 14) s_pc ltac:(vm_compute; discriminate));
                    unfold gpr_sltu_val; rewrite Hva Hvb Hp10 Hend;
                    rewrite (sltu_false_zero p (mword_of_int 0x80023558) Hsltu14); reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R4).
    assert (Hpp18 : add_vec_int (mword_of_int (KF + 0x14) : mword 64) 4 = mword_of_int (KF + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.li a5,17 *)
    iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (KF + 0x18))
              (mword_of_int 15 : mword 5) (zero_extend' 5 ('b"00") : mword 5) (zero_extend' 5 ('b"00") : mword 5)
              (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 15), ADDI))
              (mword_of_int 17 : mword 64)
              R5 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 15) (sign_extend' 12 (mword_of_int 17 : mword 6)) s_pc);
                    replace (Z.eqb (uint (mword_of_int 15 : mword 5)) 0) with false by (vm_compute; reflexivity);
                    do 2 f_equal; unfold gpr_addi_val; apply bv_eq; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 17 : mword 64)]> R5).
    assert (Hli : R6 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 17)
      by (rewrite /R6 lookup_total_insert; reflexivity).
    assert (Hpp1a : add_vec_int (mword_of_int (KF + 0x18) : mword 64) 2 = mword_of_int (KF + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.slli a5,0x1b  (a5 := 17 << 27 = PHYSTOP) *)
    iApply (wp_cslli_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x1a)) (Regidx (mword_of_int 15)) (mword_of_int 15 : mword 5) (mword_of_int 27 : mword 6)
              R6 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_left (R6 !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> R6).
    assert (Hphys : R7 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x88000000).
    { rewrite /R7 lookup_total_insert. rewrite Hli. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (KF + 0x1a) : mword 64) 2 = mword_of_int (KF + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.addi a5,-1  (a5 := PHYSTOP - 1) *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x1c)) (mword_of_int 15 : mword 5) (mword_of_int 63 : mword 6)
              R7 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (R7 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R7).
    assert (Hphysm1 : R8 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x87FFFFFF).
    { rewrite /R8 lookup_total_insert. rewrite Hphys. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp10_8 : R8 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hpp1e : add_vec_int (mword_of_int (KF + 0x1c) : mword 64) 2 = mword_of_int (KF + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e sltu a5,a5,a0  (a5 := (PHYSTOP-1) <u p = 0, since p <= PHYSTOP-1) *)
    iApply (wp_gpr_write_s_config_base root_ppn E Φ (mword_of_int (KF + 0x1e))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5)
              (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTU))
              (mword_of_int 0 : mword 64)
              R8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_RTYPE_SLTU_gpr (mword_of_int 10) (mword_of_int 15) (mword_of_int 15) s_pc ltac:(vm_compute; discriminate));
                    unfold gpr_sltu_val; rewrite Hva Hvb Hphysm1 Hp10_8;
                    rewrite (sltu_false_zero (mword_of_int 0x87FFFFFF) p Hsltu1e); reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R8).
    assert (Hor14 : R9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 0).
    { rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert; reflexivity. }
    assert (Hor15 : R9 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R9 lookup_total_insert; reflexivity).
    assert (Hpp22 : add_vec_int (mword_of_int (KF + 0x1e) : mword 64) 4 = mword_of_int (KF + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.or a5,a4  (a5 := a5 | a4 = 0) *)
    iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (KF + 0x22))
              (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), OR))
              (mword_of_int 0 : mword 64)
              R9 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    change (creg2reg_idx (Cregidx (mword_of_int 6))) with (Regidx (mword_of_int 14 : mword 5));
                    change (creg2reg_idx (Cregidx (mword_of_int 7))) with (Regidx (mword_of_int 15 : mword 5));
                    rewrite (exec_execute_RTYPE_OR_gpr (mword_of_int 14) (mword_of_int 15) (mword_of_int 15) s_pc ltac:(vm_compute; discriminate));
                    unfold gpr_or_val; rewrite Hva Hvb Hor15 Hor14;
                    replace (or_vec (mword_of_int 0 : mword 64) (mword_of_int 0)) with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi22 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R10 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R9).
    assert (Hbnez24 : R10 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R10 lookup_total_insert; reflexivity).
    assert (Hp10_10 : R10 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10_8. }
    assert (Hpp24 : add_vec_int (mword_of_int (KF + 0x22) : mword 64) 2 = mword_of_int (KF + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.bnez a5,+60  NOT taken (a5 = 0): both bounds hold, panic avoided *)
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (KF + 0x24)) (mword_of_int 30 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R10 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez24; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi24 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp26 : add_vec_int (mword_of_int (KF + 0x24) : mword 64) 2 = mword_of_int (KF + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.mv s1,a0  (s1 := p) *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R10 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi26 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R11 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (R10 !!! Regidx (mword_of_int 10 : mword 5)))]> R10).
    assert (Hp10_11 : R11 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hp10_10. }
    assert (Hpp28 : add_vec_int (mword_of_int (KF + 0x26) : mword 64) 2 = mword_of_int (KF + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 slli a5,a0,0x34  (a5 := p << 52 = 0, since p is 4096-aligned) *)
    iApply (wp_gpr_write_s_config_base root_ppn E Φ (mword_of_int (KF + 0x28))
              (mword_of_int 15 : mword 5) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLI))
              (mword_of_int 0 : mword 64)
              R11 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_SHIFTIOP_SLLI_gpr (mword_of_int 10) (mword_of_int 15) (mword_of_int 52 : mword 6) s_pc);
                    replace (Z.eqb (uint (mword_of_int 15 : mword 5)) 0) with false by (vm_compute; reflexivity);
                    unfold gpr_slli_val, gpr_src;
                    rewrite Hva Hp10_11 (shift_bits_left52_zero p Hpal); reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi28 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R12 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> R11).
    assert (Hbnez2c : R12 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0)
      by (rewrite /R12 lookup_total_insert; reflexivity).
    assert (Hpp2c : add_vec_int (mword_of_int (KF + 0x28) : mword 64) 4 = mword_of_int (KF + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* +0x2c c.bnez a5,+60  NOT taken (a5 = 0): 4096-alignment holds, panic avoided *)
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (KF + 0x2c)) (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5)
              R12 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez2c; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp2e : add_vec_int (mword_of_int (KF + 0x2c) : mword 64) 2 = mword_of_int (KF + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.lui a2,0x1  (a2 := 4096, the memset length) *)
    iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (KF + 0x2e))
              (mword_of_int 12 : mword 5) (zero_extend' 5 ('b"00") : mword 5) (zero_extend' 5 ('b"00") : mword 5)
              (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI))
              (mword_of_int 4096 : mword 64)
              R12 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_UTYPE_LUI_gpr (mword_of_int 12) (sign_extend' 20 (mword_of_int 1 : mword 6)) s_pc);
                    replace (Z.eqb (uint (mword_of_int 12 : mword 5)) 0) with false by (vm_compute; reflexivity);
                    replace (luival (sign_extend' 20 (mword_of_int 1 : mword 6))) with (mword_of_int 4096 : mword 64) by (unfold luival; apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R13 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 4096 : mword 64)]> R12).
    assert (Hpp30 : add_vec_int (mword_of_int (KF + 0x2e) : mword 64) 2 = mword_of_int (KF + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.li a1,1  (a1 := 1, the memset fill byte) *)
    iApply (wp_gpr_write_s_config root_ppn E Φ (mword_of_int (KF + 0x30))
              (mword_of_int 11 : mword 5) (zero_extend' 5 ('b"00") : mword 5) (zero_extend' 5 ('b"00") : mword 5)
              (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 11), ADDI))
              (mword_of_int 1 : mword 64)
              R13 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion
              ltac:(vm_compute; discriminate)
              ltac:(intros s_pc Hnpc Hva Hvb;
                    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) (mword_of_int 11) (sign_extend' 12 (mword_of_int 1 : mword 6)) s_pc);
                    replace (Z.eqb (uint (mword_of_int 11 : mword 5)) 0) with false by (vm_compute; reflexivity);
                    replace (gpr_addi_val (zero_extend' 5 ('b"00")) (sign_extend' 12 (mword_of_int 1 : mword 6)) s_pc) with (mword_of_int 1 : mword 64) by (unfold gpr_addi_val; apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R14 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> R13).
    assert (Hpp32 : add_vec_int (mword_of_int (KF + 0x30) : mword 64) 2 = mword_of_int (KF + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- a0 (=p), a1 (=1), a2 (=4096), sp (=spr) at the memset call ---- *)
    assert (Hp10_14 : R14 !!! Regidx (mword_of_int 10 : mword 5) = p).
    { rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hp10. }
    assert (Hsp_14 : R14 !!! Regidx csp_rs1 = spr).
    { rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspR1. }
    iPoseProof (kfi_32 with "Htext") as "Hi32".
    (* +0x32 jal ra,memset : link ra := +0x36, jump to memset entry *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_jal_gpr_s_zca root_ppn E Φ (mword_of_int (KF + 0x32)) (mword_of_int 1 : mword 5) (mword_of_int 0x250 : mword 21)
              R14 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi32 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (Mms := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x32) : mword 64) 4)]> R14).
    assert (Htgtms : add_vec (mword_of_int (KF + 0x32) : mword 64) (sign_extend' 64 (mword_of_int 0x250 : mword 21)) = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtms) in "Hpc".
    (* ---- Mms register lookups ---- *)
    assert (HMmsa0 : Mms !!! Regidx (mword_of_int 10 : mword 5) = p)
      by (rewrite /Mms lookup_total_insert_ne; [ exact Hp10_14 | vm_compute; discriminate ]).
    assert (HMmsa1 : Mms !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 1 : mword 64)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert. reflexivity. }
    assert (HMmsa2 : Mms !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 4096 : mword 64)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert. reflexivity. }
    assert (HMmsra : Mms !!! Regidx (mword_of_int 1 : mword 5) = mword_of_int (KF + 0x36)).
    { rewrite /Mms lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (HMmssp : Mms !!! Regidx csp_rs1 = spr)
      by (rewrite /Mms lookup_total_insert_ne; [ exact Hsp_14 | vm_compute; discriminate ]).
    (* ---- memset's frame slots pa_ra = ms_ra, pa_s0 = ms_s0 ---- *)
    assert (Hpara : add_vec (add_vec (Mms !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = ms_ra)
      by (rewrite HMmssp; reflexivity).
    assert (Hps0 : add_vec (add_vec (Mms !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = ms_s0)
      by (rewrite HMmssp; reflexivity).
    (* +0x32 memset(p, 1, 4096) : fills the page, returns [page_own p] + gpr_file
       (ra/s0/s1/s2/sp/tp preserved).  The return target KF+0x36 is 2-aligned;
       wp_memset_page now supports that (Zca return), so only bit0 = 0 is needed. *)
    iApply (wp_memset_page root_ppn E Φ Mms (mword_of_int 1 : mword 64) mvra mvs0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              ltac:(rewrite HMmsa0; exact Hpv)
              HMmsa1 HMmsa2
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hmyg Hramcov Hpmpp Hpteregion Halignp HW HR
              ltac:(rewrite HMmsra; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile [Hmra] [Hms0] [Hpown] [-]").
    { iEval (rewrite Hpara). iExact "Hmra". }
    { iEval (rewrite Hps0). iExact "Hms0". }
    { iEval (rewrite HMmsa0). iExact "Hpown". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hbra Hbs0 Hpage Hgprf".
    iEval (rewrite HMmsa0) in "Hpage".
    iEval (rewrite Hpara) in "Hbra". iEval (rewrite Hps0) in "Hbs0".
    iDestruct "Hgprf" as (mfp) "[Hfile %Hpinsf]".
    destruct Hpinsf as (Hfra & Hfs0 & Hfs1 & Hfs2 & Hfsp & Hftp).
    assert (Hpc36 : update_vec_dec (add_vec (Mms !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x36)).
    { rewrite HMmsra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc36) in "Hpc".
    (* ---- memset preserved sp and tp; carry them to the acquire-entry map ---- *)
    assert (Hmfpsp : mfp !!! Regidx csp_rs1 = spr) by (rewrite Hfsp HMmssp; reflexivity).
    assert (HMmstp : Mms !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R4 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hmfptp : mfp !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5))
      by (rewrite Hftp HMmstp; reflexivity).
    iPoseProof (kfi_36 with "Htext") as "Hi36".
    iPoseProof (kfi_3a with "Htext") as "Hi3a".
    iPoseProof (kfi_3e with "Htext") as "Hi3e".
    (* +0x36 auipc s2,0x12 *)
    iApply (wp_auipc_s root_ppn E Φ (mword_of_int (KF + 0x36)) (mword_of_int 18 : mword 5) (mword_of_int 0x12 : mword 20)
              mfp mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi36 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (S1 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x36) : mword 64) (auipc_off (mword_of_int 0x12 : mword 20)))]> mfp).
    assert (Hpp3a : add_vec_int (mword_of_int (KF + 0x36) : mword 64) 4 = mword_of_int (KF + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3a) in "Hpc".
    (* +0x3a addi s2,s2,-1862  (s2 := &kmem) *)
    iApply (wp_addi4_s root_ppn E Φ (mword_of_int (KF + 0x3a)) (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x8ba : mword 12)
              S1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi3a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (S2 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec (S1 !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x8ba : mword 12)))]> S1).
    assert (Hs2kmem : S2 !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /S2 lookup_total_insert. rewrite /S1 lookup_total_insert. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp3e : add_vec_int (mword_of_int (KF + 0x3a) : mword 64) 4 = mword_of_int (KF + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* +0x3e c.mv a0,s2 *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x3e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              S2 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi3e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (S3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (S2 !!! Regidx (mword_of_int 18 : mword 5)))]> S2).
    assert (Hpp40 : add_vec_int (mword_of_int (KF + 0x3e) : mword 64) 2 = mword_of_int (KF + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* +0x40 jal ra,acquire *)
    iPoseProof (kfi_40 with "Htext") as "Hi40".
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_jal_gpr_s_zca root_ppn E Φ (mword_of_int (KF + 0x40)) (mword_of_int 1 : mword 5) (mword_of_int 0x182 : mword 21)
              S3 pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi40 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (Kacq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)]> S3).
    assert (Htgtacq : add_vec (mword_of_int (KF + 0x40) : mword 64) (sign_extend' 64 (mword_of_int 0x182 : mword 21)) = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtacq) in "Hpc".
    (* ---- the acquire-entry map [Kacq] lookups ---- *)
    assert (HKacqcsp : Kacq !!! Regidx csp_rs1 = spr).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hmfpsp. }
    assert (HKacqtp : Kacq !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hmfptp. }
    assert (HKacqa0 : Kacq !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert. rewrite Hs2kmem. apply add_vec_zero_l. }
    assert (HKacqra : Kacq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x40) : mword 64) 4)
      by (rewrite /Kacq; apply lookup_total_insert).
    assert (HKacqs2 : Kacq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs2kmem. }
    assert (Hmacq_s1 : Kacq !!! Regidx (mword_of_int 9 : mword 5) = p).
    { rewrite /Kacq lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S3 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S2 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /S1 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hfs1.
      rewrite /Mms lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R14 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R13 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R12 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R11 lookup_total_insert.
      rewrite /R10 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R9 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R8 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R7 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R6 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /R5 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hp10. apply add_vec_zero_l. }
    (* ---- acquire(&kmem) ---- *)
    iApply (wp_acquire_lock root_ppn E Φ γ (kmem_res fl) Kacq
              svpn_noff svpn_intena svpn_lk svpn_cpu
              qvr24 qvr16 qvr8 qpr24 qpr16 qpr8 qfraold qfs0old qcpuold
              qnoff qintena_old a0f
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion HW HR Hramcov
              Hlegal
              ltac:(rewrite HKacqa0 -Hlk; exact Hamo)
              ltac:(erewrite (po_mycpu_out_a0_cong _ _ m);
                    [ exact Hpin1
                    | repeat (first [ (rewrite lookup_total_insert_ne; [| vm_compute; discriminate])
                                    | rewrite po_mycpu_out_tp ]); exact Hmfptp ])
              ltac:(erewrite (po_mycpu_out_a0_cong _ _ m);
                    [ exact Hpin2
                    | repeat (first [ (rewrite lookup_total_insert_ne; [| vm_compute; discriminate])
                                    | rewrite po_mycpu_out_tp ]); exact Hmfptp ])
              ltac:(erewrite (po_mycpu_out_a0_cong _ _ m);
                    [ exact Hpin3
                    | repeat (first [ (rewrite lookup_total_insert_ne; [| vm_compute; discriminate])
                                    | rewrite po_mycpu_out_tp ]); exact Hmfptp ])
              ltac:(erewrite (po_mycpu_out_a0_cong _ _ m);
                    [ exact Hpin3
                    | repeat (first [ (rewrite lookup_total_insert_ne; [| vm_compute; discriminate])
                                    | rewrite po_mycpu_out_tp ]); exact Hmfptp ])
              Hmyg
              ltac:(rewrite HKacqtp; exact Hcpune)
              Hg_noff Hg_int
              ltac:(rewrite HKacqa0 -Hlk; exact Hg_lk)
              ltac:(rewrite HKacqa0 -Hlk; exact Hg_cpu)
              ltac:(rewrite HKacqra; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                    [Hqr24] [Hqr16] [Hqr8] [Hqp24] [Hqp16] [Hqp8] [Hqfra] [Hqfs0] Hqnoff Hqint [Hkmem] [Hqcpu] [-]").
    { iEval (rewrite HKacqcsp). iExact "Hqr24". }
    { iEval (rewrite HKacqcsp). iExact "Hqr16". }
    { iEval (rewrite HKacqcsp). iExact "Hqr8". }
    { iEval (rewrite HKacqcsp). iExact "Hqp24". }
    { iEval (rewrite HKacqcsp). iExact "Hqp16". }
    { iEval (rewrite HKacqcsp). iExact "Hqp8". }
    { iEval (rewrite HKacqcsp). iExact "Hqfra". }
    { iEval (rewrite HKacqcsp). iExact "Hqfs0". }
    { iEval (rewrite HKacqa0 -Hlk). rewrite /is_kmem. iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk). iExact "Hqcpu". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Htok HRres Hgpr
             Har24 Har16 Har8 Hajunk Hanoff Haint Hacpu".
    (* pc = ret_tgt(Kacq) = +0x44 ; hold [locked γ] + [kmem_res fl] *)
    assert (Hpc44 : update_vec_dec (add_vec (Kacq !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x44)).
    { rewrite HKacqra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc44) in "Hpc".
    iDestruct "Hgpr" as (macq) "[Hfile %Hacqpins]".
    destruct Hacqpins as (Hqra & Hqs0 & Hqs1 & Hqsp & Hqa0 & Hqtp & Hqs2).
    assert (Hs1p : macq !!! Regidx (mword_of_int 9 : mword 5) = p) by (rewrite Hqs1; exact Hmacq_s1).
    assert (Hs2km : macq !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem) by (rewrite Hqs2; exact HKacqs2).
    iPoseProof (kfi_44 with "Htext") as "Hi44".
    iPoseProof (kfi_48 with "Htext") as "Hi48".
    iPoseProof (kfi_4a with "Htext") as "Hi4a".
    (* the freelist head lives at fl = &kmem + 24 *)
    iDestruct "HRres" as (head pages) "[Hflw Hchain]".
    assert (Hldaddr : add_vec (macq !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite Hs2km Hfl. apply bv_eq; vm_compute; reflexivity. }
    (* +0x44 ld a5,24(s2) : a5 := *(kmem.freelist) = head *)
    iApply (wp_ld_s_ram root_ppn E Φ (mword_of_int (KF + 0x44)) (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              macq head mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi44 [Hflw] [-]").
    { iEval (rewrite -Hldaddr) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hldaddr) in "Hflw".
    set (Rld := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg head]> macq).
    assert (HRlds1 : Rld !!! Regidx (mword_of_int 9 : mword 5) = p)
      by (rewrite /Rld lookup_total_insert_ne; [ exact Hs1p | vm_compute; discriminate ]).
    assert (HRlds2 : Rld !!! Regidx (mword_of_int 18 : mword 5) = mword_of_int KernelSyms.kmem)
      by (rewrite /Rld lookup_total_insert_ne; [ exact Hs2km | vm_compute; discriminate ]).
    assert (HRlda5 : Rld !!! Regidx (mword_of_int 15 : mword 5) = head)
      by (rewrite /Rld; apply lookup_total_insert).
    assert (Hpp48 : add_vec_int (mword_of_int (KF + 0x44) : mword 64) 4 = mword_of_int (KF + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* +0x48 c.sd a5,0(s1) : p->next := head *)
    iEval (rewrite page_own_split) in "Hpage".
    iDestruct "Hpage" as "[Hhead Hrest]".
    iDestruct (page_head8_word_at p Hpv with "Hhead") as (wold) "Hpw".
    assert (Hsdaddr : add_vec (Rld !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))) = p).
    { replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000"))) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      rewrite HRlds1. apply kv_addv_zero. }
    iApply (wp_csd_s_ram root_ppn E Φ (mword_of_int (KF + 0x48)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")))
              Rld wold mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi48 [Hpw] [-]").
    { iEval (rewrite -Hsdaddr) in "Hpw". rewrite /word_at. iExact "Hpw". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hpw".
    iEval (rewrite Hsdaddr) in "Hpw".
    (* Rld!!!a5 = head, so the stored value is [head] *)
    iEval (rewrite HRlda5) in "Hpw".
    iAssert (run_page p head) with "[Hpw Hrest]" as "Hrun".
    { rewrite /run_page. rewrite /word_at. iFrame "Hpw Hrest". }
    assert (Hpp4a : add_vec_int (mword_of_int (KF + 0x48) : mword 64) 2 = mword_of_int (KF + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    (* +0x4a sd s1,24(s2) : kmem.freelist := p *)
    assert (Hsdaddr2 : add_vec (Rld !!! Regidx (mword_of_int 18 : mword 5)) (sign_extend' 64 (mword_of_int 0x18 : mword 12)) = fl).
    { rewrite HRlds2 Hfl. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_sd_s_ram root_ppn E Φ (mword_of_int (KF + 0x4a)) (mword_of_int 9 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 0x18 : mword 12)
              Rld head mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi4a [Hflw] [-]").
    { iEval (rewrite -Hsdaddr2) in "Hflw". rewrite /word_at. iExact "Hflw". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hflw".
    iEval (rewrite Hsdaddr2) in "Hflw".
    iEval (rewrite HRlds1) in "Hflw".
    (* refold the freelist invariant with [p] pushed *)
    iAssert (kmem_res fl) with "[Hflw Hrun Hchain]" as "HRres".
    { iApply (kmem_res_push fl p head pages Hpv). rewrite /word_at. iFrame "Hflw Hrun Hchain". }
    assert (Hpp4e : add_vec_int (mword_of_int (KF + 0x4a) : mword 64) 4 = mword_of_int (KF + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    iPoseProof (kfi_4e with "Htext") as "Hi4e".
    iPoseProof (kfi_50 with "Htext") as "Hi50".
    (* +0x4e c.mv a0,s2 : a0 := &kmem (release's argument) *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x4e)) (mword_of_int 10 : mword 5) (mword_of_int 18 : mword 5)
              Rld mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi4e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (Rae := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Rld !!! Regidx (mword_of_int 18 : mword 5)))]> Rld).
    assert (Hpp50 : add_vec_int (mword_of_int (KF + 0x4e) : mword 64) 2 = mword_of_int (KF + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp50) in "Hpc".
    (* +0x50 jal ra,release *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_jal_gpr_s_zca root_ppn E Φ (mword_of_int (KF + 0x50)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fa : mword 21)
              Rae pmpcfg0 pmpaddr00 region_pte (1/2)%Qp
              HN Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi50 [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (Rrel := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)]> Rae).
    assert (Htgtrel : add_vec (mword_of_int (KF + 0x50) : mword 64) (sign_extend' 64 (mword_of_int 0x1fa : mword 21)) = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtrel) in "Hpc".
    (* ---- release-entry map facts ---- *)
    assert (HRrelcsp : Rrel !!! Regidx csp_rs1 = spr).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rld lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hqsp. exact HKacqcsp. }
    assert (HRreltp : Rrel !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rld lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hqtp. exact HKacqtp. }
    assert (HRrela0 : Rrel !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int KernelSyms.kmem).
    { rewrite /Rrel lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Rae lookup_total_insert. rewrite HRlds2. apply add_vec_zero_l. }
    assert (HRrelra : Rrel !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KF + 0x50) : mword 64) 4)
      by (rewrite /Rrel; apply lookup_total_insert).
    (* convert acquire's returned frame windows to [spr]-based addresses *)
    iEval (rewrite HKacqcsp) in "Har24". iEval (rewrite HKacqcsp) in "Har16". iEval (rewrite HKacqcsp) in "Har8".
    iDestruct "Hajunk" as (vp24 vp16 vp8 vfra vfs0) "(Hqp24 & Hqp16 & Hqp8 & Hqfra & Hqfs0)".
    iEval (rewrite HKacqcsp) in "Hqp24". iEval (rewrite HKacqcsp) in "Hqp16". iEval (rewrite HKacqcsp) in "Hqp8".
    iEval (rewrite HKacqcsp) in "Hqfra". iEval (rewrite HKacqcsp) in "Hqfs0".
    (* ---- release(&kmem) ---- *)
    iApply (wp_release root_ppn E Φ γ lk (kmem_res fl) Rrel
              svpn_lk svpn_cpu svpn_noff svpn_intena
              (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)))
              q_noff_store
              (if eq_vec (sign_extend' 64 qnoff) zero_reg then acq_intena_store mstatus0 else qintena_old)
              (Kacq !!! Regidx (mword_of_int 1 : mword 5)) (Kacq !!! Regidx (mword_of_int 8 : mword 5)) (Kacq !!! Regidx (mword_of_int 9 : mword 5))
              vp24 vp16 vp8 qpr0 vfra vfs0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dqi:=DfracOwn 1)
              HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hfiom Hlpe Hpmpp Hpteregion HW HR Hramcov Hmyg
              ltac:(rewrite HRrela0 Hlk; apply bv_eq; vm_compute; reflexivity)
              Hg_lk
              ltac:(rewrite HRrela0 -Hlk; exact Hg_cpu)
              ltac:(rewrite HRreltp -Ha0fcpu; exact Hg_noff)
              ltac:(rewrite HRreltp -Ha0fcpu; exact Hg_int)
              ltac:(rewrite HRreltp; apply eq_vec_true_iff; reflexivity)
              Hsst Hnoffpos Hintena0
              ltac:(rewrite HRrelra; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile
                    [Hkmem] Htok HRres [Hacpu] [Hanoff] [Haint] [Har24] [Har16] [Har8]
                    [Hqp24] [Hqp16] [Hqp8] [Hqp0] [Hqfra] [Hqfs0] [-]").
    { iExact "Hkmem". }
    { iEval (rewrite HKacqa0 -Hlk HKacqtp) in "Hacpu". iEval (rewrite HRrela0 -Hlk). iExact "Hacpu". }
    { iEval (rewrite HRreltp -Ha0fcpu). iExact "Hanoff". }
    { iEval (rewrite HRreltp -Ha0fcpu). iExact "Haint". }
    { iEval (rewrite HRrelcsp). iExact "Har24". }
    { iEval (rewrite HRrelcsp). iExact "Har16". }
    { iEval (rewrite HRrelcsp). iExact "Har8". }
    { iEval (rewrite HRrelcsp). iExact "Hqp24". }
    { iEval (rewrite HRrelcsp). iExact "Hqp16". }
    { iEval (rewrite HRrelcsp). iExact "Hqp8". }
    { iEval (rewrite HRrelcsp). iExact "Hqp0". }
    { iEval (rewrite HRrelcsp). iExact "Hqfra". }
    { iEval (rewrite HRrelcsp). iExact "Hqfs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hgprr Hcpu2 Hnoff2 Hint2 Hjunk2".
    (* pc = ret_tgt(Rrel) = +0x54 ; lock released. epilogue restores the frame. *)
    assert (Hpc54 : update_vec_dec (add_vec (Rrel !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (KF + 0x54)).
    { rewrite HRrelra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc54) in "Hpc".
    iDestruct "Hgprr" as (mrel) "[Hfile %Hrelpins]".
    destruct Hrelpins as (Hrra & Hrs0 & Hrs1 & Hrsp & Hrtp).
    assert (HspMrel : mrel !!! Regidx csp_rs1 = spr) by (rewrite Hrsp; exact HRrelcsp).
    iPoseProof (kfi_54 with "Htext") as "Hi54".
    iPoseProof (kfi_56 with "Htext") as "Hi56".
    iPoseProof (kfi_58 with "Htext") as "Hi58".
    iPoseProof (kfi_5a with "Htext") as "Hi5a".
    iPoseProof (kfi_5c with "Htext") as "Hi5c".
    iPoseProof (kfi_5e with "Htext") as "Hi5e".
    (* +0x54 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x54)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (R1 !!! Regidx (mword_of_int 1 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi54 [Hr24]").
    { iEval (rewrite HspMrel). iEval (rewrite HspR1) in "Hr24". iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HspMrel) in "Hr24".
    set (Q54 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    assert (HspQ54 : Q54 !!! Regidx csp_rs1 = spr) by (rewrite /Q54 lookup_total_insert_ne; [ exact HspMrel | vm_compute; discriminate ]).
    assert (Hpp56 : add_vec_int (mword_of_int (KF + 0x54) : mword 64) 2 = mword_of_int (KF + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x56)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q54 (R1 !!! Regidx (mword_of_int 8 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi56 [Hr16]").
    { iEval (rewrite HspQ54). iEval (rewrite HspR1) in "Hr16". iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HspQ54) in "Hr16".
    set (Q56 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 8 : mword 5))]> Q54).
    assert (HspQ56 : Q56 !!! Regidx csp_rs1 = spr) by (rewrite /Q56 lookup_total_insert_ne; [ exact HspQ54 | vm_compute; discriminate ]).
    assert (Hpp58 : add_vec_int (mword_of_int (KF + 0x56) : mword 64) 2 = mword_of_int (KF + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x58)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q56 (R1 !!! Regidx (mword_of_int 9 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi58 [Hr8]").
    { iEval (rewrite HspQ56). iEval (rewrite HspR1) in "Hr8". iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HspQ56) in "Hr8".
    set (Q58 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 9 : mword 5))]> Q56).
    assert (HspQ58 : Q58 !!! Regidx csp_rs1 = spr) by (rewrite /Q58 lookup_total_insert_ne; [ exact HspQ56 | vm_compute; discriminate ]).
    assert (Hpp5a : add_vec_int (mword_of_int (KF + 0x58) : mword 64) 2 = mword_of_int (KF + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x5a)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q58 (R1 !!! Regidx (mword_of_int 18 : mword 5))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Hramcov HR
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi5a [Hr0]").
    { iEval (rewrite HspQ58). iEval (rewrite HspR1) in "Hr0". iExact "Hr0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr0".
    iEval (rewrite HspQ58) in "Hr0".
    set (Q5a := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (R1 !!! Regidx (mword_of_int 18 : mword 5))]> Q58).
    assert (HspQ5a : Q5a !!! Regidx csp_rs1 = spr) by (rewrite /Q5a lookup_total_insert_ne; [ exact HspQ58 | vm_compute; discriminate ]).
    assert (Hpp5c : add_vec_int (mword_of_int (KF + 0x5a) : mword 64) 2 = mword_of_int (KF + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.addi16sp sp,32 *)
    iDestruct (kv_cfg_split mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 HSIE HMPRV HSXL Hmm HPBMTE
                 with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa")
      as "(Hsm & Hpca & Hpaa & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2 & Hpcb & Hpab)".
    iApply (wp_caddi16sp_gpr_s root_ppn E Φ (mword_of_int (KF + 0x5c)) (mword_of_int 2 : mword 6) Q5a
              pmpcfg0 pmpaddr00 region_pte (1/2)%Qp HN Hmyg Hramcov Hpmpp Hpteregion
              with "Hsm Hpca Hpaa Htlbinv Hpc Hfile Hi5c [-]").
    iIntros "Hsm Hpca Hpaa Htlbinv Hpc Hfile".
    iDestruct (kv_cfg_recombine mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00
                 with "Hsm Hpca Hpaa Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Hpcb Hpab")
      as "(Hhs & Hpriv & Hms & Hmie & Hmdl & Hmenv & Hpmpc & Hpmpa)".
    set (Q5c := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q5a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q5a).
    assert (Hpp5e : add_vec_int (mword_of_int (KF + 0x5c) : mword 64) 2 = mword_of_int (KF + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* +0x5e c.ret *)
    assert (HQ5cra : Q5c !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q5c lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q5a lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q58 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q56 lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /Q54 lookup_total_insert.
      rewrite /R1 lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (KF + 0x5e)) (mword_of_int 1) Q5c
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion ltac:(vm_compute; discriminate) Hlpe
              ltac:(rewrite HQ5cra; exact Hretm)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi5e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite HQ5cra) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] [Hr24 Hr16 Hr8 Hr0 Hbra Hbs0]").
    { iExists Q5c. iFrame "Hfile". }
    { iExists (R1 !!! Regidx (mword_of_int 1 : mword 5)), (R1 !!! Regidx (mword_of_int 8 : mword 5)),
        (R1 !!! Regidx (mword_of_int 9 : mword 5)), (R1 !!! Regidx (mword_of_int 18 : mword 5)),
        (Mms !!! Regidx (mword_of_int 1 : mword 5)), (Mms !!! Regidx (mword_of_int 8 : mword 5)).
      iFrame "Hr24 Hr16 Hr8 Hr0 Hbra Hbs0". }
  Qed.

End Kfree.

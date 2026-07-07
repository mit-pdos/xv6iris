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
Require Import WpAcquireLock WpRelease.
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

  (* ============================================================= *)
  (* kfree: whole-function S-mode WP.  WORK IN PROGRESS -- the      *)
  (* prologue (four saves + addi4spn) and the first two body        *)
  (* instructions (auipc/addi that load a5 := <end>) are proven;    *)
  (* the tail (bounds/alignment checks, memset, acquire, freelist   *)
  (* push, release, epilogue) is [admit] pending the missing        *)
  (* per-instruction S-mode step lemmas -- see the comment there.   *)
  (* ============================================================= *)
  Lemma wp_kfree (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (lk fl : mword 64)
      (m : gmap regidx (mword 64))
      (vr24 vr16 vr8 vr0 : bv 64)
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
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
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
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ (mr : gmap regidx (mword 64)), gpr_file mr) -∗
      (∃ u1 u2 u3 u4 : bv 64, a_r24 ↦₈ u1 ∗ a_r16 ↦₈ u2 ∗ a_r8 ↦₈ u3 ∗ a_r0 ↦₈ u4) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE p spr a_r24 a_r16 a_r8 a_r0 ret_tgt
      HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hpmpp Hpteregion Halignp HW HR Hramcov Hmyg.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile #Hkmem Hpre Hr24 Hr16 Hr8 Hr0 Hcont".
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
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
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite HspR1). iExact "Hr24". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KF + 0x02) : mword 64) 2 = mword_of_int (KF + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 vr16 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite HspR1). iExact "Hr16". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KF + 0x04) : mword 64) 2 = mword_of_int (KF + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 vr8 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite HspR1). iExact "Hr8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KF + 0x06) : mword 64) 2 = mword_of_int (KF + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,0(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KF + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 vr0 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmyg Hramcov
              Hpmpp Hpteregion Halignp Hramcov HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi08 [Hr0] [-]").
    { iEval (rewrite HspR1). iExact "Hr0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KF + 0x08) : mword 64) 2 = mword_of_int (KF + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              R1 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KF + 0x0a) : mword 64) 2 = mword_of_int (KF + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c auipc a5,0x23 *)
    iApply (wp_auipc_s root_ppn E Φ (mword_of_int (KF + 0x0c)) (mword_of_int 15 : mword 5) (mword_of_int 0x23 : mword 20)
              R2 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (R3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec (mword_of_int (KF + 0x0c) : mword 64) (auipc_off (mword_of_int 0x23 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KF + 0x0c) : mword 64) 4 = mword_of_int (KF + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi a5,a5,-1260  (a5 := <end> = 0x80023558) *)
    iApply (wp_addi4_s root_ppn E Φ (mword_of_int (KF + 0x10)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 0xb14 : mword 12)
              R3 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hbnez24; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi24 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    assert (Hpp26 : add_vec_int (mword_of_int (KF + 0x24) : mword 64) 2 = mword_of_int (KF + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.mv s1,a0  (s1 := p) *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (KF + 0x26)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              R10 mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmyg Hramcov Hpmpp Hpteregion Halignp
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
    (* ------------------------------------------------------------------ *)
    (* TAIL ADMITTED at the memset call: +32 jal memset then                *)
    (* wp_memset_s_full_kt (WpMemsetInstr.v:312).  a0=p (page base), a1=1,   *)
    (* a2=4096 are all set.  memset consumes+returns [page_own p] (reshaped  *)
    (* into its per-byte window via an exists-commute).  This application    *)
    (* is the "heavy geometry bundle": wp_memset_s_full_kt demands ~20       *)
    (* per-page TLB/svpn side conditions (Hmask_b/Hvpn2b/Hpb_* over the 4096  *)
    (* byte window) plus the two callee scratch slots pa_ra/pa_s0, which     *)
    (* wp_kfree's statement must be extended to carry (analogous to how      *)
    (* wp_release threads po_slot_geom for its lock word).  Left for the     *)
    (* acquire/release-pattern follow-up.  Everything through +0x32's        *)
    (* argument setup, including both bounds-check panic branches, is proven.*)
    (* ------------------------------------------------------------------ *)
    admit.
  Admitted.

End Kfree.

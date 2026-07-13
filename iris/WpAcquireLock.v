(* WpAcquireLock.v -- the CSL acquire spec: given [is_lock γ lk R], a run of
   acquire() that RETURNS has taken the lock -- the caller's continuation
   receives the ownership token [locked γ] and the protected resource [R],
   both taken OUT of the lock invariant by the winning amoswap
   (WpLockLeaves.wp_amoswap_lockinv).  If the lock stays held the amoswap
   loop spins forever -- proved by Löb induction in [wp_acquire_lock_loop],
   where EACH iteration opens the invariant: a nonzero read re-enters the
   induction hypothesis (the c.bnez-taken step runs on the raw engine so its
   later strips the IH's), a zero read exits with [locked γ ∗ R].

   Both lemmas are clones of WpAcquireTop.wp_acquire{_spin} with the lock
   word accessed through the invariant instead of an owned byte window. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpEntryNew.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpKernelvecNew WpPushOff.
Require Import WpMycpu WpPushOffTop WpAmo WpAcquireMem WpHolding WpAcquireTop.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import WpLock WpLockLeaves WpHoldingInv WpPopOff.
Require Export WpSmodeLoad WpSmodeStore WpSmodeBtype.
(* QUALIFIED (no Import): sstatus SIE-bit bridges for hiding mstatus0. *)
Require WpGprCsrwC.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* The interrupt-enable byte that push_off (inside acquire) saves to
   mycpu()->intena when it acquires the first lock (noff 0 -> 1).  It is the
   sstatus.SIE bit and depends on [mstatus0] ALONE (not on the register-file
   map): it is [po_storeval32] with the PN8 chain reduced through
   [po_mycpu_out_s1] to [PN2!!!x15 = sstatus_read mstatus0].  Exposing it in
   this map-independent form lets callers whose acquire-entry map is existential
   (e.g. kfree, whose acquire runs after memset) name it in release's
   precondition. *)
Definition acq_intena_store (mstatus0 : mword 64) : mword 32 :=
  (autocast (T := mword)
     (subrange_vec_dec
        (and_vec
           (shift_bits_right (add_vec zero_reg (sstatus_read mstatus0))
              (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
        (Z.sub (Z.mul 4 8) 1) 0) : mword 32).

(* ===================================================================== *)
(* SIE=0 (folded into smode_config) collapses the saved interrupt-enable  *)
(* store to 0, so wp_acquire_lock's intena postcondition needs no          *)
(* mstatus0.  Bridges mirror WpRelease's sstatus_sie_clear_neq.            *)
(* ===================================================================== *)
Lemma acq_mword1_zero_of_ne_one (x : mword 1) :
  eq_vec x ('b"1") = false -> x = ('b"0" : mword 1).
Proof.
  intro H. apply eq_vec_false_iff in H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  assert (Hmod : bv_modulus 1 = 2) by (vm_compute; reflexivity).
  rewrite Hmod in Hr.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  assert (H0 : bv_unsigned ('b"0" : mword 1) = 0) by (vm_compute; reflexivity).
  rewrite H0.
  assert (Hne : bv_unsigned x <> 1).
  { intro Hc. apply H. apply bv_eq. rewrite H1. exact Hc. }
  lia.
Qed.

Lemma acq_sstatus_bit1_sie (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  Z.testbit (bv_unsigned (sstatus_read m)) 1 = false.
Proof.
  intro HSIE.
  assert (Hz : _get_Mstatus_SIE m = ('b"0" : mword 1)) by (apply acq_mword1_zero_of_ne_one; exact HSIE).
  unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
  apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz.
Qed.

Lemma acq_intena_store_zero (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  acq_intena_store m = zeros' 32.
Proof.
  intro HSIE.
  pose proof (acq_sstatus_bit1_sie m HSIE) as Hb1.
  assert (Hshamt : int_of_mword false (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0) = 1)
    by (vm_compute; reflexivity).
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) : mword 64) = 1)
    by (vm_compute; reflexivity).
  assert (Hsh0 : Z.testbit (bv_unsigned (shiftr (sstatus_read m) 1)) 0 = false).
  { unfold shiftr, with_word, MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (Hn1 : bv_unsigned (MachineWord.N_to_word (MachineWord.Z_idx 64) (MachineWord.Z_idx 1)) = 1)
      by (vm_compute; reflexivity).
    rewrite Hn1. rewrite (Z.shiftr_spec (bv_unsigned (sstatus_read m)) 1 0 ltac:(lia)). simpl (0 + 1)%Z. exact Hb1. }
  assert (Hand0 : and_vec (shift_bits_right (add_vec zero_reg (sstatus_read m))
                    (subrange_vec_dec (mword_of_int 1 : mword 6) (Z.sub log2_xlen 1) 0))
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) = (zeros' 64 : mword 64)).
  { rewrite aq_addv_zero_l. unfold shift_bits_right. rewrite Hshamt.
    apply bv_eq.
    assert (Hz64 : bv_unsigned (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
    rewrite Hz64. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask.
    apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
    destruct (decide (j = 0)) as [->|Hne].
    - rewrite Hsh0. reflexivity.
    - assert (Ht1 : Z.testbit 1 j = false)
        by (apply Z.bits_above_log2; [lia| change (Z.log2 1) with 0; lia]).
      rewrite Ht1. apply andb_false_r. }
  unfold acq_intena_store. rewrite Hand0. apply bv_eq. vm_compute. reflexivity.
Qed.

Section WpAcquireLock.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation PO := KernelSyms.push_off.

  Lemma wp_acquire_lock_loop (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (R : iProp Σ)
      (M0 : gmap regidx (mword 64)) (a5v lk : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch geometry over the loop body: a single X-bit fact + RAM coverage;
       the RAM/PMP fetch geometry is derived internally from instr_bytes *)
    (* the lock word's data-slot geometry is DERIVED inside [wp_amoswap_lockinv]
       from the lock invariant -- no premise. *)
    (* the amoswap.w PMA side-condition is DERIVED inside [wp_amoswap_lockinv]
       from [pma_allows_all] (which pins [PMA_atomic_support] to [AMOSwap]) --
       no premise. *)
    (* the loop-invariant register facts *)
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (AQ + 0x1a)) -∗
    gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) -∗
    is_lock γ lk R -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (AQ + 0x24)) -∗
      gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) -∗
      locked γ -∗ R -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros a4one HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 HM0a4 HM0s1.
    (* a5v-independent register/address facts, posed once outside the Löb *)
    assert (Ha4any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 14 : mword 5) = a4one).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0a4 | vm_compute; discriminate ]. }
    assert (Hs1any : forall w : mword 64,
        (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg w]> M0) !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { intro w. rewrite lookup_total_insert_ne; [ exact HM0s1 | vm_compute; discriminate ]. }
    assert (HAlk2 : add_vec (add_vec zero_reg lk) (zeros' 64) = lk).
    { rewrite aq_addv_zero_l.
      replace (zeros' 64 : mword 64) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    set (v1 := add_vec zero_reg a4one).
    assert (Hst1 : amoswap_stored v1 = (mword_of_int 1 : mword 32))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Htgt : add_vec (mword_of_int (AQ + 0x22) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0"))))
            = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv #Htext Hpc Hfile #Hlock Hcont".
    iPoseProof (aqi_1a with "Htext") as "#Hj1a".
    iPoseProof (aqi_1c with "Htext") as "#Hj1c".
    iPoseProof (aqi_20 with "Htext") as "#Hj20".
    iPoseProof (aqi_22 with "Htext") as "#Hj22".
    iRevert "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hcont".
    iLöb as "IH" forall (a5v).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hcont".
    (* ---- +0x1a: c.mv a5,a4 ---- *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (mword_of_int (AQ + 0x1a)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0)
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hj1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iEval (rewrite (Ha4any a5v) insert_insert) in "Hfile".
    assert (Hpp1c : add_vec_int (mword_of_int (AQ + 0x1a) : mword 64) 2 = mword_of_int (AQ + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- +0x1c: amoswap.w.aq a5,a5,(s1) through the invariant ---- *)
    assert (HPAlk : add_vec ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                              !!! Regidx (mword_of_int 9 : mword 5)) (zeros' 64) = lk)
      by (rewrite (Hs1any v1); exact HAlk2).
    assert (HSTZ : neq_vec (sign_extend' 64 (amoswap_stored
                     ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
                        !!! Regidx (mword_of_int 15 : mword 5)))) zero_reg = true)
      by (rewrite lookup_total_insert Hst1; vm_compute; reflexivity).
    iApply (wp_amoswap_lockinv root_ppn E Φ γ lk R (mword_of_int (AQ + 0x1c)) (mword_of_int 15) (mword_of_int 15) (mword_of_int 9)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v1]> M0)
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HNl HPAlk
              HSTZ
              ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hj1c Hlock [-]").
    iIntros (w) "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hpay".
    iEval (rewrite insert_insert) in "Hfile".
    assert (Hpp20 : add_vec_int (mword_of_int (AQ + 0x1c) : mword 64) 4 = mword_of_int (AQ + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* ---- +0x20: sext.w a5 ---- *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (AQ + 0x20)) (mword_of_int 15 : mword 5) (mword_of_int 0 : mword 6)
              (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (amoswap_loaded w)]> M0)
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hj20 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    iEval (rewrite lookup_total_insert insert_insert) in "Hfile".
    assert (Hroundw : sign_extend' 64 (subrange_vec_dec
        (add_vec (amoswap_loaded w) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)
        = sign_extend' 64 w) by (apply aq_sextw_round).
    iEval (rewrite Hroundw) in "Hfile".
    assert (Hpp22 : add_vec_int (mword_of_int (AQ + 0x20) : mword 64) 2 = mword_of_int (AQ + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    iDestruct "Hpay" as "[(%Hw0 & Htok & HRes) | %Hwnz]".
    - (* ---- w = 0: ACQUIRED -- c.bnez falls through; hand over token + R ---- *)
      subst w.
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (AQ + 0x22)) (mword_of_int 252) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0)
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hj22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpp24 : add_vec_int (mword_of_int (AQ + 0x22) : mword 64) 2 = mword_of_int (AQ + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Htok HRes").
    - (* ---- w <> 0: c.bnez TAKEN back to +0x1a; loop via the Löb IH ---- *)
    (* ---- +0x22: c.bnez a5 TAKEN (a5 = sext32(1) <> 0), back to +0x1a ----
       Run on the raw engine so the step's later strips the Löb IH's. *)
    iDestruct "Hpc" as "[Hpc Hnpc]".
    iDestruct "Hfile" as "[%Hdom Hfmap]".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ (mword_of_int (AQ + 0x22)) true
              (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hj22").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) !! Regidx (mword_of_int 15 : mword 5)
                  = Some ((<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 w)]> M0) !!! Regidx (mword_of_int 15 : mword 5)))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int (AQ + 0x22)) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int (mword_of_int (AQ + 0x22)) 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = mword_of_int (AQ + 0x22)).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (mword_of_int 15) _ s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ (mword_of_int (AQ + 0x1a)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro. iExists (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      replace (creg2reg_idx (Cregidx (mword_of_int 7))) with (Regidx (mword_of_int 15 : mword 5))
        by (vm_compute; reflexivity).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : neq_vec (rvv (mword_of_int 15) s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match.
        rewrite lookup_total_insert. exact Hwnz. }
      epose proof (exec_execute_BTYPE_BNE_taken (sign_extend' 13 (concat_vec (mword_of_int 252 : mword 8) ('b"0")))
                     (zero_extend' 5 ('b"00")) (mword_of_int 15) s_pc Htk) as Hred.
      rewrite Hpcv Htgt in Hred.
      exact (Hred ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC (mword_of_int (AQ + 0x1a))).(sregs) = mword_of_int (AQ + 0x1a))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    (* strip the step's later against the Löb hypothesis and loop *)
    iNext.
    iApply ("IH" $! (sign_extend' 64 w) with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp] [$Hpc' $Hnpc] [Hfmap] Hcont").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* [smode_config] view of the amoswap retry loop: unbundle -> raw loop ->
     rebundle.  The loop returns [mstatus0] unchanged, so the bundle round-trips
     cleanly and acquire's body never sees the raw cells. *)
  Lemma wp_acquire_lock_loop_scfg (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γc γ : gname) (R : iProp Σ)
      (M0 : gmap regidx (mword 64)) (a5v lk : mword 64)
      :
    let a4one : mword 64 := add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    M0 !!! Regidx (mword_of_int 14 : mword 5) = a4one ->
    M0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (AQ + 0x1a)) -∗
    gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg a5v]> M0) -∗
    is_lock γ lk R -∗
    ( smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (AQ + 0x24)) -∗
      gpr_file (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> M0) -∗
      locked γ -∗ R -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros a4one HN HNl HM0a4 HM0s1.
    iIntros "Hcfg Htlbinv #Htext Hpc Hfile #Hlock Hcont".
    iDestruct (smode_config_unbundle with "Hcfg") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (mstatus0) "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iApply (wp_acquire_lock_loop root_ppn E Φ γ R M0 a5v lk mstatus0 mie_v mdv0 menvcfg0
              HN HNl HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 HM0a4 HM0s1
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hlock [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Htok HRes".
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hcfg".
    iApply ("Hcont" with "Hcfg Htlbinv Hpc Hfile Htok HRes").
  Qed.

  (* [smode_config] leaf wrapper for the generic 8-byte RAM store. *)

  Lemma wp_acquire_lock (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (γ : gname) (R : iProp Σ)
      (m : gmap regidx (mword 64))
      (cpuold : bv 64)
      (n : nat)
      (noff intena_old : mword 32) (a0f : mword 64)
      (γc : gname) (bsie : mword 1)
      :
    let AQw : mword 64 := mword_of_int AQ in
    let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
    let sp0 := m !!! Regidx csp_rs1 in
    let spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (* acquire's own frame slots (ra/s0/s1 saves at spd+24/+16/+8) *)
    let a_r24 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_r16 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_r8  := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* push_off's frame below (its sp is spd): slots at spd-8/-16/-24 *)
    let po_spd := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let a_p24 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) in
    let a_p16 := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) in
    let a_p8  := add_vec po_spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    (* mycpu's frame under push_off: slots at spd-40/-48 *)
    let po_spm10 := add_vec po_spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec po_spm10 (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    (* the per-cpu noff/intena words *)
    let a_noff := add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_intena := add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    (* the spinlock's fields *)
    let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
    (* prologue register chain *)
    let A0 := <[Regidx csp_rs1 := regval_into_reg spd]> m in
    let A1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0 in
    let A2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1 in
    (* push_off's entry map (after the jal's link write) *)
    let P0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2 in
    (* push_off's internal register chain (mirrors wp_push_off's lets) *)
    let PN0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (P0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> P0 in
    let PN1 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (PN0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> PN0 in
    (* push_off's internal register chain PN2..PN8 + po_storeval32 (which
       read [sstatus_read mstatus0]) are reconstructed inside the proof over
       the unbundled mstatus0; they are not needed in the statement. *)
    let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
        (add_vec (sign_extend' 64 noff) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
    let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    (* the return target *)
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    ↑lockN ⊆ E ->
    (10 <= n)%nat ->
    (* S-mode configuration is now folded into [smode_config γc] below. *)
    (* ---- the amoswap.w PMA side-condition is DERIVED inside
       [wp_amoswap_lockinv] from [pma_allows_all] -- no premise. ---- *)
    (* ---- push_off's mycpu calls return &cpus[cpuid]; the per-map a0f pins
       are DERIVED inside the proof from this single tp-only fact (the a0
       output of po_mycpu_out depends on x4 alone -- po_mycpu_out_a0). ---- *)
    mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
    (* ---- fetch geometry: a single X-bit fact threaded to every instruction
       (covers acquire, push_off, holding, and both mycpu call sites); the
       RAM/PMP fetch geometry is derived internally from instr_bytes ---- *)
    (* ---- the lock is not already held by THIS cpu (no panic) ---- *)
    eq_vec (cpuold : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    (* ---- data-slot geometry is DERIVED in the leaves from the owned points-to
       (noff/intena/cpu) and the lock invariant (lk) -- no premise. ---- *)
    (* ---- the return target is well-aligned ---- *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    ghost_var γc (1/2) bsie -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is AQw -∗ gpr_file m -∗
    stack_own sp0 n -∗
    a_noff ↦₄ noff -∗
    a_intena ↦₄ intena_old -∗
    is_lock γ lk R -∗
    a_cpu ↦₈ cpuold -∗
    ( ∀ mfin,
      smode_config γc (DfracOwn 1) -∗
      ghost_var γc (1/2) bsie -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      locked γ -∗ R -∗
      gpr_file mfin -∗
      ⌜ callee_saved m mfin ⌝ -∗
      stack_own sp0 n -∗
      a_noff ↦₄ po_noff_store -∗
      a_intena ↦₄ (if eq_vec (sign_extend' 64 noff) zero_reg then (zeros' 32) else intena_old) -∗
      a_cpu ↦₈ (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros AQw lk sp0 spd a_r24 a_r16 a_r8 po_spd a_p24 a_p16 a_p8 po_spm10 a_fra a_fs0
      a_noff a_intena a_cpu A0 A1 A2 P0 PN0 PN1 po_noff_a5 po_noff_store ret_tgt
      HN HNl Hn Ha0 Hnotmine Hal0.
    iIntros "Hcfg Htoken Htlbinv #Htext Hpc Hfile
             Hstk Hnoff Hintena #Hlk Hcpu Hcont".
    (* peel the top 10 slots of the frame, frame the deeper region *)
    iDestruct (stack_own_split_1 sp0 10 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Htop".
    iDestruct "Htop" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (vr24) "Hr24".   iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8) "Hr8".     iDestruct "S4" as (vgap4) "Hgap4".
    iDestruct "S5" as (pr24) "Hp24".   iDestruct "S6" as (pr16) "Hp16".
    iDestruct "S7" as (pr8) "Hp8".     iDestruct "S8" as (vgap8) "Hgap8".
    iDestruct "S9" as (fraold) "Hfra". iDestruct "S10" as (fs0old) "Hfs0".
    (* bridges: clean [pa_stk sp0 k] = raw frame-slot spelling the body uses *)
    assert (Hb1 : a_r24 = pa_stk sp0 1).
    { rewrite /a_r24 /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : a_r16 = pa_stk sp0 2).
    { rewrite /a_r16 /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : a_r8 = pa_stk sp0 3).
    { rewrite /a_r8 /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : a_p24 = pa_stk sp0 5).
    { rewrite /a_p24 /po_spd /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : a_p16 = pa_stk sp0 6).
    { rewrite /a_p16 /po_spd /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : a_p8 = pa_stk sp0 7).
    { rewrite /a_p8 /po_spd /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : a_fra = pa_stk sp0 9).
    { rewrite /a_fra /po_spm10 /po_spd /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : a_fs0 = pa_stk sp0 10).
    { rewrite /a_fs0 /po_spm10 /po_spd /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24".  iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".   iEval (rewrite -Hb5) in "Hp24".
    iEval (rewrite -Hb6) in "Hp16".  iEval (rewrite -Hb7) in "Hp8".
    iEval (rewrite -Hb9) in "Hfra".  iEval (rewrite -Hb10) in "Hfs0".
    (* hold the ambient [smode_config γc] as [Hcfg] throughout; the caller's
       token Htoken is held aside and returned at the end. *)
    (* wp_push_off now takes smode_config + the single tp-only mycpu pin and
       returns the saved intena as the concrete zeros'32, so acquire needs
       neither the reconstructed PN chain nor po_storeval32 here. *)
    iPoseProof (aqi_00 with "Htext") as "Hi00".
    iPoseProof (aqi_02 with "Htext") as "Hi02".
    iPoseProof (aqi_04 with "Htext") as "Hi04".
    iPoseProof (aqi_06 with "Htext") as "Hi06".
    iPoseProof (aqi_08 with "Htext") as "Hi08".
    iPoseProof (aqi_0a with "Htext") as "Hi0a".
    iPoseProof (aqi_0c with "Htext") as "Hi0c".
    iPoseProof (aqi_10 with "Htext") as "Hi10".
    iPoseProof (aqi_12 with "Htext") as "Hi12".
    iPoseProof (aqi_16 with "Htext") as "Hi16".
    iPoseProof (aqi_18 with "Htext") as "Hi18".
    iPoseProof (aqi_1a with "Htext") as "Hi1a".
    iPoseProof (aqi_1c with "Htext") as "Hi1c".
    iPoseProof (aqi_20 with "Htext") as "Hi20".
    iPoseProof (aqi_22 with "Htext") as "Hi22".
    iPoseProof (aqi_24 with "Htext") as "Hi24".
    iPoseProof (aqi_28 with "Htext") as "Hi28".
    iPoseProof (aqi_2a with "Htext") as "Hi2a".
    iPoseProof (aqi_2c with "Htext") as "Hi2c".
    iPoseProof (aqi_2e with "Htext") as "Hi2e".
    iPoseProof (aqi_30 with "Htext") as "Hi30".
    iPoseProof (aqi_32 with "Htext") as "Hi32".
    (* the entry pc in the canonical (AQ + 0x00) spelling *)
    assert (Hpc00 : (mword_of_int AQ : mword 64) = mword_of_int (AQ + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite /AQw Hpc00) in "Hpc".
    (* slot-align components *)
    (* ---- 0x00: c.addi sp,-32 ---- *)
    iApply (wp_caddi_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x00)) csp_rs1 (mword_of_int 32 : mword 6) m (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with A0.
    assert (Hpp02 : add_vec_int (mword_of_int (AQ + 0x00) : mword 64) 2 = mword_of_int (AQ + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    assert (Hcsp0 : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0; apply lookup_total_insert).
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              A0 vr24 (dq:=DfracOwn 1) HN
              with "Hcfg Htlbinv Hpc Hfile Hi02 [Hr24] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
    assert (HA0ra : A0 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0ra) in "Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (AQ + 0x02) : mword 64) 2 = mword_of_int (AQ + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              A0 vr16 (dq:=DfracOwn 1) HN
              with "Hcfg Htlbinv Hpc Hfile Hi04 [Hr16] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
    assert (HA0s0 : A0 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s0) in "Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (AQ + 0x04) : mword 64) 2 = mword_of_int (AQ + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iApply (wp_csdsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              A0 vr8 (dq:=DfracOwn 1) HN
              with "Hcfg Htlbinv Hpc Hfile Hi06 [Hr8] [-]").
    { iEval (rewrite Hcsp0). iExact "Hr8". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
    assert (HA0s1 : A0 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /A0; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hcsp0 HA0s1) in "Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (AQ + 0x06) : mword 64) 2 = mword_of_int (AQ + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              A0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi08 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpp0a : add_vec_int (mword_of_int (AQ + 0x08) : mword 64) 2 = mword_of_int (AQ + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x0a)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              A1 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0a [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (A1 !!! Regidx (mword_of_int 10 : mword 5)))]> A1) with A2.
    assert (Hpp0c : add_vec_int (mword_of_int (AQ + 0x0a) : mword 64) 2 = mword_of_int (AQ + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* ---- 0x0c: jal ra,push_off ---- *)
    assert (EQ0e : add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 2 = mword_of_int (AQ + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn γc E Φ (mword_of_int (AQ + 0x0c)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fffba : mword 21)
              A2 1%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)]> A2) with P0.
    assert (Htgtpo : add_vec (mword_of_int (AQ + 0x0c) : mword 64) (sign_extend' 64 (mword_of_int 0x1fffba : mword 21)) = mword_of_int (PO + 0x00))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtpo) in "Hpc".
    (* ---- push_off ---- *)
    assert (HP0csp : P0 !!! Regidx csp_rs1 = spd).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hcsp0. }
    assert (HP0ra : P0 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x0c) : mword 64) 4)
      by (rewrite /P0; apply lookup_total_insert).
    assert (E1a : add_vec_int (mword_of_int (PO + 0x18) : mword 64) 2 = mword_of_int (PO + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    (* bundle push_off's whole 6-slot frame (acquire slots 5..10) into
       [stack_own spd 6] for [wp_push_off]. *)
    assert (Hsd : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own spd 6) with "[Hp24 Hp16 Hp8 Hgap8 Hfra Hfs0]" as "Hpstk".
    { rewrite -Hsd stack_own_slots. cbn [seq].
      iSplitL "Hp24"; [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 1) -Hb5); iExact "Hp24"|].
      iSplitL "Hp16"; [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 2) -Hb6); iExact "Hp16"|].
      iSplitL "Hp8";  [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 3) -Hb7); iExact "Hp8"|].
      iSplitL "Hgap8"; [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 4)); iExact "Hgap8"|].
      iSplitL "Hfra"; [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 5) -Hb9); iExact "Hfra"|].
      iSplitL "Hfs0"; [iExists _; iEval (rewrite (pa_stk_assoc sp0 4 6) -Hb10); iExact "Hfs0"|].
      done. }
    iApply (wp_push_off root_ppn γc E Φ P0 noff intena_old a0f 6
              ltac:(lia) HN ltac:(vm_compute; reflexivity)
              ltac:(rewrite HP0ra; vm_compute; reflexivity)
              ltac:(rewrite /P0 lookup_total_insert_ne; [| vm_compute; discriminate];
                    rewrite /A2 lookup_total_insert_ne; [| vm_compute; discriminate];
                    rewrite /A1 lookup_total_insert_ne; [| vm_compute; discriminate];
                    rewrite /A0 lookup_total_insert_ne; [| vm_compute; discriminate]; exact Ha0)
              with "Hcfg Htlbinv Htext Hpc Hfile [Hpstk] [Hnoff] [Hintena] [-]").
    { iEval (rewrite HP0csp). iExact "Hpstk". }
    { iExact "Hnoff". }
    { iExact "Hintena". }
    iIntros (mfin) "Hcfg Htlbinv Hpc Hfile %Hmf Hpstk Hnoff Hintena".
    iEval (rewrite HP0csp) in "Hpstk".
    (* unbundle back into the 6 individual frame cells acquire tracks *)
    iEval (rewrite -Hsd stack_own_slots; cbn [seq]) in "Hpstk".
    iDestruct "Hpstk" as "(R1 & R2 & R3 & R4 & R5 & R6 & _)".
    iDestruct "R1" as (up24) "Hp24". iEval (rewrite (pa_stk_assoc sp0 4 1) -Hb5) in "Hp24".
    iDestruct "R2" as (up16) "Hp16". iEval (rewrite (pa_stk_assoc sp0 4 2) -Hb6) in "Hp16".
    iDestruct "R3" as (up8) "Hp8".   iEval (rewrite (pa_stk_assoc sp0 4 3) -Hb7) in "Hp8".
    iDestruct "R4" as (ug8) "Hgap8". iEval (rewrite (pa_stk_assoc sp0 4 4)) in "Hgap8".
    iDestruct "R5" as (ufra) "Hfra". iEval (rewrite (pa_stk_assoc sp0 4 5) -Hb9) in "Hfra".
    iDestruct "R6" as (ufs0) "Hfs0". iEval (rewrite (pa_stk_assoc sp0 4 6) -Hb10) in "Hfs0".
    iAssert (∃ wra0 ws00 : bv 64, a_fra ↦₈ wra0 ∗ a_fs0 ↦₈ ws00)%I with "[Hfra Hfs0]" as "Hjunk".
    { iExists ufra, ufs0. iFrame. }
    assert (Hpc10 : update_vec_dec (add_vec (P0 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x10))
      by (rewrite HP0ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    unfold callee_saved in Hmf.
    destruct Hmf as (Hfsp_ & Hftp_ & Hfs0_ & Hfs1_ & Hfs2_ & Hfs3_ & Hfs4_ & Hfs5_ & Hfs6_ & Hfs7_ & Hfs8_ & Hfs9_ & Hfs10_ & Hfs11_).
    (* canonical values of the tracked registers after push_off *)
    assert (HP0s1 : P0 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert.
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0tp : P0 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s0 : P0 !!! Regidx (mword_of_int 8 : mword 5) = A1 !!! Regidx (mword_of_int 8 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s2 : P0 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s3 : P0 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s4 : P0 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s5 : P0 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s6 : P0 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s7 : P0 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s8 : P0 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s9 : P0 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s10 : P0 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HP0s11 : P0 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { rewrite /P0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /A0. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. reflexivity. }
    rewrite HP0s1 in Hfs1_. rewrite HP0csp in Hfsp_. rewrite HP0tp in Hftp_.
    rewrite HP0s2 in Hfs2_. rewrite HP0s3 in Hfs3_. rewrite HP0s4 in Hfs4_. rewrite HP0s5 in Hfs5_.
    rewrite HP0s6 in Hfs6_. rewrite HP0s7 in Hfs7_. rewrite HP0s8 in Hfs8_.
    rewrite HP0s9 in Hfs9_. rewrite HP0s10 in Hfs10_. rewrite HP0s11 in Hfs11_.
    (* ---- 0x10: c.mv a0,s1 ---- *)
    iApply (wp_cmv_gpr_s_config_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfin (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfin !!! Regidx (mword_of_int 9 : mword 5)))]> mfin).
    assert (Hpp12 : add_vec_int (mword_of_int (AQ + 0x10) : mword 64) 2 = mword_of_int (AQ + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- 0x12: jal ra,holding ---- *)
    assert (EQ14 : add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 2 = mword_of_int (AQ + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_gpr_s root_ppn γc E Φ (mword_of_int (AQ + 0x12)) (mword_of_int 1 : mword 5) (mword_of_int 0x1fff88 : mword 21)
              B1 1%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)]> B1).
    assert (Htgtho : add_vec (mword_of_int (AQ + 0x12) : mword 64) (sign_extend' 64 (mword_of_int 0x1fff88 : mword 21)) = mword_of_int KernelSyms.holding)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtho) in "Hpc".
    (* ---- holding() (fast path) ---- *)
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = add_vec zero_reg (add_vec zero_reg lk)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert. rewrite Hfs1_. reflexivity. }
    assert (HB2ra : B2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (AQ + 0x12) : mword 64) 4)
      by (rewrite /B2; apply lookup_total_insert).
    assert (Eh2 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 2 = mword_of_int (KernelSyms.holding + 2))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh4 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 4 = mword_of_int (KernelSyms.holding + 4))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Eh6 : add_vec_int (mword_of_int KernelSyms.holding : mword 64) 6 = mword_of_int (KernelSyms.holding + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HAlk : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lk).
    { rewrite HB2a0. rewrite !aq_addv_zero_l.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12)) with (mword_of_int 0 : mword 64)
        by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* address bridges into wp_holding_lockinv's own lets *)
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spd).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfsp_. }
    assert (HB2tp : B2 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hftp_. }
    assert (HB2s2 : B2 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs2_. }
    assert (HB2s3 : B2 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs3_. }
    assert (HB2s4 : B2 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs4_. }
    assert (HB2s5 : B2 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs5_. }
    assert (HB2s6 : B2 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs6_. }
    assert (HB2s7 : B2 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs7_. }
    assert (HB2s8 : B2 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs8_. }
    assert (HB2s9 : B2 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs9_. }
    assert (HB2s10 : B2 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs10_. }
    assert (HB2s11 : B2 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs11_. }
    assert (HAcpu2 : add_vec (B2 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu)
      by (rewrite HB2a0 !aq_addv_zero_l; reflexivity).
    assert (Hspdh_eq : add_vec (B2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = po_spd)
      by (rewrite HB2sp; reflexivity).
    iDestruct "Hjunk" as (vfra0 vfs00) "[Hfra2 Hfs02]".
    iApply (wp_holding_lockinv root_ppn γc E Φ γ lk R B2 cpuold
              up24 up16 up8 vfra0 vfs00
              (dqc:=DfracOwn 1)
              HN HNl HAlk
              ltac:(rewrite HB2tp; exact Hnotmine)
              ltac:(rewrite HB2ra; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile
                    Hlk [Hcpu] [Hp24] [Hp16] [Hp8] [Hfra2] [Hfs02] [-]").
    { iEval (rewrite HAcpu2). iExact "Hcpu". }
    { iEval (rewrite Hspdh_eq). iExact "Hp24". }
    { iEval (rewrite Hspdh_eq). iExact "Hp16". }
    { iEval (rewrite Hspdh_eq). iExact "Hp8". }
    { iEval (rewrite Hspdh_eq). iExact "Hfra2". }
    { iEval (rewrite Hspdh_eq). iExact "Hfs02". }
    iIntros (mh) "Hcfg Htlbinv Hpc Hfile %Hmhf Hcpu Hhj".
    iEval (rewrite HAcpu2) in "Hcpu".
    destruct Hmhf as (Hmcs & Hma0).
    unfold callee_saved in Hmcs.
    destruct Hmcs as (Hmsp & Hmtp & Hhs0 & Hms1 & Hms2 & Hms3 & Hms4 & Hms5 & Hms6 & Hms7 & Hms8 & Hms9 & Hms10 & Hms11).
    iDestruct "Hhj" as (w24 w16 w8 wra ws0) "(Hp24 & Hp16 & Hp8 & Hfra & Hfs0)".
    iEval (rewrite Hspdh_eq) in "Hp24". iEval (rewrite Hspdh_eq) in "Hp16".
    iEval (rewrite Hspdh_eq) in "Hp8". iEval (rewrite Hspdh_eq) in "Hfra".
    iEval (rewrite Hspdh_eq) in "Hfs0".
    assert (Hpc16 : update_vec_dec (add_vec (B2 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = mword_of_int (AQ + 0x16))
      by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    (* ---- 0x16: c.li a4,1 ---- *)
    iApply (wp_cli_s root_ppn γc E Φ (mword_of_int (AQ + 0x16)) (mword_of_int 14 : mword 5)
              (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              mh (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              ltac:(reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (B5 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mh).
    assert (Hpp18 : add_vec_int (mword_of_int (AQ + 0x16) : mword 64) 2 = mword_of_int (AQ + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* ---- 0x18: c.bnez a0 (NOT taken: a0 = 0) ---- *)
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)).
    { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hma0. }
    iApply (wp_cbnez_fall_s_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x18)) (mword_of_int 14) (Cregidx (mword_of_int 2)) (mword_of_int 10)
              B5 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite HB5a0; vm_compute; reflexivity)
              with "Hcfg Htlbinv Hpc Hfile Hi18 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (AQ + 0x18) : mword 64) 2 = mword_of_int (AQ + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ---- 0x1a..0x22: the test-and-set loop, THROUGH the lock invariant ---- *)
    assert (HB2s1 : B2 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hfs1_. }
    assert (HB5a4L : B5 !!! Regidx (mword_of_int 14 : mword 5)
                    = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (rewrite /B5; apply lookup_total_insert).
    assert (HB5s1 : B5 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms1. exact HB2s1. }
    iDestruct "Hfile" as "[%HdomB5 HfmapB5]".
    assert (HB5l : B5 !! Regidx (mword_of_int 15 : mword 5)
                   = Some (B5 !!! Regidx (mword_of_int 15 : mword 5)))
      by (apply lookup_lookup_total_dom; apply HdomB5).
    iApply (wp_acquire_lock_loop_scfg root_ppn E Φ γc γ R B5 (B5 !!! Regidx (mword_of_int 15 : mword 5)) lk
              HN HNl HB5a4L HB5s1
              with "Hcfg Htlbinv Htext Hpc [HfmapB5] Hlk [-]").
    { rewrite insert_id; [| exact HB5l ].
      iSplitR; [iPureIntro; exact HdomB5 | iExact "HfmapB5"]. }
    iIntros "Hcfg Htlbinv Hpc Hfile Htok HRes".
    set (B8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 32))]> B5).
    (* ---- 0x24: jal ra,mycpu; the whole mycpu() ---- *)
    assert (HB8sp : B8 !!! Regidx csp_rs1 = spd).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmsp. exact HB2sp. }
    assert (HB9sp : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4)]> B8) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact HB8sp | vm_compute; discriminate ]).
    (* the mycpu frame slots coincide with push_off's r24/r16 cells *)
    assert (Hmra : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = a_p24).
    { rewrite /a_p24 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hms0 : add_vec (add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = a_p16).
    { rewrite /a_p16 /po_spd !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* mycpu's 2-slot frame as [pa_stk spd 1/2] = a_p24 / a_p16 *)
    assert (Hbp1 : pa_stk spd 1 = a_p24).
    { rewrite -Hmra. unfold pa_stk, add_vec_int. rewrite !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hbp2 : pa_stk spd 2 = a_p16).
    { rewrite -Hms0. unfold pa_stk, add_vec_int. rewrite !po_addv_assoc. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iApply (wp_pushoff_call_mycpu_scfg_cs root_ppn γc E Φ (mword_of_int (AQ + 0x24)) (mword_of_int 0xcb8 : mword 21) B8
              HN ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile Hi24 [Hp24 Hp16] [-]").
    { iEval (rewrite HB9sp). iApply (stack_own_2_intro with "[Hp24] [Hp16]").
      - iEval (rewrite Hbp1). iExact "Hp24".
      - iEval (rewrite Hbp2). iExact "Hp16". }
    iIntros (C1) "Hcfg Htlbinv Hpc Hfile %Hmc Hstk".
    iEval (rewrite HB9sp) in "Hstk".
    iDestruct (stack_own_2_elim with "Hstk") as (wcra wcs0) "(Hp24 & Hp16)".
    iEval (rewrite Hbp1) in "Hp24". iEval (rewrite Hbp2) in "Hp16".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc28 : update_vec_dec (add_vec (add_vec_int (mword_of_int (AQ + 0x24) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (AQ + 0x28) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc28) in "Hpc".
    destruct Hmc as (Hmc_cs & Hmc_a0).
    unfold callee_saved in Hmc_cs.
    destruct Hmc_cs as (Hmc_csp & Hmc_tp & Hmc_s0 & Hmc_s1 & Hmc_s2 & Hmc_s3 & Hmc_s4 & Hmc_s5 & Hmc_s6 & Hmc_s7 & Hmc_s8 & Hmc_s9 & Hmc_s10 & Hmc_s11).
    (* ---- 0x28: c.sd a0,16(s1) : lk->cpu := &cpus[cpuid] ---- *)
    assert (HB8s1 : B8 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HB5s1. }
    assert (HC1s1 : C1 !!! Regidx (mword_of_int 9 : mword 5) = add_vec zero_reg lk).
    { rewrite Hmc_s1. exact HB8s1. }
    assert (HAcpu : add_vec (C1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 16 : mword 12)) = a_cpu).
    { rewrite HC1s1 aq_addv_zero_l. reflexivity. }
    iApply (wp_csd_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x28)) (mword_of_int 10) (mword_of_int 9)
              (mword_of_int 16) C1 cpuold (dq:=DfracOwn 1)
              HN
              with "Hcfg Htlbinv Hpc Hfile Hi28 [Hcpu] [-]").
    { iEval (rewrite HAcpu). iExact "Hcpu". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hcpu".
    iEval (rewrite HAcpu) in "Hcpu".
    (* the stored value is mycpu's return &cpus[cpuid] *)
    assert (HB8tp : B8 !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hmtp. exact HB2tp. }
    assert (HB8s2 : B8 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms2. exact HB2s2. }
    assert (HB8s3 : B8 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms3. exact HB2s3. }
    assert (HB8s4 : B8 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms4. exact HB2s4. }
    assert (HB8s5 : B8 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms5. exact HB2s5. }
    assert (HB8s6 : B8 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms6. exact HB2s6. }
    assert (HB8s7 : B8 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms7. exact HB2s7. }
    assert (HB8s8 : B8 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms8. exact HB2s8. }
    assert (HB8s9 : B8 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms9. exact HB2s9. }
    assert (HB8s10 : B8 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms10. exact HB2s10. }
    assert (HB8s11 : B8 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { rewrite /B8. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /B5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite Hms11. exact HB2s11. }
    assert (HC1a0 : C1 !!! Regidx (mword_of_int 10 : mword 5) = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))).
    { rewrite Hmc_a0 HB8tp. reflexivity. }
    iEval (rewrite HC1a0) in "Hcpu".
    assert (Hpp2a : add_vec_int (mword_of_int (AQ + 0x28) : mword 64) 2 = mword_of_int (AQ + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* ---- 0x2a: c.ldsp ra,24(sp) ---- *)
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spd).
    { rewrite Hmc_csp. exact HB8sp. }
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x2a)) (mword_of_int 3) (mword_of_int 1 : mword 5)
              C1 (m !!! Regidx (mword_of_int 1 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi2a [Hr24]").
    { iEval (rewrite HC1sp). iExact "Hr24". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr24".
    iEval (rewrite HC1sp) in "Hr24".
    set (D1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> C1).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spd)
      by (rewrite /D1; rewrite lookup_total_insert_ne; [ exact HC1sp | vm_compute; discriminate ]).
    assert (Hpp2c : add_vec_int (mword_of_int (AQ + 0x2a) : mword 64) 2 = mword_of_int (AQ + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ---- 0x2c: c.ldsp s0,16(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x2c)) (mword_of_int 2) (mword_of_int 8 : mword 5)
              D1 (m !!! Regidx (mword_of_int 8 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi2c [Hr16]").
    { iEval (rewrite HD1sp). iExact "Hr16". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr16".
    iEval (rewrite HD1sp) in "Hr16".
    set (D2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> D1).
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spd)
      by (rewrite /D2; rewrite lookup_total_insert_ne; [ exact HD1sp | vm_compute; discriminate ]).
    assert (Hpp2e : add_vec_int (mword_of_int (AQ + 0x2c) : mword 64) 2 = mword_of_int (AQ + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ---- 0x2e: c.ldsp s1,8(sp) ---- *)
    iApply (wp_cldsp_gpr_s_ram_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x2e)) (mword_of_int 1) (mword_of_int 9 : mword 5)
              D2 (m !!! Regidx (mword_of_int 9 : mword 5))
              (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi2e [Hr8]").
    { iEval (rewrite HD2sp). iExact "Hr8". }
    iIntros "Hcfg Htlbinv Hpc Hfile Hr8".
    iEval (rewrite HD2sp) in "Hr8".
    set (D3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> D2).
    assert (HD3sp : D3 !!! Regidx csp_rs1 = spd)
      by (rewrite /D3; rewrite lookup_total_insert_ne; [ exact HD2sp | vm_compute; discriminate ]).
    assert (Hpp30 : add_vec_int (mword_of_int (AQ + 0x2e) : mword 64) 2 = mword_of_int (AQ + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ---- 0x30: c.addi16sp sp,32 ---- *)
    iApply (wp_caddi16sp_gpr_s root_ppn γc E Φ (mword_of_int (AQ + 0x30)) (mword_of_int 2 : mword 6) D3
              1%Qp HN
              with "Hcfg Htlbinv Hpc Hfile Hi30 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (D4 := <[Regidx csp_rs1 := regval_into_reg (add_vec (D3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> D3).
    assert (Hpp32 : add_vec_int (mword_of_int (AQ + 0x30) : mword 64) 2 = mword_of_int (AQ + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp32) in "Hpc".
    (* ---- 0x32: c.ret ---- *)
    assert (HD4ra : D4 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /D1. apply lookup_total_insert. }
    iApply (wp_cret_s_zca_scfg root_ppn γc E Φ (mword_of_int (AQ + 0x32)) (mword_of_int 1 : mword 5) D4
              (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate)
              ltac:(rewrite HD4ra; exact Hal0)
              with "Hcfg Htlbinv Hpc Hfile Hi32 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    iEval (rewrite HD4ra) in "Hpc".
    (* ---- rebundle the 10 frame slots back into [stack_own sp0 n].  The body
       leaves each slot's [word_pointsto] address in a spelling convertible to
       the clean [a_XX] let (as the old ∃-post consumed it), so we fold the
       goal's [pa_stk sp0 k] to [a_XX] with the bridges and close by conversion;
       the gap slots (4, 8) are already [pa_stk]-addressed from the peel. ---- *)
    iAssert (stack_own sp0 10) with "[Hr24 Hr16 Hr8 Hgap4 Hp24 Hp16 Hp8 Hgap8 Hfra Hfs0]" as "Htop".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iExists _; iEval (rewrite -Hb1); iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iEval (rewrite -Hb2); iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iEval (rewrite -Hb3); iExact "Hr8"|].
      iSplitL "Hgap4"; [by iExists _|].
      iSplitL "Hp24"; [iExists _; iEval (rewrite -Hb5); iExact "Hp24"|].
      iSplitL "Hp16"; [iExists _; iEval (rewrite -Hb6); iExact "Hp16"|].
      iSplitL "Hp8";  [iExists _; iEval (rewrite -Hb7); iExact "Hp8"|].
      iSplitL "Hgap8"; [by iExists _|].
      iSplitL "Hfra"; [iExists _; iEval (rewrite -Hb9); iExact "Hfra"|].
      iSplitL "Hfs0"; [iExists _; iEval (rewrite -Hb10); iExact "Hfs0"|].
      done. }
    iDestruct (stack_own_split_2 sp0 10 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    (* ---- hand everything to the caller's continuation ---- *)
    iApply ("Hcont" $! D4 with "Hcfg Htoken Htlbinv Hpc Htok HRes Hfile [%] Hstk Hnoff [Hintena] Hcpu").
    { unfold callee_saved. repeat split.
      - (* sp *)
        rewrite /D4. rewrite lookup_total_insert. rewrite HD3sp.
        rewrite /spd po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                         (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero.
      - (* tp *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_tp. exact HB8tp.
      - (* s0 (x8) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. apply lookup_total_insert.
      - (* s1 (x9) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. apply lookup_total_insert.
      - (* s2 (x18): preserved across the whole acquire *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s2. exact HB8s2.
      - (* s3 (x19) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s3. exact HB8s3.
      - (* s4 (x20) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s4. exact HB8s4.
      - (* s5 (x21) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s5. exact HB8s5.
      - (* s6 (x22) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s6. exact HB8s6.
      - (* s7 (x23) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s7. exact HB8s7.
      - (* s8 (x24) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s8. exact HB8s8.
      - (* s9 (x25) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s9. exact HB8s9.
      - (* s10 (x26) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s10. exact HB8s10.
      - (* s11 (x27) *)
        rewrite /D4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /D1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s11. exact HB8s11.
    }
    iExact "Hintena".
  Qed.

End WpAcquireLock.

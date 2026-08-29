(* WpSmodePtLock.v -- lock-invariant instruction leaves over [tlb_inv_pt]
   (ports of WpLockLeaves.v).  Same absorption recipe as the data leaves;
   the lock invariant is opened inside the engine callback and re-closed
   before the step commits.  The byte facts are re-derived from the
   gen_heap AFTER the absorption [iMod] (the ADUE write-back only touches
   page-table pages, never the lock word). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpGpr WpMmodeLeafBase.
Require Import WpAmo.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* Local width-4 helpers (Local in WpSmodeLoad.v, so re-proved here). *)


Section ExecAmoGS4walkPt.
  Variable rs2 rs1 rd : mword 5.
  Variable region : PMA_Region.
  Variable w : mword 32.
  Variable s s' : mstate.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s'.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64).
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Variable pa : mword 64.
  Let storeval : mword 32 :=
    sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, true, false, Data, Data))) s
                    = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr a8) (Atomic (AMOSWAP, true, false, Data, Data))) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hamo : pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s'.(mem) !! (pa_add pa j) = Some (nth_byte w j).

  Lemma exec_execute_AMOSWAP_4_gpr_S_walk_pt :
    exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            set_reg (MState s'.(sregs) (write_bytes s'.(mem) pa 4 storeval) s'.(mdev))
                    (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
  Proof.
    change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
      with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
    unfold execute_AMO. cbn zeta.
    rewrite exec_catch_early_return.
    assert (Hae : exec (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2)) "extensions/A/zaamo_insts.sail:73.32-73.33") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae).
    assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (AMOSWAP, true, false, Data, Data)) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, true, false, Data, Data)) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      rewrite Ha8ea. apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s')).
    cbn beta match.
    (* upstream reordered the body: the effective-address announcement and the
       load now run BEFORE rs2 is read *)
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_ea_amo_4 PBMT_PMA pa region (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo eq_refl Hmprv' Hcp')).
    cbn match.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_read_amo_4_S PBMT_PMA pa region w (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev
                 (fun j Hj => Hbytes j Hj) eq_refl Hmprv' Hcp')).
    cbn match. rewrite execR_returnR. cbn match.
    replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
    cbv iota.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s')).
    cbn beta. rewrite execR_returnR. cbn match.
    cbn zeta. cbn match.
    replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
    rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _
              (exec_mem_write_value_amo_4_S PBMT_PMA pa region _ (register_lookup mstatus s'.(sregs)) s'
                 HA Hord Hrange HR HW Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv' Hcp')).
    cbn match.
    match goal with |- context[execR _ ?st] =>
      set (s_m := st)
    end.
    assert (HwX : execR (Defs.liftR (wX_bits (Regidx rd)
                     (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))
                   : Defs.monadR ExecutionResult exception unit) s_m
                  = Some (inr tt,
                          set_reg s_m (R_bitvector_64 (gpr_of_Z (uint rd)))
                            (regval_into_reg (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))))).
    { rewrite execR_liftR.
      rewrite (exec_wX_bits_gpr rd _ s_m).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      reflexivity. }
    rewrite (execR_bind0_Some _ _ _ _ HwX).
    rewrite execR_returnR.
    cbn.
    reflexivity.
  Qed.
End ExecAmoGS4walkPt.

Section WpSmodePtLock.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.











End WpSmodePtLock.

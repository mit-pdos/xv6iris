(* WpGprRvcTor.v -- TOR-aware 8-byte stack WPs: [wp_csdsp_gpr_tor] and
   [wp_cldsp_gpr_tor], clones of WpGprRvc's [wp_csdsp_gpr]/[wp_cldsp_gpr] whose
   [pmp_all_off] data-side premise is replaced by the weaker TOR-entry-0 form
   [pmp_tor0_grants] (+ the [pmpaddr_n] register cell): after xv6's boot-time
   pmpcfg0 write, entry 0 is TOR-unlocked-RWX (0x0f) with pmpaddr0 covering all
   of RAM, so an 8-byte access FULLY inside [0, pmpaddr0*4) full-matches entry 0
   and the M-mode pmpCheck walk EARLY-RETURNS allow at entry 0 -- no all-OFF
   assumption, and the remaining entries are never examined.

   Layers (mirroring the all-OFF development, which is left untouched):
     1. [exec_pmpCheck_machine_tor0]  -- the pmpCheck reduction (the full-match
        twin of RiscvTryStep's [exec_pmpCheck_machine_unlocked], which only
        covers grain-cell (<=4 byte) accesses).  Placed here rather than in
        RiscvTryStep.v to avoid rebuilding the whole tree; it reuses that
        file's loop/match machinery.
     2. [_chk] clones of the 8-byte read/write exec chains of WpLoad.v /
        WpGprLoad.v / WpGprStore.v, with the per-entry all-OFF hypothesis
        replaced by the abstract pmpCheck fact.
     3. [wp_store_gpr_tor] / [wp_ld_gpr_tor] (is_rvc-generic base) engines + the
        [wp_csdsp_gpr_tor] / [wp_cldsp_gpr_tor] wrappers. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr WpGprAddi WpGprLui WpGprShift WpGprLogic WpGprLoad WpGprJalr WpGprStore WpGprRvc.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. The TOR-entry-0 pmpCheck reduction.                                 *)
(* ===================================================================== *)

(* [pmpReadAddrReg] at PMP grain 0 is a pure read of pmpaddr_n[n] (both
   grain-masking branches are dead). *)
Lemma exec_pmpReadAddrReg (n : Z) s :
  exec (pmpReadAddrReg n) s
  = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn [andb]. apply exec_returnM.
Qed.

(* pmpRangeMatch full-match arm: an access fully inside [b, e) matches. *)
Lemma pmpRangeMatch_full (b e a w : Z) :
  b <= a -> 0 < w -> a + w <= e ->
  pmpRangeMatch b e a w = PMP_Match.
Proof.
  intros Hb Hw He. unfold pmpRangeMatch.
  replace (Z.leb (Z.add a w) b) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb e a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb].
  replace (Z.leb b a) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Z.add a w) e) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(* pmpMatchAddr, entry-0 TOR shape (prev = zeros): the access [a, a+w) fully
   inside [0, uint paddr * 4) is a (full) PMP_Match, with no state change. *)
Lemma exec_pmpMatchAddr_tor0_match (a : mword 64) (wbv : mword 64) (ent : mword 8)
    (paddr : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  0 < uint wbv ->
  uint a + uint wbv <= uint paddr * 4 ->
  exec (pmpMatchAddr (Physaddr a) wbv ent paddr (zeros' 64)) s = Some (PMP_Match, s).
Proof.
  intros HA Hw Hin.
  pose proof (bv_unsigned_in_range _ a) as [Ha0 _].
  rewrite <- uint_unsigned in Ha0.
  assert (Hp0 : 0 < uint paddr) by lia.
  unfold pmpMatchAddr. cbn zeta. rewrite HA.
  assert (Hz0 : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  replace (zopz0zKzJ_u (zeros' 64) paddr) with false.
  2:{ symmetry. unfold zopz0zKzJ_u. rewrite Hz0. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
  rewrite Hz0.
  rewrite (pmpRangeMatch_full (Z.mul 0 4) (Z.mul (uint paddr) 4) (uint a) (uint wbv)
             ltac:(lia) Hw ltac:(lia)).
  apply exec_returnM.
Qed.

(* The pure predicate: PMP entry 0 is TOR + unlocked and the [width]-byte
   access at [ea] lies FULLY inside its region [0, pmpaddr0*4).  (Nothing is
   assumed of entries 1..: in M-mode the full match on the unlocked entry 0
   early-returns "allow" before any later entry is consulted.) *)
Definition pmp_tor0_grants (cfg : type_of_register pmpcfg_n)
    (pmpaddrs : type_of_register pmpaddr_n) (ea : mword 64) (width : Z) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg 0)) = TOR
  /\ pmpLocked (vec_access_dec cfg 0) = false
  /\ 0 < width
  /\ uint ea + width <= uint (vec_access_dec pmpaddrs 0) * 4.

(* THE reduction: in Machine mode, [pmp_tor0_grants] of the CURRENT pmpcfg_n /
   pmpaddr_n register values makes pmpCheck grant the access -- the loop's
   FIRST iteration full-matches entry 0, which (M-mode, unlocked) early-returns
   [None] (allow). *)
Lemma exec_pmpCheck_machine_tor0
    (addr : mword 64) (width : Z) (access : MemoryAccessType mem_payload) s :
  pmp_tor0_grants (register_lookup pmpcfg_n s.(sregs))
                  (register_lookup pmpaddr_n s.(sregs)) addr width ->
  (forall ent, exists b, exec (pmpCheckRWX ent access) s = Some (b, s)) ->
  uint (to_bits 64 width : mword 64) = width ->
  exec (pmpCheck (Physaddr addr) width access Machine) s = Some (None, s).
Proof.
  intros (HA & HL & Hw & Hin) Hrwx Hwidth.
  unfold pmpCheck.
  rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_bind0.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hbody0 : execR (body 0 tt) s
                       = Some (inl (None : option ExceptionType), s))
  end.
  { assert (HW1 : 0 < uint (to_bits 64 width : mword 64))
      by (rewrite Hwidth; exact Hw).
    assert (HW2 : uint addr + uint (to_bits 64 width : mword 64)
                  <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)
      by (rewrite Hwidth; exact Hin).
    cbn beta.
    change (Z.gtb 0 0) with false. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_tor0_match addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) s
                  HA HW1 HW2)).
    cbn beta. cbn match.
    rewrite execR_bind. unfold or_boolM. rewrite execR_bind. rewrite execR_liftR.
    destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) as [b Hb].
    rewrite Hb. cbn match.
    destruct b; [reflexivity | rewrite HL; reflexivity]. }
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inl (None : option ExceptionType), s))
  end.
  { unfold Defs.foreach_ZM_up.
    assert (Hle : 0 <= sys_pmp_count - 1) by (unfold sys_pmp_count; lia).
    rewrite (Defs.unroll_foreach_ZM_up' _ _ 0 (sys_pmp_count - 1) 1 _ tt _ Hle).
    rewrite execR_bind. rewrite Hbody0. reflexivity. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

Print Assumptions exec_pmpCheck_machine_tor0.

(* ===================================================================== *)
(* 2a. STORE chain [_chk] clones (WpGprStore.v), with the per-entry        *)
(* all-OFF hypothesis replaced by the abstract pmpCheck fact.  Everything  *)
(* else (PMA / mmio gates / write_ram leaf / translation) is reused.       *)
(* ===================================================================== *)

Lemma exec_checked_mem_write_ram_store_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Machine tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data)).
Proof.
  intros Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmpchk).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_8_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data)).
Proof.
  intros Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_chk pbmt addr region data s Hpmpchk Hmatch Halign Hwrite Hc Hsig Hh)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section SWchk.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_vmem_write_addr_8_chk :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_store (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      (* SC dummy assert (Bool.eqb false (is_store_conditional (Store Data)) = true) *)
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8_chk PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s.(sregs)) s Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh eq_refl Hmprv Hpriv)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SWchk.

(* register-generic 8-byte vmem_write, pmpCheck-abstract. *)
Section VWgchk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_vmem_write_8_gpr_chk :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8_chk a8 data region s Halign Hcp Hmprv Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh).
  reflexivity.
Qed.
End VWgchk.

(* register-generic 8-byte STORE execute, pmpCheck-abstract. *)
Section ExecStoreGchk.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).

Lemma exec_execute_STORE_8_gpr_chk :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr_chk rs1 offset _ region s Hcp Hmprv Hpmm Halign Hpmpchk Hmatch Hpalign Hwrite Hc Hsig Hh)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGchk.

(* ===================================================================== *)
(* 2b. LOAD chain [_chk] clones (WpLoad.v / WpGprLoad.v).                  *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_ram_load_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmpchk Hmatch Halign Hread Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmpchk).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_load_chk (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmpchk Hmatch Halign Hread Hc Hsig Hh Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load_chk with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section Schk.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

Lemma exec_vmem_read_addr_8_chk :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s).
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR mrm s = Some (inr data2, s))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load_chk PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End Schk.

Section VRgchk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_chk :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8_chk a8 v region s Halign Hcp Hmprv Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hbytes).
  reflexivity.
Qed.
End VRgchk.

Section ExecLoadGchk.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmpchk : exec (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_chk :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_chk rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmpchk Hmatch Hpalign Hread Hc Hsig Hh Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGchk.


(* ===================================================================== *)
(* 3. TOR-aware RVC 8-byte LOAD / STORE WP engines + the c.ldsp/c.sdsp    *)
(* wrappers.  Clones of WpGprRvc's [wp_rvc_ld_gpr]/[wp_rvc_store_gpr]:    *)
(*   - fetch side: [pmp_allows_all pmpcfg0] (as everywhere else);          *)
(*   - data side : [pmp_tor0_grants pmpcfg0 pmpaddrs ea 8] + the           *)
(*     [pmpaddr_n] register cell (read-only, handed back), discharged via  *)
(*     [exec_pmpCheck_machine_tor0] and the [_chk] chains above.           *)
(* ===================================================================== *)
Section RvcTorEngines.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma wp_ld_gpr_tor E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rd : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Htor Hrd Halign.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr E Φ pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpaddr")    as %Lpaddr.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpaddrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddrs)
      by (unfold s_pc; tmig; exact Lpaddr).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    (* THE pmpCheck fact at the ticked state, from the TOR-entry-0 predicate. *)
    assert (Hpmpchk_ea : exec (pmpCheck (Physaddr ea) 8 (Load Data) Machine) s_pc
                         = Some (None, s_pc)).
    { apply (exec_pmpCheck_machine_tor0 ea 8 (Load Data) s_pc).
      - rewrite Lpmpcp Lpaddrp. exact Htor.
      - intros ent. eexists. apply exec_returnM.
      - vm_compute; reflexivity. }
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr_chk rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - rewrite Hpa. exact Hpmpchk_ea.
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_store_gpr_tor E (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs1 rs2 : mword 5)
      (imm : mword 12) (m : gmap regidx (mword 64)) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte vold j) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
      gpr_file m -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte (m !!! Regidx rs2) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Htor Halign.
    iIntros "Hmm Hpmpc Hpaddr [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & _ & Hwrite).
    iApply (wp_instr E Φ pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 8)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpaddr")    as %Lpaddr.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lrs2v.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1)
      by exact Lrs1v.
    assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
                    = m !!! Regidx rs2)
      by exact Lrs2v.
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpaddrp : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddrs)
      by (unfold s_pc; tmig; exact Lpaddr).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false ea 8 s_pc Lhtifp) as Hwh.
    assert (Hpmpchk_ea : exec (pmpCheck (Physaddr ea) 8 (Store Data) Machine) s_pc
                         = Some (None, s_pc)).
    { apply (exec_pmpCheck_machine_tor0 ea 8 (Store Data) s_pc).
      - rewrite Lpmpcp Lpaddrp. exact Htor.
      - intros ent. eexists. apply exec_returnM.
      - vm_compute; reflexivity. }
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) ea 8 (m !!! Regidx rs2))).
    assert (Hexec_spc :
      exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr_chk rs2 rs1 imm region s_pc Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hseccfg1)
                ltac:(rewrite Ha8; unfold is_aligned_vaddr; unfold is_aligned_paddr in Halign; exact Halign)
                ltac:(rewrite Hpa; exact Hpmpchk_ea)
                ltac:(rewrite Lpmap Hpa; exact Hmatch) ltac:(rewrite Hpa; exact Halign)
                Hwrite ltac:(rewrite Hpa; apply Hwc) ltac:(rewrite Hpa; apply Hws)
                ltac:(rewrite Hpa; apply Hwh)).
      subst s_x. rewrite Hpa Hdata. reflexivity. }
    iMod (upd_window_8 σ.(mem) ea (m !!! Regidx rs2) vold
            with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
    { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' Hpaddr [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. exact Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- c.ldsp rd, uimm(sp), TOR-aware ---- *)
  Lemma wp_cldsp_gpr_tor E (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rd : mword 5) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (LOAD (imm, Regidx csp_rs1, Regidx rd, false, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN Hpmp Htor Hrd Halign.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_ld_gpr_tor E Φ pc true csp_rs1 rd imm m v
              pmpcfg0 pmpaddrs q HN Hpmp Htor Hrd Halign
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

  (* ---- c.sdsp rs2, uimm(sp), TOR-aware ---- *)
  Lemma wp_csdsp_gpr_tor E (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rs2 : mword 5) (m : gmap regidx (mword 64)) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (q : Qp) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    pmp_tor0_grants pmpcfg0 pmpaddrs ea 8 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx csp_rs1, 8)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte vold j) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte (m !!! Regidx rs2) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN Hpmp Htor Halign.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont".
    iApply (wp_store_gpr_tor E Φ pc true csp_rs1 rs2 imm m vold
              pmpcfg0 pmpaddrs q HN Hpmp Htor Halign
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hinstr Hbytes Hcont").
  Qed.

End RvcTorEngines.

(* ===================================================================== *)
(* Sanity: the register-dependent conjuncts of [pmp_tor0_grants] hold of  *)
(* the ACTUAL post-write xv6 boot config (entry 0 written 0x0f = TOR +    *)
(* R|W|X, unlocked); the range conjunct is per-address arithmetic the     *)
(* caller supplies (xv6's pmpaddr0 = 0x3fffffffffffff covers all of RAM). *)
(* ===================================================================== *)
Require Import WpGprCsrwC.

Example pmp_tor0_entry0_xv6 :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (pmpcfg_written (mword_of_int 15) pmpcfg_zero) 0)) = TOR
  /\ pmpLocked (vec_access_dec (pmpcfg_written (mword_of_int 15) pmpcfg_zero) 0) = false.
Proof. split; vm_compute; reflexivity. Qed.

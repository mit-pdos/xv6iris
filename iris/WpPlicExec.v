(* WpPlicExec.v -- the width-4 PLIC device-store exec-layer lemmas.

   A mechanical width-1 -> width-4 clone of the UART device-store stack
   (WpUart.v / WpSmodeUart.v / WpSmodePtUart.v), with the RAM leaf swapped
   for the device leaf (the model's [dev_write d pa 4 v] routes width-4
   stores to [plic_write]).  Also the PLIC geometry facts mirroring the
   UART analogs.  All lemmas here are pure exec-level (iris-free). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import InstrBytes.
Require Import KptPt SmodeCore.
Require Import WpLoad WpGpr.
Require Import WpMmodeLeafBase WpSmodeGpr.
Require Import WpUart WpSmodeUart.
Require Import SmodeCorePt SRegime.
Require Import RegFile.
Require Import MemAccessGen.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* (A)  width-4 device write_ram + pmaCheck leaves.                        *)
(* ===================================================================== *)

(* write_ram at a device address (width 4): the MemWrite outcome is
   DELIVERED to the device as one transaction; the byte memory is
   untouched. *)
Lemma exec_write_dev_4 (pa : Arch.pa) (data : bv 32) (d' : dev_state) s :
  dev_addr pa = true ->
  dev_write s.(mdev) pa 4 data = Some d' ->
  exec (write_ram rv64d_types.Write_plain (Physaddr pa) 4 data tt) s
    = Some (true, MState s.(sregs) s.(mem) d').
Proof.
  intros Hdev Hwr.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemWrite_dev; last exact Hdev.
  cbn [Interface.WriteReq.pa Interface.WriteReq.value].
  rewrite Hwr.
  reflexivity.
Qed.

(* pmaCheck for a 4-byte Store Data in a writable device PMA region.  The
   width-1 twin used the trivial [is_aligned_paddr_1]; at width 4 we thread
   the alignment hypothesis explicitly. *)
Lemma exec_pmaCheck_dev_store_4 (pa : Arch.pa) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  is_aligned_paddr (Physaddr pa) 4 = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr pa) 4 (Store Data) pbmt false) s = Some (None, s).
Proof.
  intros Halign Hmatch Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* (B)  width-4 S-mode device checked_mem_write + mem_write_value leaves.  *)
(*      = WpSmodeUart's width-1 dev leaves at width 4 (TOR grant width 4,   *)
(*      is_aligned_paddr threaded, exec_pmaCheck_dev_store_4/               *)
(*      exec_write_dev_4).                                                  *)
(* ===================================================================== *)

Lemma exec_checked_mem_write_dev_4_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (data : bv 32) (d' : dev_state) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr pa) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_write s.(mdev) pa 4 data = Some d' ->
  exec (checked_mem_write (Physaddr pa) 4 data (Store Data) pbmt Supervisor tt false false false)
       s = Some (Ok true, MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hwr.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store pa 4 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_dev_store_4 pa pbmt region s Halign Hmatch Hwrite)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr pa) 4) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags _ _ _) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_dev_4 pa data d' s Hdev Hwr)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_dev_4_S (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (data : bv 32) (d' : dev_state) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr pa) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_write s.(mdev) pa 4 data = Some d' ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_write_value (Physaddr pa) 4 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) s.(mem) d').
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hwr Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_dev_4_S pbmt pa region data d' s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hwr)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* (C)  post-state-generic aligned store.                                  *)
(*      = MemAccessGen.exec_vmem_write_addr_aligned_store with the concrete *)
(*      RAM post-state replaced by an abstract [sfin]; same proof.         *)
(* ===================================================================== *)

Lemma exec_vmem_write_addr_aligned_store_gen (width : Z) (va pa : mword 64)
    (dat : mword (8*width)) (s s' sfin : mstate) :
  let wv := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*width-1) (8*0*width))
            : mword (8 * width) in
  is_aligned_vaddr (Virtaddr va) width = true ->
  exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr va)) (0 * width))) (Store Data)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s') ->
  exec (mem_write_ea (Physaddr pa) width false false false) s' = Some (Ok tt, s') ->
  exec (mem_write_value (Physaddr pa) width wv (Store Data) PBMT_PMA false false false) s'
    = Some (Ok true, sfin) ->
  exec (vmem_write_addr (Virtaddr va) width dat (Store Data) false false false) s
    = Some (Ok true, sfin).
Proof.
  intros wv Halign Htr Hea Hwv.
  set (sw := sfin).
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr va) width)) s = Some (inr (1, width), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_g width (Virtaddr va) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (true, 0%Z, true), sw))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data)))
                            "sys/vmem_utils.sail:197.50-197.51") s' = Some (tt, s')) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data)))
                              "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s'
                     = Some (inr tt, s'))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s' = Some (inr true, sw))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        rewrite (execR_liftR_seq _ _ _ _ _ Hea).
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
        cbn match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.

(* ===================================================================== *)
(* (D)  device width-4 STORE towers (S-mode-walk-pt).  Clones of           *)
(*      WpSmodeMemGen's RAM store tower at concrete width 4, device leaf.   *)
(* ===================================================================== *)

(* ---- vmem_write_addr reduction ---- *)
Section SWS4walkDevPt.
Variable a : mword 64.
Variable dat : mword (8*4).
Variable d' : dev_state.
Variable region : PMA_Region.
Variable s s' : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
Let wv : mword (8*4) := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*4-1) (8*0*4)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hwr : dev_write s'.(mdev) pa 4 wv = Some d'.

Lemma exec_vmem_write_addr_4_S_walk_dev_pt :
  exec (vmem_write_addr (Virtaddr a) 4 dat (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) s'.(mem) d').
Proof.
  apply (exec_vmem_write_addr_aligned_store_gen 4 a pa dat s s'
           (MState s'.(sregs) s'.(mem) d') Halign Htr
           (exec_mem_write_ea_g 4 pa s')
           (exec_mem_write_value_dev_4_S PBMT_PMA pa region wv d'
              (register_lookup mstatus s'.(sregs)) s'
              HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev Hwr eq_refl Hmprv Hcp)).
Qed.
End SWS4walkDevPt.

(* ---- vmem_write (gpr) reduction ---- *)
Section VWgS4walkDevPt.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable dat : mword (8*4).
Variable d' : dev_state.
Variable region : PMA_Region.
Variable s s' : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
Let wv : mword (8*4) := autocast (T := mword) (subrange_vec_dec dat (8*(0+1)*4-1) (8*0*4)).
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hwr : dev_write s'.(mdev) pa 4 wv = Some d'.

Lemma exec_vmem_write_4_gpr_S_walk_dev_pt :
  exec (vmem_write (Regidx rs1) offset 4 dat (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) s'.(mem) d').
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Ha8ea : a8 = ea) by (unfold a8; rewrite subrange_id; apply sign_extend'_id).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ Htea).
    rewrite Ha8ea. apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_4_S_walk_dev_pt a8 dat d' region s s' Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev Hwr).
  reflexivity.
Qed.
End VWgS4walkDevPt.

(* ---- execute STORE retire ---- *)
Section ExecStoreGS4walkDevPt.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s s' : mstate.
Variable d' : dev_state.
Let offset := sign_extend' 64 imm.
Let vrs2 : mword (8*4) := autocast (T := mword)
  (subrange_vec_dec (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs))
     (4*8-1) 0).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 4)).
Let wv : mword (8*4) := autocast (T := mword) (subrange_vec_dec vrs2 (8*(0+1)*4-1) (8*0*4)).
Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s
                  = Some (Virtaddr ea, s).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 4))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = true.
Hypothesis Hwr : dev_write s'.(mdev) pa 4 wv = Some d'.

Lemma exec_execute_STORE_4_gpr_S_walk_dev :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
    = Some (RETIRE_SUCCESS, MState s'.(sregs) s'.(mem) d').
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
  unfold execute_STORE.
  replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_4_gpr_S_walk_dev_pt rs1 offset vrs2 d' region s s' Htea Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev Hwr)).
  cbn match. rewrite (exec_returnM _ _). reflexivity.
Qed.
End ExecStoreGS4walkDevPt.

(* ===================================================================== *)
(* (E)  PLIC geometry lemmas (mirror the UART analogs).                    *)
(* ===================================================================== *)

(* A PLIC address is a device address (below the DRAM bank). *)
Lemma dev_addr_plic (pa : mword 64) :
  plic_base <= uint pa < plic_base + plic_size -> dev_addr pa = true.
Proof.
  intros Hrange. unfold dev_addr. apply Z.ltb_lt.
  unfold plic_base, plic_size, dev_bound in *. lia.
Qed.

(* a width-4 PLIC MMIO write, at the fabric level, routes to plic_write *)
Lemma dev_write_plic (d : dev_state) (pa : mword 64) (v : bv 32) (p' : plic_state) :
  plic_base <= uint pa < plic_base + plic_size ->
  plic_write (dplic d) (uint pa - plic_base) v = Some p' ->
  dev_write d pa 4 v = Some (set_dplic d p').
Proof.
  intros Hrange Hwr. unfold dev_write.
  assert (Hnu : in_uart (uint pa) = false).
  { unfold in_uart. apply andb_false_intro1. apply Z.leb_gt.
    unfold uart_base, plic_base, plic_size in *. lia. }
  rewrite Hnu.
  assert (Hin : in_plic (uint pa) = true).
  { unfold in_plic. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  rewrite Hin.
  rewrite Hwr. reflexivity.
Qed.

(* a 4-byte PLIC access matches the kernel's TOR entry 0 (the PLIC window
   [0x0c000000,0x10000000) sits well inside [0, pmpaddr0*4)) *)
Lemma plic_pmp_match4 (pmpaddr0 : mword 64) (pa : mword 64) :
  plic_base <= uint pa < plic_base + plic_size ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
Proof.
  intros Hrange Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  assert (Hw4 : uint (to_bits 64 4 : mword 64) = 4) by (vm_compute; reflexivity).
  rewrite Hz Hw4. rewrite Z.mul_0_l.
  apply pmpRangeMatch_full; unfold ram_base, ram_size, plic_base, plic_size in *; lia.
Qed.

(* a PLIC address sits above the CLINT window, so it is [not_in_clint] and
   the model's within_clint check reduces to false *)
Lemma plic_pa_not_in_clint (pa : mword 64) :
  plic_base <= uint pa < plic_base + plic_size -> not_in_clint pa.
Proof.
  intros Hrange. right.
  assert (uint plat_clint_base + uint plat_clint_size = 34340864) as ->
    by (vm_compute; reflexivity).
  unfold plic_base, plic_size in *. lia.
Qed.

Lemma within_clint_plic (pa : mword 64) (w : Z) s :
  plic_base <= uint pa < plic_base + plic_size -> 0 < w ->
  exec (within_clint (Physaddr pa) w) s = Some (false, s).
Proof.
  intros Hrange Hw. apply within_clint_false; [apply plic_pa_not_in_clint; exact Hrange | exact Hw].
Qed.

(* the SIG test device is disabled (plat_have_sig = false) -- it would
   otherwise overlap the real PLIC window -- so within_sig is false for a
   PLIC address regardless of its offset (no not_in_sig fact is available,
   nor needed). *)
Lemma within_sig_plic (pa : mword 64) (w : Z) s :
  exec (within_sig (Physaddr pa) w) s = Some (false, s).
Proof.
  unfold within_sig, plat_have_sig, __id. cbn [Riscv.rv64d.not negb].
  apply exec_returnm.
Qed.

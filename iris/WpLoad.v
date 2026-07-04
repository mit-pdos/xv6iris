(* WpLoad.v -- the LOAD opcode: 8-byte data-memory reductions (vmem_read via the
   untilMT loop), exec_execute_LOAD_8, forward_exec_ld, wp_step_ld. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Lemma rX_x2 : rX (Regno 2) = Defs.read_reg (R_bitvector_64 x2).
Proof. reflexivity. Qed.

Lemma run_rX_x2 s :
  run (rX (Regno 2)) s (register_lookup (R_bitvector_64 x2) s.(sregs)) s.
Proof. rewrite rX_x2. split; reflexivity. Qed.

Lemma exec_rX_x2 s :
  exec (rX (Regno 2)) s = Some (register_lookup (R_bitvector_64 x2) s.(sregs), s).
Proof. reflexivity. Qed.

Lemma exec_rX_bits_x2 (i : mword 5) s :
  uint i = 2 ->
  exec (rX_bits (Regidx i)) s = Some (register_lookup (R_bitvector_64 x2) s.(sregs), s).
Proof. intro H. unfold rX_bits; cbn match. rewrite H. apply exec_rX_x2. Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 3: ext_data_get_addr base offset acc w = read base, return OK vaddr *)
(* ---------------------------------------------------------------------- *)
Lemma exec_ext_data_get_addr_x2 (i : mword 5) (offset : mword 64) acc w s :
  uint i = 2 ->
  exec (ext_data_get_addr (Regidx i) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset)), s).
Proof.
  intro H. unfold ext_data_get_addr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x2 i s H)).
  apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 4: effectivePrivilege (Load Data) m Machine = Machine, given MPRV=0 *)
(* (a boot-config condition, analogous to the MIE/elp conditions).          *)
(* ---------------------------------------------------------------------- *)
Lemma exec_effectivePrivilege_load (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Load Data) m Machine) s = Some (Machine, s).
Proof.
  intro H. unfold effectivePrivilege.
  cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* Leaf 5: split_misaligned vaddr 8 = (1,8) for an 8-aligned vaddr;         *)
(* misaligned_order 1 = (0,0,step).                                         *)
(* ---------------------------------------------------------------------- *)
Lemma exec_split_misaligned_aligned (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 8 = true ->
  exec (split_misaligned vaddr 8) s = Some ((1, 8), s).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
Qed.

Lemma misaligned_order_1 : misaligned_order 1 = (0, 0, if sys_misaligned_order_decreasing then -1 else 1).
Proof. unfold misaligned_order. destruct sys_misaligned_order_decreasing; reflexivity. Qed.

(* ====================================================================== *)
(* 8-byte data-load memory path -- doubleword analogues of the 4-byte      *)
(* fetch lemmas in RiscvAddTryStep.v (read_ram/pmaCheck/checked/mem_read). *)
(* Differences: width 8, access = Load Data, PMA_readable (not executable).*)
(* ====================================================================== *)

(* read_ram: pin the 8-byte value from the owned bytes (mirror _4_pin). *)
Lemma run_read_ram_plain_8_pin (addr : mword 64) (w : bv 64) s :
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 8 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_8 (addr : mword 64) (w : bv 64) s :
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 8 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_8_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 8) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* pmaCheck for Load Data: returns None when the region is readable+aligned. *)
Lemma exec_pmaCheck_ram_load (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Load Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  (* Load Data arm: assert_exp' true >>= fun _ => returnM PMA_readable  ≡  returnM PMA_readable *)
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

(* checked_mem_read for Load Data, width 8. *)
Lemma exec_checked_mem_read_ram_load (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
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
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hbytes)).
  apply exec_returnM.
Qed.

(* mem_read for Load Data in Machine mode, width 8 (needs MPRV=0). *)
Lemma exec_mem_read_load (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
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
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hbytes Hms Hmprv Hpriv.
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
      2:{ cbn match. apply exec_checked_mem_read_ram_load with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ====================================================================== *)
(* translateAddr (Load Data) = identity in Machine mode (MPRV off).        *)
(* Mirrors exec_translateAddr_identity (fetch).                            *)
(* ====================================================================== *)
Lemma exec_is_shadow_stack_load s :
  exec (is_shadow_stack_access (Load Data)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

Lemma exec_translateAddr_identity_load (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec (translateAddr (Virtaddr a) (Load Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load _ s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_load s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind.
  cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(* untilMT one-iteration: measure 1, body reaches a state where cond=true. *)
(* The loop's Acc (Zwf 0) recursion is unfolded by destructing Zwf_guarded *)
(* (same technique as currentlyEnabled), so it is axiom-free.              *)
(* ====================================================================== *)
Lemma execR_untilMT_1 {R Vars} (vars vars' : Vars) (measure : Vars -> Z)
   (cond : Vars -> Defs.monadR R exception bool) (body : Vars -> Defs.monadR R exception Vars) s s' :
  measure vars = 1 ->
  execR (body vars) s = Some (inr vars', s') ->
  execR (cond vars') s' = Some (inr true, s') ->
  execR (Defs.untilMT vars measure cond body) s = Some (inr vars', s').
Proof.
  intros Hm Hb Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge]; [| exfalso; rewrite Hm in Hge; lia ].
  rewrite (execR_bind_Some _ _ _ _ _ Hb).
  rewrite (execR_bind_Some _ _ _ _ _ Hc).
  cbn match.
  apply execR_returnR_fwd.
Qed.

Section S.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

Lemma exec_vmem_read_addr_8 :
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
    - (* measure *) reflexivity.
    - (* body *)
      cbn match.
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
          (exec_mem_read_load PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - (* cond *) apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End S.

Lemma exec_is_pmm_applicable_load s :
  exec (is_pmm_applicable (Load Data) Machine) s = Some (true, s).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity). reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_load s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Load Data) Machine) s = Some (0, s).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_load s)).
  cbn match.
  assert (Hgp : exec (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_load (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Load Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_load s Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

Section VR.
Variable i : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hi : uint i = 2.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8 :
  exec (vmem_read (Regidx i) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx i) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_x2 i offset (Load Data) 8 s Hi)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8 a8 v region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes).
  reflexivity.
Qed.
End VR.

(* ---- exec_execute_LOAD_8 + forward_exec_ld (moved from KernelBoot) ---- *)
Section ExecLoad.
Variable i : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hi : uint i = 2.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8 :
  exec (execute (LOAD (imm, Regidx i, Regidx i, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 x2) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx i, Regidx i, false, 8)))
    with (execute_LOAD imm (Regidx i) (Regidx i) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8 i offset v region s Hi Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s (extend_value false data2) Hi)).
  apply exec_returnM.
Qed.
End ExecLoad.

Section ForwardLD.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 12)
          (irs1 ird : mword 5) (data : mword 64) (b : bool).

  Hypothesis Hi : uint ird = 2.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0
      = Some (LOAD (imm, Regidx irs1, Regidx ird, false, 8), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  (* The execute clause at the post-fetch state s_pc = set_reg (set_reg s
     minstret_increment b) nextPC (pc+4).  Discharged in wp_kernel_first_two
     via the PROVEN exec_execute_LOAD_8 (no longer the over-strong forall-s0). *)
  Hypothesis Hexec_spc :
    exec (execute (LOAD (imm, Regidx irs1, Regidx ird, false, 8)))
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                    (R_bitvector_64 x2) (regval_into_reg (extend_value false data))).

  Definition sAl : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXl : mstate :=
    set_reg (set_reg sAl nextPC (add_vec_int pc 4)) (R_bitvector_64 x2)
            (regval_into_reg (extend_value false data)).
  Definition sTl : mstate := set_reg sXl PC (register_lookup nextPC sXl.(sregs)).
  Definition sFl : mstate :=
    if b then set_reg sTl minstret
                  (add_vec_int (register_lookup minstret sTl.(sregs)) 1)
         else sTl.

  Lemma forward_exec_ld :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFl).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl. trans_mi. exact Lpc. }
    assert (LprivA: register_lookup cur_privilege sAl.(sregs) = Machine).
    { unfold sAl. trans_mi. exact Lpriv. }
    assert (LhsA  : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl. trans_mi. exact Lhs. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAl.(sregs) = zeros' 64).
    { unfold sAl. trans_mi. exact Lmideleg. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl. trans_mi. exact LS. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAl.(sregs))) ('b"1") = false).
    { unfold sAl. trans_mi. exact LmIE. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl. trans_mi. exact Lelp. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAl = Some (None, sAl)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAl _ (exec_currentlyEnabled_S sAl) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAl = Some (F_Base w, sAl))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAl
              = Some (LOAD (imm, Regidx irs1, Regidx ird, false, 8), sAl))
      by (apply Hdec_gen; exact LprivA).
    pose (s_pc := set_reg sAl nextPC (add_vec_int pc 4)).
    assert (LpcAA : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc. trans_mi. exact LpcA. }
    assert (HexecA : exec (execute (LOAD (imm, Regidx irs1, Regidx ird, false, 8))) s_pc
              = Some (RETIRE_SUCCESS, sXl)).
    { unfold sXl, s_pc, sAl. exact Hexec_spc. }
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXl)).
    { exact (exec_hart_active_progress sAl sAl sXl sAl w
               (LOAD (imm, Regidx irs1, Regidx ird, false, 8)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    apply (exec_riscv_step_ADD s sXl w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXl, sAl; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  (* clean-form post-state for the ld step (x2 value already concrete). *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_l : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_l : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (extend_value false data)))
            PC (add_vec_int pc 4).
  Definition sFcl : mstate :=
    if b then set_reg base_upd_l minstret (add_vec_int mst0 1)
         else base_upd_l.

  Ltac tmissl := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sFl_eq : sFl = sFcl.
  Proof.
    assert (Enpc : register_lookup nextPC sXl.(sregs) = add_vec_int pc 4).
    { unfold sXl; unfold set_reg; cbn [sregs]. tmissl.
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTl = base_upd_l).
    { unfold sTl. rewrite Enpc. unfold sXl, sAl, base_upd_l. reflexivity. }
    unfold sFl, sFcl. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_l.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_l, set_reg; cbn [sregs]. tmissl. tmissl. tmissl. tmissl. reflexivity. }
    rewrite Emst Lmst_l. reflexivity.
  Qed.

End ForwardLD.

Section StepLD.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Lemma wp_step_ld (pc : mword 64) (w_l : mword 32) (imm_l : mword 12)
      (i_l : mword 5) (b1 : bool) (v : bv 64)
      (sp0a npc0a mstatus0a misa0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (elp0a : mword 1)
      E {dq : dfrac} (Φ : mval -> iProp Σ) :
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec sp0a offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    ↑minstretN ⊆ E ->
    uint i_l = 2 ->
    (* the pure fetch + load side-conditions; PMA covers all of memory *)
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w_l 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w_l) s0 = Some (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8), s0)) ->
    (* should_inc determined by the mcountinhibit/minstretcfg cells: *)
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MPRV mstatus0a) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    (* the 8-byte DATA access needs the stronger all-OFF form: an 8-byte
       window can partially overlap a TOR/NA4 boundary (partial match faults
       even in M-mode), so unlocked-ness alone does not suffice. *)
    pmp_all_off pmpcfg0 ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    (* within_clint/within_sig are now discharged from the RAM-constrained bytes,
       and within_htif from the owned [htif_tohost_base |-> None] below. *)
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x2) ↦ᵣ sp0a -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_l j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ reg_pointsto mseccfg dqc mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗
        reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_l j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea a8 pa data2 HN Hil Hpmaall Hpmpf Hvalignf HnotRVCf
      Hdl Hb1 HmIE Help HmisaS HMPRV Hpmm Halign Hpmp Hpalign.
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    destruct (Hpmaall pa 8) as (region & Hmatch & _ & Hread & _).
    iIntros "#Hinv Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes Hcont".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hx2")    as %Lx2.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hhtif")  as %Lhtif.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    (* derive the state-specific fetch fact from the owned instruction bytes *)
    iDestruct (fetch_from_pts_minstret pc w_l region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj).
      assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    (* the access base [pa] is real RAM: read it off the j=0 byte. *)
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int pc 4)).
    assert (Lx2p : register_lookup (R_bitvector_64 x2) s_pc.(sregs) = sp0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lx2. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine).
    { unfold s_pc; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = mstatus0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc; trans_mi; trans_mi; exact Lhtif. }
    (* discharge the MMIO-range checks: clint/sig from [pa] being RAM, htif
       from [htif_tohost_base = None]. *)
    pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_pc Lhtifp) as Hwh.
    assert (Hexec_spc :
      exec (execute (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 x2) (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8 i_l imm_l v region s_pc Hil Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hpmm.
      - rewrite Lx2p. exact Halign.
      - intro j. rewrite Lpmpcp. exact (proj1 (Hpmp j)).
      - rewrite Lpmap Lx2p. exact Hmatch.
      - rewrite Lx2p. exact Hpalign.
      - exact Hread.
      - rewrite Lx2p. apply Hwc.
      - rewrite Lx2p. apply Hws.
      - rewrite Lx2p. apply Hwh.
      - intros j Hj. rewrite Lx2p. exact (Hbytesf j Hj). }
    (* discharge the [∅ ⊆ E] mask goal with [apply empty_subseteq], NOT [set_solver]:
       [set_solver] runs [set_unfold] over the whole context, and [Hexec_spc]'s type
       embeds the dependent-width [update_subrange_vec_dec]/[extend_value] term, whose
       normalization costs ~23 min. [empty_subseteq] never touches the context. *)
    iModIntro.
    iExists (sFcl s pc data2 b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s w_l pc imm_l i_l i_l data2 b1 Hfetch_at Hsi_s Hexec_spc (register_lookup minstret s.(sregs)) eq_refl).
      apply (forward_exec_ld s w_l pc imm_l i_l i_l data2 b1 Hil Hfetch_at Hdl Hsi_s Hexec_spc Lpc Lpriv Lhs Lmdl).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x2) _ (regval_into_reg (extend_value false data2))
            with "Hreg Hx2") as "[Hreg Hx2]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFcl, base_upd_l. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytes").
  Qed.

End StepLD.

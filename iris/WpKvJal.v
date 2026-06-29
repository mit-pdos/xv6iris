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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpGprJal WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvJal.v — non-RVC (F_Base) superpage-hit fetch, for kernelvec's 4-byte
   jal kerneltrap @0x80005404 and sret @0x8000542c (both in code page 0x80005,
   TLB hit). Same as WpKvStore.FetchAt4 but the instruction is NOT compressed
   (isRVC (w[15:0]) = false), so the fetch yields F_Base w. *)

(* JAL to a 2-byte-aligned (bit1=1) target with the C extension enabled: the
   misalignment check (bit1 && not Zca) is false, so the jump succeeds. *)
Lemma exec_jump_to_zca (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hzca.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      destruct (bit_to_bool (access_vec_dec target 1)).
      - cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
        cbv iota beta. apply execR_returnR_fwd.
      - cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

Lemma exec_execute_JAL_zca (imm : mword 21) (rd : regidx) s s_w :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (wX_bits rd (register_lookup nextPC s.(sregs)))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))) = Some (tt, s_w) ->
  exec (execute_JAL imm rd) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Halign Hzca Hwx.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  apply (exec_execute_JAL_zca imm (Regidx rd) s _ Halign Hzca).
  rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
             (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

Section KVJAL.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).

(* generalized 4-byte-aligned NON-RVC (F_Base) fetch at a symbolic code-page address va. *)
Section FetchBaseAt4.
  Context (va : mword 64) (region : PMA_Region) (w : mword 32) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr va) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr va) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte w j).
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = false.
  Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = false.
  Hypothesis Halign4 : is_aligned_vaddr (Virtaddr va) 4 = true.

  Lemma exec_fetch_bytes_4b_at : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR.
        rewrite (exec_translateAddr_super_fetch_at root_ppn va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w s
                   HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_Base_4_at : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            rewrite Halign4. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4b_at).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchBaseAt4.
Section HartActiveProgress_gen.
  Context (priv : Privilege) (s s_f s_x s_final : mstate) (w : mword 32) (instr : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = priv.
  Hypothesis Hdisp : exec (dispatchInterrupt priv) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s_f).
  Hypothesis Hdec : exec (ext_decode w) s_f = Some (instr, s_f).
  Hypothesis Hlpad : eq_vec (register_lookup elp s_f.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hnotlpad : is_lpad_instruction instr = false.
  Hypothesis HpcF : register_lookup PC s_f.(sregs) = pc.
  Let s_pc : mstate := set_reg s_f nextPC (add_vec_int pc 4).
  Hypothesis Hexec : exec (execute instr) s_pc = Some (resf, s_x).
  Hypothesis Hnotexec : match resf with ExecuteAs _ => False | _ => True end.

  Lemma exec_hart_active_progress_gen :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    (* read cur_privilege -> Machine *)
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    (* dispatchInterrupt -> None ; the `fun w1 =>` body is
       (match w1) >> liftR(fetch) >>= fun w2 => ..  =  bind (bind0 MATCH (liftR fetch)) k *)
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    (* outer bind; inner bind0 (returnR tt) (liftR fetch) *)
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    (* ext_fetch_hook (F_Base w) = F_Base w ; F_Base branch (announce/callback lets) *)
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    (* ext_decode w -> instr *)
    rewrite execR_bind execR_liftR Hdec. cbn match.
    (* (if print=false then.. else returnR tt) >> and_boolM(..) >>= fun w21 => ..
       = bind (bind0 (returnR tt) and_boolM) k *)
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* and_boolM (liftR is_landing_pad) (returnR (not lpad)) -> false (short-circuit) *)
    unfold and_boolM.
    rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
    rewrite execR_returnR. cbn match. cbn match.
    (* w21 = false -> else: read PC >>= fun w22 => bind0 (write nextPC) (liftR execute) >>= ... *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* (match resf : not ExecuteAs => resf) >>= fun result' => returnR (Step_Execute ..) *)
    rewrite execR_bind.
    destruct resf; cbn in Hnotexec; try contradiction;
      cbn match; rewrite execR_returnR; cbn match; rewrite execR_returnR; reflexivity.
  Qed.

End HartActiveProgress_gen.

Section ForwardJALsup.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (imm : mword 21) (rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
    exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0).
  Hypothesis Hdisp_s : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b) = Some (None, set_reg s (R_bool minstret_increment) b).

  Definition sAjs : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcjs : mstate := set_reg sAjs nextPC (add_vec_int pc 4).
  Definition jtgts : mword 64 :=
    add_vec (register_lookup PC s_pcjs.(sregs)) (sign_extend' 64 imm).
  Definition jlinks : mword 64 := register_lookup nextPC s_pcjs.(sregs).
  Definition sXjs : mstate :=
    set_reg (set_reg s_pcjs nextPC jtgts)
            (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg jlinks).
  Definition sTjs : mstate := set_reg sXjs PC (register_lookup nextPC sXjs.(sregs)).
  Definition sFjs : mstate :=
    if b then set_reg sTjs minstret (add_vec_int (register_lookup minstret sTjs.(sregs)) 1)
         else sTjs.

  
  Lemma forward_exec_jal_sup :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (access_vec_dec jtgts 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s_pcjs = Some (true, s_pcjs) ->
    exec riscv_step s = Some (tt, sFjs).
  Proof using All.
    intros Lpc Lpriv Lhs Lelp Halign Hzca.
    assert (LpcA  : register_lookup PC sAjs.(sregs) = pc).
    { unfold sAjs, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAjs.(sregs) = Supervisor).
    { unfold sAjs, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAjs.(sregs) = HART_ACTIVE tt).
    { unfold sAjs, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAjs.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAjs, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HfetchA : exec (fetch tt) sAjs = Some (F_Base w, sAjs)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAjs = Some (JAL (imm, Regidx rd), sAjs)) by (apply Hdec; exact LprivA).
    assert (HexecJ : exec (execute (JAL (imm, Regidx rd))) s_pcjs = Some (RETIRE_SUCCESS, sXjs)).
    { change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr_zca imm rd s_pcjs Hrd0 Halign Hzca).
      unfold sXjs, jtgts, jlinks. reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAjs = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXjs)).
    { exact (exec_hart_active_progress_gen Supervisor sAjs sAjs sXjs sAjs w
               (JAL (imm, Regidx rd)) pc RETIRE_SUCCESS
               LprivA Hdisp_s HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecJ I). }
    apply (exec_riscv_step_gen_gen Supervisor s sXjs (zero_extend' 32 w) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXjs, s_pcjs, sAjs; cbn [sregs].
      do 4 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhs.
    - unfold sXjs, s_pcjs, sAjs; cbn [sregs].
      do 3 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardJALsup.


  (* generalized iris fetch bridge (4-byte NON-RVC / F_Base) at symbolic code address va. *)
  Lemma fetch_from_pts_Base (va : mword 64)
      (mstatus0 misa0 satp0 : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr va) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = sp_vpn ->
    zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    neq_vec (access_vec_dec va 0) ('b"0") = false ->
    neq_vec (access_vec_dec va 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint va) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr va) 4 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ va -∗ cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ misa ↦ᵣ misa0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add va j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hmode Hasid Hvec Hcanon Hvpn_def Hident Hbit0 Hbit1 Halign4
             HA0 Hord0 Hrange0 HX0 Halign HmisaC0 HisRVC)
            "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hmisa Hpmpc Hpmpaddr Hpma Hhtif Hbytes".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")   as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add va j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram va⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = va).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Supervisor).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltms : register_lookup mstatus t.(sregs) = mstatus0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity]. }
    assert (Ltsatp : register_lookup satp t.(sregs) = satp0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lsatp | vm_compute; reflexivity]. }
    assert (Lttlb : register_lookup tlb t.(sregs) = tlbvec).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Ltlb | vm_compute; reflexivity]. }
    assert (Ltmisa : register_lookup misa t.(sregs) = misa0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmisa | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpmpaddr : register_lookup pmpaddr_n t.(sregs) = pmpaddr00).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add va j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    exact (exec_fetch_Base_4_at va region w satp0 tlbvec t Ltpriv Ltpc
             ltac:(rewrite Ltms; exact HSXL0) Ltsatp Hmode Hasid Lttlb Hvec
             Hcanon Hvpn_def Hident
             ltac:(rewrite Ltpmpc; exact HA0)
             ltac:(rewrite Ltpmpaddr; exact Hord0)
             ltac:(rewrite Ltpmpaddr; exact Hrange0)
             ltac:(rewrite Ltpmpc; exact HX0)
             ltac:(rewrite Ltpma; exact Hmatch0)
             Halign Hexec
             (within_clint_false va 4 t Hnc ltac:(lia))
             (within_sig_false  va 4 t Hns ltac:(lia))
             (within_htif_false va 4 t Lthtif)
             Ltmem HisRVC Hbit0 Hbit1 Halign4).
  Qed.

End KVJAL.

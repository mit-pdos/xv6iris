(* WpMemsetS.v -- executing [memset]'s entry in S-mode.

   [memset(void *dst, int c, uint n)] (kernel/string.c) begins, per the proof's
   [KernelInstrs] byte map, at [KernelSyms.memset = 0x80000ccc]:

     80000ccc:  1141    addi  sp,sp,-16     <- this instruction (frame alloc)
     80000cce:  e406    sd    ra,8(sp)
     80000cd0:  e022    sd    s0,0(sp)
     80000cd2:  0800    addi  s0,sp,16
     80000cd4:  ca19    beqz  a2,...        (loop-skip when n = 0)
     ...

   The entry instruction is the compressed [c.addi sp,sp,-16] (halfword 0x1141,
   funct3 = 000 -- an ordinary C.ADDI to x2, NOT c.addi16sp).  It is register-
   only (it writes just [sp]; no memory access), so it needs no data-page Sv39
   geometry -- only the FETCH side conditions of the S-mode step engine.  We
   run it on [wp_rvc_gpr_write_s] (the generic S-mode RVC gpr-write engine, the
   same one [wp_caddi16sp_gpr_s] is built on), specialising the ExecuteAs base
   to the [ITYPE ADDI] expansion.

   THE THEOREM ([wp_memset_s]): from [memset]'s entry PC in S-mode -- with the
   standard kernel Sv39 fetch setup (identity superpage TLB hit at slot 5, PMP
   TOR entry 0 granting S-mode fetch over the code page) -- [memset] executes
   its first instruction, allocating its 16-byte stack frame ([sp := sp - 16])
   and advancing to [memset+2], with every ambient S-mode cell handed back to
   the continuation unchanged. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore.
Require Import SmodeCore WpSmodeGpr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpMemsetS.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition pc_memset : mword 64 := mword_of_int KernelSyms.memset.
  (* the entry halfword [c.addi sp,sp,-16], and the 4-byte fetch window it sits
     in (its own 0x1141 in the low half, the next halfword 0xe406 in the high). *)
  Definition h_memset0 : mword 16 := mword_of_int 0x1141.
  Definition w_memset0 : mword 32 := mword_of_int 0xe4061141.
  (* C.ADDI's 6-bit signed immediate (== -16) and destination register (== sp),
     extracted exactly as the model's decoder does (mirror of [imm_caddi] /
     [rsd_caddi] in WpEntry). *)
  Definition imm_memset0 : mword 6 :=
    concat_vec (subrange_vec_dec h_memset0 12 12) (subrange_vec_dec h_memset0 6 2).
  Definition rsd_memset0 : regidx :=
    Regidx (autocast (T := mword)
              (subrange_vec_dec (subrange_vec_dec h_memset0 11 7)
                 (Z.sub regidx_bit_width 1) 0)).

  (* The destination is sp, and the immediate sign-extends to -16. *)
  Lemma rsd_memset0_sp : rsd_memset0 = Regidx csp_rs1.
  Proof. reflexivity. Qed.

  Lemma imm_memset0_val :
    sign_extend' 64 (sign_extend' 12 imm_memset0) = (mword_of_int (-16) : mword 64).
  Proof. apply bv_eq. vm_compute; reflexivity. Qed.

  (* ---- decode: 0x1141 decodes to [C_ADDI (imm_memset0, rsd_memset0)] ---- *)
  Lemma decode_memset_addi s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_memset0) s = Some (C_ADDI (imm_memset0, rsd_memset0), s).
  Proof.
    intro HmisaC. unfold imm_memset0, rsd_memset0.
    assert (Hrsd : exec (encdec_reg_backwards (subrange_vec_dec h_memset0 11 7)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec h_memset0 11 7)
                             (Z.sub regidx_bit_width 1) 0)), s)).
    { unfold encdec_reg_backwards.
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end. cbn match. apply exec_returnM. }
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (dstep s HmisaC).
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrsd). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* ---- the [instr] fact at [memset]'s entry (4-aligned RVC) ---- *)
  (* Under the post-refactor [instr], the RVC arm carries the ExecuteAs-EXPANDED
     base instruction: the entry c.addi16sp expands to [addi sp,sp,-16]. *)
  Lemma memset_instr0 :
    kernel_text -∗ instr pc_memset true (ITYPE (sign_extend' 12 imm_memset0, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof.
    assert (Hlpad : is_lpad_instruction (ITYPE (sign_extend' 12 imm_memset0, Regidx csp_rs1, Regidx csp_rs1, ADDI)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr pc_memset) 2 = true) by (vm_compute; reflexivity).
    (* memset now sits at a 2-aligned (mod 4 = 2) address, so the entry
       c.addi16sp is recovered from a 2-byte (rvc2) fetch window. *)
    assert (H4al : is_aligned_vaddr (Virtaddr pc_memset) 4 = false) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC h_memset0 = true) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (KernelSyms.memset + Z.of_nat j)%Z = Some (nth_byte h_memset0 j)).
    { intros j Hj;
        do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC h_memset0).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc2 pc_memset h_memset0 H2al H4al Hrvc).
      iApply (kernel_window_pc KernelSyms.memset h_memset0 2 pc_memset eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC _. cbn [fetch_is_rvc].
      eexists. split; [ exact (decode_memset_addi σ HmisaC)
                      | split; [ vm_compute; reflexivity | intro; apply exec_execute_C_ADDI ] ].
  Qed.


  (* =================================================================== *)
  (*  Branch execute-reductions (BTYPE), from scratch against the model's  *)
  (*  [execute_BTYPE]: read rs1/rs2, compare, and either fall through      *)
  (*  (RETIRE_SUCCESS, state unchanged) or jump to PC + sext(imm).         *)
  (* =================================================================== *)

  (* register value as [rX_bits] reads it (x0 -> zero_reg). *)
  Definition rvv (r : mword 5) (s : mstate) : mword 64 :=
    if Z.eqb (uint r) 0 then zero_reg
    else register_lookup (R_bitvector_64 (gpr_of_Z (uint r))) s.(sregs).

  (* the comparison prefix of [execute_BTYPE] for BNE / BEQ evaluates to the
     boolean [taken], leaving the state unchanged. *)
  Lemma exec_BTYPE_cmp_BNE (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (neq_vec w2 w3)))) s
      = Some (neq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

  Lemma exec_BTYPE_cmp_BEQ (rs2 rs1 : mword 5) s :
    exec (Defs.bind (rX_bits (Regidx rs1))
            (fun w2 => Defs.bind (rX_bits (Regidx rs2))
               (fun w3 => returnM (eq_vec w2 w3)))) s
      = Some (eq_vec (rvv rs1 s) (rvv rs2 s), s).
  Proof.
    unfold rvv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BNE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BEQ_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS, s).
  Proof.
    intro Hfall.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Hfall. apply exec_returnM.
  Qed.

  Lemma exec_execute_BTYPE_BEQ_taken (imm : mword 13) (rs2 rs1 : mword 5) s :
    eq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hbit1.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to _ s Halign Hbit1).
  Qed.

  Lemma exec_execute_BTYPE_BNE_taken (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hbit1.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to _ s Halign Hbit1).
  Qed.

  (* jump_to variant allowing a 2-aligned (bit1 = 1) target under the C
     extension (Zca enabled) -- for the memset loop's back-edge, whose head
     [sb] sits at a 2-aligned (not 4-aligned) address in the relocated image.
     Mirrors WpKernelvecNew.kv_exec_jump_to_zca, which lives downstream of this
     file and so is re-proved locally. *)
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

  (* [exec_execute_JALR_ret] variant for a 2-aligned (bit1 possibly set)
     return target under the C extension: the misalignment check reduces via
     [exec_jump_to_zca] instead of requiring bit1 = 0. *)
  Lemma exec_execute_JALR_ret_zca (imm : mword 12) (rs1 rdz : mword 5) s :
    uint rs1 <> 0 -> uint rdz = 0 ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s) ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    eq_vec (access_vec_dec (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0")) 0) ('b"0") = true ->
    exec (execute_JALR imm (Regidx rs1) (Regidx rdz)) s
    = Some (RETIRE_SUCCESS,
            set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))).
  Proof.
    intros Hrs1 Hrdz Hzic Hzca Halign.
    unfold execute_JALR.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) s
                   = Some (register_lookup nextPC s.(sregs), s))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
                  (_ : exec (update_elp_state (Regidx rs1)) s = Some (tt, s))).
        2:{ unfold update_elp_state. rewrite (exec_bind_Some _ _ _ _ _ Hzic). cbn match. apply exec_returnm. }
        unfold get_next_pc. exact (exec_read_reg nextPC s). }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
    replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _
              (exec_wX_bits_gpr rdz (register_lookup nextPC s.(sregs))
                  (set_reg s nextPC (update_vec_dec (add_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (sign_extend' 64 imm)) 0 ('b"0"))))).
    rewrite Hrdz. cbn match. apply exec_returnm.
  Qed.

  Lemma exec_execute_BTYPE_BNE_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
    neq_vec (rvv rs1 s) (rvv rs2 s) = true ->
    eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
    exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
    exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))) s
      = Some (RETIRE_SUCCESS,
              set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
  Proof.
    intros Htaken Halign Hzca.
    unfold execute. cbn match. unfold execute_BTYPE.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BNE rs2 rs1 s)).
    rewrite Htaken.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    exact (exec_jump_to_zca _ s Halign Hzca).
  Qed.

  Lemma exec_execute_C_BEQZ (imm : mword 8) (rs : cregidx) s :
    exec (execute (C_BEQZ (imm, rs))) s
      = Some (ExecuteAs (BTYPE (sign_extend' 13 (concat_vec imm ('b"0")), zreg, creg2reg_idx rs, BEQ)), s).
  Proof. unfold execute. cbn match. unfold execute_C_BEQZ. apply exec_returnM. Qed.

  (* ---- bne rs1,rs2  NOT taken (rs1 == rs2): fall through to pc+4 ---- *)

  (* ---- bne rs1,rs2  TAKEN (rs1 <> rs2): jump to pc + sext(imm) ---- *)

  (* ---- beqz rs (c.beqz) NOT taken (rs <> 0): fall through to pc+2 ---- *)

  (* =================================================================== *)
  (*  Base (4-byte) register-write S-mode engine -- the [is_rvc = false]   *)
  (*  analogue of [wp_rvc_gpr_write_s]: any base instruction [i] that       *)
  (*  writes ONE gpr [rd := wval].  Used for memset's [add a4,a2,a0].       *)
  (*  Extra premise: the SECOND fetch half also has fetch geometry.         *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  c.ret  (= c.jr ra = jalr x0, 0(ra)): the RETURN.  Sets nextPC := ra  *)
  (*  (low bit cleared), no register write.  JALR's execute consults        *)
  (*  currentlyEnabled Ext_Zicfilp, which in Supervisor reads menvcfg.LPE;   *)
  (*  so this runs on [wp_instr_s_config] (menvcfg value exposed).          *)
  (* =================================================================== *)

  (* Supervisor mirror of WpGprJalr.exec_cE_zicfilp_false: get_xLPE reads
     menvcfg.LPE at Supervisor (vs mseccfg.MLPE at Machine). *)
  Lemma exec_cE_zicfilp_false_S s :
    register_lookup cur_privilege (sregs s) = Supervisor ->
    bool_bit_backwards (_get_MEnvcfg_LPE (register_lookup menvcfg s.(sregs))) = false ->
    exec (currentlyEnabled Ext_Zicfilp) s = Some (false, s).
  Proof.
    intros Hpriv Hlpe.
    unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
    cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _
              (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
                 ltac:(vm_compute; reflexivity))).
    cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    match goal with |- context[_rec_get_xLPE Supervisor _ ?acc] => destruct acc end.
    cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn match.
    rewrite Hlpe. apply exec_returnM.
  Qed.


  Lemma wp_cret_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let tgt := update_vec_dec (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hra Hlpe Halign Hbit1.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (JALR (zeros' 12, Regidx ra, zreg))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    assert (Hma : m !! Regidx ra = Some (m !!! Regidx ra))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value ra (m !!! Regidx ra) s_pc with "Hreg Hrac") as %Lra.
    iDestruct ("Hfb" with "Hrac") as "Hfmap".
    assert (Lra' : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs) = m !!! Regidx ra).
    { pose proof Lra as H.
      replace (Z.eqb (uint ra) 0) with false in H by (symmetry; apply Z.eqb_neq; exact Hra).
      cbn match in H. exact H. }
    assert (Hpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hmenv_spc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmenv | vm_compute; reflexivity ]. }
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false_S; [ exact Hpriv_spc | rewrite Hmenv_spc; exact Hlpe ]. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htgt : update_vec_dec (add_vec
                (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                (sign_extend' 64 (zeros' 12))) 0 ('b"0") = tgt)
        by (rewrite Lra'; reflexivity).
      rewrite <- Htgt.
      apply (exec_execute_JALR_ret (zeros' 12) ra (zero_extend' 5 ('b"00") : mword 5) s_pc
               Hra ltac:(vm_compute; reflexivity) Hzic).
      - rewrite Htgt. exact Halign.
      - rewrite Htgt. exact Hbit1. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes] [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  Lemma wp_cret_s_zca (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (ra : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let tgt := update_vec_dec (add_vec (m !!! Regidx ra) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint ra <> 0 ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (JALR (zeros' 12, Regidx ra, zreg)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is tgt -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hra Hlpe Halign.
    iIntros "#Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & %HmisaC & _)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (JALR (zeros' 12, Regidx ra, zreg))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx ra = Some (m !!! Regidx ra))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfb]".
    iDestruct (gpr_pt_value ra (m !!! Regidx ra) s_pc with "Hreg Hrac") as %Lra.
    iDestruct ("Hfb" with "Hrac") as "Hfmap".
    assert (Lra' : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs) = m !!! Regidx ra).
    { pose proof Lra as H.
      replace (Z.eqb (uint ra) 0) with false in H by (symmetry; apply Z.eqb_neq; exact Hra).
      cbn match in H. exact H. }
    assert (Hpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (Hmenv_spc : register_lookup menvcfg s_pc.(sregs) = menvcfg0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmenv | vm_compute; reflexivity ]. }
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false_S; [ exact Hpriv_spc | rewrite Hmenv_spc; exact Hlpe ]. }
    assert (Hmisa_spc : register_lookup misa s_pc.(sregs) = misa0).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (Hzca : exec (currentlyEnabled Ext_Zca) s_pc = Some (true, s_pc)).
    { apply exec_currentlyEnabled_Zca. rewrite Hmisa_spc. exact HmisaC. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htgt : update_vec_dec (add_vec
                (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                (sign_extend' 64 (zeros' 12))) 0 ('b"0") = tgt)
        by (rewrite Lra'; reflexivity).
      rewrite <- Htgt.
      apply (exec_execute_JALR_ret_zca (zeros' 12) ra (zero_extend' 5 ('b"00") : mword 5) s_pc
               Hra ltac:(vm_compute; reflexivity) Hzic Hzca).
      rewrite Htgt. exact Halign. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes] [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* =================================================================== *)
  (*  Width-1 (store-byte) low-level data-path primitives -- ports of the  *)
  (*  width-8 store primitives in WpSmodeGpr Part A with width := 1.        *)
  (*  (within_clint/sig/htif are width-generic and reused directly.)       *)
  (* =================================================================== *)

  Lemma exec_write_ram_plain_1 (addr : mword 64) (data : bv 8) s :
    exec (write_ram rv64d_types.Write_plain (Physaddr addr) 1 data tt) s
    = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 1 data)).
  Proof.
    unfold write_ram. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
    unfold Defs.sail_mem_write. cbn beta zeta iota match.
    unfold Defs.bind. cbn [Interface.iMon_bind]. cbn match. reflexivity.
  Qed.

  Lemma exec_pmaCheck_ram_store_1 (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (pmaCheck (Physaddr addr) 1 (Store Data) pbmt false) s = Some (None, s).
  Proof.
    intros Hmatch Halign Hwrite.
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

  Lemma exec_checked_mem_write_ram_store_S_1 (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 8) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 1)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 1) s = Some (false, s) ->
    exec (checked_mem_write (Physaddr addr) 1 data (Store Data) pbmt Supervisor tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 1 data)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh.
    unfold checked_mem_write.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store addr 1 s HA Hord Hrange HW)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_1 addr pbmt region s Hmatch Halign Hwrite)).
        cbn match. apply exec_returnM. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_writable (Physaddr addr) 1) s = Some (false, s))).
    2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_1 addr data s)).
    apply exec_returnM.
  Qed.

  Lemma exec_mem_write_value_1_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : bv 8) (m : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 1)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 1 = Some region ->
    is_aligned_paddr (Physaddr addr) 1 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 1) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) 1) s = Some (false, s) ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_write_value (Physaddr addr) 1 data (Store Data) pbmt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 1 data)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hms Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. rewrite Hms.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
    unfold mem_write_value_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_S_1 pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh)).
    cbn match. unfold mem_write_callback. apply exec_returnm.
  Qed.

  (* width-1 split_misaligned: a 1-byte access is always aligned -> 1 chunk. *)
  Lemma exec_split_misaligned_aligned_1 (vaddr : virtaddr) s :
    is_aligned_vaddr vaddr 1 = true ->
    exec (split_misaligned vaddr 1) s = Some ((1, 1), s).
  Proof.
    intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm.
  Qed.

  Lemma exec_mem_write_ea_1 (addr : mword 64) s :
    exec (mem_write_ea (Physaddr addr) 1 false false false) s = Some (Ok tt, s).
  Proof.
    unfold mem_write_ea. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    apply exec_returnM.
  Qed.

  Lemma is_aligned_vaddr_1 (vaddr : virtaddr) : is_aligned_vaddr vaddr 1 = true.
  Proof. destruct vaddr as [addr]. unfold is_aligned_vaddr. rewrite Z.rem_1_r. reflexivity. Qed.

  Lemma is_aligned_paddr_1 (paddr : physaddr) : is_aligned_paddr paddr 1 = true.
  Proof. destruct paddr as [addr]. unfold is_aligned_paddr. rewrite Z.rem_1_r. reflexivity. Qed.

  (* ---- width-1 vmem_write_addr: the aligned single-byte write path ---- *)
  Section SWS1.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).

  Lemma exec_vmem_write_addr_1_S :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 1 data)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 1 data)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                      = Some (tt, s)) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                             = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 1 data)))
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
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_1 (zero_extend' 64 (add_vec_int a (0*1))) s)).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 1 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (1*(0+1)*8-1) with 7. change (1*0*8) with 0. change (1*8) with 8.
               change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold subrange_vec_dec. change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data
               (register_lookup mstatus s.(sregs)) s HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh eq_refl Hmprv Hcp)).
          cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS1.

  (* ---- width-1 register-generic vmem_write: base from rs1, byte [data] ---- *)
  Section VWgS1.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).

  Lemma exec_vmem_write_1_gpr_S :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 1 data)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_1_S a8 data region s Halign Hcp Hmprv Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh).
    reflexivity.
  Qed.
  End VWgS1.

  (* ---- width-1 register-generic STORE execute (sb): store low byte of rs2 ---- *)
  Section ExecStoreGS1.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).

  Lemma exec_execute_STORE_1_gpr_S :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s.(sregs) (write_bytes s.(mem) pa 1
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0) : mword 8))).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 1)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 1).
    unfold execute_STORE.
    replace (1 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_1_gpr_S rs1 offset _ region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1.

  (* ---- width-1 WALK mirrors: the store's data translation FILLS the TLB
     (s -> s' = set_reg s tlb tlbf); ports of WpSmodeGpr's width-8
     SWSwalk / VWgSwalk / ExecStoreGSwalk with width := 1. ---- *)
  Section SWS1walk.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').

  Lemma exec_vmem_write_addr_1_S_walk :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data)).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s
                   = Some (inr (true, 0%Z, true), MState s'.(sregs) (write_bytes s.(mem) pa 1 data)))
    end.
    { eapply execR_untilMT_1.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s'
                      = Some (tt, s')) by reflexivity.
        assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                              : Defs.monadR (result bool ExecutionResult) exception unit) s' = Some (inr tt, s'))
          by (rewrite execR_liftR; rewrite Hsc; reflexivity).
        match goal with
        | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
            assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s'
                             = Some (inr true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data)))
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
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_1 (zero_extend' 64 (add_vec_int a (0*1))) s')).
          cbn match.
          match goal with
          | |- context [ mem_write_value ?pp 1 ?D (Store Data) ?pb false false false ] =>
              replace D with data
          end.
          2: { symmetry.
               change (1*(0+1)*8-1) with 7. change (1*0*8) with 0. change (1*8) with 8.
               change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold subrange_vec_dec. change (7 - 0 + 1) with 8. rewrite autocast_id.
               unfold to_word_idx, to_word, get_word, MachineWord.slice.
               rewrite MachineWord.cast_idx_refl.
               apply bv_eq. rewrite bv_extract_unsigned.
               change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
               apply bv_wrap_bv_unsigned. }
          assert (Hmem' : s'.(mem) = s.(mem)) by reflexivity.
          rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_1_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*1))) region data
               (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh eq_refl Hmprv Hcp)).
          cbn match.
          rewrite Hmem'.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
        cbn.
        apply execR_returnR_fwd.
      - apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu).
    cbn. reflexivity.
  Qed.
  End SWS1walk.

  Section VWgS1walk.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').

  Lemma exec_vmem_write_1_gpr_S_walk :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s
      = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 1 data)).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
    rewrite execR_liftR.
    rewrite (exec_vmem_write_addr_1_S_walk a8 data region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh).
    reflexivity.
  Qed.
  End VWgS1walk.

  Section ExecStoreGS1walk.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').

  Lemma exec_execute_STORE_1_gpr_S_walk :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s
      = Some (RETIRE_SUCCESS,
              MState s'.(sregs) (write_bytes s.(mem) pa 1
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 1 8) 1) 0) : mword 8))).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 1)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 1).
    unfold execute_STORE.
    replace (1 <=? xlen_bytes) with true by (vm_compute; reflexivity).
    assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                   = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
      (exec_vmem_write_1_gpr_S_walk rs1 offset _ region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh)).
    cbn match.
    apply exec_returnM.
  Qed.
  End ExecStoreGS1walk.

  Lemma write_bytes_1 (mm : _) (pa : Arch.pa) (v : bv 8) :
    write_bytes mm pa 1 v = <[pa := nth_byte v 0]> mm.
  Proof. unfold write_bytes. change (N.to_nat 1) with 1%nat. cbn [seq foldr]. rewrite pa_add_0. reflexivity. Qed.

  Lemma mem_update_1 (mm : _) (pa : Arch.pa) (vold vnew : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ pa ↦ₘ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa 1 vnew) ∗ pa ↦ₘ (nth_byte vnew 0).
  Proof. rewrite write_bytes_1. apply mem_update. Qed.

  (* =================================================================== *)
  (*  sb rs2, imm(rs1)  in S-mode: store the low byte of rs2 to the byte  *)
  (*  address ea = rs1 + sext(imm) -- a TLB HIT at tlb_hash of its vpn.    *)
  (*  Base (4-byte) instruction (wp_instr_s_config, is_rvc=false), width-1 *)
  (*  store path, single-byte points-to updated from [vold] to rs2's byte. *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  sb rs2, imm(rs1) UNIFIED over the TLB/page-table consistency        *)
  (*  invariant: the fetch case-splits inside the engine; the DATA        *)
  (*  translation case-splits here (hit: state-preserving; miss: store    *)
  (*  page-walk + fill at tlb_hash svpn, preserving the invariant).       *)
  (* =================================================================== *)
  Lemma wp_sb_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 8)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)) in
    let storeval := (autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    svpn_of (add_vec_int pc 2) = svpn_of pc ->
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* store PMP: TOR entry 0 covers pa with W *)
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    (pa ↦ₘ vold) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      (pa ↦ₘ (nth_byte storeval 0)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ea a8 pa storeval HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
      HX Hcov Hsp2 Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn
      Hpmpp Hpteregion Halignp Hrange_st HW.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbyte Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    destruct (Hpma_all pa 1) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st).
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    pose proof Hpmpp as Hpmpp_copy.
    destruct Hpmpp_copy as (HA0 & Hord0 & Hrangep & HRp).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (STORE (imm, Regidx rs2, Regidx rs1, 1))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov (fun _ => Hsp2)
              Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    assert (Hms1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (mem_ram with "Hbyte") as %Hr0. iPureIntro. exact Hr0. }
    (* the walk's PTE bytes + their RAM-ness (used by the data-miss branch) *)
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)⌝)%I as %Hpbytesf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hpbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (pte_paddr root_ppn)⌝)%I as %Hramp.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hpbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hms1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    destruct (Hconsf (tlb_hash (__id 39) svpn) (tlb_hash_range svpn)) as [Hd | Hd].
    - (* ---- data slot EMPTY: the store's translation WALKS and fills ---- *)
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) svpn)
                      (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      set (s_f := set_reg s_pc tlb tlbf2).
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 1 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_f Lhtif_f) as Hwh.
      pose proof (within_clint_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_clint _ Hramp) ltac:(lia)) as Hwcp.
      pose proof (within_sig_false (pte_paddr root_ppn) 8 s_pc (addr_is_ram_not_in_sig _ Hramp) ltac:(lia)) as Hwsp.
      pose proof (within_htif_false (pte_paddr root_ppn) 8 s_pc Lhtif_pc) as Hwhp.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        apply (exec_translateAddr_store_walk root_ppn a8 svpn region_pte menvcfg0 satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hppn Hasid Hcanon Hvpn_def Hident_walk Ltlb_pc Hd
                 Hvpn2 Hmvpn Hmppn
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc; exact Hrangep) ltac:(rewrite Lpmpc_pc; exact HRp)
                 ltac:(rewrite Lpma_pc; exact Hmatchp0) Halignp Hptep
                 Hwcp Hwsp Hwhp Hpbytesf Lmenv_pc HPBMTE). }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 1 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S_walk rs2 rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f (tlb_hash (__id 39) svpn)
                     (tlb_hash_range svpn) Hconsf)
                  with "Hsatp Htlb Hpbytes"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data slot RESIDENT: TLB hit (state-preserving) ---- *)
      pose proof (within_clint_false pa 1 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 1 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 1 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1)) with a8
          by (cbn [bits_of_virtaddr]; change (0 * 1) with 0; rewrite avi0; reflexivity).
        replace pa with a8 by (unfold pa; change (0 * 1) with 0; rewrite avi0; rewrite zero_extend'_id; reflexivity).
        apply (exec_translateAddr_store_hit root_ppn a8 svpn satp0 tlbvec_f s_pc
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) ltac:(rewrite Lms_pc; exact HMPRV)
                 Lsatp_pc Hmode Hasid Hcanon Hvpn_def Hident Ltlb_pc Hd Hmask). }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 1 storeval)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { rewrite (exec_execute_STORE_1_gpr_S rs2 rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva; apply is_aligned_vaddr_1) ltac:(rewrite Lva; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva; exact Hmatch_st0) ltac:(rewrite Lva; apply is_aligned_paddr_1)
                   Hwrite_st ltac:(rewrite Lva; apply Hwc) ltac:(rewrite Lva; apply Hws)
                   ltac:(rewrite Lva; apply Hwh)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2. reflexivity. }
      iMod (mem_update_1 σ.(mem) pa vold storeval with "Hmem Hbyte") as "[Hmem Hbyte]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                            [$Hpc' $Hnpc] [Hfmap] Hbyte").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  (* =================================================================== *)
  (*  UNBUNDLED register-write engine (RVC), on wp_instr_s_config: reads   *)
  (*  cur_privilege..tlb as separate cells (not the smode_config bundle),  *)
  (*  so it composes with wp_sb_s without a bundle round-trip losing the   *)
  (*  MXR/PMM facts the store needs.  Payload mirrors wp_rvc_gpr_write_s.   *)
  (* =================================================================== *)

  Lemma wp_gpr_write_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd Hbexec)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true base
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- unbundled c.addi rd,imm (on wp_gpr_write_s_config) ---- *)

  Lemma wp_caddi_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  (* ---- unbundled bne rs1,rs2 NOT taken (rs1=rs2): fall to pc+4 ---- *)

  Lemma wp_bne_fall_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    svpn_of (add_vec_int pc 2) = svpn_of pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hsp2 Hpmpp Hpteregion Halignp Hrs1 Hrs2 Hcmp)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov (fun _ => Hsp2) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BNE_fall. unfold rvv. rewrite Lva Lvb. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- unbundled bne rs1,rs2 TAKEN (rs1<>rs2): jump to pc+sext(imm) ---- *)

  Lemma wp_bne_taken_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    svpn_of (add_vec_int pc 2) = svpn_of pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rs1 <> 0 -> uint rs2 <> 0 ->
    neq_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = true ->
    (* only 2-alignment of the target is required: the C extension (Zca,
       derived internally from misa.C) legalizes a bit1 = 1 branch target. *)
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hsp2 Hpmpp Hpteregion Halignp Hrs1 Hrs2 Hcmp Hal0)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (BTYPE (imm, Regidx rs2, Regidx rs1, BNE))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov (fun _ => Hsp2) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      assert (Htk : neq_vec (rvv rs1 s_pc) (rvv rs2 s_pc) = true)
        by (unfold rvv; rewrite Lva Lvb; exact Hcmp).
      assert (HzcaS : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
      { unfold s_pc, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca imm rs2 rs1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc HzcaS)). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (add_vec pc (sign_extend' 64 imm))).(sregs)
             = add_vec pc (sign_extend' 64 imm))
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- unbundled BASE (4-byte) register-write engine (for `add a4`) ---- *)

  Lemma wp_gpr_write_s_config_base (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    svpn_of (add_vec_int pc 2) = svpn_of pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute i) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false i -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hsp2 Hpmpp Hpteregion Halignp Hrd Hbexec)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false i
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov (fun _ => Hsp2) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                with "Hsatp Htlb Hpbytes"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- unbundled c.beqz rs NOT taken (rs<>0): fall to pc+2 ---- *)

  Lemma wp_cbeqz_fall_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(discriminate) Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa [Hsatp Htlb Hpbytes]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- unbundled c.beqz rs TAKEN (rs=0): jump to pc+sext(imm) ---- *)

  (* ============ unbundled RVC register-write wrappers ============ *)
  (* Shared config-fact block, abbreviated in each wrapper below via a copy. *)


  Lemma wp_caddi4spn_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrdc Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.


  Lemma wp_cmv_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      rewrite Hva. reflexivity.
  Qed.


  Lemma wp_cslli_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    rsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrsd Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.


  Lemma wp_csrli_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hcrsd Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hrd _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.


  (* ------------------------------------------------------------------- *)
  (*  The memset fill loop, 0xce0..0xce6:                                  *)
  (*     ce0:  sb   a1, 0(a5)        (store the fill byte at a5)           *)
  (*     ce4:  c.addi a5, a5, 1      (a5 := a5 + 1)                        *)
  (*     ce6:  bne  a5, a4, ce0      (loop while a5 <> a4)                 *)
  (*  Runs [rem] iterations, filling the [rem] pending bytes at a5..a4-1   *)
  (*  with a1's low byte, ending (bne falls through) at 0xcea with a5=a4.  *)
  (*  Proved by induction on [rem]; the whole body runs on the unbundled   *)
  (*  cell interface (wp_sb_s ; wp_caddi_gpr_s_config ; wp_bne_*_s_config) *)
  (*  so no smode_config round-trip loses the store's MXR/PMM facts.       *)
  (*  The per-byte Sv39/PMP geometry and the pointer arithmetic (byte j's  *)
  (*  address, a5+1 vs a4) are provided as hypotheses quantified over the  *)
  (*  byte offset; the loop-INDUCTION structure is what is proved here.    *)
  (* ------------------------------------------------------------------- *)

  (* the store's translated (identity) byte address for a5-value [cur]. *)
  Definition ms_a8 (cur : mword 64) : mword 64 :=
    sign_extend' 64 (subrange_vec_dec (add_vec cur (sign_extend' 64 (mword_of_int 0 : mword 12)))
                       (xlen - 0 - 1) 0).
  Definition ms_pa (cur : mword 64) : mword 64 :=
    zero_extend' 64 (add_vec_int (ms_a8 cur) (0 * 1)).
  (* the j-th byte's a5-value, from base [p]. *)
  Definition ms_addr (p : mword 64) (j : nat) : mword 64 :=
    add_vec p (mword_of_int (Z.of_nat j)).
  (* c.addi a5,a5,1 increments a5 by exactly one. *)
  Definition ms_incr1 : mword 64 := sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)).

  Lemma seq_cons (a b : nat) : seq a (S b) = a :: seq (S a) b.
  Proof. reflexivity. Qed.


  Lemma wp_memset_loop (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (N : nat) (p e cval : mword 64) (ra1 ra4 ra5 : mword 5) (imm_bne : mword 13) (svpn : mword 27)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) (olds : nat -> bv 8) {dq : dfrac} :
    let pc0 := mword_of_int (KernelSyms.memset + 0x14) in
    let pc4 := add_vec_int pc0 4 in
    let pc6 := add_vec_int pc0 6 in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    ↑minstretN ⊆ E ->
    (* register indices distinct from x0 *)
    uint ra1 <> 0 -> uint ra4 <> 0 -> uint ra5 <> 0 ->
    (* shared S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (* fetch: TLB slot 5 + geometry for each of the three instructions *)
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* bne target = loop top pc0; only 2-alignment is needed (the C extension
       legalizes the bit1 = 1 target in the relocated image). *)
    add_vec pc6 (sign_extend' 64 imm_bne) = pc0 ->
    eq_vec (access_vec_dec pc0 0) ('b"0") = true ->
    (* store page-level geometry *)
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (* per-byte store geometry, for each byte offset j < N (a5-value ms_addr p j) *)
    (forall j : nat, (j < N)%nat ->
       neq_vec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j))))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0)) = false) ->
    (forall j : nat, (j < N)%nat ->
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn) ->
    (forall j : nat, (j < N)%nat ->
       zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub pagesize_bits 1) 0)) = ms_a8 (ms_addr p j)) ->
    (forall j : nat, (j < N)%nat ->
       pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
         (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
         (uint (ms_pa (ms_addr p j))) (uint (to_bits 64 1)) = PMP_Match) ->
    (* pointer arithmetic: c.addi advances offset; bne compares a5+1 vs a4=e *)
    (forall j : nat, add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j)) ->
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    (* register indices of a1/a4 are distinct from a5 (so c.addi a5 leaves them) *)
    Regidx ra4 <> Regidx ra5 -> Regidx ra1 <> Regidx ra5 ->
    (* the three loop instructions, fetched fresh each iteration from kernel_text *)
    (⊢ kernel_text -∗ instr pc0 false (STORE (mword_of_int 0, Regidx ra1, Regidx ra5, 1))) ->
    (⊢ kernel_text -∗ instr pc4 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx ra5, Regidx ra5, ADDI))) ->
    (⊢ kernel_text -∗ instr pc6 false (BTYPE (imm_bne, Regidx ra4, Regidx ra5, BNE))) ->
    forall (rem off : nat) (m : gmap regidx (mword 64)),
    (off + rem = N)%nat -> (1 <= rem)%nat ->
    m !!! Regidx ra5 = ms_addr p off ->
    m !!! Regidx ra4 = e ->
    m !!! Regidx ra1 = cval ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗
    pc_is pc0 -∗ gpr_file m -∗
    ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pc6 4) -∗
      gpr_file (<[Regidx ra5 := regval_into_reg (ms_addr p N)]> m) -∗
      ([∗ list] j ∈ seq off rem, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pc0 pc4 pc6 cbyte HN Hra1 Hra4 Hra5 HSIE HMPRV HSXL Hmm HMXR Hpmm
      HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hback Hal0 Hmask Hvpn2s Hmvpns Hmppns HW
      Hcanon Hvpn Hident Hrange Hincr Hcmp Hra4ne Hra1ne Hext0 Hext4 Hext6.
    induction rem as [|rem' IH]; intros off m Hoff Hrem Hcur Hm4 Hm1;
      [ exfalso; lia | ].
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hbuf Hcont".
    iPoseProof (Hext0 with "Htext") as "Hi0".
    iPoseProof (Hext4 with "Htext") as "Hi4".
    iPoseProof (Hext6 with "Htext") as "Hi6".
    (* off < N, and the current byte is offset off *)
    assert (HoffN : (off < N)%nat) by lia.
    (* peel the head byte of the pending buffer *)
    rewrite (seq_cons off rem').
    rewrite big_sepL_cons.
    iDestruct "Hbuf" as "[Hb0 Hbuf]".
    (* --- 0xce0: sb a1, 0(a5) : fill byte [off] --- *)
    iApply (wp_sb_s root_ppn E Φ pc0 ra1 ra5 (mword_of_int 0) svpn m (olds off)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hcur; apply (Hcanon off HoffN))
              ltac:(rewrite Hcur; apply (Hvpn off HoffN))
              ltac:(rewrite Hcur; apply (Hident off HoffN))
              Hmask Hvpn2s Hmvpns Hmppns Hpmpp Hpteregion Halignp
              ltac:(rewrite Hcur; apply (Hrange off HoffN))
              HW
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0 [Hb0]").
    { (* the byte points-to at ms_pa (m!!!ra5) = ms_pa (ms_addr p off) *)
      unfold ms_pa, ms_a8. rewrite Hcur. iExact "Hb0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hb0".
    (* --- 0xce4: c.addi a5, a5, 1 : a5 := a5 + 1 --- *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pc4 ra5 (mword_of_int 1)
              m mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp Hra5
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv [Hpc] Hfile Hi4 [-]").
    { unfold pc4. iExact "Hpc". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    (* the new a5 value = ms_addr p (S off) *)
    set (m' := <[Regidx ra5 := regval_into_reg
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m).
    assert (Hm'a5 : m' !!! Regidx ra5 = ms_addr p (S off)).
    { unfold m'. rewrite lookup_total_insert. unfold regval_into_reg. rewrite Hcur.
      change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
      apply Hincr. }
    assert (Hm'a4 : m' !!! Regidx ra4 = e).
    { unfold m'. rewrite lookup_total_insert_ne; [ exact Hm4 | exact (not_eq_sym Hra4ne) ]. }
    assert (Hm'a1 : m' !!! Regidx ra1 = cval).
    { unfold m'. rewrite lookup_total_insert_ne; [ exact Hm1 | exact (not_eq_sym Hra1ne) ]. }
    (* --- 0xce6: bne a5, a4, ce0 --- *)
    destruct rem' as [|rem''].
    - (* last iteration: S off = N, bne falls through to 0xcea *)
      assert (HSN : (S off = N)%nat) by lia.
      iApply (wp_bne_fall_s_config root_ppn E Φ pc6 imm_bne ra4 ra5
                m' mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
                HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(vm_compute; reflexivity) Hpmpp Hpteregion Halignp Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN); rewrite HSN Nat.eqb_refl; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv [Hpc] Hfile Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hfile] [Hb0 Hbuf]").
      + (* gpr_file m' = <[ra5 := ms_addr p N]> m *)
        rewrite HSN in Hm'a5. unfold m'.
        replace (ms_addr p N) with
          (add_vec (m !!! Regidx ra5) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
        2:{ change (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))) with ms_incr1.
            rewrite Hcur. rewrite Hincr. rewrite HSN. reflexivity. }
        iExact "Hfile".
      + (* buffer: seq off 1 = [off], the single filled byte *)
        cbn [seq]. rewrite big_sepL_cons.
        iSplitL "Hb0"; [ iEval (rewrite Hcur; rewrite Hm1) in "Hb0"; iExact "Hb0" | done ].
    - (* more iterations: S off < N, bne taken back to the loop head pc0 *)
      assert (HSN : (S off < N)%nat) by lia.
      iApply (wp_bne_taken_s_config root_ppn E Φ pc6 imm_bne ra4 ra5
                m' mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
                HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(vm_compute; reflexivity) Hpmpp Hpteregion Halignp Hra5 Hra4
                ltac:(rewrite Hm'a5 Hm'a4; rewrite (Hcmp off HoffN);
                      replace (Nat.eqb (S off) N) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity)
                ltac:(rewrite Hback; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv [Hpc] Hfile Hi6 [-]").
      { unfold pc6. iExact "Hpc". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
      rewrite Hback.
      (* apply the induction hypothesis for rem' = S rem'', off' = S off *)
      iApply (IH (S off) m' ltac:(lia) ltac:(lia) Hm'a5 Hm'a4 Hm'a1
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile [Hbuf] [Hb0 Hcont]").
      + iExact "Hbuf".
      + (* recombine: the just-filled byte [off] + IH's continuation gives seq off (S(S rem'')) filled *)
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbuf'".
        assert (Hmeq : <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m'
                     = <[Regidx ra5 := regval_into_reg (ms_addr p N)]> m)
          by (unfold m'; apply insert_insert).
        iEval (rewrite Hmeq) in "Hfile".
        iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile [Hb0 Hbuf']").
        change (seq off (S (S rem''))) with (off :: seq (S off) (S rem'')).
        rewrite big_sepL_cons.
        iSplitL "Hb0"; [ iEval (rewrite Hcur; rewrite Hm1) in "Hb0"; iExact "Hb0" | iExact "Hbuf'" ].
  Qed.

  (* =================================================================== *)
  (*  THE THEOREM: [memset]'s entry step in S-mode allocates its frame.  *)
  (* =================================================================== *)

  Lemma wp_memset_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) (q : Qp) :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    smode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pc_is pc_memset -∗
    gpr_file m -∗
    kernel_text -∗
    ( smode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddr00 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc_memset 2) -∗
      (* the stack frame is allocated: sp := sp - 16 *)
      gpr_file (<[Regidx csp_rs1 :=
                    regval_into_reg (add_vec (m !!! Regidx csp_rs1)
                                       (mword_of_int (-16) : mword 64))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HX Hcov Hpmpp Hpteregion Halignp) "Hsm Hpmpc Hpmpa Htlbinv Hpc Hfile Htext Hcont".
    iPoseProof (memset_instr0 with "Htext") as "Hinstr".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_rvc_gpr_write_s root_ppn E Φ pc_memset csp_rs1 csp_rs1 csp_rs1
              (ITYPE (sign_extend' 12 imm_memset0, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (mword_of_int (-16) : mword 64))
              m pmpcfg0 pmpaddr00 region_pte q HN HX Hcov Hpmpp Hpteregion Halignp Hsp
              _
              with "Hsm Hpmpc Hpmpa Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (sign_extend' 12 imm_memset0) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. rewrite imm_memset0_val. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  memset SUFFIX, 0xcea..0xcf0: restore ra/s0 from the frame, pop it,   *)
  (*  and return.                                                          *)
  (*     cea: c.ldsp ra,8(sp)   cec: c.ldsp s0,0(sp)                        *)
  (*     cee: c.addi sp,16      cf0: ret (c.jr ra)                          *)
  (*  Ends with PC at the saved return address ra0 (low bit cleared), with *)
  (*  ra=ra0 and s0=s00 restored from the two 8-byte frame slots (held at   *)
  (*  fraction dqm, returned to the caller unchanged).                     *)
  (* =================================================================== *)

  Lemma wp_memset_suffix (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (sp' : mword 64) (ra0 s00 : mword 64) (ra_idx s0_idx : mword 5) (imm_dealloc : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqm : dfrac} :
    let pcL := mword_of_int (KernelSyms.memset + 0x1e) in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    uint ra_idx <> 0 -> uint s0_idx <> 0 ->
    Regidx ra_idx <> Regidx csp_rs1 -> Regidx s0_idx <> Regidx csp_rs1 ->
    Regidx s0_idx <> Regidx ra_idx ->
    m !!! Regidx csp_rs1 = sp' ->
    m !!! Regidx ra_idx = ra0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec ret_tgt 1) = false ->
    (* load geometry for the two frame slots: just the one "PMP TOR entry 0 covers all
       of RAM" fact -- the _ram wrappers derive the rest from the owned points-to. *)
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true ->
    is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true ->
    is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pcL -∗ gpr_file m -∗
    instr pcL true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx ra_idx, false, 8)) -∗
    instr (add_vec_int pcL 2) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx s0_idx, false, 8)) -∗
    instr (add_vec_int pcL 4) true (ITYPE (sign_extend' 12 imm_dealloc, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (add_vec_int pcL 6) true (JALR (zeros' 12, Regidx ra_idx, zreg)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ{ dqm } nth_byte ra0 j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ{ dqm } nth_byte s00 j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ{ dqm } nth_byte ra0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ{ dqm } nth_byte s00 j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcL ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0 ret_tgt
      HN Hrai Hs0i Hrasp Hs0sp Hs0ra Hsp Hra
      HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      HX Hcov Hpmpp Hpteregion Halignp Hal0 Hal1
      Hpmpcov HR HalignR HpalignR HalignS HpalignS.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             Hpc Hfile Hi0 Hi2 Hi4 Hi6 Hbra Hbs0 Hcont".
    (* cea: c.ldsp ra,8(sp) : ra := ra0 *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ pcL (mword_of_int 1) ra_idx m ra0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)(dqm:=dqm)
              HN Hrai HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              Hpmpcov HR
              ltac:(rewrite Hsp; exact HalignR) ltac:(rewrite Hsp; exact HpalignR)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0 [Hbra]").
    { rewrite Hsp. iExact "Hbra". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra".
    set (m1 := <[Regidx ra_idx := regval_into_reg ra0]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = sp')
      by (unfold m1; rewrite lookup_total_insert_ne; [ exact Hsp | exact Hrasp ]).
    (* cec: c.ldsp s0,0(sp) : s0 := s00 *)
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (add_vec_int pcL 2) (mword_of_int 0) s0_idx
              m1 s00
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)(dqm:=dqm)
              HN Hs0i HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              Hpmpcov HR
              ltac:(rewrite Hsp1; exact HalignS) ltac:(rewrite Hsp1; exact HpalignS)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2 [Hbs0]").
    { rewrite Hsp1. iExact "Hbs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbs0".
    set (m2 := <[Regidx s0_idx := regval_into_reg s00]> m1).
    (* cee: c.addi sp,16 : sp := sp'+16 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ (add_vec_int pcL 4) csp_rs1 imm_dealloc
              m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    set (m3 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (m2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m2).
    assert (Hra3 : m3 !!! Regidx ra_idx = ra0).
    { unfold m3, m2, m1. rewrite lookup_total_insert_ne; [| exact (not_eq_sym Hrasp)].
      rewrite lookup_total_insert_ne; [| exact Hs0ra].
      rewrite lookup_total_insert. reflexivity. }
    (* cf0: ret (c.jr ra) : PC := ra0 (low bit cleared) *)
    iApply (wp_cret_s root_ppn E Φ (add_vec_int pcL 6) ra_idx
              m3
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              Hrai Hlpe
              ltac:(rewrite Hra3; exact Hal0) ltac:(rewrite Hra3; exact Hal1)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi6 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    iEval (rewrite Hra3) in "Hpc".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc [Hbra] [Hbs0]").
    - rewrite Hsp. iExact "Hbra".
    - rewrite Hsp1. iExact "Hbs0".
  Qed.

  (* =================================================================== *)
  (*  memset PREFIX, 0xccc..0xcdc: set up the frame and the loop bounds.   *)
  (*     ccc: c.addi sp,-16        cce: c.sdsp ra,8(sp)                     *)
  (*     cd0: c.sdsp s0,0(sp)      cd2: c.addi4spn s0,sp,16                 *)
  (*     cd4: c.beqz a2,cea (n<>0, fall through)                            *)
  (*     cd6: c.mv a5,a0           cd8: c.slli a2,32                        *)
  (*     cda: c.srli a2,32         cdc: add a4,a2,a0                        *)
  (*  Ends at the loop top 0xce0 with sp=sp', ra/s0 saved on the frame,     *)
  (*  s0=sp0, a5=a0 (dst), a2=zext32(count), a4=a2+a0 (end pointer).        *)
  (*  Registers: ra=x1 sp=x2 s0=x8 a0=x10 a1=x11 a2=x12 a4=x14 a5=x15.      *)
  (* =================================================================== *)

  Lemma wp_memset_prefix (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64))
      (imm_entry shamt_l shamt_r : mword 6) (nzimm_s0 imm8_beqz : mword 8)
      (i_add : instruction) (wval_add : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a4_idx : mword 5 := mword_of_int 14 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.memset in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    (* the final register file at the loop top *)
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (* fetch geometry + PMP for all nine C-instr addresses (and add's second half) *)
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* n <> 0 (fall through the c.beqz) *)
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = false ->
    (* the add reduces to a4 := wval_add *)
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int (add_vec_int pcE 16) 4 ->
       (if Z.eqb (uint a2_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a2_idx))) s_pc.(sregs)) = m5 !!! Regidx a2_idx ->
       (if Z.eqb (uint a0_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a0_idx))) s_pc.(sregs)) = m5 !!! Regidx a0_idx ->
       exec (execute i_add) s_pc
       = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint a4_idx))) (regval_into_reg wval_add))) ->
    (* store geometry for the two frame slots (ra at 8(sp'), s0 at 0(sp')): just the
       one "PMP TOR entry 0 covers all of RAM" fact -- the _ram wrappers derive the
       rest (canonicality, identity translation, the gigapage masks, PMP match) from
       the owned points-to (addr_is_ram) themselves. *)
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true ->
    is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true ->
    is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    pc_is pcE -∗ gpr_file m0 -∗
    instr pcE true (ITYPE (sign_extend' 12 imm_entry, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (add_vec_int pcE 2) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx ra_idx, sp, 8)) -∗
    instr (add_vec_int pcE 4) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx s0_idx, sp, 8)) -∗
    instr (add_vec_int pcE 6) true (ITYPE (caddi4spn_imm nzimm_s0, sp, Regidx s0_idx, ADDI)) -∗
    instr (add_vec_int pcE 8) true (BTYPE (sign_extend' 13 (concat_vec imm8_beqz ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) -∗
    instr (add_vec_int pcE 10) true (RTYPE (Regidx a0_idx, zreg, Regidx a5_idx, ADD)) -∗
    instr (add_vec_int pcE 12) true (SHIFTIOP (shamt_l, Regidx a2_idx, Regidx a2_idx, SLLI)) -∗
    instr (add_vec_int pcE 14) true (SHIFTIOP (shamt_r, Regidx a2_idx, Regidx a2_idx, SRLI)) -∗
    instr (add_vec_int pcE 16) false i_add -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte (bv_0 64) j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte (bv_0 64) j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is (add_vec_int pcE 20) -∗ gpr_file m6 -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte (m0 !!! Regidx ra_idx) j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte (m0 !!! Regidx s0_idx) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a2_idx a4_idx a5_idx pcE sp'
      ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0 m1 m2 m3 m4 m5 m6
      HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
      HX Hcov Hpmpp Hpteregion Halignp
      Hn0 Hbexec_add
      Hpmpcov HW_R HalignR HpalignR HalignS HpalignS.
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = sp') by (unfold m1; rewrite lookup_total_insert; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             Hpc Hfile Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16 Hbra Hbs0 Hcont".
    (* ccc: c.addi sp,-16 : sp := sp' *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 imm_entry m0
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi0 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)))]> m0)
      with m1.
    (* cce: c.sdsp ra,8(sp) : store ra0 to 8(sp') *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 2) (mword_of_int 1) ra_idx m1 (bv_0 64)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              Hpmpcov HW_R
              ltac:(rewrite Hsp1; exact HalignR) ltac:(rewrite Hsp1; exact HpalignR)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi2 [Hbra]").
    { rewrite Hsp1. iExact "Hbra". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra".
    (* cd0: c.sdsp s0,0(sp) : store s00 to 0(sp') *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (add_vec_int pcE 4) (mword_of_int 0) s0_idx m1 (bv_0 64)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp
              Hpmpcov HW_R
              ltac:(rewrite Hsp1; exact HalignS) ltac:(rewrite Hsp1; exact HpalignS)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi4 [Hbs0]").
    { rewrite Hsp1. iExact "Hbs0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbs0".
    (* cd2: c.addi4spn s0,sp,16 : s0 := sp'+16 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (add_vec_int pcE 6) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi6 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1)
      with m2.
    (* cd4: c.beqz a2,cea : n<>0, fall through *)
    iApply (wp_cbeqz_fall_s_config root_ppn E Φ (add_vec_int pcE 8) imm8_beqz (Cregidx (mword_of_int 4)) a2_idx m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(unfold m2, m1; rewrite lookup_total_insert_ne; [ rewrite lookup_total_insert_ne; [ exact Hn0 | vm_compute; discriminate ] | vm_compute; discriminate ])
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi8 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    (* cd6: c.mv a5,a0 : a5 := a0 *)
    iApply (wp_cmv_gpr_s_config root_ppn E Φ (add_vec_int pcE 10) a5_idx a0_idx m2
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2)
      with m3.
    (* cd8: c.slli a2,32 : a2 := a2 << shamt_l *)
    iApply (wp_cslli_gpr_s_config root_ppn E Φ (add_vec_int pcE 12) (Regidx a2_idx) a2_idx shamt_l m3
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3)
      with m4.
    (* cda: c.srli a2,32 : a2 := a2 >> shamt_r *)
    iApply (wp_csrli_gpr_s_config root_ppn E Φ (add_vec_int pcE 14) (Cregidx (mword_of_int 4)) a2_idx shamt_r m4
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov Hpmpp Hpteregion Halignp ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi14 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4)
      with m5.
    (* cdc: add a4,a2,a0 : a4 := a2 + a0 (end pointer) *)
    iApply (wp_gpr_write_s_config_base root_ppn E Φ (add_vec_int pcE 16) a4_idx a2_idx a0_idx i_add wval_add m5
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HPBMTE HX Hcov ltac:(vm_compute; reflexivity) Hpmpp Hpteregion Halignp ltac:(vm_compute; discriminate) Hbexec_add
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile".
    change (<[Regidx a4_idx := regval_into_reg wval_add]> m5) with m6.
    replace (add_vec_int (add_vec_int pcE 16) 4) with (add_vec_int pcE 20) by (vm_compute; reflexivity).
    assert (Hra_eq : m1 !!! Regidx ra_idx = m0 !!! Regidx ra_idx)
      by (unfold m1; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    assert (Hs0_eq : m1 !!! Regidx s0_idx = m0 !!! Regidx s0_idx)
      by (unfold m1; rewrite lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
    iEval (rewrite Hsp1 Hra_eq) in "Hbra".
    iEval (rewrite Hsp1 Hs0_eq) in "Hbs0".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra Hbs0").
  Qed.

  (* =================================================================== *)
  (*  THE END-TO-END THEOREM: a WP for the entire [memset], 0xccc through   *)
  (*  its return to the caller (PC = ra0 with the low bit cleared).         *)
  (*  It fuses the three committed segments:                                *)
  (*     wp_memset_prefix (0xccc..0xcdc)  -- frame setup + loop bounds       *)
  (*   ∘ wp_memset_loop   (0xce0..0xce6)  -- the byte-fill loop              *)
  (*   ∘ wp_memset_suffix (0xcea..0xcf0)  -- restore + return.               *)
  (*  n = zext32(count) = N >= 1 (the nonzero, in-range case).              *)
  (* =================================================================== *)

  Lemma wp_memset_s_full (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m0 : gmap regidx (mword 64)) (N : nat)
      (imm_entry shamt_l shamt_r imm_dealloc : mword 6) (nzimm_s0 imm8_beqz : mword 8)
      (i_add : instruction) (wval_add : mword 64) (imm_bne : mword 13)
      (svpn : mword 27) (olds : nat -> bv 8)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    let ra_idx : mword 5 := mword_of_int 1 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a1_idx : mword 5 := mword_of_int 11 in
    let a2_idx : mword 5 := mword_of_int 12 in
    let a4_idx : mword 5 := mword_of_int 14 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let pcE := mword_of_int KernelSyms.memset in
    let pc0L := mword_of_int (KernelSyms.memset + 0x14) in
    let pcLS := mword_of_int (KernelSyms.memset + 0x1e) in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let p := m0 !!! Regidx a0_idx in
    let e := wval_add in
    let cval := m0 !!! Regidx a1_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a8_ra := ea_ra in
    let pa_ra := a8_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a8_s0 := ea_s0 in
    let pa_s0 := a8_s0 in
    let m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0 in
    let m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1 in
    let m3 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx a0_idx))]> m2 in
    let m4 := <[Regidx a2_idx := regval_into_reg (shift_bits_left (m3 !!! Regidx a2_idx) (subrange_vec_dec shamt_l (Z.sub log2_xlen 1) 0))]> m3 in
    let m5 := <[Regidx a2_idx := regval_into_reg (shift_bits_right (m4 !!! Regidx a2_idx) (subrange_vec_dec shamt_r (Z.sub log2_xlen 1) 0))]> m4 in
    let m6 := <[Regidx a4_idx := regval_into_reg wval_add]> m5 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
    ↑minstretN ⊆ E ->
    (1 <= N)%nat ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    (* fetch geometry + PMP: prefix (0..18), loop (ce0-relative), suffix (cea-relative) *)
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (* the add reduces to a4 := wval_add (end pointer) *)
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int (add_vec_int pcE 16) 4 ->
       (if Z.eqb (uint a2_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a2_idx))) s_pc.(sregs)) = m5 !!! Regidx a2_idx ->
       (if Z.eqb (uint a0_idx) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint a0_idx))) s_pc.(sregs)) = m5 !!! Regidx a0_idx ->
       exec (execute i_add) s_pc
       = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint a4_idx))) (regval_into_reg wval_add))) ->
    (* stack-slot geometry, shared by the saves and the restores: just the one "PMP
       TOR entry 0 covers all of RAM" fact -- the _ram wrappers derive the rest
       (canonicality, identity translation, the gigapage masks, PMP match) from the
       owned points-to (addr_is_ram) themselves. *)
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_vaddr (Virtaddr a8_ra) 8 = true ->
    is_aligned_paddr (Physaddr pa_ra) 8 = true ->
    is_aligned_vaddr (Virtaddr a8_s0) 8 = true ->
    is_aligned_paddr (Physaddr pa_s0) 8 = true ->
    (* n <> 0 (fall through the c.beqz) *)
    eq_vec (m0 !!! Regidx a2_idx) zero_reg = false ->
    (* return-target low bits (2-aligned) *)
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec ret_tgt 1) = false ->
    (* loop: bne target = pc0L (only 2-alignment needed), buffer page geometry *)
    add_vec (add_vec_int pc0L 6) (sign_extend' 64 imm_bne) = pc0L ->
    eq_vec (access_vec_dec pc0L 0) ('b"0") = true ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (forall j : nat, (j < N)%nat ->
       neq_vec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j))))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0)) = false) ->
    (forall j : nat, (j < N)%nat ->
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn) ->
    (forall j : nat, (j < N)%nat ->
       zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (ms_a8 (ms_addr p j)))) (Z.sub pagesize_bits 1) 0)) = ms_a8 (ms_addr p j)) ->
    (forall j : nat, (j < N)%nat ->
       pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
         (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
         (uint (ms_pa (ms_addr p j))) (uint (to_bits 64 1)) = PMP_Match) ->
    (forall j : nat, add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j)) ->
    (forall j : nat, (j < N)%nat -> neq_vec (ms_addr p (S j)) e = negb (Nat.eqb (S j) N)) ->
    (⊢ kernel_text -∗ instr pc0L false (STORE (mword_of_int 0, Regidx a1_idx, Regidx a5_idx, 1))) ->
    (⊢ kernel_text -∗ instr (add_vec_int pc0L 4) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx a5_idx, Regidx a5_idx, ADDI))) ->
    (⊢ kernel_text -∗ instr (add_vec_int pc0L 6) false (BTYPE (imm_bne, Regidx a4_idx, Regidx a5_idx, BNE))) ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m0 -∗
    instr pcE true (ITYPE (sign_extend' 12 imm_entry, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (add_vec_int pcE 2) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx ra_idx, sp, 8)) -∗
    instr (add_vec_int pcE 4) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx s0_idx, sp, 8)) -∗
    instr (add_vec_int pcE 6) true (ITYPE (caddi4spn_imm nzimm_s0, sp, Regidx s0_idx, ADDI)) -∗
    instr (add_vec_int pcE 8) true (BTYPE (sign_extend' 13 (concat_vec imm8_beqz ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) -∗
    instr (add_vec_int pcE 10) true (RTYPE (Regidx a0_idx, zreg, Regidx a5_idx, ADD)) -∗
    instr (add_vec_int pcE 12) true (SHIFTIOP (shamt_l, Regidx a2_idx, Regidx a2_idx, SLLI)) -∗
    instr (add_vec_int pcE 14) true (SHIFTIOP (shamt_r, Regidx a2_idx, Regidx a2_idx, SRLI)) -∗
    instr (add_vec_int pcE 16) false i_add -∗
    instr pcLS true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx ra_idx, false, 8)) -∗
    instr (add_vec_int pcLS 2) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx s0_idx, false, 8)) -∗
    instr (add_vec_int pcLS 4) true (ITYPE (sign_extend' 12 imm_dealloc, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    instr (add_vec_int pcLS 6) true (JALR (zeros' 12, Regidx ra_idx, zreg)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte (bv_0 64) j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte (bv_0 64) j) -∗
    ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ olds j) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗ pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗ tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_ra j) ↦ₘ nth_byte ra0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add pa_s0 j) ↦ₘ nth_byte s00 j) -∗
      ([∗ list] j ∈ seq 0 N, (ms_pa (ms_addr p j)) ↦ₘ cbyte) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx s0_idx a0_idx a1_idx a2_idx a4_idx a5_idx pcE pc0L pcLS
      sp' ra0 s00 p e cval ea_ra a8_ra pa_ra ea_s0 a8_s0 pa_s0
      m1 m2 m3 m4 m5 m6 ret_tgt cbyte
      HN HNge1 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
      HX Hcov Hpmpp Hpteregion Halignp
      Hbexec_add
      Hpmpcov HW_R HR_R HalignR HpalignR HalignS HpalignS
      Hn0 Hret0 Hret1 Hbne HpcL0 Hmask_b Hvpn2b Hmvpnb Hmppnb
      Hpb_canon Hpb_vpn Hpb_ident Hpb_range Hincr Hcmp
      Hext0 Hext4 Hext6.
    (* interface: register file at the loop top and the suffix top *)
    assert (Hcur : m6 !!! Regidx a5_idx = ms_addr p 0).
    { unfold m6, m5, m4, m3, m2, m1.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert.
      unfold regval_into_reg. rewrite add_vec_zero_l.
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      unfold ms_addr, p. change (Z.of_nat 0) with 0%Z. symmetry. exact (avi0 (m0 !!! Regidx a0_idx)). }
    assert (Hm4 : m6 !!! Regidx a4_idx = e)
      by (unfold m6, e; rewrite lookup_total_insert; unfold regval_into_reg; reflexivity).
    assert (Hm1 : m6 !!! Regidx a1_idx = cval).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      unfold cval; reflexivity. }
    assert (Hsuf_sp : (<[Regidx a5_idx := regval_into_reg (ms_addr p N)]> m6) !!! Regidx csp_rs1 = sp').
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      rewrite lookup_total_insert; unfold regval_into_reg; reflexivity. }
    assert (Hsuf_ra : (<[Regidx a5_idx := regval_into_reg (ms_addr p N)]> m6) !!! Regidx ra_idx = ra0).
    { unfold m6, m5, m4, m3, m2, m1.
      repeat (rewrite lookup_total_insert_ne; [| vm_compute; discriminate]).
      unfold ra0; reflexivity. }
    assert (Hpc1 : add_vec_int pcE 20 = pc0L) by (vm_compute; reflexivity).
    assert (Hpc2 : add_vec_int (add_vec_int pc0L 6) 4 = pcLS) by (vm_compute; reflexivity).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv
             #Htext Hpc Hfile Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16
             HiL0 HiL2 HiL4 HiL6 Hbra Hbs0 Hbuf Hcont".
    (* --- PREFIX: 0xccc..0xcdc --- *)
    iApply (wp_memset_prefix root_ppn E Φ m0 imm_entry shamt_l shamt_r nzimm_s0 imm8_beqz
              i_add wval_add mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              HX Hcov Hpmpp Hpteregion Halignp
              Hn0 Hbexec_add
              Hpmpcov HW_R HalignR HpalignR HalignS HpalignS
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile
                    Hi0 Hi2 Hi4 Hi6 Hi8 Hi10 Hi12 Hi14 Hi16 Hbra Hbs0 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbra Hbs0".
    iEval (rewrite Hpc1) in "Hpc".
    (* --- LOOP: 0xce0..0xce6 --- *)
    iApply (wp_memset_loop root_ppn E Φ N p e cval a1_idx a4_idx a5_idx imm_bne svpn
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte olds (dq:=dq)
              HN ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              HX Hcov Hpmpp Hpteregion Halignp
              Hbne HpcL0 Hmask_b Hvpn2b Hmvpnb Hmppnb HW_R
              Hpb_canon Hpb_vpn Hpb_ident Hpb_range Hincr Hcmp
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hext0 Hext4 Hext6
              N 0%nat m6 ltac:(reflexivity) HNge1 Hcur Hm4 Hm1
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Htext Hpc Hfile Hbuf [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile Hbuf".
    iEval (rewrite Hpc2) in "Hpc".
    (* --- SUFFIX: 0xcea..ret --- *)
    iApply (wp_memset_suffix root_ppn E Φ sp' ra0 s00 ra_idx s0_idx imm_dealloc
              (<[Regidx a5_idx := regval_into_reg (ms_addr p N)]> m6)
              mstatus0 mie_v mdv0 menvcfg0 pmpcfg0 pmpaddr00 region_pte (dq:=dq)(dqm:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              Hsuf_sp Hsuf_ra
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe
              HX Hcov Hpmpp Hpteregion Halignp Hret0 Hret1
              Hpmpcov HR_R HalignR HpalignR HalignS HpalignS
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hfile
                    HiL0 HiL2 HiL4 HiL6 Hbra Hbs0 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hbra Hbs0".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hpmpc Hpmpa Htlbinv Hpc Hbra Hbs0 Hbuf").
  Qed.

End WpMemsetS.

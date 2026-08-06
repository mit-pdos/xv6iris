(** * WeakLeafBase4.v — M4 batch 1: the WIDTH-4 M-mode LOAD/STORE shape,
       SC and at [exec_eff]

    WHAT THIS DELIVERS, AND WHY IT IS TWO HALVES.  The M-mode SC leaf library
    ([WpLoad], [WpMmodeLeafBase]) reduces [execute (LOAD …)] / [execute
    (STORE …)] at width **8 only** — [WpMmodeLeafBase.exec_execute_LOAD_8_gpr]
    and [_STORE_8_gpr].  The kernel's [lw]/[sw] (and the compressed
    [c.lw]/[c.sw]/[c.lwsp]/[c.swsp], which all decode to [LOAD …/STORE … 4])
    need the width-4 versions, and they did not exist.  So:

    - **HALF A is a NEW SC library**, the width-4 twin of that chain:
      [exec_pmaCheck_ram_load_4] / [_store_4],
      [exec_checked_mem_read_ram_load_4] / [exec_checked_mem_write_ram_store_4],
      [exec_mem_read_load_4] / [exec_mem_write_value_4],
      [exec_vmem_read_addr_4] / [exec_vmem_write_addr_4] (the [untilMT] loop),
      [exec_vmem_read_4_gpr] / [exec_vmem_write_4_gpr], and the two headline
      lemmas [exec_execute_LOAD_4_gpr] / [exec_execute_STORE_4_gpr].
      Everything width-INDEPENDENT is reused rather than re-proved:
      [RiscvFetchExec.exec_read_ram_plain_4] IS the 4-byte data read (the fetch
      path already needed exactly [read_ram Read_plain (Physaddr addr) 4
      false]), and so are [WpGpr]'s register-file leaves, [WpLoad]'s
      [exec_effectivePrivilege_load] / [exec_translateAddr_identity_load] /
      [execR_untilMT_1] / [misaligned_order_1] /
      [exec_transform_effective_address_load], their [Store] twins in
      [WpMmodeLeafBase], and [RiscvTryStep.exec_pmpCheck_machine_none].
      What is genuinely width-DEPENDENT is stated afresh here: the alignment
      premise feeding [split_misaligned _ 4], and the [autocast]/[subrange]
      identities, which at width 8 are [WpMmodeLeafBase.autocast_subrange_id]
      and [data2_id] and at width 4 are [autocast_subrange_id_4] and
      [data2_id_4].  Note the ASYMMETRY the width forces: at width 8 the
      STORE's [subrange_vec_dec vrs2 63 0] is the whole register and the
      identity says [= vrs2]; at width 4 it is a genuine TRUNCATION, so
      [autocast_subrange_id_4] can only strip the [autocast] and the stored
      value in the statement is [subrange_vec_dec vrs2 31 0].  The LOAD's
      result is likewise left in the shape the peel produces —
      [extend_value u data2], with [u] the instruction's [is_unsigned] bit
      (so the one lemma covers [lw] and [lwu] alike) and [data2] the 4-byte
      read widened into [mword (8*1*4)].

    - **HALF B is the [exec_eff] mirror** of HALF A, in the shape
      [WeakEffSkel] needs: each [execute]'s trace is exactly ONE element,

        [WEread  (AkInfo false false false) pa 4]        (LOAD)
        [WEwrite (AkInfo false false false) pa 4 <value>] (STORE)

      — [Read_plain]/[Write_plain] make the model's access kind the explicit
      plain-normal [AK_explicit {| variety := AV_plain; strength := AS_normal
      |}], and [WeakInterp.classify] of that is [AkInfo false false false]
      (CONFIRMED by peeling, not assumed).  Everything else on either path —
      the two register reads, [effectivePrivilege], [split_misaligned],
      [pmaCheck], the [within_*] probes, [translateAddr], the [untilMT]
      bookkeeping, [transform_effective_address], [get_pmlen],
      [ext_data_get_addr], [rX_bits]/[wX_bits] — is register-only and
      contributes the EMPTY trace.

    WHY THE REGISTER-ONLY PREFIX IS MIRRORED AT THE EMPTY TRACE RATHER THAN
    DETECTED.  One would like to get each of those steps for free from its SC
    lemma via [WeakEff.exec_eff_quiet_of_empty] — but that lemma can only
    conclude [quiet_trace], because a ZERO-WIDTH access is invisible to [exec]
    and so no argument over [exec] can rule one out, while the certificates
    ([WeakEff.wcert_load_gen] / [wcert_store_gen]) need [nowrite_trace], of
    which a zero-width [WEwrite] is not an instance.  That zero-width residue
    is why the empty trace is established by REPLAYING each SC script with the
    bind lemmas renamed ([RiscvExec.exec_bind_Some] → [WeakEff.exec_eff_bind_nil],
    [RiscvFetchExec.execR_bind_Some] → [WeakEffSkel.execR_eff_bind_nil], and the
    [_cat] forms on the one trace-carrying bind) and not by detection.  See
    [claude-notes/projects/weak-memory.md].

    TWO PREMISES ARE TAKEN AS HYPOTHESES in HALF B rather than proved (they are
    mirrored in a separate file; keeping them as premises decouples the two):
    the M-mode [pmpCheck] reduction and the three [within_*] MMIO-window
    probes, each in its [exec_eff] form with the empty trace, which is the
    honest shape since each is a pure register reduction.  HALF A keeps the SC
    forms ([Hpmp : forall i, … = OFF], [exec (within_clint …) = Some (false, s)]).

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a named
    lemma over a bind spine, exactly as the SC originals are. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import ExecCommon RegFile.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WpGpr WpLoad WpMmodeLeafBase.
Require Import WeakLeafEffCommon WeakLeafEff8 WeakLeafEff8s.
Import Defs.
Local Open Scope Z_scope.

Lemma exec_split_misaligned_aligned_4 (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 4 = true ->
  exec (split_misaligned vaddr 4) s = Some ((1, 4), s).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnM.
Qed.

Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (None, s).
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
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_ram_load_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load_4 addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_load_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load_4 with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section S4.
Variable a : mword 64.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.

Lemma exec_vmem_read_addr_4 :
  exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
    = Some (Ok data2, s).
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 4)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
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
        (exec_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*4)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR mrm s = Some (inr data2, s))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load_4 PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - (* cond *) apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End S4.

Section VRg4.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_4_gpr :
  exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a4), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a4) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_4 a4 v region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End VRg4.

(** The width-4 analogue of [WpMmodeLeafBase.data2_id]: writing all 32 bits of
    [v] into a zero word is a noop. *)
Lemma data2_id_4 (v : mword 32) :
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v = v.
Proof.
  apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  erewrite bv_concat_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  rewrite !bv_unsigned_N_0.
  rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
  reflexivity.
Qed.

Section ExecLoadG4.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable u : bool.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_4_gpr :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, u, 4))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value u data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, u, 4)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) u 4).
  unfold execute_LOAD.
  replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_4_gpr rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value u data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value u data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value u data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadG4.

(* ---------------------------------------------------------------------- *)
(** ** HALF A(ii): the width-4 STORE chain *)

Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (None, s).
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

Lemma exec_checked_mem_write_ram_store_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (Store Data) pbmt Machine tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_4 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_ea_4 (addr : mword 64) s :
  exec (mem_write_ea (Physaddr addr) 4 false false false) s = Some (Ok tt, s).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 4 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_checked_mem_write_ram_store_4 pbmt addr region data s Hpmp Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section SW4.
Variable a : mword 64.
Variable data : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_4 :
  exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _
        (exec_translateAddr_identity_store (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*4)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)))
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
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_4 (zero_extend' 64 (add_vec_int a (0*4))) s)).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*4-1) with 31. change (8*0*4) with 0. change (8*4) with 32.
             change (31 - 0 + 1) with 32. rewrite autocast_id.
             unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_4 PBMT_PMA (zero_extend' 64 (add_vec_int a (0*4))) region data
             (register_lookup mstatus s.(sregs)) s Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hpriv)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SW4.

Section VWg4.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_4_gpr :
  exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a4), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a4) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_4 a4 data region s Halign Hcp Hmprv Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWg4.

(** The width-4 analogue of [WpMmodeLeafBase.autocast_subrange_id].  At width 8
    the subrange is the WHOLE 64-bit register and the identity is [= d]; at
    width 4 it is a genuine truncation, so all the lemma can (and must) say is
    that the [autocast] wrapper is the identity. *)
Lemma autocast_subrange_id_4 (d : bv 64) :
  @autocast mword ((4*8-1) - 0 + 1) (8*4) _ (@subrange_vec_dec 64 d (4*8-1) 0)
  = (@subrange_vec_dec 64 d (4*8-1) 0 : mword 32).
Proof.
  change (4*8-1) with 31. change (8*4) with 32. change (31 - 0 + 1) with 32.
  apply autocast_id.
Qed.

Section ExecStoreG4.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let vw4 : mword 32 := subrange_vec_dec vrs2 (4*8-1) 0.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_4_gpr :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 4 vw4) s.(mdev)).
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
    (exec_vmem_write_4_gpr rs1 offset _ region s Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id_4.
  reflexivity.
Qed.
End ExecStoreG4.

(* ====================================================================== *)
(** ** HALF B: the [exec_eff] mirrors

    The kit — the twins of the model's own [returnM], of the two
    short-circuit connectives, and of the two bus arms (the ONLY two places
    in either chain where a trace element is born) — plus the
    width-independent leaves, including [exec_eff_split_misaligned_aligned_4],
    come from [WeakLeafEffCommon]. *)

(* ---------------------------------------------------------------------- *)
(** *** B1. The width-4 LOAD, mirrored *)

Lemma exec_eff_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram rv64d_types.Read_plain (Physaddr addr) 4 false) s
    = Some ((w, default_meta), s, [WEread (AkInfo false false false) addr 4]).
Proof.
  intros Hdev Hbytes.
  pose proof (exec_read_ram_plain_4 addr w s Hdev Hbytes) as Hsc.
  unfold read_ram in Hsc |- *. cbn match in Hsc |- *.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)) in Hsc.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  cbn beta zeta in Hsc |- *.
  unfold Defs.sail_mem_read in Hsc |- *. cbn beta zeta in Hsc |- *.
  unfold Defs.bind in Hsc |- *. cbn [Interface.iMon_bind] in Hsc |- *.
  rewrite exec_MemRead in Hsc; [| exact Hdev].
  rewrite exec_eff_MemRead; [| exact Hdev].
  cbn [Interface.ReadReq.pa Interface.ReadReq.access_kind
       ConcurrencyInterfaceTypes.Mem_read_request_pa
       ConcurrencyInterfaceTypes.Mem_read_request_access_kind] in Hsc |- *.
  match goal with
  | |- context [ read_bytes ?mm ?pp ?nn ] =>
      destruct (read_bytes mm pp nn) as [w0|] eqn:Hrb
  end; [| discriminate].
  cbn [Interface.iMon_bind] in Hsc |- *. cbn match beta iota in Hsc |- *.
  rewrite exec_returnM in Hsc. rewrite exec_eff_returnM.
  cbn match beta iota.
  match goal with
  | |- context [ classify ?ak ] =>
      replace (classify ak) with (AkInfo false false false)
        by (vm_compute; reflexivity)
  end.
  change (Z.to_N 4) with 4%N.
  injection Hsc; intros; subst; reflexivity.
Qed.

Lemma exec_eff_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (None, s, []).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_checked_mem_read_ram_load_4 (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Load Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s, [WEread (AkInfo false false false) addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_load_4 addr pbmt _ s Hmatch Halign Hread)).
      cbn match. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_readable (Physaddr addr) 4) s = Some (false, s, []))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_read_ram_plain_4 addr w s Hdev Hbytes)).
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_read_load_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Load Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_read (Load Data) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s, [WEread (AkInfo false false false) addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_load m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s
                 = Some (Ok (w, default_meta), s,
                         [WEread (AkInfo false false false) addr 4]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 4 _ _ _ _) s
                     = Some (Ok (w, default_meta), s,
                             [WEread (AkInfo false false false) addr 4]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram_load_4 with (region := region); assumption. }
      cbn match. unfold mem_read_callback.
      rewrite exec_eff_returnM. cbn [app]. reflexivity. }
  cbn [MemoryOpResult_drop_meta].
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

Section SEff4.
Variable a : mword 64.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.

Lemma exec_eff_vmem_read_addr_4 :
  exec_eff (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
    = Some (Ok data2, s, [WEread (AkInfo false false false) pa 4]).
Proof.
  unfold vmem_read_addr.
  rewrite exec_eff_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR_eff (returnR (result (mword (8 * 4)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s, [])).
  { rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
    rewrite execR_eff_liftR.
    rewrite (exec_eff_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (data2, true, 0), s,
                         [WEread (AkInfo false false false) pa 4]))
  end.
  { eapply execR_eff_untilMT_1.
    - (* measure *) reflexivity.
    - (* body *)
      cbn match.
      assert (Hass : exec_eff (assert_exp' true "loop dummy assert") s
                     = Some (@eq_refl bool true, s, [])) by reflexivity.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_eff_liftR_seq _ _ _ _ _
        (exec_eff_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*4)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR_eff (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR_eff mrm s
                       = Some (inr data2, s, [WEread (AkInfo false false false) pa 4]))
      end.
      { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
          (exec_eff_mem_read_load_4 PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             Hpmp_eff Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
        rewrite autocast_id. rewrite execR_eff_returnR.
        cbn [app]. reflexivity. }
      rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hmrm).
      cbn. reflexivity.
    - (* cond *) apply execR_eff_returnR. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. cbn [app]. reflexivity.
Qed.
End SEff4.

Section VRgEff4.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_eff_vmem_read_4_gpr :
  exec_eff (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s
    = Some (Ok data2, s, [WEread (AkInfo false false false) pa 4]).
Proof.
  unfold vmem_read. rewrite exec_eff_catch_early_return.
  assert (Hgta : exec_eff (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a4), s, [])).
  { unfold get_transformed_data_addr.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_eff_returnM. }
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Virtaddr a4) s)).
  rewrite execR_eff_liftR.
  rewrite (exec_eff_vmem_read_addr_4 a4 v region s Halign Hcp Hmprv Hpmp_eff
             Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End VRgEff4.

Section ExecLoadGEff4.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable u : bool.
Variable v : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Let data2 : mword (8*1*4) :=
  update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_eff_execute_LOAD_4_gpr :
  exec_eff (execute (LOAD (imm, Regidx rs1, Regidx rd, u, 4))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (extend_value u data2)),
            [WEread (AkInfo false false false) pa 4]).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, u, 4)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) u 4).
  unfold execute_LOAD.
  replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec_eff (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s, [])) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hass).
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
    (exec_eff_vmem_read_4_gpr rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmp_eff
       Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match beta.
  assert (Hw : exec_eff (wX_bits (Regidx rd) (extend_value u data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value u data2)), [])).
  { rewrite (exec_eff_wX_bits_gpr rd (extend_value u data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ Hw).
  rewrite exec_eff_returnM. cbn match. cbn [app]. reflexivity.
Qed.
End ExecLoadGEff4.

(* ---------------------------------------------------------------------- *)
(** *** B2. The width-4 STORE, mirrored *)

Lemma exec_eff_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec_eff (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
          [WEwrite (AkInfo false false false) addr 4 data]).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_eff_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_eff_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (None, s, []).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_checked_mem_write_ram_store_4 (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (data : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Store Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  exec_eff (checked_mem_write (Physaddr addr) 4 data (Store Data) pbmt Machine
              tt false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
            [WEwrite (AkInfo false false false) addr 4 data]).
Proof.
  intros Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp_eff).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_eff_returnM. }
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_writable (Physaddr addr) 4) s = Some (false, s, []))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_write_ram_plain_4 addr data s Hdev)).
  reflexivity.
Qed.

Lemma exec_eff_mem_write_ea_4 (addr : mword 64) s :
  exec_eff (mem_write_ea (Physaddr addr) 4 false false false) s
    = Some (Ok tt, s, []).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_mem_write_value_4 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Store Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_write_value (Physaddr addr) 4 data (Store Data) pbmt
              false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
            [WEwrite (AkInfo false false false) addr 4 data]).
Proof.
  intros Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_checked_mem_write_ram_store_4 pbmt addr region data s
               Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. reflexivity.
Qed.

Section SWeff4.
Variable a : mword 64.
Variable data : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 4)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_vmem_write_addr_4 :
  exec_eff (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev),
            [WEwrite (AkInfo false false false) pa 4 data]).
Proof.
  unfold vmem_write_addr.
  rewrite exec_eff_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR_eff (returnR (result bool ExecutionResult) tt >>
                              liftR (split_misaligned (Virtaddr a) 4)) s
                   = Some (inr (1, 4), s, [])).
  { rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
    rewrite execR_eff_liftR.
    rewrite (exec_eff_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true),
                         MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev),
                         [WEwrite (AkInfo false false false) pa 4 data]))
  end.
  { eapply execR_eff_untilMT_1.
    - reflexivity.
    - (* body, vars = (false, 0, true) *)
      cbn match.
      assert (Hass : exec_eff (assert_exp' true "loop dummy assert") s
                     = Some (@eq_refl bool true, s, [])) by reflexivity.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_eff_liftR_seq _ _ _ _ _
        (exec_eff_translateAddr_identity_store
           (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*4)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      assert (Hsc : exec_eff (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s, [])) by reflexivity.
      assert (Hscm : execR_eff (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s
                     = Some (inr tt, s, []))
        by (rewrite execR_eff_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR_eff (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true,
                                   MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev),
                                   [WEwrite (AkInfo false false false) pa 4 data]))
      end.
      { match goal with
        | |- execR_eff (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_eff_bind0_nil _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR_eff (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR_eff B ss = R)
        end.
        rewrite (execR_eff_liftR_seq _ _ _ _ _
          (exec_eff_mem_write_ea_4 (zero_extend' 64 (add_vec_int a (0*4))) s)).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 4 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*4-1) with 31. change (8*0*4) with 0. change (8*4) with 32.
             change (31 - 0 + 1) with 32. rewrite autocast_id.
             unfold subrange_vec_dec. change (31 - 0 + 1) with 32. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        rewrite (execR_eff_liftR_cat _ _ _ _ _ _
          (exec_eff_mem_write_value_4 PBMT_PMA (zero_extend' 64 (add_vec_int a (0*4)))
             region data (register_lookup mstatus s.(sregs)) s Hpmp_eff Hmatch Hpalign
             Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hpriv)).
        cbn match.
        rewrite execR_eff_returnR. rewrite ?app_nil_r. reflexivity. }
      rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hwrloop).
      cbn.
      rewrite ?app_nil_r. reflexivity.
    - apply execR_eff_returnR. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu).
  cbn. rewrite ?app_nil_r. reflexivity.
Qed.
End SWeff4.

Section VWgeff4.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 32.
Variable region : PMA_Region.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_vmem_write_4_gpr :
  exec_eff (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) pa 4 data) s.(mdev),
            [WEwrite (AkInfo false false false) pa 4 data]).
Proof.
  unfold vmem_write. rewrite exec_eff_catch_early_return.
  assert (Hgta : exec_eff (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a4), s, [])).
  { unfold get_transformed_data_addr.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_eff_returnM. }
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Virtaddr a4) s)).
  rewrite execR_eff_liftR.
  rewrite (exec_eff_vmem_write_addr_4 a4 data region s Halign Hcp Hmprv Hpmp_eff
             Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgeff4.

Section ExecStoreGeff4.
Variable rs2 rs1 : mword 5.
Variable imm : mword 12.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let vw4 : mword 32 := subrange_vec_dec vrs2 (4*8-1) 0.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a4 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a4 (0 * 4)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a4) 4 = true.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_execute_STORE_4_gpr :
  exec_eff (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
    = Some (RETIRE_SUCCESS,
            MState s.(sregs) (write_bytes s.(mem) pa 4 vw4) s.(mdev),
            [WEwrite (AkInfo false false false) pa 4 vw4]).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
  unfold execute_STORE.
  replace (4 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec_eff (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s, [])) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hass).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
    (exec_eff_vmem_write_4_gpr rs1 offset _ region s Hcp Hmprv Hpmm Halign
       Hpmp_eff Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_eff_returnM _ _).
  cbn match.
  rewrite autocast_subrange_id_4.
  cbn [app]. reflexivity.
Qed.
End ExecStoreGeff4.

(* ====================================================================== *)
(** ** Soundness checks *)

Print Assumptions exec_execute_LOAD_4_gpr.
Print Assumptions exec_execute_STORE_4_gpr.
Print Assumptions exec_eff_execute_LOAD_4_gpr.
Print Assumptions exec_eff_execute_STORE_4_gpr.

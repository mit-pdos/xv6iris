(** * WeakLeafAmo4.v — M4 batch 1: [amoswap.w.aq] at width 4, M-mode,
      the SC lemma AND its [exec_eff] mirror

    WHAT THIS IS.  This is THE LOCK INSTRUCTION: xv6's [acquire()] spells its
    test-and-set as [amoswap.w.aq], i.e. [AMO (AMOSWAP, aq:=true, rl:=false,
    rs2, rs1, width:=4, rd)].  M4 batch 1 needs both halves of it at M-mode
    (translation is the identity — [Bare] — and [pmpCheck] is granted by
    unlocked / all-OFF entries rather than by a page-table walk):

      HALF A, §§1–4, is a **NEW SC LEMMA**, [exec_execute_AMOSWAP_4_gpr].  The
      tree had only S-flavoured and U-flavoured AMO chains
      ([WpSmodePtLock.exec_execute_AMOSWAP_4_gpr_S_walk_pt] over
      [WpAmo]'s Supervisor stack, and [UserMemArms]' U-mode arms); there was
      no M-mode [exec_execute_AMOSWAP_4_gpr] anywhere.  §§1–3 are the
      Machine-privilege clones of [WpAmo]'s [Atomic (AMOSWAP, Data, Data)]
      chain — the privilege-independent leaves ([exec_pmaCheck_ram_amo_4],
      [exec_read_ram_resacq_4], [exec_write_ram_cond_4],
      [exec_mem_write_ea_amo_4], [exec_is_shadow_stack_amo]) are REUSED
      verbatim from [WpAmo] rather than cloned.

      HALF B, §§5–7, is the [exec_eff] mirror, [exec_eff_execute_AMOSWAP_4_gpr],
      whose trace is exactly TWO ADJACENT elements — the read then the write.

    ===================================================================
    THE TWO ACCESS KINDS, READ OFF THE MODEL (NOT GUESSED)
    ===================================================================

    [execute_AMO] (rv64d.v:40350) issues its read as
    [mem_read access pbmt addr width aq (aq && rl) true] and its write as
    [mem_write_value addr width … (aq && rl) rl true].  At [aq = true],
    [rl = false] that is [(aq, rl, res) = (true, false, true)] for the read
    and [(aq, rl, con) = (false, false, true)] for the write.  Hence:

      READ.  [read_kind_of_flags true false true = Read_RISCV_reserved_acquire]
             (**rv64d.v:22529**), and [read_ram]'s [Read_RISCV_reserved_acquire]
             arm (**rv64d.v:6162–6165**) builds
             [AK_explicit {| variety := AV_exclusive;
                             strength := AS_rel_or_acq |}].
             [WeakInterp.classify] (WeakInterp.v:248) of that is
             [AkInfo false (av_latest AV_exclusive) (as_sync AS_rel_or_acq)]
             = **[AkInfo false true true]**.
             So **[ak_coh = false] and [ak_sync = TRUE]** — the model DOES emit
             an acquire-flavoured access kind for the [.aq], which is exactly
             what [WeakCert.wcert_amo_aq] / [WeakEff.wcert_amo_aq_gen] demand
             of the READ ([ak_coh aka = false], [ak_sync aka = true]).  The
             acquire certificate applies; no model finding to report against.

      WRITE. [write_kind_of_flags false false true = Write_RISCV_conditional]
             (**rv64d.v:22549**), and [write_ram]'s [Write_RISCV_conditional]
             arm (**rv64d.v:6108–6111**) builds
             [AK_explicit {| variety := AV_exclusive;
                             strength := AS_normal |}], whose [classify] is
             **[AkInfo false true false]** — exclusive (latest) but NOT
             synchronising.  That is correct and harmless: the certificate
             constrains only the READ's kind, the write's [ak_sync] enters
             only through [store_post_run_coh], which is monotone in it.

    ===================================================================
    WHY THE REGISTER-ONLY PREFIX IS MIRRORED, NOT DETECTED
    ===================================================================

    Every step of the [execute] outside the two memory operations — the width
    assert, [get_transformed_data_addr], [transform_effective_address],
    [translateAddr] at [Bare], [rX_bits], [mem_write_ea], the [and_boolM] CAS
    guard, [wX_bits] — is REGISTER-ONLY, so each of its [exec_eff] facts
    carries the EMPTY trace and each SC script replays verbatim under the name
    swap ([RiscvExec.exec_bind_Some] -> [WeakEff.exec_eff_bind_nil],
    [RiscvFetchExec.execR_bind_Some] -> [WeakEffSkel.execR_eff_bind_nil], …).
    One might hope to skip the replay with [WeakEff.exec_eff_quiet_of_empty] —
    but that lemma concludes only [quiet_trace], which ADMITS a zero-width
    access (invisible to [exec], so no argument over [exec] can rule one out),
    while [WeakEff.wcert_amo_aq_gen] needs [nowrite_trace] of the surrounding
    [pre]/[post].  A zero-width [WEwrite] is not [weff_nowrite].  So the
    honest premise is the EMPTY trace, produced by replay.

    ===================================================================
    WHAT IS TAKEN AS A HYPOTHESIS
    ===================================================================

    In the SC section the PMP grant is the M-mode all-OFF premise, exactly as
    in [WpMmodeLeafBase]'s [Section ExecStoreG] (l.883).  In the [exec_eff]
    section that premise is replaced by the abstract
    [Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4
                            (Atomic (AMOSWAP, Data, Data)) Machine) s
                = Some (None, s, [])]
    (dischargeable by [WeakPmpEff.exec_eff_pmpCheck_machine_none]), and the
    four MMIO-window probes are taken in their [exec_eff] form with the empty
    trace.  Nothing here reduces a model function by computation: every step
    is a named lemma over a bind spine, as the SC originals are. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: every
   space-separated [rewrite a b c] below is the ssreflect form, as in the SC
   originals this file mirrors.  There is no Iris in this file. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import ExecCommon.
Require Import WpGpr WpLoad WpMmodeLeafBase WpAmo.
Require Import WeakLeafEffCommon.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** HALF A — THE SC LEMMA                                              *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(** *** 1. The M-mode privilege leaves of the AMO chain

    [WpAmo]'s [_S] lemmas at [Machine].  [effectivePrivilege] and
    [translationMode] make the effective privilege [Machine] and the
    translation [Bare]; [is_pmm_applicable]'s [or_boolM] short-circuits on
    [Machine = Machine] (so, unlike the Supervisor version, no [mstatus.MXR]
    premise is needed) and [get_pmm Machine] reads [mseccfg]. *)

Lemma exec_effectivePrivilege_amo_M (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Atomic (AMOSWAP, Data, Data)) m Machine) s = Some (Machine, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_translateAddr_identity_amo_M (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_amo_M _ s Hmprv)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_amo s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind. cbn match. reflexivity.
Qed.

Lemma exec_is_pmm_applicable_amo_M s :
  exec (is_pmm_applicable (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (true, s).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (InstructionFetch tt)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Load PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Store PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
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

Lemma exec_get_pmlen_amo_M s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (0, s).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_amo_M s)).
  cbn match.
  assert (Hgp : exec (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_amo_M (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_M _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_amo_M s Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 2. The M-mode memory operations of the AMO

    [WpAmo]'s [exec_checked_mem_read_ram_amo_4_S] / [_mem_read_] /
    [_checked_mem_write_] / [_mem_write_value_] with the Supervisor PMP walk
    replaced by the ABSTRACT [pmpCheck] fact (which at M-mode comes from
    [RiscvTryStep.exec_pmpCheck_machine_none], i.e. from unlocked entries),
    and [Supervisor] replaced by [Machine].  The [read_ram] /[write_ram]
    leaves, the PMA check and [mem_write_ea] are privilege-independent and are
    reused from [WpAmo] verbatim. *)

Lemma exec_checked_mem_read_ram_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Atomic (AMOSWAP, Data, Data)) pbmt Machine (Physaddr addr) 4
          true false true false) s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                (exec_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (read_kind_of_flags _ _ _) s
                 = Some (rv64d_types.Read_RISCV_reserved_acquire, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_resacq_4 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (Atomic (AMOSWAP, Data, Data)) pbmt (Physaddr addr) 4 true false true)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_M m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta.
      rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_amo_4_M with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_ram_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt Machine
          tt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _
                (exec_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
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
            (_ : exec (write_kind_of_flags false false true) s
                 = Some (rv64d_types.Write_RISCV_conditional, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_cond_4 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  exec (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (None, s) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_write_value (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt
          false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_M m s Hmprv)).
  unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_checked_mem_write_ram_amo_4_M pbmt addr region data s
               Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 3. THE SC DELIVERABLE: [amoswap.w.aq] at M-mode, width 4

    Base from [rs1] (offset zero — the AMO has no immediate), value from
    [rs2], destination [rd].  The successor writes BOTH memory (the truncated,
    re-sign-extended [rs2] value, 4 bytes at [pa]) AND the register file ([rd]
    := the OLD word, sign-extended to 64).  Hypothesis style: [WpMmodeLeafBase]'s
    [Section ExecStoreG] (l.883). *)

Section ExecAmoM4.
Variable rs2 rs1 rd : mword 5.
Variable region : PMA_Region.
Variable w : mword 32.
Variable s : mstate.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (zeros' 64).
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 a8.
Let storeval : mword 32 :=
  sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs)))
                  = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4
                    = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hamo : pma_allows_atomic_op
  ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hhr : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hhw : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
  s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

Lemma exec_execute_AMOSWAP_4_gpr :
  exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval) s.(mdev))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg
                     (sign_extend' 64
                        (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))).
Proof.
  assert (Hpmpchk : exec (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
                    = Some (None, s))
    by (apply exec_pmpCheck_machine_none; exact Hpmp).
  change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
    with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
  unfold execute_AMO. cbn zeta.
  rewrite exec_catch_early_return.
  assert (Hae : exec (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2))
                        "extensions/A/zaamo_insts.sail:73.32-73.33") s = Some (eq_refl, s))
    by (unfold assert_exp'; cbn match; apply exec_returnm).
  rewrite (execR_liftR_seq _ _ _ _ _ Hae).
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64)
                         (Atomic (AMOSWAP, Data, Data)) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_ext_data_get_addr_gpr rs1 (zeros' 64) (Atomic (AMOSWAP, Data, Data)) 4 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_transform_effective_address_amo_M ea s Hcp Hmprv Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translateAddr_identity_amo_M a8 s Hcp Hmprv)).
  cbn [bits_of_virtaddr].
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s)).
  cbn beta match.
  replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
  cbv iota.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn beta. rewrite execR_returnR. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea_amo_4 pa s Hpalign)).
  cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_read_amo_4_M PBMT_PMA pa region w (register_lookup mstatus s.(sregs)) s
               Hpmpchk Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev
               (fun j Hj => Hbytes j Hj) eq_refl Hmprv Hcp)).
  cbn match. rewrite execR_returnR. cbn match.
  cbn zeta. cbn match.
  replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
  unfold and_boolM.
  rewrite execR_bind.
  rewrite execR_bind. rewrite execR_returnR. cbn match. cbv iota.
  rewrite execR_returnR. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _
            (exec_mem_write_value_amo_4_M PBMT_PMA pa region _
               (register_lookup mstatus s.(sregs)) s
               Hpmpchk Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv Hcp)).
  cbn match.
  match goal with |- context[execR _ ?st] => set (s_m := st) end.
  assert (HwX : execR (Defs.liftR (wX_bits (Regidx rd)
                   (sign_extend' 64 (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8))))
                 : Defs.monadR ExecutionResult exception unit) s_m
                = Some (inr tt,
                        set_reg s_m (R_bitvector_64 (gpr_of_Z (uint rd)))
                          (regval_into_reg
                             (sign_extend' 64
                                (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))))).
  { rewrite execR_liftR.
    rewrite (exec_wX_bits_gpr rd _ s_m).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ HwX).
  rewrite execR_returnR.
  cbn.
  reflexivity.
Qed.
End ExecAmoM4.

(* ====================================================================== *)
(** ** HALF B — THE [exec_eff] MIRROR                                     *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(** *** 4. The kit: [WeakLeafEffCommon]

    [WeakEff] supplies [exec_eff_bind_nil] / [_bind0_nil] / [_bind_Some] /
    [_returnm] / [_read_reg] / [_write_reg]; the twins of the model's own
    [returnM] (as opposed to [Defs.returnm] — it needs its own lemma so a
    SYNTACTIC rewrite matches the [returnM …] appearing in model terms), of
    the two short-circuit boolean connectives, of the two one-bus-step memory
    arms, of [WpGpr]'s register-file leaves and of [translationMode] at
    Machine are [WeakLeafEffCommon]'s — none of them is about the AMO, the
    width or the access kind. *)

(** [RiscvFetchExec.exec_MemRead]'s twin: on a RAM address the outcome exposes
    the [read_bytes] match AND emits the read's [WEread] in front of the
    continuation's trace.  This is where the AMO's FIRST trace element is born. *)
(** [RiscvFetchExec.exec_MemWrite]'s twin — where the SECOND trace element is
    born. *)
(* ---------------------------------------------------------------------- *)
(** *** 5. THE TWO MEMORY-TOUCHING STEPS, where the two trace elements are born

    [read_ram Read_RISCV_reserved_acquire] emits
    [WEread (AkInfo false true true) addr 4] — NOT coherent, latest (exclusive),
    and SYNCHRONISING, because the [.aq] makes the model's access kind
    [AK_explicit {| AV_exclusive; AS_rel_or_acq |}] (rv64d.v:6162–6165, reached
    from [read_kind_of_flags true false true], rv64d.v:22529).  That [ak_sync =
    true] is exactly what [WeakCert.wcert_amo_aq] requires of the read.

    [write_ram Write_RISCV_conditional] emits
    [WEwrite (AkInfo false true false) addr 4 data] — exclusive but NOT
    synchronising ([AK_explicit {| AV_exclusive; AS_normal |}],
    rv64d.v:6108–6111, from [write_kind_of_flags false false true],
    rv64d.v:22549). *)

Lemma exec_eff_read_ram_resacq_4 (addr : mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram rv64d_types.Read_RISCV_reserved_acquire (Physaddr addr) 4 false) s
    = Some ((w, default_meta), s, [WEread (AkInfo false true true) addr 4]).
Proof.
  intros Hdev Hbytes.
  pose proof (exec_read_ram_resacq_4 addr w s Hdev Hbytes) as Hsc.
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
  | |- context [ classify ?a ] =>
      replace (classify a) with (AkInfo false true true)
        by (vm_compute; reflexivity)
  end.
  change (Z.to_N 4) with 4%N.
  injection Hsc; intros; subst; reflexivity.
Qed.

Lemma exec_eff_write_ram_cond_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec_eff (write_ram rv64d_types.Write_RISCV_conditional (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
          [WEwrite (AkInfo false true false) addr 4 data]).
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

(* ---------------------------------------------------------------------- *)
(** *** 6. The register-only checks, mirrored at the empty trace            *)

Lemma exec_eff_effectivePrivilege_amo_M (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec_eff (effectivePrivilege (Atomic (AMOSWAP, Data, Data)) m Machine) s
    = Some (Machine, s, []).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_eff_returnm.
Qed.

Lemma exec_eff_is_shadow_stack_amo s :
  exec_eff (is_shadow_stack_access (Atomic (AMOSWAP, Data, Data))) s = Some (false, s, []).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_eff_returnM. Qed.

Lemma exec_eff_translateAddr_identity_amo_M (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec_eff (translateAddr (Virtaddr a) (Atomic (AMOSWAP, Data, Data))) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s, []).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_effectivePrivilege_amo_M _ s Hmprv)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_translationMode_M s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_is_shadow_stack_amo s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_eff_bind_eq. cbn match. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma exec_eff_is_pmm_applicable_amo_M s :
  exec_eff (is_pmm_applicable (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (true, s, []).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (InstructionFetch tt)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Load PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Atomic (AMOSWAP, Data, Data)) (Store PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec_eff orb s = Some (true, s, []))
  end.
  { rewrite (exec_eff_or_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity). reflexivity. }
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_eff_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_eff_get_pmlen_amo_M s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec_eff (get_pmlen (Atomic (AMOSWAP, Data, Data)) Machine) s = Some (0, s, []).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_is_pmm_applicable_amo_M s)).
  cbn match.
  assert (Hgp : exec_eff (get_pmm Machine) s
          = Some (pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))), s, [])).
  { unfold get_pmm.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mseccfg s)).
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_transform_effective_address_amo_M (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec_eff (transform_effective_address (Virtaddr ea) (Atomic (AMOSWAP, Data, Data))) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s, []).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_amo_M _ s Hmprv)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_get_pmlen_amo_M s Hpmm)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_pmaCheck_ram_amo_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec_eff (pmaCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) pbmt true) s
    = Some (None, s, []).
Proof.
  intros Hmatch Halign Hread Hwrite Hamo.
  unfold pmaCheck.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread, Hwrite, Hamo |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM None s)).
  cbn match beta.
  match goal with |- exec_eff (Defs.bind ?m ?k) s = _ =>
    assert (Hass : exec_eff m s
            = Some (andb (PMA_readable (override_PMA rattr pbmt))
                      (andb (PMA_writable (override_PMA rattr pbmt))
                         (pma_allows_atomic_op (PMA_atomic_support (override_PMA rattr pbmt))
                            AMOSWAP 4)), s, []))
      by (rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnm eq_refl s));
          apply exec_eff_returnM);
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hass)
  end.
  cbn beta.
  rewrite Hread Hwrite Hamo. cbn [andb]. cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_mem_write_ea_amo_4 (addr : mword 64) s :
  is_aligned_paddr (Physaddr addr) 4 = true ->
  exec_eff (mem_write_ea (Physaddr addr) 4 false false true) s = Some (Ok tt, s, []).
Proof.
  intro Halign. unfold mem_write_ea.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (write_kind_of_flags false false true) s
                 = Some (rv64d_types.Write_RISCV_conditional, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  apply exec_eff_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 7. [mem_read] and [mem_write_value] at [exec_eff]

    The PMP grant arrives as the abstract [exec_eff] fact (empty trace); every
    check above the [read_ram]/[write_ram] leaf is register-only, so
    [WeakEff.exec_eff_bind_nil] carries each one through unchanged and only the
    leaf's bind needs the concatenating [_bind_Some]. *)

Lemma exec_eff_checked_mem_read_ram_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (Atomic (AMOSWAP, Data, Data)) pbmt Machine (Physaddr addr) 4
              true false true false) s
    = Some (Ok (w, default_meta), s, [WEread (AkInfo false true true) addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
      cbn match. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_readable (Physaddr addr) 4) s = Some (false, s, []))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (read_kind_of_flags _ _ _) s
                 = Some (rv64d_types.Read_RISCV_reserved_acquire, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _ (exec_eff_read_ram_resacq_4 addr w s Hdev Hbytes)).
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_read_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_read (Atomic (AMOSWAP, Data, Data)) pbmt (Physaddr addr) 4 true false true) s
    = Some (Ok w, s, [WEread (AkInfo false true true) addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_amo_M m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s
                 = Some (Ok (w, default_meta), s,
                         [WEread (AkInfo false true true) addr 4]))).
  2:{ unfold mem_read_priv_meta.
      rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 4 _ _ _ _) s
                     = Some (Ok (w, default_meta), s,
                             [WEread (AkInfo false true true) addr 4]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram_amo_4_M with (region := region); assumption. }
      cbn match. unfold mem_read_callback.
      rewrite exec_eff_returnM. cbn [app]. reflexivity. }
  cbn [MemoryOpResult_drop_meta].
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_checked_mem_write_ram_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  exec_eff (checked_mem_write (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt Machine
              tt false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
            [WEwrite (AkInfo false true false) addr 4 data]).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_amo_4 addr pbmt region s Hmatch Halign Hread Hwrite Hamo)).
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
            (_ : exec_eff (write_kind_of_flags false false true) s
                 = Some (rv64d_types.Write_RISCV_conditional, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _ (exec_eff_write_ram_cond_4 addr data s Hdev)).
  reflexivity.
Qed.

Lemma exec_eff_mem_write_value_amo_4_M (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  pma_allows_atomic_op ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support))
    AMOSWAP 4 = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_write_value (Physaddr addr) 4 data (Atomic (AMOSWAP, Data, Data)) pbmt
              false false true) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev),
            [WEwrite (AkInfo false true false) addr 4 data]).
Proof.
  intros Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_amo_M m s Hmprv)).
  unfold mem_write_value_priv_meta.
  rewrite Halign. cbn [orb andb negb Riscv.rv64d.not].
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_checked_mem_write_ram_amo_4_M pbmt addr region data s
               Hpmp Hmatch Halign Hread Hwrite Hamo Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. reflexivity.
Qed.

(** The instruction's tail after the write: the [rd] write-back and the
    [RETIRE_SUCCESS], both register-only.  Kept as a standalone lemma over an
    ARBITRARY post-write state so the top-level script never has to name the
    post-write state (a [set]-based naming would grab the wrong occurrence once
    the read's trace has turned the goal into a [match]). *)
Lemma exec_eff_amo_writeback (rd : mword 5) (v : mword 64) (st : mstate) :
  uint rd <> 0 ->
  execR_eff (Defs.bind0 (Defs.liftR (wX_bits (Regidx rd) v)
                          : Defs.monadR ExecutionResult exception unit)
                        (Defs.returnR ExecutionResult RETIRE_SUCCESS)) st
  = Some (inr RETIRE_SUCCESS,
          set_reg st (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v), []).
Proof.
  intro Hrd.
  assert (HwX : execR_eff (Defs.liftR (wX_bits (Regidx rd) v)
                           : Defs.monadR ExecutionResult exception unit) st
                = Some (inr tt,
                        set_reg st (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v), [])).
  { rewrite execR_eff_liftR. rewrite (exec_eff_wX_bits_gpr rd v st).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (execR_eff_bind0_nil _ _ _ _ HwX).
  apply execR_eff_returnR.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 8. THE DELIVERABLE: [amoswap.w.aq] at [exec_eff], TWO ADJACENT EVENTS

    Same [Variable]s / [Let]s as §3's SC section; the SC [Hpmp] (all entries
    OFF) is replaced by the abstract [exec_eff] PMP fact and the four MMIO
    probes by their [exec_eff] forms, each at the empty trace.  The conclusion's
    trace is
      [[WEread (AkInfo false true true) pa 4;
        WEwrite (AkInfo false true false) pa 4 storeval]]
    — the acquire-flavoured read of the OLD word immediately followed by the
    exclusive write of the NEW one, with nothing between them, which is exactly
    the shape [WeakEff.wcert_amo_aq_gen] consumes. *)

Section ExecAmoM4Eff.
Variable rs2 rs1 rd : mword 5.
Variable region : PMA_Region.
Variable w : mword 32.
Variable s : mstate.
Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                  (zeros' 64).
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 a8.
Let storeval : mword 32 :=
  sign_extend' (Z.mul 8 (__id 4)) (trunc (Z.mul (__id 4) 8) vrs2).
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs)))
                  = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 4 = true.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 4 (Atomic (AMOSWAP, Data, Data)) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4
                    = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hamo : pma_allows_atomic_op
  ((override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_atomic_support)) AMOSWAP 4 = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hhr : exec_eff (within_htif_readable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hhw : exec_eff (within_htif_writable (Physaddr pa) 4) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
  s.(mem) !! (pa_add pa j) = Some (nth_byte w j).

Lemma exec_eff_execute_AMOSWAP_4_gpr :
  exec_eff (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s
  = Some (RETIRE_SUCCESS,
          set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval) s.(mdev))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg
                     (sign_extend' 64
                        (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))),
          [WEread (AkInfo false true true) pa 4;
           WEwrite (AkInfo false true false) pa 4 storeval]).
Proof.
  change (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)))
    with (execute_AMO AMOSWAP true false (Regidx rs2) (Regidx rs1) 4 (Regidx rd)).
  unfold execute_AMO. cbn zeta.
  rewrite exec_eff_catch_early_return.
  assert (Hae : exec_eff (Defs.assert_exp' (Z.leb 4 (Z.mul xlen_bytes 2))
                            "extensions/A/zaamo_insts.sail:73.32-73.33") s
                = Some (eq_refl, s, []))
    by (unfold assert_exp'; cbn match; apply exec_eff_returnm).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hae).
  assert (Hgta : exec_eff (get_transformed_data_addr (Regidx rs1) (zeros' 64)
                             (Atomic (AMOSWAP, Data, Data)) 4) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s, [])).
  { unfold get_transformed_data_addr.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_ext_data_get_addr_gpr rs1 (zeros' 64)
                 (Atomic (AMOSWAP, Data, Data)) 4 s)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_transform_effective_address_amo_M ea s Hcp Hmprv Hpmm)).
    apply exec_eff_returnM. }
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Virtaddr a8) s)).
  rewrite Halign. cbn [Riscv.rv64d.not negb]. cbv iota.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
            (exec_eff_translateAddr_identity_amo_M a8 s Hcp Hmprv)).
  cbn [bits_of_virtaddr].
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Physaddr pa, PBMT_PMA) s)).
  cbn beta match.
  replace (Z.leb 4 xlen_bytes) with true by (vm_compute; reflexivity).
  cbv iota.
  (* rs2's value: register-only, empty trace *)
  match goal with
  | |- context [ Defs.bind (Defs.liftR (rX_bits (Regidx rs2))) ?k ] =>
      assert (Hrs2 : execR_eff (Defs.bind (Defs.liftR (rX_bits (Regidx rs2))) k) s
                     = Some (inr (trunc (Z.mul (__id 4) 8) vrs2), s, []))
  end.
  { rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
    apply execR_eff_returnR. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hrs2).
  cbn beta.
  (* mem_write_ea: no trace (it only picks the write kind) *)
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_mem_write_ea_amo_4 pa s Hpalign)).
  cbn match.
  (* THE READ: the first trace element *)
  match goal with
  | |- context [ Defs.bind (Defs.liftR (mem_read ?acc ?pb ?ad ?wd ?aq ?rl ?res)) ?k ] =>
      assert (Hload : execR_eff (Defs.bind (Defs.liftR (mem_read acc pb ad wd aq rl res)) k) s
                      = Some (inr (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)),
                              s, [WEread (AkInfo false true true) pa 4]))
  end.
  { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
              (exec_eff_mem_read_amo_4_M PBMT_PMA pa region w
                 (register_lookup mstatus s.(sregs)) s
                 Hpmp_eff Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhr Hdev
                 (fun j Hj => Hbytes j Hj) eq_refl Hmprv Hcp)).
    cbn match. rewrite execR_eff_returnR. reflexivity. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hload).
  cbn zeta. cbn match.
  (* the CAS guard short-circuits: [generic_eq AMOSWAP AMOCAS = false] *)
  match goal with
  | |- context [ and_boolM ?l ?r ] =>
      assert (Hguard : execR_eff (and_boolM l r) s = Some (inr false, s, []))
  end.
  { replace (generic_eq AMOSWAP AMOCAS) with false by (vm_compute; reflexivity).
    unfold and_boolM.
    rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR false s)).
    apply execR_eff_returnR. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hguard).
  cbv iota.
  (* THE WRITE: the second trace element, immediately after the read *)
  match goal with
  | |- context [ Defs.bind (Defs.liftR (mem_write_value ?ad ?wd ?dt ?acc ?pb ?x ?y ?z)) ?k ] =>
      assert (Hstore : execR_eff
                (Defs.bind (Defs.liftR (mem_write_value ad wd dt acc pb x y z)) k) s
              = Some (inr RETIRE_SUCCESS,
                      set_reg (MState s.(sregs) (write_bytes s.(mem) pa 4 storeval) s.(mdev))
                              (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg
                                 (sign_extend' 64
                                    (autocast (T := mword) (w : mword (8 * 4)) : mword (4 * 8)))),
                      [WEwrite (AkInfo false true false) pa 4 storeval]))
  end.
  { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
              (exec_eff_mem_write_value_amo_4_M PBMT_PMA pa region _
                 (register_lookup mstatus s.(sregs)) s
                 Hpmp_eff Hmatch Hpalign Hread Hwrite Hamo Hc Hsig Hhw Hdev eq_refl Hmprv Hcp)).
    cbn beta match.
    rewrite (exec_eff_amo_writeback rd _ _ Hrd).
    reflexivity. }
  (* the write's bind is the LAST expression of the [execute], so its fact goes
     straight into the read's [_bind_cat] residue: the two elements concatenate
     into the adjacent pair. *)
  rewrite Hstore.
  reflexivity.
Qed.
End ExecAmoM4Eff.

(* ====================================================================== *)
(** ** 9. Soundness check

    Both headline lemmas rest on nothing but the Sail model's own platform
    hook [plat_term_write] (an [Axiom] of the generated [Riscv.rv64d]). *)

Print Assumptions exec_execute_AMOSWAP_4_gpr.

Print Assumptions exec_eff_execute_AMOSWAP_4_gpr.

(** * WeakLeafEff8s.v — M4 batch 1: the 8-byte M-mode STORE at [exec_eff]

    WHAT THIS IS.  [WeakEffSkel] reduced a weak-memory leaf's whole remaining
    obligation to TWO [exec_eff] facts — the fetch's and the [execute]'s —
    joined by [WeakEffSkel.exec_eff_riscv_step_base], whose conclusion's trace
    is exactly [es_f ++ es_x].  THIS FILE IS THE SECOND OF THOSE TWO, for the
    8-byte M-mode STORE shape: the [exec_eff] mirror of
    [WpMmodeLeafBase.exec_execute_STORE_8_gpr], whose trace is ONE element,

        [WEwrite (AkInfo false false false) pa 8 vrs2]

    — the data write, and nothing else.  Every other step of the [execute] (the
    two register reads, the address transform, the privilege and PMP/PMA
    checks, the misalignment split, the [untilMT] loop's bookkeeping) is
    register-only and contributes the empty trace, which is the whole content
    of the statement.

    WHY THE REGISTER-ONLY PREFIX IS MIRRORED RATHER THAN DETECTED.
    [WeakEff.exec_eff_quiet_of_empty] would give each of those steps for free
    from its SC lemma — but only up to [quiet_trace], which ADMITS a
    zero-width access (invisible to [exec]; see [WeakEff]'s header).  The
    certificate this leaf must eventually feed, [WeakEff.wcert_store_gen],
    needs [nowrite_trace] of the surroundings, and a zero-width [WEwrite] is
    not [weff_nowrite].  So the honest premise is the EMPTY trace, and the
    empty trace has to be produced by replaying the SC script with the bind
    lemmas renamed.  (See [claude-notes/projects/weak-memory.md].)

    THE METHOD IS THE NAME SWAP, and nothing else: every SC step whose
    statement is [exec m s = Some (v, s)] becomes [exec_eff m s = Some (v, s,
    [])] with an identical script under [WeakEff.exec_eff_bind_nil] /
    [_bind0_nil] and [WeakEffSkel.execR_eff_bind_nil] / [_bind0_nil] /
    [_liftR_seq]; only [exec_eff_write_ram_plain_8] and the chain textually
    above it on the path carry the one-element trace, via the [_cons] / [_cat]
    forms.  The SC chain mirrored here is, in dependency order,
    [WpMmodeLeafBase]'s [exec_write_ram_plain_8], [exec_pmaCheck_ram_store],
    [exec_checked_mem_write_ram_store], [exec_effectivePrivilege_store],
    [exec_is_shadow_stack_store], [exec_translateAddr_identity_store],
    [exec_mem_write_ea], [exec_mem_write_value_8], [exec_vmem_write_addr_8],
    [exec_is_pmm_applicable_store], [exec_get_pmlen_store],
    [exec_transform_effective_address_store], [exec_vmem_write_8_gpr] and
    [exec_execute_STORE_8_gpr], plus [WpGpr]'s [exec_rX_bits_gpr] /
    [exec_ext_data_get_addr_gpr] and [WpLoad]'s [execR_untilMT_1].  The PURE
    lemmas of that cone ([WpMmodeLeafBase.autocast_subrange_id],
    [WpLoad.misaligned_order_1]) mention no interpreter and are REUSED
    verbatim rather than mirrored.

    WHAT IS TAKEN AS A HYPOTHESIS.  The four platform checks the SC chain
    consumes as [exec] facts — the PMP walk and the three MMIO-window probes —
    are mirrored in a separate file; they enter here as [Hpmp_eff] / [Hc] /
    [Hsig] / [Hh], in exactly the shape their SC originals have with [exec]
    replaced by [exec_eff] and the empty trace attached.

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a
    named lemma over a bind spine, exactly as the SC originals are. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: every
   [rewrite a b c] and [rewrite H /=] below is the space-separated ssreflect
   form, as in the SC originals this file mirrors.  There is no Iris here. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras SailStdpp.Base RiscvLang RiscvPtsto RiscvExec RiscvFetchExec ExecCommon WpGpr RegFile RiscvModelBytes RiscvTryStep RiscvExtras WpLoad SailStdpp.TypeCasts SailStdpp.MachineWord SailStdpp.Values WpAuipc WpDecode.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WpGpr WpLoad WpMmodeLeafBase.
Require Import WeakLeafEffCommon.
Import Defs.
Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The kit, and the width-independent leaves: [WeakLeafEffCommon]

    [exec_eff_returnM] (the model's own [returnM], which is [Defs.returnm] at
    [E := exception] and must have its own lemma so a SYNTACTIC rewrite
    matches the [returnM …] appearing in model terms), the two short-circuit
    connectives, [exec_eff_MemWrite] — [RiscvFetchExec.exec_MemWrite]'s twin,
    where the [WEwrite] is born — and the leaves that are about neither the
    width nor the access ([_translationMode_M],
    [_split_misaligned_unsplit], [_split_on_page_boundary_aligned8], the
    [pma_ok_eff_peel] kit, [_rX_bits_gpr], [_ext_data_get_addr_gpr],
    [execR_eff_untilMT_1]) all live in [WeakLeafEffCommon]. *)

(* ====================================================================== *)
(** ** 1. THE ONE MEMORY-TOUCHING STEP

    [WpMmodeLeafBase.exec_write_ram_plain_8], mirrored.  This is the ONLY
    place in the whole 8-byte STORE where a trace element is born, and the
    access kind is decided here: [write_ram Write_plain] returns
    [AK_explicit {| variety := AV_plain; strength := AS_normal |}], so
    [Interface.WriteReq.access_kind req] reduces to that and
    [WeakInterp.classify] of it is [AkInfo false false false] — not coherent,
    not latest, not synchronising. *)

Lemma exec_eff_write_ram_plain_8 (addr : mword 64) (data : bv 64) s :
  dev_addr addr = false ->
  exec_eff (write_ram rv64d_types.Write_plain (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev),
          [WEwrite (AkInfo false false false) addr 8 data]).
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

(* ====================================================================== *)
(** ** 2. The register-only checks on the store path

    [exec_pmaCheck_ram_store] / [exec_effectivePrivilege_store] /
    [exec_is_shadow_stack_store] / [exec_translationMode_M] /
    [exec_split_misaligned_unsplit], each with the empty trace and the SC
    script under §0's names.  Since the sail bump [pmaCheck] answers a PLAN
    ([Ok pma_ok_aligned] for an aligned access) rather than an [option
    ExceptionType], and its body is an early-return one, so the peel is
    [WeakLeafEffCommon.pma_ok_eff_peel] — the eff twin of
    [RiscvExtras.pma_ok_peel]. *)

Lemma exec_eff_pmaCheck_ram_store (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 8 (Store Data) pbmt false) s
    = Some (Ok pma_ok_aligned, s, []).
Proof.
  intros Hmatch Halign Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_eff_peel Hmatch Hwrite (exec_eff_is_mag_applicable_store_data 8 s) Halign.
Qed.

Lemma exec_eff_effectivePrivilege_store (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec_eff (effectivePrivilege (Store Data) m Machine) s = Some (Machine, s, []).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_eff_returnm.
Qed.

Lemma exec_eff_is_shadow_stack_store s :
  exec_eff (is_shadow_stack_access (Store Data)) s = Some (false, s, []).
Proof.
  unfold is_shadow_stack_access. cbn match. apply exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 3. [checked_mem_write] and [mem_write_value]

    The first point on the path where the write's trace element is visible:
    every check above it is empty-traced, so [WeakEff.exec_eff_bind_nil]
    carries the fact through unchanged and only the final [write_ram] bind
    needs [_bind_cons].

    The PMP walk and the three MMIO-window probes arrive as PREMISES (they are
    mirrored elsewhere); the SC lemma's [Hpmp : forall i, … = OFF] is replaced
    by the [exec_eff] fact it was only ever used to produce. *)

Lemma exec_eff_checked_mem_write_ram_store (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (data : bv 64) s :
  exec_eff (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (within_clint (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 8) s = Some (false, s, []) ->
  dev_addr addr = false ->
  exec_eff (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Machine
              tt false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev),
            [WEwrite (AkInfo false false false) addr 8 data]).
Proof.
  intros Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  assert (Hcp : exec_eff (check_pma_with_pmp_priority (Store Data) pbmt Machine
                            (Physaddr addr) 8 false) s = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
    cbn match. apply exec_eff_returnM. }
  assert (Hmmio : exec_eff (within_mmio_writable (Physaddr addr) 8) s
                  = Some (false, s, [])).
  { unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  set (sw := MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
  unfold checked_mem_write. rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_split_misaligned_unsplit addr 8 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (_ : exec_eff (write_kind_of_flags false false false) s
                  = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  cbn beta.
  (* one split, at offset 0 — and the ONE trace element crosses out of it *)
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0, true), sw,
                         [WEwrite (AkInfo false false false) addr 8 data])) end.
  { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul8.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpmp_eff). cbn beta.
    cbn match.
    rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match zeta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
    rewrite autocast_id.
    change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
    rewrite subrange_full_64.
    (* the RAM write's own bind (folding the success flag) sits under the loop
       body's bind, so it has to be valued first — and it CARRIES the trace *)
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
      assert (Hwr : execR_eff (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                    = Some (inr true, sw,
                            [WEwrite (AkInfo false false false) addr 8 data])) end.
    { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
                 (exec_eff_write_ram_plain_8 addr data s Hdev)).
      cbn beta. cbn [andb]. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hwr). cbn beta zeta.
    rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_eff_returnR. cbn [app]. reflexivity.
Qed.

(** [mem_write_ea] is no longer a bare write-kind computation: it resolves the
    effective privilege, runs the PMA/PMP check, and walks the same
    one-iteration split loop as [checked_mem_write] — announcing the write
    address per split ([write_ram_ea], a state AND trace no-op).  So the lemma
    gained the region/PMP/privilege premises its SC twin
    ([WpMmodeLeafBase.exec_mem_write_ea]) gained. *)
Lemma exec_eff_mem_write_ea (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) s :
  exec_eff (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec_eff (mem_write_ea (Physaddr addr) 8 (Store Data) pbmt false false false) s
    = Some (Ok tt, s, []).
Proof.
  intros Hpmp_eff Hmatch Halign Hwrite Hcp Hmprv.
  assert (Hcpp : exec_eff (check_pma_with_pmp_priority (Store Data) pbmt Machine
                             (Physaddr addr) 8 false) s = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
    cbn match. apply exec_eff_returnM. }
  unfold mem_write_ea. rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)). cbn beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)). cbn beta.
  rewrite Hcp.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_effectivePrivilege_store (register_lookup mstatus s.(sregs)) s Hmprv)).
  cbn beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcpp). cbn beta. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_split_misaligned_unsplit addr 8 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (_ : exec_eff (write_kind_of_flags false false false) s
                  = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s = Some (inr (true, 0), s, [])) end.
  { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul8.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpmp_eff). cbn beta.
    cbn match.
    rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match zeta.
    rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_write_value_8 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 8 (Store Data) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (within_clint (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_htif_writable (Physaddr addr) 8) s = Some (false, s, []) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt
              false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev),
            [WEwrite (AkInfo false false false) addr 8 data]).
Proof.
  intros Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_store m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_checked_mem_write_ram_store pbmt addr region data s
               Hpmp_eff Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. [translateAddr] at M-mode, and the [untilMT] loop

    [exec_translateAddr_identity_store] mirrored (all register reads, so the
    empty trace), then [WpLoad.execR_untilMT_1]'s twin and the [vmem_write_addr]
    body it drives — the one point where the write's trace crosses OUT of the
    loop. *)

Lemma exec_eff_translateAddr_identity_store (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1)
    = false ->
  exec_eff (translateAddr (Virtaddr a) (Store Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s, []).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_effectivePrivilege_store _ s Hmprv)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_translationMode_M s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_is_shadow_stack_store s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_eff_bind_eq. cbn match. rewrite ?app_nil_r. reflexivity.
Qed.

(** [WpLoad.execR_untilMT_1] with the body's trace carried out of the loop:
    the guard and the measure step are empty-traced, so the loop's trace IS
    the body's. *)
(* [WpMmodeLeafBase.v : SW] *)
Section SWeff.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_vmem_write_addr_8 :
  exec_eff (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev),
            [WEwrite (AkInfo false false false) pa 8 data]).
Proof.
  set (sw := MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
  unfold vmem_write_addr.
  rewrite exec_eff_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  (* the page split: (8, 0) *)
  rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_split_on_page_boundary_aligned8 a s Halign)).
  cbn beta zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)). cbn beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_effectivePrivilege_store (register_lookup mstatus s.(sregs)) s Hmprv)).
  cbn beta.
  (* do_split_access = false: Machine-mode translation is Bare *)
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR_eff (Defs.and_boolM A B) s = Some (inr false, s, [])) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Htm : execR_eff (Defs.bind (Defs.liftR m) k1) s = Some (inr false, s, [])) end.
    { rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_translationMode_M s)). cbn beta.
      apply execR_eff_returnR. }
    rewrite (execR_eff_bind_nil _ _ _ _ _ Htm). cbn match beta.
    apply execR_eff_returnR. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hds). cbn match beta zeta.
  rewrite andb_false_r. cbn match beta.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR true s)).
  cbn beta zeta.
  (* the single full-width access *)
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_translateAddr_identity_store (bits_of_virtaddr (Virtaddr a)) s
                Hpriv Hmprv)).
  cbn [bits_of_virtaddr]. cbn match beta.
  assert (Hpaeq : zero_extend' 64 a = pa)
    by (unfold pa; cbn [bits_of_virtaddr]; rewrite avi0_mul8; reflexivity).
  rewrite Hpaeq.
  (* the store-conditional assert, then the reservation-check [if].  Both go in a
     NESTED goal: at the top level the goal is the catch_early_return wrapper's
     match, and [cbn] there reduces through [mem_write_ea] into the monad's bind
     fixpoint (the over-reduction trap the SC proof also has to dodge). *)
  match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
    assert (Hsc : execR_eff (Defs.liftR asrt
                             : Defs.monadR (result bool ExecutionResult) exception unit) s
                  = Some (inr tt, s, []))
      by (rewrite execR_eff_liftR; reflexivity) end.
  match goal with
  | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
      assert (Hwrloop : execR_eff (Defs.bind0 (Defs.liftR asrt) Nbody) s
                        = Some (inr true, sw,
                                [WEwrite (AkInfo false false false) pa 8 data]))
  end.
  { match goal with |- execR_eff (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody) end.
    rewrite (execR_eff_bind0_nil _ _ _ _ Hsc).
    unfold NN; clear NN.
    (* res = false, so [andb false _] is false by conversion: take the else *)
    match goal with
    | |- execR_eff (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
        change (execR_eff B ss = R)
    end.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (exec_eff_mem_write_ea PBMT_PMA pa region s
                  Hpmp_eff Hmatch Hpalign Hwrite Hpriv Hmprv)).
    cbn match.
    rewrite autocast_id.
    change (8 * 8 - 1) with 63.
    rewrite subrange_full_64.
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _
               (exec_eff_mem_write_value_8 PBMT_PMA pa region data
                  (register_lookup mstatus s.(sregs)) s
                  Hpmp_eff Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hpriv)).
    cbn match. cbn [andb].
    rewrite execR_eff_returnR. cbn match. cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hwrloop). cbn beta zeta.
  rewrite execR_eff_returnR. cbn match. cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.
End SWeff.

(* ====================================================================== *)
(** ** 5. The address transform, and [vmem_write] over an arbitrary rs1

    All register-only above the [vmem_write_addr] call, so the store's single
    trace element passes through untouched. *)

Lemma exec_eff_is_pmm_applicable_store s :
  exec_eff (is_pmm_applicable (Store Data) Machine) s = Some (true, s, []).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec_eff orb s = Some (true, s, []))
  end.
  { rewrite (exec_eff_or_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
    reflexivity. }
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_eff_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_eff_get_pmlen_store s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs)))
    = PMM_Disabled ->
  exec_eff (get_pmlen (Store Data) Machine) s = Some (0, s, []).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_is_pmm_applicable_store s)).
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

Lemma exec_eff_transform_effective_address_store (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs)))
    = PMM_Disabled ->
  exec_eff (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s, []).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_store _ s Hmprv)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_get_pmlen_store s Hpmm)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_eff_returnM.
Qed.

(* [WpMmodeLeafBase.v : VWg] *)
Section VWgeff.
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
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_vmem_write_8_gpr :
  exec_eff (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true,
            MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev),
            [WEwrite (AkInfo false false false) pa 8 data]).
Proof.
  unfold vmem_write. rewrite exec_eff_catch_early_return.
  assert (Hgta : exec_eff (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s, [])).
  { unfold get_transformed_data_addr.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_transform_effective_address_store ea s Hcp Hmprv Hpmm)).
    apply exec_eff_returnM. }
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Virtaddr a8) s)).
  rewrite execR_eff_liftR.
  rewrite (exec_eff_vmem_write_addr_8 a8 data region s Halign Hcp Hmprv Hpmp_eff
             Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgeff.

(* ====================================================================== *)
(** ** 6. THE DELIVERABLE: the 8-byte STORE's [execute], at [exec_eff]

    The register-generic form: base from [rs1], value from [rs2] (either may
    be [x0], in which case the model reads [zero_reg]).  The trace is the ONE
    element born in §1.  [WeakEffSkel.exec_eff_riscv_step_base] joins this to
    the fetch's trace to give the whole step's. *)

(* [WpMmodeLeafBase.v : ExecStoreG] *)
Section ExecStoreGeff.
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
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Store Data) Machine) s
                      = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_writable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_eff_execute_STORE_8_gpr :
  exec_eff (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS,
            MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2) s.(mdev),
            [WEwrite (AkInfo false false false) pa 8 vrs2]).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec_eff (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s, [])) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hass).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
    (exec_eff_vmem_write_8_gpr rs1 offset _ region s Hcp Hmprv Hpmm Halign
       Hpmp_eff Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_eff_returnM _ _).
  cbn match.
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGeff.

(* ====================================================================== *)
(** ** 7. Soundness check *)

Print Assumptions exec_eff_execute_STORE_8_gpr.

(** * WeakLeafEff8.v — M4 batch 1: the 8-byte M-mode LOAD, at [exec_eff]

    WHAT THIS DELIVERS.  [WeakEffSkel] reduced a weak-memory leaf's whole
    remaining obligation to TWO [exec_eff] facts — the fetch's and the
    [execute]'s — because everything between the [try_step] wrapper and the
    instruction is register-only and contributes nothing to the trace
    ([WeakEffSkel.exec_eff_riscv_step_base] assembles the step's trace as
    [es_fetch ++ es_execute]).  THIS FILE IS THE SECOND OF THOSE TWO, for the
    LOAD-8 shape: the [exec_eff] twin of
    [WpMmodeLeafBase.exec_execute_LOAD_8_gpr], whose trace is exactly ONE
    element — the data read,

        [WEread (AkInfo false false false) pa 8]

    ([Read_plain] makes the model's [Interface.ReadReq.access_kind] the
    explicit plain-normal kind [AK_explicit {| variety := AV_plain;
    strength := AS_normal |}], and [WeakInterp.classify] of that is
    [AkInfo false false false]).

    HOW IT IS PROVED, AND WHY THE PREFIX IS MIRRORED RATHER THAN DETECTED.
    Every step of the chain below [read_ram] — [effectivePrivilege],
    [split_misaligned], [pmaCheck], the [within_*] probes, [translateAddr],
    the [untilMT] loop, [transform_effective_address], [get_pmlen],
    [ext_data_get_addr], [wX_bits] — is REGISTER-ONLY, so each of its
    [exec_eff] facts carries the EMPTY trace and each SC script replays
    verbatim with [RiscvExec.exec_bind_Some] renamed to
    [WeakEff.exec_eff_bind_nil] (and the [execR] half with
    [WeakEffSkel.execR_eff_bind_nil] / [_bind0_nil] / [_liftR_seq]).  One
    might hope to skip the replay via [WeakEff.exec_eff_quiet_of_empty], but
    that lemma can only conclude [quiet_trace] — a ZERO-WIDTH access is
    invisible to [exec], so no argument over [exec] can rule one out — while
    the certificates ([WeakEff.wcert_load_gen] and friends) need
    [nowrite_trace].  That zero-width residue is why the empty trace is
    established by replay and not by detection; see
    [claude-notes/projects/weak-memory.md].

    TWO PREMISES ARE TAKEN AS HYPOTHESES rather than proved here (they are
    being mirrored in a separate file, and keeping them as premises decouples
    the two): the M-mode [pmpCheck] reduction, and the three [within_*]
    probes.  Both are stated in their [exec_eff] form with an empty trace,
    which is the honest shape (each is a pure register reduction).

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a
    named lemma over a bind spine, exactly as the SC originals are. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: every
   space-separated [rewrite a b c] and every [rewrite H /=] below is the
   ssreflect form, as in the SC originals this file mirrors.  There is no
   Iris in this file. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import ExecCommon.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import WpGpr WpLoad WpMmodeLeafBase.
Require Import WeakLeafEffCommon.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 0. The kit, and the width-independent leaves: [WeakLeafEffCommon]

    [exec_eff_returnM] / [_and_boolM_nil] / [_or_boolM_nil] / [_MemRead]
    (the twins this chain's SC scripts name), and the leaves that are about
    neither the width nor the access — [exec_eff_split_misaligned_aligned],
    [_translationMode_M], [_rX_bits_gpr], [_wX_bits_at], [_wX_bits_gpr],
    [_ext_data_get_addr_gpr], [execR_eff_untilMT_1] — all live in
    [WeakLeafEffCommon] and are used from there. *)

(* ====================================================================== *)
(** ** 1. The register-only leaves of the LOAD chain

    [WpLoad.exec_effectivePrivilege_load] / [exec_split_misaligned_aligned] /
    [exec_is_shadow_stack_load], with [exec_bind_Some] renamed.  Each is a
    pure register reduction, so each trace is [[]]. *)

Lemma exec_eff_effectivePrivilege_load (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec_eff (effectivePrivilege (Load Data) m Machine) s = Some (Machine, s, []).
Proof.
  intro H. unfold effectivePrivilege.
  cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_eff_returnM.
Qed.

Lemma exec_eff_is_shadow_stack_load s :
  exec_eff (is_shadow_stack_access (Load Data)) s = Some (false, s, []).
Proof.
  unfold is_shadow_stack_access. cbn match. apply exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 2. THE ONE MEMORY-TOUCHING STEP: [read_ram], where the trace is born

    The SC proof ([WpLoad.exec_read_ram_plain_8]) pins the read's value with a
    [run]-fact and then only has to show [exec <> None].  Here the value is
    already available AS the SC fact, so the mirror peels BOTH interpreters
    down to the same [read_bytes] match in lockstep: the [Some] branch has the
    same word on both sides, and the [exec_eff] side additionally carries the
    [WEread]. *)

Lemma exec_eff_read_ram_plain_8 (addr : mword 64) (w : bv 64) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram Read_plain (Physaddr addr) 8 false) s
    = Some ((w, default_meta), s, [WEread (AkInfo false false false) addr 8]).
Proof.
  intros Hdev Hbytes.
  pose proof (exec_read_ram_plain_8 addr w s Hdev Hbytes) as Hsc.
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
      replace (classify a) with (AkInfo false false false)
        by (vm_compute; reflexivity)
  end.
  change (Z.to_N 8) with 8%N.
  injection Hsc; intros; subst; reflexivity.
Qed.

(* ====================================================================== *)
(** ** 3. Up through [mem_read]: the trace's one element rides the binds

    [pmaCheck] and the three [within_*] probes are register-only, so the only
    non-empty premise on this path is [read_ram]'s.  Each bind ABOVE it uses
    [WeakEff.exec_eff_bind_Some] (the general, concatenating form) and the
    trailing [returnM] contributes [[]], so every concatenation collapses with
    one [cbn [app]]. *)

Lemma exec_eff_pmaCheck_ram_load (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 8 (Load Data) pbmt false) s = Some (None, s, []).
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

Lemma exec_eff_checked_mem_read_ram_load (pbmt : page_based_mem_type)
    (addr : mword 64) (region : PMA_Region) (w : bv 64) s :
  exec_eff (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (within_clint (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 8) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (Load Data) pbmt Machine (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s, [WEread (AkInfo false false false) addr 8]).
Proof.
  intros Hpmp Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_load addr pbmt _ s Hmatch Halign Hread)).
      cbn match. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_readable (Physaddr addr) 8) s = Some (false, s, []))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (read_kind_of_flags _ _ _) s = Some (Read_plain, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_read_ram_plain_8 addr w s Hdev Hbytes)).
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_read_load (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  exec_eff (pmpCheck (Physaddr addr) 8 (Load Data) Machine) s = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec_eff (within_clint (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 8) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s, [WEread (AkInfo false false false) addr 8]).
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
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s
                 = Some (Ok (w, default_meta), s,
                         [WEread (AkInfo false false false) addr 8]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 8 _ _ _ _) s
                     = Some (Ok (w, default_meta), s,
                             [WEread (AkInfo false false false) addr 8]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram_load with (region := region); assumption. }
      cbn match. unfold mem_read_callback.
      rewrite exec_eff_returnM. cbn [app]. reflexivity. }
  cbn [MemoryOpResult_drop_meta].
  rewrite exec_eff_returnM. cbn [app]. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. [translateAddr] (Bare, M-mode) and the one-iteration [untilMT]

    Both cross into the early-return interpreter, so this is where
    [WeakEffSkel]'s [execR_eff] kit takes over from [WeakEff]'s.
    [WpLoad.misaligned_order_1] is PURE and is reused verbatim. *)

Lemma exec_eff_translateAddr_identity_load (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  exec_eff (translateAddr (Virtaddr a) (Load Data)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s, []).
Proof.
  intros Hcp Hmprv.
  unfold translateAddr.
  rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_effectivePrivilege_load _ s Hmprv)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_translationMode_M s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_is_shadow_stack_load s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_eff_bind_eq.
  cbn match. cbn [app]. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4b. [vmem_read_addr] at width 8 — the [untilMT] loop's one turn *)

Section SEff.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.

Lemma exec_eff_vmem_read_addr_8 :
  exec_eff (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s, [WEread (AkInfo false false false) pa 8]).
Proof.
  unfold vmem_read_addr.
  rewrite exec_eff_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR_eff (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s, [])).
  { rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
    rewrite execR_eff_liftR.
    rewrite (exec_eff_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (data2, true, 0), s,
                         [WEread (AkInfo false false false) pa 8]))
  end.
  { eapply execR_eff_untilMT_1.
    - (* measure *) reflexivity.
    - (* body *)
      cbn match.
      assert (Hass : exec_eff (assert_exp' true "loop dummy assert") s
                     = Some (@eq_refl bool true, s, [])) by reflexivity.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_eff_liftR_seq _ _ _ _ _
        (exec_eff_translateAddr_identity_load (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      match goal with
      | |- execR_eff (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR_eff mrm s
                       = Some (inr data2, s, [WEread (AkInfo false false false) pa 8]))
      end.
      { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
          (exec_eff_mem_read_load PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
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
End SEff.

(* ====================================================================== *)
(** ** 5. The address-formation and register-write leaves

    [is_pmm_applicable] / [get_pmlen] / [transform_effective_address] from
    [WpLoad], and [ext_data_get_addr] / [rX_bits] / [wX_bits] from [WpGpr] —
    all register-only, all traces [[]]. *)

Lemma exec_eff_is_pmm_applicable_load s :
  exec_eff (is_pmm_applicable (Load Data) Machine) s = Some (true, s, []).
Proof.
  unfold is_pmm_applicable.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Load Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Load Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  replace (generic_neq (Load Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
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

Lemma exec_eff_get_pmlen_load s :
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec_eff (get_pmlen (Load Data) Machine) s = Some (0, s, []).
Proof.
  intro Hpmm. unfold get_pmlen.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_is_pmm_applicable_load s)).
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

Lemma exec_eff_transform_effective_address_load (ea : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled ->
  exec_eff (transform_effective_address (Virtaddr ea) (Load Data)) s
    = Some (pm_transform_PA (Virtaddr ea) 0, s, []).
Proof.
  intros Hcp Hmprv Hpmm. unfold transform_effective_address.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_load _ s Hmprv)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_get_pmlen_load s Hpmm)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_translationMode_M s)).
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity). cbn match.
  apply exec_eff_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* ====================================================================== *)
(** ** 6. THE DELIVERABLE: [vmem_read] and the LOAD-8 [execute], at [exec_eff]

    [WpMmodeLeafBase]'s [Section VRg] / [Section ExecLoadG], with the same
    [Variable]s and [Let]s; the SC [Hpmp] and the three [exec]-level
    [within_*] premises are replaced by their [exec_eff] forms (the [exec]
    ones follow from these by [WeakCert.exec_eff_exec], so nothing is lost).
    The conclusion's trace is the ONE data read. *)

Section VRgEff.
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
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_eff_vmem_read_8_gpr :
  exec_eff (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s
    = Some (Ok data2, s, [WEread (AkInfo false false false) pa 8]).
Proof.
  unfold vmem_read. rewrite exec_eff_catch_early_return.
  assert (Hgta : exec_eff (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s, [])).
  { unfold get_transformed_data_addr.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _
              (exec_eff_transform_effective_address_load ea s Hcp Hmprv Hpmm)).
    apply exec_eff_returnM. }
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_eff_bind_nil _ _ _ _ _ (execR_eff_returnR (Virtaddr a8) s)).
  rewrite execR_eff_liftR.
  rewrite (exec_eff_vmem_read_addr_8 a8 v region s Halign Hcp Hmprv Hpmp_eff
             Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End VRgEff.

(* ---------------------------------------------------------------------- *)
(** *** 6b. THE TOP LEMMA *)

Section ExecLoadGEff.
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
Hypothesis Hpmp_eff : exec_eff (pmpCheck (Physaddr pa) 8 (Load Data) Machine) s = Some (None, s, []).
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec_eff (within_clint (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hsig : exec_eff (within_sig (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hh : exec_eff (within_htif_readable (Physaddr pa) 8) s = Some (false, s, []).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

(* [Interface.ReadReq.access_kind] of the model's request reduces to
   [AK_explicit {| variety := AV_plain; strength := AS_normal |}] (the
   [Read_plain] arm of [read_ram]), whose [WeakInterp.classify] is
   [AkInfo false false false]. *)
Lemma exec_eff_execute_LOAD_8_gpr :
  exec_eff (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (extend_value false data2)),
            [WEread (AkInfo false false false) pa 8]).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec_eff (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s, [])) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hass).
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
    (exec_eff_vmem_read_8_gpr rs1 offset v region s Hcp Hmprv Hpmm Halign Hpmp_eff
       Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match beta.
  assert (Hw : exec_eff (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)), [])).
  { rewrite (exec_eff_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ Hw).
  rewrite exec_eff_returnM. cbn match. cbn [app]. reflexivity.
Qed.
End ExecLoadGEff.

(* ====================================================================== *)
(** ** 7. Soundness check *)

Print Assumptions exec_eff_execute_LOAD_8_gpr.

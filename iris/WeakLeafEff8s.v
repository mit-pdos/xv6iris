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
Import Defs.
Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The local twins the name-swap table calls for

    [RiscvTryStep.exec_returnM] (the model's own [returnM], which is
    [Defs.returnm] at [E := exception] and must have its own lemma so a
    SYNTACTIC rewrite matches the [returnM …] appearing in model terms), the
    two short-circuit connectives, and the one [exec_eff] arm lemma that the
    memory step needs — [RiscvFetchExec.exec_MemWrite]'s twin, which is where
    the [WEwrite] is born. *)

Local Lemma wl8s_exec_eff_returnM {X} (x : X) s :
  exec_eff (returnM x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Local Lemma wl8s_exec_eff_MemWrite {X} (n : N) (req : Interface.WriteReq.t n)
    (k : (option bool + Arch.abort)%type -> M X) s :
  dev_addr (Interface.WriteReq.pa req) = false ->
  exec_eff (Interface.Next (Interface.MemWrite n req) k) s
  = match exec_eff (k (inl None))
            (MState s.(sregs)
               (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                            (Interface.WriteReq.value req)) s.(mdev)) with
    | Some (y, s', es) =>
        Some (y, s', WEwrite (classify (Interface.WriteReq.access_kind req))
                             (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) :: es)
    | None => None
    end.
Proof. intros Hd. cbn [exec_eff]. rewrite Hd. reflexivity. Qed.

Local Lemma wl8s_exec_eff_and_boolM (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (and_boolM l r) s
  = (if bl then exec_eff r sl else Some (false, sl, [])).
Proof.
  intro H. unfold and_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [reflexivity | apply wl8s_exec_eff_returnM].
Qed.

Local Lemma wl8s_exec_eff_or_boolM (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (or_boolM l r) s
  = (if bl then Some (true, sl, []) else exec_eff r sl).
Proof.
  intro H. unfold or_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [apply wl8s_exec_eff_returnM | reflexivity].
Qed.

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
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
  cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite wl8s_exec_eff_MemWrite; last exact Hdev.
  reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. The register-only checks on the store path

    [exec_pmaCheck_ram_store] / [exec_effectivePrivilege_store] /
    [exec_is_shadow_stack_store] / [exec_translationMode_M] /
    [exec_split_misaligned_aligned], each with the empty trace and the SC
    script under §0's names. *)

Lemma exec_eff_pmaCheck_ram_store (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 8 (Store Data) pbmt false) s
    = Some (None, s, []).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wl8s_exec_eff_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply wl8s_exec_eff_returnM.
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
  unfold is_shadow_stack_access. cbn match. apply wl8s_exec_eff_returnM.
Qed.

Lemma exec_eff_translationMode_M s :
  exec_eff (translationMode Machine) s = Some (Bare, s, []).
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply wl8s_exec_eff_returnM.
Qed.

Lemma exec_eff_split_misaligned_aligned (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 8 = true ->
  exec_eff (split_misaligned vaddr 8) s = Some ((1, 8), s, []).
Proof.
  intro H. unfold split_misaligned. rewrite H. cbn [orb].
  apply wl8s_exec_eff_returnM.
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
  unfold checked_mem_write.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (phys_access_check _ _ _ _ _ _) s = Some (None, s, []))).
  2:{ unfold phys_access_check.
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hpmp_eff).
      cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                (exec_eff_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply wl8s_exec_eff_returnM. }
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (within_mmio_writable (Physaddr addr) 8) s
                 = Some (false, s, []))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (wl8s_exec_eff_or_boolM _ _ _ _ _ Hc). cbn match.
      rewrite (wl8s_exec_eff_or_boolM _ _ _ _ _ Hsig). cbn match.
      rewrite (wl8s_exec_eff_and_boolM _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply wl8s_exec_eff_returnM. }
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (exec_eff_write_ram_plain_8 addr data s Hdev)).
  reflexivity.
Qed.

Lemma exec_eff_mem_write_ea (addr : mword 64) s :
  exec_eff (mem_write_ea (Physaddr addr) 8 false false false) s
    = Some (Ok tt, s, []).
Proof.
  unfold mem_write_ea. cbn [orb andb].
  rewrite (exec_eff_bind_nil _ _ _ _ _
            (_ : exec_eff (write_kind_of_flags false false false) s
                 = Some (rv64d_types.Write_plain, s, []))).
  2:{ unfold write_kind_of_flags. cbn match. apply wl8s_exec_eff_returnM. }
  apply wl8s_exec_eff_returnM.
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
Lemma execR_eff_untilMT_1 {R Vars} (vars vars' : Vars) (measure : Vars -> Z)
    (cond : Vars -> Defs.monadR R exception bool)
    (body : Vars -> Defs.monadR R exception Vars) s s' es :
  measure vars = 1 ->
  execR_eff (body vars) s = Some (inr vars', s', es) ->
  execR_eff (cond vars') s' = Some (inr true, s', []) ->
  execR_eff (Defs.untilMT vars measure cond body) s = Some (inr vars', s', es).
Proof.
  intros Hm Hb Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge];
    [| exfalso; rewrite Hm in Hge; lia ].
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hb).
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hc).
  cbn match.
  rewrite execR_eff_returnR. rewrite ?app_nil_r. reflexivity.
Qed.

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
  unfold vmem_write_addr.
  rewrite exec_eff_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR_eff (returnR (result bool ExecutionResult) tt >>
                              liftR (split_misaligned (Virtaddr a) 8)) s
                   = Some (inr (1, 8), s, [])).
  { rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
    rewrite execR_eff_liftR.
    rewrite (exec_eff_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_eff_bind_nil _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true),
                         MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev),
                         [WEwrite (AkInfo false false false) pa 8 data]))
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
           (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0*8)) s Hpriv Hmprv)).
      cbn [bits_of_virtaddr]. cbn match.
      assert (Hsc : exec_eff (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s, [])) by reflexivity.
      assert (Hscm : execR_eff (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s
                     = Some (inr tt, s, []))
        by (rewrite execR_eff_liftR; rewrite Hsc; reflexivity).
      (* Isolate the SC-assert >> if-expression as Hwrloop; proving it in a
         nested goal keeps the outer goal from definitionally reducing the
         if's else branch through mem_write_value (the over-reduction trap). *)
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR_eff (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true,
                                   MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev),
                                   [WEwrite (AkInfo false false false) pa 8 data]))
      end.
      { (* peel the SC assert, keeping the if-expression opaque via [set] so
           the bind0 rewrite cannot reduce its else branch *)
        match goal with
        | |- execR_eff (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_eff_bind0_nil _ _ _ _ Hscm).
        unfold NN; clear NN.
        (* strip [if (andb false _) then THEN else ELSE] -> ELSE by conversion *)
        match goal with
        | |- execR_eff (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR_eff B ss = R)
        end.
        (* ELSE: mem_write_ea -> Ok tt *)
        rewrite (execR_eff_liftR_seq _ _ _ _ _
          (exec_eff_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        (* autocast (subrange data 63 0) = data : capture the value arg from the
           goal (so it carries the mword (8*8) type) and rewrite it to data *)
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
        (* mem_write_value -> Ok true, write_bytes state, ONE trace element *)
        rewrite (execR_eff_liftR_cat _ _ _ _ _ _
          (exec_eff_mem_write_value_8 PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8)))
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
End SWeff.

(* ====================================================================== *)
(** ** 5. The address transform, and [vmem_write] over an arbitrary rs1

    All register-only above the [vmem_write_addr] call, so the store's single
    trace element passes through untouched. *)

Lemma exec_eff_is_pmm_applicable_store s :
  exec_eff (is_pmm_applicable (Store Data) Machine) s = Some (true, s, []).
Proof.
  unfold is_pmm_applicable.
  rewrite (wl8s_exec_eff_and_boolM _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (wl8s_exec_eff_and_boolM _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  rewrite (wl8s_exec_eff_and_boolM _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true
    by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec_eff orb s = Some (true, s, []))
  end.
  { rewrite (wl8s_exec_eff_or_boolM _ _ _ _ _ (wl8s_exec_eff_returnM _ s)).
    replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
    reflexivity. }
  rewrite (wl8s_exec_eff_and_boolM _ _ _ _ _ Hor).
  cbn match.
  rewrite (wl8s_exec_eff_returnM _ s).
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
    apply wl8s_exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply wl8s_exec_eff_returnM.
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
  apply wl8s_exec_eff_returnM.
Qed.

(** [WpGpr]'s two register-file readers, at [exec_eff]. *)

Lemma exec_eff_rX_bits_gpr (i : mword 5) s :
  exec_eff (rX_bits (Regidx i)) s
  = Some (if Z.eqb (uint i) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) s.(sregs), s, []).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: unfold rX_bits, rX; rewrite H; cbn match; reflexivity.
Qed.

Lemma exec_eff_ext_data_get_addr_gpr (rs1 : mword 5) (offset : mword 64) acc w s :
  exec_eff (ext_data_get_addr (Regidx rs1) offset acc w) s
  = Some (Ext_DataAddr_OK (Virtaddr (add_vec
      (if Z.eqb (uint rs1) 0 then zero_reg
       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset)),
          s, []).
Proof.
  unfold ext_data_get_addr.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  cbn match. apply wl8s_exec_eff_returnM.
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
    apply wl8s_exec_eff_returnM. }
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
  rewrite (wl8s_exec_eff_returnM _ _).
  cbn match.
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGeff.

(* ====================================================================== *)
(** ** 7. Soundness check *)

Print Assumptions exec_eff_execute_STORE_8_gpr.

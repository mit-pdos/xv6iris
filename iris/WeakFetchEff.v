(** * WeakFetchEff.v — THE FETCH'S OWN [exec_eff] REDUCTION (M4 batch 0b)

    [WeakEffSkel] §6b named exactly two facts standing between the step
    assembly ([exec_eff_riscv_step_base]) and [WeakCert.wP_eff]:

      (i)  the FETCH's own [exec_eff] reduction — the one place a [WEread] is
           emitted for EVERY instruction, and
      (ii) the [tick_clock] mirror, which turns the assembly's
           [riscv_step false] fact into the [forall tick] shape
           [WeakCert.wstep_conf_eff] asks for.

    This file is both, plus the recipe they unlock:
    [wP_eff_of_leaf_base], the one-statement rule that turns a leaf's
    (a) text bytes, (b) decode fact and (c) [execute]'s [exec_eff] fact into
    its [wP_eff] obligation, with no hand-peeling anywhere.

    WHY THE FETCH CANNOT BE DETECTED.  [WeakEff]'s empty-memory detector
    ([exec_eff_quiet_of_empty]) does not apply: the fetch READS the text, so
    it fails at the empty memory.  And a domain-growth argument cannot
    exclude a value-preserving write to a byte the confined map already has
    (M3c's recorded finding, here at the fetch) — so nothing semantic can
    replace the syntactic replay below.

    WHY EVERY REGISTER-ONLY SUB-LEMMA IS RESTATED AT THE EMPTY TRACE rather
    than detected.  The detector can only ever give [quiet_trace], which
    ADMITS a zero-width write (invisible to [exec]); [WeakEff.wcert_store_gen]
    / [_load_gen] / [_amo_aq_gen] need [nowrite_trace], because a zero-width
    write still appends a byte-less message and [wQ_store]'s
    [wm_log σ' = wm_log σ ++ [msg]] is then false.  A syntactic bind-peel
    gives [[]] outright, which is what §1 below does for the whole
    register-only cone the fetch names.

    WHAT SHIPPED.  The 4-aligned [F_Base] arm of [WeakFunnel.exec_fetch_flat]
    — every 4-aligned 32-bit instruction, i.e. the funnel's main case.  The
    other three arms (2-aligned [F_Base], [F_RVC] at either alignment) are
    NOT mirrored here; §4 records that boundary in its statement rather than
    hiding it.

    Sections:
      §0  the trivial twins the replay needs ([returnM], and/or over [exec_eff])
      §1  the register-only cone, at the EMPTY trace
      §2  [exec_eff_read_ram_plain_4] — THE effect, and the only one
      §3  the chain: checked_mem_read -> mem_read -> fetch_bytes -> fetch
      §4  [exec_eff_fetch_flat_base4] — the [fetch_flat_ok] wrapper
      §5  the [tick_clock] mirror
      §6  [wP_eff_of_leaf_base] — the batch-2 recipe, in one statement
      §7  the end-to-end check: a [WeakCert] certificate re-derived through it
*)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakRacy.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv.
Require Import WeakEffSkel.
Require Import WeakPmpEff.
Require Import WeakFunnel.
Require Import WpDecodeBridge.
Require Import WeakTickEff.
Require Import WeakLeafEffCommon.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The trivial twins: [WeakLeafEffCommon]

    [RiscvTryStep.exec_returnM] and the two boolean connectives at
    [exec_eff] (each the SC statement with [[]] appended and the SC script
    with the bind lemma renamed), and [translationMode] at Machine, are
    [WeakLeafEffCommon]'s — the shape files need exactly the same four. *)

(* ====================================================================== *)
(** ** 1. THE REGISTER-ONLY CONE, AT THE EMPTY TRACE

    Every lemma here is [RiscvFetchExec]'s / [RiscvExtras]' verbatim, with
    [exec] replaced by [exec_eff] and [[]] appended.  Read the scripts
    against their SC originals: the only edits are the bind/lift names. *)

Lemma exec_eff_within_clint_false (a : Arch.pa) (w : Z) s :
  not_in_clint a -> (0 < w)%Z ->
  exec_eff (within_clint (Physaddr a) w) s = Some (false, s, []).
Proof.
  intros Hnc Hw. unfold within_clint, plat_have_clint, __id.
  cbn [Riscv.rv64d.not negb].
  assert (Hf : (uint plat_clint_base <=? uint a) &&
               (uint a + w <=? uint plat_clint_base + uint plat_clint_size) = false).
  { destruct Hnc as [H|H]; [apply andb_false_intro1|apply andb_false_intro2];
      apply Z.leb_gt; lia. }
  rewrite Hf. apply exec_eff_returnm.
Qed.

Lemma exec_eff_within_sig_false (a : Arch.pa) (w : Z) s :
  not_in_sig a -> (0 < w)%Z ->
  exec_eff (within_sig (Physaddr a) w) s = Some (false, s, []).
Proof.
  intros _ _. unfold within_sig, plat_have_sig, __id.
  cbn [Riscv.rv64d.not negb]. apply exec_eff_returnm.
Qed.

Lemma exec_eff_within_htif_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec_eff (within_htif_readable (Physaddr a) w) s = Some (false, s, []).
Proof.
  intro Hn. unfold within_htif_readable, within_htif_writable.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_eff_returnm.
Qed.

(** ... and its WRITE twin, the gate every store/AMO leaf probes. *)
Lemma exec_eff_within_htif_w_false (a : Arch.pa) (w : Z) s :
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec_eff (within_htif_writable (Physaddr a) w) s = Some (false, s, []).
Proof.
  intro Hn. unfold within_htif_writable.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg htif_tohost_base s)).
  rewrite Hn. cbn match. apply exec_eff_returnm.
Qed.

Lemma exec_eff_effectivePrivilege_fetch (m : SailStdpp.Values.mword 64)
    (p : Privilege) s :
  exec_eff (effectivePrivilege (InstructionFetch tt) m p) s = Some (p, s, []).
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_is_shadow_stack_fetch s :
  exec_eff (is_shadow_stack_access (InstructionFetch tt)) s = Some (false, s, []).
Proof. unfold is_shadow_stack_access. apply exec_eff_returnM. Qed.

Lemma exec_eff_translateAddr_identity (a : SailStdpp.Values.mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (translateAddr (Virtaddr a) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s, []).
Proof.
  intros Hcp.
  unfold translateAddr.
  rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_translationMode_M s)).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_is_shadow_stack_fetch s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_eff_bind_eq.
  cbn match. reflexivity.
Qed.

Lemma exec_eff_pmaCheck_ram (addr : SailStdpp.Values.mword 64)
    (pbmt : page_based_mem_type) (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s
    = Some (Ok pma_ok_aligned, s, []).
Proof.
  intros Hmatch Halign Hexec.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_eff_peel Hmatch Hexec (exec_eff_is_mag_applicable_fetch 4 s) Halign.
Qed.

Lemma exec_eff_hartSupports_Ziccif s :
  exec_eff (hartSupports Ext_Ziccif) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Ziccif s :
  exec_eff (currentlyEnabled Ext_Ziccif) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  cbn match. apply exec_eff_hartSupports_Ziccif.
Qed.

(* ====================================================================== *)
(** ** 2. THE ONE EFFECT: [read_ram] at width 4

    This is the whole content of the fetch's trace.  The SC original
    ([RiscvFetchExec.exec_read_ram_plain_4]) goes through [run_to_exec] and a
    [read_bytes <> None] argument; here the byte facts pin the read outright
    ([WeakRacy.read_bytes_of_bytes]), which is shorter AND names the value the
    [MemRead] arm stores into the trace.

    [wak_plain] is what [WeakInterp.classify] makes of the access kind the
    model attaches to an instruction fetch.  rv64d emits
    [AK_explicit {| variety := AV_plain; strength := AS_normal |}] — NOT
    [AK_ifetch] — so the fetch is an ORDINARY weak read that raises views
    ([ak_coh = false]).  That is a fact about the generated model, and it is
    why every certificate in [WeakCert] quantifies over the fetch's [akinfo]
    rather than pinning it. *)

Definition wak_plain : akinfo := AkInfo false false false.

Lemma exec_eff_read_ram_plain_4 (addr : SailStdpp.Values.mword 64) (w : bv 32) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram Read_plain (Physaddr addr) 4 false) s
    = Some ((w, default_meta), s, [WEread wak_plain addr 4]).
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn [exec_eff]. cbn [Interface.ReadReq.pa Interface.ReadReq.access_kind].
  rewrite Hdev.
  rewrite (read_bytes_of_bytes (mem s) addr (Z.to_N 4) w
             (fun j Hj => Hbytes j ltac:(lia))).
  cbn [Interface.iMon_bind]. cbn match beta iota.
  reflexivity.
Qed.

(* ====================================================================== *)
(** ** 3. THE CHAIN, replayed

    [RiscvFetchExec]'s [exec_checked_mem_read_ram] -> [exec_mem_read_fetch] ->
    [exec_fetch_bytes_4] -> [exec_fetch_done], with the bind lemmas renamed
    and ONE trace element threaded through.  The PMP premise is taken in its
    [exec_eff] form (it is discharged in §4 from [WeakPmpEff]), and so are the
    three MMIO-range gates — exactly as the SC originals take them. *)

(** [RiscvFetchExec]'s own [Local Lemma avi0_mul4], restated (it is [Local]
    there, so not importable). *)
Local Lemma avi0_mul4 (a : SailStdpp.Values.mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Lemma exec_eff_checked_mem_read_ram (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (checked_mem_read (InstructionFetch tt) pbmt Machine
              (Physaddr addr) 4 false false false false) s
    = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  (* the PMA/PMP decision, with the PMA answer prioritised on failure *)
  assert (Hcp : exec_eff (check_pma_with_pmp_priority (InstructionFetch tt) pbmt Machine
                            (Physaddr addr) 4 false) s
                = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_eff_returnM. }
  (* within_mmio_readable = false, trace [] *)
  assert (Hmmio : exec_eff (within_mmio_readable (Physaddr addr) 4) s
                  = Some (false, s, [])).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_eff_catch_early_return.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (exec_eff_split_misaligned_unsplit addr 4 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _
             (_ : exec_eff (read_kind_of_flags false false false) s
                  = Some (Read_plain, s, []))).
  2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
  cbn beta.
  (* the split loop: ONE iteration at offset 0, and THE trace element *)
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                 = Some (inr (w, true, 0), s, [WEread wak_plain addr 4])) end.
  { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul4.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpmp). cbn beta.
    cbn match.
    (* the pmpCheck arm is a [bind0] seq into within_mmio_readable *)
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR_eff (Defs.bind0 a b) s = Some (inr false, s, [])) end.
    { rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match.
      rewrite execR_eff_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_eff_bind_nil _ _ _ _ _ Hseq). cbn beta. cbn match.
    (* the RAM read, whose own bind returns just the data (the meta is dropped) *)
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR_eff (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s, [WEread wak_plain addr 4])) end.
    { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
                 (exec_eff_read_ram_plain_4 addr w s Hdev Hbytes)).
      cbn beta match. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_32.
    rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_eff_returnR. cbn [app]. reflexivity.
Qed.

Lemma exec_eff_mem_read_fetch (pbmt : page_based_mem_type)
    (addr : SailStdpp.Values.mword 64) (region : PMA_Region) (w : bv 32) s :
  exec_eff (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 4) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false) s
    = Some (Ok w, s, [WEread wak_plain addr 4]).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s
                 = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _
                (_ : exec_eff (checked_mem_read _ _ _ _ 4 _ _ _ _) s
                     = Some (Ok (w, default_meta), s, [WEread wak_plain addr 4]))).
      2:{ cbn match.
          apply exec_eff_checked_mem_read_ram with (region := region); assumption. }
      cbn match. unfold mem_read_callback. rewrite exec_eff_returnM.
      by rewrite app_nil_r. }
  cbn [MemoryOpResult_drop_meta]. rewrite exec_eff_returnM.
  by rewrite app_nil_r.
Qed.

(** [fetch_bytes pc pc 4] — [RiscvFetchExec.exec_fetch_bytes_4] replayed.  The
    [execR] plumbing (catch_early_return, the [liftR]s, the [returnR]s) is all
    trace-free; the one [_cat] is the [mem_read]. *)
Lemma exec_eff_fetch_bytes_4 (pc : SailStdpp.Values.mword 64)
    (region : PMA_Region) (w : SailStdpp.Values.mword 32) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (pmpCheck (Physaddr (fetch_pa pc)) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr (fetch_pa pc)) 4 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr (fetch_pa pc)) 4) s
    = Some (false, s, []) ->
  dev_addr (fetch_pa pc) = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  exec_eff (fetch_bytes pc pc 4) s
    = Some (@FetchBytes_Success 4 w, s, [WEread wak_plain (fetch_pa pc) 4]).
Proof.
  intros Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hdev Hbytes Hvalign.
  assert (Halign : is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true)
    by (rewrite fetch_pa_id; exact Hvalign).
  unfold fetch_bytes.
  rewrite exec_eff_catch_early_return.
  change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ _ _
    (_ : execR_eff (Defs.bind0 (Defs.returnR _ tt)
            (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
         = Some (inr (Ok (Physaddr (fetch_pa pc), PBMT_PMA, init_ext_ptw)), s, []))).
  2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
      rewrite execR_eff_liftR. rewrite (exec_eff_translateAddr_identity pc s Hpriv).
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ _ _
             (execR_eff_returnR (Physaddr (fetch_pa pc), PBMT_PMA) s)).
  cbv iota beta.
  rewrite (execR_eff_bind_cat _ _ _ _ _ _
    (_ : execR_eff (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA
                                 (Physaddr (fetch_pa pc)) 4 false false false)) s
         = Some (inr (Ok w), s, [WEread wak_plain (fetch_pa pc) 4]))).
  2:{ rewrite execR_eff_liftR.
      rewrite (exec_eff_mem_read_fetch PBMT_PMA (fetch_pa pc) region w s
                 Hpmp Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv).
      cbn match. reflexivity. }
  cbv iota beta. rewrite autocast_mword_id.
  rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
Qed.

(** ... and the outer [fetch] — [RiscvFetchExec.exec_fetch_done] replayed.
    Everything above [fetch_bytes] is PC reads and extension probes, hence
    trace-free; the whole fetch's trace is the ONE text-word read. *)
Lemma exec_eff_fetch_done (pc : SailStdpp.Values.mword 64)
    (region : PMA_Region) (w : SailStdpp.Values.mword 32) s :
  register_lookup PC s.(sregs) = pc ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (pmpCheck (Physaddr (fetch_pa pc)) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr (fetch_pa pc)) 4 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr (fetch_pa pc)) 4) s
    = Some (false, s, []) ->
  dev_addr (fetch_pa pc) = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec_eff (fetch tt) s = Some (F_Base w, s, [WEread wak_plain (fetch_pa pc) 4]).
Proof.
  intros HpcPC Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hdev Hbytes Hvalign HnotRVC.
  destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec_eff (Defs.read_reg PC : M _) s = Some (pc, s, [])).
  { rewrite (exec_eff_read_reg PC s). rewrite HpcPC. reflexivity. }
  unfold fetch.
  rewrite exec_eff_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ false s).
  2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_eff_bind_nil _ _ _ false s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_eff_returnR. }
      cbv iota beta.
      unfold Defs.and_boolM.
      rewrite (execR_eff_bind_nil _ _ _ false s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
          apply execR_eff_returnR. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ true s).
  2:{ unfold Defs.and_boolM.
      rewrite (execR_eff_bind_nil _ _ _ true s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
          apply execR_eff_returnR. }
      cbv iota beta.
      rewrite execR_eff_liftR. rewrite exec_eff_currentlyEnabled_Ziccif.
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_cat _ _ _ _ _ _
             (exec_eff_fetch_bytes_4 pc region w s Hpriv Hpmp Hmatch Hexec
                Hc Hsig Hh Hdev Hbytes Hvalign)).
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. THE FUNNEL'S FETCH, AT [exec_eff] — the 4-aligned [F_Base] arm

    [WeakFunnel.exec_fetch_flat] dispatches on the alignment and on the
    [FetchResult] constructor; THIS mirror covers the FIRST arm only —
    [F_Base] at a 4-aligned pc, i.e. every 4-aligned 32-bit instruction, which
    is the funnel's main case.  The remaining three arms (2-aligned [F_Base],
    [F_RVC] at either alignment) are NOT mirrored: they go through
    [exec_fetch_F_Base_2] / [exec_fetch_RVC_4] / [exec_fetch_RVC_2], each of
    which needs its own two-half or half-word read chain, and each of which
    emits a DIFFERENT trace (two 2-byte reads for the split fetch).  A leaf at
    those alignments therefore cannot yet close [wP_eff]; the boundary is
    stated here rather than hidden, and §6's recipe takes the 4-alignment as
    an explicit premise. *)

Lemma exec_eff_fetch_flat_base4 (t : mstate) (pc : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) :
  pmp_allows_all (register_lookup pmpcfg_n t.(sregs)) ->
  pma_allows_all (register_lookup pma_regions t.(sregs)) ->
  register_lookup PC t.(sregs) = pc ->
  register_lookup cur_privilege t.(sregs) = Machine ->
  register_lookup htif_tohost_base t.(sregs) = None ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  fetch_flat_ok t pc (F_Base w) ->
  exec_eff (fetch tt) t = Some (F_Base w, t, [WEread wak_plain pc 4]).
Proof.
  intros Hpmp Hpma Lpc Lpriv Lhtif Hal (H2al & Hram & w0 & Hr & Hbytes).
  destruct Hr as [<- HnotRVC].
  assert (Hram0 : addr_is_ram (fetch_pa pc)).
  { rewrite fetch_pa_id. rewrite <- (RiscvExtras.pa_add_0 pc). apply Hram. lia. }
  assert (Hram3 : addr_is_ram (pa_add (fetch_pa pc) 3)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)).
  { intros j Hj. rewrite fetch_pa_id. apply Hbytes. lia. }
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  destruct (pma_all_ram Hpma (fetch_pa pc) 4
             (pma_access_ram _ _ _ Hram0 Hram3
                (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & Hexec0 & _ & _).
  assert (Halign : is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true)
    by (rewrite fetch_pa_id; exact Hal).
  pose proof (exec_eff_fetch_done pc region w t Lpc Lpriv
           (exec_eff_pmpCheck_machine_unlocked_ifetch4 (fetch_pa pc) t Hpmp Halign)
           Hmatch Hexec0
           (exec_eff_within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
           (exec_eff_within_sig_false   (fetch_pa pc) 4 t Hns ltac:(lia))
           (exec_eff_within_htif_false  (fetch_pa pc) 4 t Lhtif)
           (addr_is_ram_not_dev _ Hram0) Hbf Hal HnotRVC) as Hf.
  rewrite fetch_pa_id in Hf. exact Hf.
Qed.

(* ====================================================================== *)
(** ** 5. THE INTERRUPT GATE, AT THE EMPTY TRACE

    [RiscvTryStep]'s [Section ExecPending] replayed.  [dispatchInterrupt]
    stands between the hart-active gate and the fetch, and
    [WeakEffSkel.exec_eff_dispatchInterrupt_none] reduces it to
    [getPendingSet]; THIS is that premise.  Everything here reads registers
    only, so every trace is [[]]. *)

Lemma exec_eff_hartSupports_S s :
  exec_eff (hartSupports Ext_S) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zicsr s :
  exec_eff (hartSupports Ext_Zicsr) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec_eff (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s, []).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Zicsr.
Qed.

Lemma exec_eff_currentlyEnabled_S s :
  exec_eff (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_S s)).
  rewrite (exec_eff_and_boolM_nil _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s)).
      apply exec_eff_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_eff_rec_cE_Zicsr.
  - reflexivity.
Qed.

Section ExecPendingEff.
  Context (s : mstate).
  Hypothesis HmisaS :
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE (register_lookup mstatus s.(sregs))) ('b"1") = false.

  Lemma exec_eff_cE_S_true :
    exec_eff (currentlyEnabled Ext_S) s = Some (true, s, []).
  Proof using HmisaS. rewrite exec_eff_currentlyEnabled_S HmisaS. reflexivity. Qed.

  Lemma exec_eff_ext_int_some :
    exists ev, exec_eff (external_interrupts_pending tt) s = Some (ev, s, []).
  Proof using HmisaS.
    unfold external_interrupts_pending.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg sig_meip s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_cE_S_true). cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg sig_seip s)).
    eexists. apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_read_mip_some :
    exists v, exec_eff (read_mip IncludePlatformInterrupts) s = Some (v, s, []).
  Proof using HmisaS.
    destruct exec_eff_ext_int_some as [ev Hext].
    unfold read_mip. cbn match. eexists.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mip s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hext).
    apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_mIE_false :
    exec_eff (Defs.or_boolM
            (Defs.and_boolM (returnM (generic_eq Machine Machine))
               (Defs.bind (Defs.read_reg mstatus)
                  (fun w7 : SailStdpp.Values.mword 64 =>
                     returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Machine Supervisor)
                          (generic_eq Machine User)))) s
      = Some (false, s, []).
  Proof using HmIE.
    assert (Hand : exec_eff (Defs.and_boolM (returnM (generic_eq Machine Machine))
                     (Defs.bind (Defs.read_reg mstatus)
                        (fun w7 : SailStdpp.Values.mword 64 =>
                           returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s, [])).
    { rewrite (exec_eff_and_boolM_nil _ _ _ _ _
                 (exec_eff_returnM (generic_eq Machine Machine) s)).
      change (generic_eq Machine Machine) with true. cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
      rewrite HmIE. apply exec_eff_returnm. }
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hand).
    change (orb (generic_eq Machine Supervisor) (generic_eq Machine User))
      with false.
    apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_sIE_false :
    exec_eff (Defs.or_boolM
            (Defs.and_boolM (returnM (generic_eq Machine Supervisor))
               (Defs.bind (Defs.read_reg mstatus)
                  (fun w : SailStdpp.Values.mword 64 =>
                     returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Machine User))) s
      = Some (false, s, []).
  Proof.
    assert (Hand : exec_eff (Defs.and_boolM (returnM (generic_eq Machine Supervisor))
                     (Defs.bind (Defs.read_reg mstatus)
                        (fun w : SailStdpp.Values.mword 64 =>
                           returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s, [])).
    { rewrite (exec_eff_and_boolM_nil _ _ _ _ _
                 (exec_eff_returnM (generic_eq Machine Supervisor) s)).
      change (generic_eq Machine Supervisor) with false. cbn match. reflexivity. }
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hand).
    change (generic_eq Machine User) with false. apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_getPendingSet_machine_none :
    exec_eff (getPendingSet Machine) s = Some (None, s, []).
  Proof using HmisaS HmIE.
    destruct exec_eff_read_mip_some as [mipv Hmip].
    unfold getPendingSet.
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_cE_S_true). cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hmip).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_mIE_false).
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_sIE_false).
    cbn [andb]. apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_dispatchInterrupt_machine_none :
    exec_eff (dispatchInterrupt Machine) s = Some (None, s, []).
  Proof using HmisaS HmIE.
    apply exec_eff_dispatchInterrupt_none.
    exact exec_eff_getPendingSet_machine_none.
  Qed.

End ExecPendingEff.

(* ====================================================================== *)
(** ** 6. THE REGISTER-ONLY BRIDGE — how a leaf gets its DECODE fact at
        [exec_eff] WITHOUT restating the decode library

    [WeakEffSkel.exec_eff_riscv_step_base] asks for
    [exec_eff (ext_decode w) s = Some (i, s, [])], and the whole decode
    library states [exec (ext_decode w) s = Some (i, s)].  Restating 1220
    per-word decode lemmas at [exec_eff] is not an option, and the
    empty-memory detector cannot give the EMPTY trace (only
    [WeakEff.quiet_trace]).

    [WpDecodeBridge.goodb] is the way out, and it was already there:
    it is a SYNTACTIC witness — a fixpoint over the monad, along the path the
    state resolves — that the run performs no memory outcome, and it is
    [vm_compute]d at a CONCRETE reference state by every decode call site
    already ([WpDecodeBridge.decode_bridge]).  Its ONE gap for our purpose is
    the [Barrier] arm, which [goodb] accepts (a barrier is read-only) but
    which emits a [WEbar] into the trace.  [goodb0] below is [goodb] with that
    arm closed; [goodb0_goodb] says it is strictly stronger, so nothing that
    already holds is lost.

    THE PAYOFF, and it is the batch-2 unit price: a leaf's decode obligation
    at [exec_eff] is [exec_eff_decode_bridge] — the SAME [apply] and the SAME
    two [vm_compute]s the SC leaf already performs, with ONE extra
    [vm_compute] for [goodb0]. *)

Fixpoint goodb0 (D : register -> bool) {X} (m : M X) (s : mstate) {struct m}
    : bool :=
  match m with
  | Interface.Ret _ => true
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> bool with
       | Interface.RegRead r _ =>
           fun k => andb (D r) (goodb0 D (k (register_lookup r s.(sregs))) s)
       | Interface.InstrAnnounce _   => fun k => goodb0 D (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => goodb0 D (k tt) s
       | Interface.CacheOp _         => fun k => goodb0 D (k tt) s
       | Interface.TlbOp _           => fun k => goodb0 D (k tt) s
       | Interface.TakeException _   => fun k => goodb0 D (k tt) s
       | Interface.ReturnException _ => fun k => goodb0 D (k tt) s
       | Interface.TranslationStart _=> fun k => goodb0 D (k tt) s
       | Interface.TranslationEnd _  => fun k => goodb0 D (k tt) s
       | Interface.CycleCount        => fun k => goodb0 D (k tt) s
       | Interface.Message _         => fun k => goodb0 D (k tt) s
       | Interface.GetCycleCount     => fun k => goodb0 D (k 0%Z) s
       | _ => fun _ => false   (* RegWrite / MemRead / MemWrite / Barrier / … *)
       end) k
  end.

Lemma goodb0_goodb (D : register -> bool) {X} (m : M X) (s : mstate) :
  goodb0 D m s = true -> goodb D m s = true.
Proof.
  revert s. induction m as [y | T oc k IH]; intros s Hg; [reflexivity|].
  destruct oc; cbn [goodb0 goodb] in Hg |- *; try discriminate Hg;
    try (exact (IH _ s Hg)).
  apply andb_prop in Hg as [HDr Hg']. rewrite HDr. cbn [andb].
  exact (IH _ s Hg').
Qed.

(** The read-frame congruence of [WpDecodeBridge.exec_goodb_congr], at
    [exec_eff] — same induction, with the empty trace read off each arm. *)
Lemma exec_eff_goodb0_congr (D : register -> bool) {X} (m : M X) (s1 s2 : mstate) :
  (forall r, D r = true ->
     register_lookup r s1.(sregs) = register_lookup r s2.(sregs)) ->
  goodb0 D m s1 = true ->
  exists x, exec_eff m s1 = Some (x, s1, []) /\ exec_eff m s2 = Some (x, s2, []).
Proof.
  intros Hagree. revert s2 Hagree.
  induction m as [y | T oc k IH]; intros s2 Hagree Hgood.
  - exists y. split; reflexivity.
  - destruct oc; cbn [goodb0 exec_eff] in Hgood |- *; try discriminate Hgood;
      try (apply (IH _ s2 Hagree Hgood)).
    apply andb_prop in Hgood as [HDr Hgood'].
    match goal with
    | HDr : D ?rr = true |- _ =>
      pose proof (Hagree _ HDr) as Hr; rewrite <- Hr;
      apply (IH (register_lookup rr s1.(sregs)) s2 Hagree Hgood')
    end.
Qed.

(** THE BRIDGE a batch-2 leaf applies.  Compare
    [WpDecodeBridge.decode_state_bridge]: the premises are ITS premises with
    [goodb] strengthened to [goodb0], and the conclusion is at [exec_eff]
    with the EMPTY trace. *)
Lemma exec_eff_decode_bridge (D : register -> bool) {X} (m : M X)
    (dst s : mstate) (i : X) :
  agree_on D s dst ->
  goodb0 D m dst = true ->
  exec m dst = Some (i, dst) ->
  exec_eff m s = Some (i, s, []).
Proof.
  intros Hag Hgood Hdst.
  destruct (exec_eff_goodb0_congr D m dst s (fun r HD => eq_sym (Hag r HD)) Hgood)
    as [x [Hd Hs]].
  pose proof (exec_eff_exec _ _ _ _ _ Hd) as Hd'.
  rewrite Hdst in Hd'. injection Hd' as <-. exact Hs.
Qed.

(** … and the same [Ltac] the decode files already use, at [exec_eff]. *)
Ltac decode_bridge_eff D dst :=
  apply (exec_eff_decode_bridge D _ dst _ _);
  [ assumption | vm_compute; reflexivity | vm_compute; reflexivity ].

(* ====================================================================== *)
(** ** 7. THE [tick_clock] MIRROR — [riscv_step false] to [forall tick]

    [WeakCert.wstep_conf_eff] fixes ONE trace and quantifies over [tick], so
    the tick branch must contribute EXACTLY nothing — which is what
    [WeakTickEff.exec_eff_tick_clock] says.  [RiscvExec.exec_riscv_step_tick]
    replayed, then packaged as the [forall tick] shape a leaf owes. *)

Lemma exec_eff_bind_None {X Y} (m : M X) (f : X -> M Y) s :
  exec_eff m s = None -> exec_eff (Defs.bind m f) s = None.
Proof.
  intros Hm.
  destruct (exec_eff (Defs.bind m f) s) as [[[y s'] es']|] eqn:Hb; [|reflexivity].
  exfalso. pose proof (exec_eff_exec _ _ _ _ _ Hb) as Hbe.
  rewrite exec_bind in Hbe.
  destruct (exec m s) as [[v st]|] eqn:Hme; [|discriminate].
  destruct (exec_exec_eff _ _ _ _ Hme) as [es Hee]. by rewrite Hee in Hm.
Qed.

Lemma exec_eff_riscv_step_tick (s s' s'' : mstate) (es : list weff) :
  exec_eff (riscv_step false) s = Some (tt, s', es) ->
  exec_eff (tick_clock tt) s' = Some (tt, s'', []) ->
  exec_eff (riscv_step true) s = Some (tt, s'', es).
Proof.
  intros H1 H2. unfold riscv_step in H1 |- *.
  destruct (exec_eff (try_step 0%Z false) s) as [[[b s1] es1]|] eqn:E.
  - rewrite (exec_eff_bind_Some _ _ _ _ _ _ E) in H1.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ E).
    cbn beta iota in H1 |- *.
    rewrite exec_eff_returnm in H1. injection H1 as <- <-.
    rewrite H2. by rewrite app_nil_r.
  - rewrite (exec_eff_bind_None _ _ _ E) in H1. discriminate.
Qed.

(** The shape [WeakCert.wstep_conf_eff] asks for, from the ONE
    [riscv_step false] fact the step assembly produces. *)
Lemma exec_eff_riscv_step_all_ticks (s t0 : mstate) (es : list weff) :
  exec_eff (riscv_step false) s = Some (tt, t0, es) ->
  forall tick : bool, exists t' : mstate,
    exec_eff (riscv_step tick) s = Some (tt, t', es) /\ mem t' = mem t0.
Proof.
  intros H0 tick. destruct tick.
  - destruct (exec_eff_tick_clock t0) as (c & ti & p & Htick).
    eexists. split.
    + exact (exec_eff_riscv_step_tick s t0 _ es H0 Htick).
    + reflexivity.
  - exists t0. split; [exact H0 | reflexivity].
Qed.

(** [should_inc_minstret], mirrored — [RiscvExec.exec_should_inc_minstret_Some]
    with the bind lemma renamed.  Register-only, hence [[]]. *)
Lemma exec_eff_should_inc_minstret_Some (priv : Privilege) s :
  exists b : bool, exec_eff (should_inc_minstret priv) s = Some (b, s, []).
Proof.
  unfold should_inc_minstret, Defs.and_boolM.
  erewrite exec_eff_bind_nil.
  2:{ erewrite exec_eff_bind_nil.
      2:{ apply (exec_eff_read_reg mcountinhibit s). }
      apply exec_eff_returnm. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_eff_bind_nil.
    2:{ apply (exec_eff_read_reg minstretcfg s). }
    eexists. apply exec_eff_returnm.
  - eexists. apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 8. [wP_eff_of_leaf_base] — THE BATCH-2 RECIPE, IN ONE STATEMENT

    A leaf's whole [WeakCert.wP_eff] obligation, from
      (a) its four TEXT BYTES, in the confined memory, at a 4-aligned pc;
      (b) its DECODE fact, in the shape the decode library already proves it
          (a concrete reference state [dst], [agree_on], and two
          [vm_compute]s — §6);
      (c) its [execute]'s own [exec_eff] fact,
    plus the M-mode config tower, which is the SAME register facts
    [WeakFunnel.wwp_instr] already collects.

    Nothing else about the instruction enters, and the leaf peels nothing:
    the fetch (§2–§4), the wrapper, the decode bridge (§6) and the tick (§7)
    are all discharged here. *)

Lemma align4_align2 (pc : SailStdpp.Values.mword 64) :
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  is_aligned_vaddr (Virtaddr pc) 2 = true.
Proof.
  unfold is_aligned_vaddr. intros H%Z.eqb_eq. apply Z.eqb_eq.
  apply Zrem_divides in H. destruct H as [k Hk].
  apply Zrem_divides. exists (2 * k)%Z. lia.
Qed.

(** THE RUN-ASSEMBLY HALF, standalone: everything below is pinnedness-FREE —
    the wrapper, the fetch, the decode bridge and the tick assembled into the
    [∀ tick] run fact.  [wP_eff_of_leaf_base] (whole-window pinnedness) and
    [wP_eff_pin_of_leaf_base] (trace-keyed pinnedness, the invariant-form AMO
    leaf's shape) are this plus their window packaging — so a pin-form leaf
    costs its packaging lines, not a clone of the assembly.

    [W] is written [(W : _)] deliberately: this file imports [SailStdpp.Base],
    which leaks a SECOND [Countable Arch.pa] instance, and a binder spelled
    [gset Arch.pa] here elaborates against it — the two print identically and
    every application then fails (durable notes, the binder-position instance
    trap).  Letting [wmem_restrict]'s own argument pin the type is the fix. *)
Lemma exec_eff_step_of_leaf_base
    (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (es_x : list weff)
    (D : register -> bool) (dst : mstate) :
  (* --- the M-mode config tower: the SAME facts [wwp_instr] collects --- *)
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* --- (a) the text word, IN THE CONFINED MEMORY, at a 4-aligned pc --- *)
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (* --- (b) the DECODE, exactly as the decode library states it --- *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (* --- (c) the [execute]'s own [exec_eff] fact, and its register frame --- *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  (* --- the per-tick run fact --- *)
  forall tick : bool, exists t' : mstate,
    exec_eff (riscv_step tick)
      (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
      = Some (tt, t', ([WEread wak_plain pc 4] ++ es_x)%list) /\
    dom (mem t') ⊆ W.
Proof.
  intros Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp
         Hal Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec.
  set (sconf := MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)).
  intros tick.
  (* the funnel's own choice of the [minstret_increment] flag *)
  destruct (exec_eff_should_inc_minstret_Some
              (register_lookup cur_privilege (sregs sconf)) sconf) as [b Hsi].
  destruct (Hexec b) as (s_exec & Hex & Hhe & Hmie & Hdom).
  (* every register fact, moved past the [minstret_increment] pre-write *)
  assert (Lpriv_a : register_lookup cur_privilege
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = Machine)
    by (rewrite (set_mi_lookup cur_privilege _ b eq_refl); exact Lpriv).
  assert (Lpc_a : register_lookup PC
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = pc)
    by (rewrite (set_mi_lookup PC _ b eq_refl); exact Lpc).
  assert (Lhart_a : register_lookup hart_state
            (sregs (set_reg sconf (R_bool minstret_increment) b))
            = HART_ACTIVE tt)
    by (rewrite (set_mi_lookup hart_state _ b eq_refl); exact Lhart).
  assert (Lelp_a : eq_vec (register_lookup elp
            (sregs (set_reg sconf (R_bool minstret_increment) b)))
            (landing_pad_bits_backwards LP_EXPECTED) = false)
    by (rewrite (set_mi_lookup elp _ b eq_refl); exact Lelp).
  (* the interrupt gate (§5) *)
  assert (Hdisp : exec_eff (dispatchInterrupt Machine)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (None, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_dispatchInterrupt_machine_none.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaS.
    - rewrite (set_mi_lookup mstatus _ b eq_refl). exact LmIE. }
  (* the fetch (§4), at the post-write state: only the MEMORY matters *)
  assert (Hfetch : exec_eff (fetch tt)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (F_Base w, set_reg sconf (R_bool minstret_increment) b,
                    [WEread wak_plain pc 4])).
  { apply (exec_eff_fetch_flat_base4 _ pc w).
    - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl). exact Lpmp.
    - rewrite (set_mi_lookup pma_regions _ b eq_refl). exact Lpma.
    - exact Lpc_a.
    - exact Lpriv_a.
    - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl). exact Lhtif.
    - exact Hal.
    - split; [exact (align4_align2 pc Hal)|]. split; [exact Hram|].
      exists w. split; [split; [reflexivity|exact HnotRVC]|].
      intros j Hj. rewrite mem_set_reg. exact (Htext j Hj). }
  (* the decode, through §6's bridge — no peeling, two [vm_compute]s *)
  assert (Hdec_a : exec_eff (ext_decode w)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (i, set_reg sconf (R_bool minstret_increment) b, [])).
  { refine (exec_eff_decode_bridge D (ext_decode w) dst _ i _ Hgood Hdec).
    intros r HDr.
    assert (Hne : register_beq r (R_bool minstret_increment) = false).
    { destruct (register_beq r (R_bool minstret_increment)) eqn:Hb;
        [|reflexivity].
      exfalso. rewrite (register_beq_eq _ _ Hb) in HDr.
      by rewrite HDmi in HDr. }
    rewrite (set_mi_lookup r _ b Hne). exact (Hagree r HDr). }
  (* the whole step, from the fetch's trace and the [execute]'s
     ([WeakEffSkel] §5) *)
  pose proof (exec_eff_riscv_step_base sconf s_exec w i pc b
                [WEread wak_plain pc 4] es_x Hsi Lhart_a Lpriv_a Hdisp
                Hfetch Hdec_a Lelp_a Hnlpad Lpc_a Hex Hhe Hmie) as Hstep.
  (* ... at BOTH ticks, with the SAME trace (§7) *)
  destruct (exec_eff_riscv_step_all_ticks sconf _ _ Hstep tick)
    as (t' & Ht' & Hmt').
  exists t'. split; [exact Ht'|].
  rewrite Hmt'. destruct b; cbn [mem set_reg]; exact Hdom.
Qed.

(** THE WHOLE-WINDOW PACKAGING — the recipe every owned-data leaf applies.
    Statement unchanged from when this lemma carried the assembly inline. *)
Lemma wP_eff_of_leaf_base
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (es_x : list weff)
    (D : register -> bool) (dst : mstate) :
  (* --- the window (porting guide §2, items 1-3) --- *)
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  (* --- the M-mode config tower: the SAME facts [wwp_instr] collects --- *)
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* --- (a) the text word, IN THE CONFINED MEMORY, at a 4-aligned pc --- *)
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (* --- (b) the DECODE, exactly as the decode library states it --- *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (* --- (c) the [execute]'s own [exec_eff] fact, and its register frame --- *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  (* --- the certificate's whole obligation --- *)
  wP_eff (Some cid) ([WEread wak_plain pc 4] ++ es_x) σ.
Proof.
  intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp
         Hal Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec.
  apply (wP_eff_of_window cid _ σ W Hwf HW0 HWp).
  exact (exec_eff_step_of_leaf_base σ W pc w i es_x D dst
           Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp
           Hal Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec).
Qed.

(** THE PIN PACKAGING — the same split with §5a's TRACE-KEYED pinnedness in
    place of the whole-window premise.  This is the shape an invariant-form
    leaf (the AMO) produces: it owns nothing at its data word, so it can pin
    only the reads that do not self-pin (for the AMO: the fetch alone). *)
Lemma wP_eff_pin_of_leaf_base
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (es_x : list weff)
    (D : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  trace_pin σ ([WEread wak_plain pc 4] ++ es_x) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff_pin (Some cid) ([WEread wak_plain pc 4] ++ es_x) σ.
Proof.
  intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp
         Hal Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec.
  apply (wP_eff_pin_of_window cid _ σ W Hwf HW0 HWp).
  exact (exec_eff_step_of_leaf_base σ W pc w i es_x D dst
           Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmIE Lelp
           Hal Hram Htext HnotRVC Hagree HDmi Hgood Hdec Hnlpad Hexec).
Qed.

(* ====================================================================== *)
(** ** 9. THE END-TO-END CHECK: a [WeakCert] certificate re-derived through
        the recipe, with ZERO hand-peeling

    [WeakEffSkel] §6c checked that the skeleton's trace [es_f ++ es_x] is the
    certificates' own 2-/3-element list on the nose.  Now that §2–§4 pin
    [es_f] to the CONCRETE element [WEread wak_plain pc 4], the check can be
    made at that element — and then §8's conclusion is, syntactically, the
    [P] the certificate is stated at.  Both halves below are one [exact]
    each: THAT is the "batch 2 is mechanical" claim, discharged. *)

(** *** 9a. The three certificates, at the fetch element this file produces. *)

Lemma wcert_load_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akl : akinfo) (ea : Arch.pa) :
  ak_coh akl = false ->
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEread akl ea 4]))
    (wQ_load ea).
Proof. intros Hcoh. exact (wcert_load cid pc wak_plain pc 4 akl ea Hcoh). Qed.

Lemma wcert_store_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  wstep_cert cid pc
    (wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEwrite akw ea 4 v]))
    (wQ_store (Some cid) ea v).
Proof. exact (wcert_store cid pc wak_plain pc 4 akw ea v). Qed.

Lemma wcert_amo_aq_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true -> ak_latest akw = true ->
  wstep_cert cid pc
    (wP_eff (Some cid)
       ([WEread wak_plain pc 4] ++ [WEread aka ea 4; WEwrite akw ea 4 v]))
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync Hlat.
  exact (wcert_amo_aq cid pc wak_plain pc 4 aka akw ea v Hcoh Hsync Hlat).
Qed.

(** ... and the PIN form at the same fetch element — what the invariant-form
    lock leaf's slot-in check consumes ([[a] ++ [b; c]] IS [[a; b; c]], so one
    [exact]). *)
Lemma wcert_amo_aq_pin_base4 (cid : nat) (pc : SailStdpp.Values.mword 64)
    (aka akw : akinfo) (ea : Arch.pa) (v : bv 32) :
  ak_coh aka = false -> ak_sync aka = true -> ak_latest akw = true ->
  wstep_cert cid pc
    (wP_eff_pin (Some cid)
       ([WEread wak_plain pc 4] ++ [WEread aka ea 4; WEwrite akw ea 4 v]))
    (wQ_amo_aq (Some cid) ea v).
Proof.
  intros Hcoh Hsync Hlat.
  exact (wcert_amo_aq_pin cid pc wak_plain pc 4 aka akw ea v Hcoh Hsync Hlat).
Qed.

(** *** 9b. …and the recipe at the same [es], for the LOAD shape.

    The whole body is [exact (wP_eff_of_leaf_base …)]: §8's conclusion is the
    certificate's [P] with [es_x := [WEread akl ea 4]], on the nose, because
    [[a] ++ [b]] IS [[a; b]].  No adapter, no [app] lemma, no peeling. *)
Lemma wP_load_of_leaf_base
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (akl : akinfo) (ea : Arch.pa)
    (D : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode w) dst = true ->
  exec (ext_decode w) dst = Some (i, dst) ->
  is_lpad_instruction i = false ->
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 4))
       = Some (RETIRE_SUCCESS, s_exec, [WEread akl ea 4])
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid) ([WEread wak_plain pc 4] ++ [WEread akl ea 4]) σ.
Proof. exact (wP_eff_of_leaf_base cid σ W pc w i _ D dst). Qed.

(* ====================================================================== *)
(** ** 10. Soundness check *)

Print Assumptions exec_eff_fetch_done.
Print Assumptions exec_eff_fetch_flat_base4.
Print Assumptions wP_eff_of_leaf_base.
Print Assumptions wP_load_of_leaf_base.

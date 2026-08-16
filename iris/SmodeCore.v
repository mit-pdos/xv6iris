(* SmodeCore.v -- the S-mode CORE infrastructure, mirroring the M-mode design
   of InstrBytes.v (K1 of the kernelvec effort).

   Contents:
   - dispatchInterrupt = None in Supervisor mode (getPendingSet keystone +
     the iris bridge [dispatchInterrupt_none_S_from_regs]);
   - privilege-generic run_hart_active progress lemmas (F_Base + RVC), with
     the post-fetch state THREADED (s_f may differ from s: a TLB-filling
     fetch is a state change);
   - S-mode PMP (TOR entry-0 grant: X for fetch, R for the PTE read);
   - S-mode instruction-fetch memory reads (widths 2 / 4) + the 8-byte PTE
     read of the page walk;
   - Sv39 instruction-fetch translation of an in-RAM virtual address through
     the kvmmake-faithful all-4KB kernel page table (KptPt.v): TLB HIT at the
     vpn's OWN 4KB leaf entry, or MISS (empty or foreign-entry slot) + the
     3-level page WALK (root[2] -> l1_dram[vpn1] -> l0[vpn0], all owned by
     [kpt_bytes]), filling the slot with [kpt_tlb_ent root_ppn (svpn_of va)];
   - [translate_chunk_ram_gen] -- translate one 16-bit fetch chunk over a
     [tlb_consistent P] TLB (geometry derived from the owned [addr_is_ram]);
     applied per half, so a page-straddling 4-byte fetch translates each half
     through its OWN vpn (0/1/2 slots filled), plus the state-polymorphic
     [fetch] compositions [exec_fetch_*_S_gen] that thread the translations;
   - [smode_config dq] -- the S-mode ambient-configuration bundle (mirror of
     InstrBytes' [mmode_config]) + unbundle/rebuild/split/combine;
   - [fetch_from_instr_bytes_s_consistent] -- the unified S-mode fetch over the
     [instr_bytes] footprint and a consistent TLB (the Sv39 kernel map is
     identity on kernel text, so the physical window equals the virtual pc
     numerically); its final TLB is an existential [tlbvec2] that stays
     [tlb_pt_consistent];
   - [wp_exec_step_decode_execute_inv_priv] -- the privilege-generic,
     fetch-state-threading decode/execute step engine;
   - [wp_instr_s_tlbinv] -- the unified S-mode step engine (opens [tlb_inv],
     drives the consistent fetch, re-seals the invariant). *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
(* [ret_pc] & the shared mword identities are used pervasively downstream. *)
Require Export RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import WpGprCsrwCommon.
Require Export SmodePte Pt4kWalk KptPt.
Require Import KMap.   (* kmap_static_claims, extracted from [hw_config] below *)
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. dispatchInterrupt = None in Supervisor mode.                        *)
(*    Keystone: [exec_getPendingSet_supervisor_none] -- with the S         *)
(*    extension enabled, no pending set is returned when                   *)
(*    mie & ~mideleg = 0 (nothing M-destined pending-enabled: xv6 delegates *)
(*    everything it enables) and mstatus.SIE = 0 (S-level interrupts       *)
(*    globally off inside the handler).                                    *)
(* ===================================================================== *)

Lemma and_vec_zeros64_r (x : mword 64) : and_vec x (zeros' 64) = zeros' 64.
Proof.
  cbv [and_vec word_binop with_word' with_word]. unfold MachineWord.MachineWord.and.
  apply bv_eq. rewrite bv_and_unsigned.
  assert (H0 : bv_unsigned (zeros' 64) = 0) by reflexivity. rewrite H0. apply Z.land_0_r.
Qed.

(* read_mip succeeds (any value) given the S-extension is enabled. *)
Lemma exec_read_mip_some_S (s : mstate) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exists v, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
Proof.
  intro HES.
  assert (Hext : exists ev, exec (external_interrupts_pending tt) s = Some (ev, s)).
  { unfold external_interrupts_pending.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
    rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)). eexists. apply exec_returnm. }
  destruct Hext as [ev Hext].
  unfold read_mip. cbn match. eexists.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hext). apply exec_returnm.
Qed.

Lemma exec_getPendingSet_supervisor_none (s : mstate) (mie_v mideleg_v mstatus_v : mword 64) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mideleg_v ->
  register_lookup mstatus s.(sregs) = mstatus_v ->
  and_vec mie_v (not_vec mideleg_v) = zeros' 64 ->
  eq_vec (_get_Mstatus_SIE mstatus_v) ('b"1") = false ->
  exec (getPendingSet Supervisor) s = Some (None, s).
Proof.
  intros HES Hmie Hmdl Hms Hand0 HSIE.
  destruct (exec_read_mip_some_S s HES) as [mipv Hmip].
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq Supervisor Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Machine) s)).
      change (generic_eq Supervisor Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User)) with true.
    apply exec_returnm. }
  assert (HsIEf : exec (or_boolM
            (and_boolM (returnM (generic_eq Supervisor Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Supervisor User))) s
                = Some (false, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Supervisor) s)).
      change (generic_eq Supervisor Supervisor) with true. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
      rewrite Hms. rewrite HSIE.
      apply exec_returnm. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq Supervisor User) with false. apply exec_returnm. }
  (* [getPendingSet] reads mideleg only under [currentlyEnabled Ext_S] now (it
     substitutes zeros otherwise) and reads mie twice; there is no guard/assert
     ahead of it any more. *)
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ Hmip).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIEf).
  rewrite Hmie.
  rewrite Hmdl.
  rewrite Hand0.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false).
  { vm_compute. reflexivity. }
  rewrite Hnq.
  cbn [andb].
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_none_S (s : mstate) :
  exec (getPendingSet Supervisor) s = Some (None, s) ->
  exec (dispatchInterrupt Supervisor) s = Some (None, s).
Proof.
  intros Hgp. unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ Hgp). cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* 2. Privilege-generic run_hart_active progress, with the post-fetch     *)
(*    state THREADED (a TLB-filling fetch changes state: fetch s = (r,s_f) *)
(*    with s_f possibly ≠ s; decode/execute then run at s_f).  With        *)
(*    s_f := s these are the state-preserving (TLB-hit / M-mode) variants. *)
(* ===================================================================== *)

Lemma exec_hart_active_progress_base_gen
    (priv : Privilege) (s s_f s_x : mstate) (w : mword 32) (instr : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Base w, s_f) ->
  exec (ext_decode w) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction instr = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 4)) = Some (resf, s_x) ->
  (match resf with ExecuteAs _ => False | _ => True end) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad HpcF Hexec Hnotexec.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_bind execR_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  unfold and_boolM.
  rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
  rewrite execR_returnR. cbn match. cbn match.
  rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
  rewrite execR_liftR Hexec. cbn match. cbn match.
  rewrite execR_bind.
  destruct resf; cbn in Hnotexec; try contradiction;
    cbn match; rewrite execR_returnR; cbn match; rewrite execR_returnR; reflexivity.
Qed.

Lemma exec_hart_active_progress_RVC_gen
    (priv : Privilege) (s s_f s_x : mstate) (h : mword 16) (instr other : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_RVC h, s_f) ->
  exec (ext_decode_compressed h) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (currentlyEnabled Ext_Zca) s_f = Some (true, s_f) ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 2))
    = Some (ExecuteAs other, set_reg s_f nextPC (add_vec_int pc 2)) ->
  exec (execute other) (set_reg s_f nextPC (add_vec_int pc 2)) = Some (resf, s_x) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad HpcF Hzca Hexec Hexec2.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_bind execR_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR exec_is_landing_pad Hlpad. cbn match.
  rewrite execR_bind execR_liftR Hzca. cbn match.
  rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
  rewrite execR_liftR Hexec. cbn match. cbn match.
  rewrite execR_bind execR_liftR Hexec2. cbn match.
  rewrite execR_returnR. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* 3. S-mode PMP: the TOR entry-0 grant.  Unlike M-mode (where an unlocked *)
(*    entry grants unconditionally), Supervisor accesses must pass the RWX *)
(*    permission check of the matching entry: X for a fetch, R for the PTE *)
(*    read of the page walk.                                               *)
(* ===================================================================== *)

(* S-mode PMP TOR-entry-0 grants ([exec_pmpMatchAddr_TOR_match],
   [exec_pmpCheck_supervisor_grant](_load), [pmp_tor0_pte_read]): MOVED to
   SmodePte.v. *)

Lemma exec_checked_mem_read_ram_2_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt Supervisor
                        (Physaddr addr) 2 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 2 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (read_kind_of_flags false false false) s
                  = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * 2) = addr)
      by (change (0 * 2)%Z with 0%Z; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_supervisor_grant addr 2 s HA Hord Hrange HX)). cbn beta.
    cbn match.
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_16.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_returnR. reflexivity.
Qed.

Lemma exec_mem_read_fetch_2_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2_S with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_ram_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec (check_pma_with_pmp_priority (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 4 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 4 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (read_kind_of_flags _ _ false) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    assert (Havi : add_vec_int addr (0 * 4) = addr)
      by (change (0 * 4)%Z with 0%Z; apply avi0).
    rewrite Havi.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpCheck_supervisor_grant addr 4 s HA Hord Hrange HX)). cbn beta.
    cbn match.
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_32.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_returnR. reflexivity.
Qed.

Lemma exec_mem_read_fetch_4_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_4_S with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* 5. Sv39 translation of a kernelvec-page address.                       *)
(*    The kernel's identity map covers [0x80000000,0xC0000000) by a single *)
(*    1GB superpage leaf PTE [pte_super] at root index 2.  Kernelvec's     *)
(*    code page is VPN 0x80005 (= [kv_vpn]); tlb_hash 39 0x80005 = 5, so    *)
(*    both the walk-installed superpage entry and every later hit live at   *)
(*    TLB index 5.                                                          *)
(* ===================================================================== *)

(* [exec_translationMode_S_sv39]: MOVED to SmodePte.v. *)

(* The kernelvec code-page VPN and the identity-superpage PTE. *)
(* leaf PTE mapping [0x80000000,0xC0000000) identically: ppn field 0x80000
   (1GB-aligned), flags D A _ _ X W R V = 0xCF (U=0). *)
(* The PTE physical address the Sv39 walk computes for a kernelvec-page vaddr
   at level 2: pte_paddr rp = (rp << 12) | (VPN[2] << 3). *)

(* The superpage TLB entry the walk installs at hash index 5. *)

(* (Local copies of two bitvector helpers that live downstream in WpSmodeGpr.) *)


(* The (symbolic) Sv39 output ppn for a 1GB superpage leaf with PTE ppn
   0x80000, for ANY in-region vpn: concat(0x80000[43:18], vpn[17:0]); the
   identity within the superpage.  (Local copy of WpSmodeGpr's sdata_ppn_out,
   which lives downstream of this file.) *)

(* [tlb_get_ppn] on the identity-superpage entry equals [sfetch_ppn_out].
   (Local copy of WpSmodeGpr's tlb_get_ppn_pw.) *)

(* ===================================================================== *)
(* Local RAM-geometry lemmas needed to DERIVE the S-mode fetch geometry    *)
(* from an owned instruction points-to (addr_is_ram), instead of taking it *)
(* as fetch-geometry premises.  (Local copies of the                       *)
(* WpSmodeGpr/WpGprRvcTor lemmas, which live downstream of this file; the   *)
(* others -- ram_canonical/ram_svpn2/ram_mask/ram_mvpn/svpn_of_unsigned -- *)
(* are already in RiscvExtras.)                                            *)
(* The W-byte fetch access at a RAM address matches TOR entry 0: both ends in
   RAM, hence in [0, pmpaddr0*4) given the coverage fact. *)
Lemma ram_fetch_pmp (a pmpaddr0 : mword 64) (w : Z) (k : nat) :
  0 < w ->
  (w <= 8)%Z ->
  uint (to_bits 64 w) = w ->
  (Z.of_nat k + 1 = w)%Z ->
  addr_is_ram a ->
  addr_is_ram (pa_add a k) ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint a) (uint (to_bits 64 w)) = PMP_Match.
Proof.
  intros Hw0 Hw8 Hwv Hkw Ha Hk Hcov.
  pose proof Ha as [Halo Hahi]. pose proof Hk as [_ Hkhi].
  rewrite (uint_pa_add a k ltac:(unfold ram_base, ram_size in Hahi; lia)) in Hkhi.
  apply (ram_pmp_match_w a pmpaddr0 w Hw0 Hwv Halo ltac:(unfold ram_base, ram_size in *; lia) Hcov).
Qed.

(* The megapage (1GB identity superpage) translate machinery -- hit at
   [pw_tlb_entry], one-PTE walk of [pte_super] -- is GONE: translation now
   goes through the kvmmake-faithful all-4KB kernel page table (KptPt.v /
   Pt4kWalk.v).  See [translate_chunk_ram_gen] below.  *)

(* ===================================================================== *)
(* 6b. The outer S-mode fetch assemblies (TLB hit), one per geometry.     *)
(* ===================================================================== *)

(* SFetchHitOuter (megapage hit-path fetch compositions): DELETED -- the
   unified fetch drives the [_S_gen] compositions below off
   [translate_chunk_ram_gen]. *)

(* ===================================================================== *)
(* 6b. State-polymorphic 2+2 F_Base fetch composition.  The two halfword  *)
(* translations are ABSTRACT (given as [Htrl]/[Htrh]) and may land in      *)
(* DIFFERENT states [s -> s1 -> s2]; no same-page/[svpn] assumption. Both   *)
(* the hit (s1=s2=s) and walk (s1=s2=sf) F_Base_2 lemmas are instances.     *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_2_S_gen
      (va pal pah : mword 64) (w : mword 32) (s s1 s2 : mstate) (regl regh : PMA_Region) :
  let ilo : mword 16 := subrange_vec_dec w 15 0 in
  let ihi : mword 16 := subrange_vec_dec w 31 16 in
  let vah : mword 64 := add_vec_int va 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  (* the two abstract halfword translations, threading s -> s1 -> s2;
     the two halves land in DIFFERENT physical pages [pal]/[pah] *)
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw), s1) ->
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
  (* low halfword mem-read facts, at s1 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pal) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pal) 2 = Some regl ->
  is_aligned_paddr (Physaddr pal) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pal) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pal) 2) s1 = Some (false, s1) ->
  dev_addr pal = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pal j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  (* high halfword mem-read facts, at s2 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
    (uint pah) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr pah) 2 = Some regh ->
  is_aligned_paddr (Physaddr pah) 2 = true ->
  (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_sig (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_htif_readable (Physaddr pah) 2) s2 = Some (false, s2) ->
  dev_addr pah = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s2.(mem) !! (pa_add pah j) = Some (nth_byte ihi j)) ->
  register_lookup cur_privilege s2.(sregs) = Supervisor ->
  isRVC ilo = false ->
  concat_vec ihi ilo = w ->
  exec (fetch tt) s = Some (F_Base w, s2).
Proof.
  intros ilo ihi vah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Htrh
         iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL
         iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH
         HnotRVC Hconcat.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1)).
  { rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. }
  (* first halfword: fetch_bytes at [s] that lands in [s1] *)
  assert (Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pal, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pal, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pal) 2 false false false)) s1
           = Some (inr (Ok ilo), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA pal regl ilo s1
                   iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* second halfword: fetch_bytes at [s1] that lands in [s2] *)
  assert (Hfb2h : exec (fetch_bytes va vah 2) s1 = Some (@FetchBytes_Success 2 ihi, s2)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) s1
           = Some (inr (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw)), s2))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
        rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pah, PBMT_PMA) s2)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pah) 2 false false false)) s2
           = Some (inr (Ok ihi), s2))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA pah regh ihi s2
                   iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  (* assemble the outer fetch: PC read at s pre-checks + low read; PC read at s1
     before the high read *)
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
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
  cbv iota beta. rewrite execR_returnR_fwd. cbn match.
  rewrite Hconcat. reflexivity.
Qed.

(* ===================================================================== *)
(* 6b'. State-polymorphic SINGLE-read fetch compositions.  Each takes an   *)
(* ABSTRACT translation [Htr : translateAddr va s = Some(.., s1)] and the  *)
(* single instruction read at [s1], and yields the whole [fetch] at the    *)
(* result state [s1].  Both the hit ([s1=s]) and walk ([s1=sf]) single-    *)
(* read lemmas are instances.  The PC is read only at [s] (single read).   *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_4_S_gen
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec (fetch tt) s = Some (F_Base w, s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HnotRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
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
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_4_S_gen
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = true ->
  exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
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
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta. rewrite HisRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_2_S_gen
      (va pa : mword 64) (h : mword 16) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 2 = Some region ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 2) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte h j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC h = true ->
  exec (fetch tt) s = Some (F_RVC h, s1).
Proof.
  intros HpcPC HmisaC Hbit0 Hbit1 Hvalign4 Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb2 : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 2 false false false)) s1
           = Some (inr (Ok h), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA pa region h s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
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
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2).
  cbv iota beta. rewrite HisRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* 6c. The S-mode fetch reductions with an EMPTY TLB slot 5: the page     *)
(* walk reads the PTE (at the pre-fetch state s) and FILLS the TLB; the   *)
(* instruction bytes are then read at the filled state sf.  Single-read   *)
(* geometries only (F_Base 4-aligned / F_RVC both alignments); the 2+2    *)
(* F_Base read with a mid-fetch fill is left for K2.                      *)
(* ===================================================================== *)

(* SFetchWalk (megapage walk-path fetch compositions): DELETED (same). *)

(* ===================================================================== *)
(* 7. smode_config -- the ambient resources a straight-line S-mode kernel *)
(* instruction reads and preserves (mirror of InstrBytes' mmode_config).  *)
(* [satp0] is a PARAMETER: the kernelvec proofs need the CONCRETE Sv39    *)
(* root ppn for the page walk, so the satp VALUE stays visible.           *)
(* ===================================================================== *)

(* ghost tracking of the [mstatus.SIE] bit: [smode_config] holds one half tied
   to the actual flag; functions that observe/save SIE (push_off/pop_off via
   acquire/release) own the other half.  Mirrors [lockG] in WpLock.v. *)
(* The SIE ghost's BOOT value, named here (a file that has the ['b"..."]
   notation) because the SIE ghost is canonical per hart
   ([RiscvPtsto.sie_name]), so RiscvAdequacy mints all three of its pieces per
   hart -- and RiscvAdequacy must NOT [Import SailStdpp.Values] (that leaks
   instances breaking its Iris proofs), so it cannot spell ['b"0"] itself. *)
Definition sie_bit_off : mword 1 := 'b"0".

Class sieG (Σ : gFunctors) := SieG { sie_inG :: ghost_varG Σ (mword 1) }.
Definition sieΣ : gFunctors := #[ ghost_varΣ (mword 1) ].
Global Instance subG_sieΣ {Σ} : subG sieΣ Σ -> sieG Σ.
Proof. solve_inG. Qed.

Section SmodeCoreIris.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The static kernel-mapping claims (KMap.v), off the ambient config bundle.
     [hw_config] is persistent, so this consumes nothing.  It is THE interface
     by which a proof that holds the config -- directly, or through [sconf] /
     [sie_cap_gpr] (IntrDefs.v lifts this lemma to both) -- reaches the ↦ₚ⇄↦ₘ
     tier bridges outside a leaf.  Use it instead of destructing [hw_config]'s
     eighteen conjuncts by position. *)
  Lemma hw_config_kmap_claims : hw_config -∗ kmap_static_claims.
  Proof.
    iIntros "H".
    iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk)".
    iExact "Hk".
  Qed.

  (* [senvcfg]'s own persistent conjunct, off the ambient config bundle --
     [hw_config_kmap_claims]'s twin, same reason: a proof holding [hw_config]
     (directly, or through [sconf]/[sie_cap_gpr]) reaches this without
     destructuring [hw_config]'s eighteen conjuncts by position, and without
     losing its own copy of [hw_config] in the process (both persistent). *)
  Lemma hw_config_senvcfg : hw_config -∗ senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64).
  Proof.
    iIntros "H".
    iDestruct "H" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & Hs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iExact "Hs".
  Qed.

  (* The ambient S-mode machine configuration, keyed by the SIE ghost name [γ].
     Bundles the config registers + all the pure config facts an S-mode kernel
     instruction relies on (SIE=0, MPRV=0, SXL, mie∧¬mdv=0, PBMTE, MXR=0, PMM
     disabled, LPE=0, FIOM=0, and the SIE-clear legalize fixpoint), and ties a
     half of [γ] to the live [mstatus.SIE] bit. *)
  Definition smode_config (γ : gname) (dq : dfrac) : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ{ dq } Supervisor ∗
     (∃ mstatus0 : mword 64,
        mstatus ↦ᵣ{ dq } mstatus0 ∗
        ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) ∗
        ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ ∗
        ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
        ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝ ∗
        ⌜ eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ⌝ ∗
        ⌜ legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ⌝) ∗
     (∃ mie_v mdv0 : mword 64,
        mie ↦ᵣ{ dq } mie_v ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
     (∃ menvcfg0 : mword 64,
        menvcfg ↦ᵣ{ dq } menvcfg0 ∗
        ⌜ eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ⌝ ∗
        ⌜ pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ⌝ ∗
        ⌜ bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ⌝ ∗
        ⌜ eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ⌝ ∗
        ⌜ menvcfg0 = MENVCFG_S ⌝))%I.

  (* unbundle: expose the raw cells + the ghost half + the pure facts. *)
  Lemma smode_config_unbundle (γ : gname) (dq : dfrac) :
    smode_config γ dq -∗
    hw_config ∗ minstret_inv ∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{ dq } Supervisor ∗
    (∃ mstatus0 : mword 64,
       mstatus ↦ᵣ{ dq } mstatus0 ∗
       ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) ∗
       ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ ∗
       ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
       ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝ ∗
       ⌜ eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ⌝ ∗
       ⌜ legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ⌝) ∗
    (∃ mie_v mdv0 : mword 64,
       mie ↦ᵣ{ dq } mie_v ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
       ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
    (∃ menvcfg0 : mword 64,
       menvcfg ↦ᵣ{ dq } menvcfg0 ∗
       ⌜ eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ⌝ ∗
       ⌜ pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ⌝ ∗
       ⌜ bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ⌝ ∗
       ⌜ eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ⌝ ∗
       ⌜ menvcfg0 = MENVCFG_S ⌝).
  Proof. iIntros "H". iExact "H". Qed.

  (* rebuild from raw cells + the ghost half + the pure facts (inverse). *)
  Lemma smode_config_rebuild (γ : gname) (dq : dfrac) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    legalize_sstatus_val mstatus0 (sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    smode_config γ dq.
  Proof.
    iIntros (HSIE HMPRV HSXL HMXR Hleg Hmie HPBMTE Hpmm Hlpe Hfiom Hmenvval)
            "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv".
    iFrame "Hhw Hinv Hhs Hpriv".
    iSplitL "Hms Hsie".
    { iExists mstatus0. iFrame "Hms Hsie". iPureIntro. repeat split; assumption. }
    iSplitL "Hmie Hmdl".
    { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmie. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption.
  Qed.

  (* =================================================================== *)
  (* Fraction choreography (the wp_start): full raw cells <->     *)
  (* smode_config(1/2) + retained halves with the values pinned outside. *)
  (* Shared by every S-mode function that calls mycpu (kernelvec,        *)
  (* push_off, pop_off); lives here beside smode_config_split/rebuild.   *)
  (* =================================================================== *)
  Lemma kv_cfg_split (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    smode_config γ (DfracOwn (1/2)) ∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor ∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 ∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v ∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 ∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0.
  Proof.
    iIntros (HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0)
      "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iDestruct "Hmie" as "[Hmie1 Hmie2]".
    iDestruct "Hmdl" as "[Hmdl1 Hmdl2]".
    iDestruct "Hmenv" as "[Hmenv1 Hmenv2]".
    iSplitL "Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1".
    { iApply (smode_config_rebuild γ (DfracOwn (1/2)) mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                with "Hhw Hinv Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1"). }
    iFrame.
  Qed.

  Lemma kv_cfg_recombine (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    smode_config γ (DfracOwn (1/2)) -∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor -∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 -∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v -∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 -∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0 -∗
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ Supervisor ∗
     mstatus ↦ᵣ mstatus0 ∗
     ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0).
  Proof.
    iIntros "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(_ & _ & Hhs1 & Hpriv1 & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (ms') "(Hms1 & Hsie & _ & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hms1 Hms2") as %->.
    iDestruct "Hmieb" as (mie' mdv') "(Hmi1 & Hmd1 & _)".
    iDestruct (reg_pointsto_agree with "Hmi1 Hmie2") as %->.
    iDestruct (reg_pointsto_agree with "Hmd1 Hmdl2") as %->.
    iDestruct "Hmenvb" as (menv') "(Hme1 & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hme1 Hmenv2") as %->.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iCombine "Hmi1 Hmie2" as "Hmie".
    iCombine "Hmd1 Hmdl2" as "Hmdl".
    iCombine "Hme1 Hmenv2" as "Hmenv".
    iFrame.
  Qed.



  (* dispatchInterrupt = None in S-mode, off owned (dfrac-generic) cells:
     misa.S (hw_config), the no-M-destined-pending mie/mideleg fact, and
     mstatus.SIE = 0. *)
  Lemma dispatchInterrupt_none_S_from_regs
      (σ : mstate) (misa0 mstatus0 mie_v mdv0 : mword 64)
      {dqm dqs dqi dqd : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    mstate_interp σ -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv0 -∗
    ⌜ exec (dispatchInterrupt Supervisor) σ = Some (None, σ) ⌝.
  Proof.
    iIntros (HmisaS Hmm HSIE) "[Hreg Hmem] Hmisa Hms Hmie Hmdl".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmie")  as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl")  as %Lmdl.
    iPureIntro.
    apply exec_dispatchInterrupt_none_S.
    apply (exec_getPendingSet_supervisor_none σ mie_v mdv0 mstatus0).
    - rewrite (exec_currentlyEnabled_S σ). rewrite Lmisa. rewrite HmisaS. reflexivity.
    - exact Lmie.
    - exact Lmdl.
    - exact Lms.
    - exact Hmm.
    - exact HSIE.
  Qed.

  (* =================================================================== *)
  (* 8. fetch_from_instr_bytes_s -- the S-mode analogue of InstrBytes'    *)
  (* fetch_from_instr_bytes: given state_interp, PC and the S-mode fetch  *)
  (* configuration (Supervisor privilege, Sv39 satp, the identity-        *)
  (* superpage TLB HIT at index 5, TOR PMP grants, PMA/htif/misa), and    *)
  (* the SAME [instr_bytes pc r] footprint as M-mode (the kernel map is   *)
  (* identity on kernel text), executing [fetch] yields exactly [r] with  *)
  (* NO state change.                                                     *)
  (* =================================================================== *)

  (* =================================================================== *)
  (* 9. The privilege-generic decode/execute step engine, with the        *)
  (* post-fetch state THREADED: the caller supplies fetch = Some (r, σf)  *)
  (* (σf = σ on a TLB hit; σf = the TLB-filled state on a walk), decode   *)
  (* at σf, and the execute obligations from σf.  The M-mode              *)
  (* wp_exec_step_decode_execute_inv (semantically) the p := Machine,  *)
  (* σf := σ instance.                                                    *)
  (* =================================================================== *)
  Lemma wp_exec_step_decode_execute_inv_priv (p : Privilege) {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ, mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (r : FetchResult) (i : instruction) (σf s_exec : mstate),
         ⌜ register_lookup cur_privilege σ.(sregs) = p ⌝ ∗
         ⌜ exec (dispatchInterrupt p) σ = Some (None, σ) ⌝ ∗
         ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
         ⌜ exec (decode_fetch r) σf = Some (i, σf) ⌝ ∗
         ⌜ eq_vec (register_lookup elp σf.(sregs))
                  (landing_pad_bits_backwards LP_EXPECTED) = false ⌝ ∗
         (match r with
          | F_Base w =>
              ⌜ is_lpad_instruction i = false ⌝ ∗
              ⌜ exec (execute i)
                     (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 4))
                  = Some (RETIRE_SUCCESS, s_exec) ⌝
          | F_RVC h =>
              ⌜ exec (currentlyEnabled Ext_Zca) σf = Some (true, σf) ⌝ ∗
              ∃ other : instruction,
                ⌜ exec (execute i)
                       (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 2))
                    = Some (ExecuteAs other,
                            set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 2)) ⌝ ∗
                ⌜ exec (execute other)
                       (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 2))
                    = Some (RETIRE_SUCCESS, s_exec) ⌝
          | _ => False
          end) ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "Hinv Hhs H".
    iApply (wp_exec_step_hart_active_inv with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iMod ("H" $! σ with "Hsi") as (r i σf s_exec)
      "(%Hpriv & %Hdisp & %Hfetch & %Hdec & %Hlpad & Hrest & Hpc & Hsi_exec & Hcont)".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error: unreachable *) iDestruct "Hrest" as %[].
    - (* F_Base w *)
      iDestruct "Hrest" as "[%Hnotlpad %Hexec]".
      iModIntro. iExists (zero_extend' 32 w), s_exec. iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_base_gen p σ σf s_exec w i
                 (register_lookup PC σf.(sregs)) RETIRE_SUCCESS
                 Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad eq_refl Hexec I). }
      iFrame "Hpc Hsi_exec". iExact "Hcont".
    - (* F_RVC h *)
      iDestruct "Hrest" as "[%Hzca Hrest]".
      iDestruct "Hrest" as (other) "[%Hexec %Hexec2]".
      iModIntro. iExists (zero_extend' 32 h), s_exec. iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_RVC_gen p σ σf s_exec h i other
                 (register_lookup PC σf.(sregs)) RETIRE_SUCCESS
                 Hpriv Hdisp Hfetch Hdec Hlpad eq_refl Hzca Hexec Hexec2). }
      iFrame "Hpc Hsi_exec". iExact "Hcont".
    - (* F_Error: unreachable *) iDestruct "Hrest" as %[].
  Qed.

  (* =================================================================== *)
  (* 10. instr_lift_s -- the S-mode lift of [instr]: the SAME predicate   *)
  (* as M-mode (Task 1 made its decode field privilege-generic); only the *)
  (* consumed resources differ (S-mode translation configuration + the    *)
  (* TLB-hit fact instead of M-mode's identity translation).              *)
  (* =================================================================== *)

  (* =================================================================== *)
  (* 11. wp_instr_s -- the S-mode [wp_instr]: [instr]-driven step engine  *)
  (* on the TLB-HIT path.  Consumes [smode_config] + the pmp/tlb cells +  *)
  (* PC + [instr]; discharges fetch (Sv39 identity hit), decode           *)
  (* (privilege-generic), landing-pad, and dispatchInterrupt; leaves the  *)
  (* caller exactly the execute obligation of [i], branched on [is_rvc].  *)
  (* Everything consumed is handed back to the continuation unchanged.    *)
  (* =================================================================== *)

  (* =================================================================== *)
  (* 12. The PAGE-WALK (TLB-miss) fetch: instead of the TLB-hit fact, own *)
  (* the 8 bytes of the single superpage PTE at [pte_paddr root_ppn]; the *)
  (* fetch WALKS the page table and FILLS the TLB at index 5 (state       *)
  (* change).  Single-read geometries only (F_RVC both alignments +       *)
  (* F_Base 4-aligned); the 2+2 F_Base read with a mid-fetch fill is left *)
  (* for K2 (its second halfword read HITS the just-filled entry).        *)
  (* =================================================================== *)

End SmodeCoreIris.

(* ===================================================================== *)
(* 14. Demos -- the weakened decode + constructor story, end to end.      *)
(* ===================================================================== *)

(* (b) kernelvec's FIRST instruction: the c.addi16sp sp, -448 at 0x800053e0
   (encoding 0x7111; the 4-aligned 4-byte fetch window also covers the
   following c.sdsp's low half 0xe006). *)
Definition kv_h1 : mword 16 := mword_of_int 0x7111.
Definition kv_imm1 : mword 6 :=
  concat_vec (subrange_vec_dec kv_h1 12 12)
    (concat_vec (subrange_vec_dec kv_h1 4 3)
      (concat_vec (subrange_vec_dec kv_h1 5 5)
        (concat_vec (subrange_vec_dec kv_h1 2 2) (subrange_vec_dec kv_h1 6 6)))).

Lemma kv_decode1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed kv_h1) s = Some (C_ADDI16SP kv_imm1, s).
Proof.
  intro HmisaC. rvc_oneshot s HmisaC.
Qed.

Section SmodeDemo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition kv_pc1 : mword 64 := mword_of_int (KernelSyms.kernelvec).

  (* the [instr] constructor for kernelvec's first instruction, from the
     whole-kernel text image -- the SAME predicate the M-mode chains use;
     an S-mode chain lifts it with [instr_lift_s] / steps it with
     [wp_instr_s] instead of [instr_lift] / [wp_instr]. *)
  Lemma kv_instr1 :
    kernel_text -∗ instr kv_pc1 true (ITYPE (caddi16sp_imm kv_imm1, sp, sp, ADDI)).
  Proof.
    mk_rvc KernelSyms.kernelvec kv_h1 kv_pc1
      (ITYPE (caddi16sp_imm kv_imm1, sp, sp, ADDI))
      kv_decode1 exec_execute_C_ADDI16SP.
  Qed.

End SmodeDemo.

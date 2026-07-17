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
Require Import MinstretInv InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import WpGprCsrwCommon.
Require Export SmodePte Pt4kWalk KptPt.
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
  assert (Hguard : exec (or_boolM (currentlyEnabled Ext_S)
                     (bind (read_reg mideleg)
                        (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
                   = Some (true, s)).
  { rewrite (exec_or_boolM_Some _ _ _ _ _ HES). reflexivity. }
  assert (Hae : exec (Defs.assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                = Some (eq_refl, s)).
  { unfold assert_exp'. cbn match. apply exec_returnm. }
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
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ Hguard).
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  rewrite (exec_bind_Some _ _ _ _ _ Hmip).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
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
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant addr 2 s HA Hord Hrange HX)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hdev Hbytes)).
  apply exec_returnM.
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
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant addr 4 s HA Hord Hrange HX)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
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
Definition kv_vpn : mword 27 := mword_of_int 0x80005.
(* leaf PTE mapping [0x80000000,0xC0000000) identically: ppn field 0x80000
   (1GB-aligned), flags D A _ _ X W R V = 0xCF (U=0). *)
Definition pte_super : mword 64 := mword_of_int (Z.lor (Z.shiftl 0x80000 10) 0xCF).
(* The PTE physical address the Sv39 walk computes for a kernelvec-page vaddr
   at level 2: pte_paddr rp = (rp << 12) | (VPN[2] << 3). *)
Definition pte_paddr (rp : mword 44) : mword 64 :=
  zero_extend' 64 (concat_vec rp (concat_vec (subrange_vec_dec kv_vpn 26 18 : mword 9) (zeros' 3 : mword 3))).

(* The superpage TLB entry the walk installs at hash index 5. *)
Definition pw_tlb_entry (rp : mword 44) (asid : mword 16) : TLB_Entry := {|
  TLB_Entry_asid     := asid;
  TLB_Entry_global   := false;
  TLB_Entry_vpn      := mword_of_int 0x80000;
  TLB_Entry_levelMask := mword_of_int 0x3FFFF;
  TLB_Entry_ppn      := mword_of_int 0x80000;
  TLB_Entry_pte      := pte_super;
  TLB_Entry_pteAddr  := Physaddr (pte_paddr rp);
|}.

(* (Local copies of two bitvector helpers that live downstream in WpSmodeGpr.) *)
Lemma bv_swrap_mod (n : N) (z : Z) :
  (bv_swrap n z) mod (bv_modulus n) = z mod (bv_modulus n).
Proof.
  unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l.
  f_equal. ring.
Qed.

Lemma bv_signed_testbit_low (n : N) (b : bv n) (i : Z) :
  0 <= i < Z.of_N n ->
  Z.testbit (bv_signed b) i = Z.testbit (bv_unsigned b) i.
Proof.
  intros Hi.
  unfold bv_signed.
  rewrite <- (Z.mod_pow2_bits_low (bv_swrap n (bv_unsigned b)) (Z.of_N n) i) by lia.
  rewrite <- (Z.mod_pow2_bits_low (bv_unsigned b) (Z.of_N n) i) by lia.
  f_equal.
  pose proof (bv_swrap_mod n (bv_unsigned b)) as Hm.
  unfold bv_modulus in Hm. exact Hm.
Qed.

(* The (symbolic) Sv39 output ppn for a 1GB superpage leaf with PTE ppn
   0x80000, for ANY in-region vpn: concat(0x80000[43:18], vpn[17:0]); the
   identity within the superpage.  (Local copy of WpSmodeGpr's sdata_ppn_out,
   which lives downstream of this file.) *)
Definition sfetch_ppn_out (vpn : mword 27) : mword 44 :=
  concat_vec (subrange_vec_dec (mword_of_int 0x80000 : mword 44) 43 18) (subrange_vec_dec vpn 17 0).

(* [tlb_get_ppn] on the identity-superpage entry equals [sfetch_ppn_out].
   (Local copy of WpSmodeGpr's tlb_get_ppn_pw.) *)
Lemma sfetch_tlb_get_ppn (root_ppn : mword 44) (vpn : mword 27) :
  tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn = sfetch_ppn_out vpn.
Proof.
  unfold tlb_get_ppn, pw_tlb_entry, sfetch_ppn_out.
  cbn [TLB_Entry_levelMask TLB_Entry_ppn].
  cbv [trunc vector_truncate slice or_vec and_vec sign_extend' zero_extend'
       concat_vec subrange_vec_dec Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  cbn.
  change (26 + 18) with 44.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.and MachineWord.zero_extend
       MachineWord.sign_extend MachineWord.concat MachineWord.Z_to_word mword_of_int
       Values.mword_of_int].
  apply bv_eq.
  rewrite bv_extract_unsigned.
  rewrite bv_or_unsigned.
  rewrite bv_and_unsigned.
  rewrite (@bv_zero_extend_unsigned 44 64 _ ltac:(lia)).
  rewrite (@bv_zero_extend_unsigned 45 64 _ ltac:(lia)).
  rewrite bv_sign_extend_unsigned.
  rewrite (@bv_concat_unsigned 26 44 18 _ _ eq_refl).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small (MachineWord.Z_idx 44) 524288
             ltac:(vm_compute; split; [discriminate | reflexivity])).
  rewrite (bv_wrap_small (MachineWord.Z_idx (57 - 12)) 262143
             ltac:(vm_compute; split; [discriminate | reflexivity])).
  rewrite !Z.shiftr_0_r.
  replace (bv_wrap 26 (Z.shiftr 524288 (Z.of_N 18))) with 2 by (vm_compute; reflexivity).
  apply Z.bits_inj'. intros i Hi.
  rewrite (bv_wrap_spec _ _ i Hi).
  rewrite !Z.lor_spec. rewrite Z.land_spec.
  rewrite (Z.shiftl_spec _ _ i Hi).
  rewrite (bv_wrap_spec 18 _ i Hi).
  change 2 with (Z.pow 2 1).
  rewrite (Z.pow2_bits_eqb 1 (i - Z.of_N 18) ltac:(lia)).
  change 262143 with (Z.ones 18).
  rewrite (Z.testbit_ones_nonneg 18 i ltac:(lia) Hi).
  change (MachineWord.Z_idx 44) with 44%N.
  destruct (Z.ltb_spec i 18) as [Hlt | Hge].
  - rewrite (bv_wrap_spec 64 _ i Hi).
    rewrite (bv_signed_testbit_low 27 _ i ltac:(lia)).
    rewrite !andb_true_r.
    destruct (Z.eqb_spec 1 (i - Z.of_N 18)); [lia |].
    cbn [orb].
    rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)).
    rewrite (bool_decide_true (i < Z.of_N 18) ltac:(lia)).
    rewrite (bool_decide_true (i < Z.of_N 64) ltac:(lia)).
    cbn [andb orb]. reflexivity.
  - rewrite !andb_false_r.
    rewrite (bool_decide_false (i < Z.of_N 18) ltac:(lia)).
    cbn [andb orb].
    rewrite !orb_false_r.
    destruct (Z.eqb_spec 1 (i - Z.of_N 18)) as [He | Hne].
    + rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)). reflexivity.
    + rewrite andb_false_r. reflexivity.
Qed.

(* ===================================================================== *)
(* 5a. The TLB / page-table CONSISTENCY INVARIANT (pure part).            *)
(* Every resident TLB entry is THE entry the SATP-installed identity      *)
(* table's walk produces: [pw_tlb_entry root_ppn 0] (the same VALUE at    *)
(* every slot -- the 1GB identity superpage covers all kernel pages, and  *)
(* xv6 runs at asid 0).  S-mode WPs thread this invariant instead of      *)
(* explicit slot contents: a lookup at any slot is either a MISS (walk +  *)
(* fill, which PRESERVES the invariant) or a HIT at exactly this entry.   *)
(* ===================================================================== *)

(* tlb list/vec/hash helpers: MOVED to SmodePte.v. *)

(* THE INVARIANT: every resident entry is a legal 4KB leaf of the kernel
   page table ([KptPt.P_kpt]) -- the kvmmake-faithful all-4KB table (its
   own leaf entry per mapped vpn).  The old megapage form ("every resident
   entry is THE identity-superpage entry") is gone: a walk-fill now
   installs the accessed vpn's OWN 4KB leaf entry. *)
Definition tlb_pt_consistent (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  tlb_consistent (P_kpt root_ppn) tlbvec.

(* preservation: a RAM access's walk-fill installs that vpn's own leaf. *)
Lemma tlb_pt_consistent_fill (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (a : mword 64) :
  addr_is_ram a ->
  tlb_pt_consistent root_ppn tlbvec ->
  tlb_pt_consistent root_ppn
    (vec_update_dec tlbvec (tlb_hash (__id 39) (svpn_of a))
       (Some (kpt_tlb_ent root_ppn (svpn_of a)))).
Proof.
  intros Hram Hc.
  apply tlb_consistent_fill;
    [ apply tlb_hash_range | apply P_kpt_ram; exact Hram | exact Hc ].
Qed.


(* arbitrary-A/D generalization *)
Definition tlb_pt_consistent_ad (adf : kpt_adf) (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  tlb_consistent (P_kpt_ad adf root_ppn) tlbvec.

Lemma tlb_pt_consistent_ad_fill (adf : kpt_adf) (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (a : mword 64) :
  addr_is_ram a ->
  tlb_pt_consistent_ad adf root_ppn tlbvec ->
  tlb_pt_consistent_ad adf root_ppn
    (vec_update_dec tlbvec (tlb_hash (__id 39) (svpn_of a))
       (Some (kpt_tlb_ent_ad adf root_ppn (svpn_of a)))).
Proof.
  intros Hram Hc.
  apply tlb_consistent_fill;
    [ apply tlb_hash_range | apply P_kpt_ad_ram; exact Hram | exact Hc ].
Qed.


(* per-entry existentially-quantified consistency: every resident entry is
   some mapped vpn's leaf with SOME (A, D) pair (KptPt.v §14) *)
Definition tlb_pt_consistent_e (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  tlb_consistent (P_kpt_e root_ppn) tlbvec.

Lemma tlb_pt_consistent_ad_to_e (adf : kpt_adf) (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_pt_consistent_ad adf root_ppn tlbvec ->
  tlb_pt_consistent_e root_ppn tlbvec.
Proof.
  intros Hc i Hi. destruct (Hc i Hi) as [Hn | (e & He & HPe)].
  - left; exact Hn.
  - right. exists e. split; [exact He | exact (P_kpt_ad_to_e adf root_ppn e HPe)].
Qed.

Lemma tlb_pt_consistent_to_e (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_pt_consistent root_ppn tlbvec ->
  tlb_pt_consistent_e root_ppn tlbvec.
Proof.
  intros Hc i Hi. destruct (Hc i Hi) as [Hn | (e & He & HPe)].
  - left; exact Hn.
  - right. exists e. split; [exact He | exact (P_kpt_to_e root_ppn e HPe)].
Qed.

(* a fill with ANY-bits own-vpn entry preserves the existential form *)
Lemma tlb_pt_consistent_e_fill (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (a : mword 64) (ad : bool * bool) :
  addr_is_ram a ->
  tlb_pt_consistent_e root_ppn tlbvec ->
  tlb_pt_consistent_e root_ppn
    (vec_update_dec tlbvec (tlb_hash (__id 39) (svpn_of a))
       (Some (kpt_tlb_ent_b root_ppn (svpn_of a) ad))).
Proof.
  intros Hram Hc.
  apply tlb_consistent_fill; [ apply tlb_hash_range | | exact Hc ].
  exists (svpn_of a), ad.
  split; [ left; exact (ram_svpn_range a Hram) | reflexivity ].
Qed.

(* the bridges to the generic form are now definitional *)
Lemma tlb_pt_consistent_to_generic (root_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_pt_consistent root_ppn tlbvec ->
  tlb_consistent (P_kpt root_ppn) tlbvec.
Proof. exact (fun H => H). Qed.

Lemma tlb_pt_consistent_of_generic (root_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_consistent (P_kpt root_ppn) tlbvec ->
  tlb_pt_consistent root_ppn tlbvec.
Proof. exact (fun H => H). Qed.

(* [set_reg tlb] laws: MOVED to SmodePte.v. *)

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
(* Per-chunk fetch translate for a RAM address, over a CONSISTENT TLB.     *)
(* Wraps [exec_translateAddr_fetch_S]: the [va]-geometry comes from         *)
(* [addr_is_ram a] (via the ram_* lemmas at [svpn_of a] -- NOT any other    *)
(* address's vpn), the hit/walk disjunction from the slot's consistency,    *)
(* and the PTE-read facts (consumed only on a walk).  Yields the result     *)
(* state [s'] together with the bookkeeping the two-chunk composition       *)
(* needs: [s'] is a tlb-only variant of [s] (same mem/other regs), its tlb  *)
(* is still consistent, and [s' = set_reg s tlb (its tlb)] (so nested       *)
(* chunk fills flatten to a single [set_reg]).                              *)
(* ===================================================================== *)
(* Generic per-chunk fetch translate over a [tlb_consistent P] TLB, via   *)
(* the kvmmake-shaped all-4KB kernel page table (KptPt.v).  A RAM fetch    *)
(* either HITS its vpn's own 4KB leaf entry, or MISSES (empty slot, or a   *)
(* foreign resident entry -- e.g. a different RAM page's leaf, or a device *)
(* leaf -- which the walk evicts) and re-walks the 3-level table, filling  *)
(* the slot with [kpt_tlb_ent root_ppn (svpn_of a)].  [HPk] keeps          *)
(* [tlb_consistent P] closed under the fill; [Hdisc] discriminates every   *)
(* legal resident entry: it is this vpn's own entry (a hit) or fails to    *)
(* match this fetch's tag (a walk).                                        *)
(* ===================================================================== *)
Lemma translate_chunk_ram_gen (root_ppn : mword 44) (P : TLB_Entry -> Prop)
    (a satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  register_lookup tlb s.(sregs) = tlbvec ->
  tlb_consistent P tlbvec ->
  P (kpt_tlb_ent root_ppn (svpn_of a)) ->
  (forall e, P e -> e = kpt_tlb_ent root_ppn (svpn_of a) \/
     match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
  addr_is_ram a ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z ->
  pma_allows_pte_read (register_lookup pma_regions s.(sregs)) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  kpt_ok root_ppn ->
  kpt_mem s root_ppn ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  exists s',
    exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s')
    /\ s' = set_reg s tlb (register_lookup tlb s'.(sregs))
    /\ s'.(mem) = s.(mem)
    /\ tlb_consistent P (register_lookup tlb s'.(sregs))
    /\ (forall rr, register_beq rr tlb = false ->
          register_lookup rr s'.(sregs) = register_lookup rr s.(sregs)).
Proof.
  intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hcons HPk Hdisc Hram
         HA Hord HR Hcov Hpma Hhtif HmisaS Hok Hmem Hmenv HPBMTE.
  assert (Hslot : vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a)) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a)) = Some ent /\
        match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) (svpn_of a)) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a))
        = Some (tlb4k_entry (mword_of_int 0) (svpn_of a) (kpt_leaf_ppn (svpn_of a))
                  (mk_pte (kpt_leaf_ppn (svpn_of a)) PTE_RAM) ptea))).
  { destruct (Hcons (tlb_hash (__id 39) (svpn_of a)) (tlb_hash_range (svpn_of a)))
      as [Hn | (e & He & HPe)].
    - left; exact Hn.
    - destruct (Hdisc e HPe) as [-> | Hnm].
      + right; right. exists (kpt_slot0_pa root_ppn (svpn_of a)).
        rewrite He. unfold kpt_tlb_ent, kpt_leaf_pte.
        rewrite (dram_lflags (svpn_of a) (ram_svpn_range a Hram)). reflexivity.
      + right; left. exists e. split; [exact He | exact Hnm]. }
  destruct (exec_translateAddr_kpt_ram (InstructionFetch tt) root_ppn menvcfg0 satp0 a s
              Hok Hmem Hram
              (exec_effectivePrivilege_fetch _ _ s)
              (exec_is_shadow_stack_fetch s)
              kpt_ram_check_fetch
              Hcp HSXL Hsatp Hmode Hppn Hasid HmisaS Hmenv HPBMTE Hhtif
              HA Hord HR Hcov Hpma
              tlbvec Htlb Hslot)
    as (s' & Htr & Hs').
  exists s'. split; [exact Htr|].
  destruct Hs' as [Hs' | Hs'].
  - subst s'.
    split; [ symmetry; apply set_reg_tlb_id | ].
    split; [ reflexivity | ].
    split; [ rewrite Htlb; exact Hcons | ].
    intros rr Hrr. reflexivity.
  - subst s'.
    match goal with |- context[set_reg s ?r ?tv] =>
      assert (Htlbf : register_lookup r (set_reg s r tv).(sregs) = tv) end.
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    split.
    { rewrite Htlbf. reflexivity. }
    split.
    { unfold set_reg; cbn [mem]. reflexivity. }
    split.
    { rewrite Htlbf. apply tlb_consistent_fill;
        [ apply tlb_hash_range | exact HPk | exact Hcons ]. }
    intros rr Hrr. unfold set_reg; cbn [sregs].
    apply irrelevant_register_set. exact Hrr.
Qed.

Lemma translate_chunk_ram_gen_ad (adf : kpt_adf) (root_ppn : mword 44) (P : TLB_Entry -> Prop)
    (a satp0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  register_lookup tlb s.(sregs) = tlbvec ->
  tlb_consistent P tlbvec ->
  P (kpt_tlb_ent_ad adf root_ppn (svpn_of a)) ->
  (forall e, P e -> e = kpt_tlb_ent_ad adf root_ppn (svpn_of a) \/
     match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
  addr_is_ram a ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z ->
  pma_allows_pte_read (register_lookup pma_regions s.(sregs)) ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  kpt_ok root_ppn ->
  kpt_mem_ad adf s root_ppn ->
  fst (adf (svpn_of a)) = true ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  exists s',
    exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s')
    /\ s' = set_reg s tlb (register_lookup tlb s'.(sregs))
    /\ s'.(mem) = s.(mem)
    /\ tlb_consistent P (register_lookup tlb s'.(sregs))
    /\ (forall rr, register_beq rr tlb = false ->
          register_lookup rr s'.(sregs) = register_lookup rr s.(sregs)).
Proof.
  intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hcons HPk Hdisc Hram
         HA Hord HR Hcov Hpma Hhtif HmisaS Hok Hmem Hada Hmenv HPBMTE.
  assert (Hslot : vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a)) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a)) = Some ent /\
        match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) (svpn_of a)) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of a))
        = Some (tlb4k_entry (mword_of_int 0) (svpn_of a) (kpt_leaf_ppn (svpn_of a))
                  (mk_pte (kpt_leaf_ppn (svpn_of a)) (kpt_lflags_ad adf (svpn_of a))) ptea))).
  { destruct (Hcons (tlb_hash (__id 39) (svpn_of a)) (tlb_hash_range (svpn_of a)))
      as [Hn | (e & He & HPe)].
    - left; exact Hn.
    - destruct (Hdisc e HPe) as [-> | Hnm].
      + right; right. exists (kpt_slot0_pa root_ppn (svpn_of a)).
        rewrite He. reflexivity.
      + right; left. exists e. split; [exact He | exact Hnm]. }
  destruct (exec_translateAddr_kpt_ram_ad adf (InstructionFetch tt) root_ppn menvcfg0 satp0 a s
              Hok Hmem Hram
              (exec_effectivePrivilege_fetch _ _ s)
              (exec_is_shadow_stack_fetch s)
              (kpt_check_fetch_ad adf (svpn_of a) (ram_svpn_range a Hram))
              (kpt_upd_fetch_ad adf (svpn_of a) (kpt_leaf_ppn (svpn_of a)) Hada)
              Hcp HSXL Hsatp Hmode Hppn Hasid HmisaS Hmenv HPBMTE Hhtif
              HA Hord HR Hcov Hpma
              tlbvec Htlb Hslot)
    as (s' & Htr & Hs').
  exists s'. split; [exact Htr|].
  destruct Hs' as [Hs' | Hs'].
  - subst s'.
    split; [ symmetry; apply set_reg_tlb_id | ].
    split; [ reflexivity | ].
    split; [ rewrite Htlb; exact Hcons | ].
    intros rr Hrr. reflexivity.
  - subst s'.
    match goal with |- context[set_reg s ?r ?tv] =>
      assert (Htlbf : register_lookup r (set_reg s r tv).(sregs) = tv) end.
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    split.
    { rewrite Htlbf. reflexivity. }
    split.
    { unfold set_reg; cbn [mem]. reflexivity. }
    split.
    { rewrite Htlbf. apply tlb_consistent_fill;
        [ apply tlb_hash_range | exact HPk | exact Hcons ]. }
    intros rr Hrr. unfold set_reg; cbn [sregs].
    apply irrelevant_register_set. exact Hrr.
Qed.

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
      (va : mword 64) (w : mword 32) (s s1 s2 : mstate) (regl regh : PMA_Region) :
  let ilo : mword 16 := subrange_vec_dec w 15 0 in
  let ihi : mword 16 := subrange_vec_dec w 31 16 in
  let vah : mword 64 := add_vec_int va 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  (* the two abstract halfword translations, threading s -> s1 -> s2 *)
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s1) ->
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Ok (Physaddr vah, PBMT_PMA, init_ext_ptw), s2) ->
  (* low halfword mem-read facts, at s1 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint va) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr va) 2 = Some regl ->
  is_aligned_paddr (Physaddr va) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr va) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr va) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr va) 2) s1 = Some (false, s1) ->
  dev_addr va = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  (* high halfword mem-read facts, at s2 *)
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
    (uint vah) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr vah) 2 = Some regh ->
  is_aligned_paddr (Physaddr vah) 2 = true ->
  (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr vah) 2) s2 = Some (false, s2) ->
  exec (within_sig (Physaddr vah) 2) s2 = Some (false, s2) ->
  exec (within_htif_readable (Physaddr vah) 2) s2 = Some (false, s2) ->
  dev_addr vah = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s2.(mem) !! (pa_add vah j) = Some (nth_byte ihi j)) ->
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
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) s1
           = Some (inr (Ok ilo), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA va regl ilo s1
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
           = Some (inr (Ok (Physaddr vah, PBMT_PMA, init_ext_ptw)), s2))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
        rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr vah, PBMT_PMA) s2)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr vah) 2 false false false)) s2
           = Some (inr (Ok ihi), s2))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA vah regh ihi s2
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
      (va : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint va) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr va) 4 = Some region ->
  is_aligned_paddr (Physaddr va) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr va) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr va) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr va) 4) s1 = Some (false, s1) ->
  dev_addr va = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte w j)) ->
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
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w s1
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
      (va : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint va) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr va) 4 = Some region ->
  is_aligned_paddr (Physaddr va) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr va) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr va) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr va) 4) s1 = Some (false, s1) ->
  dev_addr va = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte w j)) ->
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
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w s1
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
      (va : mword 64) (h : mword 16) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint va) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr va) 2 = Some region ->
  is_aligned_paddr (Physaddr va) 2 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr va) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr va) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr va) 2) s1 = Some (false, s1) ->
  dev_addr va = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte h j)) ->
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
           = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) s1
           = Some (inr (Ok h), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2_S PBMT_PMA va region h s1
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
Class sieG (Σ : gFunctors) := SieG { sie_inG :: ghost_varG Σ (mword 1) }.
Definition sieΣ : gFunctors := #[ ghost_varΣ (mword 1) ].
Global Instance subG_sieΣ {Σ} : subG sieΣ Σ -> sieG Σ.
Proof. solve_inG. Qed.

Section SmodeCoreIris.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

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
  (* Fraction choreography (the wp_start recipe): full raw cells <->     *)
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
  (* wp_exec_step_decode_execute_inv is (semantically) the p := Machine,  *)
  (* σf := σ instance.                                                    *)
  (* =================================================================== *)
  Lemma wp_exec_step_decode_execute_inv_priv (p : Privilege) Φ {dq : dfrac} :
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
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hinv Hhs H".
    iApply (wp_exec_step_hart_active_inv Φ with "Hinv Hhs").
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

  (* the walk's memory footprint: EVERY populated slot of the kvmmake-shaped
     all-4KB kernel page table (KptPt.v), plus the pure layout fact
     [kpt_ok].  Layout: root[0]/root[2]; l1_dev[96..128]; l1_dram[0..127];
     the 16386 device leaves (PLIC + UART + VIRTIO, vpns 0xC000..0x10001);
     the 65536 DRAM leaves (vpns 0x80000..0x8FFFF).  *)
  Definition kpt_bytes_body (root_ppn : mword 44) (dq : dfrac) : iProp Σ :=
    (pte_addr_at root_ppn (mword_of_int 0) ↦₈{ dq } mk_pte (kpt_l1_dev root_ppn) PTE_PTR ∗
     pte_addr_at root_ppn (mword_of_int 2) ↦₈{ dq } mk_pte (kpt_l1_dram root_ppn) PTE_PTR ∗
     ([∗ list] k ∈ seq 0 33,
        pte_addr_at (kpt_l1_dev root_ppn) (mword_of_int (96 + Z.of_nat k))
          ↦₈{ dq } mk_pte (kpt_l0_dev root_ppn (Z.of_nat k)) PTE_PTR) ∗
     ([∗ list] j ∈ seq 0 128,
        pte_addr_at (kpt_l1_dram root_ppn) (mword_of_int (Z.of_nat j))
          ↦₈{ dq } mk_pte (kpt_l0_dram root_ppn (Z.of_nat j)) PTE_PTR) ∗
     ([∗ list] n ∈ seq 0 (Z.to_nat 16386),
        kpt_slot0_pa root_ppn (mword_of_int (0xC000 + Z.of_nat n))
          ↦₈{ dq } kpt_leaf_pte (mword_of_int (0xC000 + Z.of_nat n))) ∗
     ([∗ list] n ∈ seq 0 (Z.to_nat 65536),
        kpt_slot0_pa root_ppn (mword_of_int (0x80000 + Z.of_nat n))
          ↦₈{ dq } kpt_leaf_pte (mword_of_int (0x80000 + Z.of_nat n))))%I.

  Definition kpt_bytes (root_ppn : mword 44) (dq : dfrac) : iProp Σ :=
    (⌜ kpt_ok root_ppn ⌝ ∗ kpt_bytes_body root_ppn dq)%I.

  (* the pure memory image of the owned PT bytes, at a state whose heap the
     [gen_heap_interp] governs.  ONE extraction per step; every walk of that
     step consumes the resulting pure [kpt_mem]. *)
  Lemma kpt_bytes_body_mem (root_ppn : mword 44) (dq : dfrac) (σ : mstate) :
    gen_heap_interp σ.(mem) -∗ kpt_bytes_body root_ppn dq -∗ ⌜ kpt_mem σ root_ppn ⌝.
  Proof.
    iIntros "Hm (Hr0 & Hr2 & Hl1dev & Hl1dram & Hdev & Hdram)".
    iDestruct (word_pointsto_bytes with "Hr0") as "Hr0".
    iDestruct (word_pointsto_bytes with "Hr2") as "Hr2".
    iAssert (⌜ kpt_slot_in σ (pte_addr_at root_ppn (mword_of_int 0))
                 (mk_pte (kpt_l1_dev root_ppn) PTE_PTR) ⌝)%I as %H0.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hr0") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ kpt_slot_in σ (pte_addr_at root_ppn (mword_of_int 2))
                 (mk_pte (kpt_l1_dram root_ppn) PTE_PTR) ⌝)%I as %H2.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hr2") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall i : mword 9, 96 <= bv_unsigned i < 129 ->
               kpt_slot_in σ (pte_addr_at (kpt_l1_dev root_ppn) i)
                 (mk_pte (kpt_l0_dev root_ppn (bv_unsigned i - 96)) PTE_PTR) ⌝)%I as %Hdev1.
    { iIntros (i Hi).
      iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned i - 96))
                   (Z.to_nat (bv_unsigned i - 96)) with "Hl1dev") as "Hsl";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      rewrite Z2Nat.id; [| lia].
      replace (96 + (bv_unsigned i - 96)) with (bv_unsigned i) by lia.
      rewrite (mword_of_int_unsigned_9 i).
      iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
      iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall i : mword 9, bv_unsigned i < 128 ->
               kpt_slot_in σ (pte_addr_at (kpt_l1_dram root_ppn) i)
                 (mk_pte (kpt_l0_dram root_ppn (bv_unsigned i)) PTE_PTR) ⌝)%I as %Hdram1.
    { iIntros (i Hi).
      pose proof (bv_unsigned_in_range _ i) as Hir.
      iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned i))
                   (Z.to_nat (bv_unsigned i)) with "Hl1dram") as "Hsl";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      rewrite Z2Nat.id; [| lia].
      rewrite (mword_of_int_unsigned_9 i).
      iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
      iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall vpn : mword 27, kpt_mapped vpn ->
               kpt_slot_in σ (kpt_slot0_pa root_ppn vpn) (kpt_leaf_pte vpn) ⌝)%I as %Hleaf.
    { iIntros (vpn Hv).
      destruct Hv as [ [Hlo Hhi] | [Hlo Hhi] ].
      - iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned vpn - 0x80000))
                     (Z.to_nat (bv_unsigned vpn - 0x80000)) with "Hdram") as "Hsl";
          [rewrite lookup_seq_lt;
             [reflexivity
             | apply (proj1 (Z2Nat.inj_lt (bv_unsigned vpn - 0x80000) 65536
                               ltac:(lia) ltac:(lia))); lia]|].
        rewrite Z2Nat.id; [| lia].
        replace (0x80000 + (bv_unsigned vpn - 0x80000)) with (bv_unsigned vpn) by lia.
        rewrite (mword_of_int_unsigned_27 vpn).
        iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
        iIntros (j Hj).
        iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
          [rewrite lookup_seq_lt; [reflexivity | lia]|].
        iApply (mem_valid with "Hm Hbj").
      - iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned vpn - 0xC000))
                     (Z.to_nat (bv_unsigned vpn - 0xC000)) with "Hdev") as "Hsl";
          [rewrite lookup_seq_lt;
             [reflexivity
             | apply (proj1 (Z2Nat.inj_lt (bv_unsigned vpn - 0xC000) 16386
                               ltac:(lia) ltac:(lia))); lia]|].
        rewrite Z2Nat.id; [| lia].
        replace (0xC000 + (bv_unsigned vpn - 0xC000)) with (bv_unsigned vpn) by lia.
        rewrite (mword_of_int_unsigned_27 vpn).
        iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
        iIntros (j Hj).
        iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
          [rewrite lookup_seq_lt; [reflexivity | lia]|].
        iApply (mem_valid with "Hm Hbj"). }
    iPureIntro. exact (conj H0 (conj H2 (conj Hdev1 (conj Hdram1 Hleaf)))).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Arbitrary-A/D PT footprint: [kpt_bytes] generalized over the        *)
  (* per-leaf A/D assignment [adf] (KptPt.v §12).                        *)
  (* ------------------------------------------------------------------ *)
  Definition kpt_bytes_body_ad (adf : kpt_adf) (root_ppn : mword 44) (dq : dfrac) : iProp Σ :=
    (pte_addr_at root_ppn (mword_of_int 0) ↦₈{ dq } mk_pte (kpt_l1_dev root_ppn) PTE_PTR ∗
     pte_addr_at root_ppn (mword_of_int 2) ↦₈{ dq } mk_pte (kpt_l1_dram root_ppn) PTE_PTR ∗
     ([∗ list] k ∈ seq 0 33,
        pte_addr_at (kpt_l1_dev root_ppn) (mword_of_int (96 + Z.of_nat k))
          ↦₈{ dq } mk_pte (kpt_l0_dev root_ppn (Z.of_nat k)) PTE_PTR) ∗
     ([∗ list] j ∈ seq 0 128,
        pte_addr_at (kpt_l1_dram root_ppn) (mword_of_int (Z.of_nat j))
          ↦₈{ dq } mk_pte (kpt_l0_dram root_ppn (Z.of_nat j)) PTE_PTR) ∗
     ([∗ list] n ∈ seq 0 (Z.to_nat 16386),
        kpt_slot0_pa root_ppn (mword_of_int (0xC000 + Z.of_nat n))
          ↦₈{ dq } kpt_leaf_pte_ad adf (mword_of_int (0xC000 + Z.of_nat n))) ∗
     ([∗ list] n ∈ seq 0 (Z.to_nat 65536),
        kpt_slot0_pa root_ppn (mword_of_int (0x80000 + Z.of_nat n))
          ↦₈{ dq } kpt_leaf_pte_ad adf (mword_of_int (0x80000 + Z.of_nat n))))%I.

  Definition kpt_bytes_ad (adf : kpt_adf) (root_ppn : mword 44) (dq : dfrac) : iProp Σ :=
    (⌜ kpt_ok root_ppn ⌝ ∗ kpt_bytes_body_ad adf root_ppn dq)%I.

  (* the pure memory image of the owned PT bytes, at a state whose heap the
     [gen_heap_interp] governs.  ONE extraction per step; every walk of that
     step consumes the resulting pure [kpt_mem]. *)
  Lemma kpt_bytes_body_mem_ad (adf : kpt_adf) (root_ppn : mword 44) (dq : dfrac) (σ : mstate) :
    gen_heap_interp σ.(mem) -∗ kpt_bytes_body_ad adf root_ppn dq -∗ ⌜ kpt_mem_ad adf σ root_ppn ⌝.
  Proof.
    iIntros "Hm (Hr0 & Hr2 & Hl1dev & Hl1dram & Hdev & Hdram)".
    iDestruct (word_pointsto_bytes with "Hr0") as "Hr0".
    iDestruct (word_pointsto_bytes with "Hr2") as "Hr2".
    iAssert (⌜ kpt_slot_in σ (pte_addr_at root_ppn (mword_of_int 0))
                 (mk_pte (kpt_l1_dev root_ppn) PTE_PTR) ⌝)%I as %H0.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hr0") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ kpt_slot_in σ (pte_addr_at root_ppn (mword_of_int 2))
                 (mk_pte (kpt_l1_dram root_ppn) PTE_PTR) ⌝)%I as %H2.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hr2") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall i : mword 9, 96 <= bv_unsigned i < 129 ->
               kpt_slot_in σ (pte_addr_at (kpt_l1_dev root_ppn) i)
                 (mk_pte (kpt_l0_dev root_ppn (bv_unsigned i - 96)) PTE_PTR) ⌝)%I as %Hdev1.
    { iIntros (i Hi).
      iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned i - 96))
                   (Z.to_nat (bv_unsigned i - 96)) with "Hl1dev") as "Hsl";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      rewrite Z2Nat.id; [| lia].
      replace (96 + (bv_unsigned i - 96)) with (bv_unsigned i) by lia.
      rewrite (mword_of_int_unsigned_9 i).
      iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
      iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall i : mword 9, bv_unsigned i < 128 ->
               kpt_slot_in σ (pte_addr_at (kpt_l1_dram root_ppn) i)
                 (mk_pte (kpt_l0_dram root_ppn (bv_unsigned i)) PTE_PTR) ⌝)%I as %Hdram1.
    { iIntros (i Hi).
      pose proof (bv_unsigned_in_range _ i) as Hir.
      iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned i))
                   (Z.to_nat (bv_unsigned i)) with "Hl1dram") as "Hsl";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      rewrite Z2Nat.id; [| lia].
      rewrite (mword_of_int_unsigned_9 i).
      iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
      iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (mem_valid with "Hm Hbj"). }
    iAssert (⌜ forall vpn : mword 27, kpt_mapped vpn ->
               kpt_slot_in σ (kpt_slot0_pa root_ppn vpn) (kpt_leaf_pte_ad adf vpn) ⌝)%I as %Hleaf.
    { iIntros (vpn Hv).
      destruct Hv as [ [Hlo Hhi] | [Hlo Hhi] ].
      - iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned vpn - 0x80000))
                     (Z.to_nat (bv_unsigned vpn - 0x80000)) with "Hdram") as "Hsl";
          [rewrite lookup_seq_lt;
             [reflexivity
             | apply (proj1 (Z2Nat.inj_lt (bv_unsigned vpn - 0x80000) 65536
                               ltac:(lia) ltac:(lia))); lia]|].
        rewrite Z2Nat.id; [| lia].
        replace (0x80000 + (bv_unsigned vpn - 0x80000)) with (bv_unsigned vpn) by lia.
        rewrite (mword_of_int_unsigned_27 vpn).
        iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
        iIntros (j Hj).
        iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
          [rewrite lookup_seq_lt; [reflexivity | lia]|].
        iApply (mem_valid with "Hm Hbj").
      - iDestruct (big_sepL_lookup _ _ (Z.to_nat (bv_unsigned vpn - 0xC000))
                     (Z.to_nat (bv_unsigned vpn - 0xC000)) with "Hdev") as "Hsl";
          [rewrite lookup_seq_lt;
             [reflexivity
             | apply (proj1 (Z2Nat.inj_lt (bv_unsigned vpn - 0xC000) 16386
                               ltac:(lia) ltac:(lia))); lia]|].
        rewrite Z2Nat.id; [| lia].
        replace (0xC000 + (bv_unsigned vpn - 0xC000)) with (bv_unsigned vpn) by lia.
        rewrite (mword_of_int_unsigned_27 vpn).
        iDestruct (word_pointsto_bytes with "Hsl") as "Hsl".
        iIntros (j Hj).
        iDestruct (big_sepL_lookup _ _ j j with "Hsl") as "Hbj";
          [rewrite lookup_seq_lt; [reflexivity | lia]|].
        iApply (mem_valid with "Hm Hbj"). }
    iPureIntro. exact (conj H0 (conj H2 (conj Hdev1 (conj Hdram1 Hleaf)))).
  Qed.

  Lemma kpt_bytes_body_adf1 (root_ppn : mword 44) (dq : dfrac) :
    kpt_bytes_body_ad kpt_adf1 root_ppn dq ⊣⊢ kpt_bytes_body root_ppn dq.
  Proof.
    unfold kpt_bytes_body_ad, kpt_bytes_body.
    do 5 f_equiv;
      try (apply big_sepL_proper; intros ? ? _; rewrite kpt_leaf_pte_adf1; reflexivity);
      reflexivity.
  Qed.

  Lemma kpt_bytes_adf1 (root_ppn : mword 44) (dq : dfrac) :
    kpt_bytes_ad kpt_adf1 root_ppn dq ⊣⊢ kpt_bytes root_ppn dq.
  Proof.
    unfold kpt_bytes_ad, kpt_bytes.
    rewrite kpt_bytes_body_adf1. reflexivity.
  Qed.


  (* =================================================================== *)
  (* THE AMBIENT PMP CONFIGURATION (Iris bundle).  PMP entry 0 is a TOR   *)
  (* region granting R/W/X, covering all of RAM, and -- together with the *)
  (* PTE-region PMA -- permitting the page-table walk's PTE read.  These  *)
  (* facts are checked on every S-mode fetch (X + the walk's PTE read)    *)
  (* and every data access (R/W + the walk's PTE read); the cells are     *)
  (* READ-ONLY in S-mode, so (like satp / the super-PTE) they are folded  *)
  (* into [tlb_inv] at full fraction, with EXISTENTIAL                     *)
  (* [pmpcfg0]/[pmpaddr00]/[region_pte] -- callers state a single          *)
  (* [tlb_inv] and never mention the PMP machinery.  Engines / data WPs    *)
  (* open this to drive fetch and the data-side walk (deriving any per-    *)
  (* access [pmpRangeMatch] from the folded RAM coverage) and re-seal it.  *)
  (* =================================================================== *)
  Definition pmp_config (root_ppn : mword 44) : iProp Σ :=
    (∃ (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n),
       pmpcfg_n ↦ᵣ pmpcfg0 ∗ pmpaddr_n ↦ᵣ pmpaddr00 ∗
       ⌜ pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ⌝ ∗
       ⌜ zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_read pmar0 ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
       ⌜ (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ⌝)%I.

  (* re-seal [pmp_config] from the raw cells + the ambient facts (used by     *)
  (* engines / data WPs after they open it to drive a fetch / data walk).     *)
  Lemma pmp_config_intro (root_ppn : mword 44)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_read pmar0) ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pmp_config root_ppn.
  Proof.
    intros HA Hord Hpma HX HW HR Hcov. iIntros "Hc Ha".
    iExists pmpcfg0, pmpaddr00. iFrame "Hc Ha". iPureIntro. tauto.
  Qed.

  (* =================================================================== *)
  (* THE TLB/PAGE-TABLE CONSISTENCY INVARIANT (Iris bundle): own the tlb  *)
  (* cell at FULL fraction (fills write it) with SOME consistent          *)
  (* contents.  S-mode WPs take [tlb_inv root_ppn] instead of an explicit *)
  (* tlbvec + slot facts, and hand it back re-established.                *)
  (* =================================================================== *)
  (* SATP is READ-ONLY in S-mode execution and the single super-PTE is read *)
  (* on every walk but never written, so both are folded INTO the invariant *)
  (* at FULL fraction alongside the tlb cell + consistency.  satp0 is now    *)
  (* EXISTENTIAL (its Sv39 mode / asid=0 / ppn=root_ppn facts are all that   *)
  (* matters); [root_ppn] stays the parameter (clients + geometry name it).  *)
  Definition tlb_inv (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_pt_consistent root_ppn tlbvec ⌝ ∗
       kpt_bytes root_ppn (DfracOwn 1) ∗
       pmp_config root_ppn)%I.

  (* introduce from the raw pieces (satp + facts + tlb + consistency + pte + *)
  (* the ambient PMP configuration).                                         *)
  Lemma tlb_inv_intro (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte Hpmp".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpte Hpmp". iPureIntro. tauto.
  Qed.

  (* open: expose satp cell + the three SATP facts + tlb cell + consistency  *)
  (* + the owned super-PTE bytes + the ambient PMP configuration.            *)
  Lemma tlb_inv_open (root_ppn : mword 44) :
    tlb_inv root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_pt_consistent root_ppn tlbvec ⌝ ∗
      kpt_bytes root_ppn (DfracOwn 1) ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

  (* close: re-seal after a read/fill that preserves consistency and does    *)
  (* not change satp / the pte bytes / the PMP configuration.                *)
  Lemma tlb_inv_close (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv root_ppn.
  Proof. apply tlb_inv_intro. Qed.

  (* ------------------------------------------------------------------ *)
  (* Arbitrary-A/D invariant: [tlb_inv] generalized over [adf].          *)
  (* ------------------------------------------------------------------ *)
  Definition tlb_inv_ad (adf : kpt_adf) (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_pt_consistent_ad adf root_ppn tlbvec ⌝ ∗
       kpt_bytes_ad adf root_ppn (DfracOwn 1) ∗
       pmp_config root_ppn)%I.

  (* introduce from the raw pieces (satp + facts + tlb + consistency + pte + *)
  (* the ambient PMP configuration).                                         *)
  Lemma tlb_inv_ad_intro (adf : kpt_adf) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent_ad adf root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes_ad adf root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_ad adf root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte Hpmp".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpte Hpmp". iPureIntro. tauto.
  Qed.

  (* open: expose satp cell + the three SATP facts + tlb cell + consistency  *)
  (* + the owned super-PTE bytes + the ambient PMP configuration.            *)
  Lemma tlb_inv_ad_open (adf : kpt_adf) (root_ppn : mword 44) :
    tlb_inv_ad adf root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_pt_consistent_ad adf root_ppn tlbvec ⌝ ∗
      kpt_bytes_ad adf root_ppn (DfracOwn 1) ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

  (* close: re-seal after a read/fill that preserves consistency and does    *)
  (* not change satp / the pte bytes / the PMP configuration.                *)
  Lemma tlb_inv_ad_close (adf : kpt_adf) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent_ad adf root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes_ad adf root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_ad adf root_ppn.
  Proof. apply tlb_inv_ad_intro. Qed.

  Lemma tlb_inv_adf1 (root_ppn : mword 44) :
    tlb_inv_ad kpt_adf1 root_ppn ⊣⊢ tlb_inv root_ppn.
  Proof.
    assert (Hp : forall v : vec (option TLB_Entry) (2 ^ 6),
              tlb_pt_consistent_ad kpt_adf1 root_ppn v <-> tlb_pt_consistent root_ppn v).
    { intro v. split; intros Hc i Hi; destruct (Hc i Hi) as [Hn | (e & He & HPe)].
      - left; exact Hn.
      - right; exists e; split;
          [exact He | exact (proj1 (P_kpt_adf1 root_ppn e) HPe)].
      - left; exact Hn.
      - right; exists e; split;
          [exact He | exact (proj2 (P_kpt_adf1 root_ppn e) HPe)]. }
    unfold tlb_inv_ad, tlb_inv.
    setoid_rewrite kpt_bytes_adf1.
    setoid_rewrite Hp.
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Existentially-quantified A/D invariant: no assignment is fixed at   *)
  (* the interface; a proof that must EXECUTE opens the existential and  *)
  (* works at the skolem map (per-page bit facts about it are the        *)
  (* model-imposed residue -- see KptPt.v §14).                          *)
  (* ------------------------------------------------------------------ *)
  Definition tlb_inv_e (root_ppn : mword 44) : iProp Σ :=
    (∃ adm : kpt_adf, tlb_inv_ad adm root_ppn)%I.

  Lemma tlb_inv_ad_to_e (adm : kpt_adf) (root_ppn : mword 44) :
    tlb_inv_ad adm root_ppn -∗ tlb_inv_e root_ppn.
  Proof. iIntros "H". iExists adm. iExact "H". Qed.

  Lemma tlb_inv_to_e (root_ppn : mword 44) :
    tlb_inv root_ppn -∗ tlb_inv_e root_ppn.
  Proof.
    iIntros "H". iExists kpt_adf1.
    iApply (tlb_inv_adf1 root_ppn). iExact "H".
  Qed.




  (* =================================================================== *)
  (* Generic TLB/page-table invariant, parametric in the legal-entry set  *)
  (* [P].  [tlb_inv] above is the [P := (= superpage)] instance; the UART  *)
  (* path uses [P := (= superpage) \/ (= uart leaf)], and the eventual     *)
  (* all-4KB kernel uses [P := (fun e => the walk of some vpn yields e)].  *)
  (* Only the [tlb_consistent] clause varies; the satp facts, the owned    *)
  (* super-PTE bytes (still read by every RAM fetch walk), and the PMP     *)
  (* configuration are shared.  Foreign page-table bytes (e.g. the UART    *)
  (* leaf PTEs) are owned by the client WP, not by this invariant.         *)
  (* =================================================================== *)
  Definition tlb_inv_gen (P : TLB_Entry -> Prop) (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_consistent P tlbvec ⌝ ∗
       kpt_bytes root_ppn (DfracOwn 1) ∗
       pmp_config root_ppn)%I.

  Lemma tlb_inv_gen_intro (P : TLB_Entry -> Prop) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_consistent P tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_gen P root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte Hpmp".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpte Hpmp". iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_gen_open (P : TLB_Entry -> Prop) (root_ppn : mword 44) :
    tlb_inv_gen P root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_consistent P tlbvec ⌝ ∗
      kpt_bytes root_ppn (DfracOwn 1) ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma tlb_inv_gen_close (P : TLB_Entry -> Prop) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_consistent P tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_gen P root_ppn.
  Proof. apply tlb_inv_gen_intro. Qed.

  (* arbitrary-A/D generic invariant *)
  Definition tlb_inv_gen_ad (adf : kpt_adf) (P : TLB_Entry -> Prop) (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_consistent P tlbvec ⌝ ∗
       kpt_bytes_ad adf root_ppn (DfracOwn 1) ∗
       pmp_config root_ppn)%I.

  Lemma tlb_inv_gen_ad_intro (adf : kpt_adf) (P : TLB_Entry -> Prop) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_consistent P tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes_ad adf root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_gen_ad adf P root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte Hpmp".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpte Hpmp". iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_gen_ad_open (adf : kpt_adf) (P : TLB_Entry -> Prop) (root_ppn : mword 44) :
    tlb_inv_gen_ad adf P root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_consistent P tlbvec ⌝ ∗
      kpt_bytes_ad adf root_ppn (DfracOwn 1) ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma tlb_inv_gen_ad_close (adf : kpt_adf) (P : TLB_Entry -> Prop) (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_consistent P tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kpt_bytes_ad adf root_ppn (DfracOwn 1) -∗
    pmp_config root_ppn -∗
    tlb_inv_gen_ad adf P root_ppn.
  Proof. apply tlb_inv_gen_ad_intro. Qed.

  (* [tlb_inv] is exactly the [P_kpt] instance of [tlb_inv_gen]. *)
  Lemma tlb_inv_to_gen (root_ppn : mword 44) :
    tlb_inv root_ppn -∗ tlb_inv_gen (P_kpt root_ppn) root_ppn.
  Proof.
    iIntros "H". iDestruct (tlb_inv_open with "H") as (satp0 tlbvec) "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hc & Hpte & Hpmp)".
    iApply (tlb_inv_gen_intro _ root_ppn satp0 tlbvec Hmode Hasid Hppn
              (tlb_pt_consistent_to_generic root_ppn tlbvec Hc) with "Hsatp Htlb Hpte Hpmp").
  Qed.

  Lemma tlb_inv_of_gen (root_ppn : mword 44) :
    tlb_inv_gen (P_kpt root_ppn) root_ppn -∗ tlb_inv root_ppn.
  Proof.
    iIntros "H". iDestruct (tlb_inv_gen_open with "H") as (satp0 tlbvec) "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hc & Hpte & Hpmp)".
    iApply (tlb_inv_intro root_ppn satp0 tlbvec Hmode Hasid Hppn
              (tlb_pt_consistent_of_generic root_ppn tlbvec Hc) with "Hsatp Htlb Hpte Hpmp").
  Qed.

  (* =================================================================== *)
  (* 12b. fetch_from_instr_bytes_s_consistent -- THE UNIFIED (hit-OR-walk, *)
  (* 0/1/2 fills) S-mode fetch over a CONSISTENT TLB.  Each 16-bit chunk    *)
  (* is translated through ITS OWN vpn via [translate_chunk_ram]: the low   *)
  (* half at [svpn_of pc], and -- for a 2-aligned-not-4 32-bit instr -- the *)
  (* high half INDEPENDENTLY at [svpn_of (pc+2)] (a DIFFERENT tlb hash when  *)
  (* [svpn_of (pc+2) <> svpn_of pc], as at the [walkaddr] jal 0x80000ffe:    *)
  (* the high slot may itself be empty and WALK).  No same-page premise.     *)
  (* The result state is [set_reg σ tlb tlbvec2] for a still-consistent      *)
  (* [tlbvec2] (0, 1 or 2 slots filled), threaded via [tlb_pt_consistent_    *)
  (* fill]; the caller (engine) re-seals [tlb_inv] with [tlbvec2].           *)
  (* =================================================================== *)
  Lemma fetch_from_instr_bytes_s_consistent_gen (root_ppn : mword 44) (P : TLB_Entry -> Prop)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    tlb_consistent P tlbvec ->
    (forall a, addr_is_ram a -> P (kpt_tlb_ent root_ppn (svpn_of a))) ->
    (forall a e, addr_is_ram a -> P e ->
       e = kpt_tlb_ent root_ppn (svpn_of a) \/
       match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pma_allows_pte_read pmar0 ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    kpt_bytes root_ppn dqb -∗
    instr_bytes pc r -∗
    ⌜ ∃ tlbvec2, exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
                 ∧ tlb_consistent P tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid Hcons HPk Hdisc HPBMTE HX Hcov HA Hord HR Hpma_pte)
      "[Hreg [Hmem Hdev]] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    (* the kernel-PT layout fact rides inside [kpt_bytes] (folded into
       [tlb_inv]); peel it off together with the owned PT slots. *)
    iDestruct "Hpbytes" as "[%Hok Hpbytes]".
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* the PT's memory image (one extraction; every chunk walk consumes it) *)
    iDestruct (kpt_bytes_body_mem root_ppn dqb σ with "Hmem Hpbytes") as %Hmemσ.
    (* register_lookup forms at σ *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpaddr; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpaddr; exact Hcov).
    assert (Hpma' : pma_allows_pte_read (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma; exact Hpma_pte).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
    assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS0).
    (* the low-chunk translate at pc: reusable across all geometries once we
       have [addr_is_ram pc].  Packaged as a tactic-producing pose. *)
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: single 4-byte read, one chunk *)
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct (translate_chunk_ram_gen root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram3 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 4 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_F_Base_4_S_gen pc w σ s1 region
                      Lpc Hal Htr1 i1HA i1Hord i1range i1HX i1match Hal Hexec0
                      (within_clint_false pc 4 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 4 s1 Hns ltac:(lia))
                      (within_htif_false pc 4 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HnotRVC) as Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
      + (* 2-aligned (not 4): 2+2 read, TWO chunks (low at pc, high at pc+2,
           through svpn_of(pc+2) INDEPENDENTLY -- may be a distinct hash/fill) *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        pose proof (align2_plus2 pc H2al) as Halignh0.
        rewrite fetch_pa_id in Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
        { intros j _. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb2") as %Hr2.
          iPureIntro. unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hraml1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro.
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl; pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch; pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (Hpma0 pc 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Hpma0 (add_vec_int pc 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pc 2) 1)).
        { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3. }
        assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [|exact Hj]. apply Hbytesf. lia. }
        assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [|exact Hj].
          rewrite (Haddr j Hj). apply Hbytesf. lia. }
        (* --- low chunk: translate pc, through svpn_of pc, -> s1 --- *)
        destruct (translate_chunk_ram_gen root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hraml) (fun e HPe => Hdisc pc e Hraml HPe) Hraml
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        (* transfer the config facts to s1 (only tlb changed) *)
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1ms : register_lookup mstatus s1.(sregs) = mstatus0)
          by (rewrite (Hs1reg mstatus ltac:(vm_compute; reflexivity)); exact Lms).
        assert (L1satp : register_lookup satp s1.(sregs) = satp0)
          by (rewrite (Hs1reg satp ltac:(vm_compute; reflexivity)); exact Lsatp).
        assert (L1menv : register_lookup menvcfg s1.(sregs) = menvcfg0)
          by (rewrite (Hs1reg menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (L1pc : register_lookup PC s1.(sregs) = pc)
          by (rewrite (Hs1reg PC ltac:(vm_compute; reflexivity)); exact Lpc).
        assert (L1SXL : _get_Mstatus_SXL (register_lookup mstatus s1.(sregs)) = 'b"10")
          by (rewrite L1ms; exact HSXL0).
        (* s1-level PTE-read facts *)
        assert (H1A' : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (H1ord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (H1R' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HR).
        assert (L1misa : register_lookup misa s1.(sregs) = misa0)
          by (rewrite (Hs1reg misa ltac:(vm_compute; reflexivity)); exact Lmisa).
        assert (H1misaS : eq_vec (_get_Misa_S (register_lookup misa s1.(sregs))) ('b"1") = true)
          by (rewrite L1misa; exact HmisaS0).
        assert (H1cov : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) * 4)%Z)
          by (rewrite L1pmpaddr; exact Hcov).
        assert (H1pma : pma_allows_pte_read (register_lookup pma_regions s1.(sregs)))
          by (rewrite L1pma; exact Hpma_pte).
        pose proof (kpt_mem_eq σ s1 root_ppn Hs1mem Hmemσ) as H1mem.
        (* --- high chunk: translate pc+2, through svpn_of(pc+2), in s1 -> s2.
             The high slot [tlb_hash 39 (svpn_of (pc+2))] gets its OWN
             None-or-Some disjunction from [Hs1cons] (post-low-fill
             consistency) at THAT hash -- it may itself be empty and WALK. --- *)
        destruct (translate_chunk_ram_gen root_ppn P (add_vec_int pc 2) satp0 menvcfg0
                    (register_lookup tlb s1.(sregs)) s1
                    L1priv L1SXL L1satp Hmode Hppn Hasid eq_refl Hs1cons
                    (HPk (add_vec_int pc 2) Hramh) (fun e HPe => Hdisc (add_vec_int pc 2) e Hramh HPe) Hramh
                    H1A' H1ord' H1R' H1cov H1pma L1htif H1misaS Hok H1mem L1menv HPBMTE)
          as (s2 & Htr2 & Hs2eq & Hs2mem & Hs2cons & Hs2reg).
        (* transfer config facts to s2 (via s1) *)
        assert (L2priv : register_lookup cur_privilege s2.(sregs) = Supervisor)
          by (rewrite (Hs2reg cur_privilege ltac:(vm_compute; reflexivity)); exact L1priv).
        assert (L2pmpc : register_lookup pmpcfg_n s2.(sregs) = pmpcfg0)
          by (rewrite (Hs2reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact L1pmpc).
        assert (L2pmpaddr : register_lookup pmpaddr_n s2.(sregs) = pmpaddr00)
          by (rewrite (Hs2reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact L1pmpaddr).
        assert (L2pma : register_lookup pma_regions s2.(sregs) = pmar0)
          by (rewrite (Hs2reg pma_regions ltac:(vm_compute; reflexivity)); exact L1pma).
        assert (L2htif : register_lookup htif_tohost_base s2.(sregs) = None)
          by (rewrite (Hs2reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact L1htif).
        assert (Hs2memσ : s2.(mem) = σ.(mem)) by (rewrite Hs2mem; exact Hs1mem).
        (* low read facts at s1 *)
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1rangeL : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hraml Hraml1 Hcov). }
        assert (i1matchL : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 2 = Some regl)
          by (rewrite L1pma; exact Hml0).
        assert (i1bytesL : forall j : nat, (N.of_nat j < 2)%N ->
                  s1.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j))
          by (rewrite Hs1mem; exact Hbl).
        (* high read facts at s2 *)
        assert (i2HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR)
          by (rewrite L2pmpc; exact HA).
        assert (i2Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false)
          by (rewrite L2pmpaddr; exact Hord).
        assert (i2HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true)
          by (rewrite L2pmpc; exact HX).
        assert (i2rangeH : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
                  (uint (add_vec_int pc 2)) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L2pmpaddr.
          exact (ram_fetch_pmp (add_vec_int pc 2) (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hramh Hramh1 Hcov). }
        assert (i2matchH : matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr (add_vec_int pc 2)) 2 = Some regh)
          by (rewrite L2pma; exact Hmh0).
        assert (i2bytesH : forall j : nat, (N.of_nat j < 2)%N ->
                  s2.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j))
          by (rewrite Hs2memσ; exact Hbh).
        (* compose the two chunks *)
        pose proof (exec_fetch_F_Base_2_S_gen pc w σ s1 s2 regl regh
                      Lpc L1pc HmisaC' Hbit0 Hbit1 Hal Htr1 Htr2
                      i1HA i1Hord i1rangeL i1HX i1matchL Halignl0 Hxl
                      (within_clint_false pc 2 s1 Hncl ltac:(lia))
                      (within_sig_false  pc 2 s1 Hnsl ltac:(lia))
                      (within_htif_false pc 2 s1 L1htif)
                      (addr_is_ram_not_dev _ Hraml) i1bytesL L1priv
                      i2HA i2Hord i2rangeH i2HX i2matchH Halignh0 Hxh
                      (within_clint_false (add_vec_int pc 2) 2 s2 Hnch ltac:(lia))
                      (within_sig_false  (add_vec_int pc 2) 2 s2 Hnsh ltac:(lia))
                      (within_htif_false (add_vec_int pc 2) 2 s2 L2htif)
                      (addr_is_ram_not_dev _ Hramh) i2bytesH L2priv HnotRVC (concat_subranges_id w)) as Hfetch.
        assert (Hs2flat : s2 = set_reg σ tlb (register_lookup tlb s2.(sregs))).
        { rewrite Hs1eq in Hs2eq. rewrite set_reg_tlb_overwrite in Hs2eq. exact Hs2eq. }
        exists (register_lookup tlb s2.(sregs)).
        split; [ rewrite <- Hs2flat; exact Hfetch | exact Hs2cons ].
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window: single 4-byte read, one chunk *)
        iDestruct "Hbytes" as (w) "[%Hsub Hbytes]".
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true) by (rewrite Hsub; exact HisRVC).
        destruct (translate_chunk_ram_gen root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram3 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 4 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_RVC_4_S_gen pc w σ s1 region
                      Lpc Hal Htr1 i1HA i1Hord i1range i1HX i1match Hal Hexec0
                      (within_clint_false pc 4 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 4 s1 Hns ltac:(lia))
                      (within_htif_false pc 4 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HisRVC') as Hfetch.
        rewrite Hsub in Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
      + (* 2-aligned: single 2-byte read, one chunk *)
        destruct (align2_not4_facts pc H2al Hal) as (Halign0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halign0.
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hram1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 2) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct (translate_chunk_ram_gen root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram1 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 2 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte h j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_RVC_2_S_gen pc h σ s1 region
                      Lpc HmisaC' Hbit0 Hbit1 Hal Htr1 i1HA i1Hord i1range i1HX i1match Halign0 Hexec0
                      (within_clint_false pc 2 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 2 s1 Hns ltac:(lia))
                      (within_htif_false pc 2 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HisRVC) as Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
    - (* F_Error *) done.
  Qed.

  (* arbitrary-A/D unified fetch (adf-generic clone) *)
  Lemma fetch_from_instr_bytes_s_consistent_gen_ad (adf : kpt_adf) (root_ppn : mword 44) (P : TLB_Entry -> Prop)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    tlb_consistent P tlbvec ->
    (forall a, addr_is_ram a -> P (kpt_tlb_ent_ad adf root_ppn (svpn_of a))) ->
    (forall a e, addr_is_ram a -> P e ->
       e = kpt_tlb_ent_ad adf root_ppn (svpn_of a) \/
       match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pma_allows_pte_read pmar0 ->
    (forall a, addr_is_ram a -> fst (adf (svpn_of a)) = true) ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    kpt_bytes_ad adf root_ppn dqb -∗
    instr_bytes pc r -∗
    ⌜ ∃ tlbvec2, exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
                 ∧ tlb_consistent P tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid Hcons HPk Hdisc HPBMTE HX Hcov HA Hord HR Hpma_pte Hada)
      "[Hreg [Hmem Hdev]] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    (* the kernel-PT layout fact rides inside [kpt_bytes] (folded into
       [tlb_inv]); peel it off together with the owned PT slots. *)
    iDestruct "Hpbytes" as "[%Hok Hpbytes]".
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* the PT's memory image (one extraction; every chunk walk consumes it) *)
    iDestruct (kpt_bytes_body_mem_ad adf root_ppn dqb σ with "Hmem Hpbytes") as %Hmemσ.
    (* register_lookup forms at σ *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpaddr; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HR).
    assert (Hcov' : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Lpmpaddr; exact Hcov).
    assert (Hpma' : pma_allows_pte_read (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma; exact Hpma_pte).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
    assert (HmisaS' : eq_vec (_get_Misa_S (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaS0).
    (* the low-chunk translate at pc: reusable across all geometries once we
       have [addr_is_ram pc].  Packaged as a tactic-producing pose. *)
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: single 4-byte read, one chunk *)
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct (translate_chunk_ram_gen_ad adf root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ (Hada pc Hram) Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram3 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 4 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_F_Base_4_S_gen pc w σ s1 region
                      Lpc Hal Htr1 i1HA i1Hord i1range i1HX i1match Hal Hexec0
                      (within_clint_false pc 4 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 4 s1 Hns ltac:(lia))
                      (within_htif_false pc 4 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HnotRVC) as Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
      + (* 2-aligned (not 4): 2+2 read, TWO chunks (low at pc, high at pc+2,
           through svpn_of(pc+2) INDEPENDENTLY -- may be a distinct hash/fill) *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        pose proof (align2_plus2 pc H2al) as Halignh0.
        rewrite fetch_pa_id in Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
        { intros j _. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb2") as %Hr2.
          iPureIntro. unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hraml1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro.
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl; pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch; pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (Hpma0 pc 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Hpma0 (add_vec_int pc 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        assert (Hramh1 : addr_is_ram (pa_add (add_vec_int pc 2) 1)).
        { rewrite (Haddr 1%nat ltac:(lia)). change (2 + 1)%nat with 3%nat. exact Hram3. }
        assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [|exact Hj]. apply Hbytesf. lia. }
        assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [|exact Hj].
          rewrite (Haddr j Hj). apply Hbytesf. lia. }
        (* --- low chunk: translate pc, through svpn_of pc, -> s1 --- *)
        destruct (translate_chunk_ram_gen_ad adf root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hraml) (fun e HPe => Hdisc pc e Hraml HPe) Hraml
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ (Hada pc Hraml) Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        (* transfer the config facts to s1 (only tlb changed) *)
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1ms : register_lookup mstatus s1.(sregs) = mstatus0)
          by (rewrite (Hs1reg mstatus ltac:(vm_compute; reflexivity)); exact Lms).
        assert (L1satp : register_lookup satp s1.(sregs) = satp0)
          by (rewrite (Hs1reg satp ltac:(vm_compute; reflexivity)); exact Lsatp).
        assert (L1menv : register_lookup menvcfg s1.(sregs) = menvcfg0)
          by (rewrite (Hs1reg menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (L1pc : register_lookup PC s1.(sregs) = pc)
          by (rewrite (Hs1reg PC ltac:(vm_compute; reflexivity)); exact Lpc).
        assert (L1SXL : _get_Mstatus_SXL (register_lookup mstatus s1.(sregs)) = 'b"10")
          by (rewrite L1ms; exact HSXL0).
        (* s1-level PTE-read facts *)
        assert (H1A' : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (H1ord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (H1R' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HR).
        assert (L1misa : register_lookup misa s1.(sregs) = misa0)
          by (rewrite (Hs1reg misa ltac:(vm_compute; reflexivity)); exact Lmisa).
        assert (H1misaS : eq_vec (_get_Misa_S (register_lookup misa s1.(sregs))) ('b"1") = true)
          by (rewrite L1misa; exact HmisaS0).
        assert (H1cov : (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) * 4)%Z)
          by (rewrite L1pmpaddr; exact Hcov).
        assert (H1pma : pma_allows_pte_read (register_lookup pma_regions s1.(sregs)))
          by (rewrite L1pma; exact Hpma_pte).
        pose proof (kpt_mem_ad_eq adf σ s1 root_ppn Hs1mem Hmemσ) as H1mem.
        (* --- high chunk: translate pc+2, through svpn_of(pc+2), in s1 -> s2.
             The high slot [tlb_hash 39 (svpn_of (pc+2))] gets its OWN
             None-or-Some disjunction from [Hs1cons] (post-low-fill
             consistency) at THAT hash -- it may itself be empty and WALK. --- *)
        destruct (translate_chunk_ram_gen_ad adf root_ppn P (add_vec_int pc 2) satp0 menvcfg0
                    (register_lookup tlb s1.(sregs)) s1
                    L1priv L1SXL L1satp Hmode Hppn Hasid eq_refl Hs1cons
                    (HPk (add_vec_int pc 2) Hramh) (fun e HPe => Hdisc (add_vec_int pc 2) e Hramh HPe) Hramh
                    H1A' H1ord' H1R' H1cov H1pma L1htif H1misaS Hok H1mem
                    (Hada (add_vec_int pc 2) Hramh) L1menv HPBMTE)
          as (s2 & Htr2 & Hs2eq & Hs2mem & Hs2cons & Hs2reg).
        (* transfer config facts to s2 (via s1) *)
        assert (L2priv : register_lookup cur_privilege s2.(sregs) = Supervisor)
          by (rewrite (Hs2reg cur_privilege ltac:(vm_compute; reflexivity)); exact L1priv).
        assert (L2pmpc : register_lookup pmpcfg_n s2.(sregs) = pmpcfg0)
          by (rewrite (Hs2reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact L1pmpc).
        assert (L2pmpaddr : register_lookup pmpaddr_n s2.(sregs) = pmpaddr00)
          by (rewrite (Hs2reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact L1pmpaddr).
        assert (L2pma : register_lookup pma_regions s2.(sregs) = pmar0)
          by (rewrite (Hs2reg pma_regions ltac:(vm_compute; reflexivity)); exact L1pma).
        assert (L2htif : register_lookup htif_tohost_base s2.(sregs) = None)
          by (rewrite (Hs2reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact L1htif).
        assert (Hs2memσ : s2.(mem) = σ.(mem)) by (rewrite Hs2mem; exact Hs1mem).
        (* low read facts at s1 *)
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1rangeL : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hraml Hraml1 Hcov). }
        assert (i1matchL : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 2 = Some regl)
          by (rewrite L1pma; exact Hml0).
        assert (i1bytesL : forall j : nat, (N.of_nat j < 2)%N ->
                  s1.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j))
          by (rewrite Hs1mem; exact Hbl).
        (* high read facts at s2 *)
        assert (i2HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR)
          by (rewrite L2pmpc; exact HA).
        assert (i2Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false)
          by (rewrite L2pmpaddr; exact Hord).
        assert (i2HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true)
          by (rewrite L2pmpc; exact HX).
        assert (i2rangeH : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
                  (uint (add_vec_int pc 2)) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L2pmpaddr.
          exact (ram_fetch_pmp (add_vec_int pc 2) (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hramh Hramh1 Hcov). }
        assert (i2matchH : matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr (add_vec_int pc 2)) 2 = Some regh)
          by (rewrite L2pma; exact Hmh0).
        assert (i2bytesH : forall j : nat, (N.of_nat j < 2)%N ->
                  s2.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j))
          by (rewrite Hs2memσ; exact Hbh).
        (* compose the two chunks *)
        pose proof (exec_fetch_F_Base_2_S_gen pc w σ s1 s2 regl regh
                      Lpc L1pc HmisaC' Hbit0 Hbit1 Hal Htr1 Htr2
                      i1HA i1Hord i1rangeL i1HX i1matchL Halignl0 Hxl
                      (within_clint_false pc 2 s1 Hncl ltac:(lia))
                      (within_sig_false  pc 2 s1 Hnsl ltac:(lia))
                      (within_htif_false pc 2 s1 L1htif)
                      (addr_is_ram_not_dev _ Hraml) i1bytesL L1priv
                      i2HA i2Hord i2rangeH i2HX i2matchH Halignh0 Hxh
                      (within_clint_false (add_vec_int pc 2) 2 s2 Hnch ltac:(lia))
                      (within_sig_false  (add_vec_int pc 2) 2 s2 Hnsh ltac:(lia))
                      (within_htif_false (add_vec_int pc 2) 2 s2 L2htif)
                      (addr_is_ram_not_dev _ Hramh) i2bytesH L2priv HnotRVC (concat_subranges_id w)) as Hfetch.
        assert (Hs2flat : s2 = set_reg σ tlb (register_lookup tlb s2.(sregs))).
        { rewrite Hs1eq in Hs2eq. rewrite set_reg_tlb_overwrite in Hs2eq. exact Hs2eq. }
        exists (register_lookup tlb s2.(sregs)).
        split; [ rewrite <- Hs2flat; exact Hfetch | exact Hs2cons ].
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window: single 4-byte read, one chunk *)
        iDestruct "Hbytes" as (w) "[%Hsub Hbytes]".
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 3)⌝)%I as %Hram3.
        { iDestruct (big_sepL_lookup _ _ 3%nat 3%nat with "Hbytes") as "Hb3".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro.
          unfold pa_add in Hr3 |- *. change (Z.of_nat 3) with 3 in Hr3 |- *. exact Hr3. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true) by (rewrite Hsub; exact HisRVC).
        destruct (translate_chunk_ram_gen_ad adf root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ (Hada pc Hram) Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 4 3
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram3 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 4 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_RVC_4_S_gen pc w σ s1 region
                      Lpc Hal Htr1 i1HA i1Hord i1range i1HX i1match Hal Hexec0
                      (within_clint_false pc 4 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 4 s1 Hns ltac:(lia))
                      (within_htif_false pc 4 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HisRVC') as Hfetch.
        rewrite Hsub in Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
      + (* 2-aligned: single 2-byte read, one chunk *)
        destruct (align2_not4_facts pc H2al Hal) as (Halign0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halign0.
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (pa_add pc 1)⌝)%I as %Hram1.
        { iDestruct (big_sepL_lookup _ _ 1%nat 1%nat with "Hbytes") as "Hb1".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb1") as %Hr1. iPureIntro.
          unfold pa_add in Hr1 |- *. change (Z.of_nat 1) with 1 in Hr1 |- *. exact Hr1. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 pc 2) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct (translate_chunk_ram_gen_ad adf root_ppn P pc satp0 menvcfg0 tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons (HPk pc Hram) (fun e HPe => Hdisc pc e Hram HPe) Hram
                    HA' Hord' HR' Hcov' Hpma' Lhtif HmisaS' Hok Hmemσ (Hada pc Hram) Lmenv HPBMTE)
          as (s1 & Htr1 & Hs1eq & Hs1mem & Hs1cons & Hs1reg).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hs1reg cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1pmpc : register_lookup pmpcfg_n s1.(sregs) = pmpcfg0)
          by (rewrite (Hs1reg pmpcfg_n ltac:(vm_compute; reflexivity)); exact Lpmpc).
        assert (L1pmpaddr : register_lookup pmpaddr_n s1.(sregs) = pmpaddr00)
          by (rewrite (Hs1reg pmpaddr_n ltac:(vm_compute; reflexivity)); exact Lpmpaddr).
        assert (L1pma : register_lookup pma_regions s1.(sregs) = pmar0)
          by (rewrite (Hs1reg pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hs1reg htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (i1HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR)
          by (rewrite L1pmpc; exact HA).
        assert (i1Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false)
          by (rewrite L1pmpaddr; exact Hord).
        assert (i1HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true)
          by (rewrite L1pmpc; exact HX).
        assert (i1range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match).
        { rewrite L1pmpaddr.
          exact (ram_fetch_pmp pc (vec_access_dec pmpaddr00 0) 2 1
                   ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity) Hram Hram1 Hcov). }
        assert (i1match : matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pc) 2 = Some region)
          by (rewrite L1pma; exact Hmatch0).
        assert (i1bytes : forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pc j) = Some (nth_byte h j))
          by (rewrite Hs1mem; exact Hbf).
        pose proof (exec_fetch_RVC_2_S_gen pc h σ s1 region
                      Lpc HmisaC' Hbit0 Hbit1 Hal Htr1 i1HA i1Hord i1range i1HX i1match Halign0 Hexec0
                      (within_clint_false pc 2 s1 Hnc ltac:(lia))
                      (within_sig_false  pc 2 s1 Hns ltac:(lia))
                      (within_htif_false pc 2 s1 L1htif)
                      (addr_is_ram_not_dev _ Hram) i1bytes L1priv HisRVC) as Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
    - (* F_Error *) done.
  Qed.

  (* Megapage instance of the generic fetch: the identity-superpage kernel  *)
  (* is [fetch_from_instr_bytes_s_consistent_gen] at [P := (= superpage)].   *)
  (* Discrimination is trivial (every legal entry IS the superpage -> hit).  *)
  (* Restores the exact old statement so all existing callers stay green.    *)
  Lemma fetch_from_instr_bytes_s_consistent (root_ppn : mword 44)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    tlb_pt_consistent root_ppn tlbvec ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pma_allows_pte_read pmar0 ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    kpt_bytes root_ppn dqb -∗
    instr_bytes pc r -∗
    ⌜ ∃ tlbvec2, exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
                 ∧ tlb_pt_consistent root_ppn tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid Hcons HPBMTE HX Hcov HA0 Hord0 HR0 Hpma_pte)
      "Hmem Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    iDestruct (fetch_from_instr_bytes_s_consistent_gen root_ppn
                 (P_kpt root_ppn) σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid
                 (tlb_pt_consistent_to_generic root_ppn tlbvec Hcons)
                 (fun a Hram => P_kpt_ram root_ppn a Hram)
                 (fun a e Hram HPe => P_kpt_disc root_ppn a e Hram HPe)
                 HPBMTE HX Hcov HA0 Hord0 HR0 Hpma_pte
                 with "Hmem Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %(tlbvec2 & Hfetch & Hcons2).
    iPureIntro. exists tlbvec2. split; [ exact Hfetch | ].
    apply tlb_pt_consistent_of_generic. exact Hcons2.
  Qed.

  (* arbitrary-A/D instance of the unified fetch *)
  Lemma fetch_from_instr_bytes_s_consistent_ad (adf : kpt_adf) (root_ppn : mword 44)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    tlb_pt_consistent_ad adf root_ppn tlbvec ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    pma_allows_pte_read pmar0 ->
    (forall a, addr_is_ram a -> fst (adf (svpn_of a)) = true) ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    menvcfg ↦ᵣ{ dqe } menvcfg0 -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    kpt_bytes_ad adf root_ppn dqb -∗
    instr_bytes pc r -∗
    ⌜ ∃ tlbvec2, exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
                 ∧ tlb_pt_consistent_ad adf root_ppn tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid Hcons HPBMTE HX Hcov HA0 Hord0 HR0 Hpma_pte Hada)
      "Hmem Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    iDestruct (fetch_from_instr_bytes_s_consistent_gen_ad adf root_ppn
                 (P_kpt_ad adf root_ppn) σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma0 HmisaC0 HmisaS0 HSXL0 Hmode Hppn Hasid
                 Hcons
                 (fun a Hram => P_kpt_ad_ram adf root_ppn a Hram)
                 (fun a e Hram HPe => P_kpt_ad_disc adf root_ppn a e Hram HPe)
                 HPBMTE HX Hcov HA0 Hord0 HR0 Hpma_pte Hada
                 with "Hmem Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %(tlbvec2 & Hfetch & Hcons2).
    iPureIntro. exists tlbvec2. split; [ exact Hfetch | exact Hcons2 ].
  Qed.

  (* =================================================================== *)
  (* 13. wp_instr_s_fill -- the walk engine: the fetch WALKS the page     *)
  (* table (owned PTE bytes) and FILLS the TLB.  This lemma performs the  *)
  (* tlb ghost update ITSELF (it holds the cell at full ownership), hands *)
  (* the caller [state_interp] of the FILLED state σf (so the execute     *)
  (* obligations run from σf), and hands the continuation the UPDATED     *)
  (* tlb cell.                                                            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (* 13b. wp_instr_s_tlbinv -- THE UNIFIED S-mode step engine.  Takes the *)
  (* TLB/page-table consistency invariant [tlb_inv root_ppn] plus the     *)
  (* page-table fact for the fetched va (RAM-derived fetch geometry +     *)
  (* the owned PTE bytes [pte_super_bytes] -- SATP's table maps this va   *)
  (* executable) and case-splits internally: slot 5 resident (TLB hit,    *)
  (* state-preserving) or empty (page WALK + fill, which PRESERVES the    *)
  (* invariant).  Subsumes [wp_instr_s] (hit) and [wp_instr_s_fill]       *)
  (* (walk), which become internal to this engine.                        *)
  (* =================================================================== *)
  Lemma wp_instr_s_tlbinv (root_ppn : mword 44) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          tlb_inv root_ppn -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    (* Open [tlb_inv] ONCE and drive the UNIFIED fetch (each chunk translates
       through its own vpn, 0/1/2 slots filled) -- no hit/walk split, no
       same-page premise.  Re-bundle [smode_config] and re-seal [tlb_inv]
       (with the fetch's [tlbvec2]) in the caller's continuation.  The ambient
       PMP config is opened out of [tlb_inv] and re-sealed unchanged. *)
    iIntros
      "Hsm Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent root_ppn σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] [Hsatp Htlb Hpbytes Hpmpc Hpmpa] Hpc'").
      - iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                  with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
      - iApply (tlb_inv_close root_ppn satp0 tlbvec2 Hmode Hasid Hppn Hcons2
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode (i0 ExecuteAs-expands to the target i) *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

  (* arbitrary-A/D plain step engine *)
  Lemma wp_instr_s_tlbinv_ad (adf : kpt_adf) (root_ppn : mword 44) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    (forall a, addr_is_ram a -> fst (adf (svpn_of a)) = true) ->
    smode_config γ dq -∗
    tlb_inv_ad adf root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          tlb_inv_ad adf root_ppn -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    (* Open [tlb_inv] ONCE and drive the UNIFIED fetch (each chunk translates
       through its own vpn, 0/1/2 slots filled) -- no hit/walk split, no
       same-page premise.  Re-bundle [smode_config] and re-seal [tlb_inv]
       (with the fetch's [tlbvec2]) in the caller's continuation.  The ambient
       PMP config is opened out of [tlb_inv] and re-sealed unchanged. *)
    iIntros (Hada)
      "Hsm Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_ad_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent_ad adf root_ppn σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte Hada
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] [Hsatp Htlb Hpbytes Hpmpc Hpmpa] Hpc'").
      - iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                  with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
      - iApply (tlb_inv_ad_close adf root_ppn satp0 tlbvec2 Hmode Hasid Hppn Hcons2
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode (i0 ExecuteAs-expands to the target i) *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

  (* =================================================================== *)
  (* 13c. wp_instr_s_tlbinv_gen -- the generic engine over [tlb_inv_gen P]. *)
  (* Identical to [wp_instr_s_tlbinv] but the fetch runs over a generic     *)
  (* [tlb_consistent P] TLB, so the fetch's slot may hold a foreign entry   *)
  (* (the UART leaf today; an arbitrary RAM leaf under the all-4KB kernel). *)
  (* [HPsuper] keeps the walk-fill inside [P]; [Hdisc] says every legal     *)
  (* entry is either the superpage (hit) or fails to match the RAM fetch    *)
  (* vpn (walk).  The client (e.g. the UART store/load WP) supplies both.   *)
  (* =================================================================== *)
  Lemma wp_instr_s_tlbinv_gen (P : TLB_Entry -> Prop) (root_ppn : mword 44) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    (forall a, addr_is_ram a -> P (kpt_tlb_ent root_ppn (svpn_of a))) ->
    (forall a e, addr_is_ram a -> P e ->
       e = kpt_tlb_ent root_ppn (svpn_of a) \/
       match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
    smode_config γ dq -∗
    tlb_inv_gen P root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          tlb_inv_gen P root_ppn -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HPsuper Hdisc)
      "Hsm Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_gen_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent_gen root_ppn P σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPsuper Hdisc HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] [Hsatp Htlb Hpbytes Hpmpc Hpmpa] Hpc'").
      - iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                  with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
      - iApply (tlb_inv_gen_close P root_ppn satp0 tlbvec2 Hmode Hasid Hppn Hcons2
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode (i0 ExecuteAs-expands to the target i) *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

  (* arbitrary-A/D P-generic step engine *)
  Lemma wp_instr_s_tlbinv_gen_ad (adf : kpt_adf) (P : TLB_Entry -> Prop) (root_ppn : mword 44) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    (forall a, addr_is_ram a -> P (kpt_tlb_ent_ad adf root_ppn (svpn_of a))) ->
    (forall a e, addr_is_ram a -> P e ->
       e = kpt_tlb_ent_ad adf root_ppn (svpn_of a) \/
       match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
    (forall a, addr_is_ram a -> fst (adf (svpn_of a)) = true) ->
    smode_config γ dq -∗
    tlb_inv_gen_ad adf P root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          tlb_inv_gen_ad adf P root_ppn -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HPsuper Hdisc Hada)
      "Hsm Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_gen_ad_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent_gen_ad adf root_ppn P σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPsuper Hdisc HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte Hada
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] [Hsatp Htlb Hpbytes Hpmpc Hpmpa] Hpc'").
      - iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                  with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc").
      - iApply (tlb_inv_gen_ad_close adf P root_ppn satp0 tlbvec2 Hmode Hasid Hppn Hcons2
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode (i0 ExecuteAs-expands to the target i) *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

End SmodeCoreIris.

(* Compatibility alias: the old megapage footprint name.  The PT footprint
   is now the whole kvmmake-shaped 4KB kernel table ([kpt_bytes]). *)
Notation pte_super_bytes := kpt_bytes (only parsing).

(* ===================================================================== *)
(* 14. Demos -- the weakened decode + constructor story, end to end.      *)
(* ===================================================================== *)

(* (b) kernelvec's FIRST instruction: the c.addi16sp sp, -448 at 0x800053e0
   (encoding 0x7111; the 4-aligned 4-byte fetch window also covers the
   following c.sdsp's low half 0xe006). *)
Definition kv_h1 : mword 16 := mword_of_int 0x7111.
Definition kv_w1 : mword 32 := mword_of_int 0xe0067111.
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
  Context `{CID : CpuId}.

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

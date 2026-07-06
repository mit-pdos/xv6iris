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
   - Sv39 instruction-fetch translation of an in-RAM virtual address, phrased
     over [svpn_of va]: TLB HIT via the identity superpage entry [pw_tlb_entry]
     (state-preserving, [exec_translateAddr_fetch_hit_g]) and TLB MISS via the
     one-PTE page WALK ([exec_translateAddr_fetch_walk], reads [pte_super] at
     [pte_paddr root_ppn], fills the slot for the fetched vpn), combined into
     the hit-or-walk [exec_translateAddr_fetch_S];
   - [translate_chunk_ram] -- translate one 16-bit fetch chunk over a
     consistent TLB (geometry derived from the owned [addr_is_ram]); applied
     per half, so a page-straddling 4-byte fetch translates each half through
     its OWN vpn (0/1/2 slots filled), plus the state-polymorphic [fetch]
     compositions [exec_fetch_*_S_gen] that thread the chunk translations;
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
From Stdlib Require Import Eqdep_dec ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpFetch WpDecode WpLeafCommon WpEntry WpLoad WpGprCsrwB WpGprRvc WpEntryNew.
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

Lemma exec_pmpMatchAddr_TOR_match (addr width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4) (uint addr) (uint width) = PMP_Match ->
  exec (pmpMatchAddr (Physaddr addr) width ent pmpaddr prev) s = Some (PMP_Match, s).
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. apply exec_returnm.
Qed.

Lemma exec_pmpReadAddrReg_val (n : Z) s :
  exec (pmpReadAddrReg n) s
    = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pmpaddr_n s)). cbn beta.
  replace (andb (Z.geb sys_pmp_grain 2)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"1")))
    with false by (vm_compute; reflexivity).
  replace (andb (Z.geb sys_pmp_grain 1)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"0")))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

Lemma exec_pmpCheck_supervisor_grant (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (InstructionFetch tt) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (InstructionFetch tt)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HX. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_pmpCheck_supervisor_grant_load (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load PageTableEntry) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Load PageTableEntry)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.


(* The TOR-entry-0 facts of the page walk's 8-byte PTE read (R instead of X). *)
Definition pmp_tor0_pte_read (cfg : type_of_register pmpcfg_n)
    (addrs : type_of_register pmpaddr_n) (a : mword 64) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg 0)) = TOR
  /\ zopz0zKzJ_u (zeros' 64) (vec_access_dec addrs 0) = false
  /\ pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
       (Z.mul (uint (vec_access_dec addrs 0)) 4)
       (uint a) (uint (to_bits 64 8)) = PMP_Match
  /\ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec cfg 0)) ('b"1") = true.

(* ===================================================================== *)
(* 4. S-mode fetch memory reads (widths 2 and 4) + the 8-byte PTE read.    *)
(* ===================================================================== *)

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
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hbytes)).
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
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
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
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hbytes)).
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
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
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

Lemma exec_translationMode_S_sv39 (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  exec (translationMode Supervisor) s = Some (Sv39, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
  cbn match.
  change (xlen >=? 64) with true.
  match goal with |- exec (Defs.bind ?ARM _) s = _ =>
    assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
  { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                  = Some (eq_refl, s)).
    { unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hae).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
    rewrite Hsatp. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ HARM).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

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

(* list_update at a valid index is stdpp's insert (local copy; also in
   WpGprCsrwC, which imports us transitively -- keep them independent). *)
Lemma tlb_list_update_insert {A} (xs : list A) (k : nat) (x : A) :
  (k < length xs)%nat -> list_update xs k x = <[k := x]> xs.
Proof. intros Hk. symmetry. apply insert_take_drop. exact Hk. Qed.

(* vec_access_dec over vec_update_dec on a 64-entry vector, at ANY index j
   (including the out-of-range ones, where both sides read the same dummy). *)
Lemma vec64_access_update {T} `{Inhabited T} (v : vec T (2 ^ 6)) (m j : Z) (t : T) :
  0 <= m < 64 ->
  vec_access_dec (vec_update_dec v m t) j
  = (if Z.eqb j m then t else vec_access_dec v j).
Proof.
  intros Hm. destruct v as [xs Hlen].
  assert (Hl : length xs = 64%nat) by (rewrite Hlen; reflexivity).
  unfold vec_update_dec.
  destruct (sumbool_of_bool (0 <=? m <? 2 ^ 6)) as [He|He].
  2:{ exfalso.
      assert (Ht : ((0 <=? m) && (m <? 2 ^ 6))%bool = true)
        by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite Ht in He. discriminate He. }
  unfold vec_access_dec. cbn [projT1].
  unfold update_list_dec, update_list_inc, access_list_dec, access_list_inc, length_list.
  rewrite !Hl.
  change (Z.of_nat 64 - 1) with 63.
  set (k := Z.to_nat (63 - m)).
  assert (Hk : (k < length xs)%nat) by (unfold k; rewrite Hl; lia).
  rewrite (tlb_list_update_insert xs k t Hk).
  rewrite length_insert. rewrite Hl.
  change (Z.of_nat 64 - 1) with 63.
  destruct (Z.ltb (63 - j) 0) eqn:Hg.
  - (* out of range below: both dummy; j > 63 > m *)
    apply Z.ltb_lt in Hg.
    replace (Z.eqb j m) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - apply Z.ltb_ge in Hg.
    destruct (Z.eqb j m) eqn:Hjm.
    + apply Z.eqb_eq in Hjm. subst j.
      rewrite nth_lookup.
      replace (Z.to_nat (63 - m)) with k by reflexivity.
      rewrite (list_lookup_insert xs k t Hk). reflexivity.
    + apply Z.eqb_neq in Hjm.
      rewrite nth_lookup.
      rewrite list_lookup_insert_ne.
      2:{ unfold k. lia. }
      rewrite <- nth_lookup. reflexivity.
Qed.

(* the direct-mapped hash always lands in range. *)
Lemma tlb_hash_range (vpn : mword 27) : 0 <= tlb_hash (__id 39) vpn < 2 ^ 6.
Proof.
  unfold tlb_hash.
  match goal with |- 0 <= uint ?x < _ =>
    pose proof (uint_range x ltac:(vm_compute; discriminate)) as Hr end.
  match type of Hr with 0 <= _ <= 2 ^ ?a - 1 =>
    replace (2 ^ a - 1) with 63 in Hr by (vm_compute; reflexivity) end.
  change (2 ^ 6) with 64. lia.
Qed.

(* THE INVARIANT: every resident entry is the identity-superpage entry. *)
Definition tlb_pt_consistent (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
  forall i, 0 <= i < 2 ^ 6 ->
    vec_access_dec tlbvec i = None \/
    vec_access_dec tlbvec i = Some (pw_tlb_entry root_ppn (mword_of_int 0)).

(* preservation: a walk's fill installs the entry the table produces. *)
Lemma tlb_pt_consistent_fill (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (j : Z) :
  0 <= j < 2 ^ 6 ->
  tlb_pt_consistent root_ppn tlbvec ->
  tlb_pt_consistent root_ppn
    (vec_update_dec tlbvec j (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
Proof.
  intros Hj Hc i Hi.
  rewrite (vec64_access_update tlbvec j i _ ltac:(lia)).
  destruct (Z.eqb i j).
  - right. reflexivity.
  - apply Hc. exact Hi.
Qed.

(* ---- [tlb]-register set laws: a TLB fill writes only the [tlb] cell, so     *)
(* nested/idempotent [set_reg .. tlb ..] collapse.  Used to flatten the         *)
(* possibly-double-filled fetch state to a single [set_reg σ tlb tlbvec2].      *)
Lemma register_set_tlb_id (rs : regstate) :
  register_set tlb (register_lookup tlb rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intros r'.
  destruct (register_vector_64_option_TLB_Entry_beq r' tlb) eqn:E.
  - apply register_vector_64_option_TLB_Entry_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

Lemma register_set_tlb_overwrite (rs : regstate) (a b : type_of_register tlb) :
  register_set tlb b (register_set tlb a rs) = register_set tlb b rs.
Proof.
  destruct rs. unfold register_set. cbn.
  f_equal. apply functional_extensionality. intros r'.
  destruct (register_vector_64_option_TLB_Entry_beq r' tlb); reflexivity.
Qed.

Lemma set_reg_tlb_id (s : mstate) :
  set_reg s tlb (register_lookup tlb s.(sregs)) = s.
Proof. destruct s. unfold set_reg. cbn. rewrite register_set_tlb_id. reflexivity. Qed.

Lemma set_reg_tlb_overwrite (s : mstate) (a b : type_of_register tlb) :
  set_reg (set_reg s tlb a) tlb b = set_reg s tlb b.
Proof. destruct s. unfold set_reg. cbn. rewrite register_set_tlb_overwrite. reflexivity. Qed.

(* ===================================================================== *)
(* Local RAM-geometry lemmas needed to DERIVE the S-mode fetch geometry    *)
(* from an owned instruction points-to (addr_is_ram), instead of taking it *)
(* as fetch-geometry premises.  (Local copies of the                       *)
(* WpSmodeGpr/WpGprRvcTor lemmas, which live downstream of this file; the   *)
(* others -- ram_canonical/ram_svpn2/ram_mask/ram_mvpn/svpn_of_unsigned -- *)
(* are already in RiscvExtras.)                                            *)
(* ===================================================================== *)

Lemma pmpRangeMatch_full (b e a w : Z) :
  b <= a -> 0 < w -> a + w <= e ->
  pmpRangeMatch b e a w = PMP_Match.
Proof.
  intros Hb Hw He. unfold pmpRangeMatch.
  replace (Z.leb (Z.add a w) b) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb e a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [orb].
  replace (Z.leb b a) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Z.add a w) e) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

(* Width-general PMP TOR-entry-0 RAM grant: the W-byte access at [a] fully
   inside [0, pmpaddr0*4) matches (W = 4 / 2 for fetch, 8 for the PTE read). *)
Lemma ram_pmp_match_w (a pmpaddr0 : mword 64) (w : Z) :
  0 < w ->
  uint (to_bits 64 w) = w ->
  ram_base <= uint a ->
  uint a + w <= ram_base + ram_size ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint a) (uint (to_bits 64 w)) = PMP_Match.
Proof.
  intros Hw0 Hwv Hlo Hfit Hcov.
  assert (Hz : uint (zeros' 64 : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz. rewrite Z.mul_0_l. rewrite Hwv.
  apply pmpRangeMatch_full; unfold ram_base, ram_size in *; lia.
Qed.

Lemma uint_pa_add (a : mword 64) (j : nat) :
  (uint a + Z.of_nat j < 18446744073709551616)%Z ->
  uint (pa_add a j) = uint a + Z.of_nat j.
Proof.
  intro Hlt. rewrite !uint_unsigned in Hlt |- *.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (Z.of_nat j) : mword 64) = Z.of_nat j).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    split.
    - apply Nat2Z.is_nonneg.
    - apply Z.le_lt_trans with (bv_unsigned a + Z.of_nat j).
      + rewrite <- (Z.add_0_l (Z.of_nat j)) at 1. apply Z.add_le_mono_r. exact Har.
      + exact Hlt. }
  rewrite Hj.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split.
  - apply Z.add_nonneg_nonneg. exact Har. apply Nat2Z.is_nonneg.
  - exact Hlt.
Qed.

(* superpage mask fact, output-PPN side (over [sfetch_ppn_out]). *)
Lemma ram_mppn (a : mword 64) :
  addr_is_ram a ->
  zero_extend' 44 (and_vec (sfetch_ppn_out (svpn_of a)) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44).
Proof.
  intros _.
  generalize (svpn_of a). intro vpn.
  unfold sfetch_ppn_out.
  cbv [and_vec or_vec not_vec sign_extend' zero_extend' concat_vec subrange_vec_dec
       Operators_mwords.sign_extend Operators_mwords.zero_extend Operators_mwords.exts_vec
       Operators_mwords.extz_vec Operators_mwords.word_binop Operators_mwords.word_unop
       Operators_mwords.with_word' SailStdpp.Values.with_word to_word get_word autocast].
  cbn.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  cbn.
  change (26 + 18) with 44.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.and MachineWord.not MachineWord.zero_extend
       MachineWord.sign_extend MachineWord.concat MachineWord.Z_to_word mword_of_int Values.mword_of_int].
  apply bv_eq.
  rewrite (@bv_zero_extend_unsigned 44 44 _ ltac:(lia)).
  rewrite bv_and_unsigned.
  rewrite (@bv_concat_unsigned 26 44 18 _ _ eq_refl).
  rewrite bv_not_unsigned.
  rewrite (@bv_zero_extend_unsigned 18 44 _ ltac:(lia)).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  assert (Hb1 : bv_wrap 26 (bv_wrap (MachineWord.MachineWord.Z_idx 44) 524288 ≫ Z.of_N 18) = 2)
    by (vm_compute; reflexivity).
  rewrite Hb1.
  assert (Hz : bv_wrap 18 (Z.lnot (bv_unsigned (zeros 18))) = 262143) by (vm_compute; reflexivity).
  rewrite Hz.
  rewrite Z.shiftr_0_r.
  assert (Hsh : (2 ≪ Z.of_N 18) = 524288) by (vm_compute; reflexivity).
  rewrite Hsh.
  assert (Hrhs : bv_wrap (MachineWord.MachineWord.Z_idx 44) 524288 = 524288) by (vm_compute; reflexivity).
  rewrite Hrhs.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec. rewrite Z.lor_spec.
  rewrite (bv_wrap_spec 44 (Z.lnot 262143) i Hi).
  rewrite (bv_wrap_spec 18 (bv_unsigned vpn) i Hi).
  rewrite (Z.lnot_spec 262143 i ltac:(lia)).
  change 262143 with (Z.ones 18).
  rewrite (Z.testbit_ones_nonneg 18 i ltac:(lia) Hi).
  change 524288 with (2 ^ 19).
  rewrite (Z.pow2_bits_eqb 19 i ltac:(lia)).
  destruct (Z.ltb_spec i 18) as [Hlt | Hge].
  - replace (i <? 18) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (19 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. rewrite !andb_false_r. reflexivity.
  - rewrite (bool_decide_false (i < Z.of_N 18) ltac:(lia)).
    replace (i <? 18) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [negb]. rewrite andb_false_l. rewrite orb_false_r. rewrite andb_true_r.
    destruct (Z.eqb_spec 19 i) as [He | Hne].
    + rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)). reflexivity.
    + reflexivity.
Qed.

(* the gigapage identity translation: a RAM vaddr walks to itself. *)
Lemma ram_ident (root_ppn : mword 44) (a : mword 64) :
  addr_is_ram a ->
  zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) (svpn_of a))
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a.
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi]. rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  rewrite sfetch_tlb_get_ppn. unfold sfetch_ppn_out.
  cbn [bits_of_virtaddr]. unfold pagesize_bits.
  apply bv_eq. symmetry.
  cbv [trunc vector_truncate slice or_vec and_vec sign_extend' zero_extend'
       concat_vec subrange_vec_dec Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  change (12 - 1 - 0 + 1) with 12.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  change (Z.of_N (44 + 12)) with 56.
  change ((44 + 12)%N) with 56%N.
  cbn.
  change (26 + 18) with 44.
  change (44 + 12) with 56.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.zero_extend MachineWord.concat
       MachineWord.Z_to_word mword_of_int Values.mword_of_int].
  rewrite (@bv_zero_extend_unsigned (44 + 12)%N 64 _ ltac:(lia)).
  rewrite (@bv_concat_unsigned 44 (44 + 12) 12 _ _ eq_refl).
  rewrite (@bv_concat_unsigned 26 (26 + 18) 18 _ _ eq_refl).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  change (bv_unsigned (get_word (bits_of_virtaddr (Virtaddr a)))) with (bv_unsigned a).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  change (Z.of_N 0) with 0.
  change (Z.of_N 18) with 18.
  change (Z.of_N 12) with 12.
  rewrite !Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (39 - 1 - 0 + 1)) with 39%N.
  assert (Hconst : bv_wrap 26 (bv_wrap 44 524288 ≫ 18) ≪ 18 = 524288) by (vm_compute; reflexivity).
  rewrite Hconst.
  assert (E39 : bv_wrap 39 (bv_unsigned a) = bv_unsigned a).
  { apply bv_wrap_small. assert (bv_modulus 39 = 549755813888) as -> by (vm_compute; reflexivity). lia. }
  rewrite E39.
  assert (E27 : bv_wrap 27 (bv_unsigned a ≫ 12) = bv_unsigned a ≫ 12).
  { apply bv_wrap_small.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)). change (2 ^ 12) with 4096.
    assert (bv_modulus 27 = 134217728) as -> by (vm_compute; reflexivity).
    split. apply Z.div_pos. lia. lia. apply Z.div_lt_upper_bound. lia. lia. }
  rewrite E27.
  assert (Hd31 : bv_unsigned a / 2147483648 = 1).
  { assert (1 <= bv_unsigned a / 2147483648) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 2147483648 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hd30 : bv_unsigned a / 1073741824 = 2).
  { assert (2 <= bv_unsigned a / 1073741824) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 1073741824 < 3) by (apply Z.div_lt_upper_bound; lia). lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec.
  rewrite (Z.shiftl_spec _ 12 i Hi).
  rewrite (bv_wrap_spec 12 (bv_unsigned a) i Hi).
  destruct (Z.ltb_spec i 12) as [Hi12 | Hi12].
  - rewrite (bool_decide_true (i < Z.of_N 12) ltac:(lia)). rewrite andb_true_l.
    rewrite (Z.testbit_neg_r _ (i - 12) ltac:(lia)). rewrite orb_false_l. reflexivity.
  - rewrite (bool_decide_false (i < Z.of_N 12) ltac:(lia)). rewrite andb_false_l. rewrite orb_false_r.
    rewrite Z.lor_spec.
    rewrite (bv_wrap_spec 18 (bv_unsigned a ≫ 12) (i - 12) ltac:(lia)).
    rewrite (Z.shiftr_spec (bv_unsigned a) 12 (i - 12) ltac:(lia)).
    replace (i - 12 + 12) with i by lia.
    change 524288 with (2 ^ 19).
    rewrite (Z.pow2_bits_eqb 19 (i - 12) ltac:(lia)).
    destruct (Z.ltb_spec (i - 12) 18) as [Hlt | Hge].
    + rewrite (bool_decide_true (i - 12 < Z.of_N 18) ltac:(lia)). rewrite andb_true_l.
      replace (19 =? i - 12) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite orb_false_l. reflexivity.
    + rewrite (bool_decide_false (i - 12 < Z.of_N 18) ltac:(lia)). rewrite andb_false_l. rewrite orb_false_r.
      destruct (Z.eqb_spec 19 (i - 12)) as [He | Hne].
      * assert (i = 31) as -> by lia.
        apply (proj2 (Z.testbit_true (bv_unsigned a) 31 ltac:(lia))).
        change (2 ^ 31) with 2147483648. rewrite Hd31. reflexivity.
      * assert (i = 30 \/ i >= 32) as [-> | Hge32] by lia.
        -- apply (proj2 (Z.testbit_false (bv_unsigned a) 30 ltac:(lia))).
           change (2 ^ 30) with 1073741824. rewrite Hd30. reflexivity.
        -- apply (proj1 (Z.bounded_iff_bits_nonneg 32 (bv_unsigned a) ltac:(lia) ltac:(lia))
                    ltac:(change (2 ^ 32) with 4294967296; lia) i ltac:(lia)).
Qed.

(* The fetch [pmpRangeMatch] from owned bytes: base [a] is RAM and the last
   read byte [pa_add a k] (k = w-1) is RAM, so the W-byte read lies fully in
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

Section KVTranslate.
  Context (root_ppn : mword 44).

  (* ---- GENERAL (any in-region svpn) TLB-hit chain, mirroring the data     *)
  (* hit path; used by the 2+2 F_Base fetch arm (each halfword hits/walks    *)
  (* its own slot [tlb_hash 39 svpn]).                                       *)
  Lemma exec_translate_TLB_hit_super_g (vpn : mword 27) (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (InstructionFetch tt) Supervisor mxr do_sum
            tt (tlb_hash (__id 39) vpn) (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[check_PTE_permission ?ac ?pr ?mx ?ds ?fl ?ex ?ep] =>
      assert (Hchk : exec (check_PTE_permission ac pr mx ds fl ex ep) s = Some (PTE_Check_Success tt, s))
        by (destruct mxr, do_sum; vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    assert (Hpbmt : exec (tlb_get_pbmt (pw_tlb_entry root_ppn (mword_of_int 0))) s = Some (PBMT_PMA, s))
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hpbmt). apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_hit_super_g (vpn : mword 27) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) vpn) s
      = Some (Some (tlb_hash (__id 39) vpn, pw_tlb_entry root_ppn (mword_of_int 0)), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    match goal with |- context[match_TLB_Entry ?e ?a ?v] =>
      replace (match_TLB_Entry e a v) with true end.
    2:{ unfold match_TLB_Entry, pw_tlb_entry; cbn.
        rewrite Hmask. vm_compute; reflexivity. }
    apply exec_returnm.
  Qed.

  Lemma exec_translate_hit_super_g (vpn : mword 27) (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_super_g vpn tlbvec s Htlb Hvec Hmask)).
    cbn match.
    apply exec_translate_TLB_hit_super_g.
  Qed.

  Lemma exec_translateAddr_fetch_hit_g (va : mword 64) (svpn : mword 27) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident Hmask.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with svpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_hit_super_g svpn _ _ _ tlbvec s Htlb Hvec Hmask)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- TLB MISS: the one-PTE page walk (STATE CHANGE: fills the TLB) ---- *)

  Lemma exec_read_pte_S (addr : mword 64) (region : PMA_Region) (w : bv 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
    is_aligned_paddr (Physaddr addr) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (read_pte (Physaddr addr) 8) s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hbytes.
    assert (Hchk : exec (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor (Physaddr addr) 8 false false false false)
                     s = Some (Ok (w, default_meta), s)).
    { unfold checked_mem_read.
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
      2:{ unfold phys_access_check.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
          cbn match.
          rewrite (exec_bind_Some _ _ _ _ _
                     (_ : exec (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) PBMT_PMA false) s
                          = Some (None, s))).
          2:{ unfold pmaCheck.
              rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
              rewrite Hmatch.
              destruct region as [rbase rsize rattr rdtree].
              cbn [PMA_Region_attributes] in Hread |- *.
              rewrite Halign. cbn [Riscv.rv64d.not negb].
              rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
              cbn match beta.
              change (assert_exp' true "sys/mem.sail:105.61-105.62" >>=
                      (fun _ : true = true => returnM (PMA_supports_pte_read (override_PMA rattr PBMT_PMA))))
                with (returnM (PMA_supports_pte_read (override_PMA rattr PBMT_PMA)) : M bool).
              rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
              rewrite Hread. cbn match.
              apply exec_returnM. }
          cbn match. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
      2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
          rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
          rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
          rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
      rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
      2:{ unfold read_kind_of_flags. apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hbytes)).
      apply exec_returnM. }
    unfold read_pte, mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _ Hchk).
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

  (* The single-level (1GB superpage) page walk: reads ONE PTE from memory
     and returns the identity translation output ppn 0x80005. *)
  Lemma exec_pt_walk_super (vpn : mword 27) (mxr do_sum : bool) (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 vpn (InstructionFetch tt) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (sfetch_ppn_out vpn) (autocast (T := mword) pte_super)
                    (Physaddr (pte_paddr root_ppn)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold pt_walk, Zwf_guarded.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (pte_paddr root_ppn : mword 64) by (unfold pte_paddr; rewrite Hvpn2; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S (pte_paddr root_ppn) region pte_super s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0))
                           (ext_bits_of_PTE pte_super)) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    match goal with |- context[pte_is_non_leaf ?f] =>
      replace (pte_is_non_leaf f) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    match goal with |- context[neq_vec ?a ?b] =>
      replace (neq_vec a b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    assert (Hchk : exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0)) (ext_bits_of_PTE pte_super) tt) s
                   = Some (PTE_Check_Success tt, s))
      by (destruct mxr, do_sum; vm_compute; reflexivity).
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hchk. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (2 >? 0) with true. cbv iota beta.
    match goal with |- context[eq_vec (_get_PTE_Ext_N ?e) ?b] =>
      replace (eq_vec (_get_PTE_Ext_N e) b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    unfold sfetch_ppn_out.
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  (* add_to_TLB installs the entry at hash index [tlb_hash 39 vpn]. *)
  Lemma exec_add_to_TLB_super (vpn : mword 27) (asid : mword 16) s :
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sfetch_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    exec (add_to_TLB 39 asid vpn (sfetch_ppn_out vpn) (autocast (T := mword) pte_super)
            (Physaddr (pte_paddr root_ppn)) 2 false) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                                   (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hmvpn Hmppn.
    unfold add_to_TLB. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    do 5 f_equal. unfold pw_tlb_entry.
    f_equal; first [ exact Hmvpn | exact Hmppn | vm_compute; reflexivity ].
  Qed.

  Lemma exec_translate_TLB_miss_super (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sfetch_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid root_ppn vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (sfetch_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_super vpn mxr do_sum region menvcfg0 s
                  Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_super vpn asid s Hmvpn Hmppn)).
    apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_miss (vpn : mword 27) (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    exec (lookup_TLB 39 asid vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. apply exec_returnm.
  Qed.

  Lemma exec_translate_walk (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region)
        (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sfetch_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid root_ppn vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (sfetch_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss vpn asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_super vpn mxr do_sum asid region menvcfg0 s
             Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
  Qed.

  (* The state after the fetch's page walk: TLB filled at hash index [tlb_hash 39 svpn]. *)
  Definition pw_filled (svpn : mword 27) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) : mstate :=
    set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) svpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).

  (* FULL Sv39 fetch translation of a kernelvec-page vaddr with an EMPTY TLB
     slot 5: the page walk reads the PTE from memory and fills the TLB. *)
  Lemma exec_translateAddr_fetch_walk (va : mword 64) (svpn : mword 27) (region : PMA_Region)
        (menvcfg0 satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = None ->
    (* the superpage-identity geometry, phrased over [svpn] (= [svpn_of va]) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sfetch_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), pw_filled svpn tlbvec s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
           HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with svpn by (symmetry; exact Hvpn_def);
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk svpn _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite <- (sfetch_tlb_get_ppn root_ppn svpn).
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- Combined per-address fetch translate (HIT or WALK) ----
     Given the slot is TLB-consistent (empty, or already holding the canonical
     superpage entry), together with the [va] geometry and the PTE-read facts
     (the latter consumed only in the empty/None branch), the fetch translation
     succeeds, and the resulting state is either unchanged (hit) or the filled
     state [pw_filled svpn tlbvec s] (walk).  This is the reusable per-chunk
     unit both fetch halves call. *)
  Lemma exec_translateAddr_fetch_S (va : mword 64) (svpn : mword 27) (region : PMA_Region)
        (menvcfg0 satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    (* TLB consistency for this slot: empty, or the canonical superpage entry *)
    (vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = None \/
     vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0))) ->
    (* geometry of [va], phrased over [svpn] (= svpn_of va) *)
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sfetch_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* PTE-read facts, consumed only in the None (walk) branch *)
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exists s', exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
                 = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s')
               /\ (s' = s \/ s' = pw_filled svpn tlbvec s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hcons Hcanon Hvpn_def Hident Hmask
           Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    destruct Hcons as [Hvec | Hvec].
    - eexists. split.
      + exact (exec_translateAddr_fetch_walk va svpn region menvcfg0 satp0 tlbvec s
                 Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
                 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
      + right. reflexivity.
    - eexists. split.
      + exact (exec_translateAddr_fetch_hit_g va svpn satp0 tlbvec s
                 Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident Hmask).
      + left. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* 6. The S-mode fetch reductions (TLB hit), one per instr_bytes geometry. *)
  (* ===================================================================== *)

Section SFetchHit.
  Context (va : mword 64) (svpn : mword 27) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis Hmask : and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45).

  (* -- width 2 read at va -- *)
  Section W2.
    Context (region : PMA_Region) (h : mword 16).
    Hypothesis HA : pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
    Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
    Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 2)) = PMP_Match.
    Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
    Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 2 = Some region.
    Hypothesis Halign : is_aligned_paddr (Physaddr va) 2 = true.
    Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
    Hypothesis Hc : exec (within_clint (Physaddr va) 2) s = Some (false, s).
    Hypothesis Hsig : exec (within_sig (Physaddr va) 2) s = Some (false, s).
    Hypothesis Hh : exec (within_htif_readable (Physaddr va) 2) s = Some (false, s).
    Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte h j).

  End W2.

  (* -- width 4 read at va -- *)
  Section W4.
    Context (region : PMA_Region) (w : mword 32).
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

    Lemma exec_fetch_bytes_4_S_hit : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s).
    Proof using Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident Hmask HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR.
          rewrite (exec_translateAddr_fetch_hit_g va svpn satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident Hmask).
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
  End W4.
End SFetchHit.

End KVTranslate.

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
Lemma translate_chunk_ram (root_ppn : mword 44)
    (a satp0 menvcfg0 : mword 64) (region_pte : PMA_Region)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  register_lookup tlb s.(sregs) = tlbvec ->
  tlb_pt_consistent root_ppn tlbvec ->
  addr_is_ram a ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
  is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
  (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
  exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
  exists s',
    exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s')
    /\ s' = set_reg s tlb (register_lookup tlb s'.(sregs))
    /\ s'.(mem) = s.(mem)
    /\ tlb_pt_consistent root_ppn (register_lookup tlb s'.(sregs))
    /\ (forall rr, register_beq rr tlb = false ->
          register_lookup rr s'.(sregs) = register_lookup rr s.(sregs)).
Proof.
  intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hcons Hram
         HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
  destruct (exec_translateAddr_fetch_S root_ppn a (svpn_of a) region_pte menvcfg0 satp0 tlbvec s
              Hcp HSXL Hsatp Hmode Hppn Hasid Htlb
              (Hcons (tlb_hash (__id 39) (svpn_of a)) (tlb_hash_range (svpn_of a)))
              (ram_canonical a Hram) eq_refl (ram_ident root_ppn a Hram) (ram_mask a Hram)
              (ram_svpn2 a Hram) (ram_mvpn a Hram) (ram_mppn a Hram)
              HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)
    as (s' & Htr & Hs').
  exists s'. split; [exact Htr|].
  destruct Hs' as [Hs' | Hs'].
  - (* HIT: no state change, s' = s *)
    subst s'.
    split; [ symmetry; apply set_reg_tlb_id | ].
    split; [ reflexivity | ].
    split; [ rewrite Htlb; exact Hcons | ].
    intros rr Hrr. reflexivity.
  - (* WALK: s' fills slot [tlb_hash 39 (svpn_of a)] *)
    subst s'.
    assert (Htlbf : register_lookup tlb (pw_filled root_ppn (svpn_of a) tlbvec s).(sregs)
                    = vec_update_dec tlbvec (tlb_hash (__id 39) (svpn_of a)) (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
    { unfold pw_filled, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    split.
    { rewrite Htlbf. unfold pw_filled. reflexivity. }
    split.
    { unfold pw_filled, set_reg; cbn [mem]. reflexivity. }
    split.
    { rewrite Htlbf. apply tlb_pt_consistent_fill; [ apply tlb_hash_range | exact Hcons ]. }
    intros rr Hrr. unfold pw_filled, set_reg; cbn [sregs].
    apply irrelevant_register_set. exact Hrr.
Qed.

(* ===================================================================== *)
(* 6b. The outer S-mode fetch assemblies (TLB hit), one per geometry.     *)
(* ===================================================================== *)

Section SFetchHitOuter.
  Context (root_ppn : mword 44).
  Context (va : mword 64) (svpn : mword 27) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis Hmask : and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.

  (* ---- 4-aligned, 4-byte window ---- *)
  Section Aligned4.
    Context (region : PMA_Region) (w : mword 32).
    Hypothesis Hvalign : is_aligned_vaddr (Virtaddr va) 4 = true.
    Hypothesis Hrange4 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 4)) = PMP_Match.
    Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 4 = Some region.
    Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
    Hypothesis Hc : exec (within_clint (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hsig : exec (within_sig (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hh : exec (within_htif_readable (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte w j).

    Let Halign4p : is_aligned_paddr (Physaddr va) 4 = true := Hvalign.
    Let Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s) :=
      exec_fetch_bytes_4_S_hit root_ppn va svpn satp0 tlbvec s
        Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def Hident Hmask region w
        HA Hord Hrange4 HX Hmatch Halign4p Hexec Hc Hsig Hh Hbytes.

    (* F_Base at a 4-aligned va (single 4-byte read). *)
    Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
  End Aligned4.

  Section Aligned4RVC.
    Context (region : PMA_Region) (w : mword 32).
    Hypothesis Hvalign : is_aligned_vaddr (Virtaddr va) 4 = true.
    Hypothesis Hrange4 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 4)) = PMP_Match.
    Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 4 = Some region.
    Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
    Hypothesis Hc : exec (within_clint (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hsig : exec (within_sig (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hh : exec (within_htif_readable (Physaddr va) 4) s = Some (false, s).
    Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte w j).
    Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  End Aligned4RVC.

  (* ---- 2-aligned (not 4-aligned) shapes: RVC + the 2+2 F_Base read ---- *)
  Section Aligned2.
    Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
    Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
    Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
    Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.
    Hypothesis Hrange2 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 2)) = PMP_Match.
    Hypothesis Halign2 : is_aligned_paddr (Physaddr va) 2 = true.

    Section RVC2.
      Context (region : PMA_Region) (h : mword 16).
      Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 2 = Some region.
      Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
      Hypothesis Hc : exec (within_clint (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hsig : exec (within_sig (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hh : exec (within_htif_readable (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte h j).
      Hypothesis HisRVC : isRVC h = true.

    End RVC2.

    Section FBase2.
      Context (regl regh : PMA_Region) (w : mword 32).
      Let ilo : mword 16 := subrange_vec_dec w 15 0.
      Let ihi : mword 16 := subrange_vec_dec w 31 16.
      Let vah : mword 64 := add_vec_int va 2.
      Hypothesis Hcanonh : neq_vec (bits_of_virtaddr (Virtaddr vah))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub 39 1) 0)) = false.
      Hypothesis Hvpn_defh : autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn.
      Hypothesis Hidenth : zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub pagesize_bits 1) 0)) = vah.
      Hypothesis Hrange2h : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
          (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
          (uint vah) (uint (to_bits 64 2)) = PMP_Match.
      Hypothesis Halign2h : is_aligned_paddr (Physaddr vah) 2 = true.
      Hypothesis Hmatchl : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 2 = Some regl.
      Hypothesis Hmatchh : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr vah) 2 = Some regh.
      Hypothesis Hexecl : (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
      Hypothesis Hexech : (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
      Hypothesis Hcl : exec (within_clint (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hsigl : exec (within_sig (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hhl : exec (within_htif_readable (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hch : exec (within_clint (Physaddr vah) 2) s = Some (false, s).
      Hypothesis Hsigh : exec (within_sig (Physaddr vah) 2) s = Some (false, s).
      Hypothesis Hhh : exec (within_htif_readable (Physaddr vah) 2) s = Some (false, s).
      Hypothesis Hbytesl : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte ilo j).
      Hypothesis Hbytesh : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add vah j) = Some (nth_byte ihi j).
      Hypothesis HnotRVC : isRVC ilo = false.
      Hypothesis Hconcat : concat_vec ihi ilo = w.

    End FBase2.
  End Aligned2.
End SFetchHitOuter.

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
  (forall j : nat, (N.of_nat j < 2)%N -> s2.(mem) !! (pa_add vah j) = Some (nth_byte ihi j)) ->
  register_lookup cur_privilege s2.(sregs) = Supervisor ->
  isRVC ilo = false ->
  concat_vec ihi ilo = w ->
  exec (fetch tt) s = Some (F_Base w, s2).
Proof.
  intros ilo ihi vah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Htrh
         iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHbytesL iHprivL
         iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHbytesH iHprivH
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
                   iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHbytesL iHprivL).
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
                   iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHbytesH iHprivH).
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
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec (fetch tt) s = Some (F_Base w, s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv HnotRVC.
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
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
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
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = true ->
  exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv HisRVC.
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
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
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
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add va j) = Some (nth_byte h j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC h = true ->
  exec (fetch tt) s = Some (F_RVC h, s1).
Proof.
  intros HpcPC HmisaC Hbit0 Hbit1 Hvalign4 Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv HisRVC.
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
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
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

Section SFetchWalk.
  Context (root_ppn : mword 44).
  Context (va : mword 64) (svpn : mword 27) (menvcfg0 satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte : PMA_Region) (s : mstate).
  Let sf := pw_filled root_ppn svpn tlbvec s.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn.
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec (tlb_hash (__id 39) svpn) = None.
  (* the superpage-identity geometry of [va], phrased over [svpn] (= svpn_of va) *)
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.
  Hypothesis Hvpn2 : subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9).
  Hypothesis Hmvpn : sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45).
  Hypothesis Hmppn : zero_extend' 44 (and_vec (sfetch_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44).
  Hypothesis Hmask : and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45).
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.
  (* ---- page-walk (PTE read) hypotheses, at s ---- *)
  Hypothesis pHA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis pHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis pHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis pHR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis pHmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte.
  Hypothesis pHalign : is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true.
  Hypothesis pHpte : (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis pHc : exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s).
  Hypothesis pHsig : exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s).
  Hypothesis pHh : exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s).
  Hypothesis pHbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j).
  (* ---- instruction-read pmp facts, at the FILLED state sf ---- *)
  Hypothesis iHA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) = TOR.
  Hypothesis iHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0) = false.
  Hypothesis iHX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) ('b"1") = true.
  Hypothesis iHpriv : register_lookup cur_privilege sf.(sregs) = Supervisor.

  Let Htrwalk : exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), sf) :=
    exec_translateAddr_fetch_walk root_ppn va svpn region_pte menvcfg0 satp0 tlbvec s
      Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec Hcanon Hvpn_def Hident Hvpn2 Hmvpn Hmppn
      pHA pHord pHrange pHR pHmatch pHalign pHpte pHc pHsig pHh pHbytes Hmenv HPBMTE.

  (* -- width 4 read at va, at sf -- *)
  Section WalkW4.
    Context (region : PMA_Region) (w : mword 32).
    Hypothesis iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 4)) = PMP_Match.
    Hypothesis iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs)) (Physaddr va) 4 = Some region.
    Hypothesis iHalign : is_aligned_paddr (Physaddr va) 4 = true.
    Hypothesis iHexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
    Hypothesis iHc : exec (within_clint (Physaddr va) 4) sf = Some (false, sf).
    Hypothesis iHsig : exec (within_sig (Physaddr va) 4) sf = Some (false, sf).
    Hypothesis iHh : exec (within_htif_readable (Physaddr va) 4) sf = Some (false, sf).
    Hypothesis iHbytes : forall j : nat, (N.of_nat j < 4)%N -> sf.(mem) !! (pa_add va j) = Some (nth_byte w j).


    (* outer assemblies, 4-aligned *)
    Hypothesis Hvalign : is_aligned_vaddr (Virtaddr va) 4 = true.

    Section WalkRVC4.
      Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.
    End WalkRVC4.

    Section WalkFBase4.
      Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
    End WalkFBase4.
  End WalkW4.

  (* -- width 2 read at va (2-aligned, not 4-aligned RVC), at sf -- *)
  Section WalkW2.
    Context (region : PMA_Region) (h : mword 16).
    Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
    Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
    Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
    Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.
    Hypothesis iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 2)) = PMP_Match.
    Hypothesis iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs)) (Physaddr va) 2 = Some region.
    Hypothesis iHalign : is_aligned_paddr (Physaddr va) 2 = true.
    Hypothesis iHexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
    Hypothesis iHc : exec (within_clint (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHsig : exec (within_sig (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHh : exec (within_htif_readable (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHbytes : forall j : nat, (N.of_nat j < 2)%N -> sf.(mem) !! (pa_add va j) = Some (nth_byte h j).
    Hypothesis HisRVC : isRVC h = true.


  End WalkW2.

  (* -- the 2+2 F_Base read at a 2-aligned (not 4) va: the FIRST halfword's
     translation WALKS and fills slot 5 (s -> sf); the SECOND halfword's
     translation (same vpn) HITS the just-filled entry at sf. -- *)
  Section WalkFBase2.
    Context (regl regh : PMA_Region) (w : mword 32).
    Let ilo : mword 16 := subrange_vec_dec w 15 0.
    Let ihi : mword 16 := subrange_vec_dec w 31 16.
    Let vah : mword 64 := add_vec_int va 2.
    Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
    Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
    Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
    Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.
    (* the (same-page) superpage-identity geometry of [vah = va+2] over [svpn] *)
    Hypothesis Hcanonh : neq_vec (bits_of_virtaddr (Virtaddr vah))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub 39 1) 0)) = false.
    Hypothesis Hvpn_defh : autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn.
    Hypothesis Hidenth : zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr vah)) (Z.sub pagesize_bits 1) 0)) = vah.
    (* low half (2 bytes at va), read at sf *)
    Hypothesis iHrangeL : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
        (uint va) (uint (to_bits 64 2)) = PMP_Match.
    Hypothesis iHmatchL : matching_pma_region (register_lookup pma_regions sf.(sregs)) (Physaddr va) 2 = Some regl.
    Hypothesis iHalignL : is_aligned_paddr (Physaddr va) 2 = true.
    Hypothesis iHexecL : (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
    Hypothesis iHcL : exec (within_clint (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHsigL : exec (within_sig (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHhL : exec (within_htif_readable (Physaddr va) 2) sf = Some (false, sf).
    Hypothesis iHbytesL : forall j : nat, (N.of_nat j < 2)%N -> sf.(mem) !! (pa_add va j) = Some (nth_byte ilo j).
    (* high half (2 bytes at va+2), read at sf (HITS the just-filled slot 5) *)
    Hypothesis iHrangeH : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
        (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
        (uint vah) (uint (to_bits 64 2)) = PMP_Match.
    Hypothesis iHmatchH : matching_pma_region (register_lookup pma_regions sf.(sregs)) (Physaddr vah) 2 = Some regh.
    Hypothesis iHalignH : is_aligned_paddr (Physaddr vah) 2 = true.
    Hypothesis iHexecH : (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
    Hypothesis iHcH : exec (within_clint (Physaddr vah) 2) sf = Some (false, sf).
    Hypothesis iHsigH : exec (within_sig (Physaddr vah) 2) sf = Some (false, sf).
    Hypothesis iHhH : exec (within_htif_readable (Physaddr vah) 2) sf = Some (false, sf).
    Hypothesis iHbytesH : forall j : nat, (N.of_nat j < 2)%N -> sf.(mem) !! (pa_add vah j) = Some (nth_byte ihi j).
    Hypothesis HnotRVC : isRVC ilo = false.
    Hypothesis Hconcat : concat_vec ihi ilo = w.

  End WalkFBase2.
End SFetchWalk.

(* ===================================================================== *)
(* 7. smode_config -- the ambient resources a straight-line S-mode kernel *)
(* instruction reads and preserves (mirror of InstrBytes' mmode_config).  *)
(* [satp0] is a PARAMETER: the kernelvec proofs need the CONCRETE Sv39    *)
(* root ppn for the page walk, so the satp VALUE stays visible.           *)
(* ===================================================================== *)

Section SmodeCoreIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition smode_config (dq : dfrac) : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ{ dq } Supervisor ∗
     (∃ mstatus0 : mword 64,
        mstatus ↦ᵣ{ dq } mstatus0 ∗
        ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ ∗
        ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
        ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝) ∗
     (∃ mie_v mdv0 : mword 64,
        mie ↦ᵣ{ dq } mie_v ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
        ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
     (∃ menvcfg0 : mword 64,
        menvcfg ↦ᵣ{ dq } menvcfg0 ∗
        ⌜ eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ⌝))%I.

  (* unbundle: expose the raw cells + the pure facts. *)
  Lemma smode_config_unbundle (dq : dfrac) :
    smode_config dq -∗
    hw_config ∗ minstret_inv ∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{ dq } Supervisor ∗
    (∃ mstatus0 : mword 64,
       mstatus ↦ᵣ{ dq } mstatus0 ∗
       ⌜ eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ⌝ ∗
       ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
       ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝) ∗
    (∃ mie_v mdv0 : mword 64,
       mie ↦ᵣ{ dq } mie_v ∗ mideleg ↦ᵣ{ dq } mdv0 ∗
       ⌜ and_vec mie_v (not_vec mdv0) = zeros' 64 ⌝) ∗
    (∃ menvcfg0 : mword 64,
       menvcfg ↦ᵣ{ dq } menvcfg0 ∗
       ⌜ eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ⌝).
  Proof. iIntros "H". iExact "H". Qed.

  (* rebuild from raw cells + the pure facts (inverse of unbundle). *)
  Lemma smode_config_rebuild (dq : dfrac) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    smode_config dq.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmie HPBMTE)
            "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv".
    iFrame "Hhw Hinv Hhs Hpriv".
    iSplitL "Hms".
    { iExists mstatus0. iFrame "Hms". iPureIntro. exact (conj HSIE (conj HMPRV HSXL)). }
    iSplitL "Hmie Hmdl".
    { iExists mie_v, mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmie. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. exact HPBMTE.
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
  Lemma wp_exec_step_decode_execute_inv_priv (p : Privilege) E Φ {dq : dfrac} :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ, mstate_interp σ ={E ∖ ↑minstretN}=∗
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
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "Hinv Hhs H".
    iApply (wp_exec_step_hart_active_inv E Φ HN with "Hinv Hhs").
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

  (* the walk's memory footprint: the identity superpage PTE. *)
  Definition pte_super_bytes (root_ppn : mword 44) (dq : dfrac) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, (pa_add (pte_paddr root_ppn) j) ↦ₘ{ dq } nth_byte pte_super j)%I.

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
       pte_super_bytes root_ppn (DfracOwn 1))%I.

  (* introduce from the raw pieces (satp + facts + tlb + consistency + pte). *)
  Lemma tlb_inv_intro (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ pte_super_bytes root_ppn (DfracOwn 1) -∗
    tlb_inv root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hc. iIntros "Hsatp Htlb Hpte".
    iExists satp0, tlbvec. iFrame "Hsatp Htlb Hpte". iPureIntro. tauto.
  Qed.

  (* open: expose satp cell + the three SATP facts + tlb cell + consistency  *)
  (* + the owned super-PTE bytes.                                            *)
  Lemma tlb_inv_open (root_ppn : mword 44) :
    tlb_inv root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_pt_consistent root_ppn tlbvec ⌝ ∗
      pte_super_bytes root_ppn (DfracOwn 1).
  Proof. iIntros "H". iExact "H". Qed.

  (* close: re-seal after a read/fill that preserves consistency and does    *)
  (* not change satp / the pte bytes.                                        *)
  Lemma tlb_inv_close (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_pt_consistent root_ppn tlbvec ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ pte_super_bytes root_ppn (DfracOwn 1) -∗
    tlb_inv root_ppn.
  Proof. apply tlb_inv_intro. Qed.

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
  Lemma fetch_from_instr_bytes_s_consistent (root_ppn : mword 44)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64) (region_pte : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    tlb_pt_consistent root_ppn tlbvec ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
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
    pte_super_bytes root_ppn dqb -∗
    instr_bytes pc r -∗
    ⌜ ∃ tlbvec2, exec (fetch tt) σ = Some (r, set_reg σ tlb tlbvec2)
                 ∧ tlb_pt_consistent root_ppn tlbvec2 ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hppn Hasid Hcons HPBMTE HX Hcov Hpmpp Hmatchp0 Hptep Halignp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    destruct Hpmpp as (HA & Hord & Hrangep & HR).
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
    (* PTE bytes + RAM-ness of the PTE *)
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
    pose proof (addr_is_ram_not_in_clint _ Hramp) as Hncp; pose proof (addr_is_ram_not_in_sig _ Hramp) as Hnsp.
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
    assert (Hrangep' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrangep).
    assert (Hmatchp : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte)
      by (rewrite Lpma; exact Hmatchp0).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
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
        destruct (translate_chunk_ram root_ppn pc satp0 menvcfg0 region_pte tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons Hram
                    HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                    (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                    (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                    (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                    Hpbytesf Lmenv HPBMTE)
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
                      i1bytes L1priv HnotRVC) as Hfetch.
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
        destruct (translate_chunk_ram root_ppn pc satp0 menvcfg0 region_pte tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons Hraml
                    HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                    (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                    (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                    (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                    Hpbytesf Lmenv HPBMTE)
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
        assert (H1rangep' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
                  (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match)
          by (rewrite L1pmpaddr; exact Hrangep).
        assert (H1matchp : matching_pma_region (register_lookup pma_regions s1.(sregs))
                  (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte)
          by (rewrite L1pma; exact Hmatchp0).
        assert (H1pbytes : forall j : nat, (N.of_nat j < 8)%N ->
                  s1.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j))
          by (rewrite Hs1mem; exact Hpbytesf).
        (* --- high chunk: translate pc+2, through svpn_of(pc+2), in s1 -> s2.
             The high slot [tlb_hash 39 (svpn_of (pc+2))] gets its OWN
             None-or-Some disjunction from [Hs1cons] (post-low-fill
             consistency) at THAT hash -- it may itself be empty and WALK. --- *)
        destruct (translate_chunk_ram root_ppn (add_vec_int pc 2) satp0 menvcfg0 region_pte
                    (register_lookup tlb s1.(sregs)) s1
                    L1priv L1SXL L1satp Hmode Hppn Hasid eq_refl Hs1cons Hramh
                    H1A' H1ord' H1rangep' H1R' H1matchp Halignp Hptep
                    (within_clint_false (pte_paddr root_ppn) 8 s1 Hncp ltac:(lia))
                    (within_sig_false  (pte_paddr root_ppn) 8 s1 Hnsp ltac:(lia))
                    (within_htif_false (pte_paddr root_ppn) 8 s1 L1htif)
                    H1pbytes L1menv HPBMTE)
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
                      i1bytesL L1priv
                      i2HA i2Hord i2rangeH i2HX i2matchH Halignh0 Hxh
                      (within_clint_false (add_vec_int pc 2) 2 s2 Hnch ltac:(lia))
                      (within_sig_false  (add_vec_int pc 2) 2 s2 Hnsh ltac:(lia))
                      (within_htif_false (add_vec_int pc 2) 2 s2 L2htif)
                      i2bytesH L2priv HnotRVC (concat_subranges_id w)) as Hfetch.
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
        destruct (translate_chunk_ram root_ppn pc satp0 menvcfg0 region_pte tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons Hram
                    HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                    (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                    (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                    (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                    Hpbytesf Lmenv HPBMTE)
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
                      i1bytes L1priv HisRVC') as Hfetch.
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
        destruct (translate_chunk_ram root_ppn pc satp0 menvcfg0 region_pte tlbvec σ
                    Lpriv HSXL' Lsatp Hmode Hppn Hasid Ltlb Hcons Hram
                    HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                    (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                    (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                    (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                    Hpbytesf Lmenv HPBMTE)
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
                      i1bytes L1priv HisRVC) as Hfetch.
        exists (register_lookup tlb s1.(sregs)).
        split; [ rewrite <- Hs1eq; exact Hfetch | exact Hs1cons ].
    - (* F_Error *) done.
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
  Lemma wp_instr_s_tlbinv (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq : dfrac} :
    ↑minstretN ⊆ E →
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    smode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config dq -∗
          pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
          pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
          tlb_inv root_ppn -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    (* Open [tlb_inv] ONCE and drive the UNIFIED fetch (each chunk translates
       through its own vpn, 0/1/2 slots filled) -- no hit/walk split, no
       same-page premise.  Re-bundle [smode_config] and re-seal [tlb_inv]
       (with the fetch's [tlbvec2]) in the caller's continuation. *)
    iIntros (HN HX Hcov Hpmpp Hpteregion Halignp)
      "Hsm Hpmpc Hpmpa Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes)".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HSIE & %HMPRV & %HSXL)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent root_ppn σ pc r
                 satp0 mstatus0 misa0 menvcfg0 region_pte pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov Hpmpp
                 Hmatchp0 Hptep Halignp
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
    { unfold σf, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hmiec Hmdlc Hmenvc] Hpmpc Hpmpa [Hsatp Htlb Hpbytes] Hpc'").
      - iApply (smode_config_rebuild dq mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL Hmm HPBMTE
                  with "Hhw Hinv Hhs' Hpriv Hmstatus Hmiec Hmdlc Hmenvc").
      - iApply (tlb_inv_close root_ppn satp0 tlbvec2 Hmode Hasid Hppn Hcons2
                  with "Hsatp Htlb Hpbytes"). }
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

(* discharge encdec_reg_backwards (subrange w hi lo) -> Regidx ... *)
Local Ltac kv_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac kv_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; cwalk s HmisaC;
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

Local Ltac kv_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Lemma kv_decode1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed kv_h1) s = Some (C_ADDI16SP kv_imm1, s).
Proof.
  intro HmisaC.
  kv_open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. kv_ast.
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
    assert (Hlpad : is_lpad_instruction (ITYPE (caddi16sp_imm kv_imm1, sp, sp, ADDI)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr kv_pc1) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr kv_pc1) 4 = true) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC kv_h1 = true) by (vm_compute; reflexivity).
    assert (Hsub : subrange_vec_dec kv_w1 15 0 = kv_h1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! ((KernelSyms.kernelvec) + Z.of_nat j)%Z = Some (nth_byte kv_w1 j)).
    { intros j Hj;
        do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC kv_h1).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc4 kv_pc1 kv_h1 kv_w1 H2al H4al Hrvc Hsub).
      iApply (kernel_window_pc (KernelSyms.kernelvec) kv_w1 4 kv_pc1 eq_refl Hbytes with "Ht").
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC _. cbn [fetch_is_rvc].
      exists (C_ADDI16SP kv_imm1).
      split; [exact (kv_decode1 σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_ADDI16SP kv_imm1 s).
  Qed.

End SmodeDemo.

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
   - Sv39 translation of a kernelvec-page virtual address: TLB HIT via the
     identity superpage entry [pw_tlb_entry] (state-preserving), and TLB MISS
     via the one-PTE page WALK [exec_translateAddr_fetch_walk] (reads
     [pte_super] at [pte_paddr root_ppn], FILLS the TLB at index 5);
   - the full S-mode fetch reductions for every [instr_bytes] geometry
     (F_Base / F_RVC x 4-aligned / 2-aligned) on the hit path, and the
     4-aligned geometries on the walk path;
   - [smode_config dq satp0] -- the S-mode ambient-configuration bundle
     (mirror of InstrBytes' [mmode_config]) + unbundle/rebuild/split/combine;
   - [fetch_from_instr_bytes_s] / [fetch_from_instr_bytes_s_walk] -- the
     S-mode fetch discharges over the SAME [instr_bytes] footprint (the Sv39
     kernel map is identity on kernel text, so the physical window equals the
     virtual pc numerically);
   - [instr_lift_s] -- the S-mode lift of the (privilege-generic) [instr]
     predicate;
   - [wp_exec_step_decode_execute_inv_priv] -- the privilege-generic,
     fetch-state-threading decode/execute step engine;
   - [wp_instr_s] (TLB hit) and [wp_instr_s_fill] (page walk, hands the
     continuation the FILLED tlb cell) -- the S-mode [wp_instr] mirrors;
   - demo lemmas: a 32-bit decode under Supervisor ([decode_jal_S]) and the
     [instr] constructor for kernelvec's first instruction (c.addi16sp at
     0x800053e0) from [kernel_text]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
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

(* The pure TOR-entry-0 grant facts a Supervisor fetch at [a] (width [width])
   needs, phrased over the pmpcfg/pmpaddr VALUES (converted to the
   register_lookup forms at the state via reg_valid). *)
Definition pmp_tor0_sfetch (cfg : type_of_register pmpcfg_n)
    (addrs : type_of_register pmpaddr_n) (a : mword 64) (width : Z) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg 0)) = TOR
  /\ zopz0zKzJ_u (zeros' 64) (vec_access_dec addrs 0) = false
  /\ pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
       (Z.mul (uint (vec_access_dec addrs 0)) 4)
       (uint a) (uint (to_bits 64 width)) = PMP_Match
  /\ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec cfg 0)) ('b"1") = true.

(* All the widths/addresses one instruction fetch can touch: a 4-byte read at
   [pc] (4-aligned F_Base / F_RVC window), a 2-byte read at [pc], and a 2-byte
   read at [pc+2] (the high half of a 2-aligned F_Base). *)
Definition pmp_tor0_sfetch_all (cfg : type_of_register pmpcfg_n)
    (addrs : type_of_register pmpaddr_n) (pc : mword 64) : Prop :=
  pmp_tor0_sfetch cfg addrs pc 4
  /\ pmp_tor0_sfetch cfg addrs pc 2
  /\ pmp_tor0_sfetch cfg addrs (add_vec_int pc 2) 2.

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

(* intro: an all-empty TLB is consistent (with ANY table). *)
Lemma tlb_pt_consistent_all_none (root_ppn : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall i, 0 <= i < 2 ^ 6 -> vec_access_dec tlbvec i = None) ->
  tlb_pt_consistent root_ppn tlbvec.
Proof. intros Hn i Hi. left. apply Hn. exact Hi. Qed.

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

(* The geometric facts pinning [va] to the kernelvec code page: canonical
   (high bits are the sign extension), VPN = kv_vpn, and identity
   (ppn 0x80005 ++ page offset = va).  vm_compute for concrete va. *)
Definition kv_fetch_geom (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false
  /\ autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = kv_vpn
  /\ zero_extend' 64 (concat_vec (mword_of_int 0x80005 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.

Section KVTranslate.
  Context (root_ppn : mword 44).

  (* ---- TLB HIT (state-preserving) ---- *)

  Lemma exec_translate_TLB_hit_super (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) kv_vpn (InstructionFetch tt) Supervisor mxr do_sum
            tt 5 (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt), s).
  Proof.
    destruct mxr, do_sum; vm_compute; reflexivity.
  Qed.

  Lemma exec_lookup_TLB_hit_super (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) kv_vpn) s
      = Some (Some (5, pw_tlb_entry root_ppn (mword_of_int 0)), s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) kv_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    replace (match_TLB_Entry (pw_tlb_entry root_ppn (mword_of_int 0)) (mword_of_int 0 : mword 16)
               (sign_extend' (57 - 12) kv_vpn)) with true
      by (vm_compute; reflexivity).
    apply exec_returnm.
  Qed.

  Lemma exec_translate_hit_super (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn kv_vpn (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_super tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_super.
  Qed.

  (* Instruction-fetch translation at a symbolic code-page address va: hit. *)
  Lemma exec_translateAddr_fetch_hit (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom va ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hasid Htlb Hvec (Hcanon & Hvpn_def & Hident).
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
      replace vpnx with kv_vpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_hit_super _ _ _ tlbvec s Htlb Hvec)).
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
  Lemma exec_pt_walk_super (mxr do_sum : bool) (region : PMA_Region) (menvcfg0 : mword 64) s :
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
    exec (pt_walk 39 kv_vpn (InstructionFetch tt) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (mword_of_int 0x80005) (autocast (T := mword) pte_super)
                    (Physaddr (pte_paddr root_ppn)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
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
      replace a with (pte_paddr root_ppn : mword 64) by (unfold pte_paddr; reflexivity);
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
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  (* add_to_TLB installs the entry at index 5 (= tlb_hash 39 kv_vpn). *)
  Lemma exec_add_to_TLB_super (asid : mword 16) s :
    exec (add_to_TLB 39 asid kv_vpn (mword_of_int 0x80005 : mword 44) (autocast (T := mword) pte_super)
            (Physaddr (pte_paddr root_ppn)) 2 false) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 5 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    unfold add_to_TLB. cbn zeta.
    replace (tlb_hash (__id 39) kv_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    do 3 f_equal.
  Qed.

  Lemma exec_translate_TLB_miss_super (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region) (menvcfg0 : mword 64) s :
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
    exec (translate_TLB_miss 39 asid root_ppn kv_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 5 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_super mxr do_sum region menvcfg0 s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_super asid s)).
    apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_miss (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
    exec (lookup_TLB 39 asid kv_vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) kv_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. apply exec_returnm.
  Qed.

  Lemma exec_translate_walk (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region)
        (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
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
    exec (translate 39 asid root_ppn kv_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_super mxr do_sum asid region menvcfg0 s
             HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
  Qed.

  (* The state after the fetch's page walk: TLB filled at index 5. *)
  Definition pw_filled (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) : mstate :=
    set_reg s tlb (vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).

  (* FULL Sv39 fetch translation of a kernelvec-page vaddr with an EMPTY TLB
     slot 5: the page walk reads the PTE from memory and fills the TLB. *)
  Lemma exec_translateAddr_fetch_walk (va : mword 64) (region : PMA_Region)
        (menvcfg0 satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
    kv_fetch_geom va ->
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
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), pw_filled tlbvec s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec (Hcanon & Hvpn_def & Hident)
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
      replace vpnx with kv_vpn by (symmetry; exact Hvpn_def);
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ===================================================================== *)
  (* 6. The S-mode fetch reductions (TLB hit), one per instr_bytes geometry. *)
  (* ===================================================================== *)

Section SFetchHit.
  Context (va : mword 64) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hgeom : kv_fetch_geom va.

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

    Lemma exec_fetch_bytes_2_S_hit : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s).
    Proof using Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR.
          rewrite (exec_translateAddr_fetch_hit va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom).
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) s
             = Some (inr (Ok h), s))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_2_S PBMT_PMA va region h s
                     HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.
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
    Proof using Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR.
          rewrite (exec_translateAddr_fetch_hit va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom).
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
(* 6b. The outer S-mode fetch assemblies (TLB hit), one per geometry.     *)
(* ===================================================================== *)

Section SFetchHitOuter.
  Context (root_ppn : mword 44).
  Context (va : mword 64) (satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
  Hypothesis Hgeom : kv_fetch_geom va.
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
      exec_fetch_bytes_4_S_hit root_ppn va satp0 tlbvec s
        Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom region w
        HA Hord Hrange4 HX Hmatch Halign4p Hexec Hc Hsig Hh Hbytes.

    (* F_Base at a 4-aligned va (single 4-byte read). *)
    Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
    Lemma exec_fetch_F_Base_4_S_hit : exec (fetch tt) s = Some (F_Base w, s).
    Proof using All.
      destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
      assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
      { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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

    (* F_RVC at a 4-aligned va (whole 4-byte window read; low 16 = the instr). *)
    Lemma exec_fetch_RVC_4_S_hit : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
    Proof using All.
      destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
      assert (Halign4p : is_aligned_paddr (Physaddr va) 4 = true) by exact Hvalign.
      pose proof (exec_fetch_bytes_4_S_hit root_ppn va satp0 tlbvec s
        Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom region w
        HA Hord Hrange4 HX Hmatch Halign4p Hexec Hc Hsig Hh Hbytes) as Hfb4.
      assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
      { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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

      Lemma exec_fetch_RVC_2_S_hit : exec (fetch tt) s = Some (F_RVC h, s).
      Proof using All.
        pose proof (exec_fetch_bytes_2_S_hit root_ppn va satp0 tlbvec s
          Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom region h
          HA Hord Hrange2 HX Hmatch Halign2 Hexec Hc Hsig Hh Hbytes) as Hfb2.
        assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
        { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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
    End RVC2.

    Section FBase2.
      Context (regl regh : PMA_Region) (w : mword 32).
      Let ilo : mword 16 := subrange_vec_dec w 15 0.
      Let ihi : mword 16 := subrange_vec_dec w 31 16.
      Let vah : mword 64 := add_vec_int va 2.
      Hypothesis Hgeomh : kv_fetch_geom vah.
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

      Lemma exec_fetch_F_Base_2_S_hit : exec (fetch tt) s = Some (F_Base w, s).
      Proof using All.
        pose proof (exec_fetch_bytes_2_S_hit root_ppn va satp0 tlbvec s
          Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom regl ilo
          HA Hord Hrange2 HX Hmatchl Halign2 Hexecl Hcl Hsigl Hhl Hbytesl) as Hfb2l.
        assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
        { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
        rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
        assert (Hfb2h : exec (fetch_bytes va vah 2) s = Some (@FetchBytes_Success 2 ihi, s)).
        { unfold fetch_bytes.
          rewrite exec_catch_early_return.
          change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _
            (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                    (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) s
                 = Some (inr (Ok (Physaddr vah, PBMT_PMA, init_ext_ptw)), s))).
          2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
              rewrite execR_liftR.
              rewrite (exec_translateAddr_fetch_hit root_ppn vah satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeomh).
              cbn match. reflexivity. }
          cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr vah, PBMT_PMA) s)).
          cbv iota beta.
          rewrite (execR_bind_Some _ _ _ _ _
            (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr vah) 2 false false false)) s
                 = Some (inr (Ok ihi), s))).
          2:{ rewrite execR_liftR.
              rewrite (exec_mem_read_fetch_2_S PBMT_PMA vah regh ihi s
                         HA Hord Hrange2h HX Hmatchh Halign2h Hexech Hch Hsigh Hhh Hbytesh Hcp).
              cbn match. reflexivity. }
          cbv iota beta. rewrite autocast_mword_id_16.
          rewrite execR_returnR_fwd. cbn match. reflexivity. }
        rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
        cbv iota beta. rewrite execR_returnR_fwd. cbn match.
        rewrite Hconcat. reflexivity.
      Qed.
    End FBase2.
  End Aligned2.
End SFetchHitOuter.

(* ===================================================================== *)
(* 6c. The S-mode fetch reductions with an EMPTY TLB slot 5: the page     *)
(* walk reads the PTE (at the pre-fetch state s) and FILLS the TLB; the   *)
(* instruction bytes are then read at the filled state sf.  Single-read   *)
(* geometries only (F_Base 4-aligned / F_RVC both alignments); the 2+2    *)
(* F_Base read with a mid-fetch fill is left for K2.                      *)
(* ===================================================================== *)

Section SFetchWalk.
  Context (root_ppn : mword 44).
  Context (va : mword 64) (menvcfg0 satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte : PMA_Region) (s : mstate).
  Let sf := pw_filled root_ppn tlbvec s.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn.
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = None.
  Hypothesis Hgeom : kv_fetch_geom va.
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
    exec_translateAddr_fetch_walk root_ppn va region_pte menvcfg0 satp0 tlbvec s
      Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec Hgeom
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

    Lemma exec_fetch_bytes_4_S_walk : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, sf).
    Proof using Htrwalk iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), sf))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite Htrwalk.
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) sf)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) sf
             = Some (inr (Ok w), sf))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w sf
                     iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.

    (* outer assemblies, 4-aligned *)
    Hypothesis Hvalign : is_aligned_vaddr (Virtaddr va) 4 = true.

    Section WalkRVC4.
      Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.
      Lemma exec_fetch_RVC_4_S_walk : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), sf).
      Proof using All.
        destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
        assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
        { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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
        rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_S_walk).
        cbv iota beta. rewrite HisRVC. cbv iota beta.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.
    End WalkRVC4.

    Section WalkFBase4.
      Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
      Lemma exec_fetch_F_Base_4_S_walk : exec (fetch tt) s = Some (F_Base w, sf).
      Proof using All.
        destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
        assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
        { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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
        rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_S_walk).
        cbv iota beta. rewrite HnotRVC. cbv iota beta.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.
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

    Lemma exec_fetch_bytes_2_S_walk : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, sf).
    Proof using Htrwalk iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv.
      unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), sf))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite Htrwalk.
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) sf)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) sf
             = Some (inr (Ok h), sf))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_2_S PBMT_PMA va region h sf
                     iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.

    Lemma exec_fetch_RVC_2_S_walk : exec (fetch tt) s = Some (F_RVC h, sf).
    Proof using All.
      assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
      { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
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
      rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_2_S_walk).
      cbv iota beta. rewrite HisRVC. cbv iota beta.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.
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
    Hypothesis Hgeomh : kv_fetch_geom vah.
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

    Lemma exec_fetch_F_Base_2_S_walk : exec (fetch tt) s = Some (F_Base w, sf).
    Proof using All.
      (* register/TLB facts at the FILLED state sf *)
      assert (HSXLf : _get_Mstatus_SXL (register_lookup mstatus sf.(sregs)) = 'b"10").
      { unfold sf, pw_filled, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact HSXL | vm_compute; reflexivity]. }
      assert (Hsatpf : register_lookup satp sf.(sregs) = satp0).
      { unfold sf, pw_filled, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact Hsatp | vm_compute; reflexivity]. }
      assert (Htlbf : register_lookup tlb sf.(sregs)
                      = vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).
      { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      assert (Hvec5f : vec_access_dec (vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0)))) 5
                       = Some (pw_tlb_entry root_ppn (mword_of_int 0))).
      { rewrite (vec64_access_update tlbvec 5 5 _ ltac:(lia)). reflexivity. }
      assert (HpcPCf : register_lookup PC sf.(sregs) = va).
      { unfold sf, pw_filled, set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [exact HpcPC | vm_compute; reflexivity]. }
      assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
      { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
      assert (HrdPCf : exec (Defs.read_reg PC) sf = Some (va, sf)).
      { rewrite (exec_read_reg PC sf). rewrite HpcPCf. reflexivity. }
      (* first halfword: the 2-byte fetch_bytes that WALKS (s -> sf) *)
      assert (Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, sf)).
      { unfold fetch_bytes.
        rewrite exec_catch_early_return.
        change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                  (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
               = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), sf))).
        2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
            rewrite execR_liftR. rewrite Htrwalk. cbn match. reflexivity. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) sf)).
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) sf
               = Some (inr (Ok ilo), sf))).
        2:{ rewrite execR_liftR.
            rewrite (exec_mem_read_fetch_2_S PBMT_PMA va regl ilo sf
                       iHA iHord iHrangeL iHX iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHbytesL iHpriv).
            cbn match. reflexivity. }
        cbv iota beta. rewrite autocast_mword_id_16.
        rewrite execR_returnR_fwd. cbn match. reflexivity. }
      (* second halfword: fetch_bytes at sf, HIT on the filled slot 5 *)
      assert (Hfb2h : exec (fetch_bytes va vah 2) sf = Some (@FetchBytes_Success 2 ihi, sf)).
      { unfold fetch_bytes.
        rewrite exec_catch_early_return.
        change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                  (Defs.liftR (translateAddr (Virtaddr vah) (InstructionFetch tt)))) sf
               = Some (inr (Ok (Physaddr vah, PBMT_PMA, init_ext_ptw)), sf))).
        2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt sf)).
            rewrite execR_liftR.
            rewrite (exec_translateAddr_fetch_hit root_ppn vah satp0
                       (vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0)))) sf
                       iHpriv HSXLf Hsatpf Hmode Hasid Htlbf Hvec5f Hgeomh).
            cbn match. reflexivity. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr vah, PBMT_PMA) sf)).
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr vah) 2 false false false)) sf
               = Some (inr (Ok ihi), sf))).
        2:{ rewrite execR_liftR.
            rewrite (exec_mem_read_fetch_2_S PBMT_PMA vah regh ihi sf
                       iHA iHord iHrangeH iHX iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHbytesH iHpriv).
            cbn match. reflexivity. }
        cbv iota beta. rewrite autocast_mword_id_16.
        rewrite execR_returnR_fwd. cbn match. reflexivity. }
      (* assemble the outer fetch (state changes s -> sf at the FIRST read) *)
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
      rewrite (execR_liftR_seq _ _ _ _ _ HrdPCf).
      rewrite (execR_liftR_seq _ _ _ _ _ HrdPCf).
      rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
      cbv iota beta. rewrite execR_returnR_fwd. cbn match.
      rewrite Hconcat. reflexivity.
    Qed.
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

  (* fraction-generic split/combine (mirrors mmode_config_split/_combine). *)
  Lemma smode_config_split (q : Qp) :
    smode_config (DfracOwn q) ⊢
      smode_config (DfracOwn (q/2)) ∗ smode_config (DfracOwn (q/2)).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (ms0) "(Hms & %HSIE & %HMPRV & %HSXL)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmi & Hmd & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hme & %HPBMTE)".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iDestruct "Hmi" as "[Hmi1 Hmi2]".
    iDestruct "Hmd" as "[Hmd1 Hmd2]".
    iDestruct "Hme" as "[Hme1 Hme2]".
    iSplitL "Hhs1 Hpriv1 Hms1 Hmi1 Hmd1 Hme1".
    - iFrame "Hhw Hinv Hhs1 Hpriv1".
      iSplitL "Hms1". { iExists ms0. iFrame "Hms1 %". }
      iSplitL "Hmi1 Hmd1". { iExists mie_v, mdv0. iFrame "Hmi1 Hmd1 %". }
      iExists menvcfg0. iFrame "Hme1 %".
    - iFrame "Hhw Hinv Hhs2 Hpriv2".
      iSplitL "Hms2". { iExists ms0. iFrame "Hms2 %". }
      iSplitL "Hmi2 Hmd2". { iExists mie_v, mdv0. iFrame "Hmi2 Hmd2 %". }
      iExists menvcfg0. iFrame "Hme2 %".
  Qed.

  Lemma smode_config_combine (q : Qp) :
    smode_config (DfracOwn (q/2)) -∗ smode_config (DfracOwn (q/2)) -∗
    smode_config (DfracOwn q).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs1 & Hpriv1 & Hmst1 & Hmie1 & Hmenv1)
             (_ & _ & Hhs2 & Hpriv2 & Hmst2 & Hmie2 & Hmenv2)".
    iDestruct "Hmst1" as (ms0) "(Hms1 & %HSIE & %HMPRV & %HSXL)".
    iDestruct "Hmst2" as (ms0') "(Hms2 & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hms1 Hms2") as %<-.
    iDestruct "Hmie1" as (mie_v mdv0) "(Hmi1 & Hmd1 & %Hmm)".
    iDestruct "Hmie2" as (mie_v' mdv0') "(Hmi2 & Hmd2 & _)".
    iDestruct (reg_pointsto_agree with "Hmi1 Hmi2") as %<-.
    iDestruct (reg_pointsto_agree with "Hmd1 Hmd2") as %<-.
    iDestruct "Hmenv1" as (menvcfg0) "(Hme1 & %HPBMTE)".
    iDestruct "Hmenv2" as (menvcfg0') "(Hme2 & _)".
    iDestruct (reg_pointsto_agree with "Hme1 Hme2") as %<-.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iCombine "Hmi1 Hmi2" as "Hmi".
    iCombine "Hmd1 Hmd2" as "Hmd".
    iCombine "Hme1 Hme2" as "Hme".
    iFrame "Hhw Hinv Hhs Hpriv".
    iSplitL "Hms". { iExists ms0. iFrame "Hms %". }
    iSplitL "Hmi Hmd". { iExists mie_v, mdv0. iFrame "Hmi Hmd %". }
    iExists menvcfg0. iFrame "Hme %".
  Qed.

  Lemma smode_config_split_half :
    smode_config (DfracOwn 1) ⊢
      smode_config (DfracOwn (1/2)) ∗ smode_config (DfracOwn (1/2)).
  Proof. apply smode_config_split. Qed.

  Lemma smode_config_combine_half :
    smode_config (DfracOwn (1/2)) -∗ smode_config (DfracOwn (1/2)) -∗
    smode_config (DfracOwn 1).
  Proof. apply smode_config_combine. Qed.

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
  Lemma fetch_from_instr_bytes_s (root_ppn : mword 44)
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    (fetch_is_rvc r = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    instr_bytes pc r -∗
    ⌜ exec (fetch tt) σ = Some (r, σ) ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hasid Hvec Hgeom HgeomB Hpmp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes".
    destruct Hpmp as ((HA & Hord & Hrange4 & HX) & Hp2 & Hp2h).
    destruct Hp2 as (_ & _ & Hrange2 & _).
    destruct Hp2h as (_ & _ & Hrange2h & _).
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    (* register_lookup forms of the pure config facts *)
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpaddr; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (Hrange4' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pc) (uint (to_bits 64 4)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrange4).
    assert (Hrange2' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pc) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrange2).
    assert (Hrange2h' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint (add_vec_int pc 2)) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrange2h).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      assert (Hgeomh : kv_fetch_geom (add_vec_int pc 2)) by (apply HgeomB; reflexivity).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: one 4-byte read *)
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr pc) 4 = Some region) by (rewrite Lpma; exact Hmatch0).
        exact (exec_fetch_F_Base_4_S_hit root_ppn pc satp0 tlbvec σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
                 HA' Hord' HX' region w Hal Hrange4' Hmatch Hexec0
                 (within_clint_false pc 4 σ Hnc ltac:(lia))
                 (within_sig_false  pc 4 σ Hns ltac:(lia))
                 (within_htif_false pc 4 σ Lhtif)
                 Hbf HnotRVC).
      + (* 2-aligned (not 4): two 2-byte reads at pc and pc+2 *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        pose proof (align2_plus2 pc H2al) as Halignh0.
        rewrite fetch_pa_id in Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
        { intros j _. unfold pa_add.
          rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb2") as %Hr2.
          iPureIntro. unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iPureIntro.
        destruct Hraml as [Hncl Hnsl]. destruct Hramh as [Hnch Hnsh].
        destruct (Hpma0 pc 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Hpma0 (add_vec_int pc 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        assert (Hml : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr pc) 2 = Some regl) by (rewrite Lpma; exact Hml0).
        assert (Hmh : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (add_vec_int pc 2)) 2 = Some regh) by (rewrite Lpma; exact Hmh0).
        assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [|exact Hj]. apply Hbytesf. lia. }
        assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [|exact Hj].
          rewrite (Haddr j Hj). apply Hbytesf. lia. }
        exact (exec_fetch_F_Base_2_S_hit root_ppn pc satp0 tlbvec σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
                 HA' Hord' HX'
                 HmisaC' Hbit0 Hbit1 Hal Hrange2' Halignl0
                 regl regh w
                 Hgeomh Hrange2h' Halignh0 Hml Hmh Hxl Hxh
                 (within_clint_false pc 2 σ Hncl ltac:(lia))
                 (within_sig_false  pc 2 σ Hnsl ltac:(lia))
                 (within_htif_false pc 2 σ Lhtif)
                 (within_clint_false (add_vec_int pc 2) 2 σ Hnch ltac:(lia))
                 (within_sig_false  (add_vec_int pc 2) 2 σ Hnsh ltac:(lia))
                 (within_htif_false (add_vec_int pc 2) 2 σ Lhtif)
                 Hbl Hbh HnotRVC (concat_subranges_id w)).
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: whole 4-byte window read *)
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
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr pc) 4 = Some region) by (rewrite Lpma; exact Hmatch0).
        assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true) by (rewrite Hsub; exact HisRVC).
        rewrite <- Hsub.
        exact (exec_fetch_RVC_4_S_hit root_ppn pc satp0 tlbvec σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
                 HA' Hord' HX' region w Hal Hrange4' Hmatch Hexec0
                 (within_clint_false pc 4 σ Hnc ltac:(lia))
                 (within_sig_false  pc 4 σ Hns ltac:(lia))
                 (within_htif_false pc 4 σ Lhtif)
                 Hbf HisRVC').
      + (* 2-aligned (not 4): a single 2-byte read *)
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
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 2) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr pc) 2 = Some region) by (rewrite Lpma; exact Hmatch0).
        exact (exec_fetch_RVC_2_S_hit root_ppn pc satp0 tlbvec σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
                 HA' Hord' HX'
                 HmisaC' Hbit0 Hbit1 Hal Hrange2' Halign0
                 region h Hmatch Hexec0
                 (within_clint_false pc 2 σ Hnc ltac:(lia))
                 (within_sig_false  pc 2 σ Hns ltac:(lia))
                 (within_htif_false pc 2 σ Lhtif)
                 Hbf HisRVC).
    - (* F_Error *) done.
  Qed.

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
  Lemma instr_lift_s (root_ppn : mword 44)
      (σ : mstate) (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    (is_rvc = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Supervisor -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dqpa } pmpaddr00 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    instr pc is_rvc i -∗
    ⌜ if is_rvc
      then ∃ (h : half) (i0 : instruction),
             exec (fetch tt) σ = Some (F_RVC h, σ) /\
             exec (decode_fetch (F_RVC h)) σ = Some (i0, σ) /\
             is_lpad_instruction i0 = false /\
             (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
      else ∃ w : word,
             exec (fetch tt) σ = Some (F_Base w, σ) /\
             exec (decode_fetch (F_Base w)) σ = Some (i, σ) /\
             is_lpad_instruction i = false ⌝.
  Proof.
    iIntros (Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom HgeomB Hpmp)
      "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iDestruct (state_interp_reg_dq σ cur_privilege dqp Supervisor
                 with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ misa dqm misa0
                 with "Hsi Hmisa") as %Lmisa.
    assert (HgeomB' : fetch_is_rvc r = false -> kv_fetch_geom (add_vec_int pc 2))
      by (rewrite Hrvc; exact HgeomB).
    iDestruct (fetch_from_instr_bytes_s root_ppn σ pc r satp0 mstatus0 misa0
                 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom HgeomB' Hpmp
                 with "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes") as %Hfetch.
    iDestruct ("Hdec" $! σ with "Hsi") as %Hdec0.
    specialize (Hdec0 ltac:(rewrite Lpriv; reflexivity) ltac:(rewrite Lmisa; exact HmisaC)).
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as %[_ []].
    - cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc. iPureIntro.
      exists w. split; [exact Hfetch | split; [exact Hdec0 | exact Hnlpad]].
    - cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp). iPureIntro.
      exists h, i0.
      split; [exact Hfetch | split; [exact Hdec | split; [exact Hnlpad0 | exact Hexp]]].
    - iDestruct "Hbytes" as %[_ []].
  Qed.

  (* =================================================================== *)
  (* 11. wp_instr_s -- the S-mode [wp_instr]: [instr]-driven step engine  *)
  (* on the TLB-HIT path.  Consumes [smode_config] + the pmp/tlb cells +  *)
  (* PC + [instr]; discharges fetch (Sv39 identity hit), decode           *)
  (* (privilege-generic), landing-pad, and dispatchInterrupt; leaves the  *)
  (* caller exactly the execute obligation of [i], branched on [is_rvc].  *)
  (* Everything consumed is handed back to the continuation unchanged.    *)
  (* =================================================================== *)
  Lemma wp_instr_s (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqsa dqt : dfrac} :
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 5 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    kv_fetch_geom pc ->
    (is_rvc = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    smode_config dq -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
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
          satp ↦ᵣ{ dqsa } satp0 -∗
          pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
          pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
          tlb ↦ᵣ{ dqt } tlbvec -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid Hvec Hgeom HgeomB Hpmp) "Hsm Hsatp Hpmpc Hpmpa Htlb Hpc Hinstr H".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HSIE & %HMPRV & %HSXL)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (instr_lift_s root_ppn σ pc is_rvc i satp0 mstatus0 misa0
                 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hasid Hvec Hgeom HgeomB Hpmp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr") as %Hlift.
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE
                 with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ Lpc with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* Reassemble [smode_config dq satp0] + the pmp/tlb cells for the caller's
       continuation: everything is held at a fraction and only read. *)
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[- Hpc' Hsatp Hpmpc Hpmpa Htlb] Hsatp Hpmpc Hpmpa Htlb Hpc'").
      iApply (smode_config_rebuild dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL Hmm HPBMTE
                with "Hhw Hinv Hhs' Hpriv Hmstatus Hmiec Hmdlc Hmenvc"). }
    iDestruct "Hexec" as %Hexec.
    destruct is_rvc.
    - (* RVC: instr_lift_s gives F_RVC h decoding to i0 with the state-generic
         [ExecuteAs i] expansion; caller's Hexec is the TARGET execute. *)
      destruct Hlift as (h & i0 & Hfetch & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σ, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σ. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_Base: instr_lift_s gives F_Base w *)
      destruct Hlift as (w & Hfetch & Hdec & Hnlpad).
      iModIntro. iExists (F_Base w), i, σ, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
  Qed.

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

  Lemma fetch_from_instr_bytes_s_walk (root_ppn : mword 44)
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
    vec_access_dec tlbvec 5 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    kv_fetch_geom pc ->
    (fetch_is_rvc r = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
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
    ⌜ exec (fetch tt) σ = Some (r, pw_filled root_ppn tlbvec σ) ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hppn Hasid Hvec HPBMTE Hgeom HgeomB Hpmp Hpmpp Hmatchp0 Hptep Halignp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    destruct Hpmp as ((HA & Hord & Hrange4 & HX) & Hp2 & Hp2h).
    destruct Hp2 as (_ & _ & Hrange2 & _).
    destruct Hp2h as (_ & _ & Hrange2h & _).
    destruct Hpmpp as (_ & _ & Hrangep & HR).
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
    (* PTE bytes + their RAM-ness *)
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
    destruct Hramp as [Hncp Hnsp].
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
    (* register/memory facts at the FILLED state sf *)
    set (sf := pw_filled root_ppn tlbvec σ).
    assert (Hsf_mem : sf.(mem) = σ.(mem)) by reflexivity.
    assert (Lfpmpc : register_lookup pmpcfg_n sf.(sregs) = pmpcfg0).
    { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Lfpmpaddr : register_lookup pmpaddr_n sf.(sregs) = pmpaddr00).
    { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Lfpma : register_lookup pma_regions sf.(sregs) = pmar0).
    { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lfpriv : register_lookup cur_privilege sf.(sregs) = Supervisor).
    { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Lfhtif : register_lookup htif_tohost_base sf.(sregs) = None).
    { unfold sf, pw_filled, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (iHA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) = TOR)
      by (rewrite Lfpmpc; exact HA).
    assert (iHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0) = false)
      by (rewrite Lfpmpaddr; exact Hord).
    assert (iHX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lfpmpc; exact HX).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w : only the 4-aligned shape is supported on the walk *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match)
          by (rewrite Lfpmpaddr; exact Hrange4).
        assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
                  (Physaddr pc) 4 = Some region) by (rewrite Lfpma; exact Hmatch0).
        assert (iHbytes : forall j : nat, (N.of_nat j < 4)%N ->
                  sf.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hsf_mem; exact Hbf).
        exact (exec_fetch_F_Base_4_S_walk root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
                 HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                 (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                 (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                 (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                 Hpbytesf iHA iHord iHX Lfpriv region w
                 iHrange iHmatch Hal Hexec0
                 (within_clint_false pc 4 sf Hnc ltac:(lia))
                 (within_sig_false  pc 4 sf Hns ltac:(lia))
                 (within_htif_false pc 4 sf Lfhtif)
                 iHbytes Hal HnotRVC).
      + (* 2-aligned (not 4): 2+2 read; the FIRST halfword's translation
           walks (σ -> sf), the SECOND hits the just-filled slot 5 at sf. *)
        assert (Hgeomh : kv_fetch_geom (add_vec_int pc 2)) by (apply HgeomB; reflexivity).
        destruct (align2_not4_facts pc H2al Hal) as (Halignl0 & Hbit0 & Hbit1).
        rewrite fetch_pa_id in Halignl0.
        pose proof (align2_plus2 pc H2al) as Halignh0.
        rewrite fetch_pa_id in Halignh0.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (add_vec_int pc 2) j = pa_add pc (2 + j)).
        { intros j _. unfold pa_add.
          rewrite avi_assoc. f_equal. lia. }
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add pc j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
        { iIntros (j Hj).
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram pc⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (add_vec_int pc 2)⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (mem_ram with "Hb2") as %Hr2.
          iPureIntro. unfold pa_add in Hr2. change (Z.of_nat 2) with 2 in Hr2. exact Hr2. }
        iPureIntro.
        destruct Hraml as [Hncl Hnsl]. destruct Hramh as [Hnch Hnsh].
        destruct (Hpma0 pc 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Hpma0 (add_vec_int pc 2) 2) as (regh & Hmh0 & Hxh & _ & _).
        assert (iHrangeL : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match)
          by (rewrite Lfpmpaddr; exact Hrange2).
        assert (iHrangeH : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                  (uint (add_vec_int pc 2)) (uint (to_bits 64 2)) = PMP_Match)
          by (rewrite Lfpmpaddr; exact Hrange2h).
        assert (iHmatchL : matching_pma_region (register_lookup pma_regions sf.(sregs))
                  (Physaddr pc) 2 = Some regl) by (rewrite Lfpma; exact Hml0).
        assert (iHmatchH : matching_pma_region (register_lookup pma_regions sf.(sregs))
                  (Physaddr (add_vec_int pc 2)) 2 = Some regh) by (rewrite Lfpma; exact Hmh0).
        assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                  sf.(mem) !! (pa_add pc j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite Hsf_mem. rewrite nth_byte_subrange_lo; [|exact Hj]. apply Hbytesf. lia. }
        assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                  sf.(mem) !! (pa_add (add_vec_int pc 2) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite Hsf_mem. rewrite nth_byte_subrange_hi; [|exact Hj].
          rewrite (Haddr j Hj). apply Hbytesf. lia. }
        exact (exec_fetch_F_Base_2_S_walk root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
                 HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                 (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                 (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                 (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                 Hpbytesf iHA iHord iHX Lfpriv
                 regl regh w
                 HmisaC' Hbit0 Hbit1 Hal Hgeomh
                 iHrangeL iHmatchL Halignl0 Hxl
                 (within_clint_false pc 2 sf Hncl ltac:(lia))
                 (within_sig_false  pc 2 sf Hnsl ltac:(lia))
                 (within_htif_false pc 2 sf Lfhtif)
                 Hbl
                 iHrangeH iHmatchH Halignh0 Hxh
                 (within_clint_false (add_vec_int pc 2) 2 sf Hnch ltac:(lia))
                 (within_sig_false  (add_vec_int pc 2) 2 sf Hnsh ltac:(lia))
                 (within_htif_false (add_vec_int pc 2) 2 sf Lfhtif)
                 Hbh HnotRVC (concat_subranges_id w)).
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window *)
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
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 4)) = PMP_Match)
          by (rewrite Lfpmpaddr; exact Hrange4).
        assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
                  (Physaddr pc) 4 = Some region) by (rewrite Lfpma; exact Hmatch0).
        assert (iHbytes : forall j : nat, (N.of_nat j < 4)%N ->
                  sf.(mem) !! (pa_add pc j) = Some (nth_byte w j))
          by (rewrite Hsf_mem; exact Hbf).
        assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true) by (rewrite Hsub; exact HisRVC).
        rewrite <- Hsub.
        exact (exec_fetch_RVC_4_S_walk root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
                 HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                 (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                 (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                 (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                 Hpbytesf iHA iHord iHX Lfpriv region w
                 iHrange iHmatch Hal Hexec0
                 (within_clint_false pc 4 sf Hnc ltac:(lia))
                 (within_sig_false  pc 4 sf Hns ltac:(lia))
                 (within_htif_false pc 4 sf Lfhtif)
                 iHbytes Hal HisRVC').
      + (* 2-aligned, single 2-byte read *)
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
          iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          iPureIntro. exact Hr0. }
        iPureIntro. destruct Hram as [Hnc Hns].
        destruct (Hpma0 pc 2) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                  (uint pc) (uint (to_bits 64 2)) = PMP_Match)
          by (rewrite Lfpmpaddr; exact Hrange2).
        assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
                  (Physaddr pc) 2 = Some region) by (rewrite Lfpma; exact Hmatch0).
        assert (iHbytes : forall j : nat, (N.of_nat j < 2)%N ->
                  sf.(mem) !! (pa_add pc j) = Some (nth_byte h j))
          by (rewrite Hsf_mem; exact Hbf).
        exact (exec_fetch_RVC_2_S_walk root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
                 Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
                 HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
                 (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
                 (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
                 (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
                 Hpbytesf iHA iHord iHX Lfpriv region h
                 HmisaC' Hbit0 Hbit1 Hal iHrange iHmatch Halign0 Hexec0
                 (within_clint_false pc 2 sf Hnc ltac:(lia))
                 (within_sig_false  pc 2 sf Hns ltac:(lia))
                 (within_htif_false pc 2 sf Lfhtif)
                 iHbytes HisRVC).
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
  Lemma wp_instr_s_fill (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) (satp0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqsa dqb : dfrac} :
    let tlbfilled := vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    ↑minstretN ⊆ E →
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    vec_access_dec tlbvec 5 = None ->
    kv_fetch_geom pc ->
    (is_rvc = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    smode_config dq -∗
    satp ↦ᵣ{ dqsa } satp0 -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ tlbvec -∗
    pte_super_bytes root_ppn dqb -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σf (Hpceq : register_lookup PC σf.(sregs) = pc),
       mstate_interp σf ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config dq -∗
          satp ↦ᵣ{ dqsa } satp0 -∗
          pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
          pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
          tlb ↦ᵣ tlbfilled -∗
          pte_super_bytes root_ppn dqb -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (tlbfilled HN Hppn Hvec Hgeom HgeomB Hpmp Hpmpp Hpteregion Halignp Hmode Hasid)
      "Hsm Hsatp Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr H".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HSIE & %HMPRV & %HSXL)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    assert (HgeomB' : fetch_is_rvc r = false -> kv_fetch_geom (add_vec_int pc 2))
      by (rewrite Hrvc; exact HgeomB).
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_walk root_ppn σ pc r
                 satp0 mstatus0 misa0 menvcfg0 region_pte pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hppn Hasid Hvec HPBMTE Hgeom HgeomB' Hpmp Hpmpp
                 Hmatchp0 Hptep Halignp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE
                 with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    (* the TLB FILL: the fetch's state change, performed on the ghost state *)
    iMod (reg_update _ tlb _ tlbfilled with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := pw_filled root_ppn tlbvec σ : mstate).
    assert (Hσf : set_reg σ tlb tlbfilled = σf) by reflexivity.
    (* decode + landing-pad + Zca facts at the FILLED state σf *)
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, pw_filled, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, pw_filled, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsatp Hmiec Hmdlc Hmenvc Hpmpc Hpmpa Htlb Hpbytes]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[- Hpc' Hsatp Hpmpc Hpmpa Htlb Hpbytes] Hsatp Hpmpc Hpmpa Htlb Hpbytes Hpc'").
      iApply (smode_config_rebuild dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL Hmm HPBMTE
                with "Hhw Hinv Hhs' Hpriv Hmstatus Hmiec Hmdlc Hmenvc"). }
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
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
      iSplitR; [iPureIntro; exact Hfetch |].
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
  (* 13b. wp_instr_s_tlbinv -- THE UNIFIED S-mode step engine.  Takes the *)
  (* TLB/page-table consistency invariant [tlb_inv root_ppn] plus the     *)
  (* page-table fact for the fetched va (the [kv_fetch_geom] geometry +   *)
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
    kv_fetch_geom pc ->
    (is_rvc = false -> kv_fetch_geom (add_vec_int pc 2)) ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
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
    iIntros (HN Hgeom HgeomB Hpmp Hpmpp Hpteregion Halignp)
      "Hsm Hpmpc Hpmpa Htlbinv Hpc Hinstr H".
    (* open the invariant: satp cell + the three SATP facts + tlb + pte bytes *)
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes)".
    destruct (Hcons 5 ltac:(vm_compute; split; [discriminate | reflexivity])) as [Hvec5 | Hvec5].
    - (* slot 5 EMPTY: the walk engine; the fill preserves consistency *)
      iApply (wp_instr_s_fill root_ppn E Φ pc is_rvc i satp0 pmpcfg0 pmpaddr00 region_pte tlbvec
                HN Hppn Hvec5 Hgeom HgeomB Hpmp Hpmpp Hpteregion Halignp Hmode Hasid
                with "Hsm Hsatp Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr").
      iIntros (σf Hpceq) "Hsi".
      iMod ("H" $! σf Hpceq with "Hsi") as (s_exec) "(Hexec & Hsi' & Hcont)".
      iModIntro. iExists s_exec. iFrame "Hexec Hsi'".
      iIntros "Hsm' Hsatp' Hpmpc' Hpmpa' Htlb' Hpbytes' Hpc'".
      iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' [Hsatp' Htlb' Hpbytes'] Hpc'").
      iApply (tlb_inv_close root_ppn satp0
                (vec_update_dec tlbvec 5 (Some (pw_tlb_entry root_ppn (mword_of_int 0))))
                Hmode Hasid Hppn
                (tlb_pt_consistent_fill root_ppn tlbvec 5
                   ltac:(vm_compute; split; [discriminate | reflexivity]) Hcons)
                with "Hsatp' Htlb' Hpbytes'").
    - (* slot 5 RESIDENT: by consistency, the identity entry -> TLB hit *)
      iApply (wp_instr_s root_ppn E Φ pc is_rvc i satp0 pmpcfg0 pmpaddr00 tlbvec
                HN Hmode Hasid Hvec5 Hgeom HgeomB Hpmp with "Hsm Hsatp Hpmpc Hpmpa Htlb Hpc Hinstr").
      iIntros (σ Hpceq) "Hsi".
      iMod ("H" $! σ Hpceq with "Hsi") as (s_exec) "(Hexec & Hsi' & Hcont)".
      iModIntro. iExists s_exec. iFrame "Hexec Hsi'".
      iIntros "Hsm' Hsatp' Hpmpc' Hpmpa' Htlb' Hpc'".
      iApply ("Hcont" with "Hsm' Hpmpc' Hpmpa' [Hsatp' Htlb' Hpbytes] Hpc'").
      iApply (tlb_inv_close root_ppn satp0 tlbvec Hmode Hasid Hppn Hcons
                with "Hsatp' Htlb' Hpbytes").
  Qed.

End SmodeCoreIris.

(* ===================================================================== *)
(* 14. Demos -- the weakened decode + constructor story, end to end.      *)
(* ===================================================================== *)

(* (a) a 32-bit decode under SUPERVISOR: the per-instruction decode lemmas
   now take the [priv_mSU] membership fact, so any non-virtual privilege
   equation feeds them.  (Task 1's weakening, cashing in the old
   TODO(non-M-mode) of InstrBytes.) *)
Lemma decode_jal_S s :
  register_lookup cur_privilege (sregs s) = Supervisor ->
  exec (ext_decode w_jal) s = Some (JAL (imm_jal, Regidx i_jal), s).
Proof.
  intro Hpriv. apply decode_jal. rewrite Hpriv. reflexivity.
Qed.

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
  skip_pure_clause; repeat (dstep s HmisaC);
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
    - iIntros (σ) "_". iPureIntro. intros _ HmisaC. cbn [fetch_is_rvc].
      exists (C_ADDI16SP kv_imm1).
      split; [exact (kv_decode1 σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_ADDI16SP kv_imm1 s).
  Qed.

End SmodeDemo.

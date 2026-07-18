(* WpIntrCore.v -- infrastructure for the INTERRUPT-SAFETY capstone: executing
   one S-mode instruction with sstatus.SIE = 1 and stvec -> kernelvec.

   Contents:
   §1  symbolic-mstatus bit toolkit: Z.testbit-level reasoning about
       subrange/update_subrange towers over an ABSTRACT mstatus (every prior
       chain had a concrete mstatus and used vm_compute; the interrupt
       round-trip changes mstatus, so the Löb invariant must carry a symbolic
       one).  [trap_ms] is the S-mode trap's mstatus tower; the lemmas here
       bridge its bits to wp_kernelvec_hit's premises and prove the headline
       fact that the trap+SRET round trip RESTORES SIE = 1.
   §2  dispatchInterrupt determinism: with the S extension on and
       mie & ~mideleg = 0 (xv6 delegates everything it enables), the dispatch
       outcome in Supervisor mode is the FUNCTION [s_dispatch] of
       mip / sig_meip / sig_seip / mie / mideleg / mstatus.SIE --
       [exec_dispatchInterrupt_S_reduce] (the transient Iris bridge is
       [dispatch_S_transient], WpIntrInv.v).
   §3  the S-mode interrupt TRAP reduction: trap_handler Supervisor
       (Interrupt i) writes scause / mstatus(SPIE,SIE,SPP,SPELP) / stval /
       sepc / cur_privilege and lands on stvec's direct-mode base
       ([exec_trap_handler_S_intr], [exec_handle_interrupt_S]).
   §4  the step-level engine: [exec_riscv_step_interrupt] threads the
       try_step wrapper around the Step_Pending_Interrupt arm (NO fetch, NO
       retire, minstret NOT bumped), and [wp_exec_step_interrupt_inv] is its
       minstret_inv WP rule.  The continuation is handed back UNDER A LATER
       (the step consumed one), which is exactly what the Löb capstone needs
       to strip the ▷ off its induction hypothesis.
   §7  small capstone helpers ([elp_no_lp], [s_dispatch_Some_S]).

   The SIE=1 instruction step engine itself lives in WpSmodeIntr.v
   ([wp_instr_s_intr], over WpIntrInv.v's interrupt-absorbing
   [wp_exec_step_intr]); the old pinned-cell §5b/§6 engines are gone.   *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv.
Require Import WpDecode WpLeafCommon.
Require Import WpGprMret.
Require Import SmodeCore.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import PtAdBits PtTree PtTreeAdue KptTree SmodeCorePt.
Import Defs.

(* ===================================================================== *)
(* §2 dispatchInterrupt determinism in Supervisor mode.                   *)
(* ===================================================================== *)

(* The platform-derived external-interrupt bits (read_mip's contribution
   beyond the [mip] register): MEI from sig_meip, SEI from sig_seip (S on). *)
Definition s_ext_ip (meip seip : mword 1) : mword 64 :=
  _update_Minterrupts_SEI (_update_Minterrupts_MEI (Mk_Minterrupts (zeros' 64)) meip) seip.

Definition s_mip_bits (mip_v : mword 64) (meip seip : mword 1) : mword 64 :=
  Mk_Minterrupts (or_vec mip_v (s_ext_ip meip seip)).

(* The S-destined pending-and-enabled set. *)
Definition s_pending (mip_v : mword 64) (meip seip : mword 1) (mie_v mdv : mword 64) : mword 64 :=
  and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v mdv).

(* The dispatch outcome as a FUNCTION of the pinned cells (Supervisor mode,
   mie & ~mideleg = 0 so nothing is ever M-destined). *)
Definition s_dispatch (mip_v : mword 64) (meip seip : mword 1) (mie_v mdv ms : mword 64)
    : option (InterruptType * Privilege) :=
  if andb (eq_vec (_get_Mstatus_SIE ms) ('b"1"))
          (neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64))
  then match findPendingInterrupt (s_pending mip_v meip seip mie_v mdv) with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Lemma exec_external_interrupts_pending_reduce (s : mstate) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  exec (external_interrupts_pending tt) s = Some (s_ext_ip meip seip, s).
Proof.
  intros HES Hmeip Hseip.
  unfold external_interrupts_pending.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_meip s)).
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sig_seip s)).
  rewrite Hmeip Hseip. apply exec_returnm.
Qed.

Lemma exec_read_mip_reduce (s : mstate) (mip_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  exec (read_mip IncludePlatformInterrupts) s = Some (s_mip_bits mip_v meip seip, s).
Proof.
  intros HES Hmip Hmeip Hseip.
  unfold read_mip. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_external_interrupts_pending_reduce s meip seip HES Hmeip Hseip)).
  rewrite Hmip. apply exec_returnm.
Qed.

(* getPendingSet Supervisor, SIE left SYMBOLIC: the M-destined set is dead
   (mie & ~mideleg = 0), and the outcome is the [s_dispatch]-shaped test. *)
Lemma exec_getPendingSet_S_reduce (s : mstate)
    (mip_v mie_v mdv_v ms_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  register_lookup mstatus s.(sregs) = ms_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (getPendingSet Supervisor) s
    = Some ((if andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                     (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64))
             then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
             else None), s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm.
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
  assert (HsIE : exec (or_boolM
            (and_boolM (returnM (generic_eq Supervisor Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Supervisor User))) s
                = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq Supervisor Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"), s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq Supervisor Supervisor) s)).
      change (generic_eq Supervisor Supervisor) with true. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
      rewrite Hms. apply exec_returnm. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    destruct (eq_vec (_get_Mstatus_SIE ms_v) ('b"1")).
    - reflexivity.
    - change (generic_eq Supervisor User) with false. apply exec_returnm. }
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ Hguard).
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIE).
  rewrite Hmie Hmdl Hmm.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq.
  rewrite andb_false_r.
  unfold s_pending, s_mip_bits.
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_S_reduce (s : mstate)
    (mip_v mie_v mdv_v ms_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  register_lookup mstatus s.(sregs) = ms_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt Supervisor) s
    = Some (s_dispatch mip_v meip seip mie_v mdv_v ms_v, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm.
  unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_getPendingSet_S_reduce s mip_v mie_v mdv_v ms_v meip seip
               HES Hmip Hmeip Hseip Hmie Hmdl Hms Hmm)).
  unfold s_dispatch.
  destruct (andb (eq_vec (_get_Mstatus_SIE ms_v) ('b"1"))
                 (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64))).
  - cbn match. destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
      apply exec_returnm.
  - cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §3 The S-mode interrupt trap reduction.                                *)
(* ===================================================================== *)


(* stvec's direct-mode target. *)
Definition stvec_base (v : mword 64) : mword 64 :=
  concat_vec (_get_Mtvec_Base v) ('b"00").




(* track_trap Supervisor: reads + callbacks only, any state. *)
Lemma exec_track_trap_S (is_i : bool) (cause : mword 6) s :
  exec (track_trap Supervisor is_i cause) s = Some (tt, s).
Proof.
  unfold track_trap.
  erewrite exec_bind_Some. 2: apply (exec_read_reg mstatus s).
  cbn beta.
  (* the whole callback chain (long_csr / scause / stval / sepc reads +
     callbacks) is read-only and computes away by conversion *)
  erewrite exec_bind0_Some.
  2: eapply (exec_long_csr_write_mstatus (register_lookup mstatus s.(sregs)) s).
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

(* lookup through a set_reg tower *)
Ltac lk :=
  unfold set_reg; cbn [sregs];
  repeat (first [ rewrite register_lookup_set
                | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ]).

Section TrapReduce.
  Context (s : mstate) (i : InterruptType) (pc0 : mword 64).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hms : register_lookup mstatus s.(sregs) = ms_v.
  Hypothesis Hsc : register_lookup scause s.(sregs) = sc_old.
  Hypothesis Hstvec : register_lookup stvec s.(sregs) = stvec_v.
  Hypothesis Help : register_lookup elp s.(sregs) = elp_v.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  Hypothesis Hpc : register_lookup PC s.(sregs) = pc0.

  (* the model's exact write order *)
  Let ms_e := update_subrange_vec_dec ms_v 23 23 elp_v.
  Let s1 := set_reg s mstatus ms_e.
  (* the zicfilp epilogue resets elp (value-identical: elp is pinned to
     NO_LP_EXPECTED by hw_config; the Iris side absorbs this write) *)
  Let s1e := set_reg s1 elp (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let c1 := update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
              (bool_to_bit (trapCause_is_interrupt (Interrupt i))).
  Let s2 := set_reg s1e scause c1.
  Let c2 := update_subrange_vec_dec c1 (64 - 2) 0
              (zero_extend' (64 - 1) (trapCause_bits_forwards (Interrupt i))).
  Let s3 := set_reg s2 scause c2.
  Let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e).
  Let s4 := set_reg s3 mstatus ms_a.
  Let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0").
  Let s5 := set_reg s4 mstatus ms_b.
  Let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"1").
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (zeros' 64).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_S_intr :
    exec (trap_handler Supervisor (Interrupt i) pc0 None None) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold trap_handler.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt)) with false.
    cbn match.
    assert (HZ : exec (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s = Some (true, s))
      by apply (exec_hartSupports_Zicfilp s).
    rewrite (exec_bind_Some _ _ _ _ _ HZ). cbn beta. cbn match.
    assert (HZP : exec (zicfilp_preserve_elp_on_trap Supervisor) s = Some (tt, s1e)).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- exec (Defs.bind0 ?A _) _ = _ =>
        assert (HARM : exec A s = Some (tt, s1)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help.
        apply exec_write_reg. }
      rewrite (exec_bind0_Some _ _ _ _ _ HARM).
      unfold reset_elp. apply exec_write_reg. }
    rewrite (exec_bind0_Some _ _ _ _ _ HZP).
    assert (HES1 : exec (currentlyEnabled Ext_S) s1e = Some (true, s1e)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal.
      unfold s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _ HES1). cbn beta.
    assert (HAE : exec (Defs.assert_exp' true "no supervisor mode present for delegation") s1e
                  = Some (eq_refl, s1e)).
    { unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HAE). cbn beta.
    (* scause chain *)
    assert (Hrd1 : exec (Defs.read_reg scause : M _) s1e = Some (sc_old, s1e)).
    { rewrite (exec_read_reg scause s1e). unfold s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hsc. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s1e)).
    assert (Hrd2 : exec (Defs.read_reg scause : M _) s2 = Some (c1, s2)).
    { rewrite (exec_read_reg scause s2). unfold s2, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s2)).
    (* mstatus chain *)
    assert (Hrm1 : exec (Defs.read_reg mstatus : M _) s3 = Some (ms_e, s3)).
    { rewrite (exec_read_reg mstatus s3). unfold s3, s2, s1e, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s3)).
    assert (Hrm2 : exec (Defs.read_reg mstatus : M _) s4 = Some (ms_a, s4)).
    { rewrite (exec_read_reg mstatus s4). unfold s4, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s4)).
    assert (Hrm3 : exec (Defs.read_reg mstatus : M _) s5 = Some (ms_b, s5)).
    { rewrite (exec_read_reg mstatus s5). unfold s5, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm3). cbn beta.
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (Supervisor, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"1" : mword 1) s5)). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s5)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stval _ s6)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc _ s7)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege _ s8)).
    cbn [handle_trap_extension].
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_track_trap_S (trapCause_is_interrupt (Interrupt i)) (trapCause_bits_forwards (Interrupt i)) s9)).
    assert (Hrc : exec (Defs.read_reg scause : M _) s9 = Some (c2, s9)).
    { rewrite (exec_read_reg scause s9).
      unfold s9, s8, s7, s6, s5, s4, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s3, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrc). cbn beta.
    unfold prepare_trap_vector.
    assert (Hrt : exec (Defs.read_reg stvec : M _) s9 = Some (stvec_v, s9)).
    { rewrite (exec_read_reg stvec s9).
      unfold s9, s8, s7, s6, s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hstvec. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrt). cbn beta.
    unfold tvec_addr. rewrite Htvd. cbn match.
    unfold stvec_base. apply exec_returnm.
  Qed.

  Lemma exec_handle_interrupt_S :
    exec (handle_interrupt i Supervisor) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_interrupt.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite Hpc.
    rewrite (exec_bind_Some _ _ _ _ _ exec_trap_handler_S_intr).
    apply exec_set_next_pc.
  Qed.


End TrapReduce.


(* ===================================================================== *)
(* §4 The interrupt step: run_hart_active early return + the try_step     *)
(* wrapper + the minstret_inv WP engine.                                  *)
(* ===================================================================== *)

Lemma execR_early_return {R X} (r : R) s :
  execR (Defs.early_return r : Defs.monadR R exception X) s = Some (inl r, s).
Proof. reflexivity. Qed.

(* run_hart_active on a pending interrupt: NO fetch, NO decode, NO execute;
   the state is UNTOUCHED (dispatchInterrupt only reads). *)
Lemma exec_run_hart_active_pending (s : mstate) (i : InterruptType) (p : Privilege) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (dispatchInterrupt Supervisor) s = Some (Some (i, p), s) ->
  exec (run_hart_active 0) s = Some (Step_Pending_Interrupt (i, p), s).
Proof.
  intros Hpriv Hdisp.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* the try_step wrapper on the Step_Pending_Interrupt arm: handle_interrupt,
   tick PC := nextPC, and NO minstret bump (the step did not retire). *)
(* ********************************************************************* *)
(* COMMENTED OUT -- pending the clock-tick rework of the interrupt stack.  *)
(* [mip] now lives in [clock_inv] (every step may nondeterministically     *)
(* rewrite MTIP/STIP via tick_clock), so the engines below -- which own    *)
(* [mip ↦ᵣ{dq}] across steps and state [exec riscv_step] witnesses --      *)
(* need a substantial redesign, not a mechanical port.                     *)
Section StepInterrupt.
  Context (s s_trap : mstate) (i : InterruptType) (p : Privilege) (b : bool).

  Hypothesis Hsi   :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Pending_Interrupt (i, p), s_a).
  Hypothesis Hhi : exec (handle_interrupt i p) s_a = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_interrupt : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    change (get_config_print_instr tt) with false. cbn match. cbv zeta.
    (* BODY = bind (bind0 (handle_interrupt i p) (read hart_state)) MATCH10 *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhi. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    (* retired = false: and_boolM (returnM false) _ short-circuits *)
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    (* the rest (no-bump arm / rvfi=false skip / pure hooks) computes away *)
    apply exec_returnm.
  Qed.
End StepInterrupt.

(* ===================================================================== *)
(* The Iris engine: one machine step that TAKES the pending interrupt.    *)
(* The continuation comes back UNDER A LATER -- the Löb capstone strips   *)
(* the ▷ off its induction hypothesis exactly here.                       *)
(* ===================================================================== *)
Section WpIntrEngine.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* mstate_interp absorbs a same-value register write (the trap's
     [reset_elp], whose cell is pinned ↦ᵣ□ by hw_config). *)
  Lemma reg_interp_set_same (rs : regstate) (r : register) (v : type_of_register r) :
    register_lookup r rs = v ->
    reg_interp rs -∗ reg_interp (register_set r v rs).
  Proof.
    iIntros (Hv) "H". iDestruct "H" as (m) "[Hh %Hag]".
    iExists m. iFrame "Hh". iPureIntro.
    intros r0 dv Hm. rewrite (Hag r0 dv Hm).
    destruct (register_beq r0 r) eqn:Hb.
    - pose proof (register_beq_true _ _ Hb) as ->.
      rewrite register_lookup_set. rewrite Hv. reflexivity.
    - rewrite irrelevant_register_set; [reflexivity | exact Hb].
  Qed.


  Lemma wp_exec_step_interrupt_inv Φ {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
         ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
         ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
         mstate_interp s_trap ∗
         ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
            WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) Φ with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as (i p s_trap) "(%Hha & %Hhi & Hpc & [Hreg Hmem] & Hcont)".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_trap.
    assert (Hhart_a :
      register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
        = HART_ACTIVE tt).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    iModIntro. iExists _. iSplitR.
    { iPureIntro.
      exact (exec_riscv_step_interrupt σ s_trap i p b
               Hsi Hhart_a Hha Hhi Hhart_trap). }
    iNext.
    iMod (reg_update _ PC _ (register_lookup nextPC s_trap.(sregs)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
    iSplitL "Hmst Hmi".
    { iExists mst, b. iFrame. }
    iApply ("Hcont" with "Hhs Hpc").
  Qed.

End WpIntrEngine.


(* ===================================================================== *)
(* §7 Small capstone helpers.                                            *)
(* ===================================================================== *)

(* a 1-bit elp that is not LP_EXPECTED is NO_LP_EXPECTED. *)
Lemma elp_no_lp (x : mword 1) :
  eq_vec x (landing_pad_bits_backwards LP_EXPECTED) = false ->
  x = landing_pad_bits_backwards NO_LP_EXPECTED.
Proof.
  intros Hne.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  unfold bv_modulus in Hr.
  match type of Hr with context [(2 ^ ?e)%Z] =>
    replace ((2 ^ e)%Z) with 2%Z in Hr by (vm_compute; reflexivity) end.
  destruct (decide (bv_unsigned x = 1)) as [He | Hne'].
  - exfalso.
    assert (Hx1 : x = landing_pad_bits_backwards LP_EXPECTED).
    { apply bv_eq. rewrite He. vm_compute. reflexivity. }
    rewrite Hx1 in Hne.
    assert (Ht : eq_vec (landing_pad_bits_backwards LP_EXPECTED)
                        (landing_pad_bits_backwards LP_EXPECTED) = true)
      by (vm_compute; reflexivity).
    congruence.
  - apply bv_eq.
    replace (bv_unsigned (landing_pad_bits_backwards NO_LP_EXPECTED)) with 0
      by (vm_compute; reflexivity).
    lia.
Qed.

(* [s_dispatch] only ever dispatches to Supervisor. *)
Lemma s_dispatch_Some_S (mip_v mie_v mdv ms : mword 64) (meip seip : mword 1)
    (i : InterruptType) (p : Privilege) :
  s_dispatch mip_v meip seip mie_v mdv ms = Some (i, p) -> p = Supervisor.
Proof.
  unfold s_dispatch.
  destruct (andb _ _); [| discriminate].
  destruct (findPendingInterrupt _); [| discriminate].
  intros H. injection H as -> ->. reflexivity.
Qed.

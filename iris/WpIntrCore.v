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
       outcome in Supervisor mode is the FUNCTION [s_dispatch] of the pinned
       cells mip / sig_meip / sig_seip / mie / mideleg / mstatus.SIE --
       [exec_dispatchInterrupt_S_reduce] + the Iris bridge
       [dispatch_S_from_regs].
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
   §5  the acquire-page fetch clones: acquire lives at 0x80000c04 (VPN
       0x80000, TLB slot 0), one superpage below the kernelvec page (VPN
       0x80005, slot 5); the S-mode TLB-hit fetch tower is cloned at the
       acquire VPN, up to [instr_lift_s_acq], plus the [instr] constructor
       for acquire's first instruction c.addi sp,-32 (0x1101).
   §6  the SIE=1 normal-path step client [wp_instr_s_intr]: like
       WpSmodeGpr.wp_instr_s_config but WITHOUT smode_config's SIE=0 --
       dispatchInterrupt = None is discharged from [s_dispatch = None]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List Bool.
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
Require Import WpFetch WpDecode WpLeafCommon WpEntry WpLoad WpGprCsrwB WpEntryNew.
Require Import WpGpr WpGprAddi WpGprMret WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret.
From Kernel Require Import KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.
Require Import WpIntrBits.

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

(* the post-trap scause: interrupt bit set, cause code of [i]. *)
Definition trap_sc (sc_old : mword 64) (i : InterruptType) : mword 64 :=
  update_subrange_vec_dec (update_subrange_vec_dec sc_old 63 63 (bool_to_bit true)) 62 0
    (zero_extend' 63 (trapCause_bits_forwards (Interrupt i))).

(* stvec's direct-mode target. *)
Definition stvec_base (v : mword 64) : mword 64 :=
  concat_vec (_get_Mtvec_Base v) ('b"00").

(* the callback plumbing is state-preserving *)
Lemma exec_csr_cb_scause (V : mword 64) s :
  exec (csr_name_write_callback "scause" V) s = Some (tt, s).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "scause") s = Some (mword_of_int 0x142, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

Lemma exec_csr_cb_stval (V : mword 64) s :
  exec (csr_name_write_callback "stval" V) s = Some (tt, s).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "stval") s = Some (mword_of_int 0x143, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

Lemma exec_csr_cb_sepc (V : mword 64) s :
  exec (csr_name_write_callback "sepc" V) s = Some (tt, s).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "sepc") s = Some (mword_of_int 0x141, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

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
     NO_LP_EXPECTED by hw_config; the Iris side absorbs this write with
     [state_interp_set_same]) *)
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

  (* the post-trap state, exported (body = the s9 Let-tower above). *)
  Definition trap_state : mstate := s9.

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

  Lemma exec_riscv_step_interrupt : exec riscv_step s = Some (tt, s_tick).
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

  (* state_interp absorbs a same-value register write (the trap's
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

  Lemma state_interp_set_same (σ : mstate) ns κs nt (r : register) (v : type_of_register r) :
    register_lookup r σ.(sregs) = v ->
    state_interp σ ns κs nt -∗ state_interp (set_reg σ r v) ns κs nt.
  Proof.
    iIntros (Hv) "[Hreg Hmem]".
    unfold set_reg; cbn [sregs mem].
    iFrame "Hmem". iApply (reg_interp_set_same _ _ _ Hv with "Hreg").
  Qed.

  Lemma wp_exec_step_interrupt_inv E Φ {dq : dfrac} :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ ns κs nt,
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (i : InterruptType) (p : Privilege) (s_trap : mstate),
         ⌜ exec (run_hart_active 0) σ = Some (Step_Pending_Interrupt (i, p), σ) ⌝ ∗
         ⌜ exec (handle_interrupt i p) σ = Some (tt, s_trap) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_trap.(sregs)) ∗
         state_interp s_trap ns κs nt ∗
         ▷ (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
            PC ↦ᵣ (register_lookup nextPC s_trap.(sregs)) -∗
            WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv Hhs H".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) ns κs nt with "[Hreg Hmem]")
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
(* §5 The acquire-page S-mode TLB-hit fetch tower (VPN 0x80000, slot 0).  *)
(* Clones of SmodeCore's kernelvec-page (VPN 0x80005, slot 5) hit path.   *)
(* ===================================================================== *)

Definition acq_vpn : mword 27 := mword_of_int 0x80000.

(* the geometric facts pinning [va] to the acquire code page. *)
Definition acq_fetch_geom (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false
  /\ autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = acq_vpn
  /\ zero_extend' 64 (concat_vec (mword_of_int 0x80000 : mword 44)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va.

Section AcqTranslate.
  Context (root_ppn : mword 44).

  Lemma exec_translate_TLB_hit_super_acq (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) acq_vpn (InstructionFetch tt) Supervisor mxr do_sum
            tt 0 (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (mword_of_int 0x80000 : mword 44, PBMT_PMA, tt), s).
  Proof.
    destruct mxr, do_sum; vm_compute; reflexivity.
  Qed.

  Lemma exec_lookup_TLB_hit_super_acq (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) acq_vpn) s
      = Some (Some (0, pw_tlb_entry root_ppn (mword_of_int 0)), s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) acq_vpn) with 0 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    replace (match_TLB_Entry (pw_tlb_entry root_ppn (mword_of_int 0)) (mword_of_int 0 : mword 16)
               (sign_extend' (57 - 12) acq_vpn)) with true
      by (vm_compute; reflexivity).
    apply exec_returnm.
  Qed.

  Lemma exec_translate_hit_super_acq (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn acq_vpn (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80000 : mword 44, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_super_acq tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_super_acq.
  Qed.

  Lemma exec_translateAddr_fetch_hit_acq (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom va ->
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
      replace vpnx with acq_vpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_hit_super_acq _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- TLB MISS at slot 0: the acquire-page page WALK (clone of the
     kernelvec walk tower at acq_vpn; same PTE, hash index 0). ---- *)

  (* The single-level (1GB superpage) page walk: reads ONE PTE from memory
     and returns the identity translation output ppn 0x80005. *)
  Lemma exec_pt_walk_super_acq (mxr do_sum : bool) (region : PMA_Region) (menvcfg0 : mword 64) s :
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
    exec (pt_walk 39 acq_vpn (InstructionFetch tt) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (mword_of_int 0x80000) (autocast (T := mword) pte_super)
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
      replace a with (pte_paddr root_ppn : mword 64) by
        (unfold pte_paddr; do 2 f_equal; apply bv_eq; vm_compute; reflexivity);
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

  (* add_to_TLB installs the entry at index 5 (= tlb_hash 39 acq_vpn). *)
  Lemma exec_add_to_TLB_super_acq (asid : mword 16) s :
    exec (add_to_TLB 39 asid acq_vpn (mword_of_int 0x80000 : mword 44) (autocast (T := mword) pte_super)
            (Physaddr (pte_paddr root_ppn)) 2 false) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 0 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    unfold add_to_TLB. cbn zeta.
    replace (tlb_hash (__id 39) acq_vpn) with 0 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    do 3 f_equal.
  Qed.

  Lemma exec_translate_TLB_miss_super_acq (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region) (menvcfg0 : mword 64) s :
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
    exec (translate_TLB_miss 39 asid root_ppn acq_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80000 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 0 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_super_acq mxr do_sum region menvcfg0 s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_super_acq asid s)).
    apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_miss_acq (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = None ->
    exec (lookup_TLB 39 asid acq_vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) acq_vpn) with 0 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. apply exec_returnm.
  Qed.

  Lemma exec_translate_walk_acq (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region)
        (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = None ->
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
    exec (translate 39 asid root_ppn acq_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80000 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss_acq asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_super_acq mxr do_sum asid region menvcfg0 s
             HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
  Qed.

  (* The state after the fetch's page walk: TLB filled at index 5. *)
  Definition pw_filled_acq (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) : mstate :=
    set_reg s tlb (vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn (mword_of_int 0)))).

  (* FULL Sv39 fetch translation of a kernelvec-page vaddr with an EMPTY TLB
     slot 5: the page walk reads the PTE from memory and fills the TLB. *)
  Lemma exec_translateAddr_fetch_walk_acq (va : mword 64) (region : PMA_Region)
        (menvcfg0 satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 0 = None ->
    acq_fetch_geom va ->
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
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), pw_filled_acq tlbvec s).
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
      replace vpnx with acq_vpn by (symmetry; exact Hvpn_def);
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk_acq _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- the 4-byte read + the two 4-aligned fetch geometries ---- *)
  Section AcqFetchHit.
    Context (va : mword 64) (satp0 : mword 64)
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
    Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
    Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
    Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
    Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
    Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
    Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
    Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
    Hypothesis Hvec : vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)).
    Hypothesis Hgeom : acq_fetch_geom va.
    Hypothesis HA : pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
    Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
    Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.

    Section AcqW4.
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

      Lemma exec_fetch_bytes_4_S_hit_acq : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s).
      Proof using Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom HA Hord Hrange4 HX Hmatch Hvalign Hexec Hc Hsig Hh Hbytes.
        assert (Halign : is_aligned_paddr (Physaddr va) 4 = true) by exact Hvalign.
        unfold fetch_bytes.
        rewrite exec_catch_early_return.
        change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                  (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
               = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
        2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
            rewrite execR_liftR.
            rewrite (exec_translateAddr_fetch_hit_acq va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom).
            cbn match. reflexivity. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 4 false false false)) s
               = Some (inr (Ok w), s))).
        2:{ rewrite execR_liftR.
            rewrite (exec_mem_read_fetch_4_S PBMT_PMA va region w s
                       HA Hord Hrange4 HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
            cbn match. reflexivity. }
        cbv iota beta. rewrite autocast_mword_id.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.

      Section AcqRVC4.
        Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.
        Lemma exec_fetch_RVC_4_S_hit_acq : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
        Proof using All.
          destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
          pose proof exec_fetch_bytes_4_S_hit_acq as Hfb4.
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
      End AcqRVC4.

      Section AcqFBase4.
        Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
        Lemma exec_fetch_F_Base_4_S_hit_acq : exec (fetch tt) s = Some (F_Base w, s).
        Proof using All.
          destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
          pose proof exec_fetch_bytes_4_S_hit_acq as Hfb4.
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
      End AcqFBase4.
    End AcqW4.

    (* ---- the 2-byte read + the 2-aligned-not-4-aligned RVC shape: needed
       whenever a symbol's address shifts by a non-multiple-of-4 offset and
       lands an instruction on a 2-but-not-4-aligned boundary (as happened to
       [acquire] here) -- mirrors SmodeCore's [Aligned2]/[RVC2]. *)
    Section AcqW2.
      Context (region : PMA_Region) (h : mword 16).
      Hypothesis Hbit0 : neq_vec (access_vec_dec va 0) ('b"0") = false.
      Hypothesis Hbit1 : neq_vec (access_vec_dec va 1) ('b"0") = true.
      Hypothesis Hvalign4 : is_aligned_vaddr (Virtaddr va) 4 = false.
      Hypothesis Hrange2 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
          (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
          (uint va) (uint (to_bits 64 2)) = PMP_Match.
      Hypothesis Halign2 : is_aligned_paddr (Physaddr va) 2 = true.
      Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr va) 2 = Some region.
      Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
      Hypothesis Hc : exec (within_clint (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hsig : exec (within_sig (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hh : exec (within_htif_readable (Physaddr va) 2) s = Some (false, s).
      Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add va j) = Some (nth_byte h j).

      Lemma exec_fetch_bytes_2_S_hit_acq : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s).
      Proof using Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom HA Hord Hrange2 HX Hmatch Halign2 Hexec Hc Hsig Hh Hbytes.
        unfold fetch_bytes.
        rewrite exec_catch_early_return.
        change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                  (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
               = Some (inr (Ok (Physaddr va, PBMT_PMA, init_ext_ptw)), s))).
        2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
            rewrite execR_liftR.
            rewrite (exec_translateAddr_fetch_hit_acq va satp0 tlbvec s Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hgeom).
            cbn match. reflexivity. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr va, PBMT_PMA) s)).
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ _ _
          (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr va) 2 false false false)) s
               = Some (inr (Ok h), s))).
        2:{ rewrite execR_liftR.
            rewrite (exec_mem_read_fetch_2_S PBMT_PMA va region h s
                       HA Hord Hrange2 HX Hmatch Halign2 Hexec Hc Hsig Hh Hbytes Hcp).
            cbn match. reflexivity. }
        cbv iota beta. rewrite autocast_mword_id_16.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.

      Section AcqRVC2.
        Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
        Hypothesis HisRVC : isRVC h = true.
        Lemma exec_fetch_RVC_2_S_hit_acq : exec (fetch tt) s = Some (F_RVC h, s).
        Proof using All.
          pose proof exec_fetch_bytes_2_S_hit_acq as Hfb2.
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
      End AcqRVC2.
    End AcqW2.
  End AcqFetchHit.
Section AcqFetchWalk.
  Context (va : mword 64) (menvcfg0 satp0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (region_pte : PMA_Region) (s : mstate).
  Let sf := pw_filled_acq tlbvec s.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = va.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn.
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 0 = None.
  Hypothesis Hgeom : acq_fetch_geom va.
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
    exec_translateAddr_fetch_walk_acq va region_pte menvcfg0 satp0 tlbvec s
      Hcp HSXL Hsatp Hmode Hppn Hasid Htlb Hvec Hgeom
      pHA pHord pHrange pHR pHmatch pHalign pHpte pHc pHsig pHh pHbytes Hmenv HPBMTE.

  (* -- width 4 read at va, at sf -- *)
  Section AcqWalkW4.
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

    Lemma exec_fetch_bytes_4_S_walk_acq : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, sf).
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

    Section AcqWalkRVC4.
      Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.
      Lemma exec_fetch_RVC_4_S_walk_acq : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), sf).
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
        rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_S_walk_acq).
        cbv iota beta. rewrite HisRVC. cbv iota beta.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.
    End AcqWalkRVC4.

    Section AcqWalkFBase4.
      Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.
      Lemma exec_fetch_F_Base_4_S_walk_acq : exec (fetch tt) s = Some (F_Base w, sf).
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
        rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_S_walk_acq).
        cbv iota beta. rewrite HnotRVC. cbv iota beta.
        rewrite execR_returnR_fwd. cbn match. reflexivity.
      Qed.
    End AcqWalkFBase4.
  End AcqWalkW4.

  (* -- width 2 read at va (2-aligned, not 4-aligned RVC), at sf -- *)
  Section AcqWalkW2.
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

    Lemma exec_fetch_bytes_2_S_walk_acq : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, sf).
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

    Lemma exec_fetch_RVC_2_S_walk_acq : exec (fetch tt) s = Some (F_RVC h, sf).
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
      rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_2_S_walk_acq).
      cbv iota beta. rewrite HisRVC. cbv iota beta.
      rewrite execR_returnR_fwd. cbn match. reflexivity.
    Qed.
  End AcqWalkW2.

End AcqFetchWalk.

End AcqTranslate.

(* ===================================================================== *)
(* §5b The Iris bridges on the acquire page: fetch-from-instr_bytes,      *)
(* instr lift, and the dispatch-outcome bridge.                           *)
(* ===================================================================== *)
Section AcqIris.
  Context `{!riscvGS Σ}.

  Lemma fetch_from_instr_bytes_s_acq (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    state_interp σ ns κs nt -∗
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
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes".
    destruct Hpmp as ((HA & Hord & Hrange4 & HX) & _ & _).
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
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w (4-aligned) *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
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
      exact (exec_fetch_F_Base_4_S_hit_acq root_ppn pc satp0 tlbvec σ
               Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
               HA' Hord' HX' region w Hal4 Hrange4' Hmatch Hexec0
               (within_clint_false pc 4 σ Hnc ltac:(lia))
               (within_sig_false  pc 4 σ Hns ltac:(lia))
               (within_htif_false pc 4 σ Lhtif)
               Hbf HnotRVC).
    - (* F_RVC h (4-aligned window) *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      rewrite Hal4.
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
      exact (exec_fetch_RVC_4_S_hit_acq root_ppn pc satp0 tlbvec σ
               Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
               HA' Hord' HX' region w Hal4 Hrange4' Hmatch Hexec0
               (within_clint_false pc 4 σ Hnc ltac:(lia))
               (within_sig_false  pc 4 σ Hns ltac:(lia))
               (within_htif_false pc 4 σ Lhtif)
               Hbf HisRVC').
    - (* F_Error *) done.
  Qed.

  (* [fetch_from_instr_bytes_s_acq]'s RVC-only sibling for a pc that's
     2-aligned but NOT 4-aligned (e.g. a symbol relocated by a
     non-multiple-of-4 offset can land an unchanged instruction stream on a
     different alignment class than before). Fixing [r] to [F_RVC h] (rather
     than generalizing over all of [FetchResult] the way the 4-aligned lemma
     does) avoids needing an F_Base-at-2-but-not-4-aligned case, which nothing
     here currently needs and which would require the two-2-byte-window
     reasoning of SmodeCore's [exec_fetch_F_Base_2_S_hit] (plus a fetch-geometry
     fact for pc+2 that callers of the 4-aligned lemma don't have lying
     around) -- narrowing the STATEMENT is cheaper than duplicating that. *)
  Lemma fetch_from_instr_bytes_s_acq_rvc2 (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (h : mword 16)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    state_interp σ ns κs nt -∗
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
    instr_bytes pc (F_RVC h) -∗
    ⌜ exec (fetch tt) σ = Some (F_RVC h, σ) ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes".
    destruct Hpmp as (_ & (HA & Hord & Hrange2 & HX) & _).
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
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpaddr; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (Hrange2' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pc) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrange2).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    iDestruct "Hbytes" as "[%HisRVC Hbytes]".
    rewrite Hal4.
    destruct (align2_not4_facts pc H2al Hal4) as (Halign2 & Hbit0 & Hbit1).
    rewrite fetch_pa_id in Halign2.
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
    assert (HmisaC0' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
    exact (exec_fetch_RVC_2_S_hit_acq root_ppn pc satp0 tlbvec σ
             Lpriv Lpc HSXL' Lsatp Hmode Hasid Ltlb Hvec Hgeom
             HA' Hord' HX' region h Hbit0 Hbit1 Hal4 Hrange2' Halign2 Hmatch Hexec0
             (within_clint_false pc 2 σ Hnc ltac:(lia))
             (within_sig_false  pc 2 σ Hns ltac:(lia))
             (within_htif_false pc 2 σ Lhtif)
             Hbf HmisaC0' HisRVC).
  Qed.

  Lemma fetch_from_instr_bytes_s_acq_walk (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (r : FetchResult)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64) (region_pte : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    vec_access_dec tlbvec 0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    state_interp σ ns κs nt -∗
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
    ⌜ exec (fetch tt) σ = Some (r, pw_filled_acq root_ppn tlbvec σ) ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hasid Hppn Hvec HPBMTE Hgeom Hal4 Hpmp Hpmpp Hmatchp0 Hptep Halignp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    destruct Hpmp as ((HA & Hord & Hrange4 & HX) & _ & _).
    destruct Hpmpp as (_ & _ & Hrangep & HRp).
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
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
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
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
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
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HRp).
    assert (Hrangep' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrangep).
    assert (Hmatchp : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte)
      by (rewrite Lpma; exact Hmatchp0).
    set (sf := pw_filled_acq root_ppn tlbvec σ).
    assert (Hsf_mem : sf.(mem) = σ.(mem)) by reflexivity.
    assert (Lfpmpc : register_lookup pmpcfg_n sf.(sregs) = pmpcfg0).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Lfpmpaddr : register_lookup pmpaddr_n sf.(sregs) = pmpaddr00).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Lfpma : register_lookup pma_regions sf.(sregs) = pmar0).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lfpriv : register_lookup cur_privilege sf.(sregs) = Supervisor).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Lfhtif : register_lookup htif_tohost_base sf.(sregs) = None).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
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
    - (* F_Base w (4-aligned) *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
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
      assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                (uint pc) (uint (to_bits 64 4)) = PMP_Match)
        by (rewrite Lfpmpaddr; exact Hrange4).
      assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
                (Physaddr pc) 4 = Some region) by (rewrite Lfpma; exact Hmatch0).
      assert (iHbytes : forall j : nat, (N.of_nat j < 4)%N ->
                sf.(mem) !! (pa_add pc j) = Some (nth_byte w j))
        by (rewrite Hsf_mem; exact Hbf).
      exact (exec_fetch_F_Base_4_S_walk_acq root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
               Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
               HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
               (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
               (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
               (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
               Hpbytesf iHA iHord iHX Lfpriv region w
               iHrange iHmatch Hal4 Hexec0
               (within_clint_false pc 4 sf Hnc ltac:(lia))
               (within_sig_false  pc 4 sf Hns ltac:(lia))
               (within_htif_false pc 4 sf Lfhtif)
               iHbytes Hal4 HnotRVC).
    - (* F_RVC h (4-aligned window) *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      rewrite Hal4.
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
      assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
                (uint pc) (uint (to_bits 64 4)) = PMP_Match)
        by (rewrite Lfpmpaddr; exact Hrange4).
      assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
                (Physaddr pc) 4 = Some region) by (rewrite Lfpma; exact Hmatch0).
      assert (iHbytes : forall j : nat, (N.of_nat j < 4)%N ->
                sf.(mem) !! (pa_add pc j) = Some (nth_byte w j))
        by (rewrite Hsf_mem; exact Hbf).
      rewrite <- Hsub.
      exact (exec_fetch_RVC_4_S_walk_acq root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
               Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
               HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
               (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
               (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
               (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
               Hpbytesf iHA iHord iHX Lfpriv region w
               iHrange iHmatch Hal4 Hexec0
               (within_clint_false pc 4 sf Hnc ltac:(lia))
               (within_sig_false  pc 4 sf Hns ltac:(lia))
               (within_htif_false pc 4 sf Lfhtif)
               iHbytes Hal4 HisRVC').
    - (* F_Error *) done.
  Qed.

  Lemma fetch_from_instr_bytes_s_acq_rvc2_walk (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (h : mword 16)
      (satp0 mstatus0 misa0 menvcfg0 : mword 64) (region_pte : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqb dqp dqs dqsa dqt dqc dqpa dqa dqh dqm dqe : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    vec_access_dec tlbvec 0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte ->
    (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    state_interp σ ns κs nt -∗
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
    instr_bytes pc (F_RVC h) -∗
    ⌜ exec (fetch tt) σ = Some (F_RVC h, pw_filled_acq root_ppn tlbvec σ) ⌝.
  Proof.
    iIntros (Hpma0 HmisaC0 HSXL0 Hmode Hasid Hppn Hvec HPBMTE Hgeom Hal4 Hpmp Hpmpp Hmatchp0 Hptep Halignp)
      "[Hreg Hmem] Hpc Hpriv Hms Hsatp Htlb Hmenv Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes".
    destruct Hpmp as (_ & (HA & Hord & Hrange2 & HX) & _).
    destruct Hpmpp as (_ & _ & Hrangep & HRp).
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
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Lpmpaddr; exact Hord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (Hrange2' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint pc) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrange2).
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL0).
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
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HRp).
    assert (Hrangep' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0)) 4)
              (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match)
      by (rewrite Lpmpaddr; exact Hrangep).
    assert (Hmatchp : matching_pma_region (register_lookup pma_regions σ.(sregs))
              (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte)
      by (rewrite Lpma; exact Hmatchp0).
    set (sf := pw_filled_acq root_ppn tlbvec σ).
    assert (Hsf_mem : sf.(mem) = σ.(mem)) by reflexivity.
    assert (Lfpmpc : register_lookup pmpcfg_n sf.(sregs) = pmpcfg0).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Lfpmpaddr : register_lookup pmpaddr_n sf.(sregs) = pmpaddr00).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Lfpma : register_lookup pma_regions sf.(sregs) = pmar0).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lfpriv : register_lookup cur_privilege sf.(sregs) = Supervisor).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Lfhtif : register_lookup htif_tohost_base sf.(sregs) = None).
    { unfold sf, pw_filled_acq, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (iHA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) = TOR)
      by (rewrite Lfpmpc; exact HA).
    assert (iHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0) = false)
      by (rewrite Lfpmpaddr; exact Hord).
    assert (iHX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lfpmpc; exact HX).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    iDestruct "Hbytes" as "[%HisRVC Hbytes]".
    rewrite Hal4.
    destruct (align2_not4_facts pc H2al Hal4) as (Halign2 & Hbit0 & Hbit1).
    rewrite fetch_pa_id in Halign2.
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
    assert (HmisaC0' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; exact HmisaC0).
    assert (iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
              (uint pc) (uint (to_bits 64 2)) = PMP_Match)
      by (rewrite Lfpmpaddr; exact Hrange2).
    assert (iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs))
              (Physaddr pc) 2 = Some region) by (rewrite Lfpma; exact Hmatch0).
    assert (iHbytes : forall j : nat, (N.of_nat j < 2)%N ->
              sf.(mem) !! (pa_add pc j) = Some (nth_byte h j))
      by (rewrite Hsf_mem; exact Hbf).
    exact (exec_fetch_RVC_2_S_walk_acq root_ppn pc menvcfg0 satp0 tlbvec region_pte σ
             Lpriv Lpc HSXL' Lsatp Hmode Hppn Hasid Ltlb Hvec Hgeom Lmenv HPBMTE
             HA' Hord' Hrangep' HR' Hmatchp Halignp Hptep
             (within_clint_false (pte_paddr root_ppn) 8 σ Hncp ltac:(lia))
             (within_sig_false  (pte_paddr root_ppn) 8 σ Hnsp ltac:(lia))
             (within_htif_false (pte_paddr root_ppn) 8 σ Lhtif)
             Hpbytesf iHA iHord iHX Lfpriv region h
             HmisaC0' Hbit0 Hbit1 Hal4 iHrange iHmatch Halign2 Hexec0
             (within_clint_false pc 2 sf Hnc ltac:(lia))
             (within_sig_false  pc 2 sf Hns ltac:(lia))
             (within_htif_false pc 2 sf Lfhtif)
             iHbytes HisRVC).
  Qed.

  Lemma instr_lift_s_acq (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    state_interp σ ns κs nt -∗
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
    iIntros (Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp)
      "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iDestruct (state_interp_reg_dq σ ns κs nt cur_privilege dqp Supervisor
                 with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ ns κs nt misa dqm misa0
                 with "Hsi Hmisa") as %Lmisa.
    iDestruct (fetch_from_instr_bytes_s_acq root_ppn σ ns κs nt pc r satp0 mstatus0 misa0
                 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp
                 with "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes") as %Hfetch.
    iDestruct ("Hdec" $! σ ns κs nt with "Hsi") as %Hdec0.
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

  (* [instr_lift_s_acq]'s sibling for pc 2-aligned but NOT 4-aligned, fixing
     is_rvc := true (the only shape the 2-aligned fetch layer proves). *)
  Lemma instr_lift_s_acq_rvc2 (root_ppn : mword 44)
      (σ : mstate) ns κs nt (pc : mword 64) (i : instruction)
      (satp0 mstatus0 misa0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      {dqp dqs dqsa dqt dqc dqpa dqa dqh dqm : dfrac} :
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    state_interp σ ns κs nt -∗
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
    instr pc true i -∗
    ⌜ ∃ (h : half) (i0 : instruction),
        exec (fetch tt) σ = Some (F_RVC h, σ) /\
        exec (decode_fetch (F_RVC h)) σ = Some (i0, σ) /\
        is_lpad_instruction i0 = false /\
        (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s)) ⌝.
  Proof.
    iIntros (Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp)
      "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iDestruct (state_interp_reg_dq σ ns κs nt cur_privilege dqp Supervisor
                 with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ ns κs nt misa dqm misa0
                 with "Hsi Hmisa") as %Lmisa.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as %[_ []].
    - cbn [fetch_is_rvc] in Hrvc. discriminate Hrvc.
    - iDestruct (fetch_from_instr_bytes_s_acq_rvc2 root_ppn σ ns κs nt pc h satp0 mstatus0 misa0
                   pmpcfg0 pmpaddr00 pmar0 tlbvec
                   Hpma HmisaC HSXL0 Hmode Hasid Hvec Hgeom Hal4 Hpmp
                   with "Hsi Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hbytes") as %Hfetch.
      iDestruct ("Hdec" $! σ ns κs nt with "Hsi") as %Hdec0.
      specialize (Hdec0 ltac:(rewrite Lpriv; reflexivity) ltac:(rewrite Lmisa; exact HmisaC)).
      cbn [fetch_is_rvc] in Hdec0.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iPureIntro. exists h, i0.
      split; [exact Hfetch | split; [exact Hdec | split; [exact Hnlpad0 | exact Hexp]]].
    - iDestruct "Hbytes" as %[_ []].
  Qed.

  (* the dispatch-outcome bridge: [s_dispatch] of the pinned cells. *)
  Lemma dispatch_S_from_regs
      (σ : mstate) ns κs nt (misa0 mip_v mie_v mdv0 mstatus0 : mword 64)
      (meip seip : mword 1)
      {dqm dqp dqe1 dqe2 dqi dqd dqs : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    state_interp σ ns κs nt -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mip ↦ᵣ{ dqp } mip_v -∗
    sig_meip ↦ᵣ{ dqe1 } meip -∗
    sig_seip ↦ᵣ{ dqe2 } seip -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv0 -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    ⌜ exec (dispatchInterrupt Supervisor) σ
        = Some (s_dispatch mip_v meip seip mie_v mdv0 mstatus0, σ) ⌝.
  Proof.
    iIntros (HmisaS Hmm) "[Hreg Hmem] Hmisa Hmip Hmeip Hseip Hmie Hmdl Hms".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmip")  as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmie")  as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl")  as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iPureIntro.
    apply exec_dispatchInterrupt_S_reduce; try assumption.
    rewrite exec_currentlyEnabled_S. rewrite Lmisa. rewrite HmisaS. reflexivity.
  Qed.

End AcqIris.

(* ===================================================================== *)
(* §5c acquire's first instruction: c.addi sp,-32 (0x1101 @ 0x80000c04).  *)
(* ===================================================================== *)
Definition acq_pc1 : mword 64 := mword_of_int KernelSyms.acquire.
Definition acq_h1 : mword 16 := mword_of_int 0x1101.
Definition acq_w1 : mword 32 := mword_of_int 0xec061101.
Definition acq_i1 : mword 6 := mword_of_int 32.   (* c.addi imm = -32 (6-bit) *)

Local Ltac acq_reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac acq_open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

Local Ltac acq_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Lemma acq_decode1 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed acq_h1) s = Some (C_ADDI (acq_i1, Regidx csp_rs1), s).
Proof.
  intro HmisaC.
  acq_reg_step Hr acq_h1 11 7 s.
  acq_open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. acq_ast.
Qed.

Section AcqInstr.
  Context `{!riscvGS Σ}.

  Lemma acq_instr1 :
    kernel_text -∗ instr acq_pc1 true (ITYPE (sign_extend' 12 acq_i1, Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof.
    assert (Hlpad : is_lpad_instruction (ITYPE (sign_extend' 12 acq_i1, Regidx csp_rs1, Regidx csp_rs1, ADDI)) = false)
      by (vm_compute; reflexivity).
    assert (H2al : is_aligned_vaddr (Virtaddr acq_pc1) 2 = true) by (vm_compute; reflexivity).
    assert (H4al : is_aligned_vaddr (Virtaddr acq_pc1) 4 = false) by (vm_compute; reflexivity).
    assert (Hrvc : isRVC acq_h1 = true) by (vm_compute; reflexivity).
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (KernelSyms.acquire + Z.of_nat j)%Z = Some (nth_byte acq_h1 j)).
    { intros j Hj;
        do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia. }
    iIntros "#Ht". rewrite /instr.
    iSplitR; [iPureIntro; exact Hlpad|].
    iExists (F_RVC acq_h1).
    iSplitR; [iPureIntro; reflexivity|].
    iSplitL "".
    - iApply (instr_bytes_rvc2 acq_pc1 acq_h1 H2al H4al Hrvc).
      iApply (kernel_window_pc KernelSyms.acquire acq_h1 2 acq_pc1 eq_refl Hbytes with "Ht").
    - iIntros (σ ns κs nt) "_". iPureIntro. intros _ HmisaC. cbn [fetch_is_rvc].
      exists (C_ADDI (acq_i1, Regidx csp_rs1)).
      split; [exact (acq_decode1 σ HmisaC) |].
      split; [vm_compute; reflexivity |].
      intro s. exact (exec_execute_C_ADDI acq_i1 (Regidx csp_rs1) s).
  Qed.

End AcqInstr.

(* ===================================================================== *)
(* §6 The SIE-symbolic S-mode step client (acquire page): dispatch = None *)
(* is discharged from [s_dispatch = None], NOT from SIE = 0.              *)
(* ===================================================================== *)
Section WpInstrIntr.
  Context `{!riscvGS Σ}.

  Lemma wp_instr_s_intr (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqt : dfrac} :
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ ns κs nt (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ{ dqt } tlbvec -∗
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone Hvec Hgeom Hal4 Hpmp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ ns κs nt) "Hsi".
    iDestruct (instr_lift_s_acq root_ppn σ ns κs nt pc is_rvc i satp0 mstatus0 misa0
                 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hasid Hvec Hgeom Hal4 Hpmp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr") as %Hlift.
    iDestruct (dispatch_S_from_regs σ ns κs nt misa0 mip_v mie_v mdv0 mstatus0 meip seip
                 HmisaS Hmm
                 with "Hsi Hmisa Hmipc Hmeipc Hseipc Hmiec Hmdlc Hmstatus") as %Hdisp0.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) σ = Some (None, σ))
      by (rewrite Hdisp0 Hdnone; reflexivity).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ ns κs nt Lpc
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct is_rvc.
    - destruct Hlift as (h & i0 & Hfetch & Hdec & Hnlpad0 & Hexp).
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
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
    - destruct Hlift as (w & Hfetch & Hdec & Hnlpad).
      iModIntro. iExists (F_Base w), i, σ, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
  Qed.

  (* [wp_instr_s_intr]'s sibling for pc 2-aligned but NOT 4-aligned, fixing
     is_rvc := true (mirrors the [is_rvc = true] branch of the 4-aligned
     lemma's proof, over [instr_lift_s_acq_rvc2] instead of [instr_lift_s_acq]). *)
  Lemma wp_instr_s_intr_rvc2 (root_ppn : mword 44) E Φ
      (pc : mword 64) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqt : dfrac} :
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    vec_access_dec tlbvec 0 = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ{ dqt } tlbvec -∗
    PC ↦ᵣ pc -∗
    instr pc true i -∗
    (∀ σ ns κs nt (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ{ dqt } tlbvec -∗
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone Hvec Hgeom Hal4 Hpmp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ ns κs nt) "Hsi".
    iDestruct (instr_lift_s_acq_rvc2 root_ppn σ ns κs nt pc i satp0 mstatus0 misa0
                 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hasid Hvec Hgeom Hal4 Hpmp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hpmpc Hpmpa Hpma Hhtif Hmisa Hinstr") as %Hlift.
    iDestruct (dispatch_S_from_regs σ ns κs nt misa0 mip_v mie_v mdv0 mstatus0 meip seip
                 HmisaS Hmm
                 with "Hsi Hmisa Hmipc Hmeipc Hseipc Hmiec Hmdlc Hmstatus") as %Hdisp0.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) σ = Some (None, σ))
      by (rewrite Hdisp0 Hdnone; reflexivity).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ ns κs nt Lpc
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
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
    rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
  Qed.

  (* [wp_instr_s_intr]'s WALK sibling: slot 0 is EMPTY, the fetch page-walks
     the owned PTE and FILLS it (ghost tlb update mirrored here); the caller's
     fupd runs at the FILLED state σf and receives the updated tlb cell. *)
  Lemma wp_instr_s_intr_fill (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqb : dfrac} :
    let tlbfilled := vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    vec_access_dec tlbvec 0 = None ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ tlbvec -∗
    pte_super_bytes root_ppn dqb -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σf ns κs nt (Hpceq : register_lookup PC σf.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ tlbfilled -∗
       pte_super_bytes root_ppn dqb -∗
       state_interp σf ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tlbfilled.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hvec Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ ns κs nt) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_acq_walk root_ppn σ ns κs nt pc r
                 satp0 mstatus0 misa0 menvcfg0 region_pte pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hasid Hppn Hvec HPBMTE Hgeom Hal4 Hpmp
                 Hpmpp Hmatchp0 Hptep Halignp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    iDestruct (dispatch_S_from_regs σ ns κs nt misa0 mip_v mie_v mdv0 mstatus0 meip seip
                 HmisaS Hmm
                 with "Hsi Hmisa Hmipc Hmeipc Hseipc Hmiec Hmdlc Hmstatus") as %Hdisp0.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) σ = Some (None, σ))
      by (rewrite Hdisp0 Hdnone; reflexivity).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbfilled with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := pw_filled_acq root_ppn tlbvec σ : state riscv_lang).
    iAssert (state_interp σf ns κs nt) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, pw_filled_acq, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf ns κs nt with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, pw_filled_acq, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf ns κs nt Lpc_σf
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
    - (* F_RVC h *)
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
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
      iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

  (* THE UNIFIED interrupt-layer engine over the consistency invariant. *)
  Lemma wp_instr_s_intr_tlbinv (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqb : dfrac} :
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pte_super_bytes root_ppn dqb -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ ns κs nt (Hpceq : register_lookup PC σ.(sregs) = pc)
       (tlbvec_f : vec (option TLB_Entry) (2 ^ 6))
       (Hconsf : tlb_pt_consistent root_ppn tlbvec_f),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ tlbvec_f -∗
       pte_super_bytes root_ppn dqb -∗
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hinstr H".
    iDestruct "Htlbinv" as (tlbvec) "[Htlb %Hcons]".
    destruct (Hcons 0 ltac:(vm_compute; split; [discriminate | reflexivity])) as [Hvec0 | Hvec0].
    - (* slot 0 EMPTY: the fetch walks and fills *)
      iApply (wp_instr_s_intr_fill root_ppn E Φ pc is_rvc i
                satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 region_pte tlbvec
                HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hvec0 Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp
                with "Hhw Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr").
      iIntros (σf ns κs nt Hpceq) "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi".
      iApply ("H" $! σf ns κs nt Hpceq
                (vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn (mword_of_int 0))))
                (tlb_pt_consistent_fill root_ppn tlbvec 0
                   ltac:(vm_compute; split; [discriminate | reflexivity]) Hcons)
              with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi").
    - (* slot 0 RESIDENT: TLB hit *)
      iApply (wp_instr_s_intr root_ppn E Φ pc is_rvc i
                satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 tlbvec
                HN Hmode Hasid HSXL Hmm Hdnone Hvec0 Hgeom Hal4 Hpmp
                with "Hhw Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpc Hinstr").
      iIntros (σ ns κs nt Hpceq) "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hsi".
      iApply ("H" $! σ ns κs nt Hpceq tlbvec Hcons
              with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi").
  Qed.

  (* [wp_instr_s_intr]'s WALK sibling: slot 0 is EMPTY, the fetch page-walks
     the owned PTE and FILLS it (ghost tlb update mirrored here); the caller's
     fupd runs at the FILLED state σf and receives the updated tlb cell. *)
  Lemma wp_instr_s_intr_rvc2_fill (root_ppn : mword 44) E Φ
      (pc : mword 64) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) {dq dqb : dfrac} :
    let tlbfilled := vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn (mword_of_int 0))) in
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    vec_access_dec tlbvec 0 = None ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb ↦ᵣ tlbvec -∗
    pte_super_bytes root_ppn dqb -∗
    PC ↦ᵣ pc -∗
    instr pc true i -∗
    (∀ σf ns κs nt (Hpceq : register_lookup PC σf.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ tlbfilled -∗
       pte_super_bytes root_ppn dqb -∗
       state_interp σf ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σf nextPC (add_vec_int (register_lookup PC σf.(sregs)) 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tlbfilled.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hvec Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpteregion pmar0 Hpma_all) as (Hmatchp0 & Hptep).
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ ns κs nt) "Hsi".
    destruct r as [e | w | h | erx];
      [ iDestruct "Hbytes" as %[_ []] | cbn [fetch_is_rvc] in Hrvc; discriminate Hrvc | | iDestruct "Hbytes" as %[_ []] ].
    iDestruct (fetch_from_instr_bytes_s_acq_rvc2_walk root_ppn σ ns κs nt pc h
                 satp0 mstatus0 misa0 menvcfg0 region_pte pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HSXL Hmode Hasid Hppn Hvec HPBMTE Hgeom Hal4 Hpmp
                 Hpmpp Hmatchp0 Hptep Halignp
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    iDestruct (dispatch_S_from_regs σ ns κs nt misa0 mip_v mie_v mdv0 mstatus0 meip seip
                 HmisaS Hmm
                 with "Hsi Hmisa Hmipc Hmeipc Hseipc Hmiec Hmdlc Hmstatus") as %Hdisp0.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) σ = Some (None, σ))
      by (rewrite Hdisp0 Hdnone; reflexivity).
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbfilled with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := pw_filled_acq root_ppn tlbvec σ : state riscv_lang).
    iAssert (state_interp σf ns κs nt) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, pw_filled_acq, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf ns κs nt with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, pw_filled_acq, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iMod ("H" $! σf ns κs nt Lpc_σf
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    cbn [fetch_is_rvc] in Hdec0.
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
    rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'".
    iIntros "Hhs' Hpc'". iSpecialize ("Hcont" with "Hhs' Hpc'"). iNext. iExact "Hcont".
  Qed.

  (* THE UNIFIED interrupt-layer engine over the consistency invariant. *)
  Lemma wp_instr_s_intr_rvc2_tlbinv (root_ppn : mword 44) E Φ
      (pc : mword 64) (i : instruction)
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqb : dfrac} :
    ↑minstretN ⊆ E →
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗
    pte_super_bytes root_ppn dqb -∗
    PC ↦ᵣ pc -∗
    instr pc true i -∗
    (∀ σ ns κs nt (Hpceq : register_lookup PC σ.(sregs) = pc)
       (tlbvec_f : vec (option TLB_Entry) (2 ^ 6))
       (Hconsf : tlb_pt_consistent root_ppn tlbvec_f),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ{ dq } satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       mip ↦ᵣ{ dq } mip_v -∗
       sig_meip ↦ᵣ{ dq } meip -∗
       sig_seip ↦ᵣ{ dq } seip -∗
       pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
       pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
       tlb ↦ᵣ tlbvec_f -∗
       pte_super_bytes root_ppn dqb -∗
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 2))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hinstr H".
    iDestruct "Htlbinv" as (tlbvec) "[Htlb %Hcons]".
    destruct (Hcons 0 ltac:(vm_compute; split; [discriminate | reflexivity])) as [Hvec0 | Hvec0].
    - (* slot 0 EMPTY: the fetch walks and fills *)
      iApply (wp_instr_s_intr_rvc2_fill root_ppn E Φ pc i
                satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 region_pte tlbvec
                HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hvec0 Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp
                with "Hhw Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hpc Hinstr").
      iIntros (σf ns κs nt Hpceq) "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi".
      iApply ("H" $! σf ns κs nt Hpceq
                (vec_update_dec tlbvec 0 (Some (pw_tlb_entry root_ppn (mword_of_int 0))))
                (tlb_pt_consistent_fill root_ppn tlbvec 0
                   ltac:(vm_compute; split; [discriminate | reflexivity]) Hcons)
              with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi").
    - (* slot 0 RESIDENT: TLB hit *)
      iApply (wp_instr_s_intr_rvc2 root_ppn E Φ pc i
                satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 tlbvec
                HN Hmode Hasid HSXL Hmm Hdnone Hvec0 Hgeom Hal4 Hpmp
                with "Hhw Hinv Hhs Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpc Hinstr").
      iIntros (σ ns κs nt Hpceq) "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hsi".
      iApply ("H" $! σ ns κs nt Hpceq tlbvec Hcons
              with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hmipc Hmeipc Hseipc Hpmpc Hpmpa Htlb Hpbytes Hsi").
  Qed.

  (* the RVC gpr-write engine over [wp_instr_s_intr] (mirror of
     WpSmodeGpr.wp_rvc_gpr_write_s, raw cells instead of smode_config). *)

  Lemma wp_rvc_gpr_write_s_intr (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5)
      (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64))
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqb : dfrac} :
    ↑minstretN ⊆ E ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      satp ↦ᵣ{ dq } satp0 -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      mip ↦ᵣ{ dq } mip_v -∗
      sig_meip ↦ᵣ{ dq } meip -∗
      sig_seip ↦ᵣ{ dq } seip -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp Hrd Hbexec)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_intr_tlbinv root_ppn E Φ pc true base satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v
              meip seip pmpcfg0 pmpaddr00 region_pte HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq tlbvec_f Hconsf) "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2).
    { tmig. exact Lnpc0. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa [Htlb] Hpbytes [$Hpc' $Hnpc] [Hfmap]").
    { iExists tlbvec_f. iFrame "Htlb". iPureIntro. exact Hconsf. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* [wp_rvc_gpr_write_s_intr]'s sibling for pc 2-aligned but NOT 4-aligned,
     over [wp_instr_s_intr_rvc2] instead of [wp_instr_s_intr]. *)

  Lemma wp_rvc_gpr_write_s_intr_rvc2 (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5)
      (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64))
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqb : dfrac} :
    ↑minstretN ⊆ E ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    acq_fetch_geom pc ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 pc ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      satp ↦ᵣ{ dq } satp0 -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      mip ↦ᵣ{ dq } mip_v -∗
      sig_meip ↦ᵣ{ dq } meip -∗
      sig_seip ↦ᵣ{ dq } seip -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp Hrd Hbexec)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_intr_rvc2_tlbinv root_ppn E Φ pc base satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v
              meip seip pmpcfg0 pmpaddr00 region_pte HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq tlbvec_f Hconsf) "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2).
    { tmig. exact Lnpc0. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa [Htlb] Hpbytes [$Hpc' $Hnpc] [Hfmap]").
    { iExists tlbvec_f. iFrame "Htlb". iPureIntro. exact Hconsf. }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- the acquire instantiation: c.addi sp,-32, SIE symbolic ---- *)

  Lemma wp_acq_caddi_intr (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v : mword 64) (meip seip : mword 1)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (region_pte : PMA_Region) {dq dqb : dfrac} :
    ↑minstretN ⊆ E ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    s_dispatch mip_v meip seip mie_v mdv0 mstatus0 = None ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    pmp_tor0_sfetch_all pmpcfg0 pmpaddr00 acq_pc1 ->
    pmp_tor0_pte_read pmpcfg0 pmpaddr00 (pte_paddr root_ppn) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_paddr root_ppn)) 8 = Some region_pte /\
       (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    satp ↦ᵣ{ dq } satp0 -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    mip ↦ᵣ{ dq } mip_v -∗
    sig_meip ↦ᵣ{ dq } meip -∗
    sig_seip ↦ᵣ{ dq } seip -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
    pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
    tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
    pc_is acq_pc1 -∗
    gpr_file m -∗
    kernel_text -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      satp ↦ᵣ{ dq } satp0 -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      mip ↦ᵣ{ dq } mip_v -∗
      sig_meip ↦ᵣ{ dq } meip -∗
      sig_seip ↦ᵣ{ dq } seip -∗
      pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
      pmpaddr_n ↦ᵣ{ dq } pmpaddr00 -∗
      tlb_inv root_ppn -∗ pte_super_bytes root_ppn dqb -∗
      pc_is (mword_of_int (KernelSyms.acquire + 0x2) : mword 64) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 acq_i1)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hpmp Hpmpp Hpteregion Halignp)
      "#Hhw #Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hfile #Htext Hcont".
    iPoseProof (acq_instr1 with "Htext") as "Hi1".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hgeom : acq_fetch_geom acq_pc1).
    { split; [vm_compute; reflexivity |].
      split; [apply bv_eq; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity]. }
    assert (Hal4 : is_aligned_vaddr (Virtaddr acq_pc1) 4 = false) by (vm_compute; reflexivity).
    assert (Hpc2 : add_vec_int acq_pc1 2 = (mword_of_int (KernelSyms.acquire + 0x2) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    unshelve iApply (wp_rvc_gpr_write_s_intr_rvc2 root_ppn E Φ acq_pc1 csp_rs1 csp_rs1 csp_rs1
              (ITYPE (sign_extend' 12 acq_i1, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 acq_i1)))
              m satp0 mstatus0 mie_v mdv0 menvcfg0 mip_v meip seip pmpcfg0 pmpaddr00 region_pte
              HN Hmode Hasid HSXL Hmm Hdnone HPBMTE Hppn Hgeom Hal4 Hpmp Hpmpp Hpteregion Halignp Hsp _
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv Hpbytes Hpc Hfile Hi1 [Hcont]").
    2:{ iIntros "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv2 Hpbytes2 Hpc Hfile".
        iEval (rewrite Hpc2) in "Hpc".
        iApply ("Hcont" with "Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Hmip Hmeip Hseip Hpmpc Hpmpa Htlbinv2 Hpbytes2 Hpc Hfile"). }
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (sign_extend' 12 acq_i1) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

End WpInstrIntr.

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

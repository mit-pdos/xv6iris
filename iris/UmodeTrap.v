(* UmodeTrap.v -- the SYNCHRONOUS-exception trap reduction, generalized over
   the trap cause and the trapping privilege (User or Supervisor).

   This is phase 1 of the arbitrary user-level execution theorem: with
   xv6's medeleg = 0xffff every exception user code can raise (ecall,
   page faults, illegal instruction, misaligned access, breakpoint, ...)
   delegates to Supervisor, and the ONLY kernel re-entry point is stvec's
   direct-mode base.  The reductions here are the sync twins of
   WpIntrCore's [exec_trap_handler_S_intr] / [exec_handle_interrupt_S]:

     [exec_exception_delegatee_ne_M] : medeleg bit set + misa.S  ==>
         exception_delegatee e p = Supervisor      (p = User or Supervisor)
     [exec_trap_handler_S_any]       : trap_handler Supervisor c pc info None
         writes scause / mstatus(SPIE,SIE,SPP,SPELP) / stval / sepc /
         cur_privilege and returns stvec's direct-mode base -- for ANY
         TrapCause c (interrupt or exception) and trapping privilege
         User or Supervisor (SPP := 0 resp. 1).
     [exec_exception_handler_ne_M]   : exception_handler p exc pc, the
         delegation + trap_handler composition.
     [exec_handle_exception_ne_M]    : handle_exception xtval e, the
         try_step-arm wrapper (reads cur_privilege + PC, runs the handler,
         writes nextPC := stvec base).

   The write tower [utrap_state] and the [stvec_base] target are the
   post-trap state the user-mode WP hands to its kernel-re-entry
   continuation. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpDecode WpLeafCommon.
Require Import WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 exception_delegatee: with the exception's medeleg bit set and       *)
(*    misa.S on, an exception raised BELOW Machine delegates to           *)
(*    Supervisor.                                                          *)
(* ===================================================================== *)

Lemma exec_exception_delegatee_ne_M (e : ExceptionType) (p : Privilege) s :
  p = User \/ p = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                 (uint (exceptionType_bits_forwards e))) = true ->
  exec (exception_delegatee e p) s = Some (Supervisor, s).
Proof.
  intros Hp HmisaS Hdel.
  unfold exception_delegatee.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)).
  cbn beta. cbv zeta.
  erewrite exec_bind_Some.
  2:{ rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_S s)).
      rewrite HmisaS. apply exec_returnM. }
  cbn beta.
  rewrite Hdel.
  destruct Hp; subst p; apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §2 The generalized S-destined trap reduction.                          *)
(*                                                                         *)
(*    [spp_bits] is the SPP bit trap_handler records: 0 when trapping      *)
(*    from User, 1 from Supervisor (Machine is an internal_error in the    *)
(*    delegated branch and excluded by [Hp]).                              *)
(* ===================================================================== *)

Definition spp_bits (p : Privilege) : mword 1 :=
  match p with User => 'b"0" | _ => 'b"1" end.

Section UTrapReduce.
  Context (s : mstate) (c : TrapCause) (p : Privilege) (pc0 : mword 64)
          (info : option (mword 64)).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hp : p = User \/ p = Supervisor.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = p.
  Hypothesis Hms : register_lookup mstatus s.(sregs) = ms_v.
  Hypothesis Hsc : register_lookup scause s.(sregs) = sc_old.
  Hypothesis Hstvec : register_lookup stvec s.(sregs) = stvec_v.
  Hypothesis Help : register_lookup elp s.(sregs) = elp_v.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  Hypothesis Hpc : register_lookup PC s.(sregs) = pc0.

  (* the model's exact write order (same tower as WpIntrCore's TrapReduce,
     with the cause bits, the SPP bit, and the stval value generalized) *)
  Let ms_e := update_subrange_vec_dec ms_v 23 23 elp_v.
  Let s1 := set_reg s mstatus ms_e.
  Let s1e := set_reg s1 elp (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let c1 := update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
              (bool_to_bit (trapCause_is_interrupt c)).
  Let s2 := set_reg s1e scause c1.
  Let c2 := update_subrange_vec_dec c1 (64 - 2) 0
              (zero_extend' (64 - 1) (trapCause_bits_forwards c)).
  Let s3 := set_reg s2 scause c2.
  Let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e).
  Let s4 := set_reg s3 mstatus ms_a.
  Let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0").
  Let s5 := set_reg s4 mstatus ms_b.
  Let ms_c := update_subrange_vec_dec ms_b 8 8 (spp_bits p).
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (tval info).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_S_any :
    exec (trap_handler Supervisor c pc0 info None) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hp Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
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
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (p, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta.
    (* the SPP bit: 0 from User, 1 from Supervisor *)
    assert (Hspp : exec (match p with
                         | User => returnM ('b"0" : mword 1)
                         | Supervisor => returnM ('b"1" : mword 1)
                         | Machine => internal_error "sys/sys_control.sail" 231
                                        "invalid privilege for s-mode trap"
                         | VirtualUser => internal_error "sys/sys_control.sail" 232
                                        "Hypervisor extension not supported"
                         | VirtualSupervisor => internal_error "sys/sys_control.sail" 233
                                        "Hypervisor extension not supported"
                         end) s5 = Some (spp_bits p, s5)).
    { destruct Hp as [-> | ->]; apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hspp). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s5)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stval _ s6)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc _ s7)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege _ s8)).
    cbn [handle_trap_extension].
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_track_trap_S (trapCause_is_interrupt c) (trapCause_bits_forwards c) s9)).
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

  (* --------------------------------------------------------------------- *)
  (* exception_handler: delegation + trap_handler, for a sync exception     *)
  (* [exc].  [c] must be the corresponding cause and [info] its excinfo.    *)
  (* --------------------------------------------------------------------- *)

  Lemma exec_exception_handler_ne_M (exc : sync_exception) :
    c = rv64d_types.Exception (exc.(sync_exception_trap)) ->
    info = exc.(sync_exception_excinfo) ->
    exc.(sync_exception_ext) = None ->
    bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                   (uint (exceptionType_bits_forwards (exc.(sync_exception_trap))))) = true ->
    exec (exception_handler p exc pc0) s = Some (stvec_base stvec_v, s9).
  Proof using Hp Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    intros Hc Hinfo Hext Hdel.
    unfold exception_handler.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_exception_delegatee_ne_M (exc.(sync_exception_trap)) p s Hp HmisaS Hdel)).
    cbn beta.
    change (get_config_print_exception tt) with false.
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt s)).
    rewrite <- Hc, <- Hinfo, Hext.
    apply exec_trap_handler_S_any.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* handle_exception: the try_step trap-arm wrapper.  Reads                *)
  (* cur_privilege + PC, runs the handler, and writes nextPC := stvec       *)
  (* base.  [c]/[info] are forced by the exception + xtval.                 *)
  (* --------------------------------------------------------------------- *)

  Lemma exec_handle_exception_ne_M (xtval : mword 64) (e : ExceptionType) :
    c = rv64d_types.Exception e ->
    info = xtval_exception_value e xtval ->
    bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                   (uint (exceptionType_bits_forwards e))) = true ->
    exec (handle_exception xtval e) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hp Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    intros Hc Hinfo Hdel.
    unfold handle_exception.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
    rewrite Hpriv Hpc.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_exception_handler_ne_M (make_sync_exception e xtval) Hc Hinfo eq_refl Hdel)).
    apply exec_set_next_pc.
  Qed.

End UTrapReduce.

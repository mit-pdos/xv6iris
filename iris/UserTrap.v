(* UserTrap.v -- the U-mode INTERRUPT trap tower: the exec-level reduction
   of taking a pending (delegated, hence S-destined) interrupt OUT OF USER
   MODE.  Mirrors WpIntrCore's Supervisor tower ([TrapReduce] /
   [exec_run_hart_active_pending]); the only semantic difference is the
   SPP write: trapping FROM User records SPP := 0 (so the handler's sret
   returns to User).

   [utrap_ms] is the delivered mstatus as a function of the pre-trap one
   (SPELP := elp; SPIE := SIE; SIE := 0; SPP := 0, in the model's exact
   update order), with the bit facts the [user_trap_frame] re-assembly
   needs: SIE = 0, SPP = 0, and MPRV / MXR / SXL preserved
   ([trap_mstatus_ok] from [user_mstatus_ok]).                            *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
From iris.program_logic Require Import language lifting.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecode WpLeafCommon WpGprCsrwB WpIntrBits WpIntrCore.
Require Import UserPt UserExec UserStep.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The delivered mstatus and its bit facts.                             *)
(* ===================================================================== *)

(* trap-from-User mstatus transform (SPP := 0; otherwise = trap_ms) *)
Definition utrap_ms (elp_v : mword 1) (ms : mword 64) : mword 64 :=
  let ms_e := update_subrange_vec_dec ms 23 23 elp_v in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  update_subrange_vec_dec ms_b 8 8 ('b"0").

Lemma utrap_ms_SIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SIE (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SPIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPIE (utrap_ms elp_v ms) = _get_Mstatus_SIE ms.
Proof. unfold utrap_ms, _get_Mstatus_SPIE, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPP (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SPP; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MPRV (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPRV (utrap_ms elp_v ms) = _get_Mstatus_MPRV ms.
Proof. unfold utrap_ms, _get_Mstatus_MPRV; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MXR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MXR (utrap_ms elp_v ms) = _get_Mstatus_MXR ms.
Proof. unfold utrap_ms, _get_Mstatus_MXR; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SXL (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL (utrap_ms elp_v ms) = _get_Mstatus_SXL ms.
Proof. unfold utrap_ms, _get_Mstatus_SXL; cbn zeta; mw_prep; tb2. Qed.

(* ===================================================================== *)
(* §2 The trap_handler / handle_interrupt reduction at cur_priv = User.    *)
(* Clone of WpIntrCore's [TrapReduce] with the SPP write flipped to 'b"0"; *)
(* the DELIVERY privilege stays Supervisor (the interrupt was delegated).  *)
(* ===================================================================== *)
Section UTrapReduce.
  Context (s : mstate) (i : InterruptType) (pc0 : mword 64).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = User.
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
  Let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"0").
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (zeros' 64).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_U_intr :
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
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (User, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"0" : mword 1) s5)). cbn beta.
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

  Lemma exec_handle_interrupt_U :
    exec (handle_interrupt i Supervisor) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_interrupt.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite Hpc.
    rewrite (exec_bind_Some _ _ _ _ _ exec_trap_handler_U_intr).
    apply exec_set_next_pc.
  Qed.

End UTrapReduce.

(* run_hart_active on a pending interrupt at User: NO fetch, NO decode, NO
   execute; the state is untouched (dispatchInterrupt only reads). *)
Lemma exec_run_hart_active_pending_U (s : mstate) (i : InterruptType) (p : Privilege) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (dispatchInterrupt User) s = Some (Some (i, p), s) ->
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

(* ===================================================================== *)
(* §3 The Iris INTERRUPT arm: a pending delegated interrupt traps the      *)
(* ACTIVE user hart to stvec, producing [user_trap_frame].  Rides the      *)
(* live [wp_exec_step_interrupt_inv] engine; the wire cells are BORROWED   *)
(* (dfrac-generic) and handed back to the continuation.                    *)
(* ===================================================================== *)
Section UserIntrArm.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  Lemma wp_user_step_interrupt E Φ (i : InterruptType)
      (ms_v sc_v stval_v sepc_v va va' : mword 64)
      (g : gmap regidx (mword 64))
      (meip seip : mword 1) {dqe1 dqe2 : dfrac} :
    ↑minstretN ⊆ E ->
    user_mstatus_ok ms_v ->
    u_dispatch (uc_mip C) meip seip (uc_mie C) (uc_mideleg C) = Some (i, Supervisor) ->
    hw_config -∗
    minstret_inv -∗
    sig_meip ↦ᵣ{ dqe1 } meip -∗
    sig_seip ↦ᵣ{ dqe2 } seip -∗
    user_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va' g -∗
    upt_inv pt -∗
    user_cfg C -∗
    ▷ (sig_meip ↦ᵣ{ dqe1 } meip -∗ sig_seip ↦ᵣ{ dqe2 } seip -∗
       user_trap_frame C pt -∗
       WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hmsok Hd) "#Hhw #Hminstret Hmeip Hseip Hregs Hupt Hcfg Hcont".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc &
                           Hpc & Hnpc & Hgpr)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & #Help & %HmisaS & _ & _ & _ & _ & _ & _ &
        %Help_ne & _)".
    (* elp is 1 bit and pinned ≠ LP_EXPECTED, so it already holds the value
       the trap's reset_elp writes *)
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    iApply (wp_exec_step_interrupt_inv E Φ HN with "Hminstret Hhs").
    iIntros (σ) "[Hreg Hmd]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsc") as %Lsc.
    iDestruct (reg_valid_dq with "Hreg Hstvec") as %Lstvec.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl") as %Lmdl.
    assert (Hdisp : exec (dispatchInterrupt User) σ = Some (Some (i, Supervisor), σ)).
    { rewrite (exec_dispatchInterrupt_U_reduce σ (uc_mip C) (uc_mie C)
                 (uc_mideleg C) meip seip); try assumption.
      - rewrite Hd. reflexivity.
      - rewrite exec_currentlyEnabled_S. rewrite Lmisa. rewrite HmisaS. reflexivity.
      - exact (uc_mm C). }
    pose proof (exec_trap_handler_U_intr σ i va ms_v sc_v (uc_stvec C) elp0
                  Lpriv Lms Lsc Lstvec Lelp
                  ltac:(rewrite Lmisa; exact HmisaS) (uc_tvd C)) as Htrap.
    pose proof (exec_handle_interrupt_U σ i va ms_v sc_v (uc_stvec C) elp0
                  Lpriv Lms Lsc Lstvec Lelp
                  ltac:(rewrite Lmisa; exact HmisaS) (uc_tvd C) Lpc) as Hhi.
    (* ghost updates, mirroring the tower's write order *)
    iMod (reg_update _ mstatus _ (update_subrange_vec_dec ms_v 23 23 elp0)
            with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite Lelp Help0. reflexivity. }
    iMod (reg_update _ scause _ _ with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ _ with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ _ with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ _ with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms elp0 ms_v) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (zeros' 64) with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ va with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base (uc_stvec C)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists i, Supervisor, _.
    iSplitR. { iPureIntro. exact (exec_run_hart_active_pending_U σ i Supervisor Lpriv Hdisp). }
    iSplitR. { iPureIntro. exact Hhi. }
    (* the engine wants [PC ↦ lookup PC s_trap]; PC is untouched by the tower *)
    unfold set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmd".
    iSplitL "Hpc".
    { repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lpc. iExact "Hpc". }
    iNext.
    iIntros "Hhs Hpc".
    rewrite register_lookup_set.
    iDestruct "Hcont" as "Hcont".
    iApply ("Hcont" with "Hmeip Hseip").
    (* re-assemble the trap frame *)
    iExists (utrap_ms elp0 ms_v), _, (zeros' 64), va, g.
    iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hgpr Hupt".
    iSplitR.
    { iPureIntro.
      destruct Hmsok as (HSXL & HMPRV & HMXR).
      split; [ rewrite utrap_ms_SXL; exact HSXL | ].
      split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
      split; [ rewrite utrap_ms_MXR; exact HMXR | ].
      split; [ rewrite utrap_ms_SPP; reflexivity | ].
      rewrite utrap_ms_SIE; reflexivity. }
    iSplitL "Hpc Hnpc". { iFrame "Hpc Hnpc". }
    iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
  Qed.

End UserIntrArm.

(* ===================================================================== *)
(* §4 Exception delegation at User: with the cause's medeleg bit set (and  *)
(* S present), a synchronous exception from U delegates to Supervisor.     *)
(* ===================================================================== *)
Lemma exec_exception_delegatee_U (e : ExceptionType) (medl : mword 64) s :
  register_lookup medeleg s.(sregs) = medl ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  bit_to_bool (access_vec_dec medl (uint (exceptionType_bits_forwards e))) = true ->
  exec (exception_delegatee e User) s = Some (Supervisor, s).
Proof.
  intros Hmedl HES Hbit.
  unfold exception_delegatee. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)). cbn beta.
  rewrite Hmedl.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hsup : exec L s = Some (true, s)) end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ HES). cbn match.
    rewrite Hbit. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsup). cbn beta. cbn match.
  replace (zopz0zI_u (privLevel_to_bits Supervisor) (privLevel_to_bits User))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

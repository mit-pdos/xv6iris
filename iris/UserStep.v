(* UserStep.v -- step-engine bricks for arbitrary user-mode execution
   (UserExec.v).  First brick: the INTERRUPT DISPATCH decision at User.

   At User privilege the effective mIE and sIE are both unconditionally
   true (priv < M and priv < S): interrupts are architecturally UNMASKABLE,
   and the device loop may raise the sig_seip wire concurrently at any
   time.  So every user-phase step begins with a genuine case split on the
   dispatch decision [u_dispatch] over the CURRENT wire/CSR values:
     - Some (i, Supervisor): a pending delegated interrupt -- the step
       takes the interrupt trap to stvec (the interrupt arm of the step
       obligation, landing in [user_trap_frame]);
     - None: the step proceeds to fetch/execute.
   The M-destined set is empty by [uc_mm] (mie & ~mideleg = 0, a boot
   constant), so a dispatched interrupt always goes to Supervisor.

   [exec_getPendingSet_U_reduce] / [exec_dispatchInterrupt_U_reduce] reduce
   the model's dispatcher to [u_dispatch], parameterized by the current
   register values; the Iris form [dispatch_U_from_regs] takes the cells at
   arbitrary dfracs, so it works both with today's pinned cells and with
   values borrowed from the future invariant shared with the device WP
   (neither the user- nor the kernel-side proofs are plumbed for that
   sharing yet).  Mirrors WpIntrCore's Supervisor reductions
   ([exec_getPendingSet_S_reduce] / [dispatch_S_from_regs]); the User
   variants are simpler because neither mstatus.MIE nor mstatus.SIE is
   consulted below the current privilege.                                 *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import MinstretInv.
Require Import SmodeCore WpIntrCore.
Require Import HartRunFull.
Require Import UserPtTree UserExec.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The dispatch decision at User: purely the S-destined pending set     *)
(* [s_pending] (no mstatus gate -- both effective enables are true).       *)
(* ===================================================================== *)

Definition u_dispatch (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv : mword 64) : option (InterruptType * Privilege) :=
  if neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64)
  then match findPendingInterrupt (s_pending mip_v meip seip mie_v mdv) with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Lemma exec_getPendingSet_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (getPendingSet User) s
    = Some ((if neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)
             then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
             else None), s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  (* effective mIE at User: priv < Machine, so unconditionally true *)
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq User Supervisor) (generic_eq User User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Machine) s)).
      change (generic_eq User Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq User Supervisor) (generic_eq User User)) with true.
    apply exec_returnm. }
  (* effective sIE at User: priv < Supervisor, so unconditionally true *)
  assert (HsIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq User User))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Supervisor) s)).
      change (generic_eq User Supervisor) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq User User) with true.
    apply exec_returnm. }
  (* upstream dropped the [or_boolM] guard and its assert: the delegation
     word is now read through a plain [if currentlyEnabled Ext_S] *)
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIEt).
  rewrite Hmie Hmdl Hmm.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq.
  rewrite andb_false_r andb_true_l.
  unfold s_pending, s_mip_bits.
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt User) s
    = Some (u_dispatch mip_v meip seip mie_v mdv_v, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_getPendingSet_U_reduce s mip_v mie_v mdv_v meip seip
               HES Hmip Hmeip Hseip Hmie Hmdl Hmm)).
  unfold u_dispatch.
  destruct (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)).
  - cbn match. destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
      apply exec_returnm.
  - cbn match. apply exec_returnm.
Qed.

(* THE BRIDGE TO THE SHARED DECISION.  [HartRunFull.dispatch_of_pending] is
   the decision ONCE THE PENDING SET IS KNOWN -- the common core of
   [WpIntrCore.s_dispatch] (Supervisor, SIE-gated) and [u_dispatch] (User,
   ungated).  The two coincide by CONVERSION, so this is [reflexivity] and
   the U rule of [HartRunFull] speaks the tier's own spelling. *)
Lemma u_dispatch_of_pending (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv : mword 64) :
  u_dispatch mip_v meip seip mie_v mdv
  = dispatch_of_pending (s_pending mip_v meip seip mie_v mdv).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* §1b .. §3 -- THE WAITING-HART STEP AND THE STEP OBLIGATION -- MOVED.    *)
(*                                                                        *)
(* The four pure [run_hart_waiting] facts ([exec_shouldWakeForInterrupt],  *)
(* [exec_run_hart_waiting_wake] / [_wake_resv] / [_stay]) and the two      *)
(* [riscv_step] wrappers around them are now in [HartStepFull.v], where    *)
(* they belong: they are facts about the MODEL with no user-tier content,  *)
(* and the rules that consume them ([swp_try_step_waiting] /               *)
(* [swp_exec_step_waiting]) sit below this file.  ONE of them changed on   *)
(* the way: [exec_run_hart_waiting_stay]'s premise was                     *)
(* [valid_reservation tt = true], which is STRONGER than the model needs   *)
(* -- at [exit_wait = false] the match's only reachable wake patterns are  *)
(* [(WAIT_WRS_STO|WAIT_WRS_NTO, false, _)], so a [WAIT_WFI] hart stays     *)
(* waiting whatever the axiom answers.  [HartStepFull]'s version takes     *)
(* [valid_reservation tt = true \/ wr = WAIT_WFI], which is what makes the *)
(* case split in [swp_try_step_waiting] EXHAUSTIVE.                        *)
(*                                                                        *)
(* The Iris halves ([wp_user_step_waiting], [user_step_obligation_holds],  *)
(* [wp_user_exec_active]) are being rebuilt on [swp_exec_step_waiting] --  *)
(* they no longer borrow [mip] from a clock invariant (the hart owns it),  *)
(* so they are frame-shaped rather than sigma-shaped.                      *)
(* ===================================================================== *)


(* (The old §4 full-WP RETIRING step engine [wp_user_step_retire] is gone:
   the payload-form [retire_branch] (UserArms.v) supersedes it -- the
   unified step wrapper owns the single step, so the retire arm produces
   the [wp_exec_step_minstret] payload instead of opening its own step.)   *)

(* ===================================================================== *)
(* §5 The decode-bridge agreement: the user frame's pins coincide with     *)
(* the U-mode reference decode state on every register the decoder reads.  *)
(* ===================================================================== *)
Require Import WpDecodeBridge DecodeTotalU.

Lemma agree_u (σ : mstate) :
  register_lookup cur_privilege σ.(sregs) = User ->
  register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
  register_lookup senvcfg σ.(sregs) = (mword_of_int 0 : mword 64) ->
  register_lookup mstateen0 σ.(sregs) = (mword_of_int 0 : mword 64) ->
  register_lookup sstateen0 σ.(sregs) = (mword_of_int 0 : mword 32) ->
  register_lookup misa σ.(sregs) = MISA_C ->
  agree_on D_u σ dstateU.
Proof.
  intros Hpriv Hmenv Hsenv Hms0 Hss0 Hmisa r Hr.
  unfold D_u in Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr | Hr]);
    apply register_beq_true in Hr; subst r;
    [ rewrite Hpriv | rewrite Hmenv | rewrite Hsenv
    | rewrite Hms0 | rewrite Hss0 | rewrite Hmisa ];
    first [ vm_compute; reflexivity
          | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* the U-mode decode image contains no landing-pad instruction (the
   Zicfilp gate is off at dstateU), so the lpad side condition of the
   run_hart_active dispatch discharges for every decodable word *)



(* ===================================================================== *)
(* §6 The BASE one-redirection progress composer: a 4-byte instruction    *)
(* whose execute returns [ExecuteAs other] (SINVAL_VMA -> SFENCE_VMA).    *)
(* [exec_hart_active_progress_base_gen] (SmodeCore.v) forbids ExecuteAs   *)
(* and [_RVC_gen] redirects only on the compressed path; this is the      *)
(* missing base-path redirect, same shape as both.                        *)
(* ===================================================================== *)
Lemma exec_hart_active_progress_base_redirect_gen
    (priv : Privilege) (s s_f s_x : mstate) (w : mword 32) (instr other : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Base w, s_f) ->
  exec (ext_decode w) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction instr = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 4))
    = Some (ExecuteAs other, set_reg s_f nextPC (add_vec_int pc 4)) ->
  exec (execute other) (set_reg s_f nextPC (add_vec_int pc 4)) = Some (resf, s_x) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad HpcF Hexec Hexec2.
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
  rewrite execR_bind execR_liftR Hexec2. cbn match.
  rewrite execR_returnR. cbn match. reflexivity.
Qed.

(* ===================================================================== *)
(* §6b The DIRECT RVC progress composer: a 2-byte compressed instruction  *)
(* whose execute returns its result DIRECTLY (no [ExecuteAs] expansion --  *)
(* C_NOP / C_NTL / ZCMOP / C_NOT / C_ZEXT_B / C_ILLEGAL).  The F_RVC analog *)
(* of [exec_hart_active_progress_base_gen]: mirrors [_RVC_gen] up to the    *)
(* nextPC write, then takes the base direct-execute tail.                  *)
(* ===================================================================== *)
Lemma exec_hart_active_progress_RVC_direct_gen
    (priv : Privilege) (s s_f s_x : mstate) (h : mword 16) (instr : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_RVC h, s_f) ->
  exec (ext_decode_compressed h) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (currentlyEnabled Ext_Zca) s_f = Some (true, s_f) ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 2)) = Some (resf, s_x) ->
  (match resf with ExecuteAs _ => False | _ => True end) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad HpcF Hzca Hexec Hnotexec.
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
  rewrite execR_bind.
  destruct resf; cbn in Hnotexec; try contradiction;
    cbn match; rewrite execR_returnR; cbn match; rewrite execR_returnR; reflexivity.
Qed.

(* ===================================================================== *)
(* §7 The ENTER-WAIT step: an ACTIVE hart executes a WRS and suspends.     *)
(* hart_state := HART_WAITING; NO pc tick, NO minstret bump (the epilogue  *)
(* only ticks/bumps a hart that ends the step ACTIVE) -- so PC stays at    *)
(* the WRS and nextPC at the instruction after it, exactly the decoupled   *)
(* shape [user_inv]'s WAITING case binds.                                  *)
(* ===================================================================== *)
Section StepEnterWait.
  Context (s s_x : mstate) (wr : WaitReason) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Execute (Enter_Wait wr, ib), s_x).
  Hypothesis Hnop : wait_is_nop wr = false.

  Let s_w : mstate := set_reg s_x hart_state (HART_WAITING (wr, ib)).

  Lemma exec_riscv_step_enter_wait : exec (riscv_step false) s = Some (tt, s_w).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (true, s_w))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Enter_Wait arm: not a nop -> (print-skip) >> write hart_state *)
    rewrite Hnop. cbn match.
    assert (Lw : register_lookup hart_state s_w.(sregs) = HART_WAITING (wr, ib)).
    { unfold s_w; rewrite ?sregs_set_reg. apply register_lookup_set. }
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ unfold get_config_print_instr. cbn match.
                apply (exec_returnM tt s_x). }
            apply (exec_write_reg hart_state (HART_WAITING (wr, ib)) s_x). }
        apply (exec_read_reg hart_state s_w). }
    rewrite Lw. cbn beta iota.
    apply exec_returnm.
  Qed.
End StepEnterWait.

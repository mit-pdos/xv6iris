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
Require Import MinstretInv RegFile.
Require Import SmodeCore WpIntrCore.
Require Import HartLift HartSpan HartMCycle HartStepFull HartRunFull.
Require Import UserFrame.
Require Import PtreeType PtTree SmodePte UserPtTree UserExec.
Require Import HartMemRun PtBytes UserBytes.
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
(* waiting whatever the predicate answers.  [HartStepFull]'s version takes *)
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
Require Import TsoCtx.

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

(* ===================================================================== *)
(* §2 THE WAITING-HART STEP, at the FRAME layer.                          *)
(*                                                                       *)
(* One machine step from a WRS-suspended hart either STAYS waiting        *)
(* (nothing observable changes but the wrapper's minstret_increment       *)
(* write) or WAKES and retires (hart_state := ACTIVE, PC ticks to         *)
(* nextPC).  The machine picks, on a value nobody can pin -- the wake     *)
(* test reads mip, which the tick writes, and [valid_reservation] is an   *)
(* opaque platform predicate -- so the rule's conclusion is a DISJUNCTION *)
(* and the tier absorbs both arms into the same [user_inv].               *)
(*                                                                       *)
(* WHAT CHANGED AGAINST THE PRE-PORT PROOF: everything sigma-shaped.      *)
(* There is no [wp_exec_step_minstret] callback, no [mstate_interp], and  *)
(* above all NO [clock_mip_acc] borrow -- the hart OWNS mip (it rides in  *)
(* [user_regs]'s [clock_res]), so the step is a plain frame-in/frame-out  *)
(* application of [HartStepFull.swp_exec_step_waiting] and the WHOLE of   *)
(* the old sigma bookkeeping (three [reg_update]s, six [reg_valid_dq]s,   *)
(* the invariant open/close) is gone.                                     *)
(*                                                                       *)
(* THE PRICE, and it is the port's one genuinely new obligation: the      *)
(* frame layer speaks a [regstate], so the entry file has to be BUILT     *)
(* ([UserFrame.u_rs]) and the exit file has to be READ BACK.  The exit is *)
(* the two [wpin_*] lemmas below: [wait_post] describes the landing file  *)
(* only up to agreement off the three clock cells, which is exactly       *)
(* enough because [clock_res] holds their values existentially anyway.    *)
(* ===================================================================== *)
(* [tk_clock3] is the three cells the tick may move; nothing the tier names
   is one of them, and the check computes. *)
Local Ltac u_notin_clock := apply (bool_decide_unpack _); vm_compute; reflexivity.

Section UserStepWaiting.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ---- reading the landing file back, cell by cell ---- *)


  Lemma wpin_stay (rs rsP rs3 : regstate) (r : register) :
    reg_agree_on (u_Drw ∪ u_Dro) rsP (wrap_pre rs) ->
    reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 rsP ->
    r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
    register_beq r (R_bool minstret_increment) = false ->
    register_lookup r rs3 = register_lookup r rs.
  Proof.
    intros Hp Hag Hin Hnc Hne.
    rewrite (Hag r ltac:(apply elem_of_difference; split; assumption)).
    rewrite (Hp r Hin). exact (wrap_pre_other r rs Hne).
  Qed.

  Lemma wpin_wake (rs rs' rs3 : regstate) (mi2 : mword 64) (r : register) :
    reg_agree_on (u_Drw ∪ u_Dro) rs'
      (register_set hart_state (HART_ACTIVE tt) (wrap_pre rs)) ->
    reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 (wrap_post rs' mi2) ->
    r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
    register_beq r (R_bitvector_64 minstret) = false ->
    register_beq r (R_bitvector_64 PC) = false ->
    register_beq r hart_state = false ->
    register_beq r (R_bool minstret_increment) = false ->
    register_lookup r rs3 = register_lookup r rs.
  Proof.
    intros Hp Hag Hin Hnc Hms Hpc Hhs Hmi.
    rewrite (Hag r ltac:(apply elem_of_difference; split; assumption)).
    rewrite (wrap_post_other r rs' mi2 Hms Hpc).
    rewrite (Hp r Hin) (irrelevant_register_set r hart_state _ _ Hhs).
    exact (wrap_pre_other r rs Hmi).
  Qed.

  (* the two cells the WAKE arm genuinely moves *)
  Lemma wpin_wake_hart (rs rs' rs3 : regstate) (mi2 : mword 64) :
    reg_agree_on (u_Drw ∪ u_Dro) rs'
      (register_set hart_state (HART_ACTIVE tt) (wrap_pre rs)) ->
    reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 (wrap_post rs' mi2) ->
    register_lookup hart_state rs3 = HART_ACTIVE tt.
  Proof.
    intros Hp Hag.
    rewrite (Hag hart_state ltac:(apply elem_of_difference; split;
              [ exact u_in_hart | u_notin_clock ])).
    rewrite (wrap_post_other hart_state rs' mi2 eq_refl eq_refl).
    rewrite (Hp hart_state u_in_hart). apply register_lookup_set.
  Qed.

  Lemma wpin_wake_pc (rs rs' rs3 : regstate) (mi2 : mword 64) :
    reg_agree_on (u_Drw ∪ u_Dro) rs'
      (register_set hart_state (HART_ACTIVE tt) (wrap_pre rs)) ->
    reg_agree_on ((u_Drw ∪ u_Dro) ∖ tk_clock3) rs3 (wrap_post rs' mi2) ->
    register_lookup (R_bitvector_64 PC) rs3
      = register_lookup (R_bitvector_64 nextPC) rs.
  Proof.
    intros Hp Hag.
    rewrite (Hag (R_bitvector_64 PC) ltac:(apply elem_of_difference; split;
              [ exact u_in_PC | u_notin_clock ])).
    rewrite wrap_post_PC.
    rewrite (Hp (R_bitvector_64 nextPC) u_in_nPC).
    rewrite (irrelevant_register_set (R_bitvector_64 nextPC) hart_state _ _
               eq_refl).
    (* [exact] with the index GIVEN: ssreflect's [apply] picks the wrong
       instantiation here and reports it as a PC/nextPC mismatch *)
    exact (wrap_pre_other (R_bitvector_64 nextPC) rs eq_refl).
  Qed.

End UserStepWaiting.

(* ===================================================================== *)
(* §2b THE CLOSE: from a landing file and its pins, back to [user_inv].    *)
(*                                                                       *)
(* Both arms of the WAITING step -- and, when it lands, the ACTIVE cycle  *)
(* -- exit here.  What it needs is exactly the cells whose VALUE          *)
(* [user_inv] pins; everything else ([scause]/[stval]/[sepc], the GPRs,   *)
(* the four counter cells) is existential in the invariant, so its pin at *)
(* [rs3] is [reflexivity] and no transport is owed.  The persistent       *)
(* [box] cells are not transported either: the caller still holds its own *)
(* copies, and the frame's are dropped.                                   *)
(*                                                                       *)
(* [Hpmp] is a WAND rather than six more pure premises: the pmp facts are *)
(* about the VALUES [pmp_config] existentially quantified, and the caller *)
(* has them in hand at the point it took that bundle apart.               *)
(* ===================================================================== *)
Section UserWaitClose.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  Lemma u_close_inv (t : ptree) (mm : PtBytes.pamap) (usatp : mword 64)
      (tlbvec : type_of_register tlb)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (rs3 : regstate) (hs3 : HartState) (ms3 va3 va3' : mword 64) :
    user_hart_ok hs3 ->
    user_mstatus_ok ms3 ->
    (forall u, hs3 = HART_ACTIVE u -> va3' = va3) ->
    register_lookup hart_state rs3 = hs3 ->
    register_lookup cur_privilege rs3 = User ->
    register_lookup (R_bitvector_64 mstatus) rs3 = ms3 ->
    register_lookup (R_bitvector_64 PC) rs3 = va3 ->
    register_lookup (R_bitvector_64 nextPC) rs3 = va3' ->
    register_lookup (R_bitvector_64 stvec) rs3 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs3 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs3 = uc_mideleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs3 = MENVCFG_S ->
    register_lookup (R_bitvector_64 satp) rs3 = usatp ->
    register_lookup pmpcfg_n rs3 = pcfg ->
    register_lookup pmpaddr_n rs3 = paddr ->
    register_lookup tlb rs3 = tlbvec ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    u_mem_wf pt t mm ->
    (pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗ pmp_config (ud_root pt)) -∗
    medeleg ↦ᵣ□ uc_medeleg C -∗
    senvcfg ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    mstateen0 ↦ᵣ□ (mword_of_int 0 : mword 64) -∗
    (R_bitvector_32 sstateen0) ↦ᵣ□ (mword_of_int 0 : mword 32) -∗
    (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv -∗
    (R_bitvector_32 scounteren) ↦ᵣ□ scenv -∗ mhpmcounter ↦ᵣ□ hpm -∗
    hreg_frame rs3 u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rs3 u_Dro -∗
    resv_any cpu_id -∗ pt_claims 2 t -∗ bytes_own mm -∗
    (∀ (t' : ptree) (mm' : PtBytes.pamap) (tlbvec' : type_of_register tlb),
       ⌜u_mem_step pt t t' mm mm'⌝ -∗
       ⌜tlb_ok_pt (mword_of_int 0) t' tlbvec'⌝ -∗
       upt_regs pt usatp tlbvec' -∗ bytes_own mm' -∗ user_pt_any pt) -∗
    Rut pt -∗
    user_inv C pt Rut.
  Proof.
    intros Hhok Hmsok Hlock Lhs Lpriv Lms Lpc Lnpc Lstvec Lmie Lmdl Lmenv
      Lsatp Lpcfg Lpaddr Ltlb Htlbok Hwf.
    iIntros "Hpmp #Hmedl #Hsenv #Hmste #Hsste #Hmcen #Hscen #Hhpm
             Hrw Hro Hresv Hclaims Hbytes Hclose Hrut".
    iDestruct (u_frames_elim rs3 (uc_dqc C) hs3 ms3
                 (register_lookup (R_bitvector_64 scause) rs3)
                 (register_lookup (R_bitvector_64 stval) rs3)
                 (register_lookup (R_bitvector_64 sepc) rs3) va3 va3'
                 (register_lookup (R_bitvector_64 minstret) rs3)
                 (register_lookup (R_bool minstret_increment) rs3)
                 (register_lookup (R_bitvector_32 mcountinhibit) rs3)
                 (register_lookup (R_bitvector_64 minstretcfg) rs3)
                 (register_lookup (R_bitvector_64 mcycle) rs3)
                 (register_lookup (R_bitvector_64 mtime) rs3)
                 (register_lookup (R_bitvector_64 mip) rs3)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C)
                 (register_lookup (R_bitvector_64 medeleg) rs3) MENVCFG_S
                 (register_lookup (R_bitvector_64 mstateen0) rs3)
                 (register_lookup (R_bitvector_32 sstateen0) rs3)
                 (register_lookup (R_bitvector_32 mcounteren) rs3)
                 (register_lookup (R_bitvector_32 scounteren) rs3)
                 (register_lookup mhpmcounter rs3)
                 (register_lookup (R_bitvector_64 misa) rs3)
                 (register_lookup (R_bitvector_64 mseccfg) rs3)
                 (register_lookup (R_bitvector_64 senvcfg) rs3)
                 (register_lookup pma_regions rs3)
                 (register_lookup htif_tohost_base rs3)
                 (register_lookup (R_bitvector_1 elp) rs3)
                 usatp pcfg paddr tlbvec
                 ltac:(rewrite /u_pins_regs; split_and!;
                       [ exact Lhs | exact Lpriv | exact Lms
                       | reflexivity | reflexivity | reflexivity
                       | exact Lpc | exact Lnpc | exact (u_regfile_agree rs3) ])
                 ltac:(rewrite /u_pins_tick; split_and!; reflexivity)
                 ltac:(rewrite /u_pins_cfg; split_and!;
                       [ exact Lstvec | exact Lmie | exact Lmdl
                       | reflexivity | exact Lmenv | reflexivity | reflexivity
                       | reflexivity | reflexivity | reflexivity ])
                 ltac:(rewrite /u_pins_hw; split_and!; reflexivity)
                 ltac:(rewrite /u_pins_pt; split_and!;
                       [ exact Lsatp | exact Lpcfg | exact Lpaddr | exact Ltlb ])
                 with "Hrw Hro")
      as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & HPC & HnPC & Hgpr &
           Hminstret & Hmincr & #Hmcnt & #Hmicfg & Hmcycle & Hmtime & Hmip &
           Hstvec & Hmie & Hmdl & _ & Hmenv & _ & _ & _ & _ & _ &
           _ & _ & _ & _ & _ & _ &
           Hsatp & Htlb & Hpcfg & Hpaddr)".
    iExists hs3, ms3, (register_lookup (R_bitvector_64 scause) rs3),
            (register_lookup (R_bitvector_64 stval) rs3),
            (register_lookup (R_bitvector_64 sepc) rs3), va3, va3',
            (u_regfile rs3).
    iSplitR; [ iPureIntro; exact Hhok |].
    iSplitR; [ iPureIntro; exact Hmsok |].
    iSplitR; [ iPureIntro; exact Hlock |].
    iSplitL "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr Hminstret Hmincr
             Hmcycle Hmtime Hmip Hresv".
    { rewrite /user_regs /u_regs /minstret_res /clock_res.
      iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr Hresv".
      iSplitL "Hminstret Hmincr".
      - iExists _, _, _, _. iFrame "Hminstret Hmincr Hmcnt Hmicfg".
      - iExists _, _, _. iFrame "Hmcycle Hmtime Hmip". }
    iSplitL "Hclaims Hbytes Hclose Hsatp Htlb Hpcfg Hpaddr Hpmp".
    { iApply ("Hclose" $! t mm tlbvec
                (u_mem_step_refl pt t mm Hwf) Htlbok with "[-Hbytes] Hbytes").
      rewrite /upt_regs. iFrame "Hsatp Htlb".
      iApply ("Hpmp" with "Hpcfg Hpaddr"). }
    iFrame "Hrut".
    rewrite /user_cfg. iFrame "Hstvec Hmie Hmdl Hmenv".
    iFrame "Hmedl Hsenv Hmste Hsste".
    iSplitR; [ iExists mcenv, scenv; iFrame "Hmcen Hscen"
             | iExists hpm; iFrame "Hhpm" ].
  Qed.

End UserWaitClose.

(* ===================================================================== *)
(* §2c THE WAITING ARM ITSELF.                                            *)
(* ===================================================================== *)
Section UserStepWaitArm.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  Lemma wp_user_step_waiting (wr : WaitReason) (ib : mword 32)
      (ms_v sc_v stval_v sepc_v va va' : mword 64) (g : regfile) :
    (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO) ->
    user_mstatus_ok ms_v ->
    hw_config -∗
    user_regs (HART_WAITING (wr, ib)) ms_v sc_v stval_v sepc_v va va' g -∗
    user_pt_any pt -∗ user_cfg C -∗ Rut pt -∗
    ▷ (user_inv C pt Rut -∗ WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hwr Hmsok.
    iIntros "#Hhw Hregs Hupt Hcfg Hrut Hcont".
    (* ---- take the three bundles apart ---- *)
    rewrite /user_regs u_regs_open.
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & HPC & HnPC
                           & Hgpr & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (mst mi mc micfg) "(Hminstret & Hmincr & #Hmcnt & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hmcycle & Hmtime & Hmip)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & #Hmedl & Hmenv & #Hsenv &
                          #Hmste & #Hsste & Hctr & Hhpmb)".
    iDestruct "Hctr" as (mcenv scenv) "[#Hmcen #Hscen]".
    iDestruct "Hhpmb" as (hpm) "#Hhpm".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & %Hmisaeq & %Hseceq & _ & #Hcert & _)".
    iDestruct (user_pt_inv_bytes pt with "Hupt") as (t mm usatp tlbvec)
      "(%Hwf & %Hsatpok & %Htlbok & (Hsatp & Htlb & Hpmp) & #Hclaims & Hbytes
        & Hclose)".
    iDestruct "Hpmp" as (pcfg paddr)
      "(Hpcfg & Hpaddr & %HpA & %Hpord & %HpX & %HpW & %HpR & %Hpcov)".
    iAssert (pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗ pmp_config (ud_root pt))%I
      as "Hpmpi".
    { iApply (pmp_config_intro (ud_root pt) pcfg paddr
                HpA Hpord HpX HpW HpR Hpcov). }
    (* ---- the entry file ---- *)
    set (RS := u_rs g (HART_WAITING (wr, ib)) mi mc (mword_of_int 0 : mword 32)
                 mcenv scenv hpm elp0 pmar0 None pcfg paddr tlbvec
                 va va' ms_v sc_v stval_v sepc_v mst cy ti ip micfg
                 misa0 mseccfg0 (mword_of_int 0 : mword 64)
                 (uc_stvec C) (uc_mie C) (uc_mideleg C) (uc_medeleg C)
                 MENVCFG_S (mword_of_int 0 : mword 64) usatp).
    iDestruct (u_frames_intro RS (uc_dqc C) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (u_rs_pins_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_tick _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_cfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 (u_rs_pins_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                 with "Hhs Hpriv Hms Hsc Hstval Hsepc HPC HnPC Hgpr
                       Hminstret Hmincr Hmcnt Hmicfg Hmcycle Hmtime Hmip
                       Hstvec Hmie Hmdl Hmedl Hmenv Hmste Hsste
                       Hmcen Hscen Hhpm
                       Hmisa Hmseccfg Hpma Hhtif Help Hsenv
                       Hsatp Htlb Hpcfg Hpaddr")
      as "[Hrw Hro]".
    (* ---- the step ---- *)
    iApply (swp_exec_step_waiting Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) RS
              wr ib emp%I
              u_disj Du_r_sub Du_w_sub
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              u_w_cy u_w_ti u_w_ip u_in_priv u_in_hart u_in_mc u_in_micfg
              u_w_mi u_in_mi u_w_ms u_in_ms u_w_PC u_in_PC u_in_nPC
              (eq_refl : register_lookup hart_state RS = HART_WAITING (wr, ib))
              with "Hcert Hresv Hrw Hro [//] [-]").
    iNext. iIntros (rs3) "(%rsP & %Hwp & %Hag) Hrw Hro Hresv _".
    iApply "Hcont".
    destruct Hwp as [Hstay | (rs' & mi2 & Hwk & ->)].
    - (* ---- STAY: the hart is still waiting, PC and nextPC untouched ---- *)
      assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
                register_beq r (R_bool minstret_increment) = false ->
                register_lookup r rs3 = register_lookup r RS)
        by (intros r H1 H2 H3; exact (wpin_stay RS rsP rs3 r Hstay Hag H1 H2 H3)).
      iApply (u_close_inv C pt Rut t mm usatp tlbvec pcfg paddr
                mcenv scenv hpm rs3
                (HART_WAITING (wr, ib)) ms_v va va'
                ltac:(exact Hwr)
                Hmsok
                ltac:(intros u Hu; discriminate Hu)
                ltac:(rewrite (T _ u_in_hart ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_priv ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mst ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_PC ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_nPC ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_stvec ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mie ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mdl ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_menv ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_satp ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_pcfg ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_paddr ltac:(u_notin_clock) eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_tlb ltac:(u_notin_clock) eq_refl); reflexivity)
                Htlbok Hwf
                with "Hpmpi Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm
                      Hrw Hro Hresv Hclaims Hbytes Hclose Hrut").
    - (* ---- WAKE: hart_state := ACTIVE, PC ticks to nextPC ---- *)
      assert (T : forall r : register, r ∈ u_Drw ∪ u_Dro -> r ∉ tk_clock3 ->
                register_beq r (R_bitvector_64 minstret) = false ->
                register_beq r (R_bitvector_64 PC) = false ->
                register_beq r hart_state = false ->
                register_beq r (R_bool minstret_increment) = false ->
                register_lookup r rs3 = register_lookup r RS)
        by (intros r H1 H2 H3 H4 H5 H6;
            exact (wpin_wake RS rs' rs3 mi2 r Hwk Hag H1 H2 H3 H4 H5 H6)).
      iApply (u_close_inv C pt Rut t mm usatp tlbvec pcfg paddr
                mcenv scenv hpm rs3
                (HART_ACTIVE tt) ms_v va' va'
                ltac:(exact I)
                Hmsok
                ltac:(intros u _; reflexivity)
                ltac:(exact (wpin_wake_hart RS rs' rs3 mi2 Hwk Hag))
                ltac:(rewrite (T _ u_in_priv ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mst ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (wpin_wake_pc RS rs' rs3 mi2 Hwk Hag); reflexivity)
                ltac:(rewrite (T _ u_in_nPC ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_stvec ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mie ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_mdl ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_menv ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_satp ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_pcfg ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_paddr ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                ltac:(rewrite (T _ u_in_tlb ltac:(u_notin_clock) eq_refl eq_refl eq_refl eq_refl); reflexivity)
                Htlbok Hwf
                with "Hpmpi Hmedl Hsenv Hmste Hsste Hmcen Hscen Hhpm
                      Hrw Hro Hresv Hclaims Hbytes Hclose Hrut").
  Qed.

End UserStepWaitArm.

(* ===================================================================== *)
(* §3 The step obligation, reduced to its ACTIVE-hart residue.            *)
(*                                                                       *)
(* The premise is [hw_config], not [minstret_inv]: there is no invariant  *)
(* left to open, and what the WAITING arm needs of the ambient machine is *)
(* the persistent misa / mseccfg / pma / htif / elp / senvcfg cells and   *)
(* the generation certificate -- all of which [hw_config] carries and     *)
(* every caller already holds.                                           *)
(* ===================================================================== *)
Section UserStepObligation.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  Theorem user_step_obligation_holds :
    hw_config -∗
    user_step_obligation_active C pt Rut -∗
    user_step_obligation C pt Rut.
  Proof.
    iIntros "#Hhw #Hactive".
    iIntros "!> Hinv Hk".
    iDestruct "Hinv" as (hs ms_v sc_v stval_v sepc_v va va' g)
      "(%Hhs & %Hms & %Hlock & Hregs & Hupt & Hcfg & Hrut)".
    destruct hs as [u | [wr ib]].
    - (* ACTIVE: hand off to the residue obligation *)
      destruct u. rewrite (Hlock tt eq_refl).
      iApply ("Hactive" with "[//] Hregs Hupt Hcfg Hrut Hk").
    - (* WAITING: the WRS stay/wake step, which re-enters [user_inv] on
         BOTH arms -- so the caller's additive conjunction is projected to
         its retire half once, here. *)
      simpl in Hhs.
      iApply (wp_user_step_waiting C pt Rut wr ib ms_v sc_v stval_v sepc_v
                va va' g Hhs Hms with "Hhw Hregs Hupt Hcfg Hrut [Hk]").
      iNext. iDestruct "Hk" as "[Hk _]". iExact "Hk".
  Qed.

  (* the capstone, over the ACTIVE residue only *)
  Corollary wp_user_exec_active :
    hw_config -∗
    user_step_obligation_active C pt Rut -∗
    user_inv C pt Rut -∗
    ▷ stvec_handler_wp C pt Rut -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hhw #Hactive Hinv Htrap".
    iApply (wp_user_exec with "[] Hinv Htrap").
    iApply (user_step_obligation_holds with "Hhw Hactive").
  Qed.

End UserStepObligation.

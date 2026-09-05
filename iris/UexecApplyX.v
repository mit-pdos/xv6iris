(* ===================================================================== *)
(* UexecApplyX.v -- UexecApply.v's round lemmas at the ENRICHED slot        *)
(* ([UexecRetExec.uslot_x]), for the trap loop that runs on the exec       *)
(* channel (lane E3b).                                                     *)
(*                                                                         *)
(* The loop holds [UexecRetExec.uexec_ret_x sc W] across a round.  Before   *)
(* the round it splits it ([uexec_ret_x_split]): the bundle -- owed only   *)
(* at an exec ecall -- goes DOWN to the kernel as uservec's pre row, and   *)
(* what is left is [UexecRet.uexec_ret_F uslot_x sc W], the plain-shaped   *)
(* return at the enriched slot.  After the round that half is re-keyed at  *)
(* the resume state exactly as UexecApply.v re-keys the plain one, with    *)
(* ONE more input: the kernel's exec result row (uservec's post row,       *)
(* [SpecUsertrap.ut_exec_out] unfolded), which decides the exec arm --     *)
(*   failure  -> the returning arm at [r = -1] (the round's own shape, so  *)
(*               [UexecApply.uexec_ret_F_returning] pays it);              *)
(*   slot     -> the new image's [uslot_x], as is;                         *)
(*   gap      -> the mint, as today.                                       *)
(* Fork and the transparent case are unchanged (the mint is at [uslot_x]). *)
(*                                                                         *)
(* Kept out of UexecApply.v so that file's cone stays clear of the         *)
(* enrichment; generic in the [uexecXG] class, so nothing fs-side enters   *)
(* here either.                                                            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import RegFile.
Require Import MinstretInv WireInv.
Require Import ProcDefs.
Require Import UserFrame.
Require Import UmodeRegs.
Require Import UexecWp.
Require Import ProcGeom.
Require Import UserPtTree.
Require Import UmodeText.
Require Import UserPerm.
Require Import UserExec.
Require Import UsysMemOk.
Require Import UexecSlot.
Require Import FdSlots.
Require Import UexecRet.
Require Import UexecRound.
Require Import TsoCtx.
Require Import UserFd.
Require Import UexecApply.
Require Import UexecRetExec.
Local Open Scope Z_scope.
Import Defs.

Section LoopApplyX.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : TsoCtx.CurCtx}.
  Context `{XG : uexecXG Σ}.

  (* [UexecApply.uexec_ret_round_slot] at the enriched slot, plus the exec
     result row.  The row is stated at the run projection of the trapped
     key, which is where the round is stated; [_of] below re-spells it at
     the record the round left, which is where uservec's post states it. *)
  Lemma uexec_ret_x_round_slot (sc : mword 64) (W W' : uvis) :
    length (uvis_tf W) = TFWORDS ->
    (sc <> uecall_scause -> uvis_fd W' = uvis_fd W) ->
    (sc = uecall_scause ->
       usys_fd_ok (usys_num (uvis_tf (uvis_run W))) (uvis_tf (uvis_run W))
         (uvis_tf W' !!! tf_arg_idx 0) (uvis_fd W) (uvis_fd W')) ->
    (sc = uecall_scause ->
       usys_pipe_ok (usys_num (uvis_tf (uvis_run W))) (uvis_tf (uvis_run W))
         (uvis_tf W' !!! tf_arg_idx 0) (uvis_M W) (uvis_M W')
         (uvis_fd W) (uvis_fd W')) ->
    uround_ok sc (uvis_tf (uvis_run W)) (uvis_M W) (uvis_perm W) (uvis_sz W)
      (uvis_cwd W)
      (uvis_tf W') (uvis_M W') (uvis_perm W') (uvis_sz W') (uvis_cwd W') ->
    (∀ W'' : uvis, uslot_x W'') -∗
    (⌜sc = uecall_scause /\ usys_num (uvis_tf (uvis_run W)) = USYS_exec⌝ -∗
       (⌜exists r : mword 64,
           uround_bump_ok (uvis_tf (uvis_run W)) (uvis_tf W') r
           /\ usys_mem_ok USYS_exec (uvis_tf (uvis_run W)) r
                (uvis_M W) (uvis_perm W) (uvis_sz W)
                (uvis_M W') (uvis_perm W') (uvis_sz W')
           /\ uvis_fd W' = uvis_fd W⌝
        ∨ uslot_x W'
        ∨ ⌜uvis_tf W' !!! tf_arg_idx 0 <> (mword_of_int (-1) : mword 64)⌝)) -∗
    uexec_ret_F uslot_x sc W -∗
    uslot_x W'.
  Proof.
    intros Hl Hfd Hfdrow Hpiperow Hr.
    iIntros "Hmk Hxo Hret".
    (* STEP A: the trapped key and its run projection are the same key *)
    iEval (rewrite (uexec_ret_F_run uslot_x uslot_x_key_cong sc W Hl)) in "Hret".
    destruct (decide (sc = uecall_scause)) as [Hec | Hne].
    - (* ---- ECALL ---- *)
      subst sc.
      rewrite /uexec_ret_F. cbv zeta.
      destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
        [| contradiction].
      destruct (uround_ok_ecall (uvis_tf (uvis_run W)) (uvis_M W) (uvis_M W')
                  (uvis_perm W) (uvis_perm W') (uvis_sz W) (uvis_sz W')
                  (uvis_cwd W) (uvis_cwd W') (uvis_tf W') Hr)
        as [[Hexec Hcwx] | [Hnex [r [Hb [Hm Hc]]]]].
      + (* exec: the kernel's answer decides *)
        destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_exit))
          as [Hx | _]; [ exfalso; rewrite Hexec in Hx; discriminate Hx | ].
        destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_fork))
          as [Hx | _]; [ exfalso; rewrite Hexec in Hx; discriminate Hx | ].
        iDestruct ("Hxo" with "[%]") as "[%Hfail | [Hslot | %Hgap]]";
          [ split; [reflexivity | exact Hexec] | | | ].
        * (* failed: the returning arm at [r = -1].  Its cwd row is the
             round's exec disjunct: exec inherits, so the field did not
             move, and exec is not chdir. *)
          destruct Hfail as (r & Hb & Hm & Hfd').
          rewrite <- Hexec in Hm.
          assert (Hne : USYS_exec <> USYS_chdir) by discriminate.
          assert (Hc : usys_cwd_ok (usys_num (uvis_tf (uvis_run W))) r
                         (uvis_cwd W) (uvis_cwd W')).
          { rewrite Hcwx. exact (usys_cwd_ok_refl_at _ USYS_exec r _ Hexec Hne). }
          iApply (uexec_ret_F_returning uslot_x uslot_x_key_cong W W' r Hl Hb Hm
                    (Hfdrow eq_refl) (Hpiperow eq_refl) Hc with "Hret").
        * (* loadable: the new image's slot *)
          iExact "Hslot".
        * (* the loadability gap: the mint *)
          iApply "Hmk".
      + destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_exit))
          as [Hx | _]; [ contradiction (Hnex Hx) | ].
        destruct (decide (usys_num (uvis_tf (uvis_run W)) = USYS_fork))
          as [_ | _].
        * (* fork: both arms are kernel mints -- [UexecApply]'s note *)
          iApply "Hmk".
        * iApply (uexec_ret_F_returning uslot_x uslot_x_key_cong W W' r Hl Hb Hm
                    (Hfdrow eq_refl) (Hpiperow eq_refl) Hc with "Hret").
    - (* ---- TRANSPARENT: interrupt, page fault, anything else ---- *)
      rewrite /uexec_ret_F.
      destruct (decide (sc = uecall_scause)) as [Hc | _]; [ contradiction | ].
      destruct (uround_ok_transparent sc (uvis_tf (uvis_run W))
                  (uvis_M W) (uvis_M W') (uvis_perm W) (uvis_perm W')
                  (uvis_sz W) (uvis_sz W') (uvis_cwd W) (uvis_cwd W')
                  (uvis_tf W') Hne Hr) as [[Hi1 Hi2] [HM [Hpi [Hsz Hcw]]]].
      iEval (rewrite (uslot_x_key_cong (uvis_run W) W'
                        (eq_sym Hi1) (eq_sym Hi2)
                        (eq_sym HM) (eq_sym Hpi) (eq_sym Hsz)
                        (eq_sym (Hfd Hne)) (eq_sym Hcw))) in "Hret".
      iExact "Hret".
  Qed.

  (* ...at the record the round left, keyed at the view the round actually
     left ([UexecApply.uexec_ret_round_slot_of]).  The row is spelled at the
     record's own projections: it is [SpecUsertrap.ut_exec_out] unfolded at
     [tf_of g (ret_pc sepc_v)], the trapframe uservec's post states it at. *)
  Lemma uexec_ret_x_round_slot_of (sc : mword 64) (W : uvis) (g : regfile)
      (sepc_v : mword 64) (U' : ustate) (fdv' : list fdstate) :
    length (uvis_tf W) = TFWORDS ->
    g = tf_resume_gpr0 (uvis_tf W) ->
    sepc_v = tf_w (uvis_tf W) tf_epc_idx ->
    (sc <> uecall_scause -> fdv' = uvis_fd W) ->
    (sc = uecall_scause ->
       usys_fd_ok (usys_num (tf_of g (ret_pc sepc_v))) (tf_of g (ret_pc sepc_v))
         (pv_tf (us_V U') !!! tf_arg_idx 0) (uvis_fd W) fdv') ->
    (sc = uecall_scause ->
       usys_pipe_ok (usys_num (tf_of g (ret_pc sepc_v))) (tf_of g (ret_pc sepc_v))
         (pv_tf (us_V U') !!! tf_arg_idx 0) (uvis_M W) (us_M U')
         (uvis_fd W) fdv') ->
    uround_ok sc (tf_of g (ret_pc sepc_v)) (uvis_M W) (uvis_perm W) (uvis_sz W)
      (uvis_cwd W)
      (pv_tf (us_V U')) (us_M U')
      (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))))
      (uint (pv_sz (us_V U'))) (pv_cwi (us_V U')) ->
    (∀ W'' : uvis, uslot_x W'') -∗
    (⌜sc = uecall_scause /\ usys_num (tf_of g (ret_pc sepc_v)) = USYS_exec⌝ -∗
       (⌜exists r : mword 64,
           uround_bump_ok (tf_of g (ret_pc sepc_v)) (pv_tf (us_V U')) r
           /\ usys_mem_ok USYS_exec (tf_of g (ret_pc sepc_v)) r
                (uvis_M W) (uvis_perm W) (uvis_sz W)
                (us_M U')
                (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))))
                (uint (pv_sz (us_V U')))
           /\ fdv' = uvis_fd W⌝
        ∨ uslot_x (uvis_of U' fdv')
        ∨ ⌜pv_tf (us_V U') !!! tf_arg_idx 0 <> (mword_of_int (-1) : mword 64)⌝)) -∗
    uexec_ret_F uslot_x sc W -∗
    uslot_x (uvis_of U' fdv').
  Proof.
    intros Hl -> -> Hfd Hfdrow Hpiperow Hr.
    exact (uexec_ret_x_round_slot sc W (uvis_of U' fdv') Hl Hfd Hfdrow
             Hpiperow Hr).
  Qed.

  (* [UexecApply.uslot_apply_loop] at the enriched slot: the seal comes off
     the hypothesis, and [uvb_x] is built row by row (it carries
     [gpr_file], so never [iFrame] -- claude-notes/optimization.md). *)
  Lemma uslot_x_apply_loop (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (HRut : forall pt' : uptd,
                ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                             (TsoCtx.own_context XI -∗ Rut pt'))
      (sz : Z) (fdv : list fdstate) (cw : Z) (W : uvis) (M : gmap Z (bv 8))
      (m : regfile) (ms_v sc_v stv_v sepc_v pc : mword 64) :
    loop_ok C pt ->
    usz_ok sz ->
    user_mstatus_ok ms_v ->
    uvis_perm W = perm_of (ud_um pt) sz ->
    uvis_M W = M ->
    uvis_sz W = sz ->
    uvis_fd W = fdv ->
    uvis_cwd W = cw ->
    tf_resume_gpr0 (uvis_tf W) = m ->
    tf_resume_pc (uvis_tf W) = pc ->
    uslot_x W -∗
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    u_regs (HART_ACTIVE tt) ms_v sc_v stv_v sepc_v pc pc m -∗
    user_ptm_inv_x pt sz M -∗
    Rfd fdv -∗
    user_cfg C -∗
    Rut pt -∗
    ▷ ukb_x C pt Rfd Rut sz (perm_of (ud_um pt) sz) fdv cw -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hlo Hsz Hms Hpi HM Hsw Hfd Hcw Hg Hpc.
    iIntros "Hs Hhw Hmi Hwi Hregs Hupt Hfrag Hcfg Hrut Hk".
    iEval (rewrite uslot_x_unfold) in "Hs".
    iEval (rewrite Hpi HM Hsw Hfd Hcw Hg Hpc) in "Hs".
    iDestruct (u_regs_uv_regs ms_v sc_v stv_v sepc_v pc m Hms with "Hregs")
      as "(Hur & Hg & Hpc)".
    iApply ("Hs" $! CID XI C pt Rfd Rut HRut
              with "[%] [%] [Hhw Hmi Hwi Hur Hg Hpc Hupt Hfrag Hcfg Hrut Hk]").
    - exact Hlo.
    - reflexivity.
    - rewrite /uvb_x /uvb_x_F.
      iSplitL "Hhw Hmi Hwi"; [ iApply (uv_amb_intro with "Hhw Hmi Hwi") | ].
      iSplitL "Hur"; [ iExact "Hur" | ].
      iSplitR; [ iPureIntro; exact Hsz | ].
      iSplitL "Hupt"; [ iExact "Hupt" | ].
      iSplitL "Hfrag"; [ iExact "Hfrag" | ].
      iSplitL "Hcfg"; [ iExact "Hcfg" | ].
      iSplitL "Hg"; [ iExact "Hg" | ].
      iSplitL "Hpc"; [ iExact "Hpc" | ].
      iSplitL "Hrut"; [ iExact "Hrut" | ].
      rewrite /ukont_x_F. iEval (rewrite /ukb_x) in "Hk". iExact "Hk".
  Qed.

End LoopApplyX.

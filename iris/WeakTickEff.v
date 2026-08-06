(** * WeakTickEff.v — [MinstretInv]'s CLOCK-TICK CONE, AT [exec_eff] (M4)

    [WeakEffSkel] §6b named two facts standing between the weak step assembly
    ([WeakEff.exec_eff_riscv_step_hart_active] / [WeakEffSkel]'s progress
    mirrors) and [WeakCert.wP_eff].  [WeakFetchEff] supplied the first (the
    fetch's own reduction).  THIS FILE IS THE SECOND: the [exec_eff] twin of
    [MinstretInv.exec_tick_clock], i.e. the whole six-lemma cone

      [should_inc_mcycle] -> [csr_name_write_callback "mip"] ->
      [external_interrupts_pending] -> [read_mip IncludePlatformInterrupts] ->
      [clint_dispatch false] -> [tick_clock]

    replayed with the trace threaded.  EVERY trace in the cone is [[]]: the
    tick is register-only from top to bottom (mcountinhibit / mcyclecfg / misa
    / mip / mtime / mtimecmp / stimecmp / menvcfg / cur_privilege reads, and
    mcycle / mtime / mip writes), and a register access is not a memory
    outcome, so [exec_eff] appends nothing.  Should any sub-step turn out to
    reach the CLINT as MMIO rather than as a register, the trace stays [[]]
    anyway — [exec_eff]'s device arms emit no effect at all.

    WHY IT MUST BE [[]] AND NOT [WeakEff.quiet_trace].  [WeakCert.wstep_conf_eff]
    fixes ONE trace [es] and then quantifies over [tick]: both the no-tick run
    and the tick run must produce THAT SAME [es].  A leaf produces its [es]
    from the instruction alone, so anything the tick branch contributed would
    make the two branches' traces differ and no leaf could ever close
    [wP_eff].  Only the EMPTY trace composes silently on both sides.

    This is also why [WeakEff]'s empty-memory detector
    ([exec_eff_quiet_of_empty]) is useless here: the strongest thing it can
    ever conclude is [quiet_trace], which ADMITS a zero-width access (invisible
    to [exec], but still a trace entry).  Only a syntactic bind-peel gives
    [[]] outright, and that is what this file does.

    METHOD.  Name-for-name replay of [MinstretInv.v] lines 92–281 under the
    [WeakEff] / [WeakEffSkel] substitution table ([exec_bind_Some] ->
    [exec_eff_bind_nil], [exec_bind0_Some] -> [exec_eff_bind0_nil],
    [exec_returnM] -> [exec_eff_returnM], [exec_read_reg] / [exec_write_reg]
    -> their [exec_eff_] twins, [exec_and_boolM_Some] / [exec_or_boolM_Some]
    -> §0's local twins).  The PURE regstate helpers
    ([MinstretInv.register_set_bv64_id] / [_overwrite] /
    [set_reg_mcycle_id] / [set_reg_mip_mip]) say nothing about the
    interpreter and are REUSED VERBATIM from [MinstretInv] rather than
    reproved.

    Sections:
      §0  the trivial twins the replay needs ([returnM], and/or, the
          three-tuple [if_some_bool])
      §1  the extension-enable probes the cone calls ([Ext_S], [Ext_Sstc])
      §2  the cone itself, ending in [exec_eff_tick_clock]
*)
From Stdlib Require Import FunctionalExtensionality.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: the
   space-separated [rewrite a b c] and [rewrite H /=] forms below are the SC
   originals'.  There is no Iris in this file. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import ExecCommon.
Require Import RiscvModelBytes DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff WeakEffSkel.
Require Import MinstretInv.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. The trivial twins

    [RiscvTryStep.exec_returnM], the two boolean connectives, and the
    three-tuple form of [MinstretInv.if_some_bool].  The last one is NOT a
    reproof of [if_some_bool]: [exec_eff]'s success is a THREE-tuple
    [Some (v, s, es)] = [Some ((v, s), es)], so [MinstretInv]'s pair-shaped
    statement does not even typecheck here.  Everything else in [MinstretInv]'s
    pure-helper block ([register_set_bv64_id], [register_set_bv64_overwrite],
    [set_reg_mcycle_id], [set_reg_mip_mip]) is about [regstate] alone and is
    used verbatim below. *)

Local Lemma wte_exec_eff_returnM {X} (x : X) s :
  exec_eff (returnM x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Local Lemma wte_exec_eff_and_boolM_nil (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (Defs.and_boolM l r) s
    = (if bl then exec_eff r sl else Some (false, sl, [])).
Proof.
  intro H. unfold Defs.and_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [reflexivity | apply exec_eff_returnm].
Qed.

Local Lemma wte_exec_eff_or_boolM_nil (l r : M bool) s bl sl :
  exec_eff l s = Some (bl, sl, []) ->
  exec_eff (Defs.or_boolM l r) s
    = (if bl then Some (true, sl, []) else exec_eff r sl).
Proof.
  intro H. unfold Defs.or_boolM. rewrite (exec_eff_bind_nil _ _ _ _ _ H).
  destruct bl; [apply exec_eff_returnm | reflexivity].
Qed.

(** The three-tuple [MinstretInv.if_some_bool]: fold the branch-neutral
    [or_boolM] result back into a single [Some] so the [erewrite] evars stay
    branch-independent. *)
Local Lemma wte_if_some_bool3 {A B} (c : bool) (x : A) (y : B) :
  (if c then Some (true, x, y) else Some (false, x, y)) = Some (c, x, y).
Proof. destruct c; reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. The extension-enable probes the cone calls

    [external_interrupts_pending] probes [Ext_S]; [clint_dispatch]'s Sstc gate
    probes [Ext_Sstc].  Both are [RiscvFetchExec]'s / [ExecCommon]'s scripts
    with the bind lemma renamed and [[]] appended — pure [misa] reads and
    [assert_exp'] discharges, no state change, no effect. *)

Local Lemma wte_exec_eff_hartSupports_S s :
  exec_eff (hartSupports Ext_S) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  apply wte_exec_eff_returnM.
Qed.

Local Lemma wte_exec_eff_hartSupports_Zicsr s :
  exec_eff (hartSupports Ext_Zicsr) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  apply wte_exec_eff_returnM.
Qed.

Local Lemma wte_exec_eff_hartSupports_Sstc s :
  exec_eff (hartSupports Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  apply wte_exec_eff_returnM.
Qed.

Local Lemma wte_exec_eff_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec_eff (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s, []).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  cbn match. apply wte_exec_eff_hartSupports_Zicsr.
Qed.

Local Lemma wte_exec_eff_currentlyEnabled_S s :
  exec_eff (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"),
            s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  cbn match.
  rewrite (wte_exec_eff_and_boolM_nil _ _ _ _ _ (wte_exec_eff_hartSupports_S s)).
  rewrite (wte_exec_eff_and_boolM_nil _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s)).
      apply wte_exec_eff_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")).
  - apply wte_exec_eff_rec_cE_Zicsr.
  - reflexivity.
Qed.

Local Lemma wte_exec_eff_currentlyEnabled_Sstc s :
  exec_eff (currentlyEnabled Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (wte_exec_eff_returnM eq_refl s)).
  cbn match. apply wte_exec_eff_hartSupports_Sstc.
Qed.

(* ====================================================================== *)
(** ** 2. THE CONE, at the empty trace

    [MinstretInv.v] lines 92–281, replayed.  Read each script against its SC
    original: the only edits are the lemma names and the [[]] in the
    statement. *)

(* ---- should_inc_mcycle is total ---- *)

Lemma exec_eff_should_inc_mcycle_Some (priv : Privilege) s :
  ∃ b : bool, exec_eff (should_inc_mcycle priv) s = Some (b, s, []).
Proof.
  unfold should_inc_mcycle, Defs.and_boolM.
  erewrite exec_eff_bind_nil.
  2:{ erewrite exec_eff_bind_nil.
      2:{ apply (exec_eff_read_reg mcountinhibit s). }
      apply exec_eff_returnm. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_eff_bind_nil.
    2:{ apply (exec_eff_read_reg mcyclecfg s). }
    eexists. apply exec_eff_returnm.
  - eexists. apply exec_eff_returnm.
Qed.

(* ---- the "mip changed" callback branch: reads only, state no-op ---- *)

Lemma exec_eff_csr_name_write_callback_mip (V : SailStdpp.Values.mword 64) s :
  exec_eff (csr_name_write_callback "mip" V) s = Some (tt, s, []).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_eff_bind_nil _ _ _ _ _
    (_ : exec_eff (csr_name_map_backwards "mip") s
         = Some (mword_of_int 0x344, s, []))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec_eff (returnM ?t) _ = _ => destruct t end.
  apply wte_exec_eff_returnM.
Qed.

Lemma exec_eff_external_interrupts_pending_Some (s : mstate) :
  ∃ v : SailStdpp.Values.mword 64,
    exec_eff (external_interrupts_pending tt) s = Some (v, s, []).
Proof.
  unfold external_interrupts_pending.
  erewrite exec_eff_bind_nil.
  2:{ apply (exec_eff_read_reg sig_meip s). }
  cbn beta.
  erewrite exec_eff_bind_nil.
  2:{ apply wte_exec_eff_currentlyEnabled_S. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_eff_bind_nil.
    2:{ apply (exec_eff_read_reg sig_seip s). }
    cbn beta. eexists. apply wte_exec_eff_returnM.
  - erewrite exec_eff_bind_nil.
    2:{ apply wte_exec_eff_returnM. }
    cbn beta. eexists. apply wte_exec_eff_returnM.
Qed.

Lemma exec_eff_read_mip_include_Some (s : mstate) :
  ∃ v : SailStdpp.Values.mword 64,
    exec_eff (read_mip IncludePlatformInterrupts) s = Some (v, s, []).
Proof.
  unfold read_mip.
  erewrite exec_eff_bind_nil.
  2:{ apply (exec_eff_read_reg mip s). }
  cbn beta.
  destruct (exec_eff_external_interrupts_pending_Some s) as [w He].
  erewrite exec_eff_bind_nil.
  2:{ exact He. }
  cbn beta. eexists. apply wte_exec_eff_returnM.
Qed.

(* ---- clint_dispatch false: total, writes exactly mip, emits nothing ---- *)

Lemma exec_eff_clint_dispatch_false (s : mstate) :
  ∃ p : SailStdpp.Values.mword 64,
    exec_eff (clint_dispatch false) s = Some (tt, set_reg s mip p, []).
Proof.
  unfold clint_dispatch.
  erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mip s). }
  cbn beta.
  erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mip s). }
  cbn beta.
  erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mtimecmp s). }
  cbn beta.
  erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mtime s). }
  cbn beta.
  (* head = (write mip MTIP) >> (Sstc && menvcfg.STCE gate) *)
  erewrite exec_eff_bind_nil.
  2:{ erewrite exec_eff_bind0_nil. 2:{ apply exec_eff_write_reg. }
      erewrite wte_exec_eff_and_boolM_nil.
      2:{ apply wte_exec_eff_currentlyEnabled_Sstc. }
      cbn match.
      erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg menvcfg _). }
      cbn beta. apply wte_exec_eff_returnM. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - (* STCE live: mip.STIP write *)
    (* head = ((STIP-write >> print-nop) >> or_boolM (mip changed?)) *)
    erewrite exec_eff_bind_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind0_nil.
            2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mip _). }
                cbn beta.
                erewrite exec_eff_bind_nil.
                2:{ apply (exec_eff_read_reg stimecmp _). }
                cbn beta.
                erewrite exec_eff_bind_nil.
                2:{ apply (exec_eff_read_reg mtime _). }
                cbn beta. apply exec_eff_write_reg. }
            apply exec_eff_returnm. }
        erewrite wte_exec_eff_or_boolM_nil.
        2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mip _). }
            cbn beta. apply wte_exec_eff_returnM. }
        rewrite wte_exec_eff_returnM. apply wte_if_some_bool3. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + (* changed: read_mip + callback, state no-op *)
      match goal with
      |- context [ exec_eff (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_eff_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_eff_bind_nil. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_eff_csr_name_write_callback_mip.
      rewrite set_reg_mip_mip. eexists. reflexivity.
    + rewrite wte_exec_eff_returnM.
      rewrite set_reg_mip_mip. eexists. reflexivity.
  - (* STCE dead: single mip write *)
    erewrite exec_eff_bind_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind0_nil.
            2:{ apply wte_exec_eff_returnM. }
            apply exec_eff_returnm. }
        erewrite wte_exec_eff_or_boolM_nil.
        2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mip _). }
            cbn beta. apply wte_exec_eff_returnM. }
        rewrite wte_exec_eff_returnM. apply wte_if_some_bool3. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + match goal with
      |- context [ exec_eff (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_eff_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_eff_bind_nil. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_eff_csr_name_write_callback_mip.
      eexists. reflexivity.
    + rewrite wte_exec_eff_returnM.
      eexists. reflexivity.
Qed.

(* ---- tick_clock: total, writes exactly {mcycle, mtime, mip}, trace [] ---- *)

(** THE DELIVERABLE.  [MinstretInv.exec_tick_clock] with [[]] appended: the
    clock tick succeeds at ANY state, writes exactly the three-register
    [set_reg] tower, and contributes NOTHING to the effect trace — which is
    what lets [WeakCert.wstep_conf_eff]'s single [es] serve both the tick and
    the no-tick branch. *)
Lemma exec_eff_tick_clock (s : mstate) :
  exists (c t p : SailStdpp.Values.mword 64),
    exec_eff (tick_clock tt) s
      = Some (tt, set_reg (set_reg (set_reg s mcycle c) mtime t) mip p, []).
Proof.
  unfold tick_clock.
  erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg cur_privilege s). }
  cbn beta.
  destruct (exec_eff_should_inc_mcycle_Some
              (register_lookup cur_privilege s.(sregs)) s) as [bc Hsic].
  erewrite exec_eff_bind_nil. 2:{ exact Hsic. }
  cbn beta.
  destruct bc.
  - (* mcycle += 1; head = (mcycle-inc >> read mtime) *)
    erewrite exec_eff_bind_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg mcycle s). }
            cbn beta. apply exec_eff_write_reg. }
        apply (exec_eff_read_reg mtime _). }
    cbn beta.
    (* write mtime >> clint_dispatch false *)
    erewrite exec_eff_bind0_nil. 2:{ apply exec_eff_write_reg. }
    match goal with
    |- context [ exec_eff (clint_dispatch false) ?st = _ ] =>
      destruct (exec_eff_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd. do 3 eexists. reflexivity.
  - (* mcycle untouched: insert the identity set *)
    erewrite exec_eff_bind_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ apply wte_exec_eff_returnM. }
        apply (exec_eff_read_reg mtime _). }
    cbn beta.
    erewrite exec_eff_bind0_nil. 2:{ apply exec_eff_write_reg. }
    match goal with
    |- context [ exec_eff (clint_dispatch false) ?st = _ ] =>
      destruct (exec_eff_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd.
    exists (register_lookup mcycle s.(sregs)).
    rewrite (set_reg_mcycle_id s). do 2 eexists. reflexivity.
Qed.

Print Assumptions exec_eff_tick_clock.

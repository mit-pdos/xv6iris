(** * WeakPmpEff.v — the [exec_eff] TWIN OF THE PMP-CHECK CONE (M4 batch 0)

    WHAT THIS IS.  [WeakCert.exec_eff] is [RiscvExec.exec] arm for arm, with a
    [list weff] threaded; [WeakEffSkel.execR_eff] is the same for
    [RiscvTryStep.execR].  Everything a leaf's [WeakCert.wP_eff] obligation
    reaches through the fetch and the load/store path eventually runs
    [pmpCheck], so the PMP cone needs its instrumented twin as well.  This file
    is that twin, and NOTHING ELSE: the SC scripts of [RiscvTryStep]'s and
    [RiscvFetchExec]'s PMP lemmas, replayed with [WeakEff]'s and
    [WeakEffSkel]'s composition kit in place of [RiscvExec]'s and
    [RiscvTryStep]'s.  No new mathematical argument appears here — the pure
    side conditions ([RiscvTryStep.pmpRangeMatch_cell],
    [RiscvTryStep.divide4_factor], [RiscvTryStep.divide4_factor_plus]) are
    REUSED VERBATIM, because they say nothing about the interpreter.

    WHY EVERY TRACE HERE IS LITERALLY [[]].  The whole PMP cone is
    register-only: [pmpReadAddrReg] reads [pmpcfg]/[pmpaddr], [pmpMatchAddr]
    and [pmpRangeMatch] are pure, [pmpCheckRWX] is a pure field test, and the
    [foreach] over the 64 entries neither reads nor writes memory nor issues a
    barrier.  So each lemma's conclusion carries the EMPTY trace, not
    [WeakEff.quiet_trace] (which the empty-memory detector
    [WeakEff.exec_eff_quiet_of_empty] produces).  The difference matters and is
    not cosmetic: [quiet_trace] ADMITS a zero-width write, and a zero-width
    write still APPENDS a (byte-less) message to [wm_log], so
    [WeakEff.wcert_store_gen] / [_load_gen] / [_amo_aq_gen] — which need
    [nowrite_trace] — cannot consume it (see the "zero-width residue" bullet of
    [claude-notes/projects/weak-memory.md]).  A syntactic bind-peel like the one
    below never meets the zero-width arms at all: they simply are not in the
    program.  Hence [[]] outright, discharged by the same script that produces
    the SC fact.

    THE METHOD IS A NAME SWAP.  [RiscvExec.exec_bind_Some] becomes
    [WeakEff.exec_eff_bind_nil], [RiscvTryStep.execR_bind] becomes
    [WeakEffSkel.execR_eff_bind_eq], [RiscvTryStep.execR_liftR_seq] becomes
    [WeakEffSkel.execR_eff_liftR_seq], and so on; the two trivial [returnM]
    twins that [WeakEff] does not state are stated here as local lemmas.

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a named
    lemma over a bind spine, exactly as the SC originals are.  (The two
    [vm_compute]s are on closed [Z] literals: [sys_pmp_count] and
    [uint (to_bits 64 4)].) *)
(* [ZArith] for [Zrem_divides], which §5's alignment side condition needs and
   which [stdpp] does not re-export. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
(* [proofmode] is required for its SSREFLECT tactic language ONLY: every
   [rewrite a b c] below is the space-separated ssreflect form, as in the SC
   originals this file mirrors.  There is no Iris in this file. *)
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WeakEffSkel.

Local Open Scope Z_scope.

(* [SailStdpp.Values] must NOT be [Import]ed here — it leaks typeclass
   instances (see [claude-notes/durable-notes.md]) — so the two names this
   file borrows from it are spelled through local abbreviations. *)
Local Notation vec_access_dec := SailStdpp.Values.vec_access_dec.

(* ====================================================================== *)
(** ** 0. The two trivial twins [WeakEff] / [WeakEffSkel] do not state

    [returnM] is [Defs.returnm] under a definitional wrapper, and the SC
    scripts name both forms; likewise [RiscvTryStep.execR_returnm_fwd] is
    [execR_eff_returnR] stated at [Defs.returnm] rather than [Defs.returnR].
    Both are [reflexivity]. *)

Local Lemma wpe_exec_eff_returnM {X} (x : X) s :
  exec_eff (returnM x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Local Lemma wpe_execR_eff_returnm_fwd {R X} (x : X) s :
  execR_eff (Defs.returnm x : Defs.monadR R exception X) s = Some (inr x, s, []).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. The two [foreach_ZM_up] loop invariants, instrumented

    [RiscvTryStep.execR_foreach_ZM_up'_allow] / [_allow] and
    [execR_foreach_ZM_up'_const] / [_const], with every
    [execR (…) s = Some (…, s)] read as [execR_eff (…) s = Some (…, s, [])].
    A body that is register-only at every index makes the whole bounded loop
    register-only, so the loop's trace is [[]] as well. *)

Lemma execR_eff_foreach_ZM_up'_allow {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (r : R) :
  (forall i v, execR_eff (body i v) s = Some (inr v, s, [])
            \/ execR_eff (body i v) s = Some (inl r, s, [])) ->
  forall (n : nat) (from : Z) (vars : Vars),
    execR_eff (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inr vars, s, [])
    \/ execR_eff (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inl r, s, []).
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - cbn [Defs.foreach_ZM_up']. destruct (from <=? to); left;
      apply wpe_execR_eff_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + rewrite (Defs.unroll_foreach_ZM_up' _ _ from to step n vars body Hle).
      destruct (Hbody from vars) as [Hb|Hb].
      * rewrite (execR_eff_bind_nil _ _ _ _ _ Hb). exact (IH (from + step) vars).
      * right. rewrite execR_eff_bind_eq Hb. reflexivity.
    + cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false by (symmetry; apply Z.leb_gt; lia).
      left. apply wpe_execR_eff_returnm_fwd.
Qed.

Lemma execR_eff_foreach_ZM_up_allow {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) (r : R) :
  (forall i v, execR_eff (body i v) s = Some (inr v, s, [])
            \/ execR_eff (body i v) s = Some (inl r, s, [])) ->
  execR_eff (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inr vars, s, [])
  \/ execR_eff (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inl r, s, []).
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply execR_eff_foreach_ZM_up'_allow; exact Hbody.
Qed.

Lemma execR_eff_foreach_ZM_up'_const {R Vars} (to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars) (s : mstate) :
  (forall i v, execR_eff (body i v) s = Some (inr v, s, [])) ->
  forall (n : nat) (from : Z) (vars : Vars),
    execR_eff (Defs.foreach_ZM_up' (E := (R + exception)%type) from to step n vars body)
          s = Some (inr vars, s, []).
Proof.
  intros Hbody. induction n as [|n IH]; intros from vars.
  - cbn [Defs.foreach_ZM_up']. destruct (from <=? to); apply wpe_execR_eff_returnm_fwd.
  - destruct (Z.leb_spec from to) as [Hle|Hgt].
    + rewrite (Defs.unroll_foreach_ZM_up' _ _ from to step n vars body Hle).
      rewrite (execR_eff_bind_nil _ _ _ _ _ (Hbody from vars)).
      exact (IH (from + step) vars).
    + cbn [Defs.foreach_ZM_up'].
      replace (from <=? to) with false.
      * apply wpe_execR_eff_returnm_fwd.
      * symmetry. apply Z.leb_gt. lia.
Qed.

Lemma execR_eff_foreach_ZM_up_const {R Vars} (from to step : Z)
    (body : forall (z : Z), Vars -> Defs.monadR R exception Vars)
    (s : mstate) (vars : Vars) :
  (forall i v, execR_eff (body i v) s = Some (inr v, s, [])) ->
  execR_eff (Defs.foreach_ZM_up (E := (R + exception)%type) from to step vars body)
        s = Some (inr vars, s, []).
Proof.
  intros Hbody. unfold Defs.foreach_ZM_up.
  apply execR_eff_foreach_ZM_up'_const; exact Hbody.
Qed.

(* ====================================================================== *)
(** ** 2. The leaf lemmas of the PMP body

    [RiscvTryStep.exec_pmpReadAddrReg_ex] and [exec_pmpMatchAddr_OFF],
    mirrored.  Both are two register reads and a [returnM]. *)

Lemma exec_eff_pmpReadAddrReg_ex (n : Z) s :
  exists v, exec_eff (pmpReadAddrReg n) s = Some (v, s, []).
Proof.
  unfold pmpReadAddrReg. cbn zeta. eexists.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)). cbn beta.
  apply wpe_exec_eff_returnM.
Qed.

Lemma exec_eff_pmpMatchAddr_OFF (pa : physaddr) (width : SailStdpp.Values.mword 64)
    (ent : SailStdpp.Values.mword 8)
    (pmpaddr prev : SailStdpp.Values.mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = OFF ->
  exec_eff (pmpMatchAddr pa width ent pmpaddr prev) s = Some (PMP_NoMatch, s, []).
Proof.
  intro HOFF. destruct pa as [addr0]. unfold pmpMatchAddr. cbn zeta.
  rewrite HOFF. cbn match. apply wpe_exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 3. The all-OFF reduction

    [RiscvTryStep.exec_pmpCheck_machine_none], mirrored through §1's
    [_const] invariant. *)

Lemma exec_eff_pmpCheck_machine_none
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  exec_eff (pmpCheck addr width access Machine) s = Some (None, s, []).
Proof.
  intro HpmpOFF.
  unfold pmpCheck.
  rewrite exec_eff_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_eff_bind0_eq.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR_eff (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inr vars, s, []))
  end.
  { apply execR_eff_foreach_ZM_up_const. intros i v. destruct v. cbn beta.
    destruct (Z.gtb i 0) eqn:Hi; cbn match.
    - destruct (exec_eff_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpv). cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_eff_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _
                 (exec_eff_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_eff_returnR.
    - rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match. cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_eff_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _
                 (exec_eff_pmpMatchAddr_OFF _ _ _ _ _ s (HpmpOFF i))). cbn beta.
      cbn match. apply execR_eff_returnR. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. The cell dichotomy, and the unlocked-M-mode reduction

    [RiscvTryStep.exec_pmpMatchAddr_machine_cell] and
    [exec_pmpCheck_machine_unlocked], mirrored.  The PURE side conditions —
    [pmpRangeMatch_cell], [divide4_factor], [divide4_factor_plus] — are
    [RiscvTryStep]'s, reused verbatim: they are statements about
    [pmpRangeMatch], not about an interpreter, so there is nothing to
    instrument. *)

Lemma exec_eff_pmpMatchAddr_machine_cell (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (paddr prev : SailStdpp.Values.mword 64) s :
  uint (bits_of_physaddr pa) mod 4 + uint wbv <= 4 ->
  exec_eff (pmpMatchAddr pa wbv ent paddr prev) s = Some (PMP_NoMatch, s, [])
  \/ exec_eff (pmpMatchAddr pa wbv ent paddr prev) s = Some (PMP_Match, s, []).
Proof.
  intros Hfit. destruct pa as [a]. cbn in Hfit.
  unfold pmpMatchAddr. cbn zeta.
  destruct (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)).
  - (* OFF *) left. apply wpe_exec_eff_returnM.
  - (* TOR *)
    destruct (zopz0zKzJ_u prev paddr).
    + left. apply wpe_exec_eff_returnM.
    + destruct (pmpRangeMatch_cell (Z.mul (uint prev) 4) (Z.mul (uint paddr) 4)
                  (uint a) (uint wbv)
                  (divide4_factor (uint prev)) (divide4_factor (uint paddr)) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply wpe_exec_eff_returnM.
  - (* NA4: the grain assertion holds (sys_pmp_grain = 0 < 1). *)
    destruct (pmpRangeMatch_cell (Z.mul (uint paddr) 4) (Z.add (Z.mul (uint paddr) 4) 4)
                  (uint a) (uint wbv)
                  (divide4_factor (uint paddr)) (divide4_factor_plus (uint paddr)) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply wpe_exec_eff_returnM.
  - (* NAPOT *)
    destruct (pmpRangeMatch_cell
                  (Z.mul (uint (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1))))) 4)
                  (Z.mul (Z.add (Z.add (uint (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1)))))
                                       (uint (xor_vec paddr (add_vec_int paddr 1)))) 1) 4)
                  (uint a) (uint wbv)
                  (divide4_factor _) (divide4_factor _) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; apply wpe_exec_eff_returnM.
Qed.

Lemma exec_eff_pmpCheck_machine_unlocked
    (addr : physaddr) (width : Z) (access : MemoryAccessType mem_payload) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  (forall ent, exists b, exec_eff (pmpCheckRWX ent access) s = Some (b, s, [])) ->
  uint (bits_of_physaddr addr) mod 4 + uint (to_bits 64 width) <= 4 ->
  exec_eff (pmpCheck addr width access Machine) s = Some (None, s, []).
Proof.
  intros HL Hrwx Hfit.
  unfold pmpCheck.
  rewrite exec_eff_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_eff_bind0_eq.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hbody : forall i v,
                 execR_eff (body i v) s = Some (inr v, s, [])
              \/ execR_eff (body i v) s
                   = Some (inl (None : option ExceptionType), s, []))
  end.
  { intros i v. destruct v. cbn beta.
    destruct (Z.gtb i 0) eqn:Hi; cbn match.
    - destruct (exec_eff_pmpReadAddrReg_ex (i - 1) s) as [pv Hpv].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hpv). cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_eff_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      destruct (exec_eff_pmpMatchAddr_machine_cell addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) w2 pv s Hfit)
        as [Hm|Hm].
      + left. rewrite (execR_eff_liftR_seq _ _ _ _ _ Hm). cbn beta.
        cbn match. apply execR_eff_returnR.
      + right. rewrite (execR_eff_liftR_seq _ _ _ _ _ Hm). cbn beta. cbn match.
        rewrite execR_eff_bind_eq. unfold Defs.or_boolM.
        rewrite execR_eff_bind_eq. rewrite execR_eff_liftR.
        destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) as [b Hb].
        rewrite Hb. cbn match.
        destruct b; [reflexivity | rewrite (HL i); reflexivity].
    - rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match. cbn beta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
      destruct (exec_eff_pmpReadAddrReg_ex i s) as [w2 Hw2].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hw2). cbn beta.
      destruct (exec_eff_pmpMatchAddr_machine_cell addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) w2 (zeros' 64) s Hfit)
        as [Hm|Hm].
      + left. rewrite (execR_eff_liftR_seq _ _ _ _ _ Hm). cbn beta.
        cbn match. apply execR_eff_returnR.
      + right. rewrite (execR_eff_liftR_seq _ _ _ _ _ Hm). cbn beta. cbn match.
        rewrite execR_eff_bind_eq. unfold Defs.or_boolM.
        rewrite execR_eff_bind_eq. rewrite execR_eff_liftR.
        destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) as [b Hb].
        rewrite Hb. cbn match.
        destruct b; [reflexivity | rewrite (HL i); reflexivity]. }
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      destruct (execR_eff_foreach_ZM_up_allow F T S body s vars _ Hbody) as [Hloop|Hloop]
  end;
  rewrite Hloop; cbn match; reflexivity.
Qed.

(* ====================================================================== *)
(** ** 5. The fetch-shaped corollary

    [RiscvFetchExec.exec_pmpCheck_machine_unlocked_ifetch4], mirrored.  A
    4-byte instruction fetch at a 4-aligned pc fits in one aligned 4-byte grain
    cell, so unlocked entries suffice; [pmpCheckRWX] at [InstructionFetch] is a
    single field test, so its [exec_eff] is a [returnM] with an empty trace. *)

Lemma exec_eff_pmpCheck_machine_unlocked_ifetch4
    (addr : SailStdpp.Values.mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  exec_eff (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []).
Proof.
  intros HL Halign.
  apply exec_eff_pmpCheck_machine_unlocked;
    [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
  rewrite Hk. replace (4 * k) with (k * 4) by lia. rewrite Z_mod_mult. lia.
Qed.

Print Assumptions exec_eff_pmpCheck_machine_unlocked_ifetch4.

(** * WeakPmpTorEff.v — the [exec_eff] TWIN OF THE PMP TOR-ENTRY-0 GRANT

    [WeakPmpEff.v] mirrors the ALL-OFF / UNLOCKED arms of the PMP cone at
    [WeakCert.exec_eff]: those are the arms a leaf needs while PMP is still
    switched off.  Once [start()] has WRITTEN pmpaddr0/pmpcfg0 — a TOR entry
    covering all of RAM — every later data access is granted by the
    entry-0 full-match arm instead, i.e. by
    [WpMmodeLeafBase.exec_pmpCheck_machine_tor0].  THIS FILE IS THAT ARM'S
    [exec_eff] TWIN, and nothing else.

    THE METHOD IS THE NAME SWAP [WeakPmpEff] established, applied to the SC
    scripts of [WpMmodeLeafBase]'s TOR block:
    [RiscvExec.exec_bind_Some] → [WeakEff.exec_eff_bind_nil],
    [RiscvTryStep.execR_bind] → [WeakEffSkel.execR_eff_bind_eq],
    [execR_bind0] → [execR_eff_bind0_eq],
    [execR_liftR_seq] → [execR_eff_liftR_seq],
    [execR_liftR] → [execR_eff_liftR],
    [execR_returnR] → [execR_eff_returnR],
    [exec_returnM] → the local [returnM] twin below,
    [exec_read_reg] → [WeakEff.exec_eff_read_reg],
    and the [foreach] unrolled by [Defs.unroll_foreach_ZM_up'] exactly as in
    SC.  No new mathematical argument appears: the PURE pieces —
    [WpMmodeLeafBase.pmpRangeMatch_full] and the predicate
    [WpMmodeLeafBase.pmp_tor0_grants] itself — are REUSED VERBATIM, because
    they say nothing about the interpreter.

    WHY EVERY TRACE HERE IS LITERALLY [[]].  Same reason as in [WeakPmpEff]:
    the whole PMP cone is register-only ([pmpReadAddrReg] reads
    pmpcfg/pmpaddr, [pmpMatchAddr]/[pmpRangeMatch] are pure, [pmpCheckRWX] is
    a field test), so the empty trace is the honest conclusion — NOT
    [WeakEff.quiet_trace], which admits a zero-width write and would then be
    unusable by the [nowrite_trace]-demanding certificates.

    NOTHING HERE REDUCES A MODEL FUNCTION BY COMPUTATION: every step is a
    named lemma over a bind spine.  (The [vm_compute]s are on closed [Z]
    literals: [sys_pmp_grain] and [sys_pmp_count].) *)
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
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WeakEffSkel.
(* THE PURE SIDE, REUSED: [pmpRangeMatch_full] and [pmp_tor0_grants].  Both
   are statements about [pmpRangeMatch] / the pmpcfg entry, not about an
   interpreter, so neither is restated here. *)
Require Import WpMmodeLeafBase.

Local Open Scope Z_scope.

(* [SailStdpp.Values] must NOT be [Import]ed here — it leaks typeclass
   instances (see [claude-notes/durable-notes.md]) — so the names this file
   borrows from it are spelled through local abbreviations / qualified. *)
Local Notation vec_access_dec := SailStdpp.Values.vec_access_dec.

(* ====================================================================== *)
(** ** 0. The two trivial twins [WeakEff] / [WeakEffSkel] do not state

    Exactly [WeakPmpEff] §0's pair, restated here (they are [Local] there).
    Both are [reflexivity]. *)

Local Lemma wpte_exec_eff_returnM {X} (x : X) s :
  exec_eff (returnM x) s = Some (x, s, []).
Proof. reflexivity. Qed.

Local Lemma wpte_execR_eff_returnm_fwd {R X} (x : X) s :
  execR_eff (Defs.returnm x : Defs.monadR R exception X) s = Some (inr x, s, []).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 1. [pmpReadAddrReg], AT ITS EXACT VALUE

    [WeakPmpEff] states only the ∃-form ([exec_eff_pmpReadAddrReg_ex]), which
    is all the all-OFF arm needs — that arm never looks at what the address
    register holds.  The TOR arm DOES: the grant is about [pmpaddr0 * 4], so
    the read must be pinned to [vec_access_dec (register_lookup pmpaddr_n …)].
    This is [WpMmodeLeafBase.exec_pmpReadAddrReg], mirrored. *)

Lemma exec_eff_pmpReadAddrReg (n : Z) s :
  exec_eff (pmpReadAddrReg n) s
  = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s, []).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)). cbn beta.
  replace (Z.geb sys_pmp_grain 2) with false by (vm_compute; reflexivity).
  replace (Z.geb sys_pmp_grain 1) with false by (vm_compute; reflexivity).
  cbn [andb]. apply wpte_exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 2. The entry-0 TOR FULL MATCH

    [WpMmodeLeafBase.exec_pmpMatchAddr_tor0_match], mirrored: the access
    [a, a+w) lying fully inside [0, uint paddr * 4) is a (full) [PMP_Match],
    with no state change and no trace.  The pure step is
    [WpMmodeLeafBase.pmpRangeMatch_full], reused verbatim. *)

Lemma exec_eff_pmpMatchAddr_tor0_match (a : SailStdpp.Values.mword 64)
    (wbv : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (paddr : SailStdpp.Values.mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  0 < uint wbv ->
  uint a + uint wbv <= uint paddr * 4 ->
  exec_eff (pmpMatchAddr (Physaddr a) wbv ent paddr (zeros' 64)) s
    = Some (PMP_Match, s, []).
Proof.
  intros HA Hw Hin.
  pose proof (bv_unsigned_in_range _ a) as [Ha0 _].
  rewrite <- uint_unsigned in Ha0.
  assert (Hp0 : 0 < uint paddr) by lia.
  unfold pmpMatchAddr. cbn zeta. rewrite HA.
  assert (Hz0 : uint (zeros' 64 : SailStdpp.Values.mword 64) = 0)
    by (vm_compute; reflexivity).
  replace (zopz0zKzJ_u (zeros' 64) paddr) with false.
  2:{ symmetry. unfold zopz0zKzJ_u. rewrite Hz0. rewrite Z.geb_leb.
      apply Z.leb_gt. lia. }
  rewrite Hz0.
  rewrite (pmpRangeMatch_full (Z.mul 0 4) (Z.mul (uint paddr) 4) (uint a)
             (uint wbv) ltac:(lia) Hw ltac:(lia)).
  apply wpte_exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 3. THE REDUCTION

    [WpMmodeLeafBase.exec_pmpCheck_machine_tor0], mirrored.  In Machine mode,
    [pmp_tor0_grants] of the CURRENT pmpcfg_n / pmpaddr_n register values
    makes [pmpCheck] grant the access: the loop's FIRST iteration full-matches
    entry 0, which (M-mode, unlocked) early-returns [None] (allow) before any
    later entry is consulted.

    Its two auxiliary premises are the SC ones VERBATIM: the [pmpCheckRWX]
    fact (a field test, so [eexists]+[returnM] at every call site) and the
    width round-trip [uint (to_bits 64 width) = width] (a [vm_compute] at
    every call site). *)

Lemma exec_eff_pmpCheck_machine_tor0
    (addr : SailStdpp.Values.mword 64) (width : Z)
    (access : MemoryAccessType mem_payload) s :
  pmp_tor0_grants (register_lookup pmpcfg_n s.(sregs))
                  (register_lookup pmpaddr_n s.(sregs)) addr width ->
  (forall ent, exists b, exec_eff (pmpCheckRWX ent access) s = Some (b, s, [])) ->
  uint (to_bits 64 width : SailStdpp.Values.mword 64) = width ->
  exec_eff (pmpCheck (Physaddr addr) width access Machine) s
    = Some (None, s, []).
Proof.
  intros (HA & HL & Hw & Hin) Hrwx Hwidth.
  unfold pmpCheck.
  rewrite exec_eff_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity).
  cbn zeta.
  rewrite execR_eff_bind0_eq.
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hbody0 : execR_eff (body 0 tt) s
                       = Some (inl (None : option ExceptionType), s, []))
  end.
  { assert (HW1 : 0 < uint (to_bits 64 width : SailStdpp.Values.mword 64))
      by (rewrite Hwidth; exact Hw).
    assert (HW2 : uint addr + uint (to_bits 64 width : SailStdpp.Values.mword 64)
                  <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)
      by (rewrite Hwidth; exact Hin).
    cbn beta.
    change (Z.gtb 0 0) with false. cbn match.
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match. cbn beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
    cbn beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_pmpReadAddrReg 0 s)).
    cbn beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (exec_eff_pmpMatchAddr_tor0_match addr (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) s
                  HA HW1 HW2)).
    cbn beta. cbn match.
    rewrite execR_eff_bind_eq. unfold Defs.or_boolM.
    rewrite execR_eff_bind_eq. rewrite execR_eff_liftR.
    destruct (Hrwx (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0))
      as [b Hb].
    rewrite Hb. cbn match.
    destruct b; [reflexivity | rewrite HL; reflexivity]. }
  match goal with
  | |- context[Defs.foreach_ZM_up ?F ?T ?S ?vars ?body] =>
      assert (Hloop : execR_eff (Defs.foreach_ZM_up F T S vars body) s
                      = Some (inl (None : option ExceptionType), s, []))
  end.
  { unfold Defs.foreach_ZM_up.
    assert (Hle : 0 <= sys_pmp_count - 1) by (unfold sys_pmp_count; lia).
    rewrite (Defs.unroll_foreach_ZM_up' _ _ 0 (sys_pmp_count - 1) 1 _ tt _ Hle).
    rewrite execR_eff_bind_eq. rewrite Hbody0. reflexivity. }
  rewrite Hloop. cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_pmpCheck_machine_tor0.

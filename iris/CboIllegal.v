(* CboIllegal.v -- U-mode cache-block ops (Zicbom) are illegal under the xv6
   config.  ZICBOM (CBO_CLEAN/FLUSH/INVAL) is gated on menvcfg/senvcfg enable
   bits; xv6 pins menvcfg = MENVCFG_S (all Zicbo* enable bits 0) and senvcfg =
   0, so in User mode each variant traps to Illegal_Instruction, state-
   preserving.  CLEAN/FLUSH short-circuit on menvcfg.CBCFE=0 inside
   feature_enabled_for_priv; INVAL sees menvcfg.CBIE=00 (CBIE_ILLEGAL) inside
   cbop_priv_check.  These feed the config-aware run producer of
   ustep_illegal_run_st. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGpr.
Local Open Scope Z_scope.
Import Defs.

(* read_senvcfg is total and state-preserving (value irrelevant when a
   later check short-circuits before consulting it). *)
Lemma exec_read_senvcfg_any' s : exists v : mword 64, exec (read_senvcfg tt) s = Some (v, s).
Proof.
  unfold read_senvcfg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
  eexists. apply exec_returnM.
Qed.

(* read_senvcfg with senvcfg = 0 reduces to a value with CBIE bits 00. *)
Lemma exec_read_senvcfg_zero s :
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (read_senvcfg tt) s
  = Some (_update_SEnvcfg_SSE (mword_of_int 0)
            (and_vec (_get_MEnvcfg_SSE MENVCFG_S) (_get_SEnvcfg_SSE (mword_of_int 0))), s).
Proof.
  intros Hs Hm. unfold read_senvcfg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)). rewrite Hs.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). rewrite Hm.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)). rewrite Hs.
  apply exec_returnM.
Qed.

(* feature_enabled_for_priv at User short-circuits to FEATURE_ILLEGAL on a
   zeroed machine enable bit (the and_boolM first conjunct is false, so the
   supervisor bit and Ext_S are never consulted). *)
Lemma feature_enabled_bit0_illegal (m su h : mword 1) (s : mstate) :
  eq_vec m ('b"1") = false ->
  exec (feature_enabled_for_priv User m su h) s = Some (FEATURE_ILLEGAL, s).
Proof.
  intro Hm.
  assert (Hl : exec (returnM (eq_vec m ('b"1")) : M bool) s = Some (false, s)).
  { rewrite Hm. apply exec_returnm. }
  assert (Hand : exec (and_boolM (returnM (eq_vec m ('b"1")))
                         (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                                      (fun b => returnM (negb b)))
                                   (returnM (eq_vec su ('b"1"))))) s
                 = Some (false, s)).
  { rewrite (exec_and_boolM_Some _ _ _ _ _ Hl). reflexivity. }
  unfold feature_enabled_for_priv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnM.
Qed.

(* CBCFE of MENVCFG_S is 0, so CLEAN/FLUSH's feature check is illegal for User. *)
Lemma feature_enabled_cbcfe_illegal s scfg :
  exec (feature_enabled_for_priv User (_get_MEnvcfg_CBCFE MENVCFG_S)
          (_get_SEnvcfg_CBCFE scfg) ('b"0")) s = Some (FEATURE_ILLEGAL, s).
Proof. apply feature_enabled_bit0_illegal. vm_compute; reflexivity. Qed.

(* CBO_CLEAN / CBO_FLUSH: feature_enabled_for_priv short-circuits on
   menvcfg.CBCFE = 0.  The two variants have identical illegal reductions. *)
Lemma exec_execute_ZICBOM_cf_illegal (op : cbop_zicbom) (rs1 : regidx) s :
  op = CBO_CLEAN \/ op = CBO_FLUSH ->
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (execute (ZICBOM (op, rs1))) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hop Hcp Hmenv.
  change (execute (ZICBOM (op, rs1))) with (execute_ZICBOM op rs1).
  unfold execute_ZICBOM.
  destruct (exec_read_senvcfg_any' s) as [scfg Hscfg].
  destruct Hop as [-> | ->]; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)) Hcp;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)) Hmenv;
    rewrite (exec_bind_Some _ _ _ _ _ Hscfg);
    rewrite (exec_bind_Some _ _ _ _ _ (feature_enabled_cbcfe_illegal s scfg));
    cbn match; apply exec_returnM.
Qed.

(* CBO_INVAL: cbop_priv_check sees menvcfg.CBIE = 00 (CBIE_ILLEGAL). *)
Lemma exec_execute_ZICBOM_inval_illegal (rs1 : regidx) s :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exec (execute (ZICBOM (CBO_INVAL, rs1))) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hmenv Hsenv HES.
  assert (HmCBIE : exec (encdec_cbie_backwards (_get_MEnvcfg_CBIE MENVCFG_S)) s
                   = Some (CBIE_ILLEGAL, s)).
  { unfold encdec_cbie_backwards.
    replace (eq_vec (_get_MEnvcfg_CBIE MENVCFG_S) ('b"00")) with true
      by (vm_compute; reflexivity). cbn match. apply exec_returnm. }
  assert (HsCBIE : exec (Defs.bind (read_senvcfg tt)
                           (fun w2 => encdec_cbie_backwards (_get_SEnvcfg_CBIE w2))) s
                   = Some (CBIE_ILLEGAL, s)).
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_senvcfg_zero s Hsenv Hmenv)).
    unfold encdec_cbie_backwards.
    replace (eq_vec (_get_SEnvcfg_CBIE (_update_SEnvcfg_SSE (mword_of_int 0)
               (and_vec (_get_MEnvcfg_SSE MENVCFG_S) (_get_SEnvcfg_SSE (mword_of_int 0))))) ('b"00"))
      with true by (vm_compute; reflexivity). cbn match. apply exec_returnm. }
  assert (Hcbop : exec (cbop_priv_check User) s = Some (CBOP_ILLEGAL, s)).
  { unfold cbop_priv_check.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). rewrite Hmenv.
    rewrite (exec_bind_Some _ _ _ _ _ HmCBIE).
    rewrite (exec_bind_Some _ _ _ _ _ HES). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ HsCBIE).
    cbn match. apply exec_returnm. }
  change (execute (ZICBOM (CBO_INVAL, rs1))) with (execute_ZICBOM CBO_INVAL rs1).
  unfold execute_ZICBOM. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ Hcbop). cbn match. apply exec_returnM.
Qed.

(* currentlyEnabled Ext_S depends only on misa, so it is preserved by a
   nextPC write (the step's frame advance). *)
Lemma exec_currentlyEnabled_S_set_nextPC (s : mstate) (v : mword 64) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exec (currentlyEnabled Ext_S) (set_reg s nextPC v)
  = Some (true, set_reg s nextPC v).
Proof.
  intro H. rewrite (exec_currentlyEnabled_S (set_reg s nextPC v)).
  rewrite (exec_currentlyEnabled_S s) in H.
  assert (Hm : register_lookup misa (set_reg s nextPC v).(sregs)
               = register_lookup misa s.(sregs)).
  { unfold set_reg; cbn [sregs].
    rewrite irrelevant_register_set; [ reflexivity | vm_compute; reflexivity ]. }
  rewrite Hm. congruence.
Qed.

(* Unified: any ZICBOM variant is illegal in U under the xv6 config. *)
Lemma exec_execute_ZICBOM_illegal (op : cbop_zicbom) (rs1 : regidx) s :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exec (execute (ZICBOM (op, rs1))) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hmenv Hsenv HES. destruct op.
  - apply exec_execute_ZICBOM_cf_illegal; [ left; reflexivity | exact Hcp | exact Hmenv ].
  - apply exec_execute_ZICBOM_cf_illegal; [ right; reflexivity | exact Hcp | exact Hmenv ].
  - apply exec_execute_ZICBOM_inval_illegal; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* Zicboz (ZICBOZ) and Zicfiss shadow-stack AMO (SSAMOSWAP): their execute
   wraps the config gate in catch_early_return / the MR monad, short-
   circuiting to Illegal via early_return.  Reductions go through execR. *)

Lemma execR_early_return' {R X} (r : R) s :
  execR (Defs.early_return r : Defs.monadR R exception X) s = Some (inl r, s).
Proof. reflexivity. Qed.

(* MR-monad or_boolM short-circuit twin (mirrors exec_or_boolM_Some). *)
Lemma execR_or_boolM_Some (A B : Defs.monadR ExecutionResult exception bool)
    s bl sl :
  execR A s = Some (inr bl, sl) ->
  execR (or_boolM A B) s = (if bl then Some (inr true, sl) else execR B sl).
Proof.
  intro H. unfold or_boolM.
  rewrite (execR_bind A). rewrite H.
  destruct bl; [ rewrite execR_returnR; reflexivity | reflexivity ].
Qed.

(* ZICBOZ: menvcfg.CBZE = 0 makes feature_enabled_for_priv illegal for User;
   the early_return short-circuits before any memory access. *)
Lemma exec_execute_ZICBOZ_illegal (rs1 : regidx) s :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  exec (execute (ZICBOZ rs1)) s = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hmenv.
  change (execute (ZICBOZ rs1)) with (execute_ZICBOZ rs1).
  unfold execute_ZICBOZ.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hcp. cbn match.
  rewrite execR_bind. rewrite (execR_liftR (read_reg menvcfg)).
  rewrite (exec_read_reg menvcfg). rewrite Hmenv. cbn match.
  destruct (exec_read_senvcfg_any' s) as [scfg Hscfg].
  rewrite execR_bind execR_liftR Hscfg. cbn match.
  assert (Hfeat : exec (feature_enabled_for_priv User (_get_MEnvcfg_CBZE MENVCFG_S)
                          (_get_SEnvcfg_CBZE scfg) ('b"0")) s = Some (FEATURE_ILLEGAL, s)).
  { apply feature_enabled_bit0_illegal. vm_compute; reflexivity. }
  rewrite execR_bind execR_liftR Hfeat. cbn match.
  rewrite (execR_bind0 (early_return (Illegal_Instruction tt))).
  rewrite execR_early_return'. cbn match. reflexivity.
Qed.

(* SSAMOSWAP: in User, or_boolM (not Ext_S) (senvcfg.SSE = 0) is true when
   Ext_S is on and senvcfg.SSE = 0, so the shadow-stack AMO is illegal. *)
Lemma exec_execute_SSAMOSWAP_illegal (aq rl : bool) (rs2 rs1 : regidx)
    (width : Z) (rd : regidx) s :
  register_lookup cur_privilege s.(sregs) = User ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup senvcfg s.(sregs) = mword_of_int 0 ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  exec (execute (SSAMOSWAP (aq, rl, rs2, rs1, width, rd))) s
    = Some (Illegal_Instruction tt, s).
Proof.
  intros Hcp Hmenv Hsenv HES.
  change (execute (SSAMOSWAP (aq, rl, rs2, rs1, width, rd)))
    with (execute_SSAMOSWAP aq rl rs2 rs1 width rd).
  unfold execute_SSAMOSWAP.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hcp. cbn match.
  (* the User arm (MR _ unit) >> rest: peel the outer bind0, reduce the arm to
     early_return Illegal via or_boolM -> true. *)
  assert (HA : execR (Defs.bind (Defs.liftR (currentlyEnabled Ext_S))
                 (fun w3 : bool => Defs.returnR ExecutionResult (negb w3))) s
               = Some (inr false, s)).
  { rewrite (execR_bind (Defs.liftR (currentlyEnabled Ext_S))).
    rewrite (execR_liftR (currentlyEnabled Ext_S)) HES. cbn match.
    rewrite execR_returnR. reflexivity. }
  rewrite (execR_bind0 (Defs.bind (or_boolM _ _) _)).
  rewrite (execR_bind (or_boolM _ _)).
  rewrite (execR_or_boolM_Some _ _ _ _ _ HA).
  (* B -> inr true *)
  rewrite (execR_bind (Defs.liftR (read_senvcfg tt))).
  rewrite (execR_liftR (read_senvcfg tt)) (exec_read_senvcfg_zero s Hsenv Hmenv). cbn match.
  rewrite execR_returnR.
  replace (eq_vec (_get_SEnvcfg_SSE (_update_SEnvcfg_SSE (mword_of_int 0)
             (and_vec (_get_MEnvcfg_SSE MENVCFG_S) (_get_SEnvcfg_SSE (mword_of_int 0))))) ('b"0"))
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite execR_early_return'. cbn match. reflexivity.
Qed.

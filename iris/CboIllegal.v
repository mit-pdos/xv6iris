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

(* feature_enabled_for_priv with a menvcfg enable bit of 0 (here CBCFE of
   MENVCFG_S) short-circuits to FEATURE_ILLEGAL for User (the senvcfg value is
   irrelevant). *)
Lemma feature_enabled_cbcfe_illegal s scfg :
  exec (feature_enabled_for_priv User (_get_MEnvcfg_CBCFE MENVCFG_S)
          (_get_SEnvcfg_CBCFE scfg) ('b"0")) s = Some (FEATURE_ILLEGAL, s).
Proof.
  assert (Hl : exec (returnM (eq_vec (_get_MEnvcfg_CBCFE MENVCFG_S) ('b"1")) : M bool) s
               = Some (false, s)).
  { replace (eq_vec (_get_MEnvcfg_CBCFE MENVCFG_S) ('b"1")) with false
      by (vm_compute; reflexivity). apply exec_returnm. }
  assert (Hand : exec (and_boolM (returnM (eq_vec (_get_MEnvcfg_CBCFE MENVCFG_S) ('b"1")))
                         (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                                      (fun b => returnM (negb b)))
                                   (returnM (eq_vec (_get_SEnvcfg_CBCFE scfg) ('b"1"))))) s
                 = Some (false, s)).
  { rewrite (exec_and_boolM_Some _ _ _ _ _ Hl). reflexivity. }
  unfold feature_enabled_for_priv. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnM.
Qed.

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
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)), Hcp;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)), Hmenv;
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

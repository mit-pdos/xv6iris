(** * WeakLeafPmpcfg0.v — the csrw-pmpcfg0 leaf on [WeakFunnelCfg.wwp_instr_config]

    The second CONFIG-WRITING csrw leaf (the weak twin of
    [WpGprCsrwC.wp_csrw_pmpcfg0_raw]): [csrw pmpcfg0] (0x3a0) writes the
    [pmpcfg_n] cell the plain funnel HOLDS across the step, so — like
    [WeakLeafCsrw.wwp_csrw_mstatus_leaf] — it goes through the
    config-variant funnel [WeakFunnelCfg.wwp_instr_config], which surrenders
    [cur_privilege] / [mstatus] / [pmpcfg_n] into the callback at FULL
    ownership.  Everything else is the batch-2 register-only recipe: a
    certificate at [WeakLeafRegOnly.wcert_regonly] / [wQ_pure] over the
    fetch-only trace [regonly_es al4 pc], so no memory arms appear anywhere
    and the leaf is alignment-generic ([al4] a parameter).

    Layout:

      §1  the [exec_eff] mirrors of the csrw-pmpcfg0 [execute] cone, at the
          empty trace — [WpGprCsrwA]'s SC scripts token-for-token under
          [exec_bind_Some] → [exec_eff_bind_nil] etc.  The SC VALUE plumbing
          ([pmpWriteCfg_val], [pmp_cfg_step], [pmpcfg0_final],
          [pmpcfg0_readback], [pmpcfg0_vecupd]) and [WpGprCsrwC]'s PURE
          collapse ([pmpcfg_written], [pmpcfg0_final_set]) are REUSED, never
          restated; so are the CSR-generic [doCSR]/[execute_CSRReg] spine
          ([WeakLeafCsrw] §1f), the check dispatchers ([WeakLeafRegOnly] §3)
          and the enablement chain ([WeakLeafEffCommon] §2).
      §2  the leaf [wwp_csrw_pmpcfg0_leaf]: statement =
          [wp_csrw_pmpcfg0_raw] under the porting-table swaps ([instr] →
          [winstr_bytes] + the decode premises, [gpr_file] → the one source
          cell, [hart_ws]/[ws_le] threading) plus the alignment bit [al4],
          driven through [wwp_instr_config]. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrwCommon WpGprCsrwA WpGprCsrwC.
Require Import WeakLeafCsrw WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [exec_eff] MIRROR OF THE csrw-pmpcfg0 CONE (trace [])

    [WpGprCsrwA]'s scripts with the trace component added; the VALUES are
    that file's ([pmpWriteCfg_val] / [pmp_cfg_step] / [pmpcfg0_final] /
    [pmpcfg0_readback]), so the two mirrors agree definitionally and
    [WpGprCsrwC]'s pure [pmpcfg0_final_set] collapse applies unchanged. *)

(** *** 1a. The per-byte write (total: [PMP_ClearPermissions]) *)

Lemma exec_eff_pmpWriteCfg (cfg v : mword 8) s :
  exec_eff (pmpWriteCfg cfg v) s = Some (pmpWriteCfg_val cfg v, s, []).
Proof.
  unfold pmpWriteCfg, pmpWriteCfg_val.
  destruct (pmpLocked cfg).
  - apply exec_eff_returnM.
  - destruct (andb (eq_vec (_get_Pmpcfg_ent_W (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"1"))
                   (eq_vec (_get_Pmpcfg_ent_R (Mk_Pmpcfg_ent (and_vec v (Ox"9F")))) ('b"0"))).
    + rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
      apply exec_eff_returnM.
    + rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
      apply exec_eff_returnM.
Qed.

(** *** 1b. The 8-iteration [foreach_ZM_up'] loop, unrolled (WpGprCsrwA's
    [do_cfg_step], at [exec_eff]) *)

Ltac do_cfg_step_eff vv ii :=
  rewrite Defs.unroll_foreach_ZM_up'; [ | lia ];
  match goal with
  | |- exec_eff (Defs.bind ?body0 _) ?si = _ =>
    let Hb := fresh "Hb" in
    assert (Hb : exec_eff body0 si = Some (tt, pmp_cfg_step vv si ii, []));
    [ replace (Z.ltb (Z.add (Z.mul 0 4) ii) sys_pmp_usable_count) with true
        by (vm_compute; reflexivity);
      cbn match;
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n si));
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n si));
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_pmpWriteCfg _ _ si));
      unfold pmp_cfg_step; apply exec_eff_write_reg
    | rewrite (exec_eff_bind_nil _ _ _ _ _ Hb) ]
  end.

Lemma exec_eff_pmpWriteCfgReg_0 (v : mword 64) s :
  exec_eff (pmpWriteCfgReg 0 v) s = Some (tt, pmpcfg0_final v s, []).
Proof.
  unfold pmpWriteCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  unfold Defs.foreach_ZM_up.
  do_cfg_step_eff v 0. do_cfg_step_eff v 1. do_cfg_step_eff v 2.
  do_cfg_step_eff v 3. do_cfg_step_eff v 4. do_cfg_step_eff v 5.
  do_cfg_step_eff v 6. do_cfg_step_eff v 7.
  cbn [Defs.foreach_ZM_up']. apply exec_eff_returnM.
Qed.

(** *** 1c. The read-back (the value [write_CSR] returns) *)

Lemma exec_eff_pmpReadCfgReg_0 s :
  exec_eff (pmpReadCfgReg 0) s
    = Some (pmpcfg0_readback (register_lookup pmpcfg_n s.(sregs)), s, []).
Proof.
  unfold pmpReadCfgReg, Defs.assert_exp'.
  replace (Z.eqb (Z.rem 0 2) 0) with true by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)).
  apply exec_eff_returnM.
Qed.

(** *** 1d. write_CSR / check / callback, for pmpcfg0 *)

Lemma exec_eff_write_CSR_pmpcfg0 (v : mword 64) s :
  exec_eff (write_CSR csr_pmpcfg0 v) s
    = Some (Ok (pmpcfg0_readback
                  (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs))),
            pmpcfg0_final v s, []).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  cbn zeta.
  assert (Hidx : uint (subrange_vec_dec csr_pmpcfg0 3 0) = 0)
    by (vm_compute; reflexivity).
  rewrite !Hidx.
  assert (Hwr : exec_eff (Defs.bind0 (pmpWriteCfgReg 0 v) (pmpReadCfgReg 0)) s
                = Some (pmpcfg0_readback
                          (register_lookup pmpcfg_n (pmpcfg0_final v s).(sregs)),
                        pmpcfg0_final v s, [])).
  { rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_pmpWriteCfgReg_0 v s)).
    exact (exec_eff_pmpReadCfgReg_0 (pmpcfg0_final v s)). }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hwr). apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_pmpcfg0 (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_pmpcfg0 d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_pmpcfg0 d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

(** The check dispatch: pmpcfg0 is a PURE-check CSR ([is_CSR_accessible] and
    [stateen_allows_CSR_access] both [returnM true]) — exactly how
    [WpGprCsrwA.exec_execute_csrw_pmpcfg0] discharges it, on
    [WeakLeafRegOnly] §3's generic dispatcher. *)
Lemma exec_eff_check_CSR_result_csrw_pmpcfg0 s :
  exec_eff (check_CSR_result csr_pmpcfg0 Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  apply (exec_eff_check_CSR_result_csrw_pure csr_pmpcfg0 s);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

(** *** 1e. The end-to-end pmpcfg0 execute, trace [] *)

Lemma exec_eff_execute_csrw_pmpcfg0 (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          pmpcfg0_final
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
            s, []).
Proof.
  intros Hrs1 Hpriv.
  change (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_pmpcfg0 (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_pmpcfg0 rs1 s _
           (pmpcfg0_readback (register_lookup pmpcfg_n
              (pmpcfg0_final (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup
                                     (R_bitvector_64 (gpr_of_Z (uint rs1)))
                                     s.(sregs)) s).(sregs)))).
  - exact Hpriv.
  - apply exec_eff_check_CSR_result_csrw_pmpcfg0.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_pmpcfg0.
  - apply exec_eff_csr_id_write_callback_pmpcfg0.
Qed.

(* ====================================================================== *)
(** ** 2. THE LEAF

    [WpGprCsrwC.wp_csrw_pmpcfg0_raw]'s statement under the weak porting
    swaps, alignment-generic.  The funnel is the CONFIG variant (the written
    cell [pmpcfg_n] is one of the three it surrenders), so the plumbing is
    [WeakLeafCsrw.wwp_csrw_mstatus_leaf]'s; the trace/certificate/recipe
    side is [WeakLeafCsrw2]'s alignment-generic kit. *)

Section leaf_pmpcfg0.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_pmpcfg0_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5)
      (ms0 rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW), dst) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ Machine -∗
       mstatus ↦ᵣ ms0 -∗
       pmpcfg_n ↦ᵣ pmpcfg_written rs1v pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz HmIE HMPRV Hdecf Hagree HDmi Hgood Hdec.
    iIntros "#Hhw #Hmiv Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrs1c #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr_config pc false
              (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) pmpcfg0 ms0
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp HmIE HMPRV
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hhw Hmiv Hhs Hpriv Hms0 Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb_config.
    iIntros (σ b) "%Lpc0 %Hcfg %Lms0 Hpriv Hms Hpmpc Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the operand register the funnel does not read *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hcfgc : register_lookup pmpcfg_n
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = pmpcfg0).
      { rewrite (set_lookup_ne pmpcfg_n nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne pmpcfg_n (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lpmpc. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      pose proof (exec_eff_execute_csrw_pmpcfg0 rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc) as He.
      rewrite Hrs1c' pmpcfg0_final_set Hcfgc in He.
      destruct (csrw_sexec_facts_r pmpcfg_n s0c b' (add_vec_int pc 4)
                  (pmpcfg_written rs1v pmpcfg0)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hcfgf : register_lookup pmpcfg_n
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = pmpcfg0).
    { rewrite (set_lookup_ne pmpcfg_n nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat pmpcfg_n σ b eq_refl). exact Lpmpc. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    pose proof (exec_eff_execute_csrw_pmpcfg0 rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf) as Hef.
    rewrite Hrs1f pmpcfg0_final_set Hcfgf in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ pmpcfg_n _ (pmpcfg_written rs1v pmpcfg0)
            with "Hreg Hpmpc") as "[Hreg Hpmpc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     pmpcfg_n (pmpcfg_written rs1v pmpcfg0)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hhs Hpc".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r pmpcfg_n (wflat_st σ) b (add_vec_int pc 4)
                (pmpcfg_written rs1v pmpcfg0)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hhs Hpriv Hms Hpmpc [$Hpc $Hnpc] Hrs1c Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_pmpcfg0.

(* ====================================================================== *)
(** ** 3. Soundness check *)

Print Assumptions exec_eff_execute_csrw_pmpcfg0.
Print Assumptions wwp_csrw_pmpcfg0_leaf.

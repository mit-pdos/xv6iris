(** * WeakLeafCsrw2.v — the SIMPLE-LEGALIZER csrw leaves (M4, start/timerinit)

    The weak twins of [WpGprCsrwA]/[WpGprCsrwB]'s register-only csrw leaves
    whose [write_CSR] reads nothing but the target CSR itself:
    medeleg / mideleg / mepc / mcounteren / menvcfg.  Each is
    [WeakLeafCsrw.wwp_csrw_mstatus_leaf]'s recipe on the PLAIN funnel
    ([WeakFunnel.wwp_instr] — none of these writes a funnel-held config
    cell), driven through the alignment-generic register-only kit
    ([WeakLeafRegOnly]): every leaf takes the fetch alignment [al4] as a
    parameter and covers both the 4-aligned and the 2-not-4-aligned call
    sites of [start()]/[timerinit()] with one statement.

    Per CSR this file owes exactly what the batch-2 worklist predicted:
      - the [write_CSR] trace-[] mirror (the [doCSR]/[execute_CSRReg] spine
        is [WeakLeafCsrw] §1f's, CSR-generic; the check dispatchers are
        [WeakLeafRegOnly] §3's);
      - the end-to-end [execute] mirror;
      - the leaf, a clone of the medeleg TEMPLATE below with the cell/value
        names substituted. *)
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
Require Import WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.
Require Import WeakLeafCsrw WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. medeleg (0x302; Ext_S-gated, pure legalize) — THE TEMPLATE *)

Lemma exec_eff_write_CSR_medeleg (v : mword 64) s :
  exec_eff (write_CSR csr_medeleg v) s
    = Some (Ok (legalize_medeleg (register_lookup medeleg s.(sregs)) v),
            set_reg s medeleg
              (legalize_medeleg (register_lookup medeleg s.(sregs)) v), []).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg medeleg s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg medeleg _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg medeleg _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_medeleg (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_medeleg d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_medeleg d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_medeleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s medeleg
            (legalize_medeleg (register_lookup medeleg s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS.
  change (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_medeleg (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_medeleg rs1 s _
           (legalize_medeleg (register_lookup medeleg s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_S csr_medeleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_medeleg.
  - apply exec_eff_csr_id_write_callback_medeleg.
Qed.

(** *** 1b. THE LEAF — the template every further register-only csrw leaf
    clones.  Statement = [WpGprCsrwA.wp_csrw_medeleg_gpr] under the
    porting-table swaps ([instr] → [winstr_bytes] + the decode premises,
    [gpr_file] → the one source cell, [hart_ws]/[ws_le] threading) plus the
    alignment bit [al4] ([is_aligned_vaddr pc 4 = al4]; both arms of
    [start()]/[timerinit()] occur). *)

Section leaf_medeleg.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_medeleg_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (medeleg0 rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    medeleg ↦ᵣ medeleg0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       medeleg ↦ᵣ legalize_medeleg medeleg0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
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
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat medeleg σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)))
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
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hcsrc : register_lookup medeleg
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = medeleg0).
      { rewrite (set_lookup_ne medeleg nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne medeleg (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_medeleg rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc) as He.
      rewrite Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r medeleg s0c b' (add_vec_int pc 4)
                  (legalize_medeleg medeleg0 rs1v)
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
               pc w (CSRReg (csr_medeleg, Regidx rs1, zreg, CSRRW)) D dst).
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
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hcsrf : register_lookup medeleg
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = medeleg0).
    { rewrite (set_lookup_ne medeleg nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_medeleg rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf) as Hef.
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ medeleg _ (legalize_medeleg medeleg0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     medeleg (legalize_medeleg medeleg0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r medeleg (wflat_st σ) b (add_vec_int pc 4)
                (legalize_medeleg medeleg0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_medeleg.

(* ====================================================================== *)
(** ** 2. mideleg (0x303; Ext_S-gated, MONADIC legalize)

    [WpGprCsrwB]'s [exec_write_CSR_mideleg] / [exec_execute_csrw_mideleg]
    cone at [exec_eff].  [legalize_mideleg] is monadic: it walks
    [currentlyEnabled Ext_Sscofpmf] once and [currentlyEnabled Ext_S] three
    times, so the Sscofpmf leg ([hartSupports Sscofpmf] / [hartSupports
    Zihpm], [WpGprCsrwB] §0) is mirrored here too.  The value itself is the
    SC [mideleg_legalized], reused. *)

Lemma exec_eff_hartSupports_Sscofpmf s :
  exec_eff (hartSupports Ext_Sscofpmf) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sscofpmf) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zihpm s :
  exec_eff (hartSupports Ext_Zihpm) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zihpm) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Sscofpmf s :
  exec_eff (currentlyEnabled Ext_Sscofpmf) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sscofpmf) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sscofpmf s)).
  cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zihpm ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)); cbn match
  end.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Zihpm s)).
  cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)); cbn match
  end.
  apply exec_eff_hartSupports_Zicsr.
Qed.

Lemma exec_eff_legalize_mideleg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (legalize_mideleg o v) s = Some (mideleg_legalized o v, s, []).
Proof.
  intro HS. unfold legalize_mideleg, mideleg_legalized.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Sscofpmf s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_write_CSR_mideleg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (write_CSR csr_mideleg v) s
    = Some (Ok (mideleg_legalized (register_lookup mideleg s.(sregs)) v),
            set_reg s mideleg
              (mideleg_legalized (register_lookup mideleg s.(sregs)) v), []).
Proof.
  intro HS. unfold write_CSR.
  skip_csr_false_clauses_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_legalize_mideleg (register_lookup mideleg s.(sregs)) v s
                HS)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mideleg _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_mideleg (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_mideleg d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_mideleg d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_mideleg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mideleg
            (mideleg_legalized (register_lookup mideleg s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS.
  change (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_mideleg (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_mideleg rs1 s _
           (mideleg_legalized (register_lookup mideleg s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_S csr_mideleg s HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | csr_dispatch_eq | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_mideleg; exact HS.
  - apply exec_eff_csr_id_write_callback_mideleg.
Qed.

(** *** 2b. THE LEAF *)

Section leaf_mideleg.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_mideleg_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (mideleg0 : type_of_register mideleg)
      (rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mideleg ↦ᵣ mideleg0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       mideleg ↦ᵣ mideleg_legalized mideleg0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
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
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mideleg σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)))
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
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hcsrc : register_lookup mideleg
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = mideleg0).
      { rewrite (set_lookup_ne mideleg nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne mideleg (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_mideleg rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc) as He.
      rewrite Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r mideleg s0c b' (add_vec_int pc 4)
                  (mideleg_legalized mideleg0 rs1v)
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
               pc w (CSRReg (csr_mideleg, Regidx rs1, zreg, CSRRW)) D dst).
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
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hcsrf : register_lookup mideleg
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = mideleg0).
    { rewrite (set_lookup_ne mideleg nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_mideleg rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf) as Hef.
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mideleg _ (mideleg_legalized mideleg0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     mideleg (mideleg_legalized mideleg0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r mideleg (wflat_st σ) b (add_vec_int pc 4)
                (mideleg_legalized mideleg0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_mideleg.


(* ====================================================================== *)
(** ** 3. mepc (0x341; pure check, [set_xepc] → [mepc_val])

    [WpGprCsrwA]'s [exec_write_CSR_mepc] cone at [exec_eff].  The only
    support leaf is [hartSupports Ext_Zca] (the IALIGN test inside
    [legalize_xepc]); the value [mepc_val] is the SC definition, reused. *)

Lemma exec_eff_hartSupports_Zca s :
  exec_eff (hartSupports Ext_Zca) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zca) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_legalize_xepc (v : mword 64) s :
  exec_eff (legalize_xepc v) s = Some (mepc_val v, s, []).
Proof.
  unfold legalize_xepc, mepc_val.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_hartSupports_Zca s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_write_CSR_mepc (v : mword 64) s :
  exec_eff (write_CSR csr_mepc v) s
    = Some (Ok (mepc_val v), set_reg s mepc (mepc_val v), []).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses_eff.
  assert (Hsx : exec_eff (set_xepc Machine v) s
                = Some (mepc_val v, set_reg s mepc (mepc_val v), [])).
  { unfold set_xepc.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_legalize_xepc v s)).
    cbn match.
    rewrite (exec_eff_bind0_nil _ _ _ _ _
               (exec_eff_write_reg mepc (mepc_val v) s)).
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hsx).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_mepc (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_mepc d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_mepc d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_mepc (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mepc
            (mepc_val (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                         s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv.
  change (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_mepc (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_mepc rs1 s _
           (mepc_val (if Z.eqb (uint rs1) 0 then zero_reg
                      else register_lookup
                             (R_bitvector_64 (gpr_of_Z (uint rs1)))
                             s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_pure csr_mepc s);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_mepc.
  - apply exec_eff_csr_id_write_callback_mepc.
Qed.

(** *** 3b. THE LEAF *)

Section leaf_mepc.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_mepc_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (mepc0 : type_of_register mepc)
      (rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       mepc ↦ᵣ mepc_val rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
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
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mepc σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)))
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
      (* no misa premise, and the written value does not read the old cell:
         [mepc_val] is a function of the SOURCE register alone. *)
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      pose proof (exec_eff_execute_csrw_mepc rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc) as He.
      rewrite Hrs1c' in He.
      destruct (csrw_sexec_facts_r mepc s0c b' (add_vec_int pc 4)
                  (mepc_val rs1v)
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
               pc w (CSRReg (csr_mepc, Regidx rs1, zreg, CSRRW)) D dst).
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
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    pose proof (exec_eff_execute_csrw_mepc rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf) as Hef.
    rewrite Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mepc _ (mepc_val rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     mepc (mepc_val rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r mepc (wflat_st σ) b (add_vec_int pc 4)
                (mepc_val rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_mepc.


(* ====================================================================== *)
(** ** 4. mcounteren (0x306; Ext_U-gated, pure legalize)

    [WpGprCsrwA]'s [exec_write_CSR_mcounteren] /
    [exec_execute_csrw_mcounteren_full] cone at [exec_eff].  Note the CELL
    is 32 bits ([type_of_register mcounteren]) while the [write_CSR] result
    the callback sees is its [zero_extend' 64]. *)

Lemma exec_eff_write_CSR_mcounteren (v : mword 64) s :
  exec_eff (write_CSR csr_mcounteren v) s
    = Some (Ok (zero_extend' 64
                  (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                     v)),
            set_reg s mcounteren
              (legalize_mcounteren (register_lookup mcounteren s.(sregs)) v),
            []).
Proof.
  unfold write_CSR.
  skip_csr_false_clauses_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mcounteren s)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mcounteren _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mcounteren _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_mcounteren (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_mcounteren d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_mcounteren d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_mcounteren (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (check_CSR_result csr_mcounteren Machine CSRWrite) s
    = Some (CSR_Check_OK tt, s, []) ->
  exec_eff (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mcounteren
            (legalize_mcounteren (register_lookup mcounteren s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv Hchk.
  change (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_mcounteren (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_mcounteren rs1 s _
           (zero_extend' 64
              (legalize_mcounteren (register_lookup mcounteren s.(sregs))
                 (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                         s.(sregs))))).
  - exact Hpriv.
  - exact Hchk.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_mcounteren.
  - apply exec_eff_csr_id_write_callback_mcounteren.
Qed.

Lemma exec_eff_execute_csrw_mcounteren_full (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mcounteren
            (legalize_mcounteren (register_lookup mcounteren s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HU. apply exec_eff_execute_csrw_mcounteren; try assumption.
  apply (exec_eff_check_CSR_result_csrw_U csr_mcounteren s HU);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | csr_dispatch_eq | vm_compute; reflexivity ].
Qed.

(** *** 4b. THE LEAF *)

Section leaf_mcounteren.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_mcounteren_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (mcounteren0 : type_of_register mcounteren)
      (rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       mcounteren ↦ᵣ legalize_mcounteren mcounteren0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
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
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mcounteren σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)))
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
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hcsrc : register_lookup mcounteren
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = mcounteren0).
      { rewrite (set_lookup_ne mcounteren nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne mcounteren (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HUc : eq_vec (_get_Misa_U (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_mcounteren_full rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HUc) as He.
      rewrite Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r mcounteren s0c b' (add_vec_int pc 4)
                  (legalize_mcounteren mcounteren0 rs1v)
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
               pc w (CSRReg (csr_mcounteren, Regidx rs1, zreg, CSRRW)) D dst).
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
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hcsrf : register_lookup mcounteren
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = mcounteren0).
    { rewrite (set_lookup_ne mcounteren nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HUf : eq_vec (_get_Misa_U (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_mcounteren_full rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HUf) as Hef.
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mcounteren _ (legalize_mcounteren mcounteren0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     mcounteren (legalize_mcounteren mcounteren0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r mcounteren (wflat_st σ) b (add_vec_int pc 4)
                (legalize_mcounteren mcounteren0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_mcounteren.


(* ====================================================================== *)
(** ** 5. menvcfg (0x30A; Ext_U-and-gated check, MONADIC legalize)

    [WpGprCsrwA]'s [exec_write_CSR_menvcfg] cone at [exec_eff].  This is
    the deepest of the five: [legalize_menvcfg] chains Zicfilp / Zicfiss /
    Zicboz / Zicbom (twice) / the cbie legalizer / Sstc / Smnpm / Svadu /
    Svpbmt, so every one of those [hartSupports]/[currentlyEnabled] SC
    leaves gets a trace-[] twin here.  The value [menvcfg_legalized] (and
    [menvcfg_cbie]) is the SC definition, reused. *)

Lemma exec_eff_hartSupports_Zicfiss s :
  exec_eff (hartSupports Ext_Zicfiss) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfiss) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zicboz s :
  exec_eff (hartSupports Ext_Zicboz) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicboz) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Zicbom s :
  exec_eff (hartSupports Ext_Zicbom) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicbom) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Sstc s :
  exec_eff (hartSupports Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Smnpm s :
  exec_eff (hartSupports Ext_Smnpm) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Smnpm) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Svadu s :
  exec_eff (hartSupports Ext_Svadu) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svadu) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_hartSupports_Svpbmt s :
  exec_eff (hartSupports Ext_Svpbmt) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svpbmt) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Zicboz s :
  exec_eff (currentlyEnabled Ext_Zicboz) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicboz) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Zicboz.
Qed.

Lemma exec_eff_currentlyEnabled_Zicbom s :
  exec_eff (currentlyEnabled Ext_Zicbom) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicbom) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Zicbom.
Qed.

Lemma exec_eff_currentlyEnabled_Sstc s :
  exec_eff (currentlyEnabled Ext_Sstc) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Sstc.
Qed.

Lemma exec_eff_currentlyEnabled_Smnpm s :
  exec_eff (currentlyEnabled Ext_Smnpm) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Smnpm) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Smnpm.
Qed.

Lemma exec_eff_currentlyEnabled_Svadu s :
  exec_eff (currentlyEnabled Ext_Svadu) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svadu) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  apply exec_eff_hartSupports_Svadu.
Qed.

(** [WpGprCsrwA.crush_inner_cE_S]'s mirror: reduce an inner
    [_rec_currentlyEnabled Ext_S k a] at a concrete [k] to the misa.S bit. *)
Ltac crush_inner_cE_S_eff s :=
  match goal with |- context[_rec_currentlyEnabled Ext_S ?k ?a] =>
    let H := fresh "HSm" in
    assert (H : exec_eff (_rec_currentlyEnabled Ext_S k a) s
                = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                          ('b"1"), s, []));
    [ destruct a; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?kk 0] =>
        replace (Z.geb kk 0) with true by reflexivity end;
      cbn match;
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s));
      cbn match;
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_S s));
      cbn match;
      rewrite (exec_eff_and_boolM_nil _ _ s
                 (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                    ('b"1")) s);
      [ destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs)))
                    ('b"1")) eqn:?;
        [ match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k2 ?a2] =>
            exact (exec_eff_rec_cE_Zicsr_any k2 a2 s
                     ltac:(vm_compute; reflexivity)) end
        | reflexivity ]
      | rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s));
        apply exec_eff_returnM ]
    | rewrite H ]
  end.

Lemma exec_eff_currentlyEnabled_Svpbmt s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Svpbmt) s = Some (true, s, []).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Svpbmt) 0) with true
    by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Svpbmt s)).
  cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] =>
    destruct a end.
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  match goal with |- context[Z.geb ?kk 0] =>
    replace (Z.geb kk 0) with true by reflexivity end.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Sv39 s)).
  cbn match.
  crush_inner_cE_S_eff s. rewrite HS. reflexivity.
Qed.

Lemma exec_eff_legalize_xenvcfg_cbie (cbie : mword 2) s :
  exec_eff (legalize_xenvcfg_cbie cbie) s
    = Some (if neq_vec cbie ('b"10") then cbie else ('b"00"), s, []).
Proof.
  unfold legalize_xenvcfg_cbie.
  destruct (neq_vec cbie ('b"10")).
  - apply exec_eff_returnM.
  - cbn match. apply exec_eff_returnM.
Qed.

Lemma exec_eff_legalize_menvcfg (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (legalize_menvcfg o v) s = Some (menvcfg_legalized o v, s, []).
Proof.
  intro HS. unfold legalize_menvcfg, menvcfg_legalized, menvcfg_cbie.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_hartSupports_Zicfilp s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_hartSupports_Zicfiss s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Zicboz s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Zicbom s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Zicbom s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_legalize_xenvcfg_cbie
                (_get_MEnvcfg_CBIE (Mk_MEnvcfg v)) s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Sstc s)).
  cbn match.
  match goal with |- context[Defs.and_boolM ?l ?r] =>
    assert (Hsm : exec_eff (Defs.and_boolM l r) s
                  = Some (andb true
                            (is_supported_pmm PM_SMNPM
                               (pmm_mode_backwards
                                  (_get_MEnvcfg_PMM (Mk_MEnvcfg v)))), s, []))
  end.
  { rewrite (exec_eff_and_boolM_nil _ _ _ _ _
               (exec_eff_currentlyEnabled_Smnpm s)). cbn match.
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hsm). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Svadu s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Svpbmt s HS)).
  cbn match.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_write_CSR_menvcfg (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (write_CSR csr_menvcfg v) s
    = Some (Ok (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v),
            set_reg s menvcfg
              (menvcfg_legalized (register_lookup menvcfg s.(sregs)) v), []).
Proof.
  intro HS. unfold write_CSR.
  skip_csr_false_clauses_eff.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg menvcfg s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_legalize_menvcfg (register_lookup menvcfg s.(sregs)) v s
                HS)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg menvcfg _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg menvcfg _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_menvcfg (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_menvcfg d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_menvcfg d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_menvcfg (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s menvcfg
            (menvcfg_legalized (register_lookup menvcfg s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS HU.
  change (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_menvcfg (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_menvcfg rs1 s _
           (menvcfg_legalized (register_lookup menvcfg s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)))).
  - exact Hpriv.
  - apply (exec_eff_check_CSR_result_csrw_U_and csr_menvcfg
             xenvcfg_csrs_are_defined s HU);
      [ vm_compute; reflexivity | vm_compute; reflexivity | csr_dispatch_eq
      | vm_compute; reflexivity | vm_compute; reflexivity ].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_menvcfg; assumption.
  - apply exec_eff_csr_id_write_callback_menvcfg.
Qed.

(** *** 5b. THE LEAF *)

Section leaf_menvcfg.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_csrw_menvcfg_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (rs1 : mword 5) (menvcfg0 : type_of_register menvcfg)
      (rs1v npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rs1 <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       menvcfg ↦ᵣ menvcfg_legalized menvcfg0 rs1v -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrs1nz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hrs1c Hcsr #Hbs Hhws Hcont".
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
    iApply (wwp_instr pc false (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
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
    (* the two registers the funnel does not read: the source and the CSR *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat menvcfg σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)))
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
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hcsrc : register_lookup menvcfg
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = menvcfg0).
      { rewrite (set_lookup_ne menvcfg nextPC _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne menvcfg (R_bool minstret_increment)
                   _ _ ltac:(reg_ne)).
        exact Lcsr. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      assert (HUc : eq_vec (_get_Misa_U (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_menvcfg rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc HUc) as He.
      rewrite Hcsrc Hrs1c' in He.
      destruct (csrw_sexec_facts_r menvcfg s0c b' (add_vec_int pc 4)
                  (menvcfg_legalized menvcfg0 rs1v)
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
               pc w (CSRReg (csr_menvcfg, Regidx rs1, zreg, CSRRW)) D dst).
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
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hcsrf : register_lookup menvcfg
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = menvcfg0).
    { rewrite (set_lookup_ne menvcfg nextPC _ _ ltac:(reg_ne)).
      exact Lcsr_a. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (HUf : eq_vec (_get_Misa_U (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_menvcfg rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf HUf) as Hef.
    rewrite Hcsrf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ menvcfg _ (menvcfg_legalized menvcfg0 rs1v)
            with "Hreg Hcsr") as "[Hreg Hcsr]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     menvcfg (menvcfg_legalized menvcfg0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts_r menvcfg (wflat_st σ) b (add_vec_int pc 4)
                (menvcfg_legalized menvcfg0 rs1v)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrs1c Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf_menvcfg.

(* ====================================================================== *)
(** ** Soundness check *)

Print Assumptions exec_eff_execute_csrw_medeleg.
Print Assumptions wwp_csrw_medeleg_leaf.
Print Assumptions exec_eff_execute_csrw_mideleg.
Print Assumptions wwp_csrw_mideleg_leaf.
Print Assumptions exec_eff_execute_csrw_mepc.
Print Assumptions wwp_csrw_mepc_leaf.
Print Assumptions exec_eff_execute_csrw_mcounteren.
Print Assumptions exec_eff_execute_csrw_mcounteren_full.
Print Assumptions wwp_csrw_mcounteren_leaf.
Print Assumptions exec_eff_execute_csrw_menvcfg.
Print Assumptions wwp_csrw_menvcfg_leaf.

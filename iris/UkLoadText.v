(* UkLoadText.v -- THE ENGINE'S LOAD OUT OF THE TEXT HALF (icache).

   [UkLoad.wp_uk_load] serves every load whose target page is WRITABLE --
   a data page, whose bytes the walker owns.  A program's string literals
   live in its text page (X, not W), whose bytes are STAMPED and outside the
   walker's map (claude-notes/projects/icache.md), so the one text-page load
   the engine speaks -- vprintf's format-string [lbu] --  is driven at the
   node ([WpUmodeTextLoad.uv_swp_lbu_text]).  This file is [UkLoad]'s
   post-fetch / obligation / driver tower for exactly that instruction:
   the same step ([UkStep.wp_uk_step]), the same fetch bridge
   ([WpUmodeFetch.uv_swp_fetch_uinstr]), the same close
   ([UkStep.uk_psi_active]); only the execute in the middle differs. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import WpGpr RegFile.
Require Import WpDecodeBridge DecodeTotalU.
Require Import PtreeType.
Require Import UserPtTree.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import UserFrame UserClassifyAsm.
Require Import UserExec.
Require UserTotalU.
Require Import UserActiveClass.
Require Import UserMemCert.
Require Import UmodeMem UmodeArith.
Require Import UmodeRegs.
Require Import WpUmodeStep WpUmodeStore WpUmodeLoad WpUmodeTextLoad.
Require Import UserPerm UexecWp UexecRet UkStep.
Require Import UmodeText.
Require Import FdSlots.
Require Import UserFd.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE POST-FETCH MIDDLE: [UkLoad.uk_load_post_fetch] with the node   *)
(* route in place of the walker.                                          *)
(* ===================================================================== *)
Section UkLbuTextPostFetch.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  Lemma uk_lbu_text_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64)
      (imm : mword 12) (lr1 lrd : mword 5)
      (w_ld va : mword 64) (bb : mword 8) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) :
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Mp !! (uint va) = Some bb ->
    uva_text pt (uint va) ->
    uva_inj pt Mp ->
    u_exec_pins pt t' rs2 ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rsE)
          (register_lookup (R_bitvector_64 minstretcfg) rsE)
          (register_lookup cur_privilege rsE) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    uk_pt_pure pt sz M Mp ->
    gen_cert -∗ uv_amb -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          (uvb C pt Rfd Rut sz π fdv M
             (<[Regidx lrd := regval_into_reg (zero_extend' 64 bb)]> m)
             (add_vec_int pc 4) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t' -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc 4) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc 4) rs2) u_Dro -∗
    swp (execute (LOAD (imm, Regidx lr1, Regidx lrd, true, 1)))
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hrd Hva Hl Hchk Hcanon Hbb Htx Hinj
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    set (wval := zero_extend' 64 bb).
    set (rsx := register_set nextPC (add_vec_int pc 4) rs2).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc 4)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    assert (Hpinsx : u_exec_pins pt t' rsx)
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc 4) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hvax : va = add_vec (if Z.eqb (uint lr1) 0 then zero_reg
                                 else register_lookup
                                        (R_bitvector_64 (gpr_of_Z (uint lr1))) rsx)
                          (sign_extend' 64 imm))
      by (rewrite (Hvals lr1); exact Hva).
    assert (Hb1 : uM_bytes Mp (uint va) 1 bb).
    { rewrite <- (uM_word_byte Mp (uint va) bb Hbb).
      exact (uM_word_bytes Mp (uint va) 1 ltac:(lia)
               ltac:(intros j Hj;
                     assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                     subst j; exists bb; rewrite Z.add_0_r; exact Hbb)). }
    assert (Hwv : extend_value true bb = wval) by reflexivity.
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    iApply (swp_mono with "[Hk Hres] [Hany Hrw Hro Hctx Hmm]").
    2:{ iApply (uv_swp_lbu_text pt Mp t' (uc_dqc C) rsx w_ld va bb imm lr1 lrd
                  Hrd Hvax Hinj Hl Hchk Hcanon Hb1 Htx Hcfgx Hpinsx Htok'
                  with "Hcert Hany Hrw Hro Hctx Hmm"). }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs3 rsr t'')
      "(%Tonly & %Hag3 & %Htlbok'' & %Htokn & %Hshape & Hrw & Hro & Hctx & Hmm & Hany)".
    rewrite Hwv in Hag3.
    (* ---- the post-execute file, from the pre-fetch one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              uv_nogpr r ->
              register_lookup r (uv_post_rs rsr None (Some (lrd, wval))) = vv).
    { intros r vv Hv Hne Hnt Hng.
      rewrite (uv_post_rs_other rsr None (Some (lrd, wval)) r Hne Hng).
      rewrite (Tonly r Hnt). exact (Tn r vv Hv Hne). }
    assert (Lnpcw : register_lookup (R_bitvector_64 nextPC)
                      (uv_post_rs rsr None (Some (lrd, wval))) = add_vec_int pc 4).
    { cbn [uv_post_rs uv_jmp_rs uv_wr_rs].
      rewrite (irrelevant_register_set _ _ rsr _ (regbeq_nextPC_gpr (uint lrd))).
      rewrite (Tonly (R_bitvector_64 nextPC) ltac:(vm_compute; reflexivity)).
      exact Lnpcx. }
    assert (Hgagr : u_gpr_agree m rsr).
    { intros q Hnz. rewrite (Tonly _ (uv_gpr_ne_tlb (uint q))). exact (Hgagx q Hnz). }
    assert (Ltlbw : register_lookup tlb (uv_post_rs rsr None (Some (lrd, wval)))
                    = register_lookup tlb rsr)
      by exact (uv_post_rs_other rsr None (Some (lrd, wval)) tlb
                  ltac:(vm_compute; reflexivity) uv_nogpr_tlb).
    iApply (run_exec_post_direct _ ib RETIRE_SUCCESS ltac:(exact I)).
    rewrite /uv_step_post.
    iExists (uv_post_rs rsr None (Some (lrd, wval))).
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_hart)
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_minc)
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 (uv_post_rs rsr None (Some (lrd, wval))) u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3
                 (uv_post_rs rsr None (Some (lrd, wval))) u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uk_psi_active C pt Rfd R Rut sz π M Mp
              (<[Regidx lrd := regval_into_reg wval]> m) (add_vec_int pc 4)
              t'' usatp pcfg paddr
              (uv_post_rs rsr None (Some (lrd, wval))) fdv
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_hart)
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_priv)
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity) uv_nogpr_mst);
                    exact Hms2)
              Lnpcw
              (uv_gpr_agree_post m rsr None (Some (lrd, wval)) Hrd Hgagr)
              (uv_upd_x0 m (Some (lrd, wval)) Hrd Hx0)
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_stvec)
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mie)
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mdl)
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_medl)
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_menv)
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mste)
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_sste)
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_senv)
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_satp)
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_pcfg)
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_paddr)
              Htokn ltac:(rewrite Ltlbw; exact Htlbok'') Hpure
              with "Hamb Hany Hmm [Hres] Hctx Hk").
    iApply (uv_res_move pt Mp t' t'' usatp pcfg paddr Hshape with "Hres").
  Qed.

End UkLbuTextPostFetch.

(* ===================================================================== *)
(* §2 THE FETCH OBLIGATION: [UkLoad.uk_load_obl_base] for the one          *)
(* instruction, mapped arm only (a text page IS mapped, X and not W).       *)
(* ===================================================================== *)
Section UkLbuTextObl.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  Lemma uk_lbu_text_obl_base (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (imm : mword 12) (lr1 lrd : mword 5) (w_ld va : mword 64) (bb : mword 8)
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    udecode_base w (LOAD (imm, Regidx lr1, Regidx lrd, true, 1)) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Mp !! (uint va) = Some bb ->
    uva_text pt (uint va) ->
    gen_cert -∗ uv_amb -∗
    uv_fetch_bridge (uc_dqc C) pt Mp rsA t (F_Base w) -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          ((uvb C pt Rfd Rut sz π fdv M
              (<[Regidx lrd := regval_into_reg (zero_extend' 64 bb)]> m)
              (add_vec_int pc 4) -∗ WP (Loop : expr riscv_lang))
           ∧ uslot (uvis_of_run m pc M π sz fdv))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hdec Hrd Hva Hl Hchk Hcanon Hbb Htx.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres".
    iApply (swp_mono with "[Hk Hres] [Hbridge Hany Hrw Hro Hctx Hmm]").
    2:{ iApply ("Hbridge" with "Hcert Hany Hrw Hro Hctx Hmm"). }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2 rsf t')
      "(%Tr & %Hag & %Htlbok' & %Htok' & %Hshape & Hrw & Hro & Hctx & Hmm & Hany)".
    iDestruct (uv_res_move pt Mp t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, (LOAD (imm, Regidx lr1, Regidx lrd, true, 1)), pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w _ Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_lbu_text_post_fetch C pt Rfd R Rut sz π M Mp m pc imm lr1 lrd
              w_ld va bb (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2 fdv
              Hrd Hva Hl Hchk Hcanon Hbb Htx Hinj
              Hpins2
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Hagd2 Htok' Hpure
              with "Hcert Hamb [Hk] Hany Hctx Hmm Hres Hrw Hro").
    iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
    iDestruct "Hkc" as "[Hkc _]". iFrame "Hrut Hfdr Hkb Hkc".
  Qed.

End UkLbuTextObl.

(* ===================================================================== *)
(* §3 THE DRIVER.                                                         *)
(* ===================================================================== *)
Section UkLbuText.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  Hypothesis (HRut : forall pt' : uptd,
                       ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                                    (TsoCtx.own_context XI -∗ Rut pt')).

  (* the load's leaf permission, on the KEY: a TEXT page -- X and not W *)
  Definition uk_text_ok (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_X q = true /\ up_W q = false.

  Lemma wp_uk_lbu_text_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_text_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    wval = zero_extend' 64 bb ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ▷ ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hbb Hwval. subst wval.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hcont".
    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut _ M m pc fdv Hal2 with "Hb [] Hcont").
    iModIntro.
    rewrite /uk_step_obl.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' HRut' Mp' t rs1s rsA usatp pcfg paddr)
      "%Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    pose proof (uk_instr_mapped π M Mp' pc _ _ pt' sz
                  (loop_ok_wf C' pt' Hlo') Hpm' Hpure Hui) as Hui'.
    pose proof (loop_ok_wf C' pt' Hlo') as Hwf'.
    destruct Hkok as (q & Hq & Hqx & Hqw).
    (* the text page is MAPPED, X and not W: [uva_text], and its leaf *)
    assert (Htx : uva_text pt' (uint va)).
    { apply (uva_text_of_perm pt' sz (uint va) q);
        [ rewrite moi_of_uint Hpm'; exact Hq | exact Hqx | exact Hqw ]. }
    pose proof Htx as (w_ld & Hl0 & _ & _).
    assert (Hl : ud_um pt' !! svpn_of va = Some w_ld)
      by (rewrite moi_of_uint in Hl0; exact Hl0).
    assert (Hchk : uleaf_ok (Load Data) w_ld)
      by exact (perm_of_R pt' sz _ q w_ld Hwf' ltac:(rewrite Hpm'; exact Hq) Hl).
    assert (Hbb' : Mp' !! (uint va) = Some bb).
    { assert (Hoff : (bv_unsigned va mod 4096 + Z.of_nat 0 < 4096)%Z).
      { change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
        apply Z.mod_pos_bound. lia. }
      assert (Hbb0 : M !! (uint va + Z.of_nat 0) = Some bb)
        by (change (Z.of_nat 0) with 0; rewrite Z.add_0_r; exact Hbb).
      pose proof (ukp_win pt' sz M Mp' va w_ld 0 bb (proj1 Hwf') Hpure Hl Hoff Hbb0)
        as Hw0.
      change (Z.of_nat 0) with 0 in Hw0. rewrite Z.add_0_r in Hw0. exact Hw0. }
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    (* the continuation at THIS table, out of the table-generic one *)
    iAssert (R -∗ (TsoCtx.own_context (CID := CIDo) XIo -∗ Rut' pt') ∗ Rfd' fdv ∗ ukb C' pt' Rfd' Rut' sz π fdv ∗
             ((uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv M
                 (<[Regidx rd := regval_into_reg (zero_extend' 64 bb)]> m)
                 (add_vec_int pc 4) -∗
               WP (Loop : expr riscv_lang))
              ∧ uslot (uvis_of_run m pc M π sz fdv)))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iFrame "Hrut Hfdr Hkb". iSplit.
      - iDestruct "Hkc" as "[Hkc _]".
        iIntros "Hb". rewrite /ukc.
        iApply ("Hkc" $! CIDo XIo C' pt' Rfd' Rut' HRut' with "[%] [%] Hb");
          [ exact Hlo' | exact Hpm' ].
      - iDestruct "Hkc" as "[_ Hkc]".
        rewrite (uslot_run m pc M π sz fdv Hx0 Hal2). iExact "Hkc". }
    iPoseProof (uv_swp_fetch_uinstr (CID := CIDo) (XI := XIo) pt' Mp' t (uc_dqc C')
                  rsA pc false _ Hinj Hui' LpcA LcpA (proj1 HmsokA) LmenvA
                  HpinsA Htok) as "Hf".
    iEval (cbn beta iota) in "Hf".
    iDestruct "Hf" as (w) "[[%HnRVC %Hdecbase] Hbridge]".
    iApply (uk_lbu_text_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w imm rs1 rd
              w_ld va bb t usatp pcfg paddr rs1s rsA fdv Hpre Hpure
              Hdecbase Hrd Hva Hl Hchk Hcanon Hbb' Htx
              with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
  Qed.

  (* the later-free restatement: the shape the run layer takes *)
  Lemma wp_uk_lbu_text_x (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_text_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    wval = zero_extend' 64 bb ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hbb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_lbu_text_later M m pc fdv imm rs1 rd va wval bb
              Hui Hrd Hva Hkok Hcanon Hbb Hwval with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

End UkLbuText.

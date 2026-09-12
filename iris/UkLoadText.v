(* UkLoadText.v -- THE ENGINE'S LOAD OUT OF THE TEXT HALF (icache).

   [UkLoad.wp_uk_load] serves every load whose target page is WRITABLE --
   a data page, whose bytes the walker owns.  A program's string literals
   live in its text page (X, not W), whose bytes are STAMPED and outside the
   walker's map (claude-notes/design/icache.md), so the text-page loads
   the engine speaks -- vprintf's format-string [lbu] and sh's jump-table
   [c.lw] -- are driven at the node ([WpUmodeTextLoad.uv_swp_load_text]).
   This file is [UkLoad]'s post-fetch / obligation / driver tower for those:
   the same step ([UkStep.wp_uk_step]), the same fetch bridge
   ([WpUmodeFetch.uv_swp_fetch_uinstr]), the same close
   ([UkStep.uk_psi_active]); only the execute in the middle differs.

   IT IS WIDTH-, SIGNEDNESS- AND GEOMETRY-GENERIC, like [UkLoad]: the width
   is any [uload_width], and a COMPRESSED load reaches the same node through
   its [ExecuteAs] redirect ([uv_redirect]), which is a register-only stretch
   and so runs on [WpUmodeFetch.uv_swp_walk].  What this file does NOT have
   is [UkLoad]'s fault arm: a text page is mapped by construction. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
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
Require Import UserMemPt UserMemCert UserMemArmsC.
Require Import MemAccessGen WpMmodeLeafBase.
Require Import UmodeMem UmodeArith.
Require Import UmodeRegs.
Require Import WpUmodeStep WpUmodeStore WpUmodeLoad WpUmodeTextLoad.
Require Import UserPerm UexecWp UexecRet UkStep.
Require Import UmodeText.
Require Import FdSlots.
Require Import UserFd.
Require Import TsoCtx.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §1 THE POST-FETCH MIDDLE: [UkLoad.uk_load_post_fetch] with the node   *)
(* route in place of the walker.                                          *)
(* ===================================================================== *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkLoadTextExec.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.

  (* THE EXECUTE, at an abstract post.  [Φ] is [run_exec_post …] when the
     instruction IS the load and the plain [fun e' => …] when a compressed
     load has already redirected to it, so the two geometries share this
     whole body. *)
  Lemma uk_load_text_exec (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (dv : mword (8 * kk)) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 rsm : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32)
      (Φ : ExecutionResult -> iProp Σ) :
    uload_width kk ->
    reg_agree_on (u_Drw ∪ u_Dro) rsm
      (register_set nextPC (add_vec_int pc dpc) rs2) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    uM_bytes Mp (uint va) (Z.to_nat kk) dv ->
    uva_text pt (uint va) ->
    uva_inj pt Mp ->
    (⊢ uv_step_post C R rsE (Step_Execute (RETIRE_SUCCESS, ib)) -∗
         Φ RETIRE_SUCCESS) ->
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
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv cw gn cs pidv ∗
          (uvb C pt Rfd Rut sz π fdv cw gn cs pidv M
             (<[Regidx lrd := regval_into_reg wval]> m)
             (add_vec_int pc dpc) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t' -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame rsm u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C)) rsm u_Dro -∗
    swp (execute (LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk))) Φ.
  Proof.
    intros Hkw Hagm Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hb1 Htx Hinj HPhi
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    pose proof (vmem_width_dvd kk (proj1 Hkw)) as Hkdvd.
    pose proof (vmem_width_uint kk (proj1 Hkw)) as Huintk.
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc dpc)
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
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc dpc) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hvax : va = add_vec (if Z.eqb (uint lr1) 0 then zero_reg
                                 else register_lookup
                                        (R_bitvector_64 (gpr_of_Z (uint lr1))) rsx)
                          (sign_extend' 64 imm))
      by (rewrite (Hvals lr1); exact Hva).
    assert (Hwv : extend_value is_unsigned dv = wval) by (symmetry; exact Hwval).
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    iApply (swp_mono with "[Hk Hres] [Hany Hrw Hro Hctx Hmm]").
    2:{ iApply (uv_swp_load_text kk (proj1 Hkw) Hkdvd Huintk is_unsigned
                  pt Mp t' (uc_dqc C) rsm rsx w_ld va dv imm lr1 lrd Hagm
                  Hrd Hvax Hinj Hl Hchk Hcanon Hpg Hal Hb1 Htx Hcfgx Hpinsx Htok'
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
                      (uv_post_rs rsr None (Some (lrd, wval))) = add_vec_int pc dpc).
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
    iApply HPhi.
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
              (<[Regidx lrd := regval_into_reg wval]> m) (add_vec_int pc dpc)
              t'' usatp pcfg paddr
              (uv_post_rs rsr None (Some (lrd, wval))) fdv cw gn cs pidv
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

  Local Lemma phi_id (P : iProp Σ) : ⊢ P -∗ P.
  Proof. iIntros "H". iExact "H". Qed.

  (* ------------------------------------------------------------------- *)
  (* THE REDIRECT DISPATCH.  A base load IS the node; a COMPRESSED one     *)
  (* returns [ExecuteAs] first, and that is a register-only stretch        *)
  (* ([WpUmodeFetch.uv_swp_walk]) -- the shape [WpUmodeStore.uv_swp_exec_mem] *)
  (* has for the walker route.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_load_text_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (dv : mword (8 * kk)) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    uM_bytes Mp (uint va) (Z.to_nat kk) dv ->
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
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv cw gn cs pidv ∗
          (uvb C pt Rfd Rut sz π fdv cw gn cs pidv M
             (<[Regidx lrd := regval_into_reg wval]> m)
             (add_vec_int pc dpc) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t' -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hb1 Htx Hinj
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    destruct o as [j | ]; cbn [uv_exp] in Hexp.
    - (* the COMPRESSED geometry: [ExecuteAs], then the node *)
      subst j.
      iApply (uv_swp_walk pt Mp Mp t' t' (uc_dqc C) rsx rsx rsx (execute i)
                (ExecuteAs (LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk))) _
                Hinj Hinj eq_refl Htok' Htok' eq_refl
                ltac:(intros q _; reflexivity)
                (Hred (u_state rsx (uv_mmd pt Mp t')))
                (Hg1 (u_state rsx (uv_mmd pt Mp t')) (uv_mmd pt Mp t'))
                with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
      iIntros (rs1) "%Hag1 Hrw Hro Hctx Hmm Hany".
      iApply run_exec_post_redirect.
      iApply (uk_load_text_exec R Rut sz π M Mp m pc dpc kk imm lr1 lrd
                is_unsigned w_ld va wval dv ib t' usatp pcfg paddr rsE rs2 rs1
                fdv cw gn cs pidv
                (fun e' : ExecutionResult =>
                   uv_step_post C R rsE (Step_Execute (e', ib)))
                Hkw Hag1 Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hb1 Htx Hinj
                (phi_id _)
                Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2
                Lmenv2 Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2
                Htok' Hpure
                with "Hcert Hamb Hk Hany Hctx Hmm Hres Hrw Hro").
    - (* the BASE geometry: the instruction IS the node *)
      subst i.
      iApply (uk_load_text_exec R Rut sz π M Mp m pc dpc kk imm lr1 lrd
                is_unsigned w_ld va wval dv ib t' usatp pcfg paddr rsE rs2 rsx
                fdv cw gn cs pidv
                (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                                  uv_step_post C R rsE (Step_Execute (r, ib'))) ib)
                Hkw ltac:(intros q _; reflexivity)
                Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hb1 Htx Hinj
                (run_exec_post_direct _ ib RETIRE_SUCCESS ltac:(exact I))
                Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2
                Lmenv2 Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2
                Htok' Hpure
                with "Hcert Hamb Hk Hany Hctx Hmm Hres Hrw Hro").
  Qed.

End UkLoadTextExec.

(* ===================================================================== *)
(* §2 THE FETCH OBLIGATION: [UkLoad.uk_load_obl_base] / [_rvc] at the text *)
(* node, MAPPED ARM ONLY (a text page IS mapped, X and not W).             *)
(* ===================================================================== *)
Section UkLoadTextObl.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  (* the payload the run keeps -- implicit; the trap arm below hands it
     over with the slot ([UexecRet.uexec_pay_dep]) *)
  Context {Qp : Z -> iProp Σ}.

  Lemma uk_load_text_obl_base (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (dv : mword (8 * kk))
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    udecode_base w i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    uM_bytes Mp (uint va) (Z.to_nat kk) dv ->
    uva_text pt (uint va) ->
    gen_cert -∗ uv_amb -∗
    uv_fetch_bridge (uc_dqc C) pt Mp rsA t (F_Base w) -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv cw gn cs pidv ∗
          ((uvb C pt Rfd Rut sz π fdv cw gn cs pidv M
              (<[Regidx lrd := regval_into_reg wval]> m)
              (add_vec_int pc 4) -∗ WP (Loop : expr riscv_lang))
           ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv)))) -∗
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
    intros Hpre Hpure Hdec Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon
      Hpg Hal Hbw Htx.
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
    iExists rs2, i, pc, 8%nat.
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
    iApply (uk_load_text_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm
              lr1 lrd is_unsigned w_ld va wval dv (zero_extend' 32 w) t' usatp pcfg paddr
              rs1 rs2 fdv cw gn cs pidv
              Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hbw Htx Hinj
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

  (* the COMPRESSED geometry: [c.lw] out of .rodata is sh's jump table *)
  Lemma uk_load_text_obl_rvc (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (dv : mword (8 * kk))
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    udecode_rvc h i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    uM_bytes Mp (uint va) (Z.to_nat kk) dv ->
    uva_text pt (uint va) ->
    gen_cert -∗ uv_amb -∗
    uv_fetch_bridge (uc_dqc C) pt Mp rsA t (F_RVC h) -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv cw gn cs pidv ∗
          ((uvb C pt Rfd Rut sz π fdv cw gn cs pidv M
              (<[Regidx lrd := regval_into_reg wval]> m)
              (add_vec_int pc 2) -∗ WP (Loop : expr riscv_lang))
           ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv)))) -∗
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
    intros Hpre Hpure Hdec Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon
      Hpg Hal Hbw Htx.
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
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_load_text_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm
              lr1 lrd is_unsigned w_ld va wval dv (zero_extend' 32 h) t' usatp pcfg paddr
              rs1 rs2 fdv cw gn cs pidv
              Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hbw Htx Hinj
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

End UkLoadTextObl.

(* ===================================================================== *)
(* §3 THE DRIVER.                                                         *)
(* ===================================================================== *)
Section UkLoadText.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  (* the payload the run keeps -- implicit, read off the continuation
     ([UexecRet.ukcq]); no call site names it *)
    Context {Qp : Z -> iProp Σ}.
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  Hypothesis (HRut : forall pt' : uptd,
                       ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                                    (TsoCtx.own_context XI -∗ Rut pt')).

  (* the load's leaf permission, on the KEY: a TEXT page -- X and not W *)
  Definition uk_text_ok (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_X q = true /\ up_W q = false.

  (* ------------------------------------------------------------------- *)
  (* THE TEXT LOAD LEAF, width- signedness- and geometry-generic.  Its one *)
  (* difference from [UkLoad.wp_uk_load] is the leaf permission: a TEXT    *)
  (* page ([uk_text_ok]) rather than a writable one, which is what puts    *)
  (* the read on the node instead of the walker.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_load_text_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (va wval : mword 64) :
    uload_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_text_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv M m pc -∗
    ▷ ukcq Qp π M sz fdv cw gn cs pidv (<[Regidx rd := regval_into_reg wval]> m)
        (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    pose proof (vmem_width_pos k (proj1 Hkw)) as Hkpos.
    iIntros "Hb Hcont".
    (* the payment goes to the engine with the continuation, under the same
       later ([UexecRet.ukcq]) *)
    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut _ Qp M m pc fdv cw gn cs pidv Hal2
              with "Hb [] [Hcont]").
    2:{ iNext. rewrite /ukcq. iExact "Hcont". }
    iModIntro.
    rewrite /uk_step_obl.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' HRut' Mp' t rs1s rsA usatp pcfg paddr)
      "%Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    pose proof (uk_instr_mapped π M Mp' pc _ i pt' sz
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
    (* the read window, transported into the table's own sub-image *)
    assert (Hbw : uM_bytes Mp' (uint va) (Z.to_nat k) (uM_word M (uint va) k)).
    { intros j Hj.
      exact (ukp_win pt' sz M Mp' va w_ld j _ (proj1 Hwf') Hpure Hl
               (ukp_off va k (Z.of_nat j) Hpg ltac:(lia))
               (uM_word_bytes M (uint va) k ltac:(lia) HMb j Hj)). }
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    (* the continuation at THIS table, out of the table-generic one *)
    iAssert (R -∗ (TsoCtx.own_context (CID := CIDo) XIo -∗ Rut' pt') ∗ Rfd' fdv ∗ ukb C' pt' Rfd' Rut' sz π fdv cw gn cs pidv ∗
             ((uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv cw gn cs pidv M
                 (<[Regidx rd := regval_into_reg wval]> m)
                 (add_vec_int pc (if is_rvc then 2 else 4)) -∗
               WP (Loop : expr riscv_lang))
              ∧ UkStep.uk_paycont Qp gn (uslot (uvis_of_run m pc M π sz fdv cw gn cs pidv))))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iFrame "Hrut Hfdr Hkb". iSplit.
      - (* the RETIRE leg: the payment goes straight back into the
           continuation *)
        iDestruct "Hkc" as "(_ & Hpayv & Hkc)".
        iDestruct ("Hkc" with "Hpayv") as "[Hkc _]".
        iIntros "Hb". rewrite /ukc.
        iApply ("Hkc" $! CIDo XIo C' pt' Rfd' Rut' HRut' with "[%] [%] Hb");
          [ exact Hlo' | exact Hpm' ].
      - (* the FAULT leg: the payment is handed to the kernel with the slot,
           and the arm hands it back into the continuation *)
        iDestruct "Hkc" as "(#Hmyp & Hpayv & Hkc)". iFrame "Hmyp Hpayv".
        iIntros "Hpayv". iDestruct ("Hkc" with "Hpayv") as "[_ Hkc]".
        rewrite (uslot_run m pc M π sz fdv cw gn cs pidv Hx0 Hal2). iExact "Hkc". }
    iPoseProof (uv_swp_fetch_uinstr (CID := CIDo) (XI := XIo) pt' Mp' t (uc_dqc C')
                  rsA pc is_rvc i Hinj Hui' LpcA LcpA (proj1 HmsokA) LmenvA
                  HpinsA Htok) as "Hf".
    destruct is_rvc.
    - iDestruct "Hf" as (h) "[[%HisRVC %Hdecrvc] Hbridge]".
      iApply (uk_load_text_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm
                rs1 rd is_unsigned w_ld va wval _ t usatp pcfg paddr rs1s rsA
                fdv cw gn cs pidv Hpre Hpure Hdecrvc Hkw Hred Hg1 Hexp Hrd Hva
                Hwval Hl Hchk Hcanon Hpg Hal Hbw Htx
                with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
    - iDestruct "Hf" as (w) "[[%HnRVC %Hdecbase] Hbridge]".
      iApply (uk_load_text_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm
                rs1 rd is_unsigned w_ld va wval _ t usatp pcfg paddr rs1s rsA
                fdv cw gn cs pidv Hpre Hpure Hdecbase Hkw Hred Hg1 Hexp Hrd Hva
                Hwval Hl Hchk Hcanon Hpg Hal Hbw Htx
                with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
  Qed.

  (* the later-free restatement: the shape the run layer takes *)
  Lemma wp_uk_load_text (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (va wval : mword 64) :
    uload_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_text_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv M m pc -∗
    ukcq Qp π M sz fdv cw gn cs pidv (<[Regidx rd := regval_into_reg wval]> m)
        (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load_text_later M m pc fdv cw gn cs pidv is_rvc i o imm rs1 rd
              is_unsigned k va wval
              Hkw Hui Hred Hg1 Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lbu rd, imm(rs1) out of the text half -- vprintf's format string.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_lbu_text_x (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_text_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    wval = zero_extend' 64 bb ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv M m pc -∗
    ukcq Qp π M sz fdv cw gn cs pidv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hbb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load_text M m pc fdv cw gn cs pidv false
              (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) None
              imm rs1 rd true 1 va wval
              uload_width_1 Hui ltac:(intro s; exact I) I eq_refl Hrd
              Hva Hkok Hcanon (uinpage_1 va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              ltac:(rewrite (uM_word_byte_val M (uint va) bb Hbb); exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.lw rd', uimm(rs1') out of the text half -- sh's jump table, which   *)
  (* lives in .rodata and so shares the executable segment's pages.  The   *)
  (* compressed form REDIRECTS to the uncompressed [lw], which is width 4  *)
  (* and SIGNED.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_clw_text_x (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname) (pidv : mword 32) (uimm : mword 5) (crs1 crd : mword 3)
      (rs1 rd : mword 5) (va wval : mword 64) (wv : mword 32) :
    uk_instr π M pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    uk_text_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = sign_extend' 64 wv ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv M m pc -∗
    ukcq Qp π M sz fdv cw gn cs pidv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcrd Hrd Hva Hkok Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load_text M m pc fdv cw gn cs pidv true
              (C_LW (uimm, Cregidx crs1, Cregidx crd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                           Regidx rs1, Regidx rd, false, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rd false 4 va wval
              uload_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_LW_leaf uimm (Cregidx crs1) (Cregidx crd)
                             _ rs1 rd s eq_refl Hcr1 Hcrd))
              (fun s mb => goodmb_execute_C_LW_U Du_r Du_w uimm (Cregidx crs1)
                             (Cregidx crd) s mb)
              eq_refl Hrd Hva Hkok Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_s M (uint va) wv Hbw); exact Hwval)
              with "Hb Hcont").
  Qed.

End UkLoadText.

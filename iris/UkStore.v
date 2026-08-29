(* ===================================================================== *)
(* UkStore.v -- THE MEMORY-WRITING LEAF of the user-mode-on-kernel tier:   *)
(* WpUmodeStore.v's §5-§6 (the store's post-fetch middle, the two          *)
(* fetch-shape obligations, the width-generic [wp_uk_store] and its six     *)
(* instances) stated against [UexecRet.uvb] / [ukc] over the UkStep.v      *)
(* engine.  §0-§4 of WpUmodeStore.v -- the width side conditions, the      *)
(* image-level [uM_store], the pure store walk, the execute facts and the   *)
(* residue re-imager -- mention no capability and are imported verbatim.   *)
(* The statements are WpUmodeStore.v's with the bundle and continuation    *)
(* re-read exactly as UkLeaf.v does; the proofs are unchanged except for   *)
(* the payload's type (see UkStep.v's header).                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile InstrBytes.
Require Import SmodeCore.
Require Import WpDecodeBridge DecodeTotalU.
Require Import CommonWalk.
Require Import PtreeType PtAdBits PtTree PtTreeAdue KptPt KptTree.
Require Import SRegime UptTree UptWalkPt.
Require Import UserBits UserPtTree UserTranslate.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFetchCert PtWalkCert.
Require Import UserExec.
Require UserTotalU.
Require Import UserActiveClass.
Require Import MemAccessGen WpMmodeLeafBase.
Require Import UserMemPt UserMemArms UserMemClassify UserMemAccess UserMemMis.
Require Import UserMemCert UserMemArmsBase UserMemArmsC.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep WpUmodeStore.
Require Import ProcPtOwn UserPerm UsysMemOk UexecWp UexecSlot UexecRet UkStep.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

Section UkStorePostFetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The geometry-agnostic middle: from the FETCHED file, write nextPC,    *)
  (* run the store, and hand [uv_psi_active] the payload at the NEW image  *)
  (* and the UNCHANGED register file.  The store-flavoured twin of         *)
  (* [WpUmodeStep.uv_retire_post_fetch].                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_store_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (sr1 sr2 : mword 5)
      (w_st va wval : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) :
    ustore_width kk ->
    uv_redirect i o ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uva_inj pt M ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
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
    uv_tree_ok pt (upa_map pt M) t' ->
    uk_pt_pure pt M ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ ukb C pt Rut π ∗
          (uvb C pt Rut π (uM_store M (uint va) kk wval) m (add_vec_int pc dpc) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt M)) -∗
    uv_res pt M t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    destruct Hkw as (Hvw & Hwrite_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof (uvw_le8 kk Hvw) as Hk8.
    pose proof (uvw_dvd kk Hvw) as Hkdvd.
    pose proof (uvw_uint kk Hvw) as Huintk.
    set (md := upa_map pt M).
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    set (pa := u_walk_pa w_st va).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by (apply (Tn _ _ Lpc2); vm_compute; reflexivity).
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc dpc)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc dpc) Hagd2).
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
    (* ---- the store window, in the re-keyed image ---- *)
    assert (Hnc : forall j : nat, (j < Z.to_nat kk)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nc_k va kk (Z.of_nat j) Hpg). lia. }
    assert (Hwin : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_pa pt (uint va + Z.of_nat j) = pa_add pa j)
      by (intros j Hj; exact (uva_pa_window pt w_st va j Hl (Hnc j Hj))).
    assert (Hmdw : forall j : nat, (j < Z.to_nat kk)%nat ->
              is_Some (md !! pa_add pa j)).
    { intros j Hj. destruct (HMb j Hj) as (bb & Hbb). exists bb.
      rewrite <- (Hwin j Hj). exact (upa_map_lookup pt M _ bb Hinj Hbb). }
    (* ---- the store, pure ---- *)
    destruct (uv_store_mm kk Hk Hk8 Hkdvd Huintk Hwrite_plain pt t' md rsx
                w_st va (ustore_data kk wval)
                Hl Hchk Hcanon Hal (uinpage_one va kk Hpg) Hmdw Hcfgx Hpinsx Htok')
      as (rsw & t'' & Hvwa & Hvwag & Tonly & Htlbok'' & Htok'' & Hshape).
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint sr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr1))) rsx)
                    = m !!! Regidx sr1) by exact (Hvals sr1).
    assert (Hvv : (if Z.eqb (uint sr2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr2))) rsx)
                  = wval) by (rewrite Hwval; exact (Hvals sr2)).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Store Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Store Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Store Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Store Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (RETIRE_SUCCESS,
                          u_state rsw (write_bytes (uv_mm t'' md) pa (Z.to_N kk)
                                         (ustore_data kk wval)))).
    { rewrite Hexp.
      exact (exec_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _
               Lcpx Heff Hpml Htm Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _ (uv_mm t' md)
               Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)
               ltac:(rewrite <- Hva; exact Hvwag)). }
    (* ---- the landing map IS the re-keyed post-store image ---- *)
    set (M' := uM_store M (uint va) kk wval).
    assert (HMdom : dom M' = dom M)
      by (apply uM_store_dom; intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
          exact (mk_is_Some _ _ Hbb)).
    assert (Hinj' : uva_inj pt M')
      by exact (uva_inj_dom pt M M' (eq_sym HMdom) Hinj).
    assert (Hmdeq : upa_map pt M' = write_bytes md pa (Z.to_N kk) wval)
      by (apply upa_map_store;
          [ exact Hinj
          | intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
            exact (mk_is_Some _ _ Hbb)
          | exact Hwin ]).
    assert (Hdat : write_bytes md pa (Z.to_N kk) (ustore_data kk wval)
                   = write_bytes md pa (Z.to_N kk) wval).
    { apply write_bytes_ext. intros j Hj.
      apply nth_byte_ustore_data; [ exact Hk | exact Hk8 | lia ]. }
    pose proof Htok'' as (Hdisj'' & Hdj'' & Hram'' & Hwfm'' & Hspec'').
    assert (Hnt : forall j : nat, (N.of_nat j < Z.to_N kk)%N ->
              ptree_bytes 2 t'' !! pa_add pa j = None).
    { intros j Hj. apply (uv_mm_tree_none t'' md _ Hdj''). apply Hmdw. lia. }
    assert (Hmmeq : write_bytes (uv_mm t'' md) pa (Z.to_N kk) (ustore_data kk wval)
                    = uv_mm t'' (upa_map pt M')).
    { rewrite /uv_mm (write_bytes_union_r (ptree_bytes 2 t'') md pa (Z.to_N kk)
                        (ustore_data kk wval) Hnt).
      rewrite Hdat Hmdeq. reflexivity. }
    rewrite Hmmeq in Hex.
    (* ---- the post-store tree is well-formed at the NEW image ---- *)
    assert (Hdomimg : (dom (upa_map pt M') : gset Arch.pa) = dom md)
      by (unfold md; exact (upa_map_dom_eq pt M' M HMdom)).
    assert (Htokn : uv_tree_ok pt (upa_map pt M') t'').
    { split_and!; [ exact Hdisj'' | | | exact Hwfm'' | exact Hspec'' ].
      - rewrite Hmdeq. apply map_disjoint_spec. intros x b1 b2 H1 H2.
        assert (Hs : is_Some (md !! x)).
        { apply (write_bytes_is_Some_iff md pa (Z.to_N kk) wval x);
            [ intros j Hj; apply Hmdw; lia | exact (mk_is_Some _ _ H2) ]. }
        destruct Hs as (b3 & Hb3).
        exact (proj1 (map_disjoint_spec (ptree_bytes 2 t'') md) Hdj'' x b1 b3 H1 Hb3).
      - intros a Ha. apply Hram''.
        rewrite (uv_mm_dom_img t'' (upa_map pt M') md Hdomimg) in Ha.
        exact Ha. }
    (* ---- the domain of the whole map does not move ---- *)
    assert (Hdomall : (dom (uv_mm t'' (upa_map pt M')) : gset Arch.pa)
                      = dom (uv_mm t' md)).
    { rewrite (uv_mm_dom_img t'' (upa_map pt M') md Hdomimg).
      exact (eq_sym (uv_mm_dom t' t'' md Hshape)). }
    (* ---- the post-store file, from the pre-store one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              register_lookup r rsw = vv).
    { intros r vv Hv Hne Hnt2. rewrite (Tonly r Hnt2). exact (Tn r vv Hv Hne). }
    iIntros "#Hcert #Hamb Hk Hany Hmm [#Hclaims Hcl] Hrw Hro".
    iApply (uv_swp_exec_mem (uc_dqc C) (uv_mm t' md) (uv_mm t'' (upa_map pt M'))
              rsx rsw i o ib _ Hred Hg1
              Hexg Hex Hdomall
              with "Hcert Hany Hrw Hro Hmm [Hk Hcl]").
    iIntros (rs3) "%Hag3 Hrw Hro Hmm Hany".
    rewrite /uv_step_post.
    iExists rsw.
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 rsw u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3 rsw u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uk_psi_active C pt R Rut π M' m (add_vec_int pc dpc) t'' usatp pcfg paddr
              rsw
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity));
                    exact Hms2)
              ltac:(rewrite (Tonly (R_bitvector_64 nextPC)
                               ltac:(vm_compute; reflexivity)); exact Lnpcx)
              ltac:(intros q Hnz;
                    rewrite (Tonly (R_bitvector_64 (gpr_of_Z (uint q)))
                               (uv_gpr_ne_tlb (uint q)));
                    exact (Hgagx q Hnz))
              Hx0
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              Htokn Htlbok'' (conj (eq_trans HMdom (proj1 Hpure)) (proj2 Hpure))
              with "Hamb Hany Hmm [] Hk").
    iApply (uv_res_reimg pt M' t'' usatp pcfg paddr Hinj'
              ltac:(pose proof Hpins2 as (_ & _ & ((us & Hok & Hsa) & _) & _);
                    rewrite Lsatp2 in Hsa; rewrite Hsa; exact Hok)
              ltac:(pose proof Hpins2 as (_ & _ &
                      (_ & HA & Hord & HX & HW & HR & Hcov) & _);
                    rewrite Lpcfg2 in HA, HX, HW, HR;
                    rewrite Lpaddr2 in Hord, Hcov;
                    unfold pmp_ent0_ok; split_and!;
                    [ exact HA | exact Hord | exact HX | exact HW | exact HR
                    | exact Hcov ])
              with "[]").
    by iApply (pt_claims_shape 2 t' t'' Hshape).
  Qed.

End UkStorePostFetch.

Section UkStoreObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* §6 THE OBLIGATION, once per FETCH SHAPE -- the store twins of         *)
  (* WpUmodeStep's [uv_obl_base] / [uv_obl_rvc], differing from them only  *)
  (* in the tail they hand the fetched file to.                           *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_store_obl_base (R : iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (w_st va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt M ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ ukb C pt Rut π ∗
          (uvb C pt Rut π (uM_store M (uint va) kk wval) m (add_vec_int pc 4) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
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
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uk_store_post_fetch C pt R Rut π M m pc 4 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
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
              with "Hcert Hamb Hk Hany Hmm Hres Hrw Hro").
  Qed.

  Lemma uk_store_obl_rvc (R : iProp Σ) (Rut : uptd -> iProp Σ)
      (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (w_st va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt M ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗
    (R -∗ Rut pt ∗ ukb C pt Rut π ∗
          (uvb C pt Rut π (uM_store M (uint va) kk wval) m (add_vec_int pc 2) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
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
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
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
    iApply (uk_store_post_fetch C pt R Rut π M m pc 2 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
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
              with "Hcert Hamb Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UkStoreObl.

Section UkStore.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).

  (* ------------------------------------------------------------------- *)
  (* THE STORE LEAF.                                                       *)
  (*                                                                       *)
  (* Width-generic: [k] is any [ustore_width] (1/2/4/8), so [sb/sh/sw/sd]  *)
  (* and every compressed store are ONE lemma.  It takes the same [uinstr] /*)
  (* [uv_redirect] pair the funnel does, so a compressed store names its   *)
  (* [ExecuteAs] expansion -- and, exactly as the ported funnel does, the  *)
  (* WRAPPER's [goodmb] certificate beside it (a redirect never reaches a  *)
  (* memory node, so it holds at every map; the STORE's own certificate is *)
  (* produced here from the catalogue).  No register is written; the image *)
  (* gains exactly the low [k] bytes of [wval = m !!! rs2].                 *)
  (* ------------------------------------------------------------------- *)
  (* the store's leaf permission, on the KEY: the target page is writable *)
  Definition uk_store_ok (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_W q = true.

  Lemma wp_uk_store_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (va wval : mword 64) :
    ustore_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ▷ ukc π (uM_store M (uint va) k wval) m (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hcont".
    iApply (wp_uk_step C pt Rut π sz Hlo Hpm _ M m pc Hal2 with "Hb [] Hcont").
    rewrite /uk_step_obl.
    iIntros (R CIDo C' pt' Rut' sz' t rs1s rsA usatp pcfg paddr)
      "%Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hmm Hres".
    destruct (Hui pt' sz' (loop_ok_wf C' pt' Hlo') Hpm')
      as [Hal2' Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    (* the store's leaf at THIS table, from the key: the byte is in the
       image, so its page is mapped; the key says the page is writable *)
    pose proof (loop_ok_wf C' pt' Hlo') as Hwf'.
    destruct Hsok as (q & Hq & Hqw).
    pose proof (vmem_width_pos k (proj1 Hkw)) as Hkpos.
    destruct (HMb 0%nat ltac:(lia)) as (b0 & Hb0).
    rewrite Z.add_0_r in Hb0.
    destruct (image_byte_mapped pt' M (uint va) b0 (proj1 Hwf') (proj1 Hpure) Hb0)
      as (w_st & Hl).
    rewrite moi_uint64 in Hl.
    destruct (perm_of_W pt' sz' _ q w_st Hwf' ltac:(rewrite Hpm'; exact Hq) Hqw Hl)
      as [Hchk _].
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    (* the continuation at THIS table, out of the table-generic one *)
    iAssert (R -∗ Rut' pt' ∗ ukb C' pt' Rut' π ∗
             (uvb (CID := CIDo) C' pt' Rut' π (uM_store M (uint va) k wval) m
                (add_vec_int pc (if is_rvc then 2 else 4)) -∗
              WP (Loop : expr riscv_lang)))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hkb & Hkc)".
      iFrame "Hrut Hkb". iIntros "Hb".
      rewrite /ukc.
      iApply ("Hkc" $! CIDo C' pt' Rut' sz' with "[%] [%] Hb");
        [ exact Hlo' | exact Hpm' ]. }
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes M (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt' M t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uk_store_obl_rvc C' pt' R Rut' π M m pc h i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_rvc_2 pt' M t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2' Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_store_obl_rvc C' pt' R Rut' π M m pc h i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt' M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uk_store_obl_base C' pt' R Rut' π M m pc w i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_base_2 pt' M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2' Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_store_obl_base C' pt' R Rut' π M m pc w i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hk Hany Hrw Hro Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every instance takes *)
  Lemma wp_uk_store (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (va wval : mword 64) :
    ustore_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store M (uint va) k wval) m (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store_later M m pc is_rvc i o imm rs1 rs2 k va wval
              Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The six instances, exactly WpUmodeStore.v's with the table's leaf     *)
  (* premises replaced by the key's [uk_store_ok].                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_sd (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store8 M (uint va) wval) m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 8)) None
              imm rs1 rs2 8 va wval
              ustore_width_8 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_sw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store M (uint va) 4 wval) m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 4)) None
              imm rs1 rs2 4 va wval
              ustore_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_sb (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store M (uint va) 1 wval) m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hbb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 1)) None
              imm rs1 rs2 1 va wval
              ustore_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon (uinpage_byte va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csdsp (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (tgt wval : mword 64) :
    uk_instr π M pc true (C_SDSP (uimm, Regidx rs2)) ->
    tgt = add_vec (m !!! Regidx csp_rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok tgt ->
    uva_canon tgt ->
    Z.rem (uint tgt) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint tgt + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store8 M (uint tgt) wval) m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc true (C_SDSP (uimm, Regidx rs2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx csp_rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              csp_rs1 rs2 8 tgt wval
              ustore_width_8 Hui
              ltac:(intro s; apply exec_execute_C_SDSP)
              (fun s mb => goodmb_execute_C_SDSP_U Du_r Du_w uimm (Regidx rs2) s mb)
              eq_refl eq_refl
              Htgt Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csd (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store8 M (uint va) wval) m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              rs1 rs2 8 va wval
              ustore_width_8 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SD_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"000")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SD_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rut π M m pc -∗
    ukc π (uM_store M (uint va) 4 wval) m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                            Regidx rs2, Regidx rs1, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rs2 4 va wval
              ustore_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SW_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"00")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SW_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

End UkStore.

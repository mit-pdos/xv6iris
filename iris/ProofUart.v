(* ProofUart.v: the UART device leaves over the SIE-agnostic v2 bundle
   ([sconf] + [sie_cap], stage-5 straggler of the interrupt sweep).

   These are the accessor-form device leaves of WpSmodePtUart rebased on
   the funnel [wp_instr_s_sconf]: [dev_inv] is opened across the funnel
   callback's own step (devN is disjoint from minstretN, so
   the open is arm-blind), the caller does its uart ghost step through
   the accessor wand while the invariant is open, and the translate side
   runs REGIME-BLIND through the derived regime instance [strans_regime]
   ([sr_inv strans_regime] IS the folded translation slot [strans_inv]
   definitionally, so the bundle's invariant [Htr] threads straight
   through [sr_transform]/[sr_absorb] (claim from the static bundle) with no skolem-root open or
   repack).  The store leaf carries no rd
   premises and no retarget; the load leaf takes [rd <> csp_rs1] and
   retargets the capability like every gpr-writing sconf leaf.          *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import DevModel RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad WpGpr WpMmodeLeafBase InstrBytes MinstretInv.
Require Import RegFile HartTp.
Require Import KptPt.
Require Import SmodeCore WpSmodeGpr.
Require Import KMap.
Require Import SmodeCorePt SRegime.
Require Import HartLift HartSpan HartSpanChar HartSwp HartSFrame HartSMem.
Require Import WpSmodePtEngine WpSmodePtFetch.
Require Import KptShare KptGoodb.
Require Import WpIntrInv.
Require Import HartMemRun.
Require Import DiskPtsto WpUart WpSmodeUart WpSmodePtUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SpecUart.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

Module UartProof : UART.

Section ProofUart.
Context `{!riscvGS Σ, !xv6G Σ}.
Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Lemma wp_sb_uart_uinv_s_sconf (γd : uart_names)
    (off : Z)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64)
    : wp_sb_uart_uinv_s_sconf_body kt γd off pc is_rvc rs2 rs1 imm m n R S b p.
  Proof.
    cbv beta delta [wp_sb_uart_uinv_s_sconf_body].
    intros ea a8 storebyte lppn Hoff Hcanon Hvpn_def Hpa.
    (* COLLAPSE [a8] INTO [ea] FIRST.  Every premise is stated at [a8] while
       every engine argument below wants [ea]; leaving the two spellings
       apart makes the [ktier_pin] argument fail to unify. *)
    assert (Ha8ea : a8 = ea)
      by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
    rewrite Ha8ea in Hcanon, Hvpn_def, Hpa.
    assert (Heapa : ea = uart_pa off).
    { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry.
      apply zero_extend'_id. }
    assert (Hdevvpn : kpt_dev_vpn (svpn_of ea)).
    { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
      assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity).
      lia. }
    (* the device window's own claim, off [hw_config]'s STATIC bundle: a
       device page is mapped by the kernel table at every tier, so nothing
       here has to open an invariant to learn its [ppn]. *)
    assert (Hdevstatic : kmap_static (svpn_of ea) KP_rw)
      by (apply kmap_class_rw; right; exact Hdevvpn).
    pose proof (static_canon_lo ea KP_rw Hdevstatic Hcanon) as Healt.
    pose proof (pa_of_id ea Healt) as Hpaid.
    assert (Halignv : is_aligned_vaddr (Virtaddr ea) 1 = true)
      by (unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity).
    assert (Halignp : is_aligned_paddr
              (Physaddr (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)) 1 = true)
      by (rewrite <- is_aligned_vaddr_paddr; unfold is_aligned_vaddr;
          rewrite Z.rem_1_r; reflexivity).
    assert (Hdcls : dev_cls 1 (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)).
    { rewrite Hpaid Heapa. split; [ exact (dev_addr_uart off Hoff) | ].
      split; [ exact (uart_pa_not_in_clint off Hoff) | ].
      exact (uart_pa_access_io off 1 Hoff (pma_width_ok 1 eq_refl eq_refl)). }
    iIntros "Hcg Hpc #Hinstr #Huinv HR Hacc Hcont".
    iApply (wp_instr_s_sconf m n b b pc is_rvc
              (STORE (imm, Regidx rs2, Regidx rs1, 1))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 (⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                  ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗ S)%I)
              with "Hcg Hpc Hinstr [HR Hacc Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HR Hacc".
    - (* ---------------- THE INSTRUCTION ---------------- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
        by exact (src_ok_rget_indep m rs1 CID CID0).
      assert (Lpin_rs2 : tp_pin (CID := CID) m !!! Regidx rs2 = rget m rs2)
        by exact (src_ok_rget_indep m rs2 CID CID0).
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
          Hmdl & Hmenv)".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
         [WpIntrInv.sda_slot_acc] below, the one place the two translation
         arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      iDestruct "Hkmapb" as "[#Hkmst #Hgcert]".
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
             [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
      iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                   pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
        as (SD satp0 tlbv pcfg paddr)
        "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR1 & Hcov).
      iAssert (sr_swp_res (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (STORE (imm, Regidx rs2, Regidx rs1, 1)))
        with (execute_STORE imm (Regidx rs2) (Regidx rs1) 1).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                      (sign_extend' 64 imm) = ea)
        by (rewrite Lpin_rs1; reflexivity).
      pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
      pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
      pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
      assert (Lsv : autocast (T := mword)
                (subrange_vec_dec (tp_pin (CID := CID) m !!! Regidx rs2)
                   (Z.sub (Z.mul 1 8) 1) 0) = storebyte)
        by (rewrite Lpin_rs2; reflexivity).
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
              = true) by (rewrite Lmst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
              = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
              by (rewrite Lmst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
              = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
              by (rewrite Lsatp;
                  exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
      assert (Lep : effectivePrivilege (Store Data) (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
              = returnM Supervisor)
              by (rewrite Lmst;
                  exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ iApply (swp_execute_STORE_dev_S1 (CID := CID)
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs2 rs1 (tp_pin (CID := CID) m)
                    (pa_of (kpt_leaf_ppn (svpn_of ea)) ea) storebyte
                    pmar0 pcfg paddr
                    S (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Lsv
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                    (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                    (sda_rs_htif _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Store Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                    Lep
                    HA Hord HW Hcov (pma_all_io Hpma_all) Hdcls
                    ltac:(rewrite Hea; exact Halignv)
                    Halignp
                    with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HR Hacc]").
          - (* the data translation, off the STATIC device claim *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            iApply ("Htrobl" $! KT0 (Store Data) KP_rw
                      ea (kpt_leaf_ppn (svpn_of ea)) rr
                      with "[%] [%] [%] [%] [%] Hwit [] Hcert
                      Hfrag HRes Hrw Hro").
            + apply _.
            + exact (or_intror (or_intror (or_introl eq_refl))).
            + exact eq_refl.
            + exact Healt.
            + exact Hpaid.
            + iApply (kmap_static_claims_at (svpn_of ea) KP_rw
                        Hdevstatic with "Hkmst").
          - (* the UART WRITE node: the device invariant, opened HERE *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
            iInv "Huinv" as ">Hdbody" "Hdclose".
            iDestruct "Hdbody" as (u) "(Huf & Hg)".
            iDestruct (uart_agree with "Hua Huf") as %Hduart.
            destruct (uart_write_total u off storebyte Hoff) as [u' Hwrite_u].
            iMod (dev_interp_update_uart sigma.(mdev) u u'
                    with "[$Hua $Hpldev $Hvdev] Huf") as "[Hdev' Huf']".
            iMod ("Hacc" $! u u' with "[//] Hg HR") as "[Hg' HS]".
            iMod ("Hdclose" with "[Huf' Hg']") as "_".
            { iNext. iExists u'. iFrame. }
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iExists (set_duart sigma.(mdev) u').
            iSplitR.
            { iPureIntro. rewrite Hpaid Heapa.
              apply (dev_write_uart sigma.(mdev) off storebyte u' Hoff).
              rewrite <- Hduart. exact Hwrite_u. }
            iNext. iMod "Hb2" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev' HS". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & HS & Hfrag)".
      iSplitR; [done|].
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (CID := CID)
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
                 hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 strans_res_at (CID := CID) satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tlbv. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (register_set tlb tvx
                      (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
        "(Htr & Hms & Hpriv & Hmenv)".
      iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0, m, n.
      iFrame "HPC HnPC".
      iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
        iPureIntro. split; assumption. }
      iSplitL "Htr Hstk Harm".
      { rewrite /sie_cap. iFrame "Hstk Htr Harm Hwit". }
      iFrame "Hfile HS". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & HS)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! CID with "[%] Hcg' Hpc' HS"). exact Hs.

Qed.

  (* The bundle-taking RESTATEMENT of the accessor leaf above, statement
     verbatim, proof one projection out of [dev_inv]. *)
  Lemma wp_sb_uart_s_sconf (γd : uart_names) (γv : disk_names)
    (off : Z)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64)
    : wp_sb_uart_s_sconf_body kt γd γv off pc is_rvc rs2 rs1 imm m n R S b p.
  Proof.
    cbv beta delta [wp_sb_uart_s_sconf_body].
    intros ea a8 storebyte lppn Hoff Hcanon Hvpn_def Hpa.
    iIntros "Hcg Hpc Hinstr #Hdinv HR Hacc Hcont".
    iDestruct (dev_inv_uart with "Hdinv") as "#Huinv".
    iApply (wp_sb_uart_uinv_s_sconf γd off pc is_rvc rs2 rs1 imm m n R S b p
              Hoff Hcanon Hvpn_def Hpa
              with "Hcg Hpc Hinstr Huinv HR Hacc Hcont").
  Qed.

  Lemma wp_lb_uart_s_sconf (γd : uart_names) (γv : disk_names)
    (off : Z)
    (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
    (m : regfile) (n : nat) (R : iProp Σ) (S : bv 8 -> iProp Σ) (b : bool) (p : mword 64)
    : wp_lb_uart_s_sconf_body kt γd γv off pc is_rvc is_unsigned rd rs1 imm m n R S b p.
  Proof.
    cbv beta delta [wp_lb_uart_s_sconf_body].
    intros ea a8 ldval lppn Hoff Hrd Hrdok Hcanon Hvpn_def Hpa.
    rdok_split Hrdok.
    (* COLLAPSE [a8] INTO [ea] FIRST -- see the store leaf above. *)
    assert (Ha8ea : a8 = ea)
      by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
    rewrite Ha8ea in Hcanon, Hvpn_def, Hpa.
    assert (Heapa : ea = uart_pa off).
    { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry.
      apply zero_extend'_id. }
    assert (Hdevvpn : kpt_dev_vpn (svpn_of ea)).
    { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
      assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity).
      lia. }
    assert (Hdevstatic : kmap_static (svpn_of ea) KP_rw)
      by (apply kmap_class_rw; right; exact Hdevvpn).
    pose proof (static_canon_lo ea KP_rw Hdevstatic Hcanon) as Healt.
    pose proof (pa_of_id ea Healt) as Hpaid.
    assert (Halignv : is_aligned_vaddr (Virtaddr ea) 1 = true)
      by (unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity).
    assert (Halignp : is_aligned_paddr
              (Physaddr (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)) 1 = true)
      by (rewrite <- is_aligned_vaddr_paddr; unfold is_aligned_vaddr;
          rewrite Z.rem_1_r; reflexivity).
    assert (Hdcls : dev_cls 1 (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)).
    { rewrite Hpaid Heapa. split; [ exact (dev_addr_uart off Hoff) | ].
      split; [ exact (uart_pa_not_in_clint off Hoff) | ].
      exact (uart_pa_access_io off 1 Hoff (pma_width_ok 1 eq_refl eq_refl)). }
    iIntros "Hcg Hpc #Hinstr #Hdinv HR Hacc Hcont".
    iDestruct (dev_inv_uart with "Hdinv") as "#Huinv".
    iApply (wp_instr_s_sconf m n b b pc is_rvc
              (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))
              (fun (_CIDx : CpuId) npc _ms' m' n' =>
                 (∃ bt : bv 8,
                    ⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                    ⌜m' = <[Regidx rd := regval_into_reg (ldval bt)]> m⌝ ∗
                    ⌜n' = n⌝ ∗ S bt)%I)
              with "Hcg Hpc Hinstr [HR Hacc Hcont]").
    iNext.
    rename CID into CID0.
    iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HR Hacc".
    - (* ---------------- THE INSTRUCTION ---------------- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
        by exact (src_ok_rget_indep m rs1 CID CID0).
      iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
          Hmdl & Hmenv)".
      pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                          HMPP & HTVM).
      (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
         [WpIntrInv.sda_slot_acc] below, the one place the two translation
         arms are told apart. *)
      iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
      iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
          %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
          %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0.
      iDestruct "Hkmapb" as "[#Hkmst #Hgcert]".
      (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
             [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
      iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                   pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                   with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
        as (SD satp0 tlbv pcfg paddr)
        "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
      destruct Hpok as (HA & Hord & HX & HW & HR1 & Hcov).
      iAssert (sr_swp_res (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
        with "[HRes]" as "HRes".
      { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
        rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
      iDestruct "Hresv" as (rr) "Hfrag".
      change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)))
        with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 1).
      assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                      (sign_extend' 64 imm) = ea)
        by (rewrite Lpin_rs1; reflexivity).
      pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
      pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
      pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
      assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
              = true) by (rewrite Lmst; exact HMXR).
      assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
              = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
      assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
              by (rewrite Lmst; exact HSXL).
      assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
                (register_lookup satp
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
              = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
              by (rewrite Lsatp;
                  exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
      assert (Lep : effectivePrivilege (Load Data) (register_lookup mstatus
                (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
              = returnM Supervisor)
              by (rewrite Lmst;
                  exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
      iApply (swp_mono (CID := CID)
                with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
      2:{ iApply (swp_execute_LOAD_dev_S1_ex (CID := CID)
                    SD sda_Dro (sda_Df (DfracOwn 1))
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                    imm rs1 rd is_unsigned (tp_pin (CID := CID) m)
                    (pa_of (kpt_leaf_ppn (svpn_of ea)) ea)
                    pmar0 pcfg paddr
                    S (Mobl_dev1_ex (pa_of (kpt_leaf_ppn (svpn_of ea)) ea) S)
                    (sr_swp_res (strans_regime (CID := CID))) rr
                    (sr_swp_mode (strans_regime (CID := CID)) satp0)
                    Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                    (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                    (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                    (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                    (sda_rs_paddr _ _ _ _ _ _ _)
                    Lmxr Lpmm Lsxl
                    (hval_transform_effective_address_S_mode
                       (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                          (sign_extend' 64 imm))
                       (Load Data)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                       (sda_rs_priv _ _ _ _ _ _ _)
                       Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                    (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                       (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                       (sr_swp_mode (strans_regime (CID := CID)) satp0)
                       (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                    Lep
                    HA Hord HR1 Hcov (pma_all_io Hpma_all) Hdcls
                    ltac:(rewrite Hea; exact Halignv)
                    Halignp Hrd
                    (swp_dev_read_node1_ex (CID := CID)
                       (pa_of (kpt_leaf_ppn (svpn_of ea)) ea) S (proj1 Hdcls))
                    with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HR Hacc]").
          - (* the data translation, off the STATIC device claim *)
            iIntros "Hfrag HRes Hrw Hro".
            rewrite Hea.
            iApply ("Htrobl" $! KT0 (Load Data) KP_rw
                      ea (kpt_leaf_ppn (svpn_of ea)) rr
                      with "[%] [%] [%] [%] [%] Hwit [] Hcert
                      Hfrag HRes Hrw Hro").
            + apply _.
            + exact (or_intror (or_introl eq_refl)).
            + exact I.
            + exact Healt.
            + exact Hpaid.
            + iApply (kmap_static_claims_at (svpn_of ea) KP_rw
                        Hdevstatic with "Hkmst").
          - (* the UART READ node: the device invariant, opened HERE.  The
               VALUE is existential -- it comes from the device, not from a
               points-to, so no leaf can name it before the step. *)
            iIntros (sigma) "Hsi".
            iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
            iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
            iInv "Huinv" as ">Hdbody" "Hdclose".
            iDestruct "Hdbody" as (u) "(Huf & Hg)".
            iDestruct (uart_agree with "Hua Huf") as %Hduart.
            destruct (uart_read_total u off Hoff) as (bt & u' & Hread_u).
            iMod (dev_interp_update_uart sigma.(mdev) u u'
                    with "[$Hua $Hpldev $Hvdev] Huf") as "[Hdev' Huf']".
            iMod ("Hacc" $! u bt u' with "[//] Hg HR") as "[Hg' HS]".
            iMod ("Hdclose" with "[Huf' Hg']") as "_".
            { iNext. iExists u'. iFrame. }
            iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
            iModIntro. iExists bt, (set_duart sigma.(mdev) u').
            iSplitR.
            { iPureIntro. rewrite Hpaid Heapa.
              apply (dev_read_uart sigma.(mdev) off bt u' Hoff).
              rewrite <- Hduart. exact Hread_u. }
            iNext. iMod "Hb2" as "_". iModIntro.
            iFrame "Hreg Hmem Hdev' HS". }
      (* ---- the post ---- *)
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (bt) "(Hfile & Hland)".
      iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & HS)".
      iSplitR; [done|].
      iAssert (∃ tv2 : type_of_register tlb,
                 hreg_frame (CID := CID)
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
                 hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
                 strans_res_at (CID := CID) satp0 tv2)%I
        with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
      { destruct Hshape as [-> | (tvx & ->)].
        - iExists tlbv. iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
                 sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
        - iExists tvx.
          iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
          iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                       pcfg paddr tlbv tvx) with "Hro") as "Hro".
          iFrame "Hrw Hro".
          iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                   (register_set tlb tvx
                      (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
                 register_lookup_set) in "HRes".
          rewrite irrelevant_register_set; [| vm_compute; reflexivity].
          rewrite sda_rs_satp. iExact "HRes". }
      (* the slot re-seals itself, at the landing tlb value *)
      iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
        "(Htr & Hms & Hpriv & Hmenv)".
      iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0,
              (<[Regidx rd := regval_into_reg (ldval bt)]> m), n.
      iFrame "HPC HnPC Hany".
      iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      { rewrite /sconf_at_priv. iExists mdv0.
        iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
        iPureIntro. split; assumption. }
      assert (Hsp : m !!! Regidx csp_rs1
                    = <[Regidx rd := regval_into_reg (ldval bt)]> m
                        !!! Regidx csp_rs1)
        by (symmetry; apply upd_ne; congruence).
      iSplitL "Htr Hstk Harm".
      { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Hwit". }
      iSplitL "Hfile".
      { iEval (rewrite (tp_pin_upd m rd (regval_into_reg (ldval bt))
                          (rd_ok_tp _ Hrdok))) in "Hfile".
        iExact "Hfile". }
      iExists bt. iFrame "HS". iPureIntro. split_and!; reflexivity.
    - (* ---------------- THE CONTINUATION ---------------- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
      iDestruct "Hpay" as (bt) "(-> & -> & -> & HS)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iSpecialize ("Hcont" $! CID with "[%]"); [ exact Hs | ].
      iApply ("Hcont" $! bt with "Hcg' Hpc' HS").

Qed.

End ProofUart.

End UartProof.

(* ProofUart.v: the UART device leaves over the SIE-agnostic v2 bundle
   ([sconf] + [sie_cap], stage-5 straggler of the interrupt sweep).

   These are the accessor-form device leaves of WpSmodePtUart rebased on
   the funnel [wp_instr_s_sconf]: [dev_inv] is opened across the funnel
   callback's own step (devN is disjoint from minstretN AND intrN, so
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
Require Import WpLoad WpGpr WpMmodeLeafBase.
Require Import RegFile HartTp.
Require Import KptPt.
Require Import SmodeCore WpSmodeGpr.
Require Import KMap.
Require Import SmodeCorePt SRegime.
Require Import DiskPtsto WpUart WpSmodeUart WpSmodePtUart.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SpecUart.
Import Defs.

Module UartProof : UART.

Section ProofUart.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{!uartGhostG Σ, !diskGhostG Σ}.
Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_sb_uart_uinv_s_sconf (γd : uart_names)
    (off : Z)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64)
    : wp_sb_uart_uinv_s_sconf_body γd off pc is_rvc rs2 rs1 imm m n R S b p.
  Proof.
    cbv beta delta [wp_sb_uart_uinv_s_sconf_body].
  intros ea a8 storebyte lppn Hoff Hcanon Hvpn_def Hpa.
  iIntros "Hcg Hpc Hinstr #Huinv HR Hacc Hcont".
  assert (Ha8pa : a8 = uart_pa off).
  { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry. apply zero_extend'_id. }
  assert (Hdevvpn : kpt_dev_vpn (svpn_of a8)).
  { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
    assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia. }
  assert (Hident_pt : zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
            (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
  { assert (Hds : kmap_static (svpn_of a8) KP_rw) by (apply kmap_class_rw; right; exact Hdevvpn).
    pose proof (pa_of_id a8 (static_canon_lo a8 KP_rw Hds Hcanon)) as Hpid.
    unfold pa_of in Hpid. exact Hpid. }
  iApply (wp_instr_s_sconf m n b pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 1))
            with "Hcg Hpc Hinstr").
  (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
  rename CID into CID0.
  iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  (* THE READS CROSS THE REBINDING: [Lva]/[Lv2] below read the file the
     callback delivered -- the REBOUND hart's pin -- while the statement's
     [ea] is spelled at the entry hart's [rget m rs].  The [SrcOk] classes
     say the words are the same. *)
  assert (Lpin_rs1 : tp_pin (CID := CID) m (Regidx rs1) = rget m rs1)
    by exact (src_ok_rget_indep m rs1 CID CID0).
  assert (Lpin_rs2 : tp_pin (CID := CID) m (Regidx rs2) = rget m rs2)
    by exact (src_ok_rget_indep m rs2 CID CID0).
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all (uart_pa off) 1
             (uart_pa_access_io off 1 Hoff (pma_width_ok 1 eq_refl eq_refl))) as (region_st & Hmatch_st & _ & Hwrite_st).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
  (* only the UART half of the fabric is touched *)
  iInv "Huinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u) "(Huf & Hg)".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  destruct (uart_write_total u off storebyte Hoff) as [u' Hwrite_u].
  iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value (CID := CID) rs2 (tp_pin (CID := CID) m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform (CID := CID) strans_regime (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iDestruct (sr_tmode (CID := CID) strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb (CID := CID) strans_regime (Store Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_intror (or_introl eq_refl))) eq_refl Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_uart : dev_write s_tr.(mdev) (uart_pa off) 1 storebyte = Some (set_duart σ.(mdev) u')).
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
    apply (dev_write_uart σ.(mdev) off storebyte u' Hoff). rewrite <- Hduart. exact Hwrite_u. }
  assert (Htr_uart : exec (translateAddr (Virtaddr a8) (Store Data)) s_pc
                     = Some (Ok (Physaddr (uart_pa off), PBMT_PMA, init_ext_ptw), s_tr)).
  { replace (uart_pa off) with a8 by exact Ha8pa. exact Htr0. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_1_gpr_S_walk_dev_pt rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; exact Htr_uart)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva ?Lpin_rs1 Hpa; exact Hmatch_st)
               Hwrite_st
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply dev_addr_uart; exact Hoff)
               ltac:(rewrite !Lva ?Lpin_rs1 !Lv2 ?Lpin_rs2 Hpa; exact Hwr_uart)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev $Hvdev] Huf") as "[Hdev' Huf']".
  iMod ("Hacc" $! u u' with "[//] Hg HR") as "[Hg' HS]".
  iMod ("Hdclose" with "[Huf' Hg']") as "_".
  { iNext. iExists u'. iFrame. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iAssert (sconf (CID := CID)) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap (CID := CID) m n b p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
     obligation is discharged by instantiating it here. *)
  iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc] HS").
  iPureIntro. exact Hs.
Qed.

  (* The bundle-taking RESTATEMENT of the accessor leaf above, statement
     verbatim, proof one projection out of [dev_inv]. *)
  Lemma wp_sb_uart_s_sconf (γd : uart_names) (γv : disk_names)
    (off : Z)
    (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) (R S : iProp Σ) (b : bool) (p : mword 64)
    : wp_sb_uart_s_sconf_body γd γv off pc is_rvc rs2 rs1 imm m n R S b p.
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
    : wp_lb_uart_s_sconf_body γd γv off pc is_rvc is_unsigned rd rs1 imm m n R S b p.
  Proof.
    cbv beta delta [wp_lb_uart_s_sconf_body].
  intros ea a8 ldval lppn Hoff Hrd Hrdok Hcanon Hvpn_def Hpa.
  pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
  pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
  iIntros "Hcg Hpc Hinstr #Hdinv HR Hacc Hcont".
  assert (Ha8pa : a8 = uart_pa off).
  { rewrite <- Hpa. change (0 * 1) with 0. rewrite avi0. symmetry. apply zero_extend'_id. }
  assert (Hdevvpn : kpt_dev_vpn (svpn_of a8)).
  { unfold svpn_of. rewrite Hvpn_def. unfold kpt_dev_vpn.
    assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia. }
  assert (Hident_pt : zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a8))
            (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
  { assert (Hds : kmap_static (svpn_of a8) KP_rw) by (apply kmap_class_rw; right; exact Hdevvpn).
    pose proof (pa_of_id a8 (static_canon_lo a8 KP_rw Hds Hcanon)) as Hpid.
    unfold pa_of in Hpid. exact Hpid. }
  iApply (wp_instr_s_sconf m n b pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))
            with "Hcg Hpc Hinstr").
  (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
  rename CID into CID0.
  iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  (* THE READS CROSS THE REBINDING: [Lva]/[Lv2] below read the file the
     callback delivered -- the REBOUND hart's pin -- while the statement's
     [ea] is spelled at the entry hart's [rget m rs].  The [SrcOk] classes
     say the words are the same. *)
  assert (Lpin_rs1 : tp_pin (CID := CID) m (Regidx rs1) = rget m rs1)
    by exact (src_ok_rget_indep m rs1 CID CID0).
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all (uart_pa off) 1
             (uart_pa_access_io off 1 Hoff (pma_width_ok 1 eq_refl eq_refl))) as (region_ld & Hmatch_ld & Hread_ld & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq (CID := CID) with "Hreg Hmisa") as %Lmisa.
  iDestruct "Hdev" as "(Hua & Hpldev & Hvdev)".
  (* only the UART half of the fabric is touched, and [↑uartN ⊆ ↑devN] *)
  iDestruct (dev_inv_uart with "Hdinv") as "#Huinv".
  iInv "Huinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (u) "(Huf & Hg)".
  iDestruct (uart_agree with "Hua Huf") as %Hduart.
  destruct (uart_read_total u off Hoff) as (bt & u' & Hread_u).
  iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value (CID := CID) rs1 (tp_pin (CID := CID) m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform (CID := CID) strans_regime (Load Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iDestruct (sr_tmode (CID := CID) strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb (CID := CID) strans_regime (Load Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_introl eq_refl)) I Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hdrd_uart : dev_read s_tr.(mdev) (uart_pa off) 1 = Some (bt, set_duart σ.(mdev) u')).
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
    apply (dev_read_uart σ.(mdev) off bt u' Hoff). rewrite <- Hduart. exact Hread_u. }
  assert (Htr_uart : exec (translateAddr (Virtaddr a8) (Load Data)) s_pc
                     = Some (Ok (Physaddr (uart_pa off), PBMT_PMA, init_ext_ptw), s_tr)).
  { replace (uart_pa off) with a8 by exact Ha8pa. exact Htr0. }
  pose (d' := set_duart σ.(mdev) u').
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) d') (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ldval bt))).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_1_gpr_S_walk_dev rs1 rd imm is_unsigned bt d' region_ld s_pc s_tr
             Hrd Htea
             ltac:(unfold is_aligned_vaddr; rewrite Z.rem_1_r; reflexivity)
             md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; exact Htr_uart)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply uart_pmp_match1; [exact Hoff | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva ?Lpin_rs1 Hpa; exact Hmatch_ld)
             Hread_ld
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_clint_false; [apply uart_pa_not_in_clint; exact Hoff | lia])
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_sig_false; [apply uart_pa_not_in_sig; exact Hoff | lia])
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; apply dev_addr_uart; exact Hoff)
             ltac:(rewrite !Lva ?Lpin_rs1 Hpa; exact Hdrd_uart)). }
  iMod (dev_interp_update_uart σ.(mdev) u u' with "[$Hua $Hpldev $Hvdev] Huf") as "[Hdev' Huf']".
  iMod ("Hacc" $! u bt u' with "[//] Hg HR") as "[Hg' HS]".
  iDestruct (gpr_file_insert_acc (tp_pin (CID := CID) m) (Regidx rd) (regval_into_reg (ldval bt)) with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz (CID := CID) rd _ Hrd).
  iMod (reg_update (CID := CID) _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ldval bt)) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz (CID := CID) rd _ Hrd). iExact "Hrdc". }
  iMod ("Hdclose" with "[Huf' Hg']") as "_".
  { iNext. iExists u'. iFrame. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; rewrite ?sregs_set_reg. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (ldval bt)]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iAssert (sconf (CID := CID)) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap (CID := CID) m n b p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  (* the leaf's own write commutes with the tp pin *)
  tp_refold Hrdtp "Hfmap".
  iDestruct (sie_cap_retarget (CID := CID) m
               (<[Regidx rd := regval_into_reg (ldval bt)]> m) n b Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iSpecialize ("Hcont" $! CID with "[]"); [iPureIntro; done|].
  iApply ("Hcont" $! bt with "Hcg [$Hpc' $Hnpc] HS").
Qed.

End ProofUart.

End UartProof.

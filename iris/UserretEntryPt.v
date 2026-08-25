(* UserretEntryPt.v -- the userret PAGE-TABLE SWITCH over the pt2 window
   (TransPt.v): sfence.vma ; csrw satp,a0 ; sfence.vma, as three uniform
   steps of the shared trampoline engine.  The KERNEL side is SHARED
   throughout (KptShare.kpt_inv, TransPt.v's [_kprev] family -- the mirror
   of uservec's [_kcur]: here the kernel table plays the PREVIOUS slot,
   since the switch installs the USER root as current): nothing about the
   kernel table is threaded in or out beyond the ordinary [tlb_res_pt]
   residue steps 0-1 already run against.

     step 1 (SHARED kernel table): the sfence flushes the TLB; [tlb_res_pt]
       re-seals with [tlb_ok_pt_empty].
     step 2 (SHARED kernel table): the csrw installs the user root; the
       kernel residue DISSOLVES into the two-table window invariant
       [tlb_inv_pt2_kprev] ([tlb_inv_pt2_kprev_enter], a plain wand -- no
       ownership ever leaves [kpt_inv]) -- the freshly parked user table
       arrives as [pt_frame], every resident TLB entry is kernel-provenance.
     step 3 (window invariant): the fetch itself is absorbed by
       [tlb_inv_pt2_kprev] (a hit on a stale kernel-provenance trampoline
       entry -- same physical page -- may Svadu-write-back into the
       KERNEL tree through the cached pteAddr, opened from [kpt_inv] for
       the span of this one call; a miss walks the USER tree); then the
       sfence flushes the TLB, the window EXITS ([tlb_inv_pt2_kprev_exit]):
       the kernel side folds back into [kpt_inv] with nothing to return,
       and the user invariant [utlb_inv_pt] seals.

   PER NODE, TWO OF THE FOUR STEPS DRIVE [TrampStepPt.wp_instr_tramp_pt]
   DIRECTLY rather than through a table wrapper, because they MOVE the
   residue and a wrapper's [_swp_close] would seal it back where it came
   from:

   - step 2 changes satp, so the engine's landing satp is [usatp] while its
     running one is the kernel's.  The kernel residue itself
     ([SRegime.kpt_res_at]) does not mention satp, so it is the SAME [Res]
     in and out; the window is entered in the engine's CONTINUATION, off
     the cells it hands back.
   - step 3 changes the RESIDUE: the flush is what turns two-table TLB
     coherence back into one-table coherence, and per node that fact is
     generated inside the [swp] obligation.  Sealing the tlb cell into
     [tlb_inv_pt2_kprev] first would discard it (the invariant is
     existential in the tlb value -- the "do not re-seal the tlb cell"
     rule).  So the step runs at [Res := pt2_res_kprev] and
     [Res1 := upt_res_pt], and the continuation is one [upt_swp_close]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import RegFile.
Require Import WpGpr WpGprCsrwB.
Require Import SmodePte PtTree PtTreeAdue.
Require Import KptExecMap.
Require Import UptTree.
Require Import HartSpan HartSwp.
Require Import WpDecodeBridge WpMmodeSwpBase WpMmodeJump WpMmodeCsrSwp
        HartSCsr.
Require Import WpSmodePtEngine.
Require Import WpSconfSfence WpSconfCsr WpSconfEngine.
Require Import SRegime TrampStepPt UptWalkPt TransPt Pt2WalkPt KptShare.
Require Import UserretDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UserretEntryPt.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_userret_entry_pt (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64))
      (m : regfile) (usatp : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    (* S-mode config *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_TVM mstatus0) ('b"1") = false ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    upt_map_wf um ->
    (* a0 holds the USER satp value *)
    m !!! Regidx (mword_of_int 10) = usatp ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    (* stage C: the trampoline claim (held post-switch); the three switch
       instructions fetch through the kernel table's trampoline mapping *)
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    tlb_res_pt kroot -∗
    pt_frame (upt_tree_spec uroot tfp um) -∗
    pc_is (uva 0x9c) -∗
    gpr_file m -∗
    instr (upa 0x9c) false ai_fencei -∗
    instr (upa 0xa0) false ai_sfence -∗
    instr (upa 0xa4) false ai_csrw -∗
    instr (upa 0xa8) false ai_sfence -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      utlb_inv_pt uroot tfp um -∗
      pc_is (uva 0xac) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwf Ha0 HuMode Huasid Huppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv #Hclaim Hktlb Hufr Hpc
             Hfmap Hi0 Hi1 Hi2 Hi3 Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0 mseccfg0.
    assert (Hva00 : add_vec_int (uva 0x9c) 4 = uva 0xa0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva01 : add_vec_int (uva 0xa0) 4 = uva 0xa4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva02 : add_vec_int (uva 0xa4) 4 = uva 0xa8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva03 : add_vec_int (uva 0xa8) 4 = uva 0xac)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ===== STEP 0: fence.i -- flush the icache after the text swap.
       Unlike the sfence below this touches no architectural state: the
       Sail model retires it as the identity, so there is no TLB cell to
       re-seal and no privilege side condition to discharge. ============ *)
    iApply (wp_instr_ktramp_pt_share kroot (uva 0x9c) (upa 0x9c) false ai_fencei
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0xa0⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hclaim Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc Hi0
                    [] [Hufr Hfmap Hi1 Hi2 Hi3 Hcont]").
    { iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      change (execute ai_fencei)
        with (execute (FENCEI (zeros' 12, zreg, zreg))).
      iApply (swp_mono with
                "[Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk
                  HPC HnPC Hresv] [-]").
      2:{ iApply (swp_execute_FENCEI_s (zeros' 12) zreg zreg with "Hcert"). }
      iIntros (e) "->".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva00 |]. iSplitR; [done|]. done. }
    iNext. iIntros (npc0 ms10 mdv10)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc (-> & -> & ->)".
    (* ============ STEP 1: sfence.vma under the kernel invariant ======== *)
    iApply (wp_instr_ktramp_pt_share kroot (uva 0xa0) (upa 0xa0) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0xa4⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hclaim Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc Hi1
                    [] [Hufr Hfmap Hi2 Hi3 Hcont]").
    { iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct "HRes" as "[Hsnap #Hkinv]".
      iDestruct "Hsnap" as (t0) "[%Hokt0 #Hlb0]".
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'
                   with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      assert (LTVM : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 ('b"1") = false)
        by (rewrite sda_rs_mst; exact HTVM).
      change (execute ai_sfence)
        with (execute (SFENCE_VMA (zreg, zreg))).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC] [-]").
      2:{ iApply (swp_execute_SFENCE_VMA_S_gen sda_Drw sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    sda_disj sda_in_priv sda_in_mst sda_w_tlb
                    (sda_rs_priv mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')
                    LTVM with "Hcert Hresv Hrw Hro"). }
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (rsf tvz) "(%Hag & %Hnone & Hrw & Hro & Hresv)".
      pose proof (reg_agree_trans (sda_Drw ∪ sda_Dro) _ _ _ Hag
                    (sda_set_tlb mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'
                       tvz)) as Hag2.
      iDestruct (sda_rw_ext _ _ Hag2 with "Hrw") as "Hrw".
      iDestruct (sda_ro_ext (sda_Df dq) _ _ Hag2 with "Hro") as "Hro".
      iDestruct (sda_frames_out dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tvz
                   with "[$Hrw $Hro]")
        as "(Htlbc & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg & Hpaddr & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc".
      { iExists tvz. iFrame "Htlbc". rewrite /kpt_res_at. iFrame "Hkinv".
        iExists t0. iFrame "Hlb0". iPureIntro.
        exact (tlb_ok_pt_empty (mword_of_int 0) t0 tvz
                 (fun vpn' => Hnone _ (tlb_hash_range vpn'))). }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva01 |]. iSplitR; [done|]. done. }
    iNext. iIntros (npc1 ms11 mdv11)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc (-> & -> & ->)".
    (* ============ STEP 2: csrw satp,a0 -- ENTER the window =============
       The kernel residue does not mention satp, so this is an ORDINARY
       [Res]-preserving step of the raw engine at a MOVED landing satp; the
       window is entered in its continuation. ============================ *)
    assert (Hcw2 : cw2_ok satp mstatus).
    { rewrite /cw2_ok /cw_fresh. split_and!;
        first [ vm_compute; reflexivity | intros HX; discriminate HX ]. }
    iDestruct (kpt_swp_open kroot with "Hktlb") as (satp2 tlbv2 pcfg2 paddr2)
      "(%Hsok2 & %Hpok2 & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    pose proof Hpok2 as (HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
    assert (Hleg2 : satp_legalized satp2 (m !!! Regidx (mword_of_int 10 : mword 5))
                    = usatp)
      by (rewrite Ha0; exact (satp_legalized_sv39 satp2 usatp HuMode)).
    iApply (wp_instr_tramp_pt (kpt_res_at kroot satp2) (kpt_res_at kroot satp2)
              (uva 0xa4) (upa 0xa4) false ai_csrw
              mstatus0 mie_v mdv0 menvcfg0 satp2 pcfg2 paddr2 tlbv2
              mie_v menvcfg0 usatp pcfg2 paddr2 Supervisor
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0xa8⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file m)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hpok2
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                    Htlbc HRes Hpc Hi2 [] [Hfmap] [Hufr Hi3 Hcont]").
    { iApply (ktramp_fetch_tr_share kroot dq (uva 0xa4) mstatus0 satp2 mie_v
                mdv0 menvcfg0 pcfg2 paddr2 Hmenvval0 HSXL HMPRV Hsok2 Hpok2
                with "Hclaim Hhw"). }
    { iIntros (tv') "%Hpok3
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct (pw2_frames_in Supervisor dq dq satp satp2 mstatus mstatus0
                   Hcw2 with "Hsatp Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      assert (LTVM2 : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (pw2_rs Supervisor satp satp2 mstatus mstatus0))) ('b"1")
                 = false)
        by (rewrite (pw2_rs_r2 Supervisor satp satp2 mstatus mstatus0);
            exact HTVM).
      change (execute ai_csrw)
        with (execute_CSRReg csr_satp (Regidx (mword_of_int 10 : mword 5))
                zreg CSRRW).
      iApply (swp_mono with
                "[Hmie Hmdl Hmenv Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
                  Hresv] [Hrw Hro Hfmap]").
      2:{ iApply (swp_execute_CSRReg_w_p (cw_Drw satp) (cw2_Dro mstatus)
                    (cw2_Df dq dq mstatus)
                    (pw2_rs Supervisor satp satp2 mstatus mstatus0)
                    (pw2_rs Supervisor satp
                       (satp_legalized satp2
                          (m !!! Regidx (mword_of_int 10 : mword 5)))
                       mstatus mstatus0)
                    m csr_satp Supervisor (mword_of_int 10)
                    (satp_legalized satp2
                       (m !!! Regidx (mword_of_int 10 : mword 5)))
                    (cw2_disj satp mstatus Hcw2) (cw2_in_priv satp mstatus)
                    (pw2_rs_priv Supervisor satp satp2 mstatus mstatus0 Hcw2)
                    ltac:(by vm_compute)
                    (hval_check_CSR_result_satp_S_w
                       (cw_Drw satp ∪ cw2_Dro mstatus) (cw_Drw satp)
                       (pw2_rs Supervisor satp satp2 mstatus mstatus0)
                       (cw2_in_priv satp mstatus) (cw2_in_sec satp mstatus)
                       (cw2_in_misa satp mstatus) (cw2_in_r2 satp mstatus)
                       LTVM2)
                    ltac:(by vm_compute) ltac:(by vm_compute)
                    ltac:(by vm_compute)
                    with "Hcert Hfmap Hrw Hro [ ]").
          iIntros "Hrw Hro".
          iApply (swp_write_CSR_satp_S dq dq satp2 mstatus0
                    (m !!! Regidx (mword_of_int 10 : mword 5)) Hcw2 HSXL
                    with "Hcert Hrw Hro"). }
      iIntros (e) "(-> & Hfmap & Hrw & Hro)".
      iDestruct (pw2_frames_out Supervisor dq dq satp
                   (satp_legalized satp2
                      (m !!! Regidx (mword_of_int 10 : mword 5)))
                   mstatus mstatus0 Hcw2 with "[$Hrw $Hro]")
        as "(Hsatp & Hms & Hpriv & _ & _)".
      iEval (rewrite Hleg2) in "Hsatp".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva02 |]. iSplitR; [done|]. iSplitR; [done|].
      iExact "Hfmap". }
    iNext. iIntros (npc2 ms12 mdv12 tv2)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hpc
       (-> & -> & -> & Hfmap)".
    (* dissolve the kernel residue into the two-table window; the kernel
       side comes entirely from [kpt_inv] (a plain wand -- no ownership
       ever left it), so no [kmap_at_lookup] against a mapping auth is
       needed here at all *)
    iDestruct "HRes" as "[Hsnap #Hkinv2]".
    iDestruct (tlb_inv_pt2_kprev_enter uroot kroot
                 (upt_tree_spec uroot tfp um) usatp tv2
                 HuMode Huasid Huppn PtTreeAdue.pma_allows_all_pte_write
                 with "Hsatp Htlbc Hsnap Hufr [Hpcfg Hpaddr] Hkinv2") as "Hpt2".
    { iApply (pmp_config_intro uroot pcfg2 paddr2 HA2 Hord2 HX2 HW2 HR2 Hcov2
                with "Hpcfg Hpaddr"). }
    (* ============ STEP 3: sfence.vma -- EXIT into the user invariant ===
       The window's residue LEAVES as the user table's: the flush is the
       fact that makes the exchange, and it is born inside the [swp]
       obligation, so the engine carries it out on [Res1]. ============== *)
    iDestruct (pt2_kprev_swp_open uroot kroot (upt_tree_spec uroot tfp um)
                 with "Hpt2") as (satp3 tlbv3 pcfg3 paddr3)
      "(%Hsok3 & %Hpok3 & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    iApply (wp_instr_tramp_pt
              (pt2_res_kprev uroot kroot (upt_tree_spec uroot tfp um))
              (upt_res_pt uroot tfp um)
              (uva 0xa8) (upa 0xa8) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 satp3 pcfg3 paddr3 tlbv3
              mie_v menvcfg0 satp3 pcfg3 paddr3 Supervisor
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0xac⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hpok3
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr
                    Htlbc HRes Hpc Hi3 [] [] [Hfmap Hcont]").
    { iApply (pt2_tramp_fetch_tr_kprev uroot kroot
                (upt_tree_spec uroot tfp um) dq (uva 0xa8) mstatus0 satp3
                mie_v mdv0 menvcfg0 pcfg3 paddr3 Hmenvval0 HSXL HMPRV Hsok3
                Hpok3 (upt_pt2_tramp_spec uroot tfp um Hwf)
                (upt_pt2_base uroot tfp um) with "Hclaim Hhw"). }
    { iIntros (tv') "%Hpok4
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct "HRes" as (tp0 tc) "(%Hok2 & %HSc & Htc & #Hlb0 & #Hkinv3)".
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3
                   tv' with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr
                             Hhtif Hmisa") as "[Hrw Hro]".
      assert (LTVM3 : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (sda_rs mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3 tv')))
                 ('b"1") = false)
        by (rewrite sda_rs_mst; exact HTVM).
      change (execute ai_sfence)
        with (execute (SFENCE_VMA (zreg, zreg))).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Htc] [-]").
      2:{ iApply (swp_execute_SFENCE_VMA_S_gen sda_Drw sda_Dro (sda_Df dq)
                    (sda_rs mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3 tv')
                    sda_disj sda_in_priv sda_in_mst sda_w_tlb
                    (sda_rs_priv mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3 tv')
                    LTVM3 with "Hcert Hresv Hrw Hro"). }
      iIntros (e) "(-> & Hpost)".
      iDestruct "Hpost" as (rsf tvz) "(%Hag & %Hnone & Hrw & Hro & Hresv)".
      pose proof (reg_agree_trans (sda_Drw ∪ sda_Dro) _ _ _ Hag
                    (sda_set_tlb mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3
                       tv' tvz)) as Hag2.
      iDestruct (sda_rw_ext _ _ Hag2 with "Hrw") as "Hrw".
      iDestruct (sda_ro_ext (sda_Df dq) _ _ Hag2 with "Hro") as "Hro".
      iDestruct (sda_frames_out dq mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3
                   tvz
                   with "[$Hrw $Hro]")
        as "(Htlbc & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg & Hpaddr & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc Htc".
      { iExists tvz. iFrame "Htlbc". iExists tc. iFrame "Htc". iPureIntro.
        split_and!;
          [ exact (tlb_ok_pt_empty (mword_of_int 0) tc tvz
                     (fun vpn' => Hnone _ (tlb_hash_range vpn')))
          | exact HSc | exact Hwf ]. }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva03 |]. iSplitR; [done|]. done. }
    iNext. iIntros (npc3 ms13 mdv13 tv3)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hpc
       (-> & -> & ->)".
    iDestruct (upt_swp_close uroot tfp um satp3 tv3 pcfg3 paddr3 Hsok3 Hpok3
                 with "Hsatp Htlbc Hpcfg Hpaddr HRes") as "Hutlb".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hfmap").
  Qed.

End UserretEntryPt.

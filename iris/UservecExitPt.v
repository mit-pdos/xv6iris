(* UservecExitPt.v -- the uservec PAGE-TABLE SWITCH back to the KERNEL
   table over the pt2 window (TransPt.v), plus the final jump into
   usertrap:

       sfence.vma x0,x0   @ uva 0x8e
       csrw satp, t1      @ uva 0x92   (t1 holds the KERNEL satp)
       sfence.vma x0,x0   @ uva 0x96
       c.jalr t0          @ uva 0x9a   (ra := uva 0x9c ; pc := t0 & ~1)

   This is the EXACT mirror of [wp_userret_entry_pt] (UserretEntryPt.v)
   with the two tables' roles swapped -- the same three-step window
   machinery -- extended with the compressed jalr.  The KERNEL side is
   SHARED throughout (KptShare.kpt_inv, TransPt.v's [_kcur] family):
   nothing about the kernel table is threaded in or out of this lemma's
   own premises/postcondition, only the ambient persistent [kpt_inv kroot].

     step 1 (USER invariant): the sfence flushes the TLB; the user
       invariant re-seals with [tlb_ok_pt_empty].
     step 2 (USER invariant): the csrw installs the kernel root; the
       user invariant DISSOLVES into the two-table window invariant
       [tlb_inv_pt2_kcur] ([tlb_inv_pt2_kcur_enter]) -- the kernel side
       comes from [kpt_inv] alone (a fresh snapshot, no ownership), every
       resident TLB entry is user-provenance.
     step 3 (window invariant): the fetch is absorbed by [tlb_inv_pt2_kcur]
       (the trampoline page is mapped by BOTH tables at the same pa; a
       kernel-provenance hit may Svadu-write-back through [kpt_inv],
       opened for the span of this one call); the sfence flushes the TLB
       and the window EXITS ([tlb_inv_pt2_kcur_exit]): the USER table
       parks as [pt_frame] and the kernel side folds back into
       [tlb_res_pt] -- nothing is resealed into an exclusive invariant.
     step 4 (SHARED kernel table): the compressed jalr links [ra] and
       jumps to [ret_pc t0], fetched through [tlb_res_pt] like any other
       ordinary kernel trampoline step.

   PER NODE, steps 2 and 3 drive [TrampStepPt.wp_instr_tramp_pt] DIRECTLY
   rather than through [UptWalkPt.wp_instr_u_pt] / [Pt2WalkPt.
   wp_instr_pt2_tramp_kcur], because they MOVE what those wrappers seal:

   - step 2 changes satp, and [wp_instr_u_pt] pins the landing satp to the
     running one.  The user residue ([UptWalkPt.upt_res_pt]) does not
     mention satp, so it is the SAME [Res] in and out and the window is
     entered in the engine's CONTINUATION, off the cells it hands back.
   - step 3 changes the RESIDUE: the flush is what turns two-table TLB
     coherence back into one-table coherence, and per node that fact is
     born inside the [swp] obligation.  Sealing the tlb cell back into
     [tlb_inv_pt2_kcur] first would discard it (the invariant is
     existential in the tlb value -- the "do not re-seal the tlb cell"
     rule), so the step runs at [Res := pt2_res_kcur] and [Res1 :=
     kpt_res_at ∗ pt_frame], and its continuation is one [kpt_swp_close]. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile.
Require Import WpGpr WpGprCsrwB.
Require Import SmodePte PtTree PtTreeAdue.
Require Import KptExecMap KptGhost.
Require Import UptTree.
Require Import HartSpan HartSwp HartMFrame.
Require Import WpDecodeBridge WpMmodeSwpBase WpMmodeJump WpMmodeCsrSwp
        HartSCsr.
Require Import WpSmodePtEngine.
Require Import WpSconfSfence WpSconfCsr.
Require Import SRegime TrampStepPt UptWalkPt TransPt Pt2WalkPt KptShare.
Require Import UserretDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* The LINKING compressed jalr, per node.                                 *)
(*                                                                        *)
(* [WpSmodePtEngine.swp_cj_JALR_ret] is the rd = x0 form; uservec's tail   *)
(* jump writes the link register, so the last node is [swp_wX_file]        *)
(* rather than [swp_wX_zero] and the register file moves.  Everything      *)
(* else -- the elp gate at the lent fraction ([swp_cj_update_elp]), the    *)
(* link read, the [ret_pc] target and its alignment -- is that lemma       *)
(* verbatim.  (This replaces the file's old whole-[execute] tower          *)
(* [exec_execute_JALR_link_zca] and the [currentlyEnabled Ext_Zicfilp]     *)
(* peel it needed: per node the gate is [hval_cj_update_elp].)             *)
(* ===================================================================== *)

(* the target's bit 0, spelled as the MODEL spells it -- [WpSmodePtEngine]'s
   own [sb_zerobit], which is a [Local Notation] there. *)
Local Notation uve_zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Section UveJalr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_cj_JALR_link (dq : dfrac) (rs1 rd : SailStdpp.Values.mword 5)
      (m : regfile) (npc0 menv0 : SailStdpp.Values.mword 64) :
    uint rd <> 0 ->
    menv0 = MENVCFG_S ->
    gen_cert -∗ gpr_file m -∗
    (R_bitvector_64 nextPC) ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    menvcfg ↦ᵣ{ dq } menv0 -∗
    misa ↦ᵣ□ MISA_C -∗
    swp (execute (JALR (zeros' 12, Regidx rs1, Regidx rd)))
      (fun e => ⌜e = RETIRE_SUCCESS⌝ ∗
                gpr_file (<[Regidx rd := regval_into_reg npc0]> m) ∗
                (R_bitvector_64 nextPC) ↦ᵣ (ret_pc (m !!! Regidx rs1)) ∗
                cur_privilege ↦ᵣ{ dq } Supervisor ∗
                menvcfg ↦ᵣ{ dq } menv0 ∗
                misa ↦ᵣ□ MISA_C).
  Proof.
    intros Hrd Hmenv. subst menv0.
    (* the alignment side condition is [ret_pc]'s own construction, and it
       has to be POSED rather than passed as an [ltac:] inside the
       application: inside one, the goal still carries the application's
       evars. *)
    assert (Halign : eq_vec (access_vec_dec
              (update_vec_dec
                 (add_vec (m !!! Regidx rs1) (sign_extend' 64 (zeros' 12))) 0
                 uve_zerobit) 0) uve_zerobit = true)
      by (rewrite ret_pc_jalr; apply ret_pc_aligned).
    iIntros "#Hcert Hf HnPC Hpriv Hmenv Hmisa".
    change (execute (JALR (zeros' 12, Regidx rs1, Regidx rd)))
      with (execute_JALR (zeros' 12) (Regidx rs1) (Regidx rd)).
    unfold execute_JALR. cbn match.
    iApply (swp_bind_use
              (Defs.bind0 (update_elp_state (Regidx rs1)) (get_next_pc tt)) _
              (fun link => ⌜link = npc0⌝ ∗
                 (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                 cur_privilege ↦ᵣ{ dq } Supervisor ∗
                 menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                 misa ↦ᵣ□ MISA_C)%I _
              with "[HnPC Hpriv Hmenv Hmisa] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (R_bitvector_64 nextPC) ↦ᵣ npc0 ∗
                   cur_privilege ↦ᵣ{ dq } Supervisor ∗
                   menvcfg ↦ᵣ{ dq } MENVCFG_S ∗
                   misa ↦ᵣ□ MISA_C)%I _
                with "[HnPC Hpriv Hmenv Hmisa] [-]").
      { iApply (swp_cj_update_elp dq rs1 npc0
                  with "Hcert HnPC Hpriv Hmenv Hmisa"). }
      iIntros (u) "(HnPC & Hpriv & Hmenv & Hmisa)".
      unfold get_next_pc.
      iApply (swp_mono with "[Hpriv Hmenv Hmisa] [-]");
        [| iApply (swp_read_reg_cell (R_bitvector_64 nextPC) npc0
                     with "Hcert HnPC") ].
      iIntros (link) "[-> HnPC]". iSplitR; [done|]. iFrame. }
    iIntros (link) "(-> & HnPC & Hpriv & Hmenv & Hmisa)".
    iApply (swp_bind_use (rX_bits (Regidx rs1)) _ _ _ with "[Hf] [-]").
    { iApply (swp_rX_file rs1 m with "Hcert Hf"). }
    iIntros (w) "[-> Hf]".
    iApply (swp_bind_use _ _ _ _ with "[HnPC Hmisa] [-]").
    { iApply (swp_sb_jump _ npc0 Halign with "Hcert HnPC Hmisa"). }
    iIntros (r) "(-> & HnPC & Hmisa)". cbn match.
    iApply (swp_bind0_use _ _ _ _ with "[Hf] [-]").
    { iApply (swp_wX_file rd m npc0 Hrd with "Hcert Hf"). }
    iIntros (u2) "Hf". iApply swp_ret. rewrite ret_pc_jalr.
    iSplitR; [done|]. iFrame.
  Qed.

End UveJalr.

Section UservecExitPt.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma wp_uservec_exit_pt (kroot uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64))
      (m : regfile) (ksatp : mword 64)
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
    (* t1 holds the KERNEL satp value *)
    m !!! Regidx (mword_of_int 6) = ksatp ->
    _get_Satp64_Mode (Mk_Satp64 ksatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) ksatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) ksatp : mword 64)) = kroot ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    (* the trampoline claim: the KERNEL table maps the trampoline page, so
       the post-switch fetches go through it *)
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    utlb_inv_pt uroot tfp um -∗
    kpt_inv kroot -∗
    pc_is (uva 0x8e) -∗
    gpr_file m -∗
    instr (upa 0x8e) false ai_sfence -∗
    instr (upa 0x92) false (CSRReg (csr_satp, Regidx (mword_of_int 6 : mword 5), zreg, CSRRW)) -∗
    instr (upa 0x96) false ai_sfence -∗
    instr (upa 0x9a) true (JALR (zeros' 12, Regidx (mword_of_int 5 : mword 5), ra)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      pt_frame (upt_tree_spec uroot tfp um) -∗
      (* STEP 4's own [tlb_res_pt kroot] -- KEPT, not [iClear]ed: a chained
         caller that goes on to userret's own entry switch needs it as
         ITS precondition (see SpecUserret.v's own header). *)
      tlb_res_pt kroot -∗
      pc_is (ret_pc (m !!! Regidx (mword_of_int 5))) -∗
      gpr_file (<[Regidx (mword_of_int 1) := regval_into_reg (uva 0x9c)]> m) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HSIE HMPRV HSXL HTVM Hmm HPBMTE Hmenvval0 Hwf Ht1 HkMode Hkasid Hkppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv #Hclaim Hutlb #Hkinv Hpc
             Hfmap Hi1 Hi2 Hi3 Hi4 Hcont".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA &
        %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0 mseccfg0.
    assert (Hva01 : add_vec_int (uva 0x8e) 4 = uva 0x92)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva02 : add_vec_int (uva 0x92) 4 = uva 0x96)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva03 : add_vec_int (uva 0x96) 4 = uva 0x9a)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hva04 : add_vec_int (uva 0x9a) 2 = uva 0x9c)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HEk : (↑kptN : coPset) ⊆ (⊤ : coPset)) by solve_ndisj.
    assert (Hcw2 : cw2_ok satp mstatus).
    { rewrite /cw2_ok /cw_fresh. split_and!;
        first [ vm_compute; reflexivity | intros HX; discriminate HX ]. }
    assert (Hra1 : ra = Regidx (mword_of_int 1 : mword 5))
      by (unfold ra; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Hrd1 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; lia).
    (* ============ STEP 1: sfence.vma under the USER invariant ========== *)
    iApply (wp_instr_u_pt uroot tfp um (uva 0x8e) (upa 0x8e) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0x92⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝)%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc Hi1
                    [] [Hfmap Hi2 Hi3 Hi4 Hcont]").
    { iIntros (satp0 pcfg paddr tv') "%Hsok %Hpok
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct "HRes" as (t0) "(%Hokt0 & %Hspect0 & %Hwft0 & Ht0)".
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv'
                   with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr Hhtif
                         Hmisa") as "[Hrw Hro]".
      assert (LTVM : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (sda_rs mstatus0 menvcfg0 satp0 pmar0 pcfg paddr tv')))
                 ('b"1") = false)
        by (rewrite sda_rs_mst; exact HTVM).
      change (execute ai_sfence)
        with (execute (SFENCE_VMA (zreg, zreg))).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Ht0] [-]").
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
      iSplitL "Htlbc Ht0".
      { iExists tvz. iFrame "Htlbc". iExists t0. iFrame "Ht0". iPureIntro.
        split_and!;
          [ exact (tlb_ok_pt_empty (mword_of_int 0) t0 tvz
                     (fun vpn' => Hnone _ (tlb_hash_range vpn')))
          | exact Hspect0 | exact Hwft0 ]. }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva01 |]. iSplitR; [done|]. done. }
    iNext. iIntros (npc1 ms11 mdv11)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hutlb Hpc (-> & -> & ->)".
    (* ============ STEP 2: csrw satp,t1 -- ENTER the window =============
       The user residue does not mention satp, so this is an ORDINARY
       [Res]-preserving step of the raw engine at a MOVED landing satp; the
       window is entered in its continuation. ============================ *)
    iDestruct (upt_swp_open uroot tfp um with "Hutlb")
      as (usatp2 tlbv2 pcfg2 paddr2)
      "(%Hsok2 & %Hpok2 & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    pose proof Hpok2 as (HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
    assert (Hleg2 : satp_legalized usatp2 (m !!! Regidx (mword_of_int 6 : mword 5))
                    = ksatp)
      by (rewrite Ht1; exact (satp_legalized_sv39 usatp2 ksatp HkMode)).
    iApply (wp_instr_tramp_pt (upt_res_pt uroot tfp um)
              (upt_res_pt uroot tfp um)
              (uva 0x92) (upa 0x92) false
              (CSRReg (csr_satp, Regidx (mword_of_int 6 : mword 5), zreg, CSRRW))
              mstatus0 mie_v mdv0 menvcfg0 usatp2 pcfg2 paddr2 tlbv2
              mie_v menvcfg0 ksatp pcfg2 paddr2 Supervisor
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0x96⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
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
                    Htlbc HRes Hpc Hi2 [] [Hfmap] [Hi3 Hi4 Hcont]").
    { iApply (utramp_fetch_tr uroot tfp um dq (uva 0x92) mstatus0 usatp2 mie_v
                mdv0 menvcfg0 pcfg2 paddr2 Hmenvval0 HSXL HMPRV Hsok2 Hpok2
                with "Hhw"). }
    { iIntros (tv') "%Hpok3
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct (pw2_frames_in Supervisor dq dq satp usatp2 mstatus mstatus0
                   Hcw2 with "Hsatp Hms Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      assert (LTVM2 : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (pw2_rs Supervisor satp usatp2 mstatus mstatus0))) ('b"1")
                 = false)
        by (rewrite (pw2_rs_r2 Supervisor satp usatp2 mstatus mstatus0);
            exact HTVM).
      change (execute (CSRReg (csr_satp, Regidx (mword_of_int 6 : mword 5),
                               zreg, CSRRW)))
        with (execute_CSRReg csr_satp (Regidx (mword_of_int 6 : mword 5))
                zreg CSRRW).
      iApply (swp_mono with
                "[Hmie Hmdl Hmenv Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
                  Hresv] [Hrw Hro Hfmap]").
      2:{ iApply (swp_execute_CSRReg_w_p (cw_Drw satp) (cw2_Dro mstatus)
                    (cw2_Df dq dq mstatus)
                    (pw2_rs Supervisor satp usatp2 mstatus mstatus0)
                    (pw2_rs Supervisor satp
                       (satp_legalized usatp2
                          (m !!! Regidx (mword_of_int 6 : mword 5)))
                       mstatus mstatus0)
                    m csr_satp Supervisor (mword_of_int 6)
                    (satp_legalized usatp2
                       (m !!! Regidx (mword_of_int 6 : mword 5)))
                    (cw2_disj satp mstatus Hcw2) (cw2_in_priv satp mstatus)
                    (pw2_rs_priv Supervisor satp usatp2 mstatus mstatus0 Hcw2)
                    ltac:(by vm_compute)
                    (hval_check_CSR_result_satp_S_w
                       (cw_Drw satp ∪ cw2_Dro mstatus) (cw_Drw satp)
                       (pw2_rs Supervisor satp usatp2 mstatus mstatus0)
                       (cw2_in_priv satp mstatus) (cw2_in_sec satp mstatus)
                       (cw2_in_misa satp mstatus) (cw2_in_r2 satp mstatus)
                       LTVM2)
                    ltac:(by vm_compute) ltac:(by vm_compute)
                    ltac:(by vm_compute)
                    with "Hcert Hfmap Hrw Hro [ ]").
          iIntros "Hrw Hro".
          iApply (swp_write_CSR_satp_S dq dq usatp2 mstatus0
                    (m !!! Regidx (mword_of_int 6 : mword 5)) Hcw2 HSXL
                    with "Hcert Hrw Hro"). }
      iIntros (e) "(-> & Hfmap & Hrw & Hro)".
      iDestruct (pw2_frames_out Supervisor dq dq satp
                   (satp_legalized usatp2
                      (m !!! Regidx (mword_of_int 6 : mword 5)))
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
    (* dissolve the USER invariant into the two-table window; the KERNEL
       side is sourced from the ambient [kpt_inv] -- a fresh snapshot, no
       ownership, so this is the one [iMod] of the proof *)
    iDestruct "HRes" as (t2) "(%Hokt2 & %Hspect2 & %Hwft2 & Ht2)".
    iApply fupd_wp.
    iMod (tlb_inv_pt2_kcur_enter kroot (upt_tree_spec uroot tfp um) ⊤
             ksatp tv2 t2 HEk HkMode Hkasid Hkppn Hokt2 Hspect2
             PtTreeAdue.pma_allows_all_pte_write
             with "Hsatp Htlbc Ht2 [Hpcfg Hpaddr] Hkinv") as "Hpt2".
    { iApply (pmp_config_intro kroot pcfg2 paddr2 HA2 Hord2 HX2 HW2 HR2 Hcov2
                with "Hpcfg Hpaddr"). }
    iModIntro.
    (* ============ STEP 3: sfence.vma -- EXIT into the kernel residue ===
       The window's residue LEAVES as the kernel's, with the user table
       parked beside it: the flush is what makes the exchange, and it is
       born inside the [swp] obligation. ================================ *)
    iDestruct (pt2_kcur_swp_open kroot (upt_tree_spec uroot tfp um)
                 with "Hpt2") as (satp3 tlbv3 pcfg3 paddr3)
      "(%Hsok3 & %Hpok3 & Hsatp & Htlbc & Hpcfg & Hpaddr & HRes)".
    pose proof Hsok3 as (Hm3 & Ha3 & Hp3 & _).
    assert (Hksok3 : kpt_satp_ok kroot satp3)
      by (rewrite /kpt_satp_ok; split_and!; assumption).
    iApply (wp_instr_tramp_pt
              (pt2_res_kcur kroot (upt_tree_spec uroot tfp um))
              (fun tv => (kpt_res_at kroot satp3 tv ∗
                          pt_frame (upt_tree_spec uroot tfp um))%I)
              (uva 0x96) (upa 0x96) false ai_sfence
              mstatus0 mie_v mdv0 menvcfg0 satp3 pcfg3 paddr3 tlbv3
              mie_v menvcfg0 satp3 pcfg3 paddr3 Supervisor
              (fun npc ms1 mdv1 =>
                 (⌜npc = uva 0x9a⌝ ∗ ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝)%I)
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
                    Htlbc HRes Hpc Hi3 [] [] [Hfmap Hi4 Hcont]").
    { iApply (pt2_tramp_fetch_tr_kcur kroot (upt_tree_spec uroot tfp um) dq
                (uva 0x96) mstatus0 satp3 mie_v mdv0 menvcfg0 pcfg3 paddr3
                Hmenvval0 HSXL HMPRV Hsok3 Hpok3
                (upt_pt2_tramp_spec uroot tfp um Hwf) with "Hclaim Hhw"). }
    { iIntros (tv') "%Hpok4
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iDestruct "HRes" as (tp tc0) "(%Hok2 & %HSp & Htp & #Hlb0 & #Hkinv3)".
      iDestruct (sda_frames_in dq mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3
                   tv' with "Htlbc Hms Hpriv Hmenv Hsatp Hpma Hpcfg Hpaddr
                             Hhtif Hmisa") as "[Hrw Hro]".
      assert (LTVM3 : eq_vec (_get_Mstatus_TVM (register_lookup mstatus
                 (sda_rs mstatus0 menvcfg0 satp3 pmar0 pcfg3 paddr3 tv')))
                 ('b"1") = false)
        by (rewrite sda_rs_mst; exact HTVM).
      change (execute ai_sfence)
        with (execute (SFENCE_VMA (zreg, zreg))).
      iApply (swp_mono with "[Hmie Hmdl Hclk HPC HnPC Htp] [-]").
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
                   tvz with "[$Hrw $Hro]")
        as "(Htlbc & Hms & Hpriv & Hmenv & Hsatp & _ & Hpcfg & Hpaddr & _ & _)".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc Htp".
      { iExists tvz. iFrame "Htlbc". rewrite /kpt_res_at.
        iSplitR "Htp".
        { iFrame "Hkinv3". iExists tc0. iFrame "Hlb0". iPureIntro.
          exact (tlb_ok_pt_empty (mword_of_int 0) tc0 tvz
                   (fun vpn' => Hnone _ (tlb_hash_range vpn'))). }
        iExists tp. iFrame "Htp". iPureIntro. exact HSp. }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [iPureIntro; exact Hva03 |]. iSplitR; [done|]. done. }
    iNext. iIntros (npc3 ms13 mdv13 tv3)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hpc
       (-> & -> & ->)".
    iDestruct "HRes" as "[Hkres Hufr]".
    iDestruct (kpt_swp_close kroot satp3 tv3 pcfg3 paddr3 Hksok3 Hpok3
                 with "Hsatp Htlbc Hpcfg Hpaddr Hkres") as "Hktlb".
    (* ============ STEP 4: c.jalr t0 under the SHARED kernel table ====== *)
    rewrite Hra1.
    iApply (wp_instr_ktramp_pt_share kroot (uva 0x9a) (upa 0x9a) true
              (JALR (zeros' 12, Regidx (mword_of_int 5 : mword 5),
                     Regidx (mword_of_int 1 : mword 5)))
              mstatus0 mie_v mdv0 menvcfg0 mie_v menvcfg0
              (fun npc ms1 mdv1 =>
                 (⌜npc = ret_pc (m !!! Regidx (mword_of_int 5 : mword 5))⌝ ∗
                  ⌜ms1 = mstatus0⌝ ∗ ⌜mdv1 = mdv0⌝ ∗
                  gpr_file (<[Regidx (mword_of_int 1 : mword 5)
                              := regval_into_reg (uva 0x9c)]> m))%I)
              (dq := dq) HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hclaim Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc Hi4
                    [Hfmap] [Hufr Hcont]").
    { iIntros (satp4 pcfg paddr tv') "%Hsok4 %Hpok4
        Hpriv Hms Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC HnPC
        Hresv".
      iApply (swp_mono with
                "[Hms Hmdl Hmie Hsatp Hpcfg Hpaddr Htlbc HRes Hclk HPC Hresv]
                 [Hfmap HnPC Hpriv Hmenv]").
      2:{ iApply (swp_cj_JALR_link dq (mword_of_int 5) (mword_of_int 1) m
                    (add_vec_int (uva 0x9a) 2) menvcfg0 Hrd1 Hmenvval0
                    with "Hcert Hfmap HnPC Hpriv Hmenv Hmisa"). }
      iIntros (e) "(-> & Hfmap & HnPC & Hpriv & Hmenv & _)".
      iEval (rewrite Hva04) in "Hfmap".
      iSplitR; [done|].
      iFrame "Hpriv Hmie Hmenv Hsatp Hpcfg Hpaddr".
      iSplitL "Htlbc HRes". { iExists tv'. iFrame "Htlbc HRes". }
      iFrame "Hclk".
      iSplitR "Hresv"; [| iExact "Hresv"].
      iExists mstatus0, mdv0, _.
      iFrame "Hms Hmdl HPC HnPC".
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iExact "Hfmap". }
    iNext. iIntros (npc4 ms14 mdv14)
      "Hhs Hpriv Hms Hmie Hmdl Hmenv Hktlb Hpc (-> & -> & -> & Hfmap)".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Hufr Hktlb Hpc Hfmap").
  Qed.

End UservecExitPt.

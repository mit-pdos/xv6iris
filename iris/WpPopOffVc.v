(* WpPopOffVc.v -- pop_off() re-proved with the S-mode VCgen (VcGenS.v),
   including the function it calls (mycpu(), via WpMycpuVc.wp_mycpu_vc).

   Same statement as WpPopOff.wp_pop_off.  The straight-line runs are VCgen
   blocks (one [vm_compute]d symbolic execution + one [iApply wp_vc_block_s]
   each):

     - the PROLOGUE  +0x00..+0x06 (c.addi sp,-16; sd ra,8(sp); sd s0,0(sp);
       addi s0,sp,16) -- literally the same [mycpu_prologue] program as
       mycpu's, run at pop_off's pc ([popoff_prologue_run]);
     - the EPILOGUE  +0x28..+0x2c (ld ra,8(sp); ld s0,0(sp); c.addi sp,16),
       shared by BOTH bnez outcomes -- the same [mycpu_epilogue] program,
       run at pop_off's pc ([popoff_epilogue_run]) and applied once per
       branch.

   The call [jal mycpu] reuses the WpPushOffTop call-composite pattern with
   [wp_mycpu_vc] as the callee (so mycpu's straight-line runs are ALSO VCgen
   blocks), and the value-computing middle (csrr sstatus / c.andi / the
   three branches / c.lw / c.addiw / c.sw / csrsi-skip) keeps the existing
   per-instruction leaves -- branch conditions and 32-bit sign-extension
   live outside the VCgen's symbolic domain by design. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding.
Require Import WpRvcBridge WpPopOff.
Require Import VcGen VcGenS WpMycpuVc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* pop_off's blocks use PARTIAL symbolic register maps (the agreement
   interface): each block's map seeds only the registers it touches plus the
   ones whose values must be carried across it (s1/tp/a0 feed the final
   register facts; sp feeds the epilogue).  Variable convention: xk ↦ SX k 0
   (the register's current value); 33/34 = memory-cell contents. *)
Definition po_pro_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 1 0]>
  (<[Regidx (mword_of_int 8 : mword 5) := SX 8 0]>
  (<[Regidx (mword_of_int 9 : mword 5) := SX 9 0]>
  (<[Regidx (mword_of_int 4 : mword 5) := SX 4 0]> ∅)))).
Definition po_pro_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 8 : mword 5) := SX 2 0]>
    (<[Regidx csp_rs1 := SX 2 (wrap64 (-16))]> po_pro_regs0).

Lemma po_prologue_run :
  vc_block_s (VSt KernelSyms.pop_off po_pro_regs0 mycpu_pro_heap0 []) mycpu_prologue
  = Some (VSt (KernelSyms.pop_off + 8) po_pro_regs1 mycpu_pro_heap1 []).
Proof. vm_compute. reflexivity. Qed.

(* the noff word cell: [a0 + 120], variable 33 = the (sign-extended)
   pre-decrement word. *)
Definition popoff_lw_prog : list vop_s :=
  [ VSclw (mword_of_int 120) (mword_of_int 10) (mword_of_int 15) ].
Definition po_noff_cell0 : list (sval * sval32) :=
  [ (SX 10 120, SX32 33 0) ].
Definition po_lw_regs0 : gmap regidx sval :=
  <[Regidx (mword_of_int 10 : mword 5) := SX 10 0]>
  (<[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 9 : mword 5) := SX 9 0]>
  (<[Regidx (mword_of_int 4 : mword 5) := SX 4 0]> ∅))).
Definition po_lw_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 15 : mword 5) := S32 (SX32 33 0)]> po_lw_regs0.

Lemma po_lw_run :
  vc_block_s (VSt (KernelSyms.pop_off + 0x14) po_lw_regs0 [] po_noff_cell0)
             popoff_lw_prog
  = Some (VSt (KernelSyms.pop_off + 0x16) po_lw_regs1 [] po_noff_cell0).
Proof. vm_compute. reflexivity. Qed.

(* [c.addiw a5,-1; c.sw a5,120(a0)]: the decrement is tracked symbolically
   in the 32-bit domain -- a5 and the stored word become "noff minus one"
   ([SX32 33 (2^32-1)]). *)
Definition popoff_decsw_prog : list vop_s :=
  [ VScaddiw (mword_of_int 63) (mword_of_int 15);
    VScsw (mword_of_int 120) (mword_of_int 15) (mword_of_int 10) ].
Definition po_decsw_regs0 : gmap regidx sval :=
  <[Regidx (mword_of_int 15 : mword 5) := S32 (SX32 33 0)]> po_lw_regs0.
Definition po_decsw_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 15 : mword 5) := S32 (SX32 33 4294967295)]> po_decsw_regs0.
Definition po_noff_cell1 : list (sval * sval32) :=
  [ (SX 10 120, SX32 33 4294967295) ].

Lemma po_decsw_run :
  vc_block_s (VSt (KernelSyms.pop_off + 0x1a) po_decsw_regs0 [] po_noff_cell0)
             popoff_decsw_prog
  = Some (VSt (KernelSyms.pop_off + 0x1e) po_decsw_regs1 [] po_noff_cell1).
Proof. vm_compute. reflexivity. Qed.

Definition po_epi_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 9 : mword 5) := SX 9 0]>
  (<[Regidx (mword_of_int 4 : mword 5) := SX 4 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 10 0]> ∅))).
Definition po_epi_regs1 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 16]>
  (<[Regidx (mword_of_int 8 : mword 5) := SX 34 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> po_epi_regs0)).

Lemma po_epilogue_run :
  vc_block_s (VSt (KernelSyms.pop_off + 0x28) po_epi_regs0 mycpu_epi_heap []) mycpu_epilogue
  = Some (VSt (KernelSyms.pop_off + 0x2e) po_epi_regs1 mycpu_epi_heap []).
Proof. vm_compute. reflexivity. Qed.

Section WpPopOffVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Notation PP := KernelSyms.pop_off.

  Lemma popoff_prologue_instrs :
    kernel_text -∗ block_instrs_s PP mycpu_prologue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_prologue vop_s_ast].
    replace (PP + 2 + 2) with (PP + 4) by lia.
    replace (PP + 4 + 2) with (PP + 6) by lia.
    iSplitR; [by iApply ppi_00|].
    iSplitR; [by iApply ppi_02|].
    iSplitR; [by iApply ppi_04|].
    iSplitR.
    { assert (Hcreg : creg2reg_idx (Cregidx (mword_of_int 0 : mword 3))
                      = Regidx (mword_of_int 8 : mword 5))
        by (vm_compute; reflexivity).
      rewrite -Hcreg. by iApply ppi_06. }
    done.
  Qed.

  Lemma popoff_epilogue_instrs :
    kernel_text -∗ block_instrs_s (PP + 0x28) mycpu_epilogue.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s mycpu_epilogue vop_s_ast].
    replace (PP + 0x28 + 2) with (PP + 0x2a) by lia.
    replace (PP + 0x2a + 2) with (PP + 0x2c) by lia.
    iSplitR; [by iApply ppi_28|].
    iSplitR; [by iApply ppi_2a|].
    iSplitR; [by iApply ppi_2c|].
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the call composite (jal + the whole mycpu): the WpPushOffTop proof,  *)
  (* verbatim, with wp_mycpu_vc as the callee.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_call_mycpu_vc (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      (raold s0old : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      :
    let ra_idx : mword 5 := mword_of_int 1 in
    let tp_idx : mword 5 := mword_of_int 4 in
    let s0_idx : mword 5 := mword_of_int 8 in
    let a0_idx : mword 5 := mword_of_int 10 in
    let a5_idx : mword 5 := mword_of_int 15 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let imm_entry : mword 6 := mword_of_int 48 in
    let sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)) in
    let ra0 := m0 !!! Regidx ra_idx in
    let s00 := m0 !!! Regidx s0_idx in
    let ea_ra := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let pa_ra := ea_ra in
    let ea_s0 := add_vec sp' (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let pa_s0 := ea_s0 in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    add_vec P (sign_extend' 64 jimm) = pcE ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
    ghost_var γc (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file m -∗
    instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
    pa_ra ↦₈ raold -∗
    pa_s0 ↦₈ s0old -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      ghost_var γc (1/2) (_get_Mstatus_SIE mstatus0) -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗ gpr_file (po_mycpu_out P m) -∗
      pa_ra ↦₈ ra0 -∗
      pa_s0 ↦₈ s00 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros ra_idx tp_idx s0_idx a0_idx a5_idx m0 pcE imm_entry sp' ra0 s00
      ea_ra pa_ra ea_s0 pa_s0 ret_tgt
      HN Htarget Halign_tgt
      HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe HFIOM Hlegal Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv #Htext Hpc Hfile Hjal Hbra Hbs0 Hcont".
    iDestruct (kv_cfg_split γc mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hlegal Hmm HPBMTE Hpmm Hlpe HFIOM
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_jal_gpr_s2 root_ppn γc E Φ P (mword_of_int 1) jimm m (1/2)%Qp
              HN ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halign_tgt)
              with "Hhw Hsm Htlbinv Hpc Hfile Hjal [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite Htarget) in "Hpc".
    iDestruct (kv_cfg_recombine γc mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hgc & Hmie & Hmdl & Hmenv)".
    iApply (wp_mycpu_vc root_ppn E Φ m0 raold s0old mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hbra Hbs0 [Hgc Hcont]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbra Hbs0".
    iApply ("Hcont" with "Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hbra Hbs0").
  Qed.

  (* ==================================================================== *)
  (* wp_pop_off, re-proved.  Statement identical to WpPopOff.wp_pop_off.   *)
  (* ==================================================================== *)
  Lemma wp_pop_off_vc (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (noffv intenav : mword 32)
      (vp8 vp0 vfra vfs0 : bv 64)
      {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int PP in
    let spd := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_p8 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_p0 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let mc_sp := add_vec spd (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) in
    let a_fra := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) in
    let a_fs0 := add_vec mc_sp (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) in
    let a0v := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    ↑minstretN ⊆ E ->
    (* S-mode config facts + the interrupt-off sstatus fact are folded into
       [smode_config γc] below. *)
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    eq_vec (sign_extend' 64 intenav) zero_reg = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    a_p8 ↦₈ vp8 -∗
    a_p0 ↦₈ vp0 -∗
    a_fra ↦₈ vfra -∗
    a_fs0 ↦₈ vfs0 -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄{ dqi } intenav -∗
    ( smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      (∃ mf, gpr_file mf ∗
        ⌜ mf !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5) /\
          mf !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5) /\
          mf !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5) /\
          mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1 /\
          mf !!! Regidx (mword_of_int 4 : mword 5) = m !!! Regidx (mword_of_int 4 : mword 5) /\
          mf !!! Regidx (mword_of_int 10 : mword 5) = a0v ⌝) -∗
      a_noff ↦₄ storeval -∗
      a_int ↦₄{ dqi } intenav -∗
      (∃ (w8 w0 wra ws0 : bv 64),
        a_p8 ↦₈ w8 ∗
        a_p0 ↦₈ w0 ∗
        a_fra ↦₈ wra ∗
        a_fs0 ↦₈ ws0) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros pcE spd a_p8 a_p0 mc_sp a_fra a_fs0 a0v a_noff a_int nv1 storeval ret_tgt
      HN Hnoffpos Hint Hal0.
    iIntros "Hcfg Htlbinv
             #Htext Hpc Hfile Hp8 Hp0 Hfra Hfs0 Hnoff Hint Hcont".
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(Hhw & Hinv & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hhw" as "#Hhw". iDestruct "Hinv" as "#Hinv".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hlegal)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM)".
    assert (Hsst2 : neq_vec (and_vec (sstatus_read mstatus0)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false)
      by (apply pop_sstatus_clear_neq; exact HSIE).
    iPoseProof (ppi_08 with "Htext") as "Hi08".
    iPoseProof (ppi_0c with "Htext") as "Hi0c".
    iPoseProof (ppi_10 with "Htext") as "Hi10".
    iPoseProof (ppi_12 with "Htext") as "Hi12".
    iPoseProof (ppi_14 with "Htext") as "Hi14".
    iPoseProof (ppi_16 with "Htext") as "Hi16".
    iPoseProof (ppi_1a with "Htext") as "Hi1a".
    iPoseProof (ppi_1c with "Htext") as "Hi1c".
    iPoseProof (ppi_1e with "Htext") as "Hi1e".
    iPoseProof (ppi_20 with "Htext") as "Hi20".
    iPoseProof (ppi_22 with "Htext") as "Hi22".
    iPoseProof (ppi_2e with "Htext") as "Hi2e".
    (* ------------------------------------------------------------------ *)
    (* PROLOGUE +0x00..+0x06: one VCgen block (agreement interface: the     *)
    (* symbolic map seeds sp/ra/s0 (touched) and s1/tp (observed across).   *)
    (* ------------------------------------------------------------------ *)
    pose (ρA := fun k : nat => match k with
           | 1%nat => m !!! Regidx (mword_of_int 1 : mword 5)
           | 2%nat => m !!! Regidx csp_rs1
           | 4%nat => m !!! Regidx (mword_of_int 4 : mword 5)
           | 8%nat => m !!! Regidx (mword_of_int 8 : mword 5)
           | 9%nat => m !!! Regidx (mword_of_int 9 : mword 5)
           | 33%nat => (vp8 : mword 64)
           | _ => (vp0 : mword 64)
           end).
    assert (HmA : gpr_matches ρA po_pro_regs0 m).
    { unfold po_pro_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (Hara : sval_den ρA (SX 2 (wrap64 (-8))) = a_p8).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx csp_rs1) by reflexivity.
      unfold a_p8, spd. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Has0 : sval_den ρA (SX 2 (wrap64 (-16))) = a_p0).
    { cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx csp_rs1) by reflexivity.
      unfold a_p0, spd. rewrite add_vec_off2.
      f_equal; f_equal; vm_compute; reflexivity. }
    assert (Hv33 : sval_den ρA (SX 33 0) = (vp8 : mword 64))
      by (rewrite sval_den_SX0; reflexivity).
    assert (Hv34 : sval_den ρA (SX 34 0) = (vp0 : mword 64))
      by (rewrite sval_den_SX0; reflexivity).
    iDestruct (popoff_prologue_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn mycpu_prologue E Φ
              (VSt PP po_pro_regs0 mycpu_pro_heap0 [])
              (VSt (PP + 8) po_pro_regs1 mycpu_pro_heap1 [])
              ρA m mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE po_prologue_run HmA
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi [Hp8 Hp0] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_pro_heap0.
      cbn [big_opL fst snd]. rewrite Hara Has0 Hv33 Hv34.
      iFrame "Hp8 Hp0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (M1) "%HmA1 Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
    assert (Hvra1 : sval_den ρA (SX 1 0) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite sval_den_SX0; reflexivity).
    assert (Hvs81 : sval_den ρA (SX 8 0) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite sval_den_SX0; reflexivity).
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_pro_heap1;
           cbn [big_opL fst snd];
           rewrite Hara Has0 Hvra1 Hvs81) in "Hheap".
    iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
    iEval (cbn [vpc]) in "Hpc".
    (* the post-block register facts, via the agreement *)
    assert (Hsp1 : M1 !!! Regidx csp_rs1 = spd).
    { assert (Hl : po_pro_regs1 !! Regidx csp_rs1 = Some (SX 2 (wrap64 (-16))))
        by (vm_compute; reflexivity).
      rewrite (HmA1 _ _ Hl). cbn [sval_den].
      replace (ρA 2%nat) with (m !!! Regidx csp_rs1) by reflexivity.
      unfold spd. f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Htp1 : M1 !!! Regidx (mword_of_int 4 : mword 5)
                   = m !!! Regidx (mword_of_int 4 : mword 5)).
    { assert (Hl : po_pro_regs1 !! Regidx (mword_of_int 4 : mword 5) = Some (SX 4 0))
        by (vm_compute; reflexivity).
      rewrite (HmA1 _ _ Hl) sval_den_SX0. reflexivity. }
    assert (Hs91 : M1 !!! Regidx (mword_of_int 9 : mword 5)
                   = m !!! Regidx (mword_of_int 9 : mword 5)).
    { assert (Hl : po_pro_regs1 !! Regidx (mword_of_int 9 : mword 5) = Some (SX 9 0))
        by (vm_compute; reflexivity).
      rewrite (HmA1 _ _ Hl) sval_den_SX0. reflexivity. }
    (* +0x08 jal ra,mycpu; the whole mycpu() -- via the VCgen-based callee *)
    assert (HspP2r : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4)]> M1) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact Hsp1 | vm_compute; discriminate ]).
    iApply (wp_call_mycpu_vc root_ppn γc E Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) M1 vfra vfs0
              mstatus0 mie_v mdv0 menvcfg0
              HN ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe HFIOM Hlegal
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hi08 [Hfra] [Hfs0] [-]").
    { iEval (rewrite HspP2r). iExact "Hfra". }
    { iEval (rewrite HspP2r). iExact "Hfs0". }
    iIntros "Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hfra Hfs0".
    iEval (rewrite HspP2r) in "Hfra". iEval (rewrite HspP2r) in "Hfs0".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc0c : update_vec_dec (add_vec (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PP + 0x0c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    set (C := po_mycpu_out (mword_of_int (PP + 0x08)) M1).
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /C po_mycpu_out_a0 Htp1. reflexivity. }
    assert (HspC : C !!! Regidx csp_rs1 = spd).
    { rewrite /C po_mycpu_out_csp. exact Hsp1. }
    assert (Hs9C : C !!! Regidx (mword_of_int 9 : mword 5)
                   = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /C po_mycpu_out_s1. exact Hs91. }
    assert (HtpC : C !!! Regidx (mword_of_int 4 : mword 5)
                   = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /C po_mycpu_out_tp. exact Htp1. }
    (* +0x0c csrr a5,sstatus *)
    iApply (wp_csrr_sstatus_s root_ppn E Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15) C
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> C).
    assert (Hpp10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.andi a5,2 *)
    iApply (wp_candi_s root_ppn E Φ (mword_of_int (PP + 0x10)) (mword_of_int 15) (mword_of_int 2 : mword 6)
              P3 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3).
    assert (Ha5P3 : P3 !!! Regidx (mword_of_int 15 : mword 5) = sstatus_read mstatus0)
      by (rewrite /P3; apply lookup_total_insert).
    assert (Hpp12 : add_vec_int (mword_of_int (PP + 0x10) : mword 64) 2 = mword_of_int (PP + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.bnez a5 NOT taken (SIE = 0) *)
    assert (Ha5P4 : P4 !!! Regidx (mword_of_int 15 : mword 5)
                    = and_vec (sstatus_read mstatus0) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /P4. rewrite lookup_total_insert. rewrite Ha5P3. reflexivity. }
    iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (PP + 0x12)) (mword_of_int 15) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              P4 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P4; exact Hsst2)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp14 : add_vec_int (mword_of_int (PP + 0x12) : mword 64) 2 = mword_of_int (PP + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* P4-level register facts pushed through the two inserts *)
    assert (Ha0P4 : P4 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Ha0C. }
    assert (HspP4 : P4 !!! Regidx csp_rs1 = spd).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HspC. }
    assert (Hs9P4 : P4 !!! Regidx (mword_of_int 9 : mword 5)
                    = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Hs9C. }
    assert (HtpP4 : P4 !!! Regidx (mword_of_int 4 : mword 5)
                    = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact HtpC. }
    (* ------------------------------------------------------------------ *)
    (* +0x14 c.lw a5,120(a0): a ONE-instruction VCgen block over the noff   *)
    (* word cell (geometry from RAM-ness; alignment from po_slot_geom).     *)
    (* ------------------------------------------------------------------ *)
    pose (ρD := fun k : nat => match k with
           | 2%nat => P4 !!! Regidx csp_rs1
           | 4%nat => P4 !!! Regidx (mword_of_int 4 : mword 5)
           | 9%nat => P4 !!! Regidx (mword_of_int 9 : mword 5)
           | 10%nat => P4 !!! Regidx (mword_of_int 10 : mword 5)
           | _ => sign_extend' 64 noffv
           end).
    assert (HmD : gpr_matches ρD po_lw_regs0 P4).
    { unfold po_lw_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HaD : sval_den ρD (SX 10 120) = a_noff).
    { cbn [sval_den].
      replace (ρD 10%nat) with (P4 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
      rewrite Ha0P4. unfold a_noff. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (HvD : sval32_den ρD (SX32 33 0) = noffv).
    { cbn [sval32_den].
      replace (ρD 33%nat) with (sign_extend' 64 noffv) by reflexivity.
      rewrite trunc32_sext. apply avi0_32. }
    iAssert (block_instrs_s (PP + 0x14) popoff_lw_prog) with "[Hi14]" as "Hbi14".
    { cbn [block_instrs_s popoff_lw_prog vop_s_ast]. iFrame "Hi14". }
    iApply (wp_vc_block_s root_ppn popoff_lw_prog E Φ
              (VSt (PP + 0x14) po_lw_regs0 [] po_noff_cell0)
              (VSt (PP + 0x16) po_lw_regs1 [] po_noff_cell0)
              ρD P4 mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE po_lw_run HmD
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi14 [] [Hnoff]").
    { rewrite /vheap_own. cbn [vheap]. done. }
    { rewrite /vheap4_own. cbn [vheap4]. rewrite /po_noff_cell0.
      cbn [big_opL fst snd].
      rewrite HaD HvD. iFrame "Hnoff". }
    iIntros (M2) "%HmD1 Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile _ Hheap4".
    iEval (rewrite /vheap4_own; cbn [vheap4]; rewrite /po_noff_cell0;
           cbn [big_opL fst snd];
           rewrite HaD HvD) in "Hheap4".
    iDestruct "Hheap4" as "[Hnoffw _]".
    (* M2 facts *)
    assert (Ha5M2 : M2 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noffv).
    { assert (Hl : po_lw_regs1 !! Regidx (mword_of_int 15 : mword 5) = Some (S32 (SX32 33 0)))
        by (vm_compute; reflexivity).
      rewrite (HmD1 _ _ Hl). cbn [sval_den sval32_den].
      replace (ρD 33%nat) with (sign_extend' 64 noffv) by reflexivity.
      rewrite trunc32_sext avi0_32. reflexivity. }
    assert (Ha0M2 : M2 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { assert (Hl : po_lw_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 10 0))
        by (vm_compute; reflexivity).
      rewrite (HmD1 _ _ Hl) sval_den_SX0.
      replace (ρD 10%nat) with (P4 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
      exact Ha0P4. }
    assert (HspM2 : M2 !!! Regidx csp_rs1 = spd).
    { assert (Hl : po_lw_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (HmD1 _ _ Hl) sval_den_SX0.
      replace (ρD 2%nat) with (P4 !!! Regidx csp_rs1) by reflexivity.
      exact HspP4. }
    assert (Hs9M2 : M2 !!! Regidx (mword_of_int 9 : mword 5)
                    = m !!! Regidx (mword_of_int 9 : mword 5)).
    { assert (Hl : po_lw_regs1 !! Regidx (mword_of_int 9 : mword 5) = Some (SX 9 0))
        by (vm_compute; reflexivity).
      rewrite (HmD1 _ _ Hl) sval_den_SX0.
      replace (ρD 9%nat) with (P4 !!! Regidx (mword_of_int 9 : mword 5)) by reflexivity.
      exact Hs9P4. }
    assert (HtpM2 : M2 !!! Regidx (mword_of_int 4 : mword 5)
                    = m !!! Regidx (mword_of_int 4 : mword 5)).
    { assert (Hl : po_lw_regs1 !! Regidx (mword_of_int 4 : mword 5) = Some (SX 4 0))
        by (vm_compute; reflexivity).
      rewrite (HmD1 _ _ Hl) sval_den_SX0.
      replace (ρD 4%nat) with (P4 !!! Regidx (mword_of_int 4 : mword 5)) by reflexivity.
      exact HtpP4. }
    (* +0x16 blez a5 NOT taken (noff >= 1) *)
    iApply (wp_bge_x0_fall_s root_ppn E Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15)
              M2 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5M2; exact Hnoffpos)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* ------------------------------------------------------------------ *)
    (* +0x1a c.addiw a5,-1 ; +0x1c c.sw a5,120(a0): ONE VCgen block.        *)
    (* ------------------------------------------------------------------ *)
    pose (ρE := fun k : nat => match k with
           | 2%nat => M2 !!! Regidx csp_rs1
           | 4%nat => M2 !!! Regidx (mword_of_int 4 : mword 5)
           | 9%nat => M2 !!! Regidx (mword_of_int 9 : mword 5)
           | 10%nat => M2 !!! Regidx (mword_of_int 10 : mword 5)
           | _ => sign_extend' 64 noffv
           end).
    assert (HmE : gpr_matches ρE po_decsw_regs0 M2).
    { unfold po_decsw_regs0.
      apply gpr_matches_ins.
      { cbn [sval_den sval32_den].
        replace (ρE 33%nat) with (sign_extend' 64 noffv) by reflexivity.
        rewrite trunc32_sext avi0_32. exact Ha5M2. }
      unfold po_lw_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HaE : sval_den ρE (SX 10 120) = a_noff).
    { cbn [sval_den].
      replace (ρE 10%nat) with (M2 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
      rewrite Ha0M2. unfold a_noff. f_equal;
      apply bv_eq; vm_compute; reflexivity. }
    assert (HvE : sval32_den ρE (SX32 33 0) = noffv).
    { cbn [sval32_den].
      replace (ρE 33%nat) with (sign_extend' 64 noffv) by reflexivity.
      rewrite trunc32_sext. apply avi0_32. }
    iAssert (block_instrs_s (PP + 0x1a) popoff_decsw_prog) with "[Hi1a Hi1c]" as "Hbi1a".
    { cbn [block_instrs_s popoff_decsw_prog vop_s_ast].
      replace (PP + 0x1a + 2) with (PP + 0x1c) by lia.
      iFrame "Hi1a Hi1c". }
    iApply (wp_vc_block_s root_ppn popoff_decsw_prog E Φ
              (VSt (PP + 0x1a) po_decsw_regs0 [] po_noff_cell0)
              (VSt (PP + 0x1e) po_decsw_regs1 [] po_noff_cell1)
              ρE M2 mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE po_decsw_run HmE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                    Hpc Hfile Hbi1a [] [Hnoffw]").
    { rewrite /vheap_own. cbn [vheap]. done. }
    { rewrite /vheap4_own. cbn [vheap4]. rewrite /po_noff_cell0.
      cbn [big_opL fst snd].
      rewrite HaE HvE. iFrame "Hnoffw". }
    iIntros (M3) "%HmE1 Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile _ Hheap4".
    assert (Hc63 : (mword_of_int 4294967295 : mword 32)
                   = trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))).
    { apply bv_eq. vm_compute. reflexivity. }
    (* the stored word IS the statement's [storeval] *)
    assert (Hstv : sval32_den ρE (SX32 33 4294967295) = storeval).
    { cbn [sval32_den].
      replace (ρE 33%nat) with (sign_extend' 64 noffv) by reflexivity.
      unfold storeval. fold (trunc32 nv1). unfold nv1.
      rewrite -trunc32_subrange.
      rewrite trunc32_sext.
      rewrite trunc32_add.
      rewrite !(trunc32_sext noffv).
      rewrite -Hc63.
      rewrite ?trunc32_sext. reflexivity. }
    iEval (rewrite /vheap4_own; cbn [vheap4]; rewrite /po_noff_cell1;
           cbn [big_opL fst snd];
           rewrite HaE Hstv) in "Hheap4".
    iDestruct "Hheap4" as "[Hnoffw2 _]".
    iRename "Hnoffw2" into "Hnoff".
    (* M3 facts *)
    assert (Ha5M3 : M3 !!! Regidx (mword_of_int 15 : mword 5) = nv1).
    { assert (Hl : po_decsw_regs1 !! Regidx (mword_of_int 15 : mword 5)
                   = Some (S32 (SX32 33 4294967295))) by (vm_compute; reflexivity).
      rewrite (HmE1 _ _ Hl). cbn [sval_den sval32_den].
      replace (ρE 33%nat) with (sign_extend' 64 noffv) by reflexivity.
      unfold nv1.
      rewrite -trunc32_subrange trunc32_add !(trunc32_sext noffv) -Hc63.
      rewrite ?trunc32_sext. reflexivity. }
    assert (Ha0M3 : M3 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { assert (Hl : po_decsw_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 10 0))
        by (vm_compute; reflexivity).
      rewrite (HmE1 _ _ Hl) sval_den_SX0.
      replace (ρE 10%nat) with (M2 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
      exact Ha0M2. }
    assert (HspM3 : M3 !!! Regidx csp_rs1 = spd).
    { assert (Hl : po_decsw_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (HmE1 _ _ Hl) sval_den_SX0.
      replace (ρE 2%nat) with (M2 !!! Regidx csp_rs1) by reflexivity.
      exact HspM2. }
    assert (Hs9M3 : M3 !!! Regidx (mword_of_int 9 : mword 5)
                    = m !!! Regidx (mword_of_int 9 : mword 5)).
    { assert (Hl : po_decsw_regs1 !! Regidx (mword_of_int 9 : mword 5) = Some (SX 9 0))
        by (vm_compute; reflexivity).
      rewrite (HmE1 _ _ Hl) sval_den_SX0.
      replace (ρE 9%nat) with (M2 !!! Regidx (mword_of_int 9 : mword 5)) by reflexivity.
      exact Hs9M2. }
    assert (HtpM3 : M3 !!! Regidx (mword_of_int 4 : mword 5)
                    = m !!! Regidx (mword_of_int 4 : mword 5)).
    { assert (Hl : po_decsw_regs1 !! Regidx (mword_of_int 4 : mword 5) = Some (SX 4 0))
        by (vm_compute; reflexivity).
      rewrite (HmE1 _ _ Hl) sval_den_SX0.
      replace (ρE 4%nat) with (M2 !!! Regidx (mword_of_int 4 : mword 5)) by reflexivity.
      exact HtpM2. }
    (* +0x1e c.bnez a5: both outcomes (noff-1 <> 0 / = 0) *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnz.
    - (* taken: skip the intena check, straight to the epilogue at +0x28 *)
      iApply (wp_cbnez_taken_s_zca root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                M3 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5M3; exact Hnz)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpc28 : add_vec (mword_of_int (PP + 0x1e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                      = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- VCgen epilogue from M3 ---- *)
      pose (ρC := fun k : nat => match k with
             | 2%nat => M3 !!! Regidx csp_rs1
             | 4%nat => M3 !!! Regidx (mword_of_int 4 : mword 5)
             | 9%nat => M3 !!! Regidx (mword_of_int 9 : mword 5)
             | 10%nat => M3 !!! Regidx (mword_of_int 10 : mword 5)
             | 33%nat => m !!! Regidx (mword_of_int 1 : mword 5)
             | _ => m !!! Regidx (mword_of_int 8 : mword 5)
             end).
      assert (HmC : gpr_matches ρC po_epi_regs0 M3).
      { unfold po_epi_regs0.
        repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
        apply gpr_matches_empty. }
      assert (HaraC : sval_den ρC (SX 2 8) = a_p8).
      { cbn [sval_den].
        replace (ρC 2%nat) with (M3 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspM3. unfold a_p8. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Has0C : sval_den ρC (SX 2 0) = a_p0).
      { cbn [sval_den].
        replace (ρC 2%nat) with (M3 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspM3. unfold a_p0. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hv33C : sval_den ρC (SX 33 0) = m !!! Regidx (mword_of_int 1 : mword 5))
        by (rewrite sval_den_SX0; reflexivity).
      assert (Hv34C : sval_den ρC (SX 34 0) = m !!! Regidx (mword_of_int 8 : mword 5))
        by (rewrite sval_den_SX0; reflexivity).
      iDestruct (popoff_epilogue_instrs with "Htext") as "Hbi2".
      iApply (wp_vc_block_s root_ppn mycpu_epilogue E Φ
                (VSt (PP + 0x28) po_epi_regs0 mycpu_epi_heap [])
                (VSt (PP + 0x2e) po_epi_regs1 mycpu_epi_heap [])
                ρC M3 mstatus0 mie_v mdv0 menvcfg0
                (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE po_epilogue_run HmC
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0] []").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        cbn [big_opL fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      { rewrite /vheap4_own. cbn [vheap4]. done. }
      iIntros (Mf) "%HmC1 Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
      iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
             cbn [big_opL fst snd];
             rewrite HaraC Has0C Hv33C Hv34C) in "Hheap".
      iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
      (* the final register facts, via the agreement *)
      assert (HraF : Mf !!! Regidx (mword_of_int 1 : mword 5)
                     = m !!! Regidx (mword_of_int 1 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 33 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0. reflexivity. }
      assert (Hs0F : Mf !!! Regidx (mword_of_int 8 : mword 5)
                     = m !!! Regidx (mword_of_int 8 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 8 : mword 5) = Some (SX 34 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0. reflexivity. }
      assert (Hs1F : Mf !!! Regidx (mword_of_int 9 : mword 5)
                     = m !!! Regidx (mword_of_int 9 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 9 : mword 5) = Some (SX 9 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 9%nat) with (M3 !!! Regidx (mword_of_int 9 : mword 5)) by reflexivity.
        exact Hs9M3. }
      assert (HspF : Mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
      { assert (Hl : po_epi_regs1 !! Regidx csp_rs1 = Some (SX 2 16))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl). cbn [sval_den].
        replace (ρC 2%nat) with (M3 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspM3. rewrite /spd po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                         (mword_of_int 16 : mword 64))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero. }
      assert (HtpF : Mf !!! Regidx (mword_of_int 4 : mword 5)
                     = m !!! Regidx (mword_of_int 4 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 4 : mword 5) = Some (SX 4 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 4%nat) with (M3 !!! Regidx (mword_of_int 4 : mword 5)) by reflexivity.
        exact HtpM3. }
      assert (Ha0F : Mf !!! Regidx (mword_of_int 10 : mword 5) = a0v).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 10 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 10%nat) with (M3 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
        exact Ha0M3. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Mf
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraF; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      iEval (rewrite HraF) in "Hpc".
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hlegal Hmm HPBMTE Hpmm Hlpe HFIOM
                   with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
      iApply ("Hcont" with "Hcfg Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Mf. iFrame "Hfile". iPureIntro.
        exact (conj HraF (conj Hs0F (conj Hs1F (conj HspF (conj HtpF Ha0F))))). }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
    - (* fall: noff-1 = 0, read intena (= 0), c.beqz taken to +0x28 *)
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                M3 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5M3; exact Hnz)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpp20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.lw a5,124(a0): a5 := sext64 intenav (fractional cell: leaf) *)
      assert (HAint : add_vec (M3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 124 : mword 12)) = a_int)
        by (rewrite Ha0M3; reflexivity).
      iApply (wp_clw_s_ram root_ppn E Φ (mword_of_int (PP + 0x20)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 124) M3 intenav mstatus0 mie_v mdv0 menvcfg0
                (dq:=DfracOwn 1) (dqm:=dqi)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi20 [Hint] [-]").
      { iEval (rewrite HAint). iExact "Hint". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hint".
      iEval (rewrite HAint) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> M3).
      assert (Ha5P7 : P7 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 intenav)
        by (rewrite /P7; apply lookup_total_insert).
      assert (Hpp22 : add_vec_int (mword_of_int (PP + 0x20) : mword 64) 2 = mword_of_int (PP + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.beqz a5 TAKEN (intena = 0) *)
      iApply (wp_cbeqz_taken_s_zca root_ppn E Φ (mword_of_int (PP + 0x22)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P7 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P7; exact Hint)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpc28 : add_vec (mword_of_int (PP + 0x22) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
                      = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- VCgen epilogue from P7 ---- *)
      assert (HspP7 : P7 !!! Regidx csp_rs1 = spd).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspM3. }
      assert (Hs9P7 : P7 !!! Regidx (mword_of_int 9 : mword 5)
                      = m !!! Regidx (mword_of_int 9 : mword 5)).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Hs9M3. }
      assert (HtpP7 : P7 !!! Regidx (mword_of_int 4 : mword 5)
                      = m !!! Regidx (mword_of_int 4 : mword 5)).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HtpM3. }
      assert (Ha0P7 : P7 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact Ha0M3. }
      pose (ρC := fun k : nat => match k with
             | 2%nat => P7 !!! Regidx csp_rs1
             | 4%nat => P7 !!! Regidx (mword_of_int 4 : mword 5)
             | 9%nat => P7 !!! Regidx (mword_of_int 9 : mword 5)
             | 10%nat => P7 !!! Regidx (mword_of_int 10 : mword 5)
             | 33%nat => m !!! Regidx (mword_of_int 1 : mword 5)
             | _ => m !!! Regidx (mword_of_int 8 : mword 5)
             end).
      assert (HmC : gpr_matches ρC po_epi_regs0 P7).
      { unfold po_epi_regs0.
        repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
        apply gpr_matches_empty. }
      assert (HaraC : sval_den ρC (SX 2 8) = a_p8).
      { cbn [sval_den].
        replace (ρC 2%nat) with (P7 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspP7. unfold a_p8. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Has0C : sval_den ρC (SX 2 0) = a_p0).
      { cbn [sval_den].
        replace (ρC 2%nat) with (P7 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspP7. unfold a_p0. f_equal;
        apply bv_eq; vm_compute; reflexivity. }
      assert (Hv33C : sval_den ρC (SX 33 0) = m !!! Regidx (mword_of_int 1 : mword 5))
        by (rewrite sval_den_SX0; reflexivity).
      assert (Hv34C : sval_den ρC (SX 34 0) = m !!! Regidx (mword_of_int 8 : mword 5))
        by (rewrite sval_den_SX0; reflexivity).
      iDestruct (popoff_epilogue_instrs with "Htext") as "Hbi2".
      iApply (wp_vc_block_s root_ppn mycpu_epilogue E Φ
                (VSt (PP + 0x28) po_epi_regs0 mycpu_epi_heap [])
                (VSt (PP + 0x2e) po_epi_regs1 mycpu_epi_heap [])
                ρC P7 mstatus0 mie_v mdv0 menvcfg0
                (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE po_epilogue_run HmC
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0] []").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        cbn [big_opL fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      { rewrite /vheap4_own. cbn [vheap4]. done. }
      iIntros (Mf) "%HmC1 Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
      iEval (rewrite /vheap_own; cbn [vheap]; rewrite /mycpu_epi_heap;
             cbn [big_opL fst snd];
             rewrite HaraC Has0C Hv33C Hv34C) in "Hheap".
      iDestruct "Hheap" as "(Hp8 & Hp0 & _)".
      assert (HraF : Mf !!! Regidx (mword_of_int 1 : mword 5)
                     = m !!! Regidx (mword_of_int 1 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 33 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0. reflexivity. }
      assert (Hs0F : Mf !!! Regidx (mword_of_int 8 : mword 5)
                     = m !!! Regidx (mword_of_int 8 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 8 : mword 5) = Some (SX 34 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0. reflexivity. }
      assert (Hs1F : Mf !!! Regidx (mword_of_int 9 : mword 5)
                     = m !!! Regidx (mword_of_int 9 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 9 : mword 5) = Some (SX 9 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 9%nat) with (P7 !!! Regidx (mword_of_int 9 : mword 5)) by reflexivity.
        exact Hs9P7. }
      assert (HspF : Mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
      { assert (Hl : po_epi_regs1 !! Regidx csp_rs1 = Some (SX 2 16))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl). cbn [sval_den].
        replace (ρC 2%nat) with (P7 !!! Regidx csp_rs1) by reflexivity.
        rewrite HspP7. rewrite /spd po_addv_assoc.
        replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                         (mword_of_int 16 : mword 64))
          with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        apply kv_addv_zero. }
      assert (HtpF : Mf !!! Regidx (mword_of_int 4 : mword 5)
                     = m !!! Regidx (mword_of_int 4 : mword 5)).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 4 : mword 5) = Some (SX 4 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 4%nat) with (P7 !!! Regidx (mword_of_int 4 : mword 5)) by reflexivity.
        exact HtpP7. }
      assert (Ha0F : Mf !!! Regidx (mword_of_int 10 : mword 5) = a0v).
      { assert (Hl : po_epi_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 10 0))
          by (vm_compute; reflexivity).
        rewrite (HmC1 _ _ Hl) sval_den_SX0.
        replace (ρC 10%nat) with (P7 !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
        exact Ha0P7. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Mf
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraF; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      iEval (rewrite HraF) in "Hpc".
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hlegal Hmm HPBMTE Hpmm Hlpe HFIOM
                   with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
      iApply ("Hcont" with "Hcfg Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Mf. iFrame "Hfile". iPureIntro.
        exact (conj HraF (conj Hs0F (conj Hs1F (conj HspF (conj HtpF Ha0F))))). }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
  Qed.

End WpPopOffVc.

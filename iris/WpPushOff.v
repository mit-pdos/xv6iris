(* WpPushOff.v -- executing xv6's [push_off] in supervisor mode.

   [push_off] (kernel/spinlock.c) disables S-mode interrupts and bumps the
   per-cpu nesting depth [noff], saving the previous interrupt-enable state in
   [intena] on the first (noff==0) push.  Its byte image (KernelInstrs.v,
   symbol [push_off] @ 0x80000bc0):

     80000bc0:  addi  sp,sp,-32          (c.addi16sp)   frame alloc
     80000bc2:  sd    ra,24(sp)          (c.sdsp)
     80000bc4:  sd    s0,16(sp)          (c.sdsp)
     80000bc6:  sd    s1,8(sp)           (c.sdsp)
     80000bc8:  addi  s0,sp,32           (c.addi4spn)
     80000bca:  csrrci a5,sstatus,2                     read+clear SIE
     80000bce:  mv    s1,a5              (c.mv)         save old sstatus
     80000bd0:  jal   mycpu                              a0 = &cpus[cpuid]
     80000bd4:  lw    a5,120(a0)         (c.lw)         a5 = noff
     80000bd6:  beqz  a5,80000bec        (c.beqz)       if noff==0 -> set intena
     80000bd8:  jal   mycpu                              (merge point)
     80000bdc:  lw    a5,120(a0)         (c.lw)
     80000bde:  addiw a5,a5,1            (c.addiw)      noff+1
     80000be0:  sw    a5,120(a0)         (c.sw)         noff := noff+1
     80000be2:  ld    ra,24(sp)          (c.ldsp)       epilogue
     80000be4:  ld    s0,16(sp)          (c.ldsp)
     80000be6:  ld    s1,8(sp)           (c.ldsp)
     80000be8:  addi  sp,sp,32           (c.addi16sp)
     80000bea:  ret                      (c.ret)
     80000bec:  jal   mycpu                              intena path
     80000bf0:  srli  a5,s1,0x1                          old sstatus >> 1
     80000bf4:  andi  a5,a5,1            (c.andi)        old SIE bit
     80000bf6:  sw    a5,124(a0)         (c.sw)         intena := old SIE
     80000bf8:  j     80000bd8           (c.j)          back to merge

   Everything runs in Supervisor mode with paging on (Sv39 identity superpage,
   the standard kernel setup used by WpMemsetS/WpSmodeGpr).  Because every
   S-mode instruction lemma requires [mstatus.SIE = 0] (so no interrupt is
   taken mid-instruction), we prove [push_off] under the contract that it is
   entered with interrupts already disabled; [csrrci] then re-clears SIE (a
   no-op on SIE) while still reading the old sstatus and driving the [intena]
   logic.

   This file first builds the S-mode instruction WP lemmas [push_off]/[mycpu]
   need that the framework lacks (compressed addiw/andi/add, 4-byte addi/srli,
   auipc, c.beqz-taken, c.j, 4-byte lw/sw, and csrrci-on-sstatus), then the
   whole-function WPs [wp_mycpu] and [wp_push_off]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAuipc.
Require Import WpGpr WpGprAddi WpMmodeShiftiop WpGprLogic WpGprAuipc.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew.
Require Export WpSmodeToBeDeleted WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeUtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpPushOff.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* Shorthand: the block of S-mode config side-conditions shared by every
     [_s_config] arithmetic wrapper (identical to wp_caddi_gpr_s_config's). *)

  (* ---- c.addiw rd,imm : ADDIW rd,rd,sext(imm) (RVC, +2) ---- *)

  (* ---- c.andi rd,imm : ANDI rd,rd,sext(imm) (RVC, +2) ---- *)

  (* ---- c.add rd,rs2 : ADD rd,rd,rs2 (RVC, +2) ---- *)

  (* ---- addi rd,rs1,imm (4-byte F_Base, +4) ---- *)

  (* ---- srli rd,rs1,shamt (4-byte F_Base, +4) ---- *)

  (* ---- generic 4-byte register writer that ALSO exposes [PC = pc] to the
     forward-exec obligation (for PC-reading instructions like auipc).  A
     verbatim clone of [wp_gpr_write_s_config_base] with one extra premise. ---- *)

  (* ---- auipc rd,imm (4-byte, reads PC) ---- *)

  (* ---- c.beqz rs TAKEN (rs == 0): jump to pc + sext(offset) ---- *)
  Lemma wp_cbeqz_taken_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := add_vec pc (sign_extend' 64 (sign_extend' 13 (concat_vec imm8 ('b"0")))) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec tgt 1) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hrs Hrd1 Hcmp Hal0 Hal1.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      rewrite Hrs. change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      assert (Htk : eq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      epose proof (exec_execute_BTYPE_BEQ_taken (sign_extend' 13 (concat_vec imm8 ('b"0")))
                     (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. fold tgt in Hred.
      exact (Hred Hal0 Hal1). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- c.j (JAL x0): jump to pc + sext(offset) ---- *)
  Lemma wp_cj_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    let tgt := add_vec pc (sign_extend' 64 jimm) in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (JAL (jimm, zreg)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (JAL (jimm, zreg))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (HzcaC : eq_vec (_get_Misa_C (register_lookup misa s_pc.(sregs))) ('b"1") = true).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ rewrite Lmisa; exact HmisaC | vm_compute; reflexivity ]. }
    assert (Halign_spc : eq_vec (access_vec_dec
              (add_vec (register_lookup PC s_pc.(sregs)) (sign_extend' 64 jimm)) 0) ('b"0") = true).
    { rewrite Hpcv. exact Hal0. }
    iMod (reg_update _ nextPC _ tgt with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC tgt).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      change (execute (JAL (jimm, zreg))) with (execute_JAL jimm zreg).
      rewrite (exec_execute_JAL_zreg_zca jimm s_pc Halign_spc
                 (exec_currentlyEnabled_Zca s_pc HzcaC)).
      rewrite Hpcv. reflexivity. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc nextPC tgt).(sregs) = tgt)
      by (unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

End WpPushOff.

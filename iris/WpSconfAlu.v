(* WpSconfAlu.v -- the SIE-AGNOSTIC ALU leaf layer (interrupt-sweep
   stage 5, first family file): the [sconf]+[sie_cap] twins of
   WpSmodePtAlu.v's leaves, over the agnostic gpr-write engines
   [wp_gpr_write_s_sconf{,_base}] (WpSmodeIntr.v).

   Uniform transform vs the `_pt` originals:
     - resources: `smode_config γ dq ∗ tlb_inv_pt` becomes
       `sconf γ ∗ hart_state ∗ sie_cap γ root_ppn m ∗ tlb_inv_pt`
       (full ownership; hart_state travels beside the bundle);
     - the raw-cell/_scfg PAIR collapses to ONE lemma (sconf is the
       only bundle; raw-cell forms stay in WpSmodePtAlu for the mycpu
       fraction-island until the sweep completes);
     - NEW premise `rd <> csp_rs1` on every rd-writing leaf: [sie_cap]'s
       '1' arm is keyed on sp ([sie_cap_retarget]); sp-MOVING
       instructions (c.addi sp, imm / c.addi16sp) are NOT in this file
       -- they re-carve their stack explicitly at the function level;
     - the value-hypothesis discharge scripts are VERBATIM copies.
   Also here: the PC-READING 4-byte engine [wp_gpr_write_s_sconf_base_pc]
   (the [wp_gpr_write_s_config_base_pc_pt] twin) and [wp_auipc_s_sconf]
   over it.                                                              *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase WpSmodeLeafBase WpMmodeShiftiop.
Require Import SmodeCore WpAuipc KptTree SmodeCorePt.
Require Import StackOwn WpSmodeSret AlignBits.
Require Import WpIntrBits WpIntrCore IntrDefs WpIntrInv WpSmodeIntr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Section WpSconfAlu.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- ITYPE family ---------------------------------------------------- *)

  (* addi rd, rs1, imm (base width) is [wp_addi_s_sconf] (WpSmodeIntr.v). *)

  Lemma wp_caddi4spn_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : gmap regidx (mword 64)) :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrdc Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_candi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))
              (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ANDI_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_andi_val. rewrite Hva. reflexivity.
  Qed.

  (* c.li rd, imm is [wp_cli_s_sconf] (WpSmodeIntr.v). *)

  Lemma wp_sltiu_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_sltiu_val. rewrite Hva Hwval. reflexivity.
  Qed.

  (* ---- RTYPE family ---------------------------------------------------- *)

  Lemma wp_cadd_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rd) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rd rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb. reflexivity.
  Qed.

  Lemma wp_cmv_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec zero_reg (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
    rewrite Hva. reflexivity.
  Qed.

  Lemma wp_sltu_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_sltu_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_cor_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_sub_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
    rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_add_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* ---- UTYPE / ADDIW / SHIFTIOP families ------------------------------- *)

  Lemma wp_clui_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    luival imm = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (UTYPE (imm, Regidx rd, LUI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI)) wval m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc _ _.
    rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  Lemma wp_caddiw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ADDIW_gpr rd rd (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addiw_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_cslli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) :
    rsd = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrsd Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_csrli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) :
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hcrsd Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_srli4_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The PC-READING 4-byte gpr-write engine (auipc): the base engine      *)
  (* with [register_lookup PC s_pc = pc] handed to the exec hypothesis.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_gpr_write_s_sconf_base_pc (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup PC s_pc.(sregs) = pc ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute i) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false i -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hbexec)
      "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    iApply (wp_instr_s_sconf γ root_ppn m Φ pc false i
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv [%Hdom Hfmap] Hnpc [Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    assert (LpcS : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 LpcS Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply lookup_total_insert_ne; exact Hspne).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg wval]> m) Hsp with "Hcap") as "Hcap".
    iApply ("Hcont" with "Hhs' Hsc Hcap Htlbinv [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  Lemma wp_auipc_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : gmap regidx (mword 64)) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base_pc γ root_ppn Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, AUIPC))
              (add_vec pc (auipc_off imm)) m
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc HPCpc _ _.
    rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite HPCpc. reflexivity.
  Qed.

End WpSconfAlu.

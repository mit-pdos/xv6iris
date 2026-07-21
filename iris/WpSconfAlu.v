(* WpSconfAlu.v -- the SIE-AGNOSTIC ALU leaf layer (interrupt-sweep
   stage 5, first family file): the [sconf]+[sie_cap] twins of
   WpSmodePtAlu.v's leaves, over the agnostic gpr-write engines
   [wp_gpr_write_s_sconf{,_base}] (WpSmodeIntr.v).

   Uniform transform vs the `_pt` originals:
     - resources: `smode_config γ dq ∗ tlb_inv_pt` becomes
       `sconf γ ∗ hart_state ∗ sie_cap γ root_ppn m n ∗ tlb_inv_pt`
       (full ownership; hart_state travels beside the bundle);
     - the raw-cell/_scfg PAIR collapses to ONE lemma (sconf is the
       only bundle; raw-cell forms stay in WpSmodePtAlu for the mycpu
       fraction-island until the sweep completes);
     - NEW premise `rd <> csp_rs1` on every rd-writing leaf: [sie_cap]
       is keyed on sp ([sie_cap_retarget]); the sp-MOVING instructions
       (c.addi sp, imm / c.addi16sp) live at the END of this file --
       a generic transformer engine plus the direct PUSH/POP specs
       (wp_caddi{_sp,16sp}_{push,pop}_s_sconf) that trade the moved
       slots against [sie_cap]'s available count;
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
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RegFile WpGpr InstrBytes WpMmodeLeafBase WpMmodeShiftiop StackOwn.
Require Import SmodeCore WpAuipc KptTree.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
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
      (m : regfile) (n : nat) :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrdc Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_caddi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_candi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))
              (and_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ANDI_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_andi_val. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  (* c.li rd, imm is [wp_cli_s_sconf] (WpSmodeIntr.v). *)

  Lemma wp_sltiu_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sltiu_val. rewrite Hva Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  (* ---- RTYPE family ---------------------------------------------------- *)

  Lemma wp_cadd_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              (add_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rd) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rd rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val. rewrite Hva Hvb. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_cmv_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (m !!! Regidx rs2))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (add_vec zero_reg (m !!! Regidx rs2))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_sltu_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_sltu_val. rewrite Hva Hvb Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_cor_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  (* c.and rd,rd,rs2 (register-register AND; the freerange PGROUNDUP mask
     step -- homed here since it is an ordinary c.and leaf like [wp_cor_s_sconf]
     above, not freerange-specific). *)
  Lemma wp_cand_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (and_vec (m !!! Regidx rd) (m !!! Regidx rs2))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))
              (and_vec (m !!! Regidx rd) (m !!! Regidx rs2))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rd rd s_pc Hrd).
      unfold gpr_and_val. rewrite Hva Hvb. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_sub_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
      rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_add_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val. rewrite Hva Hvb Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  (* ---- UTYPE / ADDIW / SHIFTIOP families ------------------------------- *)

  (* base (32-bit) SLLI: [slli rd,rs1,shamt] with rd <> rs1 (not compressible). *)
  Lemma wp_slli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    shift_bits_left (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_clui_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    luival imm = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (UTYPE (imm, Regidx rd, LUI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc _ _.
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_caddiw_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ADDIW_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addiw_val. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_cslli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) :
    rsd = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrsd Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (shift_bits_left (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_csrli_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) :
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hcrsd Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf γ root_ppn Φ pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_srli4_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              (shift_bits_right (m !!! Regidx rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.


  (* base-width addi (rd != x0, rd != sp): [wval] is the model's
     [gpr_addi_val] at map-form operands. *)
  Lemma wp_addi4_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm))
              m n Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val, gpr_src. rewrite Hva. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.



  (* ------------------------------------------------------------------- *)
  (* The PC-READING 4-byte gpr-write engine (auipc): the base engine      *)
  (* with [register_lookup PC s_pc = pc] handed to the exec hypothesis.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_gpr_write_s_sconf_base_pc (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : regfile) (n : nat) :
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
    sie_cap_gpr γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc false i -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hbexec)
      "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    iApply (wp_instr_s_sconf γ root_ppn m n Φ pc false i
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    assert (LpcS : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc m (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
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
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ root_ppn m
                 (<[Regidx rd := regval_into_reg wval]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hhs' Hsc Hcg Htlbinv [$Hpc' $Hnpc]").
  Qed.

  Lemma wp_auipc_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base_pc γ root_ppn Φ pc rd rd rd
              (UTYPE (imm, Regidx rd, AUIPC))
              (add_vec pc (auipc_off imm)) m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont").
    intros s_pc Hnpc HPCpc _ _.
    rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite HPCpc. reflexivity.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* SP-MOVERS: the cap engine takes a caller-supplied [sie_cap]          *)
  (* TRANSFORMER (n -> n') instead of the rd <> sp retarget premise --    *)
  (* an sp-write trades slots against the available count where the       *)
  (* function proof does its stack bookkeeping.  The push/pop leaves      *)
  (* below instantiate it with [sie_cap_push]/[sie_cap_pop].              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_gpr_write_s_sconf_cap (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) :
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗
    tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true base -∗
    ( sie_cap γ root_ppn m n -∗
      sie_cap γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n' ∗ P ) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n' -∗
      P -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hbexec)
      "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hrecap Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    iApply (wp_instr_s_sconf γ root_ppn m n Φ pc true base
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Htlbinv Hfile Hnpc [Hreg Hmem]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (gpr_file_lookup_acc m (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc m (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct ("Hrecap" with "Hcap") as "[Hcap HP]".
    iDestruct (sie_cap_gpr_join with "Hcap Hfile") as "Hcg".
    iApply ("Hcont" with "Hhs' Hsc Hcg HP Htlbinv [$Hpc' $Hnpc]").
  Qed.

  (* the two real sp-movers over the cap engine: c.addi sp, imm and
     c.addi16sp.  The caller supplies the capability transformer -- at
     SIE=0 ('0' arm) it is [sie_cap_retarget]-free (iLeft is m-blind);
     at SIE=1 it re-carves the >= 32-slot stack bound at the new sp,
     exactly where function proofs already do their stack bookkeeping. *)
  Lemma wp_caddi_sp_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n n' : nat) (P : iProp Σ) :
    let wval := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm)) in
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    ( sie_cap γ root_ppn m n -∗
      sie_cap γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' ∗ P ) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' -∗
      P -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros wval.
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hrecap Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_cap γ root_ppn Φ pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) wval m n n' P
              ltac:(vm_compute; discriminate) _
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hrecap Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint (csp_rs1 : mword 5)) 0) with false by (vm_compute; reflexivity).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi16sp_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n n' : nat) (P : iProp Σ) :
    let wval := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)) in
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( sie_cap γ root_ppn m n -∗
      sie_cap γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' ∗ P ) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' -∗
      P -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros wval.
    iIntros "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hrecap Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_cap γ root_ppn Φ pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) wval m n n' P
              ltac:(vm_compute; discriminate) _
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hrecap Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) s_pc).
    replace (Z.eqb (uint (csp_rs1 : mword 5)) 0) with false by (vm_compute; reflexivity).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The DIRECT sp-mover specs: PUSH (sp -= 8k, prologue) trades k off    *)
  (* the available count (k <= n -- the accounting cannot go below zero)  *)
  (* and hands out the freed frame region [sp', sp); POP (sp += 8k,       *)
  (* epilogue) feeds the k-slot frame at the NEW sp back in and returns   *)
  (* k to the count.  The address premise (the immediate denotes the      *)
  (* k-slot move) is a per-call-site fact on the concrete immediate.      *)
  (* Note the post-pop count is (n - k) + k after a matching push --      *)
  (* callers restore the syntactic n with a [replace ... by lia].         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_caddi_sp_push_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n k : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm)) in
    (k <= n)%nat ->
    wval = pa_stk sp0 k ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n - k) -∗
      stack_own sp0 k -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 wval.
    iIntros (Hk Hw) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    assert (Hsp' : <[Regidx csp_rs1 := regval_into_reg wval]> m !!! Regidx csp_rs1
                   = pa_stk (m !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pc imm m n (n - k) (stack_own sp0 k)
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr [] [Hcont]").
    { iIntros "Hcap".
      iDestruct (sie_cap_push γ root_ppn m _ n k Hk Hsp' with "Hcap")
        as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iApply ("Hcont" with "Hhs Hsc Hcg Hframe Htlbinv Hpc").
  Qed.

  Lemma wp_caddi_sp_pop_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n k : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm)) in
    sp0 = pa_stk wval k ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    stack_own wval k -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n + k) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 wval.
    iIntros (Hw) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hframe Hcont".
    assert (Hsp : m !!! Regidx csp_rs1
                  = pa_stk (<[Regidx csp_rs1 := regval_into_reg wval]> m
                            !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi_sp_s_sconf γ root_ppn Φ pc imm m n (n + k) emp%I
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr [Hframe] [Hcont]").
    { iIntros "Hcap".
      iSplitL; [| done].
      iApply (sie_cap_pop γ root_ppn m _ n k Hsp with "[Hframe] Hcap").
      rewrite upd_eq. iExact "Hframe". }
    iIntros "Hhs Hsc Hcg _ Htlbinv Hpc".
    iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc").
  Qed.

  Lemma wp_caddi16sp_push_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n k : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (caddi16sp_imm imm6)) in
    (k <= n)%nat ->
    wval = pa_stk sp0 k ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n - k) -∗
      stack_own sp0 k -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 wval.
    iIntros (Hk Hw) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    assert (Hsp' : <[Regidx csp_rs1 := regval_into_reg wval]> m !!! Regidx csp_rs1
                   = pa_stk (m !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ pc imm6 m n (n - k) (stack_own sp0 k)
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr [] [Hcont]").
    { iIntros "Hcap".
      iDestruct (sie_cap_push γ root_ppn m _ n k Hk Hsp' with "Hcap")
        as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    iApply ("Hcont" with "Hhs Hsc Hcg Hframe Htlbinv Hpc").
  Qed.

  Lemma wp_caddi16sp_pop_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n k : nat) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (caddi16sp_imm imm6)) in
    sp0 = pa_stk wval k ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    stack_own wval k -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n + k) -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 wval.
    iIntros (Hw) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hframe Hcont".
    assert (Hsp : m !!! Regidx csp_rs1
                  = pa_stk (<[Regidx csp_rs1 := regval_into_reg wval]> m
                            !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi16sp_s_sconf γ root_ppn Φ pc imm6 m n (n + k) emp%I
              with "Hsc Hhs Hcg Htlbinv Hpc Hinstr [Hframe] [Hcont]").
    { iIntros "Hcap".
      iSplitL; [| done].
      iApply (sie_cap_pop γ root_ppn m _ n k Hsp with "[Hframe] Hcap").
      rewrite upd_eq. iExact "Hframe". }
    iIntros "Hhs Hsc Hcg _ Htlbinv Hpc".
    iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc").
  Qed.


  (* srl/ori/andi -- moved here from WpSconfWalk.v (leaves belong in the leaf file). *)
  Lemma wp_srl_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    shift_bits_right (m !!! Regidx rs1)
      (subrange_vec_dec (m !!! Regidx rs2) (Z.sub log2_xlen 1) 0) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_SRL_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_srl_val. rewrite Hva Hvb Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_ori_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    or_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_ori_val. rewrite Hva Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.

  Lemma wp_andi_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_andi_val. rewrite Hva Hwval. reflexivity.
    - iIntros "Hhs' Hsc' Hcap' Htlbinv' Hpc' Hfile'".
      iDestruct (sie_cap_gpr_join with "Hcap' Hfile'") as "Hcg'".
      iApply ("Hcont" with "Hhs' Hsc' Hcg' Htlbinv' Hpc'").
  Qed.


  (* base-width OR -- moved here from WpSconfMappages.v (dedup: leaf belongs in the leaf file). *)
  Lemma wp_or_s_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) :
    uint rd <> 0 -> rd <> csp_rs1 ->
    or_vec (m !!! Regidx rs1) (m !!! Regidx rs2) = wval ->
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
      sie_cap_gpr γ root_ppn (<[Regidx rd := regval_into_reg wval]> m) n -∗
      tlb_inv_pt root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp Hwval) "Hsc Hhs Hcg Htlbinv Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "[Hcap Hfile]".
    unshelve iApply (wp_gpr_write_s_sconf_base γ root_ppn Φ pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m n
              Hrd Hrdsp _
              with "Hsc Hhs Hcap Htlbinv Hpc Hfile Hinstr [Hcont]").
    2:{ iIntros "Hhs Hsc Hcap Htlbinv Hpc Hfile".
        iDestruct (sie_cap_gpr_join with "Hcap Hfile") as "Hcg".
        iApply ("Hcont" with "Hhs Hsc Hcg Htlbinv Hpc"). }
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

End WpSconfAlu.
